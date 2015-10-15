/*
JSNES dynamic recompilation module
Copyright (C) 2010 Humberto Silva Naves

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

JSNES.CPU = function(nes) {
  this.nes = nes;
    
  // Keep Chrome happy
  this.mem = new Array(0x10000);
  this.ownerFunction = new Array(this.mem.length);
  this.usedResources = new Array(this.mem.length);
  this.chgResources = new Array(this.mem.length);
  this.innerLabel = new Array(this.mem.length);
  this.followStatus = new Array(this.mem.length);
  this.cache = new Array(this.mem.length);
  this.memRegion = new Array(this.mem.length);
  this.irq_pending = null;
  this.cyclesToHalt = 0;
  this.halted = null;

  this.pc_reg = null;
  this.a_reg = null;
  this.p_reg = null;
  this.x_reg = null;
  this.y_reg = null;
  this.s_reg = null;
  this.opdata = new JSNES.CPU.OpData();
  this.reset();
};

JSNES.CPU.prototype = {
  // IRQ Types
  IRQ_NORMAL: 0,
  IRQ_NMI:    1,
  IRQ_RESET:  2,
  // Vector addresses
  NMI_VECTOR:     0xFFFA,
  RESET_VECTOR:   0xFFFC,
  IRQ_VECTOR:     0xFFFE,
  // cycle counts for interrupts
  IRQ_CYCLES:   7,
  RESET_CYCLES: 6,

  load: function(address) {
    if (address < 0x2000) {
      return this.mem[address & 0x7FF];
    } else if (address < 0x8000) {
      return this.nes.mmap.load(address);
    } else {
      return this.mem[address];
    }
  },

  write: function(address, value) {
    if (address < 0x2000) {
      this.mem[address & 0x7FF] = value;
    } else {
      this.nes.mmap.write(address, value);
    }
  },

  pull: function() {
    this.s_reg = 0x100 | ((this.s_reg + 1) & 0xFF);
    return this.mem[this.s_reg];
  },

  pull16: function() {
    this.s_reg = 0x100 | ((this.s_reg + 1) & 0xFF);
    var v = this.mem[this.s_reg];
    this.s_reg = 0x100 | ((this.s_reg + 1) & 0xFF);
    v |= this.mem[this.s_reg] << 8;
    return v;
  },

  push: function(value) {
    this.mem[this.s_reg] = value;
    this.s_reg = 0x100 | ((this.s_reg - 1) & 0xFF);
  },

  push16: function(value) {
    this.mem[this.s_reg] = value >> 8;
    this.s_reg = 0x100 | ((this.s_reg - 1) & 0xFF);
    this.mem[this.s_reg] = value & 0xFF;
    this.s_reg = 0x100 | ((this.s_reg - 1) & 0xFF);
  },

  halt: function() {
    this.halted = false;
    this.cyclesToHalt = 0;
  },

  haltCycles: function(cycles) {
    this.cyclesToHalt += cycles;
  },

  reset: function() {
    for(var i = 0; i < this.mem.length; i++) {
      this.mem[i] = 0;
      this.ownerFunction[i] = undefined;
      this.usedResources[i] = undefined;
      this.chgResources[i] = undefined;
      this.innerLabel[i] = undefined;
      this.followStatus[i] = undefined;
      this.cache[i] = undefined;
      this.memRegion[i] = undefined;
    }
    this.requestIrq(this.IRQ_RESET);
  },

  requestIrq: function(irqType) {
    if (irqType == this.IRQ_RESET) {
      this.pc_reg = this.mem[this.RESET_VECTOR];
      this.pc_reg |= this.mem[this.RESET_VECTOR + 1] << 8;
      this.p_reg = 2 | 32; // Z_FLAG | R_FLAG
      this.cyclesToHalt = this.RESET_CYCLES;
      this.int_pending = false;
      this.halted = false;
      this.a_reg = 0;
      this.x_reg = this.y_reg = 0;
      this.s_reg = 0x1FF;
    } else if (!this.halted) {
      var mem = this.mem;
      if ((this.p_reg & 4 /* I_FLAG */) && (irqType == this.IRQ_NORMAL)) {
        this.int_pending = true;
      } else {
        var address = (irqType == this.IRQ_NMI) ? this.NMI_VECTOR : this.IRQ_VECTOR;
        this.cyclesToHalt += this.IRQ_CYCLES;
        this.push16(this.pc_reg);
        this.p_reg &= ~16; // ~B_FLAG
        this.push(this.p_reg);
        this.p_reg |= 4; // I_FLAG
        this.pc_reg = (mem[address] | (mem[address+1]<<8));
      }
    }
  },

  disassemble: function(address) {
    return this.opdata.disassemble(this.mem, address, address);
  },

  emulate2: function(count) {
    if (this.halted) return 0;

    if (!(this.p_reg & 4) && this.int_pending) {
      this.int_pending = false;
      this.requestIrq(this.IRQ_NORMAL);
    }

    if (count === undefined) count = 1;
    var cycles = count;
    while (cycles > 0) {
      if (this.ownerFunction[this.pc_reg] === undefined) {
        this.translate(this.pc_reg);
      }
      var f = this.cache[this.ownerFunction[this.pc_reg]];
      var innerLabel = this.innerLabel[this.pc_reg];
      if (innerLabel !== undefined) {
        cycles = f.call(this, cycles, innerLabel);
      } else {
        cycles -= this.interpret(1);
      }
    }
    return count - cycles;
  },

  emulate: function(count) {
    if (this.halted) return 0;

    if (!(this.p_reg & 4) && this.int_pending) {
      this.int_pending = false;
      this.requestIrq(this.IRQ_NORMAL);
    }

    var c_flag, z_flag, i_flag, d_flag;
    var b_flag, v_flag, n_flag;
    var mem = this.mem;
    var a_reg = this.a_reg, x_reg = this.x_reg, y_reg = this.y_reg;
    var pc_reg = this.pc_reg, p_reg = this.p_reg, s_reg = this.s_reg;

    if (count === undefined) count = 1;
    var cycles = 0;

    c_flag = p_reg & 1;
    z_flag = p_reg & 2;
    i_flag = p_reg & 4;
    d_flag = p_reg & 8;
    b_flag = p_reg & 16;
    v_flag = p_reg & 64;
    n_flag = p_reg & 128;

    var opdata = this.opdata.opdata;
    var insndetails = this.opdata.insndetails;

    while (cycles < count) {
      var opc;
      var opcode;
      var oper = 0, operp = 0, t;
      var insn, cyc, addressing;
      var details;
      opc = mem[pc_reg];
      opcode = opdata[opc];
      cyc = (opcode >> 24) & 0xFF;
      addressing = (opcode >> 8) & 0xFF;
      insn = opcode & 0xFF;
      details = insndetails[insn];

      cycles += cyc;
      pc_reg++;

      switch (addressing) {
      case 0: // ADDR_ACCUMULATOR
        oper = a_reg;
        break;
      case 1: // ADDR_IMMEDIATE
        oper = mem[pc_reg];
        pc_reg++;
        break;
      case 2: // ADDR_ZERO_PAGE
        operp = mem[pc_reg];
        oper = mem[operp];
        pc_reg++;
        break;
      case 3: // ADDR_ZERO_PAGE_X
        operp = (mem[pc_reg] + x_reg) & 0xFF;
        oper = mem[operp];
        pc_reg++;
        break;
      case 4: // ADDR_ZERO_PAGE_Y
        operp = (mem[pc_reg] + y_reg) & 0xFF;
        oper = mem[operp];
        pc_reg++;
        break;
      case 5: // ADDR_ABSOLUTE
        operp = (mem[pc_reg] | (mem[pc_reg+1]<<8));
        pc_reg += 2;
        if (details & 1 /* I_RD */)
          oper = this.load (operp);
        break;
      case 6: // ADDR_ABSOLUTE_X
        operp = (mem[pc_reg] + x_reg);
        pc_reg++;
        if (operp & 0x100) cycles++;
        operp += (mem[pc_reg]) << 8;
        pc_reg++;
        operp &= 0xFFFF;
        if (details & 1 /* I_RD */)
          oper = this.load (operp);
        break;
      case 7: // ADDR_ABSOLUTE_Y
        operp = (mem[pc_reg] + y_reg);
        pc_reg++;
        if (operp & 0x100) cycles++;
        operp += (mem[pc_reg]) << 8;
        pc_reg++;
        operp &= 0xFFFF;
        if (details & 1 /* I_RD */)
          oper = this.load (operp);
        break;
      case 8: // ADDR_INDIRECT
        t = (mem[pc_reg] | (mem[pc_reg+1]<<8));
        pc_reg += 2;
        /* 6502 bug here! */
        operp = mem[t];
        if ((t & 0xFF) == 0xFF)
          operp |= (mem[t - 0xFF]) << 8;
        else
          operp |= (mem[t + 1]) << 8;
        /* We don't need to eval "oper" because ADDR_INDIRECT
         * is used only for the JMP instruction
         * */
        break;
      case 9: // ADDR_INDIRECT_X
        t = (mem[pc_reg] + x_reg) & 0xFF;
        pc_reg++;
        operp = mem[t];
        operp |= (mem[(t + 1) & 0xFF]) << 8;
        if (details & 1 /* I_RD */)
          oper = this.load (operp);
        break;
      case 10: // ADDR_INDIRECT_Y
        t = mem[pc_reg] & 0xFF;
        pc_reg++;
        operp = (mem[t]) + y_reg;
        if (operp & 0x100) cycles++;
        operp += (mem[(t + 1) & 0xFF]) << 8;
        operp &= 0xFFFF;
        if (details & 1 /* I_RD */)
          oper = this.load (operp);
        break;
      case 11: // ADDR_RELATIVE
        t = mem[pc_reg];
        pc_reg++;
        if (t & 0x80) t |= 0xFF00;
        oper = (pc_reg + t) & 0xFFFF;
        break;
      case 12: // ADDR_IMPLIED
      default:
        oper = 0;
        break;
      }

      switch (insn) {
      case 0: // INSN_AAC - Undocumented
        a_reg &= oper;
        z_flag = (a_reg == 0); n_flag = (a_reg & 0x80);
        c_flag = z_flag;
        break;
      case 1: // INSN_AAX - Undocumented
        oper = x_reg & a_reg;
        this.write(operp, oper);
        break;
      case 2: // INSN_ADC
        t = oper + a_reg;
        if (c_flag) t++;
        c_flag = (t & 0x100);
        v_flag = (!((a_reg ^ oper) & 0x80) && ((a_reg ^ t) & 0x80));
        a_reg = t & 0xFF;
        z_flag = (a_reg == 0); n_flag = (a_reg & 0x80);
        break;
      case 3: // INSN_AND
        a_reg &= oper;
        z_flag = (a_reg == 0); n_flag = (a_reg & 0x80);
        break;
      case 4: // INSN_ARR - Undocumented
        a_reg &= oper;
        a_reg >>= 1;
        if (c_flag) a_reg |= 0x80;
        c_flag = a_reg & 0x40;
        v_flag = (((a_reg >> 1) ^ a_reg) & 0x20);
        z_flag = (a_reg == 0); n_flag = (a_reg & 0x80);
        break;
      case 5: // INSN_ASL
        c_flag = oper & 0x80;
        oper = (oper << 1) & 0xFF;
        z_flag = (oper == 0); n_flag = (oper & 0x80);
        if (addressing == 0) a_reg = oper; else this.write(operp, oper);
        break;
      case 6: // INSN_ASR - Undocumented
        a_reg &= oper;
        c_flag = a_reg & 0x01;
        a_reg >>= 1;
        z_flag = (a_reg == 0);
        n_flag = (0);
        break;
      case 7: // INSN_ATX - Undocumented
        a_reg = x_reg = ((a_reg | 0xEE) & oper); /* Unpredictable */
        z_flag = (oper == 0); n_flag = (oper & 0x80);
        break;
      case 8: // INSN_AXA - Undocumented
        oper = a_reg & x_reg & (((operp >> 8) + 1)); /* Unpredictable */
        this.write(operp, oper);
        break;
      case 9: // INSN_AXS - Undocumented
        x_reg = ((a_reg & x_reg) - oper);
        c_flag = x_reg < 0x100;
        x_reg &= 0xFF;
        z_flag = (x_reg == 0); n_flag = (x_reg & 0x80);
        break;
      case 10: // INSN_BCC
        if (!c_flag) {
          cycles++;
          if ((oper & 0xFF00) != (pc_reg & 0xFF00)) {
            cycles++;
          }
          pc_reg = oper;
        }
        break;
      case 11: // INSN_BCS
        if (c_flag) {
          cycles++;
          if ((oper & 0xFF00) != (pc_reg & 0xFF00)) {
            cycles++;
          }
          pc_reg = oper;
        }
        break;
      case 12: // INSN_BEQ
        if (z_flag) {
          cycles++;
          if ((oper & 0xFF00) != (pc_reg & 0xFF00)) {
            cycles++;
          }
          pc_reg = oper;
        }
        break;
      case 13: // INSN_BIT
        n_flag = (oper & 0x80);
        v_flag = (oper & 0x40);
        z_flag = ((oper & a_reg) == 0);
        break;
      case 14: // INSN_BMI
        if (n_flag) {
          cycles++;
          if ((oper & 0xFF00) != (pc_reg & 0xFF00)) {
            cycles++;
          }
          pc_reg = oper;
        }
        break;
      case 15: // INSN_BNE
        if (!z_flag) {
          cycles++;
          if ((oper & 0xFF00) != (pc_reg & 0xFF00)) {
            cycles++;
          }
          pc_reg = oper;
        }
        break;
      case 16: // INSN_BPL
        if (!n_flag) {
          cycles++;
          if ((oper & 0xFF00) != (pc_reg & 0xFF00)) {
            cycles++;
          }
          pc_reg = oper;
        }
        break;
      case 17: // INSN_BRK
        /* RTI from break causes the next instruction to be ignored */
        pc_reg++;
        mem[s_reg] = (pc_reg) >> 8;
        s_reg = 0x100 | ((s_reg - 1) & 0xFF);
        mem[s_reg] = (pc_reg) & 0xFF;
        s_reg = 0x100 | ((s_reg - 1) & 0xFF);
        b_flag = 1;
        p_reg = 32 | 16; // R_FLAG | B_FLAG
        if (c_flag) p_reg |= 1;
        if (z_flag) p_reg |= 2;
        if (i_flag) p_reg |= 4;
        if (d_flag) p_reg |= 8;
        if (v_flag) p_reg |= 64;
        if (n_flag) p_reg |= 128;
        mem[s_reg] = p_reg;
        s_reg = 0x100 | ((s_reg - 1) & 0xFF);
        i_flag = 1;
        pc_reg = (mem[0xFFFE] | (mem[0xFFFF]<<8));
        break;
      case 18: // INSN_BVC
        if (!v_flag) {
          cycles++;
          if ((oper & 0xFF00) != (pc_reg & 0xFF00)) {
            cycles++;
          }
          pc_reg = oper;
        }
        break;
      case 19: // INSN_BVS
        if (v_flag) {
          cycles++;
          if ((oper & 0xFF00) != (pc_reg & 0xFF00)) {
            cycles++;
          }
          pc_reg = oper;
        }
        break;
      case 20: // INSN_CLC
        c_flag = 0;
        break;
      case 21: // INSN_CLD
        d_flag = 0;
        break;
      case 22: // INSN_CLI
        i_flag = 0;
        if (this.int_pending && count > cycles) {
          this.int_pending = false;
          p_reg = 32; // R_FLAG
          if (c_flag) p_reg |= 1;
          if (z_flag) p_reg |= 2;
          if (d_flag) p_reg |= 8;
          if (b_flag) p_reg |= 16;
          if (v_flag) p_reg |= 64;
          if (n_flag) p_reg |= 128;
          this.cyclesToHalt += 7;
          mem[s_reg] = (pc_reg) >> 8;
          s_reg = 0x100 | ((s_reg - 1) & 0xFF);
          mem[s_reg] = (pc_reg) & 0xFF;
          s_reg = 0x100 | ((s_reg - 1) & 0xFF);
          p_reg &= ~16; // ~B_FLAG
          mem[s_reg] = p_reg;
          s_reg = 0x100 | ((s_reg - 1) & 0xFF);
          p_reg |= 4; // I_FLAG
          pc_reg = (mem[0xFFFE] | (mem[0xFFFF]<<8));
        }
        break;
      case 23: // INSN_CLV
        v_flag = 0;
        break;
      case 24: // INSN_CMP
        oper = a_reg - oper;
        c_flag = (oper >= 0);
        oper &= 0xff;
        z_flag = (oper == 0); n_flag = (oper & 0x80);
        break;
      case 25: // INSN_CPX
        oper = x_reg - oper;
        c_flag = (oper >= 0);
        oper &= 0xff;
        z_flag = (oper == 0); n_flag = (oper & 0x80);
        break;
      case 26: // INSN_CPY
        oper = y_reg - oper;
        c_flag = (oper >= 0);
        oper &= 0xff;
        z_flag = (oper == 0); n_flag = (oper & 0x80);
        break;
      case 27: // INSN_DCP - Undocumented
        oper = (oper - 1) & 0xFF;
        this.write(operp, oper);
        oper = a_reg - oper;
        c_flag (oper < 0x100);
        oper &= 0xff;
        z_flag = (oper == 0); n_flag = (oper & 0x80);
        break;
      case 28: // INSN_DEC
        oper = (oper - 1) & 0xFF;
        z_flag = (oper == 0); n_flag = (oper & 0x80);
        this.write(operp, oper);
        break;
      case 29: // INSN_DEX
        x_reg = (x_reg - 1) & 0xFF;
        z_flag = (x_reg == 0); n_flag = (x_reg & 0x80);
        break;
      case 30: // INSN_DEY
        y_reg = (y_reg - 1) & 0xFF;
        z_flag = (y_reg == 0); n_flag = (y_reg & 0x80);
        break;
      case 31: // INSN_DOP - Undocumented
        /* Do nothing */
        break;
      case 32: // INSN_EOR
        a_reg ^= oper;
        z_flag = (a_reg == 0); n_flag = (a_reg & 0x80);
        break;
      case 33: // INSN_HLT
        cycles = count;
        this.halted = true;
        break;
      case 34: // INSN_INC
        oper = (oper + 1) & 0xFF;
        z_flag = (oper == 0); n_flag = (oper & 0x80);
        this.write(operp, oper);
        break;
      case 35: // INSN_INX
        x_reg = (x_reg + 1) & 0xFF;
        z_flag = (x_reg == 0); n_flag = (x_reg & 0x80);
        break;
      case 36: // INSN_INY
        y_reg = (y_reg + 1) & 0xFF;
        z_flag = (y_reg == 0); n_flag = (y_reg & 0x80);
        break;
      case 37: // INSN_ISC - Undocumented
        oper = (oper + 1) & 0xFF;
        this.write(operp, oper);
        t = a_reg - oper;
        if (!c_flag) t--;
        c_flag = (t < 0x100);
        v_flag = (((a_reg ^ oper) & 0x80) && ((a_reg ^ t) & 0x80));
        a_reg = t & 0xFF;
        z_flag = (a_reg == 0); n_flag = (a_reg & 0x80);
        break;
      case 38: // INSN_JMP
        pc_reg = operp;
        break;
      case 39: // INSN_JSR
        pc_reg--;
        mem[s_reg] = (pc_reg) >> 8;
        s_reg = 0x100 | ((s_reg - 1) & 0xFF);
        mem[s_reg] = (pc_reg) & 0xFF;
        s_reg = 0x100 | ((s_reg - 1) & 0xFF);
        pc_reg = operp;
        break;
      case 40: // INSN_LAR - Undocumented
        a_reg = x_reg = ((s_reg) & oper);
        s_reg = a_reg | 0x100;
        z_flag = (a_reg == 0); n_flag = (a_reg & 0x80);
        break;
      case 41: // INSN_LAX - Undocumented
        a_reg = x_reg = oper;
        z_flag = (a_reg == 0); n_flag = (a_reg & 0x80);
        break;
      case 42: // INSN_LDA
        a_reg = oper;
        z_flag = (a_reg == 0); n_flag = (a_reg & 0x80);
        break;
      case 43: // INSN_LDX
        x_reg = oper;
        z_flag = (x_reg == 0); n_flag = (x_reg & 0x80);
        break;
      case 44: // INSN_LDY
        y_reg = oper;
        z_flag = (y_reg == 0); n_flag = (y_reg & 0x80);
        break;
      case 45: // INSN_LSR
        c_flag = (oper & 0x01);
        oper >>= 1;
        z_flag = (oper == 0);
        n_flag = (0);
        if (addressing == 0) a_reg = oper; else this.write(operp, oper);
        break;
      case 46: // INSN_NOP
        break;
      case 47: // INSN_ORA
        a_reg |= oper;
        z_flag = (a_reg == 0); n_flag = (a_reg & 0x80);
        break;
      case 48: // INSN_PHA
        mem[s_reg] = a_reg;
        s_reg = 0x100 | ((s_reg - 1) & 0xFF);
        break;
      case 49: // INSN_PHP
        p_reg = 32; // R_FLAG
        if (c_flag) p_reg |= 1;
        if (z_flag) p_reg |= 2;
        if (i_flag) p_reg |= 4;
        if (d_flag) p_reg |= 8;
        if (b_flag) p_reg |= 16;
        if (v_flag) p_reg |= 64;
        if (n_flag) p_reg |= 128;
        mem[s_reg] = p_reg;
        s_reg = 0x100 | ((s_reg - 1) & 0xFF);
        break;
      case 50: // INSN_PLA
        s_reg = 0x100 | ((s_reg + 1) & 0xFF);
        a_reg = mem[s_reg];
        z_flag = (a_reg == 0); n_flag = (a_reg & 0x80);
        break;
      case 51: // INSN_PLP
        s_reg = 0x100 | ((s_reg + 1) & 0xFF);
        p_reg = mem[s_reg];
        c_flag = p_reg & 1;
        z_flag = p_reg & 2;
        i_flag = p_reg & 4;
        d_flag = p_reg & 8;
        b_flag = p_reg & 16;
        v_flag = p_reg & 64;
        n_flag = p_reg & 128;
        break;
      case 52: // INSN_RLA - Undocumented
        oper <<= 1;
        if (c_flag) oper |= 0x01;
        c_flag = (oper & 0x100);
        oper = oper & 0xFF;
        this.write(operp, oper);
        a_reg &= oper;
        z_flag = (a_reg == 0); n_flag = (a_reg & 0x80);
        break;
      case 53: // INSN_ROL
        oper <<= 1;
        if (c_flag) oper |= 0x01;
        c_flag = (oper & 0x100);
        oper = oper & 0xFF;
        z_flag = (oper == 0); n_flag = (oper & 0x80);
        if (addressing == 0) a_reg = oper; else this.write(operp, oper);
        break;
      case 54: // INSN_ROR
        if (c_flag) oper |= 0x100;
        c_flag = (oper & 0x01);
        oper >>= 1;
        z_flag = (oper == 0); n_flag = (oper & 0x80);
        if (addressing == 0) a_reg = oper; else this.write(operp, oper);
        break;
      case 55: // INSN_RRA - Undocumented
        if (c_flag) oper |= 0x100;
        c_flag = (oper & 0x01);
        oper >>= 1;
        this.write(operp, oper);
        t = oper + a_reg;
        if (c_flag) t++;
        c_flag = (t & 0x100);
        v_flag = (!((a_reg ^ oper) & 0x80) && ((a_reg ^ t) & 0x80));
        a_reg = t & 0xFF;
        z_flag = (a_reg == 0); n_flag = (a_reg & 0x80);
        break;
      case 56: // INSN_RTI
        s_reg = 0x100 | ((s_reg + 1) & 0xFF);
        p_reg = mem[s_reg];
        c_flag = p_reg & 1;
        z_flag = p_reg & 2;
        i_flag = p_reg & 4;
        d_flag = p_reg & 8;
        b_flag = p_reg & 16;
        v_flag = p_reg & 64;
        n_flag = p_reg & 128;
        s_reg = 0x100 | ((s_reg + 1) & 0xFF);
        pc_reg = mem[s_reg];
        s_reg = 0x100 | ((s_reg + 1) & 0xFF);
        pc_reg |= mem[s_reg] << 8;
        if (!i_flag && this.int_pending && count > cycles) {
          this.int_pending = false;
          this.cyclesToHalt += 7;
          mem[s_reg] = (pc_reg) >> 8;
          s_reg = 0x100 | ((s_reg - 1) & 0xFF);
          mem[s_reg] = (pc_reg) & 0xFF;
          s_reg = 0x100 | ((s_reg - 1) & 0xFF);
          p_reg &= ~16; // ~B_FLAG
          mem[s_reg] = p_reg;
          s_reg = 0x100 | ((s_reg - 1) & 0xFF);
          p_reg |= 4; // I_FLAG
          pc_reg = (mem[0xFFFE] | (mem[0xFFFF]<<8));
        }
        break;
      case 57: // INSN_RTS
        s_reg = 0x100 | ((s_reg + 1) & 0xFF);
        pc_reg = mem[s_reg];
        s_reg = 0x100 | ((s_reg + 1) & 0xFF);
        pc_reg |= mem[s_reg] << 8;
        pc_reg++;
        break;
      case 58: // INSN_SBC
        t = a_reg - oper;
        if (!c_flag) t--;
        c_flag = (t >= 0);
        v_flag = (((a_reg ^ oper) & 0x80) && ((a_reg ^ t) & 0x80));
        a_reg = t & 0xFF;
        z_flag = (a_reg == 0); n_flag = (a_reg & 0x80);
        break;
      case 59: // INSN_SEC
        c_flag = 1;
        break;
      case 60: // INSN_SED
        d_flag = 1;
        break;
      case 61: // INSN_SEI
        i_flag = 1;
        break;
      case 62: // INSN_SLO - Undocumented
        c_flag = (oper & 0x80);
        oper = (oper << 1) & 0xFF;
        this.write(operp, oper);
        a_reg |= oper;
        z_flag = (a_reg == 0); n_flag = (a_reg & 0x80);
        break;
      case 63: // INSN_SRE - Undocumented
        c_flag = (oper & 0x01);
        oper >>= 1;
        this.write(operp, oper);
        a_reg ^= oper;
        z_flag = (a_reg == 0); n_flag = (a_reg & 0x80);
        break;
      case 64: // INSN_STA
        this.write (operp, a_reg);
        break;
      case 65: // INSN_STX
        this.write (operp, x_reg);
        break;
      case 66: // INSN_STY
        this.write (operp, y_reg);
        break;
      case 67: // INSN_SXA - Undocumented
        oper = x_reg & ((operp >> 8) + 1); /* Unpredictable */
        this.write(operp, oper);
        break;
      case 68: // INSN_SYA - Undocumented
        oper = y_reg & ((operp >> 8) + 1); /* Unpredictable */
        this.write(operp, oper);
        break;
      case 69: // INSN_TAX
        x_reg = a_reg;
        z_flag = (x_reg == 0); n_flag = (x_reg & 0x80);
        break;
      case 70: // INSN_TAY
        y_reg = a_reg;
        z_flag = (y_reg == 0); n_flag = (y_reg & 0x80);
        break;
      case 71: // INSN_TOP - Undocumented
        /* Do nothing */
        break;
      case 72: // INSN_TSX
        x_reg = s_reg & 0xFF;
        z_flag = (x_reg == 0); n_flag = (x_reg & 0x80);
        break;
      case 73: // INSN_TXA
        a_reg = x_reg;
        z_flag = (a_reg == 0); n_flag = (a_reg & 0x80);
        break;
      case 74: // INSN_TXS
        s_reg = x_reg | 0x100;
        break;
      case 75: // INSN_TYA
        a_reg = y_reg;
        z_flag = (a_reg == 0); n_flag = (a_reg & 0x80);
        break;
      case 76: // INSN_XAA - Undocumented
        a_reg = (a_reg | 0xEE) & x_reg & oper;
        z_flag = (a_reg == 0); n_flag = (a_reg & 0x80);
        break;
      case 77: // INSN_XAS - Undocumented
        s_reg = x_reg & a_reg;
        oper = s_reg & ((operp >> 8) + 1);
        s_reg |= 0x100;
        this.write(operp, oper);
        break;
      }
    }

    p_reg = 32; // R_FLAG
    if (c_flag) p_reg |= 1;
    if (z_flag) p_reg |= 2;
    if (i_flag) p_reg |= 4;
    if (d_flag) p_reg |= 8;
    if (b_flag) p_reg |= 16;
    if (v_flag) p_reg |= 64;
    if (n_flag) p_reg |= 128;
    this.a_reg = a_reg;
    this.x_reg = x_reg; this.y_reg = y_reg;
    this.pc_reg = pc_reg; this.p_reg = p_reg;
    this.s_reg = s_reg;
    return cycles;
  },

  visit: function(address) {
    var region = this.memRegion[address];
    var labels = new Array();
    var visited = new Array();
    var opdata = this.opdata.opdata;
    var insndetails = this.opdata.insndetails;
    var used = this.opdata.used;
    var chg = this.opdata.chg;
    var mem = this.mem;

    labels.push(address);
    this.innerLabel[address] = 0;
    for(var j = 0; j < labels.length; j++) {
      var pc = labels[j];
      while(true) {
        if (this.ownerFunction[pc] === address) break;
        visited.push(pc);
        this.ownerFunction[pc] = address;
        this.usedResources[pc] = undefined;
        this.followStatus[pc] = 0;
        var opc = mem[pc];
        var opcode = opdata[opc];
        var addressing = (opcode >> 8) & 0xFF;
        var insn = opcode & 0xFF;
        var len = (opcode >> 16) & 0xFF;
        var details = insndetails[insn];
        var target = undefined;

        if (details & this.opdata.I_JP) {
          var isbranch = false;
          this.usedResources[pc] = -1;
          switch (addressing) {
          case 5: // ADDR_ABSOLUTE
            target = (mem[pc + 1] | (mem[pc + 2]<<8));
            break;
          case 11: // ADDR_RELATIVE
            t = mem[pc + 1];
            if (t & 0x80) t |= 0xFF00;
            target = (pc + t + 2) & 0xFFFF;
            isbranch = true;
            break;
          }
          if (target !== undefined) {
            if (this.memRegion[target] === region &&
                (this.ownerFunction[target] === undefined || this.ownerFunction[target] === address)) {
              if (this.innerLabel[target] === undefined) {
                this.innerLabel[target] = labels.length;
                labels.push(target);
              }
              this.followStatus[pc] |= 2;
            }
          }
          if (!isbranch && insn != this.opdata.INSN_JSR) break;
        }
        var oldpc = pc;
        pc += len;
        pc &= 0xFFFF;
        if ((this.ownerFunction[pc] !== undefined && this.ownerFunction[pc] !== address)||
            this.memRegion[pc] !== region) {
          if (insn != this.opdata.INSN_JSR) {
            this.followStatus[oldpc] |= 1;
          }
          this.usedResources[oldpc] = -1;
          break;
        }
        if (insn == this.opdata.INSN_JSR) {
          if (this.innerLabel[pc] === undefined) {
            this.innerLabel[pc] = labels.length;
            labels.push(pc);
          }
        }
      }
    }
    for(var i = visited.length - 1; i >= 0; i--) {
      pc = visited[i];
      opc = mem[pc];
      opcode = opdata[opc];
      insn = opcode & 0xFF;
      if (this.usedResources[pc] === undefined) {
        len = (opcode >> 16) & 0xFF;
        this.chgResources[pc] = chg[insn] & this.usedResources[pc + len];
        this.usedResources[pc] = (this.usedResources[pc + len] & (~chg[insn])) | used[insn];
      } else {
        this.chgResources[pc] = -1;
      }
    }
    return visited;
  },

  translate: function(address) {
    if (this.ownerFunction[address] !== undefined) return;
    var visited = this.visit(address);
    visited.sort();

    var out = new JSNES.CPU.CodeBuffer(this);

    var R_A = this.opdata.R_A;
    var R_X = this.opdata.R_X;
    var R_Y = this.opdata.R_Y;
    var R_S = this.opdata.R_S;

    var F_C = this.opdata.F_C;
    var F_Z = this.opdata.F_Z; 
    var F_I = this.opdata.F_I; 
    var F_D = this.opdata.F_D; 
    var F_B = this.opdata.F_B; 
    var F_R = this.opdata.F_R; 
    var F_V = this.opdata.F_V; 
    var F_N = this.opdata.F_N;

    out.startFunction();

    for(var i = 0; i < visited.length; i++) {
      var pc = visited[i];
      var insn = out.startOpcode(pc);

      switch (insn) {
      case 0: // INSN_AAC - Undocumented
        out.useOperIf(R_A | F_C | F_Z | F_N);
        out.appendIf(R_A | F_C | F_Z | F_N, 'a_reg &= ' + out.operr + ';\n');
        out.appendCheckZeroAndSign('a_reg');
        out.appendIf(F_C, 'c_flag = (a_reg == 0);\n');
        break;
      case 1: // INSN_AAX - Undocumented
        out.useOper();
        out.appendWriteback('x_reg & a_reg');
        break;
      case 2: // INSN_ADC
        out.useOperIf(R_A | F_C | F_Z | F_N | F_V);
        out.appendIf(R_A | F_C | F_Z | F_N | F_V, 't1 = ' + out.operr + ';\n');
        out.appendIf(R_A | F_C | F_Z | F_N | F_V, 't2 = t1 + a_reg;\n');
        out.appendIf(R_A | F_C | F_Z | F_N | F_V, 'if (c_flag) t2++;\n');
        out.appendIf(F_C, 'c_flag = (t2 & 0x100);\n');
        out.appendIf(F_V, 'v_flag = (!((a_reg ^ t1) & 0x80) && ((a_reg ^ t2) & 0x80));\n');
        out.appendIf(R_A, 'a_reg = t2 & 0xFF;\n');
        out.appendCheckZeroAndSign('a_reg');
        break;
      case 3: // INSN_AND
        out.useOperIf(R_A | F_Z | F_N);
        out.appendIf(R_A | F_Z | F_N, 'a_reg &= ' + out.operr + ';\n');
        out.appendCheckZeroAndSign('a_reg');
        break;
      case 4: // INSN_ARR - Undocumented
        out.useOperIf(R_A | F_C | F_V | F_Z | F_N);
        out.appendIf(R_A | F_C | F_V | F_Z | F_N, 'a_reg &= ' + out.operr + ';\n');
        out.append(R_A | F_C | F_V | F_Z | F_N, 'a_reg >>= 1;\n');
        out.append(R_A | F_C | F_V | F_Z | F_N, 'if (c_flag) a_reg |= 0x80;\n');
        out.append(F_C, 'c_flag = (a_reg & 0x40);\n');
        out.append(F_V, 'v_flag = (((a_reg >> 1) ^ a_reg) & 0x20);\n');
        out.appendCheckZeroAndSign('a_reg');
        break;
      case 5: // INSN_ASL
        out.useOper();
        out.append('t1 = ' + out.operr + ';\n');
        out.appendIf(F_C, 'c_flag = (t1 & 0x80);\n');
        out.append('t1 = (t1 << 1) & 0xFF;\n');
        out.appendCheckZeroAndSign('t1');
        out.appendWriteback('t1');
        break;
      case 6: // INSN_ASR - Undocumented
        out.useOperIf(R_A | F_C | F_Z);
        out.appendIf(R_A | F_C | F_Z, 'a_reg &= ' + out.operr + ';\n');
        out.appendIf(F_C, 'c_flag = (a_reg & 0x01);\n');
        out.appendIf(R_A | F_Z, 'a_reg >>= 1;\n');
        out.appendIf(F_Z, 'z_flag = (a_reg == 0);\n');
        out.appendIf(F_N, 'n_flag = (0);\n');
        break;
      case 7: // INSN_ATX - Undocumented
        out.useOperIf(R_A | R_X | F_Z | F_N);
        out.appendIf(R_A | R_X | F_Z | F_N, 't1 = ' + out.operr + ';\n');
        out.appendIf(R_A | R_X, 't2 = ((a_reg | 0xEE) & t1);\n');
        out.appendIf(R_A, 'a_reg = t2;\n');
        out.appendIf(R_X, 'x_reg = t2;\n');
        out.appendCheckZeroAndSign('t1');
        break;
      case 8: // INSN_AXA - Undocumented
        out.useOper();
        out.append('t1 = a_reg & x_reg & (((operp >> 8) + 1));\n');
        out.appendWriteback('t1');
        break;
      case 9: // INSN_AXS - Undocumented
        out.useOper();
        out.append('x_reg = ((a_reg & x_reg) - ' + out.operr + ');\n');
        out.appendIf(F_C, 'c_flag = (x_reg < 0x100);\n');
        out.append('x_reg &= 0xFF;\n');
        out.appendCheckZeroAndSign('x_reg');
        break;
      case 10: // INSN_BCC
        out.appendBranch('!c_flag');
        break;
      case 11: // INSN_BCS
        out.appendBranch('c_flag');
        break;
      case 12: // INSN_BEQ
        out.appendBranch('z_flag');
        break;
      case 13: // INSN_BIT
        out.useOperIf(F_N | F_V | F_Z);
        out.appendIf(F_N | F_V | F_Z, 't1 = ' + out.operr + ';\n');
        out.appendIf(F_N, 'n_flag = (t1 & 0x80);\n');
        out.appendIf(F_V, 'v_flag = (t1 & 0x40);\n');
        out.appendIf(F_Z, 'z_flag = ((t1 & a_reg) == 0);\n');
        break;
      case 14: // INSN_BMI
        out.appendBranch('n_flag');
        break;
      case 15: // INSN_BNE
        out.appendBranch('!z_flag');
        break;
      case 16: // INSN_BPL
        out.appendBranch('!n_flag');
        break;
      case 17: // INSN_BRK
        /* RTI from break causes the next instruction to be ignored */
        out.appendPush16(pc + 2);
        out.append('b_flag = 1;\n');
        out.appendCompactFlags(-1);
        out.appendPush('p_reg');
        out.append('i_flag = 1;\n');
        out.append('pc_reg = (mem[0xFFFE] | (mem[0xFFFF]<<8));\n');
        break;
      case 18: // INSN_BVC
        out.appendBranch('!v_flag');
        break;
      case 19: // INSN_BVS
        out.appendBranch('v_flag');
        break;
      case 20: // INSN_CLC
        out.appendIf(F_C, 'c_flag = 0;\n');
        break;
      case 21: // INSN_CLD
        out.appendIf(F_D, 'd_flag = 0;\n');
        break;
      case 22: // INSN_CLI
        out.appendIf(F_I, 'i_flag = 0;\n');
        out.appendIrqProc();
        break;
      case 23: // INSN_CLV
        out.appendIf(F_V, 'v_flag = (0);\n');
        break;
      case 24: // INSN_CMP
        out.useOperIf(F_C | F_Z | F_N);
        out.appendIf(F_C | F_Z | F_N, 't1 = ' + out.operr + ';\n');
        out.appendIf(F_C | F_Z | F_N, 't1 = a_reg - t1;\n');
        out.appendIf(F_C, 'c_flag = (t1 >= 0);\n');
        out.appendIf(F_Z | F_N, 't1 &= 0xff;\n');
        out.appendCheckZeroAndSign('t1');
        break;
      case 25: // INSN_CPX
        out.useOperIf(F_C | F_Z | F_N);
        out.appendIf(F_C | F_Z | F_N, 't1 = ' + out.operr + ';\n');
        out.appendIf(F_C | F_Z | F_N, 't1 = x_reg - t1;\n');
        out.appendIf(F_C, 'c_flag = (t1 >= 0);\n');
        out.appendIf(F_Z | F_N, 't1 &= 0xff;\n');
        out.appendCheckZeroAndSign('t1');
        break;
      case 26: // INSN_CPY
        out.useOperIf(F_C | F_Z | F_N);
        out.appendIf(F_C | F_Z | F_N, 't1 = ' + out.operr + ';\n');
        out.appendIf(F_C | F_Z | F_N, 't1 = y_reg - t1;\n');
        out.appendIf(F_C, 'c_flag = (t1 >= 0);\n');
        out.appendIf(F_Z | F_N, 't1 &= 0xff;\n');
        out.appendCheckZeroAndSign('t1');
        break;
      case 27: // INSN_DCP - Undocumented
        out.useOper();
        out.append('t1 = ' + out.operr + ';\n');
        out.append('t1 = (t1 - 1) & 0xFF;\n');
        out.appendWriteback('t1');
        out.appendIf(F_Z | F_N | F_C, 't1 = a_reg - t1;\n');
        out.appendIf(F_C, 'c_flag = (t1 < 0x100);\n');
        out.appendIf(F_Z | F_N, 't1 &= 0xff;\n');
        out.appendCheckZeroAndSign('t1');
        break;
      case 28: // INSN_DEC
        out.useOper();
        out.append('t1 = ' + out.operr + ';\n');
        out.append('t1 = (t1 - 1) & 0xFF;\n');
        out.appendCheckZeroAndSign('t1');
        out.appendWriteback('t1');
        break;
      case 29: // INSN_DEX
        out.appendIf(R_X | F_Z | F_N, 'x_reg = (x_reg - 1) & 0xFF;\n');
        out.appendCheckZeroAndSign('x_reg');
        break;
      case 30: // INSN_DEY
        out.appendIf(R_Y | F_Z | F_N, 'y_reg = (y_reg - 1) & 0xFF;\n');
        out.appendCheckZeroAndSign('y_reg');
        break;
      case 31: // INSN_DOP - Undocumented
        /* Do nothing */
        break;
      case 32: // INSN_EOR
        out.useOperIf(R_A | F_Z | F_N);
        out.appendIf(R_A | F_Z | F_N, 'a_reg ^= ' + out.operr + ';\n');
        out.appendCheckZeroAndSign('a_reg');
        break;
      case 33: // INSN_HLT
        out.append('cycles = 0;\n');
        out.append('this.halted = true;\n');
        out.appendExit();
        break;
      case 34: // INSN_INC
        out.useOper();
        out.append('t1 = ' + out.operr + ';\n');
        out.append('t1 = (t1 + 1) & 0xFF;\n');
        out.appendCheckZeroAndSign('t1');
        out.appendWriteback('t1');
        break;
      case 35: // INSN_INX
        out.appendIf(R_X | F_Z | F_N, 'x_reg = (x_reg + 1) & 0xFF;\n');
        out.appendCheckZeroAndSign('x_reg');
        break;
      case 36: // INSN_INY
        out.appendIf(R_Y | F_Z | F_N, 'y_reg = (y_reg + 1) & 0xFF;\n');
        out.appendCheckZeroAndSign('y_reg');
        break;
      case 37: // INSN_ISC - Undocumented
        out.useOper();
        out.append('t1 = ' + out.operr + ';\n');
        out.append('t1 = (t1 + 1) & 0xFF;\n');
        out.appendWriteback('t1');
        out.append('t2 = a_reg - t1;\n');
        out.append('if (!c_flag) t2--;\n');
        out.appendIf(F_C, 'c_flag = (t2 < 0x100);\n');
        out.appendIf(F_V, 'v_flag = (((a_reg ^ t1) & 0x80) && ((a_reg ^ t2) & 0x80));\n');
        out.appendIf(R_A | F_Z | F_N, 'a_reg = t & 0xFF;\n');
        out.appendCheckZeroAndSign('a_reg');
        break;
      case 38: // INSN_JMP
        out.useOper();
        out.append('pc_reg = ' + out.operr + ';\n');
        out.appendJump();
        break;
      case 39: // INSN_JSR
        out.useOper();
        out.appendPush16(pc + 2);
        out.append('pc_reg = ' + out.operr + ';\n');
        out.appendJump();
        break;
      case 40: // INSN_LAR - Undocumented
        out.useOper();
        out.append('a_reg = x_reg = ((s_reg) & ' + out.operr + ');\n');
        out.append('s_reg = a_reg | 0x100;\n');
        out.appendCheckZeroAndSign('a_reg');
        break;
      case 41: // INSN_LAX - Undocumented
        out.useOperIf(R_A | R_X | F_Z | F_N);
        out.appendIf(R_A | R_X | F_Z | F_N, 't1 = ' + out.operr + ';\n');
        out.appendIf(R_A, 'a_reg = t1;\n');
        out.appendIf(R_X, 'x_reg = t1;\n');
        out.appendCheckZeroAndSign('t1');
        break;
      case 42: // INSN_LDA
        out.useOperIf(R_A | F_Z | F_N);
        out.appendIf(R_A | F_Z | F_N, 'a_reg = ' + out.operr + ';\n');
        out.appendCheckZeroAndSign('a_reg');
        break;
      case 43: // INSN_LDX
        out.useOperIf(R_X | F_Z | F_N);
        out.appendIf(R_X | F_Z | F_N, 'x_reg = ' + out.operr + ';\n');
        out.appendCheckZeroAndSign('x_reg');
        break;
      case 44: // INSN_LDY
        out.useOperIf(R_Y | F_Z | F_N);
        out.appendIf(R_Y | F_Z | F_N, 'y_reg = ' + out.operr + ';\n');
        out.appendCheckZeroAndSign('y_reg');
        break;
      case 45: // INSN_LSR
        out.useOper();
        out.append('t1 = ' + out.operr + ';\n');
        out.appendIf(F_C, 'c_flag = (t1 & 0x01);\n');
        out.append('t1 >>= 1;\n');
        out.appendIf(F_Z, 'z_flag = (t1 == 0);\n');
        out.appendIf(F_N, 'n_flag = (0);\n');
        out.appendWriteback('t1');
        break;
      case 46: // INSN_NOP
        break;
      case 47: // INSN_ORA
        out.useOperIf(R_A | F_Z | F_N);
        out.appendIf(R_A | F_Z | F_N, 'a_reg |= ' + out.operr + ';\n');
        out.appendCheckZeroAndSign('a_reg');
        break;
      case 48: // INSN_PHA
        out.appendPush('a_reg');
        break;
      case 49: // INSN_PHP
        out.appendCompactFlags(-1);
        out.appendPush('p_reg');
        break;
      case 50: // INSN_PLA
        out.appendPull('a_reg');
        out.appendCheckZeroAndSign('a_reg');
        break;
      case 51: // INSN_PLP
        out.appendPull('p_reg');
        out.appendExpandFlags(-1);
        break;
      case 52: // INSN_RLA - Undocumented
        out.useOper();
        out.append('t1 = ' + out.operr + ';\n');
        out.append('t1 <<= 1;\n');
        out.append('if (c_flag) t1 |= 0x01;\n');
        out.appendIf(F_C, 'c_flag = (t1 & 0x100);\n');
        out.append('t1 = t1 & 0xFF;\n');
        out.appendWriteback('t1');
        out.appendIf(R_A | F_Z | F_N, 'a_reg &= t1;\n');
        out.appendCheckZeroAndSign('a_reg');
        break;
      case 53: // INSN_ROL
        out.useOper();
        out.append('t1 = ' + out.operr + ';\n');
        out.append('t1 <<= 1;\n');
        out.append('if (c_flag) t1 |= 0x01;\n');
        out.appendIf(F_C, 'c_flag = (t1 & 0x100);\n');
        out.append('t1 = t1 & 0xFF;\n');
        out.appendCheckZeroAndSign('t1');
        out.appendWriteback('t1');
        break;
      case 54: // INSN_ROR
        out.useOper();
        out.append('t1 = ' + out.operr + ';\n');
        out.append('if (c_flag) t1 |= 0x100;\n');
        out.appendIf(F_C, 'c_flag = (t1 & 0x01);\n');
        out.append('t1 >>= 1;\n');
        out.appendCheckZeroAndSign('t1');
        out.appendWriteback('t1');
        break;
      case 55: // INSN_RRA - Undocumented
        out.useOper();
        out.append('t1 = ' + out.operr + ';\n');
        out.append('if (c_flag) t1 |= 0x100;\n');
        out.appendIf(F_C, 'c_flag = (t1 & 0x01);\n');
        out.append('t1 >>= 1;\n');
        out.appendWriteback('t1');
        out.appendIf(R_A | F_Z | F_N | F_C | F_V, 't2 = t1 + a_reg;\n');
        out.appendIf(R_A | F_Z | F_N | F_C | F_V, 'if (c_flag) t2++;\n');
        out.appendIf(F_C, 'c_flag = (t2 & 0x100);\n');
        out.appendIf(F_V, 'v_flag = (!((a_reg ^ t1) & 0x80) && ((a_reg ^ t2) & 0x80));\n');
        out.appendIf(R_A | F_Z | F_N, 'a_reg = t2 & 0xFF;\n');
        out.appendCheckZeroAndSign('a_reg');
        break;
      case 56: // INSN_RTI
        out.appendPull('p_reg');
        out.appendExpandFlags(-1);
        out.appendPull16('pc_reg');
        out.append('if (!i_flag) {\n');
        out.appendIrqProc();
        out.append('}\n');
        out.appendExit();
        break;
      case 57: // INSN_RTS
        out.appendPull16('pc_reg');
        out.append('pc_reg++;\n');
        out.appendExit();
        break;
      case 58: // INSN_SBC
        out.useOperIf(R_A | F_C | F_V | F_Z | F_N);
        out.appendIf(R_A | F_C | F_V | F_Z | F_N, 't1 = ' + out.operr + ';\n');
        out.appendIf(R_A | F_C | F_V | F_Z | F_N, 't2 = a_reg - t1;\n');
        out.appendIf(R_A | F_C | F_V | F_Z | F_N, 'if (!c_flag) t2--;\n');
        out.appendIf(F_C, 'c_flag = (t2 >= 0);\n');
        out.appendIf(F_V, 'v_flag = (((a_reg ^ t1) & 0x80) && ((a_reg ^ t2) & 0x80));\n');
        out.appendIf(R_A | F_Z | F_N, 'a_reg = t2 & 0xFF;\n');
        out.appendCheckZeroAndSign('a_reg');
        break;
      case 59: // INSN_SEC
        out.appendIf(F_C, 'c_flag = 1;\n');
        break;
      case 60: // INSN_SED
        out.appendIf(F_D, 'd_flag = 1;\n');
        break;
      case 61: // INSN_SEI
        out.appendIf(F_I, 'i_flag = 1;\n');
        break;
      case 62: // INSN_SLO - Undocumented
        out.useOper();
        out.append('t1 = ' + out.operr + ';\n');
        out.appendIf(F_C, 'c_flag = (t1 & 0x80);\n');
        out.append('t1 = (t1 << 1) & 0xFF;\n');
        out.appendWriteback('t1');
        out.appendIf(R_A | F_Z | F_N, 'a_reg |= t1;\n');
        out.appendCheckZeroAndSign('a_reg');
        break;
      case 63: // INSN_SRE - Undocumented
        out.useOper();
        out.append('t1 = ' + out.operr + ';\n');
        out.appendIf(F_C, 'c_flag = (t1 & 0x01);\n');
        out.append('t1 >>= 1;\n');
        out.appendWriteback('t1');
        out.appendIf(R_A | F_Z | F_N, 'a_reg ^= t1;\n');
        out.appendCheckZeroAndSign('a_reg');
        break;
      case 64: // INSN_STA
        out.useOper();
        out.appendWriteback('a_reg');
        break;
      case 65: // INSN_STX
        out.useOper();
        out.appendWriteback('x_reg');
        break;
      case 66: // INSN_STY
        out.useOper();
        out.appendWriteback('y_reg');
        break;
      case 67: // INSN_SXA - Undocumented
        out.useOper();
        out.append('t1 = ' + out.operr + ';\n');
        out.append('t1 = x_reg & ((t1 >> 8) + 1);\n');
        out.appendWriteback('t1');
        break;
      case 68: // INSN_SYA - Undocumented
        out.useOper();
        out.append('t1 = ' + out.operr + ';\n');
        out.append('t1 = y_reg & ((t1 >> 8) + 1);\n');
        out.appendWriteback('t1');
        break;
      case 69: // INSN_TAX
        out.appendIf(R_X, 'x_reg = a_reg;\n');
        out.appendCheckZeroAndSign('a_reg');
        break;
      case 70: // INSN_TAY
        out.appendIf(R_Y, 'y_reg = a_reg;\n');
        out.appendCheckZeroAndSign('a_reg');
        break;
      case 71: // INSN_TOP - Undocumented
        /* Do nothing */
        break;
      case 72: // INSN_TSX
        out.appendIf(R_X | F_Z | F_N, 'x_reg = s_reg & 0xFF;\n');
        out.appendCheckZeroAndSign('x_reg');
        break;
      case 73: // INSN_TXA
        out.appendIf(R_A, 'a_reg = x_reg;\n');
        out.appendCheckZeroAndSign('x_reg');
        break;
      case 74: // INSN_TXS
        out.append('s_reg = x_reg | 0x100;\n');
        break;
      case 75: // INSN_TYA
        out.appendIf(R_A, 'a_reg = y_reg;\n');
        out.appendCheckZeroAndSign('y_reg');
        break;
      case 76: // INSN_XAA - Undocumented
        out.useOperIf(R_A | F_Z | F_N);
        out.appendIf(R_A | F_Z | F_N, 'a_reg = (a_reg | 0xEE) & x_reg & ' + out.operr +';\n');
        out.appendCheckZeroAndSign('a_reg');
        break;
      case 77: // INSN_XAS - Undocumented
        out.useOper();
        out.append('t1 = ' + out.operr + ';\n');
        out.append('s_reg = x_reg & a_reg;\n');
        out.append('t1 = s_reg & ((t1 >> 8) + 1);\n');
        out.append('s_reg |= 0x100;\n');
        out.appendWriteback('t1');
        break;
      }
      out.endOpcode();
    }
    out.endFunction();
    this.cache[address] = out.output();
  },

  JSON_PROPERTIES: [
    'mem', 'ownerFunction', 'usedResources', 'chgResources', 'innerLabel', 'followStatus', 'cache', 'memRegion',
    'irq_pending', 'cyclesToHalt', 'halted',
    // Registers
    'pc_reg', 'a_reg', 'p_reg', 'x_reg', 'y_reg', 's_reg'
  ],
    
  toJSON: function() {
    return JSNES.Utils.toJSON(this);
  },
    
  fromJSON: function(s) {
    JSNES.Utils.fromJSON(this, s);
  }
}


JSNES.CPU.OpData = function() {
  this.addressingLength = new Array(1, 2, 2, 2, 2, 3, 3, 3, 3, 2, 2, 2, 1);
  // Helper Definitions
  var I_JP = this.I_JP;
  var I_ST = this.I_ST;
  var I_RD = this.I_RD;
  var I_WR = this.I_WR;
  var I_UN = this.I_UN;

  var I_JS = I_JP | I_ST;
  var I_RW = I_RD | I_WR;
  var I_UR = I_UN | I_RD;
  var I_UW = I_UN | I_WR;
  var I_UM = I_RD | I_WR | I_UN;
  var I_UP = I_UN | I_JP;

  // Now for flags
  var C_FLAG = this.F_C;
  var Z_FLAG = this.F_Z;
  var I_FLAG = this.F_I;
  var D_FLAG = this.F_D;
  var B_FLAG = this.F_B;
  var R_FLAG = this.F_R;
  var V_FLAG = this.F_V;
  var N_FLAG = this.F_N;

  var BI_FLAGS     = B_FLAG       | I_FLAG;
  var ZN_FLAGS     = Z_FLAG       | N_FLAG;
  var ZNV_FLAGS    = ZN_FLAGS     | V_FLAG;
  var CZN_FLAGS    = ZN_FLAGS     | C_FLAG;
  var CZNV_FLAGS   = CZN_FLAGS    | V_FLAG;
  var CZNVDI_FLAGS = CZNV_FLAGS   | D_FLAG | I_FLAG;
  var ALL_FLAGS    = CZNVDI_FLAGS | B_FLAG;

  // Now for registers
  var R_A = this.R_A;
  var R_X = this.R_X;
  var R_Y = this.R_Y;
  var R_S = this.R_S;

  var R_AX  = R_A | R_X;
  var R_AXS = R_A | R_X | R_S;

  this.insnname =    new Array(this.INSN_TOTAL);
  this.insndetails = new Array(this.INSN_TOTAL);
  this.used =        new Array(this.INSN_TOTAL);
  this.chg =         new Array(this.INSN_TOTAL);

  this.index = 0;
  this.setInsn("AAC", I_UN , 0   , R_A  , CZN_FLAGS  , 0           );
  this.setInsn("AAX", I_UW , 0   , R_AX , 0          , 0           );
  this.setInsn("ADC", I_RD , R_A , R_A  , CZNV_FLAGS , C_FLAG      );
  this.setInsn("AND", I_RD , R_A , R_A  , ZN_FLAGS   , 0           );
  this.setInsn("ARR", I_UN , R_A , R_A  , CZNV_FLAGS , C_FLAG      );
  this.setInsn("ASL", I_RW , 0   , 0    , CZN_FLAGS  , 0           );
  this.setInsn("ASR", I_UN , R_A , R_A  , CZN_FLAGS  , 0           );
  this.setInsn("ATX", I_UN , R_AX, R_AX , ZN_FLAGS   , 0           );
  this.setInsn("AXA", I_UW , 0   , R_AX , 0          , 0           );
  this.setInsn("AXS", I_UN , R_X , R_AX , CZN_FLAGS  , 0           );
  this.setInsn("BCC", I_JP , 0   , 0    , 0          , C_FLAG      );
  this.setInsn("BCS", I_JP , 0   , 0    , 0          , C_FLAG      );
  this.setInsn("BEQ", I_JP , 0   , 0    , 0          , Z_FLAG      );
  this.setInsn("BIT", I_RD , 0   , R_A  , ZNV_FLAGS  , 0           );
  this.setInsn("BMI", I_JP , 0   , 0    , 0          , N_FLAG      );
  this.setInsn("BNE", I_JP , 0   , 0    , 0          , Z_FLAG      );
  this.setInsn("BPL", I_JP , 0   , 0    , 0          , N_FLAG      );
  this.setInsn("BRK", I_JS , 0   , 0    , BI_FLAGS   , CZNVDI_FLAGS);
  this.setInsn("BVC", I_JP , 0   , 0    , 0          , V_FLAG      );
  this.setInsn("BVS", I_JP , 0   , 0    , 0          , V_FLAG      );
  this.setInsn("CLC", 0    , 0   , 0    , C_FLAG     , 0           );
  this.setInsn("CLD", 0    , 0   , 0    , D_FLAG     , 0           );
  this.setInsn("CLI", 0    , 0   , 0    , I_FLAG     , 0           );
  this.setInsn("CLV", 0    , 0   , 0    , V_FLAG     , 0           );
  this.setInsn("CMP", I_RD , 0   , R_A  , CZN_FLAGS  , 0           );
  this.setInsn("CPX", I_RD , 0   , R_X  , CZN_FLAGS  , 0           );
  this.setInsn("CPY", I_RD , 0   , R_Y  , CZN_FLAGS  , 0           );
  this.setInsn("DCP", I_UM , 0   , R_A  , CZN_FLAGS  , 0           );
  this.setInsn("DEC", I_RW , 0   , 0    , ZN_FLAGS   , 0           );
  this.setInsn("DEX", I_RW , R_X , R_X  , ZN_FLAGS   , 0           );
  this.setInsn("DEY", I_RW , R_Y , R_Y  , ZN_FLAGS   , 0           );
  this.setInsn("DOP", I_UR , 0   , 0    , 0          , 0           );
  this.setInsn("EOR", I_RD , R_A , R_A  , ZN_FLAGS   , 0           );
  this.setInsn("HLT", I_UP , 0   , 0    , 0          , 0           );
  this.setInsn("INC", I_RW , 0   , 0    , ZN_FLAGS   , 0           );
  this.setInsn("INX", I_RW , R_X , R_X  , ZN_FLAGS   , 0           );
  this.setInsn("INY", I_RW , R_Y , R_Y  , ZN_FLAGS   , 0           );
  this.setInsn("ISC", I_UM , R_A , R_A  , CZNV_FLAGS , C_FLAG      );
  this.setInsn("JMP", I_JP , 0   , 0    , 0          , 0           );
  this.setInsn("JSR", I_JS , 0   , 0    , 0          , 0           );
  this.setInsn("LAR", I_UR , R_AXS, R_S , ZN_FLAGS   , 0           );
  this.setInsn("LAX", I_UR , R_AX, 0    , ZN_FLAGS   , 0           );
  this.setInsn("LDA", I_RD , R_A , 0    , ZN_FLAGS   , 0           );
  this.setInsn("LDX", I_RD , R_X , 0    , ZN_FLAGS   , 0           );
  this.setInsn("LDY", I_RD , R_Y , 0    , ZN_FLAGS   , 0           );
  this.setInsn("LSR", I_RW , 0   , 0    , CZN_FLAGS  , 0           );
  this.setInsn("NOP", 0    , 0   , 0    , 0          , 0           );
  this.setInsn("ORA", I_RD , R_A , R_A  , ZN_FLAGS   , 0           );
  this.setInsn("PHA", I_ST , 0   , R_A  , 0          , 0           );
  this.setInsn("PHP", I_ST , 0   , 0    , 0          , ALL_FLAGS   );
  this.setInsn("PLA", I_ST , R_A , 0    , ZN_FLAGS   , 0           );
  this.setInsn("PLP", I_ST , 0   , 0    , ALL_FLAGS  , 0           );
  this.setInsn("RLA", I_UM , R_A , R_A  , CZN_FLAGS  , C_FLAG      );
  this.setInsn("ROL", I_RW , 0   , 0    , CZN_FLAGS  , C_FLAG      );
  this.setInsn("ROR", I_RW , 0   , 0    , CZN_FLAGS  , C_FLAG      );
  this.setInsn("RRA", I_UM , R_A , R_A  , CZNV_FLAGS , C_FLAG      );
  this.setInsn("RTI", I_JS , 0   , 0    , ALL_FLAGS  , 0           );
  this.setInsn("RTS", I_JS , 0   , 0    , 0          , 0           );
  this.setInsn("SBC", I_RD , R_A , R_A  , CZNV_FLAGS , C_FLAG      );
  this.setInsn("SEC", 0    , 0   , 0    , C_FLAG     , 0           );
  this.setInsn("SED", 0    , 0   , 0    , D_FLAG     , 0           );
  this.setInsn("SEI", 0    , 0   , 0    , I_FLAG     , 0           );
  this.setInsn("SLO", I_UM , R_A , R_A  , CZN_FLAGS  , 0           );
  this.setInsn("SRE", I_UM , R_A , R_A  , CZN_FLAGS  , 0           );
  this.setInsn("STA", I_WR , 0   , R_A  , 0          , 0           );
  this.setInsn("STX", I_WR , 0   , R_X  , 0          , 0           );
  this.setInsn("STY", I_WR , 0   , R_Y  , 0          , 0           );
  this.setInsn("SXA", I_UW , 0   , R_X  , 0          , 0           );
  this.setInsn("SYA", I_UW , 0   , R_Y  , 0          , 0           );
  this.setInsn("TAX", 0    , R_X , R_A  , ZN_FLAGS   , 0           );
  this.setInsn("TAY", 0    , R_Y , R_A  , ZN_FLAGS   , 0           );
  this.setInsn("TOP", I_UR , 0   , 0    , 0          , 0           );
  this.setInsn("TSX", 0    , R_X , R_S  , ZN_FLAGS   , 0           );
  this.setInsn("TXA", 0    , R_A , R_X  , ZN_FLAGS   , 0           );
  this.setInsn("TXS", 0    , R_S , R_X  , 0          , 0           );
  this.setInsn("TYA", 0    , R_A , R_Y  , ZN_FLAGS   , 0           );
  this.setInsn("XAA", I_UN , R_A , R_AX , ZN_FLAGS   , 0           );
  this.setInsn("XAS", I_UW , R_S , R_AX , 0          , 0           );
  delete this.index;

  this.opdata = new Array(256);
  this.setOp(0x00, this.ADDR_IMPLIED     , this.INSN_BRK, 7);
  this.setOp(0x01, this.ADDR_INDIRECT_X  , this.INSN_ORA, 6);
  this.setOp(0x02, this.ADDR_IMPLIED     , this.INSN_HLT, 0);
  this.setOp(0x03, this.ADDR_INDIRECT_X  , this.INSN_SLO, 8);
  this.setOp(0x04, this.ADDR_ZERO_PAGE   , this.INSN_DOP, 3);
  this.setOp(0x05, this.ADDR_ZERO_PAGE   , this.INSN_ORA, 3);
  this.setOp(0x06, this.ADDR_ZERO_PAGE   , this.INSN_ASL, 5);
  this.setOp(0x07, this.ADDR_ZERO_PAGE   , this.INSN_SLO, 5);
  this.setOp(0x08, this.ADDR_IMPLIED     , this.INSN_PHP, 3);
  this.setOp(0x09, this.ADDR_IMMEDIATE   , this.INSN_ORA, 2);
  this.setOp(0x0a, this.ADDR_ACCUMULATOR , this.INSN_ASL, 2);
  this.setOp(0x0b, this.ADDR_IMMEDIATE   , this.INSN_AAC, 2);
  this.setOp(0x0c, this.ADDR_ABSOLUTE    , this.INSN_TOP, 4);
  this.setOp(0x0d, this.ADDR_ABSOLUTE    , this.INSN_ORA, 4);
  this.setOp(0x0e, this.ADDR_ABSOLUTE    , this.INSN_ASL, 6);
  this.setOp(0x0f, this.ADDR_ABSOLUTE    , this.INSN_SLO, 6);
  this.setOp(0x10, this.ADDR_RELATIVE    , this.INSN_BPL, 2);
  this.setOp(0x11, this.ADDR_INDIRECT_Y  , this.INSN_ORA, 5);
  this.setOp(0x12, this.ADDR_IMPLIED     , this.INSN_HLT, 0);
  this.setOp(0x13, this.ADDR_INDIRECT_Y  , this.INSN_SLO, 8);
  this.setOp(0x14, this.ADDR_ZERO_PAGE_X , this.INSN_DOP, 4);
  this.setOp(0x15, this.ADDR_ZERO_PAGE_X , this.INSN_ORA, 4);
  this.setOp(0x16, this.ADDR_ZERO_PAGE_X , this.INSN_ASL, 6);
  this.setOp(0x17, this.ADDR_ZERO_PAGE_X , this.INSN_SLO, 6);
  this.setOp(0x18, this.ADDR_IMPLIED     , this.INSN_CLC, 2);
  this.setOp(0x19, this.ADDR_ABSOLUTE_Y  , this.INSN_ORA, 4);
  this.setOp(0x1a, this.ADDR_IMPLIED     , this.INSN_NOP, 2);
  this.setOp(0x1b, this.ADDR_ABSOLUTE_Y  , this.INSN_SLO, 7);
  this.setOp(0x1c, this.ADDR_ABSOLUTE_X  , this.INSN_TOP, 4);
  this.setOp(0x1d, this.ADDR_ABSOLUTE_X  , this.INSN_ORA, 4);
  this.setOp(0x1e, this.ADDR_ABSOLUTE_X  , this.INSN_ASL, 7);
  this.setOp(0x1f, this.ADDR_ABSOLUTE_X  , this.INSN_SLO, 7);
  this.setOp(0x20, this.ADDR_ABSOLUTE    , this.INSN_JSR, 6);
  this.setOp(0x21, this.ADDR_INDIRECT_X  , this.INSN_AND, 6);
  this.setOp(0x22, this.ADDR_IMPLIED     , this.INSN_HLT, 0);
  this.setOp(0x23, this.ADDR_INDIRECT_X  , this.INSN_RLA, 8);
  this.setOp(0x24, this.ADDR_ZERO_PAGE   , this.INSN_BIT, 3);
  this.setOp(0x25, this.ADDR_ZERO_PAGE   , this.INSN_AND, 3);
  this.setOp(0x26, this.ADDR_ZERO_PAGE   , this.INSN_ROL, 5);
  this.setOp(0x27, this.ADDR_ZERO_PAGE   , this.INSN_RLA, 5);
  this.setOp(0x28, this.ADDR_IMPLIED     , this.INSN_PLP, 4);
  this.setOp(0x29, this.ADDR_IMMEDIATE   , this.INSN_AND, 2);
  this.setOp(0x2a, this.ADDR_ACCUMULATOR , this.INSN_ROL, 2);
  this.setOp(0x2b, this.ADDR_IMMEDIATE   , this.INSN_AAC, 2);
  this.setOp(0x2c, this.ADDR_ABSOLUTE    , this.INSN_BIT, 4);
  this.setOp(0x2d, this.ADDR_ABSOLUTE    , this.INSN_AND, 4);
  this.setOp(0x2e, this.ADDR_ABSOLUTE    , this.INSN_ROL, 6);
  this.setOp(0x2f, this.ADDR_ABSOLUTE    , this.INSN_RLA, 6);
  this.setOp(0x30, this.ADDR_RELATIVE    , this.INSN_BMI, 2);
  this.setOp(0x31, this.ADDR_INDIRECT_Y  , this.INSN_AND, 5);
  this.setOp(0x32, this.ADDR_IMPLIED     , this.INSN_HLT, 0);
  this.setOp(0x33, this.ADDR_INDIRECT_Y  , this.INSN_RLA, 8);
  this.setOp(0x34, this.ADDR_ZERO_PAGE_X , this.INSN_DOP, 4);
  this.setOp(0x35, this.ADDR_ZERO_PAGE_X , this.INSN_AND, 4);
  this.setOp(0x36, this.ADDR_ZERO_PAGE_X , this.INSN_ROL, 6);
  this.setOp(0x37, this.ADDR_ZERO_PAGE_X , this.INSN_RLA, 6);
  this.setOp(0x38, this.ADDR_IMPLIED     , this.INSN_SEC, 2);
  this.setOp(0x39, this.ADDR_ABSOLUTE_Y  , this.INSN_AND, 4);
  this.setOp(0x3a, this.ADDR_IMPLIED     , this.INSN_NOP, 2);
  this.setOp(0x3b, this.ADDR_ABSOLUTE_Y  , this.INSN_RLA, 7);
  this.setOp(0x3c, this.ADDR_ABSOLUTE_X  , this.INSN_TOP, 4);
  this.setOp(0x3d, this.ADDR_ABSOLUTE_X  , this.INSN_AND, 4);
  this.setOp(0x3e, this.ADDR_ABSOLUTE_X  , this.INSN_ROL, 7);
  this.setOp(0x3f, this.ADDR_ABSOLUTE_X  , this.INSN_RLA, 7);
  this.setOp(0x40, this.ADDR_IMPLIED     , this.INSN_RTI, 6);
  this.setOp(0x41, this.ADDR_INDIRECT_X  , this.INSN_EOR, 6);
  this.setOp(0x42, this.ADDR_IMPLIED     , this.INSN_HLT, 0);
  this.setOp(0x43, this.ADDR_INDIRECT_X  , this.INSN_SRE, 8);
  this.setOp(0x44, this.ADDR_ZERO_PAGE   , this.INSN_DOP, 3);
  this.setOp(0x45, this.ADDR_ZERO_PAGE   , this.INSN_EOR, 3);
  this.setOp(0x46, this.ADDR_ZERO_PAGE   , this.INSN_LSR, 5);
  this.setOp(0x47, this.ADDR_ZERO_PAGE   , this.INSN_SRE, 5);
  this.setOp(0x48, this.ADDR_IMPLIED     , this.INSN_PHA, 3);
  this.setOp(0x49, this.ADDR_IMMEDIATE   , this.INSN_EOR, 2);
  this.setOp(0x4a, this.ADDR_ACCUMULATOR , this.INSN_LSR, 2);
  this.setOp(0x4b, this.ADDR_IMMEDIATE   , this.INSN_ASR, 2);
  this.setOp(0x4c, this.ADDR_ABSOLUTE    , this.INSN_JMP, 3);
  this.setOp(0x4d, this.ADDR_ABSOLUTE    , this.INSN_EOR, 4);
  this.setOp(0x4e, this.ADDR_ABSOLUTE    , this.INSN_LSR, 6);
  this.setOp(0x4f, this.ADDR_ABSOLUTE    , this.INSN_SRE, 6);
  this.setOp(0x50, this.ADDR_RELATIVE    , this.INSN_BVC, 2);
  this.setOp(0x51, this.ADDR_INDIRECT_Y  , this.INSN_EOR, 5);
  this.setOp(0x52, this.ADDR_IMPLIED     , this.INSN_HLT, 0);
  this.setOp(0x53, this.ADDR_INDIRECT_Y  , this.INSN_SRE, 8);
  this.setOp(0x54, this.ADDR_ZERO_PAGE_X , this.INSN_DOP, 4);
  this.setOp(0x55, this.ADDR_ZERO_PAGE_X , this.INSN_EOR, 4);
  this.setOp(0x56, this.ADDR_ZERO_PAGE_X , this.INSN_LSR, 6);
  this.setOp(0x57, this.ADDR_ZERO_PAGE_X , this.INSN_SRE, 6);
  this.setOp(0x58, this.ADDR_IMPLIED     , this.INSN_CLI, 2);
  this.setOp(0x59, this.ADDR_ABSOLUTE_Y  , this.INSN_EOR, 4);
  this.setOp(0x5a, this.ADDR_IMPLIED     , this.INSN_NOP, 2);
  this.setOp(0x5b, this.ADDR_ABSOLUTE_Y  , this.INSN_SRE, 7);
  this.setOp(0x5c, this.ADDR_ABSOLUTE_X  , this.INSN_TOP, 4);
  this.setOp(0x5d, this.ADDR_ABSOLUTE_X  , this.INSN_EOR, 4);
  this.setOp(0x5e, this.ADDR_ABSOLUTE_X  , this.INSN_LSR, 7);
  this.setOp(0x5f, this.ADDR_ABSOLUTE_X  , this.INSN_SRE, 7);
  this.setOp(0x60, this.ADDR_IMPLIED     , this.INSN_RTS, 6);
  this.setOp(0x61, this.ADDR_INDIRECT_X  , this.INSN_ADC, 6);
  this.setOp(0x62, this.ADDR_IMPLIED     , this.INSN_HLT, 0);
  this.setOp(0x63, this.ADDR_INDIRECT_X  , this.INSN_RRA, 8);
  this.setOp(0x64, this.ADDR_ZERO_PAGE   , this.INSN_DOP, 3);
  this.setOp(0x65, this.ADDR_ZERO_PAGE   , this.INSN_ADC, 3);
  this.setOp(0x66, this.ADDR_ZERO_PAGE   , this.INSN_ROR, 5);
  this.setOp(0x67, this.ADDR_ZERO_PAGE   , this.INSN_RRA, 5);
  this.setOp(0x68, this.ADDR_IMPLIED     , this.INSN_PLA, 4);
  this.setOp(0x69, this.ADDR_IMMEDIATE   , this.INSN_ADC, 2);
  this.setOp(0x6a, this.ADDR_ACCUMULATOR , this.INSN_ROR, 2);
  this.setOp(0x6b, this.ADDR_IMMEDIATE   , this.INSN_ARR, 2);
  this.setOp(0x6c, this.ADDR_INDIRECT    , this.INSN_JMP, 5);
  this.setOp(0x6d, this.ADDR_ABSOLUTE    , this.INSN_ADC, 4);
  this.setOp(0x6e, this.ADDR_ABSOLUTE    , this.INSN_ROR, 6);
  this.setOp(0x6f, this.ADDR_ABSOLUTE    , this.INSN_RRA, 6);
  this.setOp(0x70, this.ADDR_RELATIVE    , this.INSN_BVS, 2);
  this.setOp(0x71, this.ADDR_INDIRECT_Y  , this.INSN_ADC, 5);
  this.setOp(0x72, this.ADDR_IMPLIED     , this.INSN_HLT, 0);
  this.setOp(0x73, this.ADDR_INDIRECT_Y  , this.INSN_RRA, 8);
  this.setOp(0x74, this.ADDR_ZERO_PAGE_X , this.INSN_DOP, 4);
  this.setOp(0x75, this.ADDR_ZERO_PAGE_X , this.INSN_ADC, 4);
  this.setOp(0x76, this.ADDR_ZERO_PAGE_X , this.INSN_ROR, 6);
  this.setOp(0x77, this.ADDR_ZERO_PAGE_X , this.INSN_RRA, 6);
  this.setOp(0x78, this.ADDR_IMPLIED     , this.INSN_SEI, 2);
  this.setOp(0x79, this.ADDR_ABSOLUTE_Y  , this.INSN_ADC, 4);
  this.setOp(0x7a, this.ADDR_IMPLIED     , this.INSN_NOP, 2);
  this.setOp(0x7b, this.ADDR_ABSOLUTE_Y  , this.INSN_RRA, 7);
  this.setOp(0x7c, this.ADDR_ABSOLUTE_X  , this.INSN_TOP, 4);
  this.setOp(0x7d, this.ADDR_ABSOLUTE_X  , this.INSN_ADC, 4);
  this.setOp(0x7e, this.ADDR_ABSOLUTE_X  , this.INSN_ROR, 7);
  this.setOp(0x7f, this.ADDR_ABSOLUTE_X  , this.INSN_RRA, 7);
  this.setOp(0x80, this.ADDR_IMMEDIATE   , this.INSN_DOP, 2);
  this.setOp(0x81, this.ADDR_INDIRECT_X  , this.INSN_STA, 6);
  this.setOp(0x82, this.ADDR_IMMEDIATE   , this.INSN_DOP, 2);
  this.setOp(0x83, this.ADDR_INDIRECT_X  , this.INSN_AAX, 6);
  this.setOp(0x84, this.ADDR_ZERO_PAGE   , this.INSN_STY, 3);
  this.setOp(0x85, this.ADDR_ZERO_PAGE   , this.INSN_STA, 3);
  this.setOp(0x86, this.ADDR_ZERO_PAGE   , this.INSN_STX, 3);
  this.setOp(0x87, this.ADDR_ZERO_PAGE   , this.INSN_AAX, 3);
  this.setOp(0x88, this.ADDR_IMPLIED     , this.INSN_DEY, 2);
  this.setOp(0x89, this.ADDR_IMMEDIATE   , this.INSN_DOP, 2);
  this.setOp(0x8a, this.ADDR_IMPLIED     , this.INSN_TXA, 2);
  this.setOp(0x8b, this.ADDR_IMMEDIATE   , this.INSN_XAA, 2);
  this.setOp(0x8c, this.ADDR_ABSOLUTE    , this.INSN_STY, 4);
  this.setOp(0x8d, this.ADDR_ABSOLUTE    , this.INSN_STA, 4);
  this.setOp(0x8e, this.ADDR_ABSOLUTE    , this.INSN_STX, 4);
  this.setOp(0x8f, this.ADDR_ABSOLUTE    , this.INSN_AAX, 4);
  this.setOp(0x90, this.ADDR_RELATIVE    , this.INSN_BCC, 2);
  this.setOp(0x91, this.ADDR_INDIRECT_Y  , this.INSN_STA, 6);
  this.setOp(0x92, this.ADDR_IMPLIED     , this.INSN_HLT, 0);
  this.setOp(0x93, this.ADDR_INDIRECT_Y  , this.INSN_AXA, 6);
  this.setOp(0x94, this.ADDR_ZERO_PAGE_X , this.INSN_STY, 4);
  this.setOp(0x95, this.ADDR_ZERO_PAGE_X , this.INSN_STA, 4);
  this.setOp(0x96, this.ADDR_ZERO_PAGE_Y , this.INSN_STX, 4);
  this.setOp(0x97, this.ADDR_ZERO_PAGE_Y , this.INSN_AAX, 4);
  this.setOp(0x98, this.ADDR_IMPLIED     , this.INSN_TYA, 2);
  this.setOp(0x99, this.ADDR_ABSOLUTE_Y  , this.INSN_STA, 5);
  this.setOp(0x9a, this.ADDR_IMPLIED     , this.INSN_TXS, 2);
  this.setOp(0x9b, this.ADDR_ABSOLUTE_Y  , this.INSN_XAS, 5);
  this.setOp(0x9c, this.ADDR_ABSOLUTE_X  , this.INSN_SYA, 5);
  this.setOp(0x9d, this.ADDR_ABSOLUTE_X  , this.INSN_STA, 5);
  this.setOp(0x9e, this.ADDR_ABSOLUTE_Y  , this.INSN_SXA, 5);
  this.setOp(0x9f, this.ADDR_ABSOLUTE_Y  , this.INSN_AXA, 5);
  this.setOp(0xa0, this.ADDR_IMMEDIATE   , this.INSN_LDY, 2);
  this.setOp(0xa1, this.ADDR_INDIRECT_X  , this.INSN_LDA, 6);
  this.setOp(0xa2, this.ADDR_IMMEDIATE   , this.INSN_LDX, 2);
  this.setOp(0xa3, this.ADDR_INDIRECT_X  , this.INSN_LAX, 6);
  this.setOp(0xa4, this.ADDR_ZERO_PAGE   , this.INSN_LDY, 3);
  this.setOp(0xa5, this.ADDR_ZERO_PAGE   , this.INSN_LDA, 3);
  this.setOp(0xa6, this.ADDR_ZERO_PAGE   , this.INSN_LDX, 3);
  this.setOp(0xa7, this.ADDR_ZERO_PAGE   , this.INSN_LAX, 3);
  this.setOp(0xa8, this.ADDR_IMPLIED     , this.INSN_TAY, 2);
  this.setOp(0xa9, this.ADDR_IMMEDIATE   , this.INSN_LDA, 2);
  this.setOp(0xaa, this.ADDR_IMPLIED     , this.INSN_TAX, 2);
  this.setOp(0xab, this.ADDR_IMMEDIATE   , this.INSN_ATX, 2);
  this.setOp(0xac, this.ADDR_ABSOLUTE    , this.INSN_LDY, 4);
  this.setOp(0xad, this.ADDR_ABSOLUTE    , this.INSN_LDA, 4);
  this.setOp(0xae, this.ADDR_ABSOLUTE    , this.INSN_LDX, 4);
  this.setOp(0xaf, this.ADDR_ABSOLUTE    , this.INSN_LAX, 4);
  this.setOp(0xb0, this.ADDR_RELATIVE    , this.INSN_BCS, 2);
  this.setOp(0xb1, this.ADDR_INDIRECT_Y  , this.INSN_LDA, 5);
  this.setOp(0xb2, this.ADDR_IMPLIED     , this.INSN_HLT, 0);
  this.setOp(0xb3, this.ADDR_INDIRECT_Y  , this.INSN_LAX, 5);
  this.setOp(0xb4, this.ADDR_ZERO_PAGE_X , this.INSN_LDY, 4);
  this.setOp(0xb5, this.ADDR_ZERO_PAGE_X , this.INSN_LDA, 4);
  this.setOp(0xb6, this.ADDR_ZERO_PAGE_Y , this.INSN_LDX, 4);
  this.setOp(0xb7, this.ADDR_ZERO_PAGE_Y , this.INSN_LAX, 4);
  this.setOp(0xb8, this.ADDR_IMPLIED     , this.INSN_CLV, 2);
  this.setOp(0xb9, this.ADDR_ABSOLUTE_Y  , this.INSN_LDA, 4);
  this.setOp(0xba, this.ADDR_IMPLIED     , this.INSN_TSX, 2);
  this.setOp(0xbb, this.ADDR_ABSOLUTE_Y  , this.INSN_LAR, 4);
  this.setOp(0xbc, this.ADDR_ABSOLUTE_X  , this.INSN_LDY, 4);
  this.setOp(0xbd, this.ADDR_ABSOLUTE_X  , this.INSN_LDA, 4);
  this.setOp(0xbe, this.ADDR_ABSOLUTE_Y  , this.INSN_LDX, 4);
  this.setOp(0xbf, this.ADDR_ABSOLUTE_Y  , this.INSN_LAX, 4);
  this.setOp(0xc0, this.ADDR_IMMEDIATE   , this.INSN_CPY, 2);
  this.setOp(0xc1, this.ADDR_INDIRECT_X  , this.INSN_CMP, 6);
  this.setOp(0xc2, this.ADDR_IMMEDIATE   , this.INSN_DOP, 2);
  this.setOp(0xc3, this.ADDR_INDIRECT_X  , this.INSN_DCP, 8);
  this.setOp(0xc4, this.ADDR_ZERO_PAGE   , this.INSN_CPY, 3);
  this.setOp(0xc5, this.ADDR_ZERO_PAGE   , this.INSN_CMP, 3);
  this.setOp(0xc6, this.ADDR_ZERO_PAGE   , this.INSN_DEC, 5);
  this.setOp(0xc7, this.ADDR_ZERO_PAGE   , this.INSN_DCP, 5);
  this.setOp(0xc8, this.ADDR_IMPLIED     , this.INSN_INY, 2);
  this.setOp(0xc9, this.ADDR_IMMEDIATE   , this.INSN_CMP, 2);
  this.setOp(0xca, this.ADDR_IMPLIED     , this.INSN_DEX, 2);
  this.setOp(0xcb, this.ADDR_IMMEDIATE   , this.INSN_AXS, 2);
  this.setOp(0xcc, this.ADDR_ABSOLUTE    , this.INSN_CPY, 4);
  this.setOp(0xcd, this.ADDR_ABSOLUTE    , this.INSN_CMP, 4);
  this.setOp(0xce, this.ADDR_ABSOLUTE    , this.INSN_DEC, 6);
  this.setOp(0xcf, this.ADDR_ABSOLUTE    , this.INSN_DCP, 6);
  this.setOp(0xd0, this.ADDR_RELATIVE    , this.INSN_BNE, 2);
  this.setOp(0xd1, this.ADDR_INDIRECT_Y  , this.INSN_CMP, 5);
  this.setOp(0xd2, this.ADDR_IMPLIED     , this.INSN_HLT, 0);
  this.setOp(0xd3, this.ADDR_INDIRECT_Y  , this.INSN_DCP, 8);
  this.setOp(0xd4, this.ADDR_ZERO_PAGE_X , this.INSN_DOP, 4);
  this.setOp(0xd5, this.ADDR_ZERO_PAGE_X , this.INSN_CMP, 4);
  this.setOp(0xd6, this.ADDR_ZERO_PAGE_X , this.INSN_DEC, 6);
  this.setOp(0xd7, this.ADDR_ZERO_PAGE_X , this.INSN_DCP, 6);
  this.setOp(0xd8, this.ADDR_IMPLIED     , this.INSN_CLD, 2);
  this.setOp(0xd9, this.ADDR_ABSOLUTE_Y  , this.INSN_CMP, 4);
  this.setOp(0xda, this.ADDR_IMPLIED     , this.INSN_NOP, 2);
  this.setOp(0xdb, this.ADDR_ABSOLUTE_Y  , this.INSN_DCP, 7);
  this.setOp(0xdc, this.ADDR_ABSOLUTE_X  , this.INSN_TOP, 4);
  this.setOp(0xdd, this.ADDR_ABSOLUTE_X  , this.INSN_CMP, 4);
  this.setOp(0xde, this.ADDR_ABSOLUTE_X  , this.INSN_DEC, 7);
  this.setOp(0xdf, this.ADDR_ABSOLUTE_X  , this.INSN_DCP, 7);
  this.setOp(0xe0, this.ADDR_IMMEDIATE   , this.INSN_CPX, 2);
  this.setOp(0xe1, this.ADDR_INDIRECT_X  , this.INSN_SBC, 6);
  this.setOp(0xe2, this.ADDR_IMMEDIATE   , this.INSN_DOP, 2);
  this.setOp(0xe3, this.ADDR_INDIRECT_X  , this.INSN_ISC, 8);
  this.setOp(0xe4, this.ADDR_ZERO_PAGE   , this.INSN_CPX, 3);
  this.setOp(0xe5, this.ADDR_ZERO_PAGE   , this.INSN_SBC, 3);
  this.setOp(0xe6, this.ADDR_ZERO_PAGE   , this.INSN_INC, 5);
  this.setOp(0xe7, this.ADDR_ZERO_PAGE   , this.INSN_ISC, 5);
  this.setOp(0xe8, this.ADDR_IMPLIED     , this.INSN_INX, 2);
  this.setOp(0xe9, this.ADDR_IMMEDIATE   , this.INSN_SBC, 2);
  this.setOp(0xea, this.ADDR_IMPLIED     , this.INSN_NOP, 2);
  this.setOp(0xeb, this.ADDR_IMMEDIATE   , this.INSN_SBC, 2);
  this.setOp(0xec, this.ADDR_ABSOLUTE    , this.INSN_CPX, 4);
  this.setOp(0xed, this.ADDR_ABSOLUTE    , this.INSN_SBC, 4);
  this.setOp(0xee, this.ADDR_ABSOLUTE    , this.INSN_INC, 6);
  this.setOp(0xef, this.ADDR_ABSOLUTE    , this.INSN_ISC, 6);
  this.setOp(0xf0, this.ADDR_RELATIVE    , this.INSN_BEQ, 2);
  this.setOp(0xf1, this.ADDR_INDIRECT_Y  , this.INSN_SBC, 5);
  this.setOp(0xf2, this.ADDR_IMPLIED     , this.INSN_HLT, 0);
  this.setOp(0xf3, this.ADDR_INDIRECT_Y  , this.INSN_ISC, 8);
  this.setOp(0xf4, this.ADDR_ZERO_PAGE_X , this.INSN_DOP, 4);
  this.setOp(0xf5, this.ADDR_ZERO_PAGE_X , this.INSN_SBC, 4);
  this.setOp(0xf6, this.ADDR_ZERO_PAGE_X , this.INSN_INC, 6);
  this.setOp(0xf7, this.ADDR_ZERO_PAGE_X , this.INSN_ISC, 6);
  this.setOp(0xf8, this.ADDR_IMPLIED     , this.INSN_SED, 2);
  this.setOp(0xf9, this.ADDR_ABSOLUTE_Y  , this.INSN_SBC, 4);
  this.setOp(0xfa, this.ADDR_IMPLIED     , this.INSN_NOP, 2);
  this.setOp(0xfb, this.ADDR_ABSOLUTE_Y  , this.INSN_ISC, 7);
  this.setOp(0xfc, this.ADDR_ABSOLUTE_X  , this.INSN_TOP, 4);
  this.setOp(0xfd, this.ADDR_ABSOLUTE_X  , this.INSN_SBC, 4);
  this.setOp(0xfe, this.ADDR_ABSOLUTE_X  , this.INSN_INC, 7);
  this.setOp(0xff, this.ADDR_ABSOLUTE_X  , this.INSN_ISC, 7);
};

JSNES.CPU.OpData.prototype = {
  INSN_AAC:  0, // [Undocumented]Logical "And" byte with accumulator. If result is negative then carry is set.
  INSN_AAX:  1, // [Undocumented]Logical "And" X register with accumulator and store result in memory. (No flags changed)
  INSN_ADC:  2, // Add Memory to Accumulator with Carry
  INSN_AND:  3, // Logical "And" Memory with Accumulator
  INSN_ARR:  4, // [Undocumented]Logical "And" byte with accumulator, then rotate one bit right in accumulator and check bit 5 and 6.
  INSN_ASL:  5, // Shift Left One Bit (Memory or Accumulator)
  INSN_ASR:  6, // [Undocumented]Logical "And" byte with accumulator, then shift right one bit in accumulator.
  INSN_ATX:  7, // [Undocumented]Logical "And" byte with accumulator, then transfer accumulator to X register. Or it could be (A = X = ((A | 0xEE) & data)).  Highly unpredictable.*/
  INSN_AXA:  8, // [Undocumented]Logical "And" X register with accumulator then AND result with (ADDR_HI + 1) and store in memory. Unpredictable.
  INSN_AXS:  9, // [Undocumented]Logical "And" X register with accumulator and store result in X register, then subtract byte from X register (without borrow). (carry should work the same way as CMP)
  INSN_BCC: 10, // Branch on Carry Clear
  INSN_BCS: 11, // Branch on Carry Set
  INSN_BEQ: 12, // Branch on Result Zero
  INSN_BIT: 13, // Test Bits in Memory with Accumulator
  INSN_BMI: 14, // Branch on Result Minus
  INSN_BNE: 15, // Branch on Result not Zero
  INSN_BPL: 16, // Branch on Result Plus
  INSN_BRK: 17, // Force Break
  INSN_BVC: 18, // Branch on Overflow Clear
  INSN_BVS: 19, // Branch on Overflow Set
  INSN_CLC: 20, // Clear Carry Flag
  INSN_CLD: 21, // Clear Decimal Mode
  INSN_CLI: 22, // Clear interrupt Disable Bit
  INSN_CLV: 23, // Clear Overflow Flag
  INSN_CMP: 24, // Compare Memory and Accumulator
  INSN_CPX: 25, // Compare Memory and Index X
  INSN_CPY: 26, // Compare Memory and Index Y
  INSN_DCP: 27, // [Undocumented]Subtract 1 from memory (without borrow) and then compare with accumulator
  INSN_DEC: 28, // Decrement Memory by One
  INSN_DEX: 29, // Decrement Index X by One
  INSN_DEY: 30, // Decrement Index Y by One
  INSN_DOP: 31, // [Undocumented]Double NOP (fetches memory)
  INSN_EOR: 32, // Logical "Exclusive-Or" Memory with Accumulator
  INSN_HLT: 33, // [Undocumented] Halt (JAM) 6502.
  INSN_INC: 34, // Increment Memory by One
  INSN_INX: 35, // Increment Index X by One
  INSN_INY: 36, // Increment Index Y by One
  INSN_ISC: 37, // [Undocumented]Increase memory by one, then subtract memory from accumulator (with borrow) like SBC.
  INSN_JMP: 38, // Jump to New Location
  INSN_JSR: 39, // Jump to New Location Saving Return Address
  INSN_LAR: 40, // [Undocumented]AND memory with stack pointer, transfer result to accumulator, X register and stack pointer.
  INSN_LAX: 41, // [Undocumented]Load accumulator and X register with memory.
  INSN_LDA: 42, // Load Accumulator with Memory
  INSN_LDX: 43, // Load Index X with Memory
  INSN_LDY: 44, // Load Index Y with Memory
  INSN_LSR: 45, // Shift Right One Bit (Memory or Accumulator)
  INSN_NOP: 46, // No Operation
  INSN_ORA: 47, // Logical "Or" Memory with Accumulator
  INSN_PHA: 48, // Push Accumulator on Stack
  INSN_PHP: 49, // Push Processor Status on Stack
  INSN_PLA: 50, // Pull Accumulator from Stack
  INSN_PLP: 51, // Pull Processor Status from Stack
  INSN_RLA: 52, // [Undocumented]Rotate one bit left in memory, then AND accumulator with memory.
  INSN_ROL: 53, // Rotate One Bit Left (Memory or Accumulator)
  INSN_ROR: 54, // Rotate One Bit Right (Memory or Accumulator)
  INSN_RRA: 55, // [Undocumented]Rotate one bit right in memory, then add memory to accumulator (with carry).
  INSN_RTI: 56, // Return from Interrupt
  INSN_RTS: 57, // Return from Subroutine
  INSN_SBC: 58, // Subtract Memory from Accumulator with Borrow
  INSN_SEC: 59, // Set Carry Flag
  INSN_SED: 60, // Set Decimal Mode
  INSN_SEI: 61, // Set Interrupt Disable Status
  INSN_SLO: 62, // [Undocumented]Shift left one bit in memory, then OR accumulator with memory.
  INSN_SRE: 63, // [Undocumented]Shift right one bit in memory, then EOR accumulator with memory.
  INSN_STA: 64, // Store Accumulator in Memory
  INSN_STX: 65, // Store Index X in Memory
  INSN_STY: 66, // Store Index Y in Memory
  INSN_SXA: 67, // [Undocumented]AND X register with the high byte of the target address of the argument + 1. Store the result in memory.
  INSN_SYA: 68, // [Undocumented]AND Y register with the high byte of the target address of the argument + 1. Store the result in memory.
  INSN_TAX: 69, // Transfer Accumulator to Index X
  INSN_TAY: 70, // Transfer Accumulator to Index Y
  INSN_TOP: 71, // [Undocumented]Triple NOP
  INSN_TSX: 72, // Transfer Stack Pointer to Index X
  INSN_TXA: 73, // Transfer Index X to Accumulator
  INSN_TXS: 74, // Transfer Index X to Stack Pointer
  INSN_TYA: 75, // Transfer Index Y to Accumulator
  INSN_XAA: 76, // [Undocumented]A = (A | #$EE) & X & #byte
  INSN_XAS: 77, // [Undocumented]AND X register with accumulator and store result in stack pointer, then
                // AND stack pointer with the high byte of the target address of the argument + 1. Store result in memory.
  INSN_TOTAL: 78,
    
  // -------------------------------- //
  // Addressing modes:
  ADDR_ACCUMULATOR :  0,
  ADDR_IMMEDIATE   :  1,
  ADDR_ZERO_PAGE   :  2,
  ADDR_ZERO_PAGE_X :  3,
  ADDR_ZERO_PAGE_Y :  4,
  ADDR_ABSOLUTE    :  5,
  ADDR_ABSOLUTE_X  :  6,
  ADDR_ABSOLUTE_Y  :  7,
  ADDR_INDIRECT    :  8,
  ADDR_INDIRECT_X  :  9,
  ADDR_INDIRECT_Y  : 10,
  ADDR_RELATIVE    : 11,
  ADDR_IMPLIED     : 12,

  // -------------------------------- //
  // Instruction details:
  I_RD :  1, // The instruction reads from memory
  I_WR :  2, // The instruction writes to memory 
  I_JP :  4, // It is a jump/branch (or related) 
  I_ST :  8, // This instruction access the stack
  I_UN : 16, // It is an undocumented instruction

  // For the used/changed registers
  R_A :  256, // Accumulator
  R_X :  512, // X register
  R_Y : 1024, // Y register
  R_S : 2048, // Stack register

  // P (flag) register bitmasks
  F_C :   1, // Carry flag
  F_Z :   2, // Zero flag
  F_I :   4, // Interrupt flag
  F_D :   8, // Decimal flag
  F_B :  16, // Break flag
  F_R :  32, // Reserved flag
  F_V :  64, // Overflow flag
  F_N : 128, // Negative flag

  setInsn: function(iname, details, chgRegs, usedRegs, chgFlags, usedFlags) {
    this.insnname[this.index] = iname;
    this.insndetails[this.index] = details;
    this.chg[this.index] = chgRegs | chgFlags;
    this.used[this.index] = usedRegs | usedFlags;
    this.index++;
  },

  setOp: function(op, addr, insn, cycles) {
    var size = this.addressingLength[addr];
    this.opdata[op] = 
      ((insn  &0xFF)    )| 
      ((addr  &0xFF)<< 8)| 
      ((size  &0xFF)<<16)| 
      ((cycles&0xFF)<<24);
  },

  disassemble: function(input, offset, addr) {
    function formatHex(value, numDigits) {
      var out = value.toString(16).toUpperCase();
      while (out.length < numDigits) out = "0" + out;
      return out;
    }

    var output = "";
    var opcode;
    var insn, len, addressing;
    var oper, address;
    var opc;

    opc = input[offset];
    opcode = this.opdata[opc];
    insn = opcode & 0xFF;
    addressing = (opcode >> 8) & 0xFF;
    len = (opcode >> 16) & 0xFF;

    output = "$" + formatHex(addr, 4) + ": [ $" + formatHex(opc, 2) + " ";
    switch (len) {
      case 1: output += "]           "; break;
      case 2: output += "$" + formatHex(input[offset + 1], 2) + " ]       "; break;
      case 3: output += "$" + formatHex(input[offset + 1], 2) + " $" + formatHex(input[offset + 2], 2) + " ]   "; break;
    }

    output = output + this.insnname[insn] + " ";
    addr += len;

    switch (addressing) {
      case 0: // ADDR_ACCUMULATOR
        output += "A\n";
        break;
      case 1: // ADDR_IMMEDIATE
        output += "#$" + formatHex(input[offset + 1], 2) + "\n";
        break;
      case 2: // ADDR_ZERO_PAGE
        output += "$" + formatHex(input[offset + 1], 2) + "\n";
        break;
      case 3: // ADDR_ZERO_PAGE_X
        output += "$" + formatHex(input[offset + 1], 2) + ", X\n";
        break;
      case 4: // ADDR_ZERO_PAGE_Y
        output += "$" + formatHex(input[offset + 1], 2) + ", Y\n";
        break;
      case 5: // ADDR_ABSOLUTE
        oper = input[offset + 1];
        oper += (input[offset + 2]) << 8;
        output += "$" + formatHex(oper, 4) + "\n";
        break;
      case 6: // ADDR_ABSOLUTE_X
        oper = input[offset + 1];
        oper += (input[offset + 2]) << 8;
        output += "$" + formatHex(oper, 4) + ", X\n";
        break;
      case 7: // ADDR_ABSOLUTE_Y
        oper = input[offset + 1];
        oper += (input[offset + 2]) << 8;
        output += "$" + formatHex(oper, 4) + ", Y\n";
        break;
      case 8: // ADDR_INDIRECT
        oper = input[offset + 1];
        oper += (input[offset + 2]) << 8;
        output += "($" + formatHex(oper, 4) + ")\n";
        break;
      case 9: // ADDR_INDIRECT_X
        output += "($" + formatHex(input[offset + 1], 2) + ", X)\n";
        break;
      case 10: // ADDR_INDIRECT_Y
        output += "($" + formatHex(input[offset + 1], 2) + "), Y\n";
        break;
      case 11: // ADDR_RELATIVE
        address = input[offset + 1];
        if (address & 0x80) address |= 0xFF00;
        address = (address + addr) & 0xFFFF;
        output += "$" + formatHex(address, 4) + "\n";
        break;
      case 12: // ADDR_IMPLIED
        output += "\n";
        break;
    }
    return output;
  }
};

JSNES.CPU.CodeBuffer = function(cpu) {
  this.cpu = cpu;
  this.buffer = [];
  this.opcodeBuffer = [];
  this.operr = null;
  this.operw = null;
  this.operws = null;
  this.outa = null;
  this.pc = null;
  this.cycles = null;
  this.addressing = null;
  this.details = null;
  this.len = null;
};

JSNES.CPU.CodeBuffer.prototype = {
  append: function(str) {
    this.opcodeBuffer.push(str);
    return this;
  },

  funcAppend : function(str) {
    this.buffer.push(str);
  },

  startFunction: function() {
    this.cycles = 0;
    this.funcAppend(
      'if (innerLabel === undefined) innerLabel = 0;\n' +
      'var p_reg = this.p_reg, pc_reg = this.pc_reg, s_reg = this.s_reg;\n' +
      'var a_reg = this.a_reg, x_reg = this.x_reg, y_reg = this.y_reg;\n' +
      'var c_flag = p_reg & 1;\n' +
      'var z_flag = p_reg & 2;\n' +
      'var i_flag = p_reg & 4;\n' +
      'var d_flag = p_reg & 8;\n' +
      'var b_flag = p_reg & 16;\n' +
      'var v_flag = p_reg & 64;\n' +
      'var n_flag = p_reg & 128;\n' +
      'var operp, t1, t2;\n' +
      'var mem=this.mem;\n' + 
      'main_loop:\n' + 
      'while (cycles > 0) {\n' +
      'switch(innerLabel) {\n');
  },

  startOpcode: function(pc) {
    this.pc = pc;
    var opc = this.cpu.mem[pc];
    var opcode = this.cpu.opdata.opdata[opc];
    var insn, cyc, addressing;
    var details;

    cyc = (opcode >> 24) & 0xFF;
    addressing = (opcode >> 8) & 0xFF;
    insn = opcode & 0xFF;
    this.len = (opcode >> 16) & 0xFF;
    details = this.cpu.opdata.insndetails[insn];

    this.opcodeBuffer.length = 0;
    if (this.cpu.innerLabel[pc] !== undefined) {
      this.funcAppend('case ' + this.cpu.innerLabel[pc] + ':\n');
    }
    this.funcAppend('// ' + this.cpu.disassemble(pc));
    this.funcAppend('cycles -= 3;\n');
    this.setupAddressing(addressing, details);
    this.cycles += cyc;
    return insn;
  },

  assignOper: function(val) {
    this.operr = val;
    this.operw = val + ' = ';
    this.operws = '';
  },

  readwriteOper: function(val) {
    this.operr = 'this.load('+val+')';
    this.operw = 'this.write('+val+', ';
    this.operws = ')';
  },

  setupAddressing: function(addressing, details) {
    var pc = this.pc + 1;
    this.outa = '';
    var t, mem = this.cpu.mem;
    this.addressing = addressing;
    this.details = details;
    switch (addressing) {
    case 0: // ADDR_ACCUMULATOR
      this.assignOper('a_reg');
      break;
    case 1: // ADDR_IMMEDIATE
      this.operr = mem[pc];
      break;
    case 2: // ADDR_ZERO_PAGE
      t = mem[pc];
      this.assignOper('mem['+t+']');
      break;
    case 3: // ADDR_ZERO_PAGE_X
      t = mem[pc];
      this.outa = 'operp = (x_reg + ' + t + ') & 0xFF;\n';
      this.assignOper('mem[operp]');
      break;
    case 4: // ADDR_ZERO_PAGE_Y
      t = mem[pc];
      this.outa = 'operp = (y_reg + ' + t + ') & 0xFF;\n';
      this.assignOper('mem[operp]');
      break;
    case 5: // ADDR_ABSOLUTE
      t = (mem[pc] | (mem[pc+1]<<8));
      if (details & 4 /* I_JP */) {
        this.operr = t;
      } else {
        this.readwriteOper(t);
      }
      break;
    case 6: // ADDR_ABSOLUTE_X
      t = mem[pc];
      this.outa = 'operp = x_reg + ' + t + ';\n';
      this.outa += 'if (operp & 0x100) cycles--;\n';
      t = mem[pc + 1];
      this.outa += 'operp = (operp + ' + (t << 8) + ') & 0xFFFF;\n';
      this.readwriteOper('operp');
      break;
    case 7: // ADDR_ABSOLUTE_Y
      t = mem[pc];
      this.outa = 'operp = y_reg + ' + t + ';\n';
      this.outa += 'if (operp & 0x100) cycles--;\n';
      t = mem[pc + 1];
      this.outa += 'operp = (operp + ' + (t << 8) + ') & 0xFFFF;\n';
      this.readwriteOper('operp');
      break;
    case 8: // ADDR_INDIRECT
      t = (mem[pc] | (mem[pc+1]<<8));
      /* 6502 bug here! */
      this.outa = 'operp = mem[' + t + ']';
      if ((t & 0xFF) == 0xFF)
        this.outa += ' | (mem[' + (t-0xFF) + '] << 8);\n';
      else
        this.outa += ' | (mem[' + (t+1) + '] << 8);\n';
      this.operr = 'operp';
      /* We don't need to eval "oper" because ADDR_INDIRECT
       * is used only for the JMP instruction
       * */
      break;
    case 9: // ADDR_INDIRECT_X
      t = mem[pc];
      this.outa = 'operp = mem[(' + t + ' + x_reg) & 0xFF] + mem[(' + t + ' + x_reg + 1) & 0xFF] << 8;\n';
      this.readwriteOper('operp');
      break;
    case 10: // ADDR_INDIRECT_Y
      t = mem[pc];
      this.outa = 'operp = mem[' + t + '] + y_reg;\n;';
      this.outa += 'if (operp & 0x100) cycles--;\n';
      this.outa += 'operp = (operp + (mem[' + ((t+1)&0xFF) + '] << 8)) & 0xFFFF\n';
      this.readwriteOper('operp');
      break;
    case 11: // ADDR_RELATIVE
      t = mem[pc];
      if (t & 0x80) t |= 0xFF00;
      this.operr = ((pc + t + 1) & 0xFFFF);
      break;
    case 12: // ADDR_IMPLIED
    default:
      this.operr = 0;
      break;
    }
  },

  useOperIf: function(mask) {
    //if (this.cpu.chgResources[this.pc] & mask) {
      this.append(this.outa);
    //}
  },

  useOper: function() {
    this.append(this.outa);
  },

  appendExpandFlags: function(mask) {
    mask = -1;
    if (mask &   1) this.append('c_flag = p_reg & 1;\n');
    if (mask &   2) this.append('z_flag = p_reg & 2;\n');
    if (mask &   4) this.append('i_flag = p_reg & 4;\n');
    if (mask &   8) this.append('d_flag = p_reg & 8;\n');
    if (mask &  16) this.append('b_flag = p_reg & 16;\n');
    if (mask &  64) this.append('v_flag = p_reg & 64;\n');
    if (mask & 128) this.append('n_flag = p_reg & 128;\n');
  },

  appendCompactFlags: function(mask) {
    mask = -1;
    this.append('p_reg = 32;\n'); // R_FLAG
    if (mask &   1) this.append('if (c_flag) p_reg |= 1;\n');
    if (mask &   2) this.append('if (z_flag) p_reg |= 2;\n');
    if (mask &   4) this.append('if (i_flag) p_reg |= 4;\n');
    if (mask &   8) this.append('if (d_flag) p_reg |= 8;\n');
    if (mask &  16) this.append('if (b_flag) p_reg |= 16;\n');
    if (mask &  64) this.append('if (v_flag) p_reg |= 64;\n');
    if (mask & 128) this.append('if (n_flag) p_reg |= 128;\n');
  },

  appendPush: function(val) {
    this.append('mem[s_reg] = ' + val + ';\n');
    this.append('s_reg = 0x100 | ((s_reg - 1) & 0xFF);\n');
  },

  appendPush16: function(val) {
    this.append('mem[s_reg] = (' + val + ') >> 8;\n');
    this.append('s_reg = 0x100 | ((s_reg - 1) & 0xFF);\n');
    this.append('mem[s_reg] = (' + val + ') & 0xFF;\n');
    this.append('s_reg = 0x100 | ((s_reg - 1) & 0xFF);\n');
  },

  appendPull: function(val) {
    this.append('s_reg = 0x100 | ((s_reg + 1) & 0xFF);\n');
    this.append(val + ' = mem[s_reg];\n');
  },

  appendPull16: function(val) {
    this.append('s_reg = 0x100 | ((s_reg + 1) & 0xFF);\n');
    this.append(val + ' = mem[s_reg];\n');
    this.append('s_reg = 0x100 | ((s_reg + 1) & 0xFF);\n');
    this.append(val + ' |= mem[s_reg] << 8;\n');
  },

  appendIrqProc: function() {
    this.append('if (this.int_pending && cycles > 0) {\n');
    this.append('this.int_pending = false;\n');
    this.appendCompactFlags(~4);
    this.append('this.cyclesToHalt += 7;\n');
    this.appendPush16(this.pc + this.len);
    this.append('p_reg &= ~16;\n'); // ~B_FLAG
    this.appendPush('p_reg');
    this.append('p_reg |= 4;\n'); // I_FLAG
    this.append('pc_reg = (mem[0xFFFE] | (mem[0xFFFF]<<8));\n');
    this.append('break main_loop;\n');
    this.append('}\n');
  },

  appendIf: function(mask, str) {
    //if (this.cpu.chgResources[this.pc] & mask) {
      this.append(str);
    //}
  },

  appendCheckZero: function(val) {
    this.appendIf(2, 'z_flag = (' + val + ' === 0);\n');
  },

  appendCheckSign: function(val) {
    this.appendIf(128, 'n_flag = (' + val + ' & 0x80);\n');
  },

  appendCheckZeroAndSign: function(val) {
    this.appendCheckZero(val);
    this.appendCheckSign(val);
  },

  appendWriteback: function(val) {
    this.append(this.operw + val + this.operws + ';\n');
  },

  appendJump: function() {
    if (this.cpu.followStatus[this.pc] & 2) {
      this.append('innerLabel = ' + this.cpu.innerLabel[this.operr] + ';\n' +
                  'continue;\n');
    } else {
      this.append('break main_loop;\n');
    }
  },

  appendBranch: function(cond) {
    this.append('if (' + cond + ') {\n' +
                'cycles--;\n' +
                'if ('+ (this.operr & 0xFF00) + ' != (pc_reg & 0xFF00)) {\n' +
                '  cycles--;\n' +
                '}\n' +
                'pc_reg = ' + this.operr + ';\n');
    this.appendJump();
    this.append('}\n');
  },

  appendExit: function() {
    this.append('break main_loop;\n');
  },

  endOpcode: function() {
    this.funcAppend(this.opcodeBuffer.join(""));
    if (this.cpu.followStatus[this.pc] & 1) {      
      this.append('pc_reg = ' + (this.pc + this.len) + ';\n');
      this.appendExit();
    }
  },

  endFunction: function() {
    this.funcAppend('}\n}\n' +
                    'p_reg = 32;\n' +
                    'if (c_flag) p_reg |= 1;\n' +
                    'if (z_flag) p_reg |= 2;\n' +
                    'if (i_flag) p_reg |= 4;\n' +
                    'if (d_flag) p_reg |= 8;\n' +
                    'if (b_flag) p_reg |= 16;\n' +
                    'if (v_flag) p_reg |= 64;\n' +
                    'if (n_flag) p_reg |= 128;\n' +
                    'this.p_reg = p_reg; this.pc_reg = pc_reg; this.s_reg = s_reg;\n' +
                    'this.a_reg = a_reg; this.x_reg = x_reg; this.y_reg = y_reg;\n' +
                    'return cycles;\n');
  },

  output: function() {
    var out = this.buffer.join("");
    if (window.code === undefined) window.code = '';
    window.code += out;
    return new Function('cycles', 'innerLabel', out);
  }
};

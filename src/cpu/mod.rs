use std::path::Path;
use std::io;
use std::fs::File;
use std::io::{Read, ErrorKind};
use crate::bus::Bus;

/// The PSX's MIPS R3000 based CPU
pub struct CPU {
    /// The program counter register, holding the address of the next instruction
    pc: u32,
    /// Address of the instruction currently being executed. Used for setting the EPC in exceptions
    pc_current: u32,
    /// Next value for the Program Counter, used to simulate the branch delay slot
    pc_next: u32,
    /// Cop0 status register (register 12)
    sr: u32,
    /// Cop0 register 13: the Cause register
    cause: u32,
    /// Cop0 register 14: the EPC
    epc: u32,
    /// The CPU's 32 general-purpose registers
    regs: [u32; 32],
    /// The 2nd set of registers used to emulate the load-delay slot accurately. The contain
    /// the output of the current instruction.
    out_regs: [u32; 32],
    /// HI register for division remainder and multiplication high result
    hi: u32,
    /// LO register for division remainder and multiplication low result
    lo: u32,
    /// Load initiated by the current instruction
    load: (RegisterIndex, u32),
    /// Set the current instruction if a branch occurred and the next instruction will be in the
    /// delay slot
    branch: bool,
    /// Set if the current instruction executes in the delay slot
    delay_slot: bool,
    /// Bus that controls memory access
    bus: Bus,
}

impl CPU {
    pub fn new(bus: Bus) -> Self {
        // Reset the registers to a fixed garbage value
        let mut regs = [0xdeadbeef; 32];

        // Register 0 is hardwired to 0x0
        regs[0] = 0x0;

        // Set the PC to the beginning of the PSX BIOS
        let pc = 0xbfc00000;

        CPU {
            pc,
            pc_current: pc,
            // Set the next pc four bytes ahead of the current PC
            pc_next: pc.wrapping_add(4),
            sr: 0,
            cause: 0,
            epc: 0,
            regs,
            // The out-regs are the same as the the regular registers on reset
            out_regs: regs,
            hi: 0xdeadbeef,
            lo: 0xdeadbeef,
            load: (RegisterIndex(0), 0),
            branch: false,
            delay_slot: false,
            bus,
        }
    }

    /// Fetch the next instruction and execute it
    pub fn step(&mut self) {
        // Save the address of the current instruction to save in `EPC` in case of an exception
        self.pc_current = self.pc;

        // Check if Program Counter is not correctly aligned
        if self.pc_current % 4 != 0 {
            self.exception(Exception::ReadAddressError);
            return;
        }

        // Fetch the instruction at the current PC
        let instruction = Instruction(self.mem_read32(self.pc));

        // Increment the next PC to point to the next instruction
        self.pc = self.pc_next;
        self.pc_next = self.pc_next.wrapping_add(4);

        // If the last instruction was a branch then we're in the delay slot
        self.delay_slot = self.branch;
        self.branch = false;

        // Execute the pending load (if any, otherwise it will load $zero which is NOP).
        // `set_reg` works only on `out_regs` so this operation won't be visible the next instruction.
        let (RegisterIndex(reg), val) = self.load;
        self.set_reg(RegisterIndex(reg), val);

        // We reset the load to target register 0 for the next instruction
        self.load = (RegisterIndex(0), 0);

        println!("Instruction: 0x{:08x} -- 0b{:06b} -- 0b{:06b} -- PC: 0x{:08x}",
                instruction.0,
                instruction.function(),
                instruction.subfunction(),
                self.pc
        );

        self.exec(instruction);

        // Copy the output registers as input for the next instruction
        self.regs = self.out_regs;
    }

    /// Decode and execute an instruction
    fn exec(&mut self, instruction: Instruction) {
        match instruction.function() {
            // Subfunctions
            0b000000 => match instruction.subfunction() {
                0b000000 => self.op_sll(instruction),
                0b000010 => self.op_srl(instruction),
                0b000011 => self.op_sra(instruction),
                0b000100 => self.op_sllv(instruction),
                0b000110 => self.op_srlv(instruction),
                0b000111 => self.op_srav(instruction),
                0b001000 => self.op_jr(instruction),
                0b001001 => self.op_jalr(instruction),
                0b001100 => self.op_syscall(instruction),
                0b010000 => self.op_mfhi(instruction),
                0b010001 => self.op_mthi(instruction),
                0b010010 => self.op_mflo(instruction),
                0b010011 => self.op_mtlo(instruction),
                0b011001 => self.op_multu(instruction),
                0b011010 => self.op_div(instruction),
                0b011011 => self.op_divu(instruction),
                0b100000 => self.op_add(instruction),
                0b100001 => self.op_addu(instruction),
                0b100011 => self.op_subu(instruction),
                0b100100 => self.op_and(instruction),
                0b100101 => self.op_or(instruction),
                0b100111 => self.op_nor(instruction),
                0b101010 => self.op_slt(instruction),
                0b101011 => self.op_sltu(instruction),
                _ => unimplemented!("UNHANDLED_INSTRUCTION_0x{:08x}", instruction.0),
            }

            0b000001 => self.op_bxx(instruction),
            0b000010 => self.op_j(instruction),
            0b000011 => self.op_jal(instruction),
            0b000100 => self.op_beq(instruction),
            0b000101 => self.op_bne(instruction),
            0b000110 => self.op_blez(instruction),
            0b000111 => self.op_bgtz(instruction),
            0b001000 => self.op_addi(instruction),
            0b001001 => self.op_addiu(instruction),
            0b001010 => self.op_slti(instruction),
            0b001011 => self.op_sltiu(instruction),
            0b001100 => self.op_andi(instruction),
            0b001101 => self.op_ori(instruction),
            0b001111 => self.op_lui(instruction),
            0b010000 => self.op_cop0(instruction),
            0b100000 => self.op_lb(instruction),
            0b100001 => self.op_lh(instruction),
            0b100011 => self.op_lw(instruction),
            0b100100 => self.op_lbu(instruction),
            0b100101 => self.op_lhu(instruction),
            0b101000 => self.op_sb(instruction),
            0b101001 => self.op_sh(instruction),
            0b101011 => self.op_sw(instruction),

            _ => unimplemented!("UNHANDLED_INSTRUCTION_0x{:08x}", instruction.0),
        }
    }

    fn get_reg(&self, index: RegisterIndex) -> u32 {
        self.regs[index.0 as usize]
    }

    fn set_reg(&mut self, index: RegisterIndex, value: u32) {
        self.out_regs[index.0 as usize] = value;

        // Register 0 is hardwired to 0x0
        self.out_regs[0] = 0;
    }

    /// Read a single byte from memory at the specified address
    fn mem_read8(&self, addr: u32) -> u8 {
        self.bus.mem_read8(addr)
    }

    /// Read a 16-bit word from memory at the specified address
    fn mem_read16(&self, addr: u32) -> u16 {
        self.bus.mem_read16(addr)
    }

    /// Read a 32-bit word from memory at the specified address
    fn mem_read32(&self, addr: u32) -> u32 {
        self.bus.mem_read32(addr)
    }

    /// Write a single byte to memory at the specified address
    fn mem_write8(&mut self, addr: u32, val: u8) {
        self.bus.mem_write8(addr, val);
    }

    /// Write a 16-bit word to memory at the specified address
    fn mem_write16(&mut self, addr: u32, val: u16) {
        self.bus.mem_write16(addr, val);
    }

    /// Write a 32-bit word to memory at the specified address
    fn mem_write32(&mut self, addr: u32, val: u32) {
        self.bus.mem_write32(addr, val);
    }

    /// Branch to immediate value `offset`
    fn branch(&mut self, offset: u32) {
        // Offset immediates are shifted two places to the right since program counter addresses
        // have to be aligned on 32 bits at all times
        let offset = offset << 2;

        self.pc_next = self.pc.wrapping_add(offset);

        self.branch = true;
    }

    /// Trigger an exception
    fn exception(&mut self, cause: Exception) {
        // Exception handler address depends on the 'BEV' bit
        let handler = match self.sr & (1 << 22) != 0 {
            true => 0xbfc00180,
            false => 0x80000080,
        };

        // Shift bits [5:0] of 'SR' two places to the left. Those bits are three pairs of
        // "Interrupt Enable / User Mode" bits behaving like a stack 3 entries deep. Entering
        // an exception pushes a pair of zeroes by left shifting the stack which disables interrupts
        // and puts the CPU in kernel mode. The original third entry is discarded (it's up to the
        // kernel to handle mode than two recursive exception levels).
        let mode = self.sr & 0x3f;
        self.sr = self.sr & !0x3f;
        self.sr = self.sr | (mode << 2) & 0x3f;

        // Update the Cause register with the exception code (bits [6:2])
        self.cause = (cause as u32) << 2;

        // Save current instruction address in 'EPC'
        self.epc = self.pc_current;

        if self.delay_slot {
            // When an exception occurs in a delay slot 'EPC' points to the branch instruction
            // and bit 31 of 'Cause' is set
            self.epc = self.epc.wrapping_sub(4);
            self.cause = self.cause | (1 << 31);
        }

        // Exceptions do not have a branch delay, we dump directly in the handler
        self.pc = handler;
        self.pc_next = self.pc.wrapping_add(4);
    }

    /// System call
    fn op_syscall(&mut self, _: Instruction) {
        self.exception(Exception::SysCall);
    }

    /// Add and generate an exception on overflow
    fn op_add(&mut self, instruction: Instruction) {
        let s = instruction.rs();
        let t = instruction.rt();
        let d = instruction.rd();

        let s = self.get_reg(s) as i32;
        let t = self.get_reg(t) as i32;

        // Check for overflow
        match s.checked_add(t) {
            Some(v) => self.set_reg(d, v as u32),
            None => self.exception(Exception::Overflow),
        };
    }

    /// Add Immediate Unsigned and check for overflow
    fn op_addi(&mut self, instruction: Instruction) {
        let i = instruction.immediate_signed() as i32;
        let t = instruction.rt();
        let s = instruction.rs();

        let s = self.get_reg(s) as i32;

        // Check for overflow
        match s.checked_add(i) {
            Some(v) => self.set_reg(t, v as u32),
            None => self.exception(Exception::Overflow),
        };
    }

    /// Add Immediate Unsigned
    fn op_addiu(&mut self, instruction: Instruction) {
        let i = instruction.immediate_signed();
        let t = instruction.rt();
        let s = instruction.rs();

        let v = self.get_reg(s).wrapping_add(i);

        self.set_reg(t, v);
    }

    /// Add Unsigned
    fn op_addu(&mut self, instruction: Instruction) {
        let s = instruction.rs();
        let t = instruction.rt();
        let d = instruction.rd();

        let v = self.get_reg(s).wrapping_add(self.get_reg(t));

        self.set_reg(d, v);
    }

    /// Bitwise AND
    fn op_and(&mut self, instruction: Instruction) {
        let d = instruction.rd();
        let s = instruction.rs();
        let t = instruction.rt();

        let v = self.get_reg(s) & self.get_reg(t);

        self.set_reg(d, v);
    }

    /// Bitwise AND Immediate
    fn op_andi(&mut self, instruction: Instruction) {
        let i = instruction.immediate();
        let t = instruction.rt();
        let s = instruction.rs();

        let v = self.get_reg(s) & i;

        self.set_reg(t, v);
    }

    /// Branch if Equal
    fn op_beq(&mut self, instruction: Instruction) {
        let i = instruction.immediate_signed();
        let s = instruction.rs();
        let t = instruction.rt();

        if self.get_reg(s) == self.get_reg(t) {
            self.branch(i)
        }
    }

    /// Branch if Greater Than Zero
    fn op_bgtz(&mut self, instruction: Instruction) {
        let i = instruction.immediate_signed();
        let s = instruction.rs();

        let v = self.get_reg(s) as i32;

        if v > 0 {
            self.branch(i);
        }
    }

    /// Branch if Less than or Equal to Zero
    fn op_blez(&mut self, instruction: Instruction) {
        let i = instruction.immediate_signed();
        let s = instruction.rs();

        let v = self.get_reg(s) as i32;

        if v <= 0 {
            self.branch(i);
        }
    }

    /// Branch If Not Equal
    fn op_bne(&mut self, instruction: Instruction) {
        let i = instruction.immediate_signed();
        let s = instruction.rs();
        let t = instruction.rt();

        if self.get_reg(s) != self.get_reg(t) {
            self.branch(i);
        }
    }

    /// Generic branch instruction for BGEZ, BLTZ, BGEZAL, BLTZAL
    /// Bits 16 and 20 are used to figure out which one to use
    fn op_bxx(&mut self, instruction: Instruction) {
        let i = instruction.immediate_signed();
        let s = instruction.rs();

        let instruction = instruction.0;

        let is_bgez = (instruction >> 16) & 1;
        let is_link = (instruction >> 20) & 1 != 0;

        let v = self.get_reg(s) as i32;

        // Test "less than zero"
        let test = (v < 0) as u32;

        // If the test is "greater than or equal to zero" we need to negate the comparison above
        // since ("a >= 0" <=> "!(a < 0)"). The XOR takes cares of that.
        let test = test ^ is_bgez;

        if test != 0 {
            if is_link {
                let ra = self.pc_next;

                // Store return address in R31
                self.set_reg(RegisterIndex(31), ra);
            }

            self.branch(i);
        }
    }

    /// Coprocessor 0 opcode
    fn op_cop0(&mut self, instruction: Instruction) {
        match instruction.cop_opcode() {
            0b00000 => self.op_mfc0(instruction),
            0b00100 => self.op_mtc0(instruction),
            0b10000 => self.op_rfe(instruction),
            code => unimplemented!("UNHANDLED_COP0_INSTRUCTION_0x{:08x}", code),
        }
    }

    /// Divide signed
    fn op_div(&mut self, instruction: Instruction) {
        let s = instruction.rs();
        let t = instruction.rt();

        let n = self.get_reg(s) as i32;
        let d = self.get_reg(t) as i32;

        if d == 0 {
            // Division by zero, results are bogus
            self.hi = n as u32;

            if n >= 0 {
                self.lo = 0xffffffff;
            } else {
                self.lo = 1;
            }
        } else if n as u32 == 0x80000000 && d == -1 {
            // The result is not representable in a 32 bit signed integer
            self.hi = 0;
            self.lo = 0x80000000;
        } else {
            self.hi = (n % d) as u32;
            self.lo = (n / d) as u32;
        }
    }

    /// Divide Unsigned
    fn op_divu(&mut self, instruction: Instruction) {
        let s = instruction.rs();
        let t = instruction.rt();

        let n = self.get_reg(s);
        let d = self.get_reg(t);

        if d == 0 {
            // Divide by zero, results are bogus
            self.hi = n;
            self.lo = 0xffffffff;
        } else {
            self.hi = n % d;
            self.lo = n / d;
        }
    }

    /// Jump
    fn op_j(&mut self, instruction: Instruction) {
        let i = instruction.immediate_jump();

        self.pc_next = (self.pc & 0xf0000000) | (i << 2);

        self.branch = true;
    }

    /// Jump and Link
    fn op_jal(&mut self, instruction: Instruction) {
        let ra = self.pc_next;

        // The return address is stored in register 31
        self.set_reg(RegisterIndex(31), ra);

        self.op_j(instruction);

        self.branch = true;
    }

    /// Jump And Link Register
    fn op_jalr(&mut self, instruction: Instruction) {
        let d = instruction.rd();
        let s = instruction.rs();

        let ra = self.pc_next;

        // Store return address in register d
        self.set_reg(d, ra);

        self.pc_next = self.get_reg(s);

        self.branch = true;
    }

    /// Jump Register
    fn op_jr(&mut self, instruction: Instruction) {
        let s = instruction.rs();

        self.pc_next = self.get_reg(s);

        self.branch = true;
    }

    /// Load Byte
    fn op_lb(&mut self, instruction: Instruction) {
        let i = instruction.immediate_signed();
        let t = instruction.rt();
        let s = instruction.rs();

        let addr = self.get_reg(s).wrapping_add(i);

        // Cast as i8 to force sign extension
        let v = self.mem_read8(addr) as i8;

        // Put the load in the delay slot
        self.load = (t, v as u32);
    }

    /// Load Byte Unsigned
    fn op_lbu(&mut self, instruction: Instruction) {
        let i = instruction.immediate_signed();
        let t = instruction.rt();
        let s = instruction.rs();

        let addr = self.get_reg(s).wrapping_add(i);
        let v = self.mem_read8(addr);

        // Put the load in the delay slot
        self.load = (t, v as u32);
    }

    /// Load Halfword signed
    fn op_lh(&mut self, instruction: Instruction) {
        let i = instruction.immediate_signed();
        let t = instruction.rt();
        let s = instruction.rs();

        let addr = self.get_reg(s).wrapping_add(i);

        // Cast as i16 to force sign extension
        let v = self.mem_read16(addr) as i16;

        // Put the load in the delay slot
        self.load = (t, v as u32);
    }

    /// Load Half-word Unsigned
    fn op_lhu(&mut self, instruction: Instruction) {
        let i = instruction.immediate_signed();
        let t = instruction.rt();
        let s = instruction.rs();

        let addr = self.get_reg(s).wrapping_add(i);

        // Address must be 16 bit aligned
        if addr % 2 == 0 {
            let v = self.mem_read16(addr);

            // Put the load in the delay slot
            self.load = (t, v as u32);
        } else {
            self.exception(Exception::ReadAddressError);
        }
    }

    /// Load Upper Immediate
    fn op_lui(&mut self, instruction: Instruction) {
        let i = instruction.immediate();
        let t = instruction.rt();

        // Low 16 bits are set to 0
        let v = i << 16;

        self.set_reg(t, v);
    }

    /// Load Word
    fn op_lw(&mut self, instruction: Instruction) {
        if self.sr & 0x10000 != 0 {
            // Ignore cache writes
            println!("IGNORING_READ_WHILE_CACHE_IS_ISOLATED");
        } else {
            let i = instruction.immediate_signed();
            let t = instruction.rt();
            let s = instruction.rs();

            let addr = self.get_reg(s).wrapping_add(i);

            // Address must be 32 bit aligned
            if addr % 4 == 0 {
                let v = self.mem_read32(addr);

                // Put the load in the delay slot
                self.load = (t, v);
            } else {
                self.exception(Exception::ReadAddressError);
            }
        }
    }

    /// Move From Coprocessor 0
    fn op_mfc0(&mut self, instruction: Instruction) {
        let cpu_r = instruction.rt();
        let cop_r = instruction.rd().0;

        let v = match cop_r {
            12 => self.sr,
            13 => self.cause,
            14 => self.epc,
            _  => unimplemented!("UNHANDLED_READ_FROM_COP0_REGISTER_{}", cop_r),
        };

        self.load = (cpu_r, v);
    }

    /// Move From HI
    fn op_mfhi(&mut self, instruction: Instruction) {
        let d = instruction.rd();

        self.set_reg(d, self.hi);
    }

    /// Move From LO
    fn op_mflo(&mut self, instruction: Instruction) {
        let d = instruction.rd();

        self.set_reg(d, self.lo);
    }

    /// Move to LO
    fn op_mtlo(&mut self, instruction: Instruction) {
        let s = instruction.rs();

        self.lo = self.get_reg(s);
    }

    /// Move to HI
    fn op_mthi(&mut self, instruction: Instruction) {
        let s = instruction.rs();

        self.hi = self.get_reg(s);
    }

    /// Move To Coprocessor 0
    fn op_mtc0(&mut self, instruction: Instruction) {
        let cpu_r = instruction.rt();
        let cop_r = instruction.rd().0;

        let v = self.get_reg(cpu_r);

        match cop_r {
            // COP0 Breakpoint registers
            3 | 5 | 6 | 7 | 9 | 11 => {
                if v != 0 {
                    // TODO: Is it necessary to support these?
                    unimplemented!("UNHANDLED_WRITE_TO_COP0_BREAKPOINT_REGISTER {}", cop_r);
                }
            },
            // COP0 Status register
            12 => self.sr = v,
            // COP0 Cause register
            13 => {
                if v != 0 {
                    unimplemented!("UNHANDLED_WRITE_TO_COP0_CAUSE_REGISTER");
                }
            },
            _ => unimplemented!("UNHANDLED_COP0_REGISTER_0x{:08x}", instruction.0),
        }
    }

    /// Multiply Unsigned
    fn op_multu(&mut self, instruction: Instruction) {
        let s = instruction.rs();
        let t = instruction.rt();

        let a = self.get_reg(s) as u64;
        let b = self.get_reg(t) as u64;

        let v = a * b;

        self.hi = (v >> 32) as u32;
        self.lo = v as u32;
    }

    /// Bitwise Not OR
    fn op_nor(&mut self, instruction: Instruction) {
        let d = instruction.rd();
        let s = instruction.rs();
        let t = instruction.rt();

        let v = !(self.get_reg(s) | self.get_reg(t));

        self.set_reg(d, v);
    }

    /// Bitwise OR
    fn op_or(&mut self, instruction: Instruction) {
        let d = instruction.rd();
        let s = instruction.rs();
        let t = instruction.rt();

        let v = self.get_reg(s) | self.get_reg(t);

        self.set_reg(d, v);
    }

    /// Bitwise OR immediate
    fn op_ori(&mut self, instruction: Instruction) {
        let i = instruction.immediate();
        let s = instruction.rs();
        let t = instruction.rt();

        let v = self.get_reg(s) | i;

        self.set_reg(t, v);
    }

    /// Return From Exception
    fn op_rfe(&mut self, instruction: Instruction) {
        // There are other instructions with the same encoding but all are virtual memory related
        // and the PSX doesn't implement them. Still, let's make sure we're not running buggy code.
        if instruction.0 & 0x3f != 0b010000 {
            panic!("INVALID_COP0_INSTRUCTION_0x{:08x}", instruction.0);
        }

        // Restore the pre-exception mode by shifting the "Interrupt Enable / User Mode" stack
        // back to its original position.
        let mode = self.sr & 0x3f;
        self.sr = self.sr & !0x3f;
        self.sr = self.sr | (mode >> 2);
    }

    /// Store Byte
    fn op_sb(&mut self, instruction: Instruction) {
        if self.sr & 0x10000 != 0 {
            // Ignore cache writes
            println!("IGNORING_READ_WHILE_CACHE_IS_ISOLATED");
        } else {
            let i = instruction.immediate_signed();
            let t = instruction.rt();
            let s = instruction.rs();

            let addr = self.get_reg(s).wrapping_add(i);
            let v = self.get_reg(t);

            self.mem_write8(addr, v as u8);
        }
    }

    /// Store Half-word
    fn op_sh(&mut self, instruction: Instruction) {
        if self.sr & 0x10000 != 0 {
            // Ignore cache writes
            println!("IGNORING_WRITE_WHILE_CACHE_IS_ISOLATED");
        } else {
            let i = instruction.immediate_signed();
            let t = instruction.rt();
            let s = instruction.rs();

            let addr = self.get_reg(s).wrapping_add(i);
            let v = self.get_reg(t);

            // Address must be 16 bit aligned
            if addr % 2 == 0 {
                self.mem_write16(addr, v as u16);
            } else {
                self.exception(Exception::WriteAddressError);
            }

            self.mem_write16(addr, v as u16);
        }
    }

    /// Shift Left Logical
    fn op_sll(&mut self, instruction: Instruction) {
        let i = instruction.shift();
        let t = instruction.rt();
        let d = instruction.rd();

        let v = self.get_reg(t) << i;

        self.set_reg(d, v);
    }

    /// Shift Left Logical Variable
    fn op_sllv(&mut self, instruction: Instruction) {
        let d = instruction.rd();
        let s = instruction.rs();
        let t = instruction.rt();

        // Shift amount is truncated to 5 bits
        let v = self.get_reg(t) << (self.get_reg(s) & 0x1f);

        self.set_reg(d, v);
    }

    /// Set if Less Than Immediate signed
    fn op_slti(&mut self, instruction: Instruction) {
        let i = instruction.immediate_signed() as i32;
        let s = instruction.rs();
        let t = instruction.rt();

        let v = (self.get_reg(s) as i32) < i;

        self.set_reg(t, v as u32);
    }

    /// Set if LEss Than Immediate Unsigned
    fn op_sltiu(&mut self, instruction: Instruction) {
        let i = instruction.immediate_signed();
        let s = instruction.rs();
        let t = instruction.rt();

        let v = self.get_reg(s) < i;

        self.set_reg(t, v as u32);
    }

    /// Set on Less Than signed
    fn op_slt(&mut self, instruction: Instruction) {
        let d = instruction.rd();
        let s = instruction.rs();
        let t = instruction.rt();

        let s = self.get_reg(s) as i32;
        let t = self.get_reg(t) as i32;

        let v = s < t;

        self.set_reg(d, v as u32);
    }

    /// Set On Less Then Unsigned
    fn op_sltu(&mut self, instruction: Instruction) {
        let d = instruction.rd();
        let s = instruction.rs();
        let t = instruction.rt();

        let v = self.get_reg(s) < self.get_reg(t);

        self.set_reg(d, v as u32);
    }

    /// Shift Right Arithmetic Variable
    fn op_srav(&mut self, instruction: Instruction) {
        let d = instruction.rd();
        let s = instruction.rs();
        let t = instruction.rt();

        // Shift amount is truncated to 5 bits
        let v = (self.get_reg(t) as i32) >> (self.get_reg(s) & 0x1f);

        self.set_reg(d, v as u32);
    }

    /// Shift Right Logical
    fn op_srl(&mut self, instruction: Instruction) {
        let i = instruction.shift();
        let t = instruction.rt();
        let d = instruction.rd();

        let v = self.get_reg(t) >> i;

        self.set_reg(d, v);
    }

    /// Shift Right Logical Variable
    fn op_srlv(&mut self, instruction: Instruction) {
        let d = instruction.rd();
        let s = instruction.rs();
        let t = instruction.rt();

        // Shift amount is truncated to 5 bits
        let v = self.get_reg(t) >> (self.get_reg(s) & 0x1f);

        self.set_reg(d, v);
    }

    /// Subtract Unsigned
    fn op_subu(&mut self, instruction: Instruction) {
        let s = instruction.rs();
        let t = instruction.rt();
        let d = instruction.rd();

        let v = self.get_reg(s).wrapping_sub(self.get_reg(t));

        self.set_reg(d, v);
    }

    /// Shift Right Arithmetic
    fn op_sra(&mut self, instruction: Instruction) {
        let i = instruction.shift();
        let t = instruction.rt();
        let d = instruction.rd();

        let v = (self.get_reg(t) as i32) >> i;

        self.set_reg(d, v as u32);
    }

    /// Store word
    fn op_sw(&mut self, instruction: Instruction) {
        if self.sr & 0x10000 != 0 {
            // Ignore cache writes
            println!("IGNORING_WRITE_WHILE_CACHE_IS_ISOLATED");
        } else {
            let i = instruction.immediate_signed();
            let s = instruction.rs();
            let t = instruction.rt();

            let addr = self.get_reg(s).wrapping_add(i);
            let val = self.get_reg(t);

            if addr % 4 == 0 {
                self.mem_write32(addr, val);
            } else {
                self.exception(Exception::WriteAddressError);
            }
        }
    }
}

/// The PSX BIOS image size is 512kb
pub const BIOS_SIZE: u32 = 512 * 1024;

/// The PSX BIOS image
pub struct BIOS {
    data: Vec<u8>,
}

impl BIOS {
    /// Load a new BIOS file from the file located at `path`
    pub fn from_file(path: &impl AsRef<Path>) -> Result<Self, io::Error> {
        let file = File::open(path)?;
        let mut data = Vec::with_capacity(BIOS_SIZE as usize);

        file.take(BIOS_SIZE as u64).read_to_end(&mut data)?;

        if data.len() == BIOS_SIZE as usize {
            Ok(Self {
                data
            })
        } else {
            Err(io::Error::new(ErrorKind::InvalidInput, "INVALID_BIOS_SIZE"))
        }
    }

    /// Read a single byte from the BIOS at the specified address
    pub fn mem_read8(&self, offset: u32) -> u8 {
        self.data[offset as usize]
    }

    /// Read a 32-bit word from the BIOS at the specified offset
    pub fn mem_read32(&self, offset: u32) -> u32 {
        let offset = offset as usize;

        let b0 = self.data[offset + 0];
        let b1 = self.data[offset + 1];
        let b2 = self.data[offset + 2];
        let b3 = self.data[offset + 3];

        u32::from_le_bytes([b0, b1, b2, b3])
    }
}

struct Instruction(u32);

struct RegisterIndex(u32);

impl Instruction {
    /// Reads the coprocessor opcode in bits [25:21] of the instruction
    fn cop_opcode(&self) -> u32 {
        let Instruction(op) = self;

        (op >> 21) & 0x1f
    }

    /// Reads the function from bits [31:26] of the instruction
    fn function(&self) -> u32 {
        let Instruction(op) = self;

        op >> 26
    }

    /// Reads the immediate value from bits [16:0] of the instruction
    fn immediate(&self) -> u32 {
        let Instruction(op) = self;

        op &0xffff
    }

    /// Reads the jump target stored in bits [25:0]
    fn immediate_jump(&self) -> u32 {
        let Instruction(op) = self;

        op & 0x3ffffff
    }

    /// Reads the immediate value from bits [16:0] as a sign-extended 32-bit value
    fn immediate_signed(&self) -> u32 {
        let Instruction(op) = self;

        let val = (op & 0xffff) as i16;

        val as u32
    }

    /// Reads the register index in bits [15:11] of the instruction
    fn rd(&self) -> RegisterIndex {
        let Instruction(op) = self;

        RegisterIndex((op >> 11) & 0x1f)
    }

    /// Reads the register index in bits [25:21] of the instruction
    fn rs(&self) -> RegisterIndex {
        let Instruction(op) = self;

        RegisterIndex((op >> 21) & 0x1f)
    }

    /// Reads the register index from bits [20:16] of the instruction
    fn rt(&self) -> RegisterIndex {
        let Instruction(op) = self;

        RegisterIndex((op >> 16) & 0x1f)
    }

    /// Reads the shifted immediate value from bits [10:6] of the instruction
    fn shift(&self) -> u32 {
        let Instruction(op) = self;

        (op >> 6) & 0x1f
    }

    /// Reads the subfunction from bits [5:0] of the instruction
    fn subfunction(&self) -> u32 {
        let Instruction(op) = self;

        op & 0x3f
    }
}

/// Exception types (as stored in the Cause register)
enum Exception {
    /// Arithmetic overflow
    Overflow = 0xc,
    /// Address error on read
    ReadAddressError = 0x4,
    /// System call (caused by the SYSCALL opcode)
    SysCall = 0x8,
    /// Address error on write
    WriteAddressError = 0x5,
}
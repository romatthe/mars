use std::path::Path;
use std::io;
use std::fs::File;
use std::io::{Read, ErrorKind};
use crate::bus::Bus;

/// The PSX's MIPS R3000 based CPU
pub struct CPU {
    /// The program counter register, holding the address of the next instruction
    pc: u32,
    /// The CPU's 32 general-purpose registers
    regs: [u32; 32],
    /// Bus that controls memory map
    bus: Bus,
}

impl CPU {
    pub fn new(bus: Bus) -> Self {
        // Reset the registers to a fixed garbage value
        let mut regs = [0xdeadbeef; 32];

        // Register 0 is hardwired to 0x0
        regs[0] = 0x0;

        CPU {
            // Set the PC to the beginning of the PSX BIOS
            pc: 0xbfc00000,
            regs,
            bus
        }
    }

    /// Fetch the next instruction and execute it
    pub fn step(&mut self) {
        // Fetch the next instruction
        let instruction = self.mem_read32(self.pc);

        // Increment the PC to the next instruction (MIPS architecture has fixed length instructions)
        self.pc = self.pc.wrapping_add(4);

        println!("Instruction: 0x{:08x}", instruction);

        self.exec(Instruction(instruction));
    }

    /// Decode and execute an instruction
    fn exec(&mut self, instruction: Instruction) {
        match instruction.function() {
            // Subfunctions
            0b000000 => match instruction.subfunction() {
                0b000000 => self.op_sll(instruction),
                _ => unimplemented!("UNHANDLED_INSTRUCTION_0x{:08x}", instruction.0),
            }

            0b000010 => self.op_j(instruction),
            0b001001 => self.op_addiu(instruction),
            0b001101 => self.op_ori(instruction),
            0b001111 => self.op_lui(instruction),
            0b101011 => self.op_sw(instruction),

            _ => unimplemented!("UNHANDLED_INSTRUCTION_0x{:08x}", instruction.0),
        }
    }

    /// Read a 32-bit word from memory at the specified address
    fn mem_read32(&self, addr: u32) -> u32 {
        self.bus.mem_read32(addr)
    }

    /// Write a 32-bit word to memory at the specified address
    fn mem_write32(&mut self, addr: u32, val: u32) {
        self.bus.mem_write32(addr, val)
    }

    fn get_reg(&self, index: u32) -> u32 {
        self.regs[index as usize]
    }

    fn set_reg(&mut self, index: u32, value: u32) {
        self.regs[index as usize] = value;

        // Register 0 is hardwired to 0x0
        self.regs[0] = 0;
    }

    /// Add Immedate Unsigned
    fn op_addiu(&mut self, instruction: Instruction) {
        let i = instruction.immediate_signed();
        let t = instruction.rt();
        let s = instruction.rs();

        let v = self.get_reg(s).wrapping_add(i);

        self.set_reg(t, v);
    }

    /// Jump
    fn op_j(&mut self, instruction: Instruction) {
        let i = instruction.immediate_jump();

        self.pc = (self.pc & 0xf0000000) | (i << 2);
    }

    /// Load Upper Immediate
    fn op_lui(&mut self, instruction: Instruction) {
        let i = instruction.immediate();
        let t = instruction.rt();

        // Low 16 bits are set to 0
        let v = i << 16;

        self.set_reg(t, v);
    }

    /// Bitwise OR immediate
    fn op_ori(&mut self, instruction: Instruction) {
        let i = instruction.immediate();
        let s = instruction.rs();
        let t = instruction.rt();

        let v = self.get_reg(s) | i;

        self.set_reg(t, v);
    }

    /// Shift Left Logical
    fn op_sll(&mut self, instruction: Instruction) {
        let i = instruction.shift();
        let t = instruction.rt();
        let d = instruction.rd();

        let v = self.get_reg(t) << i;

        self.set_reg(d, v);
    }

    /// Store word
    fn op_sw(&mut self, instruction: Instruction) {
        let i = instruction.immediate_signed();
        let s = instruction.rs();
        let t = instruction.rt();

        let addr = self.get_reg(s).wrapping_add(i);
        let val = self.get_reg(t);

        self.mem_write32(addr, val);
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

impl Instruction {
    /// Reads the function from bits [31:36] of the instruction
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
    fn rd(&self) -> u32 {
        let Instruction(op) = self;

        (op >> 11) % 0x1f
    }

    /// Reads the register index in bits [25:21] of the instruction
    fn rs(&self) -> u32 {
        let Instruction(op) = self;

        (op >> 21) & 0x1f
    }

    /// Reads the register index from bits [20:16] of the instruction
    fn rt(&self) -> u32 {
        let Instruction(op) = self;

        (op >> 16) & 0x1f
    }

    /// Reads the shifted immediate value from bits [10:6] of the instruction
    fn shift(&self) -> u32 {
        let Instruction(op) = self;

        (op >> 6) & 0x1f
    }

    /// Reads the subfunction from bits [5:0] of the instruction
    fn subfunction(&self) -> u32 {
        let Instruction(op) = self;

        (op >> 6) & 0x1f
    }
}
//! PSX Memory map:
//!
//! KUSEG     KSEG0     KSEG1
//! 00000000h 80000000h A0000000h  2048K  Main RAM (first 64K reserved for BIOS)
//! 1F000000h 9F000000h BF000000h  8192K  Expansion Region 1 (ROM/RAM)
//! 1F800000h 9F800000h    --      1K     Scratchpad (D-Cache used as Fast RAM)
//! 1F801000h 9F801000h BF801000h  8K     I/O Ports
//! 1F802000h 9F802000h BF802000h  8K     Expansion Region 2 (I/O Ports)
//! 1FA00000h 9FA00000h BFA00000h  2048K  Expansion Region 3 (whatever purpose)
//! 1FC00000h 9FC00000h BFC00000h  512K   BIOS ROM (Kernel) (4096K max)
//!       FFFE0000h (KSEG2)        0.5K   I/O Ports (Cache Control)

use crate::cpu::{BIOS, BIOS_SIZE};
use crate::ram::RAM;
use std::sync::mpsc::RecvTimeoutError::Timeout;

/// BIOS image region
const BIOS: MemRange = MemRange(0x1fc00000 , 512 * 1024);

/// Cache control register (Full address since it's in KSEG2)
const CACHE_CONTROL: MemRange = MemRange(0xfffe0130, 4);

/// Expansion 1 region
const EXPANSION1: MemRange = MemRange(0x1f000000, 512 * 1024);

/// Expansion 2 region
const EXPANSION2: MemRange = MemRange(0x1f802000, 66);

/// Interrupt Control registers
const IRQ_CONTROL: MemRange = MemRange(0x1f801070, 8);

/// Memory latency and expansion mapping region
const MEM_CONTROL: MemRange = MemRange(0x1f801000, 36);

/// RAM region
const RAM: MemRange = MemRange(0x00000000, 2 * 1024 * 1024);

/// Register that has something to do with RAM configuration configured by the BIOS
const RAM_SIZE: MemRange = MemRange(0x1f801060, 4);

/// Registers for the SPU
const SPU: MemRange = MemRange(0x1f801c00, 640);

/// Registers with an unknown purpose, the name comes from the Mednafen PSX implementation
const SYS_CONTROL: MemRange = MemRange(0x1f801000, 36);

/// Timer registers
const TIMERS: MemRange = MemRange(0x1f801100, 0x30);

/// Mask array used to strip the region bits of the address. The mask is selected using the 3 most
/// significant bits of the address so each entry effectively matches 512KB of the address space.
/// KSEG2 is not touched since it doesn't share anything with the other regions.
const REGION_MASK: [u32; 8] = [
    // KUSEG: 2048MB
    0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
    // KSEG0: 512MB
    0x7fffffff,
    // KSEG1: 512MB
    0x1fffffff,
    // KSEG2: 1024MB
    0xffffffff, 0xffffffff
];

/// Mask a CPU address to remove the region bits
pub fn mask_region(addr: u32) -> u32 {
    // Index address space in 512MB chunks
    let index = (addr >> 29) as usize;

    addr & REGION_MASK[index]
}

/// Memory bus for shared memory access
pub struct Bus {
    /// Basic Input/Output System memory
    bios: BIOS,
    /// General purpose working memory
    ram: RAM,
}

impl Bus {
    pub fn new(bios: BIOS, ram: RAM) -> Self {
        Self {
            bios,
            ram
        }
    }

    /// Read a single byte from memory at the specified address
    pub fn mem_read8(&self, addr: u32) -> u8 {
        let abs_addr = mask_region(addr);

        if let Some(offset) = BIOS.contains(abs_addr) {
            return self.bios.mem_read8(offset);
        }

        if let Some(offset) = EXPANSION1.contains(abs_addr) {
            // No expansion implemented
            return 0xff;
        }

        if let Some(offset) = RAM.contains(abs_addr) {
            return self.ram.mem_read8(offset);
        }

        panic!("UNHANDLED_READ8_AT_ADDRESS_0x{:08x}", abs_addr);
    }

    /// Read a 32-bit word from memory at the specified address
    pub fn mem_read32(&self, addr: u32) -> u32 {
        // Unaligned memory access is not allowed
        if addr % 4 != 0 {
            panic!("UNALIGNED_READ32_AT_ADDRESS_0x{:08x}", addr);
        }

        let abs_addr = mask_region(addr);

        // BIOS
        if let Some(offset) = BIOS.contains(abs_addr) {
            return self.bios.mem_read32(offset);
        }

        if let Some(offset) = IRQ_CONTROL.contains(abs_addr) {
            println!("UNHANDLED_IRQ_CONTROL_READ32_0x{:08x}", abs_addr);
            // TODO: Needs to return an actual value from the IRQ Control register
            return 0;
        }

        // RAM
        if let Some(offset) = RAM.contains(abs_addr) {
            return self.ram.mem_read32(offset);
        }

        panic!("UNHANDLED_READ32_AT_ADDRESS_0x{:08x}", abs_addr);
    }

    /// Write a single byte to memory at the specified address
    pub fn mem_write8(&mut self, addr: u32, val: u8) {
        let abs_addr = mask_region(addr);

        if let Some(offset) = EXPANSION2.contains(abs_addr) {
            println!("UNHANDLED_EXPANSION2_REGISTER_WRITE8: 0x{:08x}", abs_addr);
            return;
        }

        if let Some(offset) = RAM.contains(abs_addr) {
            return self.ram.mem_write8(offset, val);
        }

        panic!("UNHANDLED_WRITE8_AT_ADDRESS_0x{:08x}", addr);
    }

    /// Write a 16-bit word to memory at the specified address
    pub fn mem_write16(&mut self, addr: u32, val: u16) {
        // Unaligned memory access is not allowed
        if addr % 2 != 0 {
            panic!("UNALIGNED_WRITE16_AT_ADDRESS_0x{:08x}", addr);
        }

        let abs_addr = mask_region(addr);

        // SPU
        if let Some(offset) = SPU.contains(abs_addr) {
            println!("UNHANDLED_SPU_REGISTER_WRITE16: 0x{:08x}", abs_addr);
            return;
        }

        // TIMERS
        if let Some(offset) = TIMERS.contains(abs_addr) {
            println!("UNHANDLED_TIMER_REGISTER_WRITE16: 0x{:08x}", abs_addr);
            return;
        }

        panic!("UNHANDLED_WRITE16_AT_ADDRESS_0x{:08x}", addr);
    }

    /// Write a 32-bit word to memory at the specified address
    pub fn mem_write32(&mut self, addr: u32, val: u32) {
        // Unaligned memory access is not allowed
        if addr % 4 != 0 {
            panic!("UNALIGNED_WRITE32_AT_ADDRESS_0x{:08x}", addr);
        }

        let abs_addr = mask_region(addr);

        // CACHE_CONTROL register
        if let Some(_) = CACHE_CONTROL.contains(abs_addr) {
            // TODO: We're ignoring this right now, not sure if this should be the case
            return;
        }

        if let Some(offset) = IRQ_CONTROL.contains(abs_addr) {
            println!("IRQ_CONTROL:{:x}<-{:08x}", offset, val);
            // TODO: This is a bit disgusting
            return;
        }

        // Memory Control
        if let Some(offset) = MEM_CONTROL.contains(abs_addr) {
            match offset {
                // Expansion 1 base address
                0 => {
                    if val != 0x1f000000 {
                        panic!("BAD_EXPANSION_1_BASE_ADDRESS: 0x{:08x}", abs_addr);
                    }
                },
                // Expansion 2 base address
                4 => {
                    if val != 0x1f802000 {
                        panic!("BAD_EXPANSION_2_BASE_ADDRESS: 0x{:08x}", abs_addr);
                    }
                },
                _ => {
                    println!("UNHANDLED_MEMCONTROL_REGISTER_WRITE32: 0x{:08x}", abs_addr);
                }
            }
            // TODO: This is a bit disgusting
            return;
        }

        // RAM
        if let Some(offset) = RAM.contains(abs_addr) {
            self.ram.mem_write32(offset, val);
            return;
        }

        // RAM_SIZE register
        if let Some(_) = RAM_SIZE.contains(abs_addr) {
            // TODO: We're ignoring this right now, not sure if this should be the case
            return;
        }

        panic!("UNHANDLED_WRITE32_AT_ADDRESS_0x{:08x}", abs_addr);
    }
}

/// A range in the PSX memory map
struct MemRange(pub u32, pub u32);


impl MemRange {
    /// Return `Some(offset)` if addr is contained within this memory range
    fn contains(self, addr: u32) -> Option<u32> {
        let MemRange(start, length) = self;


        if addr >= start && addr < start + length {
            Some(addr - start)
        } else {
            None
        }
    }
}
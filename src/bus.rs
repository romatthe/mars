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

/// BIOS image region
const BIOS: MemRange = MemRange(0xbfc00000 , 512 * 1024);

/// Cache control register
const CACHE_CONTROL: MemRange = MemRange(0xfffe0130, 4);

/// Memory latency and expansion mapping region
const MEM_CONTROL: MemRange = MemRange(0x1f801000, 36);

/// Register that has something to do with RAM configuration configured by the BIOS
const RAM_SIZE: MemRange = MemRange(0x1f801060, 4);

/// Memory bus for shared memory access
pub struct Bus {
    /// Basic Input/Output System memory
    bios: BIOS,
}

impl Bus {
    pub fn new(bios: BIOS) -> Self {
        Self {
            bios
        }
    }

    pub fn mem_read32(&self, addr: u32) -> u32 {
        // Unaligned memory access is not allowed
        if addr % 4 != 0 {
            panic!("UNALIGNED_READ32_AT_ADDRESS_0x{:08x}", addr);
        }

        // BIOS
        if let Some(offset) = BIOS.contains(addr) {
            return self.bios.mem_read32(offset);
        }

        panic!("UNHANDLED_READ32_AT_ADDRESS_0x{:08x}", addr);
    }

    pub fn mem_write32(&mut self, addr: u32, val: u32) {
        // Unaligned memory access is not allowed
        if addr % 4 != 0 {
            panic!("UNALIGNED_WRITE32_AT_ADDRESS_0x{:08x}", addr);
        }

        // CACHE_CONTROL register
        if let Some(_) = CACHE_CONTROL.contains(addr) {
            // TODO: We're ignoring this right now, not sure if this should be the case
            return;
        }

        // Memory Control
        if let Some(offset) = MEM_CONTROL.contains(addr) {
            match offset {
                // Expansion 1 base address
                0 => {
                    if val != 0x1f000000 {
                        panic!("BAD_EXPANSION_1_BASE_ADDRESS: 0x{:08x}", addr);
                    }
                },
                // Expansion 2 base address
                4 => {
                    if val != 0x1f802000 {
                        panic!("BAD_EXPANSION_2_BASE_ADDRESS: 0x{:08x}", addr);
                    }
                },
                _ => {
                    println!("UNHANDLED_MEMCONTROL_REGISTER_WRITE32: 0x{:08x}", addr);
                }
            }
            // TODO: This is a bit disgusting
            return;
        }

        // RAM_SIZE register
        if let Some(_) = RAM_SIZE.contains(addr) {
            // TODO: We're ignoring this right now, not sure if this should be the case
            return;
        }

        panic!("UNHANDLED_WRITE32_AT_ADDRESS_0x{:08x}", addr);
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
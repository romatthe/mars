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

const BIOS_START: u32 = 0xbfc00000;
const BIOS_END: u32 = BIOS_START + BIOS_SIZE - 1;

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
        match addr {
            BIOS_START..=BIOS_END => self.bios.mem_read32(addr - BIOS_START),
            _ => panic!("UNHANDLED_READ32_AT_ADDRESS_{:08x}", addr),
        }
    }
}
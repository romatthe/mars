use cpu::BIOS;
use crate::bus::Bus;
use crate::cpu::CPU;
use crate::ram::RAM;

mod bus;
mod cpu;
mod ram;

fn main() {
    // Initialize components
    let bios = BIOS::from_file(&"bios/scph1001.bin").unwrap();
    let ram = RAM::new();
    let bus = Bus::new(bios, ram);

    let mut cpu = CPU::new(bus);

    loop {
        cpu.step();
    }
}

use cpu::BIOS;
use crate::bus::Bus;
use crate::cpu::CPU;

mod bus;
mod cpu;

fn main() {
    let bios = BIOS::from_file(&"bios/scph1001.bin").unwrap();
    let bus = Bus::new(bios);
    let mut cpu = CPU::new(bus);

    loop {
        cpu.step();
    }
}

use crate::prelude::*;

pub type Mask = [MaskBit; 36];
pub type Memory = HashMap<u64, u64>;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum MaskBit {
    None,
    Zero,
    One,
}

impl From<u8> for MaskBit {
    fn from(b: u8) -> Self {
        match b {
            b'0' => MaskBit::Zero,
            b'1' => MaskBit::One,
            _ => MaskBit::None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Instr {
    Mask(Mask),
    MemSet(u64, u64),
}

#[derive(Debug)]
pub struct DockingComputer {
    program: Vec<Instr>,
    memory: Memory,
    mask: Mask,
}

impl DockingComputer {
    pub fn new(program: &[Instr]) -> Self {
        Self {
            program: program.to_vec(),
            memory: HashMap::default(),
            mask: [MaskBit::None; 36],
        }
    }

    pub fn execute1(&mut self) {
        self.program.clone().iter().for_each(|&instr| match instr {
            Instr::Mask(mask) => self.mask = mask,
            Instr::MemSet(addr, value) => self.set_value(addr, value),
        })
    }

    pub fn execute2(&mut self) {
        self.program.clone().iter().for_each(|&instr| match instr {
            Instr::Mask(mask) => self.mask = mask,
            Instr::MemSet(addr, value) => self.set_address(addr, value),
        })
    }

    pub fn mem_sum(&self) -> u64 {
        self.memory.values().sum()
    }

    fn set_value(&mut self, addr: u64, value: u64) {
        let value_set = self.mask_value(value);
        let _ = self.memory.insert(addr, value_set);
    }

    fn set_address(&mut self, addr: u64, value: u64) {
        self.mask_address(addr).for_each(|addr| {
            let _ = self.memory.insert(addr, value);
        });
    }

    fn mask_value(&self, mut value: u64) -> u64 {
        self.mask
            .iter()
            .copied()
            .rev()
            .enumerate()
            .for_each(|(pos, bit)| match bit {
                MaskBit::Zero => {
                    let mask = !(1 << pos);
                    value &= mask;
                },
                MaskBit::One => {
                    let mask = 1 << pos;
                    value |= mask;
                },
                _ => (),
            });

        value
    }

    fn mask_address(&self, mut address: u64) -> impl Iterator<Item = u64> {
        let floating_bits = self
            .mask
            .iter()
            .rev()
            .enumerate()
            .filter_map(|(mbi, mb)| {
                match mb {
                    MaskBit::None => return Some(mbi),
                    MaskBit::One => {
                        let mask = 1 << mbi;
                        address |= mask;
                    },
                    _ => (),
                }
                None
            })
            .collect_vec();

        let max = 1_u64 << floating_bits.len();

        (0..max).scan((floating_bits, address), |(positions, addr), floats| {
            let mut new_addr = *addr;

            positions.iter().enumerate().for_each(|(i, &pos)| {
                match (floats >> i) & 1 {
                    0 => {
                        let mask = !(1 << pos);
                        new_addr &= mask;
                    },
                    1 => {
                        let mask = 1 << pos;
                        new_addr |= mask;
                    },
                    _ => unreachable!(),
                }
            });

            Some(new_addr)
        })
    }
}

pub struct Answer;

impl Solver for Answer {
    type Input = Vec<Instr>;
    type Output1 = u64;
    type Output2 = u64;

    fn parse_input<R: Reader>(&self, r: R) -> Self::Input {
        r.lines()
            .map(|line| {
                let line = line.unwrap();
                if line.starts_with("mask") {
                    let mask_string =
                        scan_fmt!(&line, "mask = {}", String).unwrap();
                    let mut mask = [MaskBit::None; 36];
                    let bits = mask_string.bytes().map_into::<MaskBit>();
                    mask.iter_mut().set_from(bits);
                    Instr::Mask(mask)
                } else {
                    let (addr, val) =
                        scan_fmt!(&line, "mem[{d}] = {d}", _, _).unwrap();
                    Instr::MemSet(addr, val)
                }
            })
            .collect_vec()
    }

    /// Correct: `6513443633260`
    fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
        let mut computer = DockingComputer::new(input);
        computer.execute1();
        computer.mem_sum()
    }

    /// Correct: `3442819875191`
    fn solve_second(&self, input: &Self::Input) -> Self::Output2 {
        let mut computer = DockingComputer::new(input);
        computer.execute2();
        computer.mem_sum()
    }
}

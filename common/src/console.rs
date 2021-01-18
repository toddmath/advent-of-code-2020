use scan_fmt::scan_fmt;
use std::{
    collections::{HashSet, VecDeque},
    num::ParseIntError,
    str::FromStr,
};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum Inst {
    Acc(i32),
    Jmp(i32),
    Nop(i32),
}

impl FromStr for Inst {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (inst, n) = scan_fmt!(s, "{} {}", String, i32).unwrap();

        match inst.as_str() {
            "acc" => {
                // let amount = n.parse::<isize>()?;
                Ok(Inst::Acc(n))
            },
            "jmp" => {
                // let amount = n.parse::<isize>()?;
                Ok(Inst::Jmp(n))
            },
            "nop" => Ok(Inst::Nop(n)),
            _ => panic!("Invalid instruction"),
        }
    }
}

#[derive(Debug)]
pub struct Console {
    /// All `Inst`s
    instructions: VecDeque<Inst>,
    /// Current index for list of `Inst`s
    cursor: isize,
    /// Current state
    state: i32,
    program_counter: usize,
    jump: Option<usize>,
}

impl Default for Console {
    fn default() -> Self {
        Self {
            instructions: VecDeque::default(),
            cursor: 0,
            state: 0,
            program_counter: 0,
            jump: None,
        }
    }
}

impl Console {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub fn with_instructions(inst: VecDeque<Inst>) -> Self {
        Self {
            instructions: inst,
            cursor: 0,
            state: 0,
            program_counter: 0,
            jump: None,
        }
    }

    pub fn run_till_loop_or_termination(&mut self) -> bool {
        let mut visited = HashSet::new();
        let program_size = self.instructions.len();

        loop {
            if self.program_counter == program_size {
                return true;
            }

            if self.program_counter > program_size
                || !visited.insert(self.program_counter)
            {
                return false;
            }

            self.step();
        }
    }

    fn step(&mut self) {
        self.exec();
        self.program_counter =
            self.jump.take().unwrap_or(self.program_counter + 1);
    }

    #[allow(
        clippy::cast_sign_loss,
        clippy::cast_possible_truncation,
        clippy::cast_possible_wrap
    )]
    fn exec(&mut self) {
        match self.instructions[self.program_counter] {
            Inst::Acc(n) => self.state += n,
            Inst::Jmp(n) => {
                let new_addr = self.program_counter as i32 + n;
                self.jump.replace(new_addr as usize);
            },
            Inst::Nop(_) => (),
        }
    }

    #[must_use]
    #[inline]
    pub fn state(&self) -> i32 {
        self.state
    }

    #[must_use]
    #[inline]
    pub fn instructions(&self) -> &VecDeque<Inst> {
        &self.instructions
    }

    #[must_use]
    #[inline]
    pub fn cursor(&self) -> isize {
        self.cursor
    }

    #[must_use]
    pub fn jump(&self) -> Option<usize> {
        self.jump
    }
}

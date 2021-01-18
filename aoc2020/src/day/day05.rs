use crate::prelude::*;
use std::{num::ParseIntError, ops::AddAssign};

pub struct Answer;

impl Solver for Answer {
    type Input = Vec<SeatId>;
    type Output1 = SeatId;
    type Output2 = SeatId;

    fn parse_input<R: Reader>(&self, r: R) -> Self::Input {
        parse_to(r)
    }

    /// Correct: `813`
    fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
        input.iter().max().unwrap().to_owned()
    }

    /// Correct: `612`
    fn solve_second(&self, input: &Self::Input) -> Self::Output2 {
        input
            .iter()
            .sorted()
            .tuple_windows()
            .find_map(|(a, b): (&SeatId, &SeatId)| {
                if a.plus_one() != *b {
                    Some(a.plus_one())
                } else {
                    None
                }
            })
            .unwrap()
    }
}

#[derive(
    Debug,
    Ord,
    PartialOrd,
    Eq,
    PartialEq,
    Copy,
    Clone,
    Default,
    Hash,
    num_derive::FromPrimitive,
    num_derive::ToPrimitive,
    num_derive::Zero,
    num_derive::NumCast,
    num_derive::NumOps,
    num_derive::One,
    num_derive::Num,
)]
pub struct SeatId(u32);

impl SeatId {
    fn plus_one(&self) -> Self {
        *self + Self(1)
    }
}

impl FromStr for SeatId {
    type Err = ParseIntError;

    fn from_str(s: &str) -> anyhow::Result<Self, Self::Err> {
        let id = izip!((0..10).rev(), s.chars())
            .map(|(n, c)| {
                let bit = ['B', 'R'].contains(&c) as i32;
                bit << n
            })
            .sum::<i32>() as u32;

        Ok(Self(id))
    }
}

impl AddAssign for SeatId {
    fn add_assign(&mut self, other: Self) {
        *self = *self + other
    }
}

impl Deref for SeatId {
    type Target = u32;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Display for SeatId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Default, Hash)]
struct Ticket {
    row: u8,
    column: u8,
}

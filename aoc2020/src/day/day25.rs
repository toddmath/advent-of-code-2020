use crate::prelude::*;

pub const MODULO: u64 = 20_201_227;

pub struct Answer;

impl Solver for Answer {
    type Input = (u64, u64);
    type Output1 = u64;
    type Output2 = u64;

    fn parse_input<R: Reader>(&self, r: R) -> Self::Input {
        r.lines()
            .map(|r| r.unwrap())
            .map(|line| line.parse().unwrap())
            .collect_tuple()
            .unwrap()
    }

    /// Correct: `18293391`
    fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
        let &(card_pub, door_pub) = input;
        let card_loop_size = trans::<7>().position(|v| v == card_pub).unwrap();
        transforms(door_pub).nth(card_loop_size).unwrap()
    }

    /// This isn't implemented, because it's the end of AOC-2020!
    fn solve_second(&self, _input: &Self::Input) -> Self::Output2 {
        0
    }
}

fn transforms(subject: u64) -> impl Iterator<Item = u64> {
    itertools::iterate(subject, move |curr| curr * subject % MODULO)
}

fn trans<const N: u64>() -> impl Iterator<Item = u64> {
    itertools::iterate(N, move |curr| curr * N % MODULO)
}

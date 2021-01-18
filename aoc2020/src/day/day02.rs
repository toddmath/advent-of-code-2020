use crate::prelude::*;
use std::num::ParseIntError;
// use aoc_runner::{parse_to, Reader, Solver};

pub struct Answer;

#[derive(Debug, Ord, PartialOrd, Eq, PartialEq)]
pub struct Password {
    min: usize,
    max: usize,
    character: char,
    entry: String,
}

impl FromStr for Password {
    type Err = ParseIntError;

    fn from_str(s: &str) -> anyhow::Result<Self, Self::Err> {
        let line = s.split_whitespace().collect_vec();
        let minmax = line[0]
            .split('-')
            .map(|s| s.parse::<usize>().unwrap())
            .collect_vec();
        let character =
            line[1].chars().find(char::is_ascii_alphabetic).unwrap();
        let entry = line[2].to_string();
        Ok(Password {
            min: minmax[0],
            max: minmax[1],
            character,
            entry,
        })
    }
}

impl Solver for Answer {
    type Input = Vec<Password>;
    type Output1 = usize;
    type Output2 = usize;

    fn parse_input<R: Reader>(&self, r: R) -> Self::Input {
        parse_to(r)
    }

    fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
        input
            .iter()
            .filter(|&p| {
                let occurs = p.entry.matches(p.character).count();
                occurs <= p.max && occurs >= p.min
            })
            .count()
    }

    fn solve_second(&self, input: &Self::Input) -> Self::Output2 {
        input
            .iter()
            .filter(|&p| {
                let e = p.entry.chars().collect_vec();
                let min = e[p.min as usize - 1] == p.character;
                let max = e[p.max as usize - 1] == p.character;
                matches!((min, max), (true, false) | (false, true))
            })
            .count()
    }
}

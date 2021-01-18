#![allow(incomplete_features)]
#![feature(
    type_alias_impl_trait,
    int_error_matching,
    bool_to_option,
    inplace_iteration,
    option_insert,
    generic_associated_types,
    iterator_fold_self
)]

use anyhow::{bail, Result};
use aoc_runner::Solver;
use clap::Clap;
use std::path::PathBuf;

mod day;
mod prelude;
use day::*;

fn main() -> Result<()> {
    let app: App = App::parse();
    app.run()?;
    Ok(())
}

/// Advent of code 2020
#[derive(Debug, Clap)]
struct App {
    /// Day to run
    #[clap(short = 'd', long)]
    day: usize,

    /// Optional path to input file. If not supplied, will read from STDIN.
    #[clap(short = 'i', long, parse(from_os_str))]
    input: Option<PathBuf>,
}

impl App {
    fn run(&self) -> Result<()> {
        match self.day {
            1 => day01::Answer.solve(self.day)?,
            2 => day02::Answer.solve(self.day)?,
            3 => day03::Answer.solve(self.day)?,
            4 => day04::Answer.solve(self.day)?,
            5 => day05::Answer.solve(self.day)?,
            6 => day06::Answer.solve(self.day)?,
            7 => day07::Answer.solve(self.day)?,
            8 => day08::Answer.solve(self.day)?,
            9 => day09::Answer.solve(self.day)?,
            10 => day10::Answer.solve(self.day)?,
            11 => day11::Answer.solve(self.day)?,
            12 => day12::Answer.solve(self.day)?,
            13 => day13::Answer.solve(self.day)?,
            14 => day14::Answer.solve(self.day)?,
            15 => day15::Answer.solve(self.day)?,
            16 => day16::Answer.solve(self.day)?,
            17 => day17::Answer.solve(self.day)?,
            18 => day18::Answer.solve(self.day)?,
            19 => day19::Answer.solve(self.day)?,
            20 => day20::Answer.solve(self.day)?,
            21 => day21::Answer.solve(self.day)?,
            22 => day22::Answer.solve(self.day)?,
            23 => day23::Answer.solve(self.day)?,
            24 => day24::Answer.solve(self.day)?,
            25 => day25::Answer.solve(self.day)?,
            _ => bail!("Not yet implemented"),
        };
        Ok(())
    }
}

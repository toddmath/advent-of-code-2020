#![feature(
    auto_traits,
    negative_impls,
    trusted_len,
    drain_filter,
    is_sorted,
    trivial_bounds
)]
#![allow(unused_imports)]
#![deny(clippy::all, clippy::pedantic)]
#![allow(clippy::missing_errors_doc)]

#[macro_use]
extern crate num_derive;

pub mod output;

use anyhow::{bail, Context, Error, Result};
use colored::Colorize;
use itertools::Itertools;
use std::{
    collections,
    fmt::Display,
    fs::{self, File},
    io::{self, prelude::*, BufRead, BufReader, Cursor, Seek},
    num::ParseIntError,
    ops::{Deref, DerefMut},
    path::Path,
    str::FromStr,
    time::{Duration, Instant},
};

fn input_path(day: usize) -> String {
    format!("input/day/{:02}.txt", day)
}

#[allow(dead_code)]
pub fn read_to_vec<R: std::io::Read>(r: R) -> Vec<String> {
    let r = std::io::BufReader::new(r);
    r.lines().filter_map(std::result::Result::ok).collect()
}

pub fn read_to_iter<R, T>(r: R) -> impl Iterator<Item = T>
where
    R: io::Read,
    T: FromStr<Err = ParseIntError>,
{
    let buf = BufReader::new(r);
    buf.lines().map(|l| l.unwrap().parse::<T>().unwrap())
}

pub fn read_chars_to_iter<R, T>(r: R) -> impl Iterator<Item = T>
where
    R: io::Read,
    T: FromStr<Err = ParseIntError>,
{
    let buf = BufReader::new(r);
    buf.lines().flatten().map(|l| l.parse::<T>().unwrap())
}

pub fn read_to_iter_anyhow<R, T>(r: R) -> impl Iterator<Item = T>
where
    R: io::Read,
    T: FromStr<Err = anyhow::Error>,
{
    let buf = BufReader::new(r);
    buf.lines().map(|l| {
        l.unwrap()
            .parse::<T>()
            .with_context(|| "parsing error")
            .unwrap()
    })
}

pub fn parse_to<R: Reader, T: FromStr<Err = ParseIntError>>(r: R) -> Vec<T> {
    read_to_iter(r).collect()
}

pub fn parse_string<R: Reader>(mut r: R) -> String {
    let mut buf = String::new();
    r.read_to_string(&mut buf).unwrap();
    buf
}

pub fn parse_group<R, T>(input: R, _sep: &str) -> Result<Vec<T>>
where
    R: Reader,
    T: FromStr<Err = Error>,
{
    // let buf = BufReader::new(input);
    input
        .lines()
        .map(|x| x.unwrap().parse::<T>().with_context(|| "invalid input"))
        .collect()
}

pub fn parse_list<T>(input: &str, sep: &str) -> Result<Vec<T>>
where
    T: FromStr<Err = Error>,
{
    input
        .trim()
        .split(sep)
        .map(|x| x.parse::<T>().with_context(|| "invalid input"))
        .collect()
}

pub fn parse_into<R, T>(r: R) -> Vec<T>
where
    R: Reader,
    T: FromStr<Err = Error> + From<Vec<u8>>,
{
    // BufReader::new(r)
    r.split(b',').flatten().map_into::<T>().collect_vec()
}

pub fn parse_many<'a, F, I, S>(
    lines: I,
) -> anyhow::Result<Vec<F>, <F as FromStr>::Err>
where
    F: FromStr,
    I: IntoIterator<Item = &'a S>,
    S: AsRef<str> + 'a,
{
    Ok(lines
        .into_iter()
        .map(|s| s.as_ref().parse::<F>())
        .collect::<Result<_, _>>()?)
}

pub fn read_lines<R: Reader>(r: R) -> impl Iterator<Item = String> {
    r.lines().map(Result::unwrap)
}

pub fn read_groups<R: Reader, F: FnMut(&String)>(r: R, mut f: F) {
    // let lines = read_lines(r);
    let mut builder = String::new();

    for line in read_lines(r) {
        if line.is_empty() {
            f(&builder);
            builder.clear();
        } else {
            builder.push(' ');
            builder.push_str(line.as_str());
        }
    }

    f(&builder);
}

// pub type FileReader = BufReader<fs::File>;
pub type FRead = BufReader<fs::File>;

pub struct FileReader<R>
where
    R: Reader,
{
    reader: R,
}

// impl Clone for FileReader<FRead> {
//     fn clone(&self) -> Self {
//         *self
//     }
// }

impl<T> Clone for FileReader<T>
where
    Self: Sized,
    T: Sized + Clone + Reader,
{
    fn clone(&self) -> Self {
        FileReader {
            reader: self.reader.clone(),
        }
    }
}
impl<T> Deref for FileReader<T>
where
    T: Reader,
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.reader
    }
}
impl<T> DerefMut for FileReader<T>
where
    T: Reader,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.reader
    }
}

pub trait Reader: io::Seek + io::Read + io::BufRead {}

impl<T> Reader for T where T: BufRead + Seek + io::Read {}
// impl Reader for BufReader<fs::File> {}
// impl Reader for BufReader<fs::File> where Self: Clone {}

pub fn file_reader<P: AsRef<Path>>(path: P) -> Result<FileReader<FRead>> {
    let file = File::open(path)?;
    let meta = file.metadata()?;

    if meta.is_dir() {
        bail!("Is a directory");
    }

    let returned_reader = BufReader::new(file);

    Ok(FileReader {
        reader: returned_reader,
    })
}

pub trait Solver {
    type Input;
    type Output1: Display;
    type Output2: Display;

    fn parse_input<R: Reader>(&self, r: R) -> Self::Input;
    fn solve_first(&self, input: &Self::Input) -> Self::Output1;
    fn solve_second(&self, input: &Self::Input) -> Self::Output2;

    fn load_input<P: AsRef<Path>>(&self, p: P) -> Result<Self::Input> {
        // let f = File::open(p)?;
        let mut f = file_reader(p)?;
        Ok(self.parse_input(f.deref_mut()))
    }

    fn solve(&self, day: usize) -> Result<()> {
        let input_file = input_path(day);
        let input = self
            .load_input(input_file)
            .with_context(|| "unable to open input file")?;

        let run_timed = |part: &i32| {
            let now = Instant::now();
            let s = match part {
                1 => format!(
                    "\n{}: {}",
                    "Part 1".red().bold(),
                    format!("{}", self.solve_first(&input)).red().bold()
                ),
                2 => format!(
                    "{}: {}",
                    "Part 2".green().bold(),
                    format!("{}", self.solve_second(&input)).green().bold()
                ),
                _ => unreachable!(),
            };
            (s, now.elapsed())
        };

        output::print_header();
        output::print_day(day);

        [1, 2].iter().for_each(|p| {
            let (s, t) = run_timed(p);
            println!("{}", s);
            self.print_time(t);
            println!();
        });

        Ok(())
    }

    fn print_time(&self, d: Duration) {
        println!(
            "- {}.{}{}{:03} {}",
            format!("{:03}", d.as_secs()).bright_red(),
            format!("{:03}", d.subsec_millis()).red(),
            format!("{:03}", d.subsec_micros() % 1_000).yellow(),
            format!("{}", d.subsec_nanos() % 1_000).green(),
            "seconds".bold(),
        );
    }
}

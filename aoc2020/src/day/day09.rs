use crate::prelude::*;
use std::{cmp::Ordering, iter};

pub struct Answer;

fn is_valid_window(window: &[u64]) -> bool {
    let (preamble, validated) = match window {
        [preamble @ .., v] => (preamble, v),
        _ => unreachable!(),
    };
    let mut remainders = HashSet::default();

    preamble.iter().any(|&v| {
        if remainders.contains(&v) {
            return true;
        }
        !remainders.insert(validated - v)
    })
}

fn find_contiguous_sum(partials: &[u64], sum: u64) -> Option<(usize, usize)> {
    let (mut l, mut r) = (0, 2);
    let size = partials.len();

    while r < size && l < r {
        let (a, b) = (partials[l], partials[r]);
        let slice_sum = b - a;

        match slice_sum.cmp(&sum) {
            Ordering::Equal => return Some((l, r)),
            Ordering::Greater => l += 1,
            Ordering::Less => r += 1,
        }
    }

    None
}

fn xmas(input: &[u64]) -> u64 {
    input
        .windows(26)
        .find_map(|w| {
            if !is_valid_window(w) {
                w.last().copied()
            } else {
                None
            }
        })
        .unwrap()
}

impl Solver for Answer {
    type Input = Vec<u64>;
    type Output1 = u64;
    type Output2 = u64;

    fn parse_input<R: Reader>(&self, r: R) -> Self::Input {
        parse_to(r)
    }

    /// Correct: `177777905`
    fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
        xmas(input)
    }

    /// Correct: `23463012`
    fn solve_second(&self, input: &Self::Input) -> Self::Output2 {
        let searched = xmas(input);

        let partial_sums = itertools::chain(iter::once(&0), input)
            .scan(0, |acc, v| {
                *acc += v;
                Some(*acc)
            })
            .collect_vec();

        let (index_low, index_high) =
            find_contiguous_sum(&partial_sums, searched).unwrap();

        let (min, max) = input[index_low..index_high]
            .iter()
            .minmax()
            .into_option()
            .unwrap();

        min + max
    }
}

use crate::prelude::*;

pub struct Answer;

impl Solver for Answer {
    type Input = Vec<u64>;
    type Output1 = u64;
    type Output2 = i64;

    fn parse_input<R: Reader>(&self, r: R) -> Self::Input {
        parse_to(r)
    }

    fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
        let mut remainders = HashSet::<u64>::default();
        let second = input
            .iter()
            .find(|&entry| {
                if remainders.contains(&entry) {
                    true
                } else {
                    let other = 2020 - *entry;
                    !remainders.insert(other)
                }
            })
            .unwrap();

        let first = 2020 - *second;

        first * second
    }

    fn solve_second(&self, input: &Self::Input) -> Self::Output2 {
        let input = input.iter().map(|&n| n as i64).collect_vec();
        let (first, second, third) = input
            .iter()
            .find_map(|&first| find_occurences(first, &input))
            .unwrap();

        first * second * third
    }
}

fn find_occurences(first: i64, input: &[i64]) -> Option<(i64, i64, i64)> {
    let mut remainders = HashSet::default();
    let remaining_sum = 2020 - first;

    input
        .iter()
        .filter(|&el| *el != first)
        .find(|&record| {
            if remainders.contains(record) {
                true
            } else {
                let other = remaining_sum - *record;
                !remainders.insert(other)
            }
        })
        .map(|&n| (first, remaining_sum - n, n))
}

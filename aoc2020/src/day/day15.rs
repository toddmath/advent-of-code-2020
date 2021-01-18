use crate::prelude::*;

const START: [usize; 7] = [12_usize, 20, 0, 6, 1, 17, 7];
const TARGET_SIZE_1: usize = 2020;
const TARGET_SIZE_2: usize = 30_000_000;

fn get_num<const N: usize>(start_seq: &[usize]) -> usize {
    let mut last_seen = vec![usize::MAX; N];
    for (index, &value) in start_seq[..(start_seq.len() - 1)].iter().enumerate()
    {
        last_seen[value] = index;
    }
    let mut last_number = *start_seq.last().unwrap();

    (start_seq.len() - 1..N - 1).for_each(|i| {
        let last_index = last_seen[last_number];
        last_seen[last_number] = i;

        if last_index != usize::MAX {
            last_number = i - last_index;
        } else {
            last_number = 0;
        }
    });
    last_number
}

pub struct Answer;

impl Solver for Answer {
    type Input = Vec<usize>;
    type Output1 = usize;
    type Output2 = usize;

    fn parse_input<R: Reader>(&self, _r: R) -> Self::Input {
        START.iter().copied().collect()
    }

    /// Correct: `866`
    fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
        get_num::<TARGET_SIZE_1>(input)
    }

    /// Correct: `1437692`
    fn solve_second(&self, input: &Self::Input) -> Self::Output2 {
        get_num::<TARGET_SIZE_2>(input)
    }
}

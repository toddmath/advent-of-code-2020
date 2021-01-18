use crate::prelude::*;

pub struct Answer;

impl Solver for Answer {
    type Input = Vec<u64>;
    type Output1 = u64;
    type Output2 = usize;

    fn parse_input<R: Reader>(&self, r: R) -> Self::Input {
        parse_to(r)
    }

    /// Correct: `1625`
    fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
        let mut nums = input.clone();
        nums.sort_unstable();

        let (mut x, mut y) = (0, 0);
        [0].iter().chain(&nums).tuple_windows().for_each(|(a, b)| {
            match b - a {
                1 => x += 1,
                3 => y += 1,
                _ => {},
            }
        });

        x * (y + 1)
    }

    /// Correct: `3100448333024`
    fn solve_second(&self, input: &Self::Input) -> Self::Output2 {
        let mut nums = input.clone();
        nums.sort_unstable();
        let mut k = VecDeque::with_capacity(4);
        [1usize, 0, 0, 0].iter().for_each(|&n| k.push_back(n));

        for (a, b) in [0].iter().chain(&nums).tuple_windows() {
            (0..b - a).for_each(|_| {
                k.pop_back();
                k.push_front(0);
            });
            k[0] += k.iter().sum::<usize>();
        }

        k[0]
    }
}

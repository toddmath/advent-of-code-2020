use crate::prelude::*;
use std::iter;

#[allow(clippy::many_single_char_names)]
fn step<const N: u32>(arr: &mut [u32], x: u32) -> Option<u32> {
    let a = arr[x as usize];
    let b = arr[a as usize];
    let c = arr[b as usize];
    let y = arr[c as usize];

    let not_abc = |n: &u32| ![a, b, c].contains(&n);
    let t =
        iter::successors(Some(x), |t| Some(t.checked_sub(1).unwrap_or(N - 1)))
            .skip(1)
            .find(not_abc)?;

    let u = *arr.get(t as usize)?;
    arr[x as usize] = y;
    arr[t as usize] = a;
    arr[c as usize] = u;
    Some(y)
}

fn play_cups(initial: &[u32]) -> Option<u32> {
    let mut arr = [0; 9];

    for (i, x) in initial.iter().enumerate() {
        arr[x.checked_sub(1)? as usize] =
            *initial.get(i + 1).or_else(|| initial.first())? - 1;
    }

    let mut x = initial[0] - 1;
    for _ in 0..100 {
        x = step::<9>(&mut arr, x)?;
    }

    Some(
        iter::successors(arr.get(0), |&&x| arr.get(x as usize))
            .take_while(|&&x| x != 0)
            .fold(0, |acc, x| 10 * acc + x + 1),
    )
}

fn play_cups_2(nums: &[u32]) -> Option<u64> {
    let mut arr: Vec<u32> = Vec::with_capacity(1000000);
    arr.extend(1..=1000000);

    for (i, x) in nums.iter().enumerate() {
        arr[x.checked_sub(1)? as usize] = *nums.get(i + 1).unwrap_or(&10) - 1;
    }

    let mut x = nums[0] - 1;
    *arr.last_mut()? = x;

    for _ in 0..10000000 {
        x = step::<1000000>(&mut arr[..], x)?;
    }

    Some((arr[0] as u64 + 1) * (arr[arr[0] as usize] as u64 + 1))
}

pub struct Answer;

impl Solver for Answer {
    type Input = Vec<u32>;
    type Output1 = u32;
    type Output2 = u64;

    fn parse_input<R: Reader>(&self, _r: R) -> Self::Input {
        vec![3_u32, 6, 4, 2, 9, 7, 5, 8, 1]
    }

    /// Correct: `47382659`
    fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
        play_cups(input).unwrap()
    }

    /// Correct: `42271866720`
    fn solve_second(&self, input: &Self::Input) -> Self::Output2 {
        play_cups_2(input).unwrap()
    }
}

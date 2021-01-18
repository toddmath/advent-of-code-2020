use crate::prelude::*;
use common::console::{Console, Inst};

pub struct Answer;
pub type Instructions = VecDeque<Inst>;

impl Solver for Answer {
    type Input = Instructions;
    type Output1 = i32;
    type Output2 = i32;

    fn parse_input<R: Reader>(&self, r: R) -> Self::Input {
        read_to_iter(r).collect()
    }

    /// Correct: `1816`
    fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
        let mut console = Console::with_instructions(input.to_owned());
        let _ = console.run_till_loop_or_termination();
        console.state()
    }

    /// Correct: `1149`
    fn solve_second(&self, input: &Self::Input) -> Self::Output2 {
        input
            .iter()
            .enumerate()
            .filter(|&(_, &inst)| matches!(inst, Inst::Jmp(_) | Inst::Nop(_)))
            .find_map(|(i, &inst)| {
                let mut copy = input.clone();
                copy[i] = match inst {
                    Inst::Jmp(n) => Inst::Nop(n),
                    Inst::Nop(n) => Inst::Jmp(n),
                    _ => unreachable!(),
                };
                let mut console = Console::with_instructions(copy);
                if console.run_till_loop_or_termination() {
                    Some(console.state())
                } else {
                    None
                }
            })
            .unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn part_one() {
        let input = r"nop +0
acc +1
jmp +4
acc +3
jmp -3
acc -99
acc +1
jmp -4
acc +6";
        let instructions =
            read_to_iter(input.as_bytes()).collect::<VecDeque<Inst>>();
        assert_eq!(Answer.solve_first(&instructions), 5);
    }
}

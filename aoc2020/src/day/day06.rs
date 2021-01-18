use crate::prelude::*;

pub struct Answer;

impl Solver for Answer {
    type Input = Vec<Group>;
    type Output1 = usize;
    type Output2 = usize;

    fn parse_input<R: Reader>(&self, r: R) -> Self::Input {
        let s = parse_string(r);
        s.split("\n\n")
            .map(|lines| {
                Group::from_iter(lines.split('\n').map(|l| l.chars().collect()))
            })
            .collect_vec()
    }

    /// Correct: `6683`
    fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
        input.par_iter().map(|g| g.count_union()).sum()
    }

    /// Correct: `3122`
    fn solve_second(&self, input: &Self::Input) -> Self::Output2 {
        input.par_iter().map(|g| g.count_intersection()).sum()
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub struct Group {
    people: Vec<HashSet<char>>,
}

impl Group {
    fn from_iter<I>(people: I) -> Self
    where
        I: Iterator<Item = HashSet<char>>,
    {
        Self {
            people: people.collect_vec(),
        }
    }

    fn count_union(&self) -> usize {
        self.people
            .par_iter()
            .flatten()
            .collect::<HashSet<&char>>()
            .len()
    }

    fn count_intersection(&self) -> usize {
        self.people
            .iter()
            .fold(self.people.first().unwrap().to_owned(), |acc, person| {
                acc.intersection(person).copied().collect()
            })
            .len()
    }
}

use crate::prelude::*;

pub type Rules = HashMap<usize, Vec<Rule>>;
type Message = SmallVec<[u8; 32]>;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Satellite {
    rules: Rules,
    messages: Vec<Message>,
    /* messages: Vec<BV>,
     * messages: Vec<Vec<u8>>, */
}

impl Satellite {
    fn check_matches(&self, message: &Message) -> bool {
        let size = message.len();
        let mut stack: Vec<(usize, Vec<usize>)> = vec![(0, vec![0])];

        while let Some((index, mut current)) = stack.pop() {
            let id = current.pop().unwrap();
            let alternatives = &self.rules[&id];

            for rule in alternatives {
                match rule {
                    Rule::Compound(ids) => {
                        let mut cl = current.clone();
                        let elems = ids.iter().copied().rev();
                        cl.extend(elems);
                        stack.push((index, cl));
                    },
                    Rule::Symbol(byte) => {
                        if byte != &message[index] {
                            break;
                        }
                        let new_index = index + 1;
                        match (new_index == size, current.is_empty()) {
                            (true, true) => return true,
                            (false, false) => {
                                stack.push((new_index, current.clone()))
                            },
                            _ => break,
                        }
                    },
                }
            }
        }
        false
    }

    fn count_all_matches(&self) -> usize {
        self.messages
            .par_iter()
            .filter(|&m| self.check_matches(m))
            .count()
    }

    pub fn insert_rule(
        &mut self,
        index: usize,
        rule: &[Rule],
    ) -> Option<Vec<Rule>> {
        self.rules.insert(index, rule.to_vec())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Rule {
    Compound(Vec<usize>),
    Symbol(u8),
}

impl Rule {
    fn new_comp(compounds: &[usize]) -> Self {
        Self::Compound(compounds.to_vec())
    }
}

pub struct Answer;

impl Solver for Answer {
    type Input = Satellite;
    type Output1 = usize;
    type Output2 = usize;

    fn parse_input<R: Reader>(&self, r: R) -> Self::Input {
        let mut satellite = Satellite::default();
        let input = parse_string(r);
        let sections = input.split("\n\n");

        for (section_i, section) in sections.enumerate() {
            if section_i == 0 {
                satellite.rules = section
                    .trim()
                    .lines()
                    .map(|line| {
                        let (id, rule_str) = scan_fmt!(
                            line,
                            "{d}: {[ \"|0-9a-z]}",
                            usize,
                            String
                        )
                        .unwrap();
                        (
                            id,
                            rule_str
                                .split(" | ")
                                .map(|a| {
                                    if a.starts_with('"') {
                                        Rule::Symbol(a.as_bytes()[1])
                                    } else {
                                        Rule::Compound(
                                            a.split_whitespace()
                                                .map(|n| n.parse().unwrap())
                                                .collect_vec(),
                                        )
                                    }
                                })
                                .collect_vec(),
                        )
                    })
                    .collect();
            } else {
                satellite.messages = section
                    .trim()
                    .lines()
                    .map(|l| SmallVec::from_slice(l.as_bytes()))
                    .collect_vec();
            }
        }

        satellite
    }

    /// Correct: `285`
    fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
        input.count_all_matches()
    }

    /// Correct: `412`
    fn solve_second(&self, input: &Self::Input) -> Self::Output2 {
        let mut satellite = input.clone();
        let _ = satellite
            .insert_rule(8, &[Rule::new_comp(&[42]), Rule::new_comp(&[42, 8])]);
        let _ = satellite.insert_rule(
            11,
            &[Rule::new_comp(&[42, 31]), Rule::new_comp(&[42, 11, 31])],
        );
        satellite.count_all_matches()
    }
}

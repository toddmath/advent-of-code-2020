use crate::prelude::*;
use std::ops::RangeInclusive;

pub type Rule = (String, Vec<RangeInclusive<u64>>);
pub type Rules = Vec<Rule>;
pub type Ticket = Vec<u64>;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Translation {
    rules: Rules,
    tickets: Vec<Ticket>,
    my_ticket: Ticket,
}

impl Translation {
    fn push_rule(&mut self, rule: Rule) {
        self.rules.push(rule);
    }

    fn push_ticket(&mut self, ticket: Ticket) {
        self.tickets.push(ticket);
    }

    fn push_my_ticket(&mut self, my_ticket: Ticket) {
        self.my_ticket.reserve(my_ticket.len());
        self.my_ticket.extend(my_ticket);
    }

    fn invalid_ticket_numbers(&self, ticket: &[u64]) -> Ticket {
        ticket
            .par_iter()
            .filter(|&val| {
                self.rules
                    .par_iter()
                    .find_any(|(_name, ranges)| {
                        ranges.iter().any(|range| range.contains(val))
                    })
                    .is_none()
            })
            .copied()
            .collect()
    }

    fn ticket_scanning_error_rate(&self) -> u64 {
        self.tickets
            .par_iter()
            .flat_map(|ticket| self.invalid_ticket_numbers(ticket))
            .sum()
    }

    fn departure_code(&self) -> u64 {
        let valid_tickets = self
            .tickets
            .par_iter()
            .filter(|ticket| self.invalid_ticket_numbers(ticket).is_empty())
            .collect::<Vec<_>>();

        let mut label_candidates = (0..self.rules.len())
            .into_par_iter()
            .map(|i| {
                (
                    i,
                    self.rules
                        .par_iter()
                        .filter(|(_name, ranges)| {
                            valid_tickets
                                .iter()
                                .find(|&&ticket| {
                                    !ranges
                                        .par_iter()
                                        .any(|range| range.contains(&ticket[i]))
                                })
                                .is_none()
                        })
                        .map(|(name, _rules)| name.to_string())
                        .collect::<Vec<String>>(),
                )
            })
            .collect::<Vec<_>>();

        let mut ordered_labels = vec![String::new(); self.rules.len()];

        while !label_candidates.is_empty() {
            let (i, candidate) = label_candidates
                .iter_mut()
                .find(|(_i, c)| c.len() == 1)
                .unwrap()
                .clone();

            let label = candidate[0].clone();
            ordered_labels[i] = label.clone();

            label_candidates.retain(|(j, _c)| i != *j);
            label_candidates
                .iter_mut()
                .for_each(|(_i, c)| c.retain(|e| *e != label))
        }

        ordered_labels
            .par_iter()
            .enumerate()
            .filter_map(|(i, name)| {
                if name.starts_with("departure") {
                    Some(self.my_ticket[i])
                } else {
                    None
                }
            })
            .product()
    }
}

pub struct Answer;

impl Solver for Answer {
    type Input = Translation;
    type Output1 = u64;
    type Output2 = u64;

    fn parse_input<R: Reader>(&self, r: R) -> Self::Input {
        let mut translation = Translation::default();
        let get_range = |s: &str| scan_fmt!(&s, "{}-{}", u64, u64).unwrap();

        r.lines().enumerate().for_each(|(line_idx, line)| {
            let line = line.unwrap();
            if line_idx < 20 {
                let mut parts = line.split(": ");
                let rule_name = parts.next().unwrap().to_string();
                let ranges = parts.next().unwrap().split(" or ");
                let rule = ranges
                    .map(get_range)
                    .map(|(lo, hi)| RangeInclusive::new(lo, hi))
                    .collect_vec();
                translation.push_rule((rule_name, rule));
            } else if line_idx == 22 {
                translation.push_my_ticket(
                    line.split(',').map(|s| s.parse().unwrap()).collect_vec(),
                );
            } else if line_idx >= 25 {
                translation.push_ticket(
                    line.split(',').map(|s| s.parse().unwrap()).collect_vec(),
                );
            }
        });

        translation
    }

    /// Correct: `20975`
    fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
        input.ticket_scanning_error_rate()
    }

    /// Correct: `910339449193`
    fn solve_second(&self, input: &Self::Input) -> Self::Output2 {
        input.departure_code()
    }
}

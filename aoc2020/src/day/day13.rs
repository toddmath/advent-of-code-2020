use crate::prelude::*;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Bus {
    offset: i64,
    id: i64,
}

impl Bus {
    const fn new(offset: i64, id: i64) -> Self {
        Self { offset, id }
    }

    fn modular_inverse_id(&self, num: i64) -> Option<i64> {
        (0..self.id).into_par_iter().find_map_any(|i| {
            if (i * num) % self.id == 1 {
                Some(i)
            } else {
                None
            }
        })
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TimeTable {
    departure: i64,
    buses: Vec<Bus>,
}

pub struct Answer;

impl Solver for Answer {
    type Input = TimeTable;
    type Output1 = i64;
    type Output2 = i64;

    fn parse_input<R: Reader>(&self, r: R) -> Self::Input {
        let mut departure: i64 = 0;
        let mut buses = vec![];

        for (line_i, line) in r.lines().map(|re| re.unwrap()).enumerate() {
            match line_i {
                0 => departure = line.parse().unwrap(),
                1 => {
                    buses.extend(
                        line.split(',')
                            .enumerate()
                            .filter(|(_i, c)| *c != "x")
                            .map(|(i, id)| {
                                Bus::new(i as i64, id.parse().unwrap())
                            })
                            .collect_vec(),
                    );
                },
                _ => {},
            }
        }

        TimeTable { departure, buses }
    }

    /// Correct: `2406`
    fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
        let (id, dep) = input
            .buses
            .par_iter()
            .map(|bus| {
                let rem = input.departure % bus.id;
                if rem == 0 {
                    (bus.id, rem)
                } else {
                    (bus.id, bus.id - rem)
                }
            })
            .min_by_key(|&(_, time)| time)
            .unwrap();

        id * dep
    }

    /// Correct: `225850756401039`
    fn solve_second(&self, input: &Self::Input) -> Self::Output2 {
        let mut constraints = input.buses.to_owned();
        constraints.sort_by_key(|t| t.id);
        constraints.reverse();
        let big_n = constraints.par_iter().map(|bus| bus.id).product::<i64>();

        constraints
            .par_iter()
            .map(|bus| {
                let yi = big_n / bus.id;
                debug_assert_eq!(yi * bus.id, big_n);
                let zi = bus.modular_inverse_id(yi).unwrap();

                (bus.id - bus.offset) * yi * zi
            })
            .sum::<i64>()
            % big_n
    }
}

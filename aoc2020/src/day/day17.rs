use crate::prelude::*;
use std::ops::RangeInclusive;
use tuple::T4;

type Cube = T4<i32, i32, i32, i32>;
type Grid = HashMap<Cube, bool>;
type Range = RangeInclusive<i32>;

trait GridExt {
    fn get_cube(&self, val: &Cube) -> bool;
}

impl GridExt for Grid {
    fn get_cube(&self, val: &Cube) -> bool {
        self.get(val).copied().unwrap_or_default()
    }
}

fn get_ranges(cube: Cube) -> Option<(Range, Range, Range, Range)> {
    let T4(x, y, z, w) = cube;
    [x, y, z, w]
        .iter()
        .map(|n| RangeInclusive::new(n - 1, n + 1))
        .collect_tuple()
}

fn neighbors(cube: Cube, four_d: bool) -> impl Iterator<Item = Cube> {
    let (rx, ry, rz, mut rw) = get_ranges(cube).unwrap();
    let not_cube = predicate::ne(cube);
    if !four_d {
        rw = 0..=0;
    }
    iproduct!(rx, ry, rz, rw)
        .filter(move |&pos| not_cube.eval(&pos.into()))
        .map(|(a, b, c, d)| T4::<i32, i32, i32, i32>(a, b, c, d))
}

fn tick(current: &Grid, four_d: bool) -> Grid {
    let mut inactive_neighbors = HashSet::<Cube>::default();
    let mut next = Grid::default();

    current.iter().for_each(|(&pos, &state)| {
        let mut n_active = 0;
        let is_conway = predicate::function(|n: &i32| !(2..=3).contains(n));

        neighbors(pos, four_d).for_each(|neighbor| {
            // if current.get(&neighbor).copied().unwrap_or_default() {
            if current.get_cube(&neighbor) {
                n_active += 1;
            } else if state {
                let _ = inactive_neighbors.insert(neighbor);
            }
        });

        let new_state = match (state, n_active) {
            (true, n) if is_conway.eval(&n) => false,
            (false, 3) => true,
            (state, _) => state,
        };

        next.insert(pos, new_state);
    });

    inactive_neighbors
        .iter()
        .map(|&n| {
            (
                n,
                neighbors(n, four_d)
                    .filter(|pos| current.get_cube(pos))
                    .count()
                    == 3,
            )
        })
        .for_each(|(k, v)| {
            next.insert(k, v);
        });

    next
}

fn run_tick<const N: usize>(init: &Grid, four_d: bool) -> Grid {
    (0..N).fold(init.clone(), |current, _| tick(&current, four_d))
}

pub struct Answer;

impl Solver for Answer {
    type Input = Grid;
    type Output1 = usize;
    type Output2 = usize;

    fn parse_input<R: Reader>(&self, r: R) -> Self::Input {
        let rows = r.lines().map(|r| r.unwrap()).collect_vec();
        let row_len = rows[0].len() as i32;

        rows.iter()
            .flat_map(|s| s.chars())
            .enumerate()
            .filter_map(|(i, c)| {
                if c == '#' {
                    Some((
                        T4(i as i32 % row_len, i as i32 / row_len, 0, 0),
                        true,
                    ))
                } else {
                    None
                }
            })
            .collect()
    }

    /// Correct: `215`
    fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
        let booted = run_tick::<6>(input, false);
        booted.values().par_bridge().filter(|&&state| state).count()
    }

    /// Correct: `1728`
    fn solve_second(&self, input: &Self::Input) -> Self::Output2 {
        let booted = run_tick::<6>(input, true);
        booted.values().par_bridge().filter(|&&state| state).count()
    }
}

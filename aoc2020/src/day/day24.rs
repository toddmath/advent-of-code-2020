use crate::prelude::*;
use hex2d::{Coordinate, Direction};

pub struct Answer;

pub type Coord = Coordinate<i32>;
pub type Floor = HashMap<Coord, bool>;
// pub type Floor = std::collections::HashMap<Coord, bool>;

impl Solver for Answer {
    type Input = Vec<String>;
    type Output1 = usize;
    type Output2 = usize;

    fn parse_input<R: Reader>(&self, r: R) -> Self::Input {
        r.lines().map(|r| r.unwrap()).collect_vec()
    }

    /// Correct: `332`
    fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
        let floor = prepare_floor(input);
        floor.values().filter(|color| **color).count()
    }

    /// Correct: `3900`
    fn solve_second(&self, input: &Self::Input) -> Self::Output2 {
        let init = prepare_floor(input);
        let after_exhibit = run_exhibit(init, 100);
        after_exhibit.values().filter(|&&color| color).count()
    }
}

fn next_iter(current: &Floor) -> Floor {
    let mut white_neighbors = HashSet::<Coordinate>::default();
    let mut next = Floor::default();

    for (&pos, &state) in current {
        let mut n_black = 0;
        for &neighbor in &pos.neighbors() {
            if current.get(&neighbor).copied().unwrap_or_default() {
                n_black += 1;
            } else if state {
                white_neighbors.insert(neighbor);
            }
        }

        let new_state = match (state, n_black) {
            (true, n) if n == 0 || n > 2 => false,
            (false, 2) => true,
            (state, _) => state,
        };

        if new_state {
            next.insert(pos, new_state);
        }
    }

    for n in white_neighbors {
        let n_black = n
            .neighbors()
            .iter()
            .filter(|pos| current.get(pos).copied().unwrap_or_default())
            .count();

        let new_state = n_black == 2;
        if new_state {
            next.insert(n, new_state);
        }
    }

    next
}

fn run_exhibit(init: Floor, n: usize) -> Floor {
    (0..n).fold(init, |curr, _| next_iter(&curr))
}

fn prepare_floor(inst: &[String]) -> Floor {
    let mut floor = Floor::default();

    inst.iter().for_each(|line| {
        let color = floor
            .entry(
                tile_line(&line).fold(Coord::new(0, 0), |acc, dir| acc + dir),
            )
            .or_default();
        *color = !*color;
    });

    // for line in inst {
    //     // let mut current_tile = Coord::new(0, 0);
    //     // let current_tile =
    //     // tile_line(&line).fold(Coord::new(0, 0), |acc, dir| acc + dir);
    //     // for dir in tile_line(&line) {
    //     //     current_tile = current_tile + dir;
    //     // }

    //     let color = floor
    //         .entry(
    //             tile_line(&line).fold(Coord::new(0, 0), |acc, dir| acc +
    // dir),         )
    //         .or_default();
    //     *color = !*color;
    // }

    floor
}

fn tile_line(desc: &str) -> impl Iterator<Item = Direction> + '_ {
    let bytes = desc.as_bytes();
    itertools::unfold(0, move |pos| {
        let current_pos = *pos;
        match bytes[current_pos..] {
            [b'e', ..] => {
                *pos += 1;
                Some(Direction::XY)
            },
            [b'w', ..] => {
                *pos += 1;
                Some(Direction::YX)
            },
            [b's', b'e', ..] => {
                *pos += 2;
                Some(Direction::ZY)
            },
            [b's', b'w', ..] => {
                *pos += 2;
                Some(Direction::ZX)
            },
            [b'n', b'e', ..] => {
                *pos += 2;
                Some(Direction::XZ)
            },
            [b'n', b'w', ..] => {
                *pos += 2;
                Some(Direction::YZ)
            },
            [] => None,
            _ => unreachable!(),
        }
    })
}

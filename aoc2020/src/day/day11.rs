use crate::prelude::*;
use std::ops::RangeInclusive;
use tuple::{A2, T2};

pub type Grid = HashMap<T2<i32, i32>, bool>;

pub struct Answer;

impl Solver for Answer {
    type Input = Grid;
    type Output1 = usize;
    type Output2 = usize;

    fn parse_input<R: Reader>(&self, r: R) -> Self::Input {
        let lines = read_to_vec(r);
        let row_size = lines[0].len();

        lines
            .iter()
            .flat_map(|s| s.chars())
            .enumerate()
            .filter_map(|(i, c)| {
                let (x, y) = (i % row_size, i / row_size);
                if c == 'L' {
                    Some((T2(x as i32, y as i32), false))
                } else {
                    None
                }
            })
            .collect()
    }

    /// Correct: `2222`
    fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
        let stabilized = stabilize_traffic(input);
        count_occupied(&stabilized)
    }

    /// Correct: `2032`
    fn solve_second(&self, input: &Self::Input) -> Self::Output2 {
        let (width, height) = (91_i32, 94_i32);
        let stabilized = stabilize_traffic2(input, width, height);
        count_occupied(&stabilized)
    }
}

const DIRECTIONS: [A2<i32>; 8] = [
    T2(0, 1),
    T2(0, -1),
    T2(1, 0),
    T2(-1, 0),
    T2(-1, -1),
    T2(1, 1),
    T2(-1, 1),
    T2(1, -1),
];

fn count_occupied(grid: &Grid) -> usize {
    grid.values()
        .par_bridge()
        .filter(|&&occupied| occupied)
        .count()
}

fn scan_visible(grid: &Grid, xy: A2<i32>, w: i32, h: i32) -> usize {
    let T2(x, y) = xy;
    let in_range = |&(x, y): &(i32, i32)| x >= 0 && y >= 0 && x < w && y < h;
    DIRECTIONS
        .par_iter()
        .map(|T2::<i32, i32>(hor, ver)| {
            let start = (x + hor, y + ver);
            itertools::iterate(start, |(x, y)| (x + hor, y + ver))
                .take_while(in_range)
                .find_map(|pos| grid.get(&pos.into()).copied())
                .filter(|&occupied| occupied)
                .is_some() as usize
        })
        .sum()
}

fn next_iteration2(current: &Grid, w: i32, h: i32) -> Grid {
    current
        .par_iter()
        .map(|(&seat_pos, &occupied)| {
            let occupied_visible = scan_visible(current, seat_pos, w, h);
            let new_state = match (occupied, occupied_visible) {
                (false, 0) => true,
                (true, n) if n >= 5 => false,
                (state, _) => state,
            };
            (seat_pos, new_state)
        })
        .collect()
}

fn stabilize_traffic2(initial: &Grid, w: i32, h: i32) -> Grid {
    let mut current = initial.clone();
    loop {
        let next = next_iteration2(&current, w, h);
        if next == current {
            return next;
        }
        current = next;
    }
}

#[inline]
fn neighbor_ranges(
    x: i32,
    y: i32,
) -> (RangeInclusive<i32>, RangeInclusive<i32>) {
    let ((ax, bx), (ay, by)) = ((x - 1, x + 1), (y - 1, y + 1));
    (ax..=bx, ay..=by)
}

#[inline]
fn neighbors((x, y): (i32, i32)) -> impl Iterator<Item = (i32, i32)> {
    let (range_x, range_y) = neighbor_ranges(x, y);
    iproduct!(range_x, range_y).filter(move |&pos| pos != (x, y))
}

fn occupied_neighbors(current: &Grid, seat_pos: (i32, i32)) -> usize {
    neighbors(seat_pos)
        .map(|pos| current.get(&pos.into()).copied().unwrap_or_default())
        .filter(|&occ| occ)
        .count()
}

fn next_iteration(current: &Grid) -> Grid {
    current
        .par_iter()
        .map(|(&seat_pos, &occupied)| {
            let occupied_neighbors =
                occupied_neighbors(current, seat_pos.into());
            let new_state = match (occupied, occupied_neighbors) {
                (false, 0) => true,
                (true, n) if n >= 4 => false,
                (state, _) => state,
            };
            (seat_pos, new_state)
        })
        .collect()
}

fn stabilize_traffic(initial: &Grid) -> Grid {
    let mut current = initial.clone();
    loop {
        let next = next_iteration(&current);
        if next == current {
            return next;
        }
        current = next;
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn seat_location() {
//         let input =
// r#"#.##.##.##
// #######.##
// #.#.#..#..
// ####.##.##
// #.##.##.##
// #.#####.##
// ..#.#.....
// ##########
// #.######.#
// #.#####.##"#;

//     }
// }

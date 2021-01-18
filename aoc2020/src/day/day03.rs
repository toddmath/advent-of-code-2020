use crate::prelude::*;

pub struct Answer;

impl Solver for Answer {
    type Input = Vec<Vec<bool>>;
    type Output1 = usize;
    type Output2 = usize;

    fn parse_input<R: Reader>(&self, r: R) -> Self::Input {
        r.lines()
            .map_ok(|line| line.chars().map(|c| c == '#').collect())
            .map(|l| l.unwrap())
            .collect_vec()
    }

    /// Correct: `203`
    fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
        let land = LandMap::from_slice(input);
        land.count_slope_trees(3, 1)
    }

    /// Correct: `3316272960`
    fn solve_second(&self, input: &Self::Input) -> Self::Output2 {
        let land = LandMap::from_slice(input);
        [(1, 1), (3, 1), (5, 1), (7, 1), (1, 2)]
            .iter()
            .map(|&(w, h)| land.count_slope_trees(w, h))
            .product()
    }
}

struct LandMap {
    map: Vec<Vec<bool>>,
}

impl LandMap {
    fn from_slice(map: &[Vec<bool>]) -> Self {
        Self { map: map.into() }
    }

    fn count_slope_trees(&self, w: usize, h: usize) -> usize {
        let vert_dist = self.map.len();
        let horiz_dist = self.map[0].len();

        Self::get_slope(w, h)
            .take_while(|&(_, y)| y < vert_dist)
            .filter(|&(x, y)| {
                let row = &self.map[y];
                let mapped_x = x % horiz_dist;
                row[mapped_x]
            })
            .count()
    }

    fn get_slope(w: usize, h: usize) -> impl Iterator<Item = (usize, usize)> {
        itertools::iterate((0, 0), move |&(x, y)| (x + w, y + h))
    }
}

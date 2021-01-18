use crate::prelude::*;
use std::num::ParseIntError;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Action {
    North(i32),
    South(i32),
    East(i32),
    West(i32),
    Left(i32),
    Right(i32),
    Forward(i32),
}

impl FromStr for Action {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (dir, amt) = s.split_at(1);
        let amount = amt.parse::<i32>().unwrap();
        Ok(match dir {
            "N" => Self::North(amount),
            "S" => Self::South(amount),
            "E" => Self::East(amount),
            "W" => Self::West(amount),
            "L" => Self::Left(amount),
            "R" => Self::Right(amount),
            "F" => Self::Forward(amount),
            _ => panic!("Invalid str"),
        })
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Navigation {
    x: i32,
    y: i32,
    /// 0 => N, 1 => E, 2 => S, 3 => W
    direction: i32,
    waypoint_x: i32,
    waypoint_y: i32,
}

impl Navigation {
    pub const fn new() -> Self {
        Self {
            x: 0,
            y: 0,
            direction: 1,
            waypoint_x: 10,
            waypoint_y: 1,
        }
    }

    pub const fn manhattan(&self) -> i32 {
        self.x.abs() + self.y.abs()
    }

    pub fn tick(&mut self, action: Action) {
        match action {
            Action::North(n) => self.y += n,
            Action::South(n) => self.y -= n,
            Action::East(n) => self.x += n,
            Action::West(n) => self.x -= n,
            Action::Left(n) => {
                self.direction = i32::rem_euclid(self.direction - (n / 90), 4);
            },
            Action::Right(n) => {
                self.direction = i32::rem_euclid(self.direction + (n / 90), 4);
            },
            Action::Forward(n) => self.move_forward(n),
        }
    }

    pub fn tick2(&mut self, action: Action) {
        match action {
            Action::North(n) => self.waypoint_y += n,
            Action::South(n) => self.waypoint_y -= n,
            Action::East(n) => self.waypoint_x += n,
            Action::West(n) => self.waypoint_x -= n,
            Action::Left(n) => {
                self.rotate_waypoint(i32::rem_euclid(-(n / 90), 4));
            },
            Action::Right(n) => {
                self.rotate_waypoint(i32::rem_euclid(n / 90, 4));
            },
            Action::Forward(n) => self.move_forward2(n),
        }
    }

    fn execute(&mut self, actions: &[Action]) {
        actions.iter().for_each(|&action| self.tick(action));
    }

    fn execute2(&mut self, actions: &[Action]) {
        actions.iter().for_each(|&action| self.tick2(action));
    }

    fn move_forward(&mut self, n: i32) {
        match self.direction {
            0 => self.y += n,
            1 => self.x += n,
            2 => self.y -= n,
            3 => self.x -= n,
            _ => unreachable!(),
        }
    }

    fn move_forward2(&mut self, n: i32) {
        self.x += n * self.waypoint_x;
        self.y += n * self.waypoint_y;
    }

    fn rotate_waypoint(&mut self, n: i32) {
        match n {
            0 => (),
            1 => {
                let tmp = self.waypoint_x;
                self.waypoint_x = self.waypoint_y;
                self.waypoint_y = -tmp;
            },
            2 => {
                self.waypoint_x = -self.waypoint_x;
                self.waypoint_y = -self.waypoint_y;
            },
            3 => {
                let tmp = self.waypoint_x;
                self.waypoint_x = -self.waypoint_y;
                self.waypoint_y = tmp;
            },
            _ => unreachable!(),
        }
    }
}

pub struct Answer;

impl Solver for Answer {
    type Input = Vec<Action>;
    type Output1 = i32;
    type Output2 = i32;

    fn parse_input<R: Reader>(&self, r: R) -> Self::Input {
        read_to_iter(r).collect_vec()
    }

    /// Correct: `1956`
    fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
        let mut navigation = Navigation::new();
        navigation.execute(input);
        navigation.manhattan()
    }

    /// Correct: `126797`
    fn solve_second(&self, input: &Self::Input) -> Self::Output2 {
        let mut navigation = Navigation::new();
        navigation.execute2(input);
        navigation.manhattan()
    }
}

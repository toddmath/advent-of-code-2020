use crate::prelude::*;
use scan_fmt::scan_fmt;

type MaybeFields = HashSet<String>;
type MaybePassport = Vec<(String, String)>;

pub struct Answer;

impl Solver for Answer {
    type Input = String;
    type Output1 = usize;
    type Output2 = usize;

    fn parse_input<R: Reader>(&self, mut r: R) -> Self::Input {
        let mut whole = String::new();
        r.read_to_string(&mut whole).unwrap();
        whole
    }

    /// Correct: `237`
    fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
        input
            .split("\n\n")
            .map(|p| {
                p.split_whitespace()
                    .map(|kv| scan_fmt!(kv, "{}:{*}", String).unwrap())
                    .collect()
            })
            .filter(validate_first)
            .count()
    }

    /// Correct: `172`
    fn solve_second(&self, input: &Self::Input) -> Self::Output2 {
        input
            .split("\n\n")
            .map(|p| {
                p.split_whitespace()
                    .map(|kv| scan_fmt!(kv, "{}:{}", _, _).unwrap())
                    .collect()
            })
            .filter(validate_second)
            .count()
    }
}

trait Validate<T>: Sized {
    #[allow(clippy::wrong_self_convention)]
    fn to_option(self) -> Option<T>;

    fn validate<F>(self, pred: F) -> bool
    where
        F: FnOnce(&T) -> bool,
    {
        self.to_option().filter(pred).is_some()
    }
}

impl<T, E> Validate<T> for Result<T, E> {
    fn to_option(self) -> Option<T> {
        self.ok()
    }
}

fn validate_year_range(val: &str, min: i32, max: i32) -> bool {
    val.parse::<i32>().validate(|&n| n >= min && n <= max)
}

#[allow(clippy::ptr_arg)]
fn validate_second(validated: &MaybePassport) -> bool {
    validated
        .iter()
        .filter(|&(key, val)| match key.as_str() {
            "byr" => validate_year_range(val, 1920, 2002),
            "iyr" => validate_year_range(val, 2010, 2020),
            "eyr" => validate_year_range(val, 2020, 2030),
            "hgt" => {
                scan_fmt!(val, "{d}{}", i32, String).validate(|(v, unit)| {
                    match unit.as_str() {
                        "cm" => *v >= 150 && *v <= 193,
                        "in" => *v >= 59 && *v <= 76,
                        _ => false,
                    }
                })
            },
            "hcl" => scan_fmt!(val, "#{[0-9a-f]}", String)
                .validate(|color| color.len() == 6),
            "ecl" => ["amb", "blu", "brn", "gry", "grn", "hzl", "oth"]
                .contains(&val.as_str()),
            "pid" => {
                scan_fmt!(val, "{[0-9]}", String).validate(|id| id.len() == 9)
            },
            _ => false,
        })
        .count()
        == 7
}

fn validate_first(validated: &MaybeFields) -> bool {
    let pass_fields = ["byr", "iyr", "eyr", "hgt", "hcl", "ecl", "pid"]
        .iter()
        .map(|s| s.to_string())
        .collect::<HashSet<_>>();

    pass_fields
        .difference(validated)
        .exactly_one()
        .map(|f| f == "cid")
        .unwrap_or_else(|mut rest| rest.next().is_none())
}

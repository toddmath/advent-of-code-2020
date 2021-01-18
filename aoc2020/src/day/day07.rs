use crate::prelude::*;

type Bags = HashMap<String, Vec<(i32, String)>>;
const GOAL: &str = "shiny gold";

pub struct Answer;

impl Solver for Answer {
    type Input = Bags;
    type Output1 = usize;
    type Output2 = i32;

    fn parse_input<R: Reader>(&self, r: R) -> Self::Input {
        r.lines()
            .map(|r| r.unwrap())
            .map(|l| {
                let mut it = l.split("bags contain");
                let bag_container = it.next().unwrap().trim();
                let rest = it.next().unwrap().trim();
                let items = rest
                    .split(',')
                    .filter_map(|x| {
                        if x.starts_with("no other") {
                            return None;
                        };
                        let x = x.trim();
                        let space_index = x.find(' ').unwrap();
                        let nr = x[0..space_index].parse::<i32>().unwrap();
                        let bag = &x[(space_index + 1)..]
                            .split(" bag")
                            .next()
                            .unwrap();
                        Some((nr, bag.to_string()))
                    })
                    .collect_vec();
                (bag_container.to_string(), items)
            })
            .collect()
    }

    /// Correct: `126`
    fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
        input
            .par_iter()
            .filter(|(_, inside)| {
                inside.iter().any(|(_, bag)| search_gold(input, bag))
            })
            .count()
    }

    /// Correct: `220149`
    fn solve_second(&self, input: &Self::Input) -> Self::Output2 {
        count_bags(input, GOAL) - 1
    }
}

fn count_bags(m: &Bags, bag: &str) -> i32 {
    m[bag].iter().fold(0, |acc, (nr, bag_inside)| {
        acc + nr * count_bags(m, bag_inside)
    }) + 1
}

fn search_gold(m: &Bags, s: &str) -> bool {
    if s == GOAL {
        return true;
    }
    if let Some(inside) = m.get(s) {
        if inside.iter().map(|(_i, s)| s).any(|s| search_gold(m, s)) {
            return true;
        }
    }
    false
}

// lazy_static! {
//     static ref LINE_RE: Regex =
//         Regex::new(r"(\w+ \w+) bags contain (.*)").unwrap();
//     static ref ITEM_RE: Regex = Regex::new(r"(\d+) (\w+ \w+)
// bags?").unwrap(); }

// const GOAL: &str = "shiny gold";

// type Bags = HashMap<String, Vec<(usize, String)>>;

// impl Solver for Answer {
//     type Input = Bags;
//     type Output1 = usize;
//     type Output2 = usize;

//     fn parse_input<R: io::Seek + io::Read + BufRead>(
//         &self,
//         r: R,
//     ) -> Self::Input {
//         let mut bags: Bags = HashMap::default();
//         let lines = read_to_vec(r);

//         lines.into_iter().for_each(|line| {
//             if let Some((item, items)) =
//                 LINE_RE.captures(line.as_ref()).map(|captures| {
//                     (
//                         captures.get(1).unwrap().as_str(),
//                         captures.get(2).unwrap().as_str(),
//                     )
//                 })
//             {
//                 bags.insert(
//                     item.to_string(),
//                     ITEM_RE
//                         .captures_iter(items)
//                         .map(|captures| {
//                             (
//                                 captures
//                                     .get(1)
//                                     .unwrap()
//                                     .as_str()
//                                     .parse()
//                                     .ok()
//                                     .unwrap(),
//
// captures.get(2).unwrap().as_str().to_string(),                             )
//                         })
//                         .collect(),
//                 );
//             }
//         });

//         bags
//     }

//     /// Correct: `126`
//     fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
//         let mut golds = HashMap::default();
//         let mut stack = vec![];

//         input
//             .keys()
//             .filter(|key| {
//                 golds.get(*key).copied().unwrap_or_else(|| {
//                     stack.push((*key, 0));
//                     'stack: loop {
//                         match stack.pop() {
//                             Some((key, i)) => {
//                                 for (j, (_, item)) in
//                                     input[key][i..].iter().enumerate()
//                                 {
//                                     if item == GOAL {
//                                         golds.insert(key, true);
//                                         continue 'stack;
//                                     }
//                                     match golds.get(item) {
//                                         None => {
//                                             stack.push((key, i + j));
//                                             stack.push((item, 0));
//                                             continue 'stack;
//                                         },
//                                         Some(true) => {
//                                             golds.insert(key, true);
//                                             continue 'stack;
//                                         },
//                                         Some(false) => {},
//                                     }
//                                 }
//                                 golds.insert(key, false);
//                             },
//                             None => break golds[*key],
//                         }
//                     }
//                 })
//             })
//             .count()
//     }

//     /// Correct: `220149`
//     fn solve_second(&self, input: &Self::Input) -> Self::Output2 {
//         let mut sum = 0;
//         let mut queue = input.get(GOAL).map_or_else(VecDeque::new, |items| {
//             items
//                 .iter()
//                 .map(|(count, item)| (*count, item.as_str()))
//                 .collect()
//         });

//         while let Some((count, item)) = queue.pop_front() {
//             sum += count;
//             if let Some(items) = input.get(item) {
//                 items.iter().for_each(|(subcount, subitem)| {
//                     queue.push_back((count * subcount, subitem))
//                 });
//             }
//         }

//         sum
//     }
// }

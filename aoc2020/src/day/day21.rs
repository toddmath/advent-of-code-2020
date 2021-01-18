use crate::prelude::*;

pub type Foods = Vec<(HashSet<String>, HashSet<String>)>;

pub struct Answer;

impl Solver for Answer {
    type Input = Foods;
    type Output1 = usize;
    type Output2 = String;

    fn parse_input<R: Reader>(&self, r: R) -> Self::Input {
        r.lines()
            .map(|l| l.unwrap())
            .map(|line| {
                let (ings, algs) = line
                    .strip_suffix(')')
                    .unwrap()
                    .split(" (contains ")
                    .collect_tuple::<(&str, &str)>()
                    .unwrap();
                (
                    ings.split_whitespace().map_into().collect(),
                    algs.split(", ").map_into().collect(),
                )
            })
            .collect_vec()
    }

    /// Correct: `1815`
    fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
        let foods = input.clone();

        let allergens = foods.iter().fold(
            HashSet::<&String>::default(),
            |mut acc, (_, algs)| {
                acc.extend(algs);
                acc
            },
        );

        let carriers = allergens
            .par_iter()
            .flat_map(|alg| {
                foods
                    .iter()
                    .filter_map(|(ings, algs)| {
                        Some(ings).filter(|_| algs.contains(*alg))
                    })
                    .fold(HashSet::<String>::default(), |acc, ings| {
                        if acc.is_empty() {
                            ings.clone()
                        } else {
                            &acc & ings
                        }
                    })
            })
            .collect::<HashSet<String>>();

        foods
            .par_iter()
            .flat_map(|(ingredients, _)| ingredients)
            .filter(|ing| !carriers.contains(*ing))
            .count()
    }

    /// Correct: `kllgt,jrnqx,ljvx,zxstb,gnbxs,mhtc,hfdxb,hbfnkq`
    fn solve_second(&self, input: &Self::Input) -> Self::Output2 {
        let foods = input.clone();

        let allergens = foods.iter().fold(
            HashSet::<&String>::default(),
            |mut acc, (_, algs)| {
                acc.extend(algs);
                acc
            },
        );

        let mut matches =
            HashMap::<&String, HashSet<String>>::with_capacity_and_hasher(
                allergens.len(),
                Default::default(),
            );
        // matches.reserve(allergens.len());

        allergens.iter().for_each(|&alg| {
            let possible_carriers = foods
                .iter()
                .filter_map(|(ings, algs)| {
                    Some(ings).filter(|_| algs.contains(alg))
                })
                .fold(HashSet::<String>::default(), |acc, ings| {
                    if acc.is_empty() {
                        ings.clone()
                    } else {
                        &acc & ings
                    }
                });

            matches.insert(alg, possible_carriers);
        });

        let mut mappings = Vec::with_capacity(matches.len());

        while !matches.is_empty() {
            let matching_allergen = *matches
                .iter()
                .find_map(|(alg, ings)| Some(alg).filter(|_| ings.len() == 1))
                .unwrap();

            let matching_ingredient = matches
                .remove(matching_allergen)
                .and_then(|ings| ings.into_iter().next())
                .unwrap();

            matches.values_mut().for_each(|ings| {
                ings.remove(&matching_ingredient);
            });

            mappings.push((matching_allergen, matching_ingredient));
        }

        mappings.sort_unstable_by(|&(alg_a, _), &(alg_b, _)| alg_a.cmp(alg_b));
        mappings.into_iter().map(|(_, ing)| ing).join(",")
    }
}

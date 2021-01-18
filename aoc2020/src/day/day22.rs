use crate::prelude::*;
use std::cmp::Ordering;

pub struct Answer;

pub type Deck = VecDeque<usize>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Winner {
    One,
    Two,
}

#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Cards {
    player1: Deck,
    player2: Deck,
}

impl Cards {
    const fn new(player1: Deck, player2: Deck) -> Self {
        Self { player1, player2 }
    }

    fn play(&mut self) {
        loop {
            if self.player1.is_empty() || self.player2.is_empty() {
                break;
            }
            let (c1, c2) = self.top_cards().unwrap();
            self.round(c1, c2);
        }
    }

    #[inline]
    fn round(&mut self, card1: usize, card2: usize) {
        match card1.cmp(&card2) {
            Ordering::Greater => {
                self.player1.push_back(card1);
                self.player1.push_back(card2);
            },
            Ordering::Less => {
                self.player2.push_back(card2);
                self.player2.push_back(card1);
            },
            Ordering::Equal => {
                self.player1.push_back(card1);
                self.player2.push_back(card2);
            },
        }
    }

    #[inline]
    fn score_deck(&self, deck: &Deck) -> usize {
        izip!((1..=deck.len()).rev(), deck)
            .map(|(rank, &val)| rank * val)
            .sum()
    }

    #[inline]
    fn score(&self) -> Option<usize> {
        match (self.player1.len(), self.player2.len()) {
            (n, 0) if n > 0 => Some(self.score_deck(&self.player1)),
            (0, n) if n > 0 => Some(self.score_deck(&self.player2)),
            (_, _) => None,
        }
    }

    #[inline]
    fn top_cards(&mut self) -> Option<(usize, usize)> {
        match (self.player1.pop_front(), self.player2.pop_front()) {
            (Some(c1), Some(c2)) => Some((c1, c2)),
            (_, _) => None,
        }
    }
}

#[allow(clippy::type_complexity)]
fn play_combat(player1: Deck, player2: Deck) -> usize {
    let mut games: Vec<(
        (Deck, Deck),
        Option<(usize, usize)>,
        HashSet<(Deck, Deck)>,
    )> = vec![((player1, player2), None, HashSet::default())];
    let mut last_winner = None;

    loop {
        let (players, prev_draw, prev_rounds) = games.last_mut().unwrap();

        match prev_draw.take() {
            // play another standard round
            None => {
                if prev_rounds.contains(players) {
                    last_winner.replace(Winner::One);
                    games.pop();
                    continue;
                }

                prev_rounds.insert(players.clone());

                let (player1, player2) = players;

                let current_draw = (
                    player1.pop_front().unwrap(),
                    player2.pop_front().unwrap(),
                );
                match current_draw {
                    (one, two)
                        if player1.len() >= one && player2.len() >= two =>
                    {
                        let p1_copy =
                            player1.iter().copied().take(one).collect();
                        let p2_copy =
                            player2.iter().copied().take(two).collect();

                        prev_draw.replace(current_draw);

                        games.push((
                            (p1_copy, p2_copy),
                            None,
                            HashSet::default(),
                        ));
                        continue;
                    }
                    (one, two) if one > two => {
                        player1.push_back(one);
                        player1.push_back(two);
                    },
                    (one, two) => {
                        player2.push_back(two);
                        player2.push_back(one);
                    },
                }
            },
            // resolve round via sub-game result
            Some((one, two)) => {
                let (player1, player2) = players;

                match last_winner.take().unwrap() {
                    Winner::One => {
                        player1.push_back(one);
                        player1.push_back(two);
                    },
                    Winner::Two => {
                        player2.push_back(two);
                        player2.push_back(one);
                    },
                }
            },
        }

        let player1_empty = players.0.is_empty();
        let player2_empty = players.1.is_empty();

        if !player1_empty && !player2_empty {
            continue;
        }

        let winner = if !player1_empty {
            &players.0
        } else {
            &players.1
        };

        let score = izip!((1..=winner.len()).rev(), winner)
            .map(|(pos, &val)| pos * val)
            .sum();

        // finally, a global-game victory
        if games.len() == 1 {
            return score;
        }

        // mark this sub-game's winner
        if !player1_empty {
            last_winner.replace(Winner::One);
        } else {
            last_winner.replace(Winner::Two);
        }

        games.pop();
    }
}

impl Solver for Answer {
    type Input = Cards;
    type Output1 = usize;
    type Output2 = usize;

    fn parse_input<R: Reader>(&self, r: R) -> Self::Input {
        let s = parse_string(r);
        let mut sections = s.split("\n\n");
        let player1 = parse_player(&mut sections);
        let player2 = parse_player(&mut sections);
        Cards::new(player1, player2)
    }

    /// Correct: `32413`
    fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
        let mut cards = input.clone();
        cards.play();
        cards.score().unwrap()
    }

    /// Correct: `31596`
    fn solve_second(&self, input: &Self::Input) -> Self::Output2 {
        play_combat(input.player1.clone(), input.player2.clone())
    }
}

fn parse_player(sections: &mut std::str::Split<&str>) -> Deck {
    sections
        .next()
        .unwrap()
        .lines()
        .filter_map(|l| {
            if !l.starts_with("Player") {
                Some(l.parse::<usize>().unwrap())
            } else {
                None
            }
        })
        .collect()
}

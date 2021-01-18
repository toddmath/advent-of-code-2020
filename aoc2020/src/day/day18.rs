use crate::prelude::*;

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Op {
    Add,
    Mul,
    Val(u64),
}

#[derive(Debug, Clone, Copy)]
pub enum Token {
    Op(char),
    LeftParen,
}

impl TryFrom<Token> for Op {
    type Error = &'static str;

    fn try_from(token: Token) -> Result<Self, Self::Error> {
        match token {
            Token::Op('+') => Ok(Op::Add),
            Token::Op('*') => Ok(Op::Mul),
            _ => Err("Invalid token"),
        }
    }
}

impl Token {
    fn into_op(self) -> Op {
        self.try_into().unwrap()
    }

    fn is_gt(&self, other: &Self) -> bool {
        matches!((self, other), (Token::Op('+'), Token::Op('*')))
    }
}

fn parse_infix(s: &str, second: bool) -> Vec<Op> {
    let s_len = s.len();
    let mut result = Vec::with_capacity(s_len);
    let mut ops = Vec::with_capacity(s_len);

    for atom in s.split_whitespace().flat_map(str::chars) {
        match atom {
            op @ '+' | op @ '*' => {
                let opped = Token::Op(op);
                while let Some(t @ Token::Op(_)) = ops.last() {
                    if second && opped.is_gt(t) {
                        break;
                    }
                    result.push(t.into_op());
                    ops.pop();
                }
                ops.push(opped);
            },
            '(' => ops.push(Token::LeftParen),
            ')' => {
                while let Some(t @ Token::Op(_)) = ops.pop() {
                    result.push(t.try_into().unwrap());
                }
            },
            n => {
                let v = n.to_digit(10).unwrap();
                result.push(Op::Val(v as u64));
            },
        }
    }

    let rest = ops.into_iter().rev().map(Token::into_op);
    result.extend(rest);
    result
}

fn eval(rpn: &'_ [Op]) -> u64 {
    let mut partials = Vec::with_capacity(rpn.len());
    rpn.iter().for_each(|&el| match el {
        Op::Val(n) => partials.push(n),
        Op::Add => {
            let (a, b) = (partials.pop().unwrap(), partials.pop().unwrap());
            partials.push(a + b);
        },
        Op::Mul => {
            let (a, b) = (partials.pop().unwrap(), partials.pop().unwrap());
            partials.push(a * b);
        },
    });
    partials.pop().unwrap()
}

pub struct Answer;

impl Solver for Answer {
    type Input = Vec<String>;
    type Output1 = u64;
    type Output2 = u64;

    fn parse_input<R: Reader>(&self, r: R) -> Self::Input {
        r.lines().map(|r| r.unwrap()).collect_vec()
    }

    /// Correct: `14208061823964`
    fn solve_first(&self, input: &Self::Input) -> Self::Output1 {
        input
            .par_iter()
            .map(|expr| eval(&parse_infix(expr, false)))
            .sum()
    }

    /// Correct: `320536571743074`
    fn solve_second(&self, input: &Self::Input) -> Self::Output2 {
        input
            .par_iter()
            .map(|expr| eval(&parse_infix(expr, true)))
            .sum()
    }
}

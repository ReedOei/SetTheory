#![feature(int_log)]
#![feature(box_patterns)]

#![allow(clippy::redundant_field_names)]
#![allow(clippy::needless_return)]

#[macro_use]
extern crate educe;
extern crate pest;
#[macro_use]
extern crate pest_derive;

use num_bigint::{BigInt, ToBigUint};
use num_traits::{Zero, One, Pow};
use pest::Parser;
use pest::iterators::Pair;
use pest::prec_climber::{Assoc, Operator, PrecClimber};

use std::cell::RefCell;
use std::collections::{HashSet, HashMap, VecDeque};
use std::cmp::{max, Ordering};
use std::env;
use std::fs;
use std::fmt;
use std::fmt::Debug;
use std::hash::Hash;
use std::iter::Iterator;
use std::time::{SystemTime, UNIX_EPOCH};
use std::rc::Rc;

static mut fresh_counter : usize = 0;

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct LangParser;

pub fn to_usize(n : &BigInt) -> Result<usize, String> {
    match ToBigUint::to_biguint(n) {
        Some(m) => Ok(m.iter_u64_digits()
            .map(|d| d as usize)
            .fold(0, |accum, d| accum * (std::u64::MAX as usize) + d)),
        None => Err(format!("Could not convert {:?} to usize", n.clone()))
    }
}

pub trait Sequence {
    fn nth(&mut self, n : usize) -> Result<AST, String>;
    fn increasing(&self) -> bool;
    fn index_of(&mut self, v : AST) -> Option<usize>;
}

pub struct PrimeSeq {
    max : usize,
    primes : Vec<BigInt>,
    primes_set : HashSet<BigInt>,
    sieve : Vec<bool>
}

impl PrimeSeq {
    fn new() -> PrimeSeq {
        return PrimeSeq {
            max: 3,
            primes: vec!(BigInt::from(2)),
            primes_set : vec!(BigInt::from(2)).into_iter().collect(),
            sieve : vec!(false, false, true)
        };
    }

    fn run_sieve(&mut self, increment : usize) {
        let mut i = 0;
        while i < increment {
            self.sieve.push(true);
            i += 1;
        }

        println!("Running sieve to {}", increment + self.max);

        let mut p = 0;
        while p < self.sieve.len() {
            if self.sieve[p] {
                let start = max(p*p, p * (self.max / p + 1));

                let mut i = start;
                while i < self.sieve.len() {
                    self.sieve[i] = false;
                    i += p;
                }

                if p >= self.max {
                    self.primes.push(BigInt::from(p));
                    self.primes_set.insert(BigInt::from(p));
                }
            }
            p += 1;
        }

        self.max += increment;
    }

    fn at(&mut self, n : usize) -> BigInt {
        if n >= self.primes.len() {
            // See: https://en.wikipedia.org/wiki/Prime_number_theorem#Approximations_for_the_nth_prime_number
            // This guarantees we will find the nth prime in this round of the sieve
            let new_max = if n < 2 { // If n = 1, then loglog(n) is undefined, choose 100 because why not
                100
            } else {
                // We use log2 here because it will overshoot even more than we need, and there's
                // no built-in ln anyway.
                n*(n.log2() + n.log2().log2())
            };

            self.run_sieve(new_max - self.max);
        }

        return self.primes[n].clone();
    }
}

struct PrimeIt {
    n : usize,
    seq : PrimeSeq
}

fn primes() -> PrimeIt {
    return PrimeIt { n : 0, seq : PrimeSeq::new() };
}

impl Iterator for PrimeIt {
    type Item = BigInt;
    fn next(&mut self) -> Option<Self::Item> {
        let idx = self.n;
        let p = self.seq.at(idx);
        self.n += 1;
        return Some(p);
    }
}

struct Factors {
    n : BigInt,
    m : usize,
    ps : PrimeSeq
}

fn factor(n : BigInt) -> Factors {
    return Factors { n: n, m: 0, ps: PrimeSeq::new() };
}

impl Iterator for Factors {
    type Item = BigInt;
    fn next(&mut self) -> Option<Self::Item> {
        if self.n <= One::one() {
            return None;
        }

        loop {
            let p = self.ps.at(self.m);
            if self.n.clone() % p.clone() == Zero::zero() {
                self.m = 0;
                self.n /= p.clone();
                return Some(p);
            }
            self.m += 1;
        }
    }
}

impl Sequence for PrimeSeq {
    fn nth(&mut self, n : usize) -> Result<AST, String> {
        return Ok(AST::Int(self.at(n)));
    }

    fn increasing(&self) -> bool {
        return true;
    }

    fn index_of(&mut self, v : AST) -> Option<usize> {
        let n = as_int(v).ok()?;

        // The list of primes is never empty.
        if n > self.primes.last().unwrap().clone() {
            self.run_sieve(to_usize(&n).ok()? - self.max);
        }

        let mut min_idx = 0;
        let mut max_idx = self.primes.len() - 1;

        while max_idx - min_idx > 1 {
            let guess = (min_idx + max_idx) / 2;
            match self.primes[guess].cmp(&n) {
                Ordering::Less => min_idx = guess,
                Ordering::Greater => max_idx = guess,
                Ordering::Equal => return Some(guess)
            }
        }

        return None;
    }
}

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum Op {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Exp,
    Concat,
    Lt,
    Le,
    Gt,
    Ge,
    Equals,
    NotEquals,
    Elem,
    Or,
    And,
    Imp,
    Prove
}

#[derive(Clone, Educe)]
#[educe(Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum AST {
    Skip(),

    Definition(String, Box<AST>),
    Rule(Vec<String>, Box<AST>, Box<AST>),
    Assumption(Box<AST>),
    Prove(Box<AST>),

    Int(BigInt),

    Var(String),

    Seq(String,
        #[educe(Debug(ignore))]
        #[educe(Hash(ignore))]
        #[educe(Eq(ignore))]
        #[educe(PartialEq(ignore))]
        #[educe(Ord(ignore))]
        #[educe(PartialOrd(ignore))]
        Rc<RefCell<dyn Sequence>>),

    FinSet(Vec<AST>),
    List(Vec<AST>),
    RangeSet(Box<AST>, Box<AST>, Box<AST>),
    Image(Box<AST>, Box<AST>),
    CompSet(Vec<(String, AST)>, Vec<AST>),

    Bin(Op, Box<AST>, Box<AST>),

    App(Box<AST>, Vec<AST>),
    Function(Option<String>, Vec<String>, Box<AST>),
    Memo(Option<String>,
         Vec<String>,
         Box<AST>,
         #[educe(Debug(ignore))]
         #[educe(Hash(ignore))]
         #[educe(Eq(ignore))]
         #[educe(PartialEq(ignore))]
         #[educe(Ord(ignore))]
         #[educe(PartialOrd(ignore))]
         Rc<RefCell<HashMap<Vec<AST>, Result<AST, String>>>>
    ),

    IfThenElse(Box<AST>, Box<AST>, Box<AST>),

    Sum(Box<AST>),

    Factorial(Box<AST>),
    Negate(Box<AST>),
    Complement(Box<AST>)
}

impl fmt::Display for AST {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AST::Skip() => write!(f, "skip"),
            AST::Int(n) => write!(f, "{}", n),
            AST::Var(x) => write!(f, "{}", x),
            AST::Definition(name, body) => write!(f, "Let {} := {}", name, body),
            AST::Rule(attrs, lhs, rhs) => write!(f, "Rule {} => {} {:?}", lhs, rhs, attrs),
            AST::Assumption(t) => write!(f, "Assume {}", t),
            AST::Prove(t) => write!(f, "Prove {}", t),
            AST::Seq(name, _) => write!(f, "Seq({})", name),
            AST::FinSet(elems) => {
                let mut s = String::new();
                s.push_str("{");
                if elems.len() > 0 {
                    for e in &elems[..elems.len() - 1] {
                        s.push_str(format!("{}, ", e).as_str());
                    }
                    s.push_str(format!("{}", elems[elems.len() - 1]).as_str());
                }
                s.push_str("}");
                write!(f, "{}", s)
            }
            AST::List(elems) => {
                let mut s = String::new();
                s.push_str("[");
                if elems.len() > 0 {
                    for e in &elems[..elems.len() - 1] {
                        s.push_str(format!("{}, ", e).as_str());
                    }
                    s.push_str(format!("{}", elems[elems.len() - 1]).as_str());
                }
                s.push_str("]");
                write!(f, "{}", s)
            }
            AST::RangeSet(start, end, step) => write!(f, "{{ {}, {}...{} }}", start, step, end),
            AST::IfThenElse(cond, then_expr, else_expr) => write!(f, "(if {} then {} else {})", cond, then_expr, else_expr),
            AST::Image(a, b) => write!(f, "{}[{}]", a, b),

            AST::Bin(Op::Add, a, b) => write!(f, "({} + {})", a, b),
            AST::Bin(Op::Sub, a, b) => write!(f, "({} - {})", a, b),
            AST::Bin(Op::Mul, a, b) => write!(f, "({} * {})", a, b),
            AST::Bin(Op::Div, a, b) => write!(f, "({} / {})", a, b),
            AST::Bin(Op::Mod, a, b) => write!(f, "({} % {})", a, b),
            AST::Bin(Op::Exp, a, b) => write!(f, "({}^{})", a, b),

            AST::Bin(Op::Concat, a, b) => write!(f, "({} @ {})", a, b),

            AST::Bin(Op::And, a, b) => write!(f, "({} and {})", a, b),
            AST::Bin(Op::Or, a, b) => write!(f, "({} or {})", a, b),
            AST::Bin(Op::Imp, a, b) => write!(f, "({} ==> {})", a, b),

            AST::Bin(Op::Elem, a, b) => write!(f, "({} ∈ {})", a, b),

            AST::Bin(Op::Prove, a, b) => write!(f, "({} |- {})", a, b),

            AST::Bin(Op::Lt, a, b) => write!(f, "({} < {})", a, b),
            AST::Bin(Op::Le, a, b) => write!(f, "({} ≤ {})", a, b),
            AST::Bin(Op::Gt, a, b) => write!(f, "({} > {})", a, b),
            AST::Bin(Op::Ge, a, b) => write!(f, "({} ≥ {})", a, b),
            AST::Bin(Op::Equals, a, b) => write!(f, "({} = {})", a, b),
            AST::Bin(Op::NotEquals, a, b) => write!(f, "({} ≠ {})", a, b),

            AST::CompSet(var_doms, clauses) => {
                let mut s = String::new();
                s.push_str("{");
                s.push_str(var_doms.iter().map(|(x, dom)| format!("{} ∈ {}", x, dom)).collect::<Vec<String>>().join(", ").as_str());
                s.push_str(" : ");
                s.push_str(clauses.iter().map(|clause| format!("{}", clause)).collect::<Vec<String>>().join(", ").as_str());
                s.push_str("}");
                write!(f, "{}", s)
            }

            AST::Memo(name, args, body, _) => write!(f, "memo({:?}: {:?} |-> {})", name, args, body),
            AST::Function(name, args, body) => write!(f, "{:?}: {:?} |-> {}", name, args, body),
            AST::App(name, xs) => {
                if **name == AST::Var("|".to_string()) {
                    write!(f, "({} | {})", xs[0], xs[1])
                } else {
                    write!(f, "{}({})", name, xs.iter().map(|x| format!("{}", x)).collect::<Vec<String>>().join(", "))
                }
            }

            AST::Sum(a) => write!(f, "(Σ {})", a),
            AST::Negate(a) => write!(f, "(- {})", a),
            AST::Factorial(a) => write!(f, "({}!)", a),
            AST::Complement(a) => write!(f, "(not {})", a),
        }
    }
}

pub fn to_ast(pair : Pair<Rule>, arith_climber : &PrecClimber<Rule>, bool_climber : &PrecClimber<Rule>) -> Result<AST, String> {
    let primary = |pair| to_ast(pair, arith_climber, bool_climber);

    match pair.as_rule() {
        Rule::definition => {
            let mut it = pair.into_inner();
            let var = match primary(it.next().unwrap())? {
                AST::Var(x) => Ok(x),
                expr => Err(format!("Unexpected term {:?} on LHS of definition", expr))
            }?;
            let body = primary(it.next().unwrap())?;

            return Ok(AST::Definition(var, Box::new(body)));
        }

        Rule::rule => {
            let mut it = pair.into_inner();
            let lhs = primary(it.next().unwrap())?;
            let rhs = primary(it.next().unwrap())?;
            return Ok(AST::Rule(Vec::new(), Box::new(lhs), Box::new(rhs)));
        }

        Rule::proof_rule => {
            let mut it = pair.into_inner();
            let lhs = primary(it.next().unwrap())?;
            let rhs = primary(it.next().unwrap())?;
            return Ok(AST::Rule(vec!("proof rule".to_string()), Box::new(lhs), Box::new(rhs)));
        }

        Rule::rel => {
            let mut it = pair.into_inner();
            let mut res = primary(it.next().unwrap())?;
            loop {
                match it.next() {
                    None => break,
                    Some(rel_op) => {
                        let rhs = primary(it.next().unwrap())?;
                        match rel_op.as_str() {
                            "|-" => res = AST::Bin(Op::Prove, Box::new(res), Box::new(rhs)),
                            "<" => res = AST::Bin(Op::Lt, Box::new(res), Box::new(rhs)),
                            "<=" => res = AST::Bin(Op::Le, Box::new(res), Box::new(rhs)),
                            "≤" => res = AST::Bin(Op::Le, Box::new(res), Box::new(rhs)),
                            ">" => res = AST::Bin(Op::Gt, Box::new(res), Box::new(rhs)),
                            ">=" => res = AST::Bin(Op::Ge, Box::new(res), Box::new(rhs)),
                            "≥" => res = AST::Bin(Op::Ge, Box::new(res), Box::new(rhs)),
                            "=" => res = AST::Bin(Op::Equals, Box::new(res), Box::new(rhs)),
                            "!=" => res = AST::Bin(Op::NotEquals, Box::new(res), Box::new(rhs)),
                            "≠" => res = AST::Bin(Op::NotEquals, Box::new(res), Box::new(rhs)),
                            s => res = AST::App(Box::new(AST::Var(s.to_string())), vec!(res, rhs)),
                        }
                    }
                }
            }
            return Ok(res);
        }

        Rule::ite => {
            let mut it = pair.into_inner();
            let cond = primary(it.next().unwrap())?;
            let then_expr = primary(it.next().unwrap())?;
            let else_expr = primary(it.next().unwrap())?;

            return Ok(AST::IfThenElse(Box::new(cond), Box::new(then_expr), Box::new(else_expr)));
        }

        Rule::int => {
            return match BigInt::parse_bytes(pair.as_str().as_bytes(), 10) {
                Some(n) => Ok(AST::Int(n)),
                None => Err(format!("Failed to parse string '{}' as integer", pair.as_str()))
            }
        }

        Rule::finset => {
            let mut elems = Vec::new();
            for elem in pair.into_inner() {
                elems.push(primary(elem)?);
            }
            return Ok(AST::FinSet(elems));
        }

        Rule::rangeset => {
            let mut it = pair.into_inner();
            let start = primary(it.next().unwrap())?;
            let end = primary(it.next().unwrap())?;
            return Ok(AST::RangeSet(Box::new(start), Box::new(end), Box::new(AST::Int(One::one()))));
        }

        Rule::rangeset_step => {
            let mut it = pair.into_inner();
            let start = primary(it.next().unwrap())?;
            let second = primary(it.next().unwrap())?;
            let end = primary(it.next().unwrap())?;
            return Ok(AST::RangeSet(Box::new(start.clone()),
                                    Box::new(end),
                                    Box::new(AST::Bin(Op::Sub, Box::new(second), Box::new(start)))));
        }

        Rule::comp_set => {
            let mut it = pair.into_inner();

            let quant = primary(it.next().unwrap())?;

            let mut clauses = Vec::new();
            for term in it {
                clauses.push(primary(term)?);
            }

            match quant {
                AST::Bin(Op::Elem, x, dom) =>
                    match *x {
                        AST::Var(name) => {
                            return Ok(AST::CompSet(vec!((name, *dom)), clauses));
                        }

                        other_x => Err(format!("Expected var on LHS of elem in CompSet, but got: {:?}", other_x))
                    }

                body => {
                    let mut vars = Vec::new();
                    let mut quants = Vec::new();
                    let mut new_clauses = Vec::new();

                    for clause in clauses {
                        match clause {
                            AST::Bin(Op::Elem, x, dom) =>
                                match *x {
                                    AST::Var(name) => {
                                        if !vars.contains(&name) {
                                            vars.push(name.clone());
                                            quants.push((name, *dom));
                                        } else {
                                            new_clauses.push(AST::Bin(Op::Elem, Box::new(AST::Var(name)), dom))
                                        }
                                    }

                                   other => new_clauses.push(AST::Bin(Op::Elem, Box::new(other), dom))
                                }

                            other => new_clauses.push(other)
                        }
                    }

                    return Ok(AST::Image(Box::new(AST::Function(None, vars, Box::new(body))),
                                         Box::new(AST::CompSet(quants, new_clauses))));
                }
                // Err(format!("Expected Elem, but got: {:?}", other))
            }
        }

        Rule::bool_term => {
            let infix = |lhs : Result<AST, String>, op : Pair<Rule>, rhs : Result<AST, String>|
                match op.as_rule() {
                    Rule::elem => Ok(AST::Bin(Op::Elem, Box::new(lhs?), Box::new(rhs?))),
                    Rule::and_op => Ok(AST::Bin(Op::And, Box::new(lhs?), Box::new(rhs?))),
                    Rule::imp_op => Ok(AST::Bin(Op::Imp, Box::new(lhs?), Box::new(rhs?))),
                    Rule::or_op => Ok(AST::Bin(Op::Or, Box::new(lhs?), Box::new(rhs?))),
                    _ => unreachable!(),
                };
            return bool_climber.climb(pair.into_inner(), primary, infix);
        }

        Rule::list => {
            let mut elems = Vec::new();
            for elem in pair.into_inner() {
                elems.push(primary(elem)?);
            }
            return Ok(AST::List(elems));
        }

        Rule::call => {
            let mut it = pair.into_inner();
            let func = primary(it.next().unwrap())?;
            let mut args = Vec::new();

            for arg in it {
                args.push(primary(arg)?);
            }

            return Ok(AST::App(Box::new(func), args));
        }

        Rule::var => Ok(AST::Var(pair.as_str().to_string())),

        Rule::fun_single_arg => {
            let mut it = pair.into_inner();
            let arg = match primary(it.next().unwrap())? {
                AST::Var(x) => Ok(x),
                expr => Err(format!("Expected only Var as formal argument, but got: {:?}", expr))
            }?;
            let body = primary(it.next().unwrap())?;
            return Ok(AST::Function(None, vec![arg], Box::new(body)));
        }

        Rule::fun_multi_arg => {
            let mut args = Vec::new();
            let mut last = None;
            for arg in pair.into_inner() {
                match primary(arg)? {
                    AST::Var(x) => args.push(x),
                    expr => {
                        match last {
                            None => last = Some(expr),
                            Some(_) => return Err("Found multiple non-Var terms in function declaration".to_string())
                        }
                    }
                }
            }
            return Ok(AST::Function(None, args, Box::new(last.unwrap())));
        }

        Rule::image => {
            let mut it = pair.into_inner();
            let f = primary(it.next().unwrap())?;
            let arg = primary(it.next().unwrap())?;
            return Ok(AST::Image(Box::new(f), Box::new(arg)));
        }

        Rule::assumption => Ok(AST::Assumption(Box::new(primary(pair.into_inner().next().unwrap())?))),
        Rule::prove => Ok(AST::Prove(Box::new(primary(pair.into_inner().next().unwrap())?))),

        Rule::factorial => {
            let mut it = pair.into_inner();
            let arg = primary(it.next().unwrap())?;
            return Ok(AST::Factorial(Box::new(arg)));
        }

        Rule::negate => {
            let mut it = pair.into_inner();
            let arg = primary(it.next().unwrap())?;
            return Ok(AST::Negate(Box::new(arg)));
        }

        Rule::complement => {
            let mut it = pair.into_inner();
            let arg = primary(it.next().unwrap())?;
            return Ok(AST::Complement(Box::new(arg)));
        }

        Rule::sum => {
            let mut it = pair.into_inner();
            let arg = primary(it.next().unwrap())?;
            return Ok(AST::Sum(Box::new(arg)));
        }

        Rule::EOI => Ok(AST::Skip()),

        Rule::bin_arith => {
            let infix = |lhs : Result<AST, String>, op : Pair<Rule>, rhs : Result<AST, String>|
                match op.as_rule() {
                    Rule::add => Ok(AST::Bin(Op::Add, Box::new(lhs?), Box::new(rhs?))),
                    Rule::sub => Ok(AST::Bin(Op::Sub, Box::new(lhs?), Box::new(rhs?))),
                    Rule::mul => Ok(AST::Bin(Op::Mul, Box::new(lhs?), Box::new(rhs?))),
                    Rule::div => Ok(AST::Bin(Op::Div, Box::new(lhs?), Box::new(rhs?))),
                    Rule::mod_op => Ok(AST::Bin(Op::Mod, Box::new(lhs?), Box::new(rhs?))),
                    Rule::exp => Ok(AST::Bin(Op::Exp, Box::new(lhs?), Box::new(rhs?))),
                    Rule::concat => Ok(AST::Bin(Op::Concat, Box::new(lhs?), Box::new(rhs?))),
                    _ => unreachable!(),
                };

            return arith_climber.climb(pair.into_inner(), primary, infix);
        }

        _ => Err(format!("Unimplemented: {:?}", pair))
    }
}

pub fn parse(source : &str) -> Result<Vec<AST>, String> {
    let pairs = LangParser::parse(Rule::main, source).expect("parse error");

    let mut res = Vec::new();

    let arith_climber = PrecClimber::new(vec!(
            Operator::new(Rule::concat, Assoc::Left),
            Operator::new(Rule::add, Assoc::Left)
            | Operator::new(Rule::sub, Assoc::Left),
            Operator::new(Rule::mul, Assoc::Left)
            | Operator::new(Rule::div, Assoc::Left)
            | Operator::new(Rule::mod_op, Assoc::Left),
            Operator::new(Rule::exp, Assoc::Right)));

    let bool_climber = PrecClimber::new(vec!(
            Operator::new(Rule::imp_op, Assoc::Right),
            Operator::new(Rule::and_op, Assoc::Left),
            Operator::new(Rule::or_op, Assoc::Left),
            Operator::new(Rule::elem, Assoc::Left)));

    for pair in pairs {
        res.push(to_ast(pair, &arith_climber, &bool_climber)?);
    }

    return Ok(res);
}

pub fn as_int(expr : AST) -> Result<BigInt, String> {
    match expr {
        AST::Int(n) => Ok(n),
        _ => Err(format!("Expected integer but got {:?}", expr))
    }
}

pub fn subs_expr(expr : AST, rep : &AST, pat : &AST) -> AST {
    if &expr == pat {
        return rep.clone();
    }
    match expr {
        AST::Definition(name, body) => AST::Definition(name, Box::new(subs_expr(*body, rep, pat))),
        AST::Rule(attrs, lhs, rhs) => AST::Rule(attrs, Box::new(subs_expr(*lhs, rep, pat)),
                                                       Box::new(subs_expr(*rhs, rep, pat))),

        AST::Assumption(t) => AST::Assumption(Box::new(subs_expr(*t, rep, pat))),
        AST::Prove(t) => AST::Prove(Box::new(subs_expr(*t, rep, pat))),

        AST::FinSet(elems) => AST::FinSet(elems.into_iter().map(| e | subs_expr(e, rep, pat)).collect()),

        AST::Memo(name, args, body, memo) => AST::Memo(name, args, body, memo),

        AST::List(elems) => AST::List(elems.into_iter().map(| e | subs_expr(e, rep, pat)).collect()),

        AST::Seq(name, implementation) => AST::Seq(name, implementation),

        AST::RangeSet(start, end, step) =>
                AST::RangeSet(Box::new(subs_expr(*start, rep, pat)),
                              Box::new(subs_expr(*end, rep, pat)),
                              Box::new(subs_expr(*step, rep, pat))),

        AST::CompSet(var_doms, clauses) => {
            let mut found = false;
            let mut new_var_doms = Vec::new();
            for (x, dom) in var_doms {
                if &AST::Var(x.clone()) == pat {
                    found = true;
                }

                if found {
                    new_var_doms.push((x, dom));
                } else {
                    new_var_doms.push((x, subs_expr(dom, rep, pat)));
                }
            }

            if found {
                return AST::CompSet(new_var_doms, clauses);
            }

            let mut new_clauses = Vec::new();
            for clause in clauses {
                new_clauses.push(subs_expr(clause, rep, pat));
            }
            return AST::CompSet(new_var_doms, new_clauses);
        }

        AST::IfThenElse(cond, then_expr, else_expr) =>
                AST::IfThenElse(Box::new(subs_expr(*cond, rep, pat)),
                                Box::new(subs_expr(*then_expr, rep, pat)),
                                Box::new(subs_expr(*else_expr, rep, pat))),

        AST::Bin(op, a, b) => AST::Bin(op, Box::new(subs_expr(*a, rep, pat)),
                                           Box::new(subs_expr(*b, rep, pat))),

        AST::App(f, args) => AST::App(Box::new(subs_expr(*f, rep, pat)),
                                      args.into_iter().map(| e | subs_expr(e, rep, pat)).collect()),

        AST::Function(name, formal_args, body) => {
            let mut found = false;
            for formal_arg in &formal_args {
                if &AST::Var(formal_arg.to_string()) == pat {
                    found = true;
                }
            }
            if found {
                return AST::Function(name, formal_args, body);
            } else {
                return AST::Function(name, formal_args, Box::new(subs_expr(*body, rep, pat)));
            }
        }

        AST::Image(f, arg) => AST::Image(Box::new(subs_expr(*f, rep, pat)),
                                         Box::new(subs_expr(*arg, rep, pat))),

        AST::Factorial(arg) => AST::Factorial(Box::new(subs_expr(*arg, rep, pat))),
        AST::Negate(arg) => AST::Negate(Box::new(subs_expr(*arg, rep, pat))),
        AST::Complement(arg) => AST::Complement(Box::new(subs_expr(*arg, rep, pat))),
        AST::Sum(arg) => AST::Sum(Box::new(subs_expr(*arg, rep, pat))),

        AST::Int(n) => AST::Int(n),
        AST::Var(x) => AST::Var(x),
        AST::Skip() => AST::Skip()
    }
}

pub fn subs(expr : AST, to_subs : &HashMap<String, AST>) -> AST {
    match expr {
        AST::Definition(name, body) => AST::Definition(name, Box::new(subs(*body, to_subs))),
        AST::Rule(attrs, lhs, rhs) => AST::Rule(attrs, Box::new(subs(*lhs, to_subs)),
                                                       Box::new(subs(*rhs, to_subs))),

        AST::Assumption(t) => AST::Assumption(Box::new(subs(*t, to_subs))),
        AST::Prove(t) => AST::Prove(Box::new(subs(*t, to_subs))),

        AST::FinSet(elems) => AST::FinSet(elems.into_iter().map(| e | subs(e, to_subs)).collect()),

        AST::Memo(name, args, body, memo) => AST::Memo(name, args, body, memo),

        AST::List(elems) => AST::List(elems.into_iter().map(| e | subs(e, to_subs)).collect()),

        AST::Seq(name, implementation) => AST::Seq(name, implementation),

        AST::RangeSet(start, end, step) =>
                AST::RangeSet(Box::new(subs(*start, to_subs)),
                              Box::new(subs(*end, to_subs)),
                              Box::new(subs(*step, to_subs))),

        AST::CompSet(var_doms, clauses) => {
            let mut new_subs = to_subs.clone();
            let mut new_var_doms = Vec::new();
            for (x, dom) in var_doms {
                let x_cp = x.clone();
                new_var_doms.push((x, subs(dom, &new_subs)));
                new_subs.remove(&x_cp);
            }
            let mut new_clauses = Vec::new();
            for clause in clauses {
                new_clauses.push(subs(clause, &new_subs));
            }
            return AST::CompSet(new_var_doms, new_clauses);
        }

        AST::IfThenElse(cond, then_expr, else_expr) =>
                AST::IfThenElse(Box::new(subs(*cond, to_subs)),
                                Box::new(subs(*then_expr, to_subs)),
                                Box::new(subs(*else_expr, to_subs))),

        AST::Bin(op, a, b) => AST::Bin(op, Box::new(subs(*a, to_subs)),
                                           Box::new(subs(*b, to_subs))),

        AST::App(f, args) => {
            if *f == AST::Var("$fresh".to_string()) {
                match args[0].clone() {
                    AST::Var(x) => {
                        let mut new_subs = to_subs.clone();
                        unsafe {
                            fresh_counter += 1;
                            new_subs.insert(x.clone(), AST::Var(format!("v_{}", fresh_counter)));
                        }
                        return subs(args[1].clone(), &new_subs);
                    }
                    _ => (),
                }
            }

            return AST::App(Box::new(subs(*f, to_subs)),
                            args.into_iter().map(| e | subs(e, to_subs)).collect());
        }

        AST::Function(name, formal_args, body) => {
            let mut new_subs = to_subs.clone();
            for formal_arg in &formal_args {
                new_subs.remove(formal_arg.as_str());
            }
            return AST::Function(name, formal_args, Box::new(subs(*body, &new_subs)));
        }

        AST::Image(f, arg) => AST::Image(Box::new(subs(*f, to_subs)),
                                         Box::new(subs(*arg, to_subs))),

        AST::Factorial(arg) => AST::Factorial(Box::new(subs(*arg, to_subs))),
        AST::Negate(arg) => AST::Negate(Box::new(subs(*arg, to_subs))),
        AST::Complement(arg) => AST::Complement(Box::new(subs(*arg, to_subs))),
        AST::Sum(arg) => AST::Sum(Box::new(subs(*arg, to_subs))),

        AST::Int(n) => AST::Int(n),
        AST::Var(x) =>
            if to_subs.contains_key(x.as_str()) {
                return to_subs[x.as_str()].clone();
            } else {
                return AST::Var(x);
            },

        AST::Skip() => AST::Skip()
    }
}

pub fn is_list(expr : &AST) -> bool {
    match expr {
        AST::List(_) => true,
        AST::Image(_, arg) => is_list(&*arg),

        _ => false
    }
}

pub fn is_finite(expr : &AST) -> bool {
    match expr {
        AST::Int(_) => true,

        AST::List(_) => true,
        AST::FinSet(_) => true,

        AST::Bin(Op::Lt, _, _) => true,
        AST::Bin(Op::Le, _, _) => true,
        AST::Bin(Op::Gt, _, _) => true,
        AST::Bin(Op::Ge, _, _) => true,
        AST::Bin(Op::Equals, _, _) => true,
        AST::Bin(Op::NotEquals, _, _) => true,

        AST::App(_, _) => true,

        AST::IfThenElse(_, then_expr, else_expr) => is_finite(then_expr) && is_finite(else_expr),

        AST::Factorial(n) => is_finite(n),
        AST::Negate(n) => is_finite(n),
        AST::Complement(b) => is_finite(b),

        // TODO: not really right, we need to make sure every element of s is finite too...
        AST::Sum(s) => is_finite(s),

        AST::Image(_, arg) => is_finite(arg),

        AST::Bin(_, a, b) => is_finite(a) && is_finite(b),

        AST::RangeSet(start, end, _) => is_finite(start) && is_finite(end),
        AST::CompSet(var_doms, _) => {
            for (_, dom) in var_doms {
                if !is_finite(dom) {
                    return false;
                }
            }
            return true;
        }

        _ => false
    }
}

struct RangeSetIterator {
    cur_val : BigInt,
    end_val : BigInt,
    step : BigInt
}

impl RangeSetIterator {
    fn new(cur_val : BigInt, end_val : BigInt, step : BigInt) -> RangeSetIterator {
        return RangeSetIterator { cur_val: cur_val, end_val: end_val, step: step };
    }
}

impl Iterator for RangeSetIterator {
    type Item = AST;

    fn next(&mut self) -> Option<Self::Item> {
        if self.cur_val > self.end_val {
            return None;
        }

        let old_val = self.cur_val.clone();
        self.cur_val += self.step.clone();
        return Some(AST::Int(old_val));
    }
}

struct CompSetIterator {
    i : usize,
    cur_its : Vec<Box<dyn Iterator<Item=Result<AST, String>>>>,
    to_subs : HashMap<String, AST>,
    var_doms : Vec<(String, AST)>,
    clauses : Vec<AST>
}

impl CompSetIterator {
    fn new(var_doms : Vec<(String, AST)>, clauses : Vec<AST>) -> Result<CompSetIterator, String> {
        let mut cur_its = Vec::new();
        for (_, dom) in &var_doms {
            cur_its.push(enumerate(dom.clone())?);
        }

        return Ok(CompSetIterator {
            i: 0,
            cur_its: cur_its,
            to_subs: HashMap::new(),
            var_doms: var_doms,
            clauses: clauses
        });
    }
}

impl Iterator for CompSetIterator {
    type Item = Result<AST, String>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let mut skip = false;
            for j in self.i..self.var_doms.len() {
                let (x, dom) = &self.var_doms[j];
                match (*self.cur_its[j]).next() {
                    // If this iterator has a next value, then we simply take it and add it to the
                    // hashmap.
                    Some(x_val) => {
                        self.to_subs.insert(x.clone(), match x_val {
                            Ok(val) => val,
                            Err(err) => return Some(Err(err))
                        });
                    }

                    // If it does not, then we need to go back and get new values from the previous
                    // iterators. However, if there is no previous iterator (i.e., j = 0), then we
                    // are simply done iterating.
                    None => {
                        if j == 0 {
                            return None;
                        } else {
                            self.i -= 1;
                            self.cur_its[j] = match enumerate(dom.clone()) {
                                Ok(it) => it,
                                Err(err) => return Some(Err(err))
                            };
                            skip = true;
                            break;
                        }
                    }
                }
            }

            if skip {
                continue;
            }

            let mut res = true;
            for clause in &self.clauses {
                match eval(subs(clause.clone(), &self.to_subs)) {
                    Ok(val) => match as_int(val) {
                        Ok(n) => if n == Zero::zero() {
                            res = false;
                            break;
                        }
                        Err(err) => return Some(Err(err))
                    }
                    Err(err) => return Some(Err(err))
                }
            }

            if res {
                return Some(Ok(make_val(&self.to_subs,&self.var_doms)));
            } else {
                continue;
            }
        }
    }
}

pub fn enumerate(expr : AST) -> Result<Box<dyn Iterator<Item=Result<AST, String>>>, String> {
    match expr {
        AST::FinSet(elems) => Ok(Box::new(elems.into_iter().map(Ok))),
        AST::List(elems) => Ok(Box::new(elems.into_iter().map(Ok))),

        AST::RangeSet(start, end, step) => {
            let start_val = as_int(eval(*start)?)?;
            let end_val = as_int(eval(*end)?)?;
            let step_val = as_int(eval(*step)?)?;
            return Ok(Box::new(RangeSetIterator::new(start_val, end_val, step_val).map(Ok)));
        }

        AST::CompSet(var_doms, clauses) => {
            return Ok(Box::new(CompSetIterator::new(var_doms, clauses)?));
        }

        AST::Bin(Op::Concat, a, b) => Ok(Box::new(enumerate(*a)?.chain(enumerate(*b)?))),

        AST::Bin(op, a, b) => enumerate(eval(AST::Bin(op, a, b))?),

        AST::App(f, args) => enumerate(eval(AST::App(f, args))?),

        AST::Image(f, arg) => {
            let func = eval(*f)?;
            return Ok(Box::new(
                        enumerate(*arg)?
                        .map(move |x| eval(AST::App(Box::new(func.clone()), vec!(x?))))));
        }

        AST::IfThenElse(cond, then_expr, else_expr) => enumerate(eval(AST::IfThenElse(cond, then_expr, else_expr))?),

        expr => Err(format!("Cannot enumerate: {:?}", expr)),
    }
}

pub fn enum_contains(enumerable : AST, search_val : AST) -> Result<bool, String> {
    match enumerable {
        AST::RangeSet(start, end, step) => {
            match search_val {
                AST::Int(n) => {
                    let start_val = as_int(eval(*start)?)?;
                    let end_val = as_int(eval(*end)?)?;
                    let step_val = as_int(eval(*step)?)?;
                    return Ok(n >= start_val && n <= end_val && (n - start_val) % step_val == Zero::zero());
                }
                _ => Ok(false)
            }
        }

        AST::Seq(_, implementation) => {
            return Ok(implementation.borrow_mut().index_of(search_val) != None);
        }

        other => {
            for val in enumerate(other)? {
                if search_val == val? {
                    return Ok(true);
                }
            }
            return Ok(false);
        }
    }
}

pub fn make_val(to_subs : &HashMap<String, AST>,
                var_doms : &[(String, AST)]) -> AST {
    if var_doms.len() == 1 {
        let (x, _) = &var_doms[0];
        return to_subs[x].clone();
    }

    let mut res = Vec::new();

    for (x, _) in var_doms {
        res.push(to_subs[x].clone());
    }

    return AST::List(res);
}

pub fn is_value(expr : &AST) -> bool {
    match expr {
        AST::Skip() => true,
        AST::Int(_) => true,
        AST::Var(_) => true,
        AST::Seq(_, _) => true,

        AST::Function(_, _, _) => true,
        AST::Memo(_, _, _, _) => true,

        AST::FinSet(elems) => elems.iter().all(is_value),
        AST::List(elems) => elems.iter().all(is_value),

        _ => false
    }
}

pub fn eval(expr : AST) -> Result<AST, String> {
    match expr {
        AST::Int(n) => Ok(AST::Int(n)),

        AST::Seq(name, implementation) => Ok(AST::Seq(name, implementation)),

        AST::FinSet(elems) => {
            let mut new_elems = Vec::new();
            for e in elems {
                new_elems.push(eval(e)?);
            }
            return Ok(AST::FinSet(new_elems));
        }

        AST::List(elems) => {
            let mut new_elems = Vec::new();
            for e in elems {
                new_elems.push(eval(e)?);
            }
            return Ok(AST::List(new_elems));
        }

        AST::RangeSet(start, end, step) => {
            let mut elems = Vec::new();
            let start_val = as_int(eval(*start)?)?;
            let end_val = as_int(eval(*end)?)?;
            let step_val = as_int(eval(*step)?)?;
            for elem in RangeSetIterator::new(start_val, end_val, step_val) {
                elems.push(elem);
            }
            return Ok(AST::FinSet(elems));
        }

        AST::Bin(Op::Elem, x, dom) => {
            let xval = eval(*x)?;
            if enum_contains(*dom, xval)? {
                return Ok(AST::Int(One::one()));
            } else{
                return Ok(AST::Int(Zero::zero()));
            }
        }

        AST::CompSet(var_doms, clauses) => {
            let mut elems = Vec::new();
            for val in enumerate(AST::CompSet(var_doms, clauses))? {
                elems.push(val?);
            }
            return Ok(AST::FinSet(elems));
        }

        AST::IfThenElse(cond, then_expr, else_expr) => {
            if as_int(eval(*cond)?)? != Zero::zero() {
                return eval(*then_expr);
            } else {
                return eval(*else_expr);
            }
        }

        AST::Bin(Op::Concat, a, b) => {
            let mut vals = Vec::new();
            for x in enumerate(AST::Bin(Op::Concat, a, b))? {
                vals.push(eval(x?)?);
            }
            return Ok(AST::List(vals));
        }

        AST::Bin(Op::Add, a, b) => {
            return Ok(AST::Int(as_int(eval(*a)?)? + as_int(eval(*b)?)?));
        }

        AST::Bin(Op::Sub, a, b) => {
            return Ok(AST::Int(as_int(eval(*a)?)? - as_int(eval(*b)?)?));
        }

        AST::Bin(Op::Mul, a, b) => {
            return Ok(AST::Int(as_int(eval(*a)?)? * as_int(eval(*b)?)?));
        }

        AST::Bin(Op::Div, a, b) => {
            let aval = as_int(eval(*a)?)?;
            let bval = as_int(eval(*b)?)?;

            if bval == Zero::zero() {
                return Err("Cannot divide by 0".to_string());
            }

            if aval.clone() % bval.clone() == Zero::zero() {
                return Ok(AST::Int(aval / bval));
            } else {
                return Err(format!("Cannot do {} / {} (rational numbers not implemented)", aval, bval));
            }
        }

        AST::Bin(Op::Mod, a, b) => {
            let bval = as_int(eval(*b)?)?;
            if bval == Zero::zero() {
                return Err("Cannot divide by 0".to_string());
            }
            return Ok(AST::Int(as_int(eval(*a)?)? % bval));
        }

        AST::Bin(Op::Exp, a, b) => {
            return match as_int(eval(*b)?)?.to_biguint() {
                Some(n) => Ok(AST::Int(Pow::pow(as_int(eval(*a)?)?, n))),
                None => Err("Cannot raise integer to negative power!".to_string())
            };
        }

        AST::Bin(Op::Equals, a, b) => {
            if eval(*a)? == eval(*b)? {
                return Ok(AST::Int(One::one()));
            } else {
                return Ok(AST::Int(Zero::zero()));
            }
        }

        AST::Bin(Op::Prove, assms, b) => {
            for assm in enumerate(*assms)? {
                if as_int(eval(assm?)?)? == Zero::zero() {
                    return Ok(AST::Int(One::one()));
                }
            }
            return eval(*b);
        }

        AST::Bin(Op::NotEquals, a, b) => {
            if eval(*a)? != eval(*b)? {
                return Ok(AST::Int(One::one()));
            } else {
                return Ok(AST::Int(Zero::zero()));
            }
        }

        AST::Bin(Op::Lt, a, b) => {
            if as_int(eval(*a)?)? < as_int(eval(*b)?)? {
                return Ok(AST::Int(One::one()));
            } else {
                return Ok(AST::Int(Zero::zero()));
            }
        }

        AST::Bin(Op::Le, a, b) => {
            if as_int(eval(*a)?)? <= as_int(eval(*b)?)? {
                return Ok(AST::Int(One::one()));
            } else {
                return Ok(AST::Int(Zero::zero()));
            }
        }

        AST::Bin(Op::Gt, a, b) => {
            if as_int(eval(*a)?)? > as_int(eval(*b)?)? {
                return Ok(AST::Int(One::one()));
            } else {
                return Ok(AST::Int(Zero::zero()));
            }
        }

        AST::Bin(Op::Ge, a, b) => {
            if as_int(eval(*a)?)? >= as_int(eval(*b)?)? {
                return Ok(AST::Int(One::one()));
            } else {
                return Ok(AST::Int(Zero::zero()));
            }
        }

        AST::Bin(Op::Or, a, b) => {
            let lval = as_int(eval(*a)?)?;
            if lval != Zero::zero() {
                return Ok(AST::Int(lval));
            } else {
                return eval(*b);
            }
        }

        AST::Bin(Op::And, a, b) => {
            let lval = as_int(eval(*a)?)?;

            if lval == Zero::zero() {
                return Ok(AST::Int(lval));
            } else {
                return eval(*b);
            }
        }

        AST::App(func, args) => {
            match eval(*func)? {
                AST::Function(name, formal_args, body) => {
                    let mut to_subs = HashMap::new();
                    for (formal, actual) in formal_args.iter().zip(args) {
                        to_subs.insert(formal.clone(), eval(actual)?);
                    }

                    if let Some(ref f_name) = name {
                        to_subs.insert(f_name.clone(), AST::Function(name.clone(), formal_args, body.clone()));
                    }

                    return eval(subs(*body, &to_subs));
                }

                AST::Memo(name, formal_args, body, memo) => {
                    let mut vals = Vec::new();

                    for arg in args {
                        vals.push(eval(arg)?);
                    }

                    if memo.borrow().contains_key(&vals) {
                        return memo.borrow()[&vals].clone();
                    }

                    let mut to_subs = HashMap::new();
                    for (formal, val) in formal_args.iter().zip(vals.clone()) {
                        to_subs.insert(formal.clone(), val);
                    }

                    if let Some(ref f_name) = name {
                        to_subs.insert(f_name.clone(), AST::Memo(name.clone(), formal_args, body.clone(), memo.clone()));
                    }

                    let res = eval(subs(*body, &to_subs));
                    memo.borrow_mut().insert(vals, res.clone());

                    return res;
                }

                AST::List(elems) => {
                    let n = to_usize(&as_int(eval(args[0].clone())?)?)?;
                    return Ok(elems[n].clone());
                }

                AST::Seq(_, implementation) => {
                    let n = to_usize(&as_int(eval(args[0].clone())?)?)?;
                    return implementation.borrow_mut().nth(n);
                }

                AST::Var(name) => {
                    match name.as_str() {
                        "set" => {
                            let mut res = HashSet::new();
                            for val in enumerate(args[0].clone())? {
                                res.insert(val?);
                            }
                            return Ok(AST::FinSet(res.into_iter().collect()));
                        }

                        "list" => {
                            let mut res = Vec::new();
                            for val in enumerate(args[0].clone())? {
                                res.push(val?);
                            }
                            return Ok(AST::List(res));
                        }

                        "card" => {
                            let mut n = Zero::zero();
                            for _ in enumerate(args[0].clone())? {
                                n += 1;
                            }
                            return Ok(AST::Int(n));
                        }

                        "gcd" => {
                            let mut a = as_int(eval(args[0].clone())?)?;
                            let mut b = as_int(eval(args[0].clone())?)?;

                            while b != Zero::zero() {
                                let temp = a;
                                a = b.clone();
                                b = temp % b;
                            }

                            return Ok(AST::Int(a));
                        }

                        "memo" => {
                            match eval(args[0].clone())? {
                                AST::Function(name, args, body) => {
                                    return Ok(AST::Memo(name, args, body, Rc::new(RefCell::new(HashMap::new()))));
                                }

                                val => Err(format!("memo() expected a function but got: {:?}", val))
                            }
                        }

                        "sort" => {
                            let mut items = Vec::new();
                            for val in enumerate(args[0].clone())? {
                                items.push(val?);
                            }
                            items.sort();
                            return Ok(AST::List(items));
                        }

                        "|" => {
                            return eval(AST::Bin(Op::Equals, Box::new(AST::Bin(Op::Mod, Box::new(args[1].clone()), Box::new(args[0].clone()))),
                                                             Box::new(AST::Int(Zero::zero()))));
                        }

                        "μ" => {
                            let mut n = Zero::zero();
                            let f = eval(args[0].clone())?;
                            if args.len() > 1 {
                                n = as_int(eval(args[1].clone())?)?;
                            }
                            if args.len() > 2 {
                                let mut m = match eval(args[2].clone())? {
                                    AST::Function(name, args, body) => {
                                        let bound_func = AST::Function(name, args, body);
                                        let mut upper = n.clone();
                                        while as_int(eval(AST::App(Box::new(f.clone()), vec!(AST::Int(upper.clone()))))?)? == Zero::zero() {
                                            upper = as_int(eval(AST::App(Box::new(bound_func.clone()), vec!(AST::Int(upper.clone()))))?)?;
                                        }
                                        Ok(upper)
                                    }

                                    AST::Int(k) => Ok(k),

                                    expr => Err(format!("Minimization operator expected either Function or Int as its third argument, but got: {:?}", expr))
                                }?;

                                while (m.clone() - n.clone()) > One::one() {
                                    // TODO: Some of these clones should be unnecessary...
                                    let guess : BigInt = (n.clone() + m.clone()) / 2;
                                    if as_int(eval(AST::App(Box::new(f.clone()), vec!(AST::Int(guess.clone()))))?)? == Zero::zero() {
                                        n = guess;
                                    } else {
                                        m = guess;
                                    }
                                }
                            }

                            while as_int(eval(AST::App(Box::new(f.clone()), vec!(AST::Int(n.clone()))))?)? == Zero::zero() {
                                n += 1;
                            }
                            return Ok(AST::Int(n));
                        }

                        _ => Ok(AST::App(Box::new(AST::Var(name)), args))
                    }
                }

                res => Err(format!("Expected a function in function application expression, got {:?}", res))
            }
        }

        AST::Var(x) => Ok(AST::Var(x)),

        AST::Function(name, formal_args, body) => Ok(AST::Function(name, formal_args, body)),
        AST::Memo(name, formal_args, body, memo) => Ok(AST::Memo(name, formal_args, body, memo)),

        AST::Image(f, arg) => {
            let mut vals = Vec::new();
            let arg_is_finite = is_finite(&arg);

            if !arg_is_finite {
                return Ok(AST::Image(Box::new(eval(*f)?), Box::new(eval(*arg)?)));
            }

            let arg_is_list = is_list(&arg);

            let func = eval(*f)?;
            for val in enumerate(*arg)? {
                vals.push(eval(AST::App(Box::new(func.clone()), vec!(val?)))?);
            }

            if arg_is_list && arg_is_finite {
                return Ok(AST::List(vals));
            } else {
                return Ok(AST::FinSet(vals));
            }
        }

        AST::Sum(s) => {
            if is_finite(&s) {
                let mut accum = Zero::zero();

                for val in enumerate(*s)? {
                    accum += as_int(val?)?;
                }

                return Ok(AST::Int(accum));
            } else {
                return Ok(AST::Sum(Box::new(eval(*s)?)));
            }
        }

        AST::Factorial(arg) => {
            let n = as_int(eval(*arg)?)?;

            let mut res = One::one();
            let mut i : BigInt = One::one();
            while i <= n {
                res *= i.clone();
                i += 1;
            }

            return Ok(AST::Int(res));
        }

        AST::Negate(arg) => Ok(AST::Int(-as_int(eval(*arg)?)?)),

        AST::Complement(arg) => {
            if as_int(eval(*arg)?)? == Zero::zero() {
                return Ok(AST::Int(One::one()));
            } else {
                return Ok(AST::Int(Zero::zero()));
            }
        }

        expr => Err(format!("Unimplemented expression variant: {:?}", expr))
    }
}

pub fn union(a : HashSet<String>, b : HashSet<String>) -> HashSet<String> {
    return a.into_iter().chain(b.into_iter()).collect();
}

pub fn diff(a : HashSet<String>, b : &HashSet<String>) -> HashSet<String> {
    return a.into_iter().filter(|v| !b.contains(v)).collect();
}

pub fn vars(expr : &AST) -> HashSet<String> {
    match expr {
        AST::Skip() => HashSet::new(),
        AST::Int(_) => HashSet::new(),

        AST::Assumption(t) => vars(t),
        AST::Prove(t) => vars(t),

        AST::Var(x) => {
            let mut vs = HashSet::new();
            if !x.starts_with('$') && x.chars().next().unwrap().is_alphabetic() {
                vs.insert(x.clone());
            }
            return vs;
        }
        AST::Definition(_, body) => vars(body),
        AST::Rule(_, lhs, rhs) => union(vars(lhs), vars(rhs)),

        AST::Seq(_, _) => HashSet::new(),

        AST::FinSet(elems) => elems.iter().map(vars).fold(HashSet::new(), union),
        AST::List(elems) => elems.iter().map(vars).fold(HashSet::new(), union),

        AST::RangeSet(start, end, step) => union(vars(start), union(vars(end), vars(step))),
        AST::Image(f, s) => union(vars(f), vars(s)),
        AST::CompSet(var_doms, clauses) => {
            let mut bound_vars = HashSet::new();
            let mut res = HashSet::new();
            for (x, dom) in var_doms {
                for v in vars(dom) {
                    if !bound_vars.contains(&v) {
                        res.insert(v);
                    }
                }
                bound_vars.insert(x.clone());
            }
            for clause in clauses {
                res.extend(diff(vars(clause), &bound_vars));
            }
            return res;
        }

        AST::App(f, xs) => union(vars(f), xs.iter().map(vars).fold(HashSet::new(), union)),

        AST::Bin(_, a, b) => union(vars(a), vars(b)),

        AST::Function(_, args, body) => {
            let arg_vars : HashSet<String> = args.iter().cloned().collect();
            return diff(vars(body), &arg_vars);
        }

        AST::Memo(_, args, body, _) => {
            let arg_vars : HashSet<String> = args.iter().cloned().collect();
            return diff(vars(body), &arg_vars);
        }

        AST::IfThenElse(cond, then_val, else_val) => union(vars(cond), union(vars(then_val), vars(else_val))),

        AST::Sum(a) => vars(a),
        AST::Negate(a) => vars(a),
        AST::Complement(a) => vars(a),
        AST::Factorial(a) => vars(a),
    }
}

#[derive(Hash, PartialEq, Eq, Debug, Clone, Ord, PartialOrd)]
enum UnificationStatus {
    Running,
    Done,
    Failed
}

#[derive(PartialEq, Eq, Debug, Clone)]
struct Unification {
    eqs : Vec<(AST, AST)>,
    lhs_vars : HashSet<String>,
    subs : HashMap<String, AST>,
}

impl Unification {
    fn new(lhs : AST, rhs : AST) -> Unification {
        let lhs_vars = vars(&lhs);
        return Unification {
            eqs: vec!((lhs, rhs)),
            lhs_vars: lhs_vars,
            subs: HashMap::new(),
        };
    }

    fn step(&mut self, unifs : &mut Vec<Unification>) -> UnificationStatus {
        // println!("Equations: {:?}", self.eqs);
        // println!("Substitution: {:?}", self.subs);
        match self.eqs.pop() {
            None => {
                return UnificationStatus::Done;
            }

            Some((lhs, rhs)) => {
                if lhs == rhs {
                    return UnificationStatus::Running;
                }

                match (lhs, rhs) {
                    (AST::Var(x), t) => {
                        if let Some(name) = x.strip_prefix('$').map(|s| s.to_string()) {
                            if AST::Var(name) == t {
                                return UnificationStatus::Running;
                            } else {
                                return UnificationStatus::Failed;
                            }
                        } else if !self.lhs_vars.contains(&x) {
                            if AST::Var(x) == t {
                                return UnificationStatus::Running;
                            } else {
                                return UnificationStatus::Failed;
                            }
                        } else {
                            let mut new_subs = HashMap::new();
                            new_subs.insert(x, t);
                            for (a, b) in &mut self.eqs {
                                *a = subs(a.clone(), &new_subs);
                                *b = subs(b.clone(), &new_subs);
                            }
                            self.subs.extend(new_subs);
                            return UnificationStatus::Running;
                        }
                    }

                    (AST::FinSet(es1), AST::FinSet(es2)) => {
                        self.eqs.extend(es1.into_iter().zip(es2));
                        return UnificationStatus::Running;
                    }

                    (AST::List(es1), AST::List(es2)) => {
                        self.eqs.extend(es1.into_iter().zip(es2));
                        return UnificationStatus::Running;
                    }

                    (AST::Bin(op1, a, b), AST::Bin(op2, c, d)) => {
                        if op1 != op2 {
                            return UnificationStatus::Failed;
                        }
                        self.eqs.push((*a, *c));
                        self.eqs.push((*b, *d));
                        return UnificationStatus::Running;
                    }

                    (AST::App(f, xs), AST::Var(y)) => {
                        if *f == AST::Var("$var".to_string()) {
                            self.eqs.push((xs[0].clone(), AST::Var(y)));
                            return UnificationStatus::Running;
                        } else if *f == AST::Var("$coeff".to_string()) {
                            self.eqs.push((xs[0].clone(), AST::Int(One::one())));
                            self.eqs.push((xs[1].clone(), AST::Var(y)));
                            return UnificationStatus::Running;
                        } else {
                            return UnificationStatus::Failed;
                        }
                    }

                    (AST::App(f, xs), AST::Int(n)) => {
                        if *f == AST::Var("$int".to_string()) {
                            self.eqs.push((xs[0].clone(), AST::Int(n)));
                            return UnificationStatus::Running;
                        } else if *f == AST::Var("$s".to_string()) {
                            if n <= Zero::zero() {
                                return UnificationStatus::Failed;
                            } else {
                                self.eqs.push((xs[0].clone(), AST::Int(n - 1)));
                                return UnificationStatus::Running;
                            }
                        } else if *f == AST::Var("$prime_factor".to_string()) {
                            for p in factor(n.clone()) {
                                if p == n {
                                    break;
                                }
                                let mut new_unif = self.clone();
                                new_unif.eqs.push((xs[0].clone(), AST::Int(p.clone())));
                                new_unif.eqs.push((xs[1].clone(), AST::Int(n.clone() / p)));
                                unifs.push(new_unif);
                            }
                            // We say failed because we actually transferred all the other
                            // possibilities to the other unifications we created above.
                            return UnificationStatus::Failed;
                        } else if *f == AST::Var("$power".to_string()) {
                            if n == One::one() {
                                self.eqs.push((xs[1].clone(), AST::Int(Zero::zero())));
                                return UnificationStatus::Running;
                            } else {
                                return UnificationStatus::Failed;
                            }
                        } else {
                            return UnificationStatus::Failed;
                        }
                    }

                    (AST::App(f, xs), AST::Bin(Op::Mul, a, b)) => {
                        if *f == AST::Var("$coeff".to_string()) {
                            self.eqs.push((xs[0].clone(), *a));
                            self.eqs.push((xs[1].clone(), *b));
                            return UnificationStatus::Running;
                        } else {
                            return UnificationStatus::Failed;
                        }
                    }

                    (AST::App(f, xs), AST::FinSet(elems)) => {
                        if *f == AST::Var("$elem".to_string()) {
                            for (i, e) in elems.iter().enumerate() {
                                let mut new_unif = self.clone();
                                new_unif.eqs.push((xs[0].clone(), e.clone()));

                                let other_elems = elems.iter().enumerate().filter(|(j,_)| i != *j).map(|(_,t)| t).cloned().collect();
                                new_unif.eqs.push((xs[1].clone(), AST::FinSet(other_elems)));

                                unifs.push(new_unif);
                            }
                            // This unification "failed", but we generated new unifications for each of
                            // the elements of the set.
                            return UnificationStatus::Failed;
                        } else if *f == AST::Var("$union".to_string()) {
                            // TODO: Should allow matching all possible partitions of the set into
                            // two nonempty subsets.
                            unreachable!();
                        }

                        return UnificationStatus::Failed;
                    }

                    (AST::App(f, xs), AST::App(g, ys)) => {
                        self.eqs.push((*f, *g));
                        for (x, y) in xs.into_iter().zip(ys) {
                            self.eqs.push((x, y));
                        }
                        return UnificationStatus::Running;
                    }

                    (AST::IfThenElse(c1, t1, e1), AST::IfThenElse(c2, t2, e2)) => {
                        self.eqs.push((*c1, *c2));
                        self.eqs.push((*t1, *t2));
                        self.eqs.push((*e1, *e2));
                        return UnificationStatus::Running;
                    }

                    (AST::Factorial(a), AST::Factorial(b)) => {
                        self.eqs.push((*a, *b));
                        return UnificationStatus::Running;
                    }

                    (AST::Sum(a), AST::Sum(b)) => {
                        self.eqs.push((*a, *b));
                        return UnificationStatus::Running;
                    }

                    (AST::Complement(a), AST::Complement(b)) => {
                        self.eqs.push((*a, *b));
                        return UnificationStatus::Running;
                    }

                    (AST::Negate(a), AST::Negate(b)) => {
                        self.eqs.push((*a, *b));
                        return UnificationStatus::Running;
                    }

                    (AST::RangeSet(s1, e1, st1), AST::RangeSet(s2, e2, st2)) => {
                        self.eqs.push((*s1, *s2));
                        self.eqs.push((*e1, *e2));
                        self.eqs.push((*st1, *st2));
                        return UnificationStatus::Running;
                    }

                    // TODO: This doesn't handle scope right.
                    (AST::CompSet(vs1, cls1), AST::CompSet(vs2, cls2)) => {
                        for ((x1, dom1), (x2, dom2)) in vs1.into_iter().zip(vs2) {
                            self.eqs.push((AST::Var(x1), AST::Var(x2)));
                            self.eqs.push((dom1, dom2));
                        }

                        for (c1, c2) in cls1.into_iter().zip(cls2) {
                            self.eqs.push((c1, c2));
                        }

                        return UnificationStatus::Running;
                    }

                    (_, _) => {
                        return UnificationStatus::Failed;
                    }
                }
            }
        }
    }
}

struct UnificationIterator {
    unifs : Vec<Unification>
}

impl UnificationIterator {
    fn new(lhs : AST, rhs : AST) -> UnificationIterator {
        return UnificationIterator {
            unifs: vec!(Unification::new(lhs, rhs))
        };
    }
}

impl Iterator for UnificationIterator {
    type Item = HashMap<String, AST>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.unifs.pop() {
                None => return None,
                Some(unification) => {
                    let mut u = unification;

                    match u.step(&mut self.unifs) {
                        UnificationStatus::Failed => continue,
                        UnificationStatus::Done => return Some(u.subs),
                        UnificationStatus::Running => self.unifs.push(u),
                    }
                }
            }
        }
    }
}

struct Positions {
    pos_queue : VecDeque<(AST, Vec<usize>)>
}

fn concat_pos(pos : Vec<usize>, i : usize) -> Vec<usize> {
    let mut new_pos = pos;
    new_pos.push(i);
    return new_pos;
}

impl Iterator for Positions {
    type Item = Vec<usize>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.pos_queue.pop_front() {
            None => return None,
            Some((expr, pos)) => {
                match expr {
                    AST::Skip() => (),
                    AST::Int(_) => (),
                    AST::Var(_) => (),
                    AST::Seq(_, _) => (),

                    AST::Assumption(t) => self.pos_queue.push_back((*t, concat_pos(pos.clone(), 0))),
                    AST::Prove(t) => self.pos_queue.push_back((*t, concat_pos(pos.clone(), 0))),

                    AST::FinSet(elems) => {
                        for (i, e) in elems.into_iter().enumerate() {
                            self.pos_queue.push_back((e, concat_pos(pos.clone(), i)));
                        }
                    }

                    AST::List(elems) => {
                        for (i, e) in elems.into_iter().enumerate() {
                            self.pos_queue.push_back((e, concat_pos(pos.clone(), i)));
                        }
                    }

                    AST::Memo(_, _, body, _) => self.pos_queue.push_back((*body, concat_pos(pos.clone(), 0))),
                    AST::Function(_, _, body) => self.pos_queue.push_back((*body, concat_pos(pos.clone(), 0))),

                    AST::App(func, xs) => {
                        self.pos_queue.push_back((*func, concat_pos(pos.clone(), 0)));
                        for (i, x) in xs.into_iter().enumerate() {
                            self.pos_queue.push_back((x, concat_pos(pos.clone(), i + 1)));
                        }
                    }

                    AST::RangeSet(start, end, step) => {
                        self.pos_queue.push_back((*start, concat_pos(pos.clone(), 0)));
                        self.pos_queue.push_back((*end, concat_pos(pos.clone(), 1)));
                        self.pos_queue.push_back((*step, concat_pos(pos.clone(), 2)));
                    }

                    AST::IfThenElse(cond, then_expr, else_expr) => {
                        self.pos_queue.push_back((*cond, concat_pos(pos.clone(), 0)));
                        self.pos_queue.push_back((*then_expr, concat_pos(pos.clone(), 1)));
                        self.pos_queue.push_back((*else_expr, concat_pos(pos.clone(), 2)));
                    }

                    AST::CompSet(var_doms, clauses) => {
                        let n = var_doms.len();
                        for (i, (_, dom)) in var_doms.into_iter().enumerate() {
                            self.pos_queue.push_back((dom, concat_pos(pos.clone(), i)));
                        }
                        for (i, clause) in clauses.into_iter().enumerate() {
                            self.pos_queue.push_back((clause, concat_pos(pos.clone(), n + i)));
                        }
                    }

                    AST::Bin(_, a, b) => {
                        self.pos_queue.push_back((*a, concat_pos(pos.clone(), 0)));
                        self.pos_queue.push_back((*b, concat_pos(pos.clone(), 1)));
                    }

                    AST::Image(a, b) => {
                        self.pos_queue.push_back((*a, concat_pos(pos.clone(), 0)));
                        self.pos_queue.push_back((*b, concat_pos(pos.clone(), 1)));
                    }

                    AST::Complement(a) => self.pos_queue.push_back((*a, concat_pos(pos.clone(), 0))),
                    AST::Sum(a) => self.pos_queue.push_back((*a, concat_pos(pos.clone(), 0))),
                    AST::Negate(a) => self.pos_queue.push_back((*a, concat_pos(pos.clone(), 0))),
                    AST::Factorial(a) => self.pos_queue.push_back((*a, concat_pos(pos.clone(), 0))),

                    AST::Definition(_, body) => self.pos_queue.push_back((*body, concat_pos(pos.clone(), 0))),

                    AST::Rule(_, lhs, rhs) => {
                        self.pos_queue.push_back((*lhs, concat_pos(pos.clone(), 0)));
                        self.pos_queue.push_back((*rhs, concat_pos(pos.clone(), 1)));
                    }
                }

                return Some(pos);
            }
        }
    }
}

fn map<'a, F>(expr : &'a AST, pos : Vec<usize>, i : usize, f : F) -> Box<dyn Iterator<Item=AST> + 'a> where F : Fn(AST) -> Box<dyn Iterator<Item=AST> + 'a> {
    if i >= pos.len() {
        return f(expr.clone());
    }
    let idx = pos[i];
    match expr {
        AST::Skip() => Box::new(std::iter::empty()),
        AST::Int(_) => Box::new(std::iter::empty()),
        AST::Var(_) => Box::new(std::iter::empty()),
        AST::Seq(_, _) => Box::new(std::iter::empty()),

        AST::Assumption(t) => Box::new(map(t, pos, i + 1, f).map(|t| AST::Assumption(Box::new(t)))),
        AST::Prove(t) => Box::new(map(t, pos, i + 1, f).map(|t| AST::Prove(Box::new(t)))),

        AST::FinSet(elems) =>
            Box::new(map(&elems[idx], pos, i + 1, f).map(move |t| {
                let mut new_elems = elems.clone();
                new_elems[idx] = t;
                return AST::FinSet(new_elems);
            })),

        AST::List(elems) =>
            Box::new(map(&elems[idx], pos, i + 1, f).map(move |t| {
                let mut new_elems = elems.clone();
                new_elems[idx] = t;
                return AST::FinSet(new_elems);
            })),

        AST::Memo(name, args, body, memo) =>
            Box::new(map(body, pos, i + 1, f).map(move |t| AST::Memo(name.clone(), args.clone(), Box::new(t), memo.clone()))),
        AST::Function(name, args, body) =>
            Box::new(map(body, pos, i + 1, f).map(move |t| AST::Function(name.clone(), args.clone(), Box::new(t)))),

        AST::App(func, xs) => {
            if idx == 0 {
                return Box::new(map(func, pos, i + 1, f).map(move |t| AST::App(Box::new(t), xs.clone())));
            } else {
                let xs_idx = idx - 1;
                return Box::new(map(&xs[xs_idx], pos, i + 1, f).map(move |t| {
                    let mut new_xs = xs.clone();
                    new_xs[xs_idx] = t;
                    return AST::App(func.clone(), new_xs);
                }));
            }
        }

        AST::RangeSet(start, end, step) => {
            if idx == 0 {
                return Box::new(map(start, pos, i + 1, f).map(move |t| AST::RangeSet(Box::new(t), end.clone(), step.clone())));
            } else if idx == 1 {
                return Box::new(map(end, pos, i + 1, f).map(move |t| AST::RangeSet(start.clone(), Box::new(t), step.clone())));
            } else {
                return Box::new(map(step, pos, i + 1, f).map(move |t| AST::RangeSet(start.clone(), end.clone(), Box::new(t))));
            }
        }

        AST::IfThenElse(cond, then_expr, else_expr) => {
            if idx == 0 {
                return Box::new(map(cond, pos, i + 1, f).map(move |t| AST::IfThenElse(Box::new(t), then_expr.clone(), else_expr.clone())));
            } else if idx == 1 {
                return Box::new(map(then_expr, pos, i + 1, f).map(move |t| AST::IfThenElse(cond.clone(), Box::new(t), else_expr.clone())));
            } else {
                return Box::new(map(else_expr, pos, i + 1, f).map(move |t| AST::IfThenElse(cond.clone(), then_expr.clone(), Box::new(t))));
            }
        }

        AST::CompSet(var_doms, clauses) => {
            if idx < var_doms.len() {
                return Box::new(map(&var_doms[idx].1, pos, i + 1, f).map(move |t| {
                    let mut new_var_doms = var_doms.clone();
                    new_var_doms[idx] = (new_var_doms[idx].0.clone(), t);
                    return AST::CompSet(new_var_doms, clauses.clone());
                }));
            } else {
                let clause_idx = idx - var_doms.len();
                return Box::new(map(&clauses[clause_idx], pos, i + 1, f).map(move |t| {
                    let mut new_clauses = clauses.clone();
                    new_clauses[clause_idx] = t;
                    return AST::CompSet(var_doms.clone(), new_clauses);
                }));
            }
        }

        AST::Bin(op, a, b) => {
            if idx == 0 {
                return Box::new(map(a, pos, i + 1, f).map(move |t| AST::Bin(*op, Box::new(t), b.clone())));
            } else {
                return Box::new(map(b, pos, i + 1, f).map(move |t| AST::Bin(*op, a.clone(), Box::new(t))));
            }
        }

        AST::Image(a, b) => {
            if idx == 0 {
                return Box::new(map(a, pos, i + 1, f).map(move |t| AST::Image(Box::new(t), b.clone())));
            } else {
                return Box::new(map(b, pos, i + 1, f).map(move |t| AST::Image(a.clone(), Box::new(t))));
            }
        }

        AST::Complement(a) => Box::new(map(a, pos, i + 1, f).map(|t| AST::Complement(Box::new(t)))),
        AST::Sum(a) => Box::new(map(a, pos, i + 1, f).map(|t| AST::Sum(Box::new(t)))),
        AST::Negate(a) => Box::new(map(a, pos, i + 1, f).map(|t| AST::Negate(Box::new(t)))),
        AST::Factorial(a) => Box::new(map(a, pos, i + 1, f).map(|t| AST::Factorial(Box::new(t)))),

        AST::Definition(name, body) => Box::new(map(body, pos, i + 1, f).map(move |t| AST::Definition(name.clone(), Box::new(t)))),

        AST::Rule(attrs, lhs, rhs) => {
            if idx == 0 {
                return Box::new(map(lhs, pos, i + 1, f).map(move |t| AST::Rule(attrs.clone(), Box::new(t), rhs.clone())));
            } else {
                return Box::new(map(rhs, pos, i + 1, f).map(move |t| AST::Rule(attrs.clone(), lhs.clone(), Box::new(t))));
            }
        }
    }
}

impl AST {
    fn positions(&self) -> Positions {
        let mut pos_queue = VecDeque::new();
        pos_queue.push_back((self.clone(), vec!()));
        return Positions { pos_queue: pos_queue };
    }
}

fn rewrite_with<'a>(lhs : &'a AST, rhs : &'a AST, expr : &'a AST) -> Box<dyn Iterator<Item=AST> + 'a> {
    return Box::new(expr.positions().flat_map(move |pos| {
        return map(expr, pos, 0, move |t| {
            let f = move |to_subs| subs(rhs.clone(), &to_subs);
            return Box::new(UnificationIterator::new(lhs.clone(), t).map(f));
        });
    }));
}

fn single_rewrite<'a>(rules : &'a [AST], expr : &'a AST) -> Box<dyn Iterator<Item=AST> + 'a> {
    return Box::new(rules.iter().flat_map(move |rule| match rule {
        AST::Rule(_, lhs, rhs) => rewrite_with(lhs, rhs, expr),
        _ => Box::new(std::iter::empty()),
    }));
}

pub fn simplify_tree(expr : AST) -> AST {
    // println!("e: {:?}, pos: {:?}", expr, expr.positions().collect::<Vec<Vec<usize>>>());
    for pos in expr.positions() {
        for new_expr in map(&expr, pos, 0, |t| Box::new(std::iter::once(simplify(t)))) {
            if new_expr != expr {
                return new_expr;
            }
        }
    }
    return expr;
}

pub fn simplify(expr : AST) -> AST {
    match expr {
        AST::Bin(Op::Add, box AST::Int(n), box AST::Int(m)) => AST::Int(n + m),
        AST::Bin(Op::Add, box AST::Int(n), b) =>
            if n == Zero::zero() {
                *b
            } else {
                AST::Bin(Op::Add, Box::new(AST::Int(n)), b)
            }
        AST::Bin(Op::Add, a, box AST::Int(m)) =>
            if m == Zero::zero() {
                *a
            } else {
                AST::Bin(Op::Add, a, Box::new(AST::Int(m)))
            }

        AST::Bin(Op::Sub, box AST::Int(n), box AST::Int(m)) => AST::Int(n - m),

        AST::Bin(Op::Mul, box AST::Int(n), box AST::Int(m)) => AST::Int(n * m),
        AST::Bin(Op::Mul, box AST::Int(n), b) =>
            if n == Zero::zero() {
                AST::Int(Zero::zero())
            } else if n == One::one() {
                *b
            } else {
                AST::Bin(Op::Mul, Box::new(AST::Int(n)), b)
            }
        AST::Bin(Op::Mul, a, box AST::Int(m)) =>
            if m == Zero::zero() {
                AST::Int(Zero::zero())
            } else if m == One::one() {
                *a
            } else {
                AST::Bin(Op::Mul, a, Box::new(AST::Int(m)))
            }

        AST::Bin(Op::And, box AST::Int(n), b) =>
            if n == Zero::zero() {
                AST::Int(Zero::zero())
            } else if n == One::one() {
                *b
            } else {
                AST::Bin(Op::And, Box::new(AST::Int(n)), b)
            }
        AST::Bin(Op::And, a, box AST::Int(m)) =>
            if m == Zero::zero() {
                AST::Int(Zero::zero())
            } else if m == One::one() {
                *a
            } else {
                AST::Bin(Op::And, a, Box::new(AST::Int(m)))
            }

        AST::Bin(Op::Or, box AST::Int(n), b) =>
            if n == Zero::zero() {
                *b
            } else if n == One::one() {
                AST::Int(One::one())
            } else {
                AST::Bin(Op::Or, Box::new(AST::Int(n)), b)
            }
        AST::Bin(Op::Or, a, box AST::Int(m)) =>
            if m == Zero::zero() {
                *a
            } else if m == One::one() {
                AST::Int(One::one())
            } else {
                AST::Bin(Op::Or, a, Box::new(AST::Int(m)))
            }

        AST::Bin(Op::Div, box AST::Int(n), box AST::Int(m)) => AST::Int(n / m),

        AST::Bin(Op::Mod, box AST::Int(n), box AST::Int(m)) => AST::Int(n % m),
        AST::Bin(Op::Mod, box AST::Bin(Op::Mod, a, b), c) =>
            if b == c {
                AST::Bin(Op::Mod, a, b)
            } else {
                AST::Bin(Op::Mod, Box::new(AST::Bin(Op::Mod, a, b)), c)
            }

        AST::Bin(Op::Exp, box AST::Int(n), box AST::Int(m)) => match m.to_biguint() {
                Some(b) => AST::Int(Pow::pow(n, b)),
                None => AST::Bin(Op::Exp, Box::new(AST::Int(n)), Box::new(AST::Int(m)))
            }

        AST::Bin(Op::Prove, box AST::FinSet(assms), p) =>
            if assms.len() == 0 {
                *p
            } else {
                AST::Bin(Op::Prove, Box::new(AST::FinSet(assms)), p)
            }

        AST::Bin(Op::Equals, box AST::Int(n), box AST::Int(m)) => AST::Int(if n == m { One::one() } else { Zero::zero() }),
        AST::Bin(Op::Equals, a, b) =>
            if a == b {
                AST::Int(One::one())
            } else {
                AST::Bin(Op::Equals, a, b)
            }

        AST::App(f, xs) => {
            if *f == AST::Var("subs".to_string()) {
                match &xs[..] {
                    [e, rep, pat] => {
                        return subs_expr(e.clone(), rep, pat);
                    }
                    _ => AST::App(f, xs)
                }
            } else if *f == AST::Var("∪".to_string()) {
                let mut ys = xs;
                match (ys.pop(), ys.pop()) {
                    (Some(AST::FinSet(ref mut es1)), Some(AST::FinSet(ref mut es2))) => {
                        es1.append(es2);
                        return AST::FinSet(es1.to_vec());
                    }
                    (y1, y2) => {
                        ys.extend(y2.into_iter());
                        ys.extend(y1.into_iter());
                        return AST::App(f, ys)
                    }
                }
            } else {
                AST::App(f, xs)
            }
        }

        other => other
    }
}

struct TerminatingRewriter<'a> {
    rules : &'a [AST],
    exprs : Vec<AST>
}

impl <'a> TerminatingRewriter<'a> {
    fn new(rules : &'a [AST], expr : AST) -> TerminatingRewriter<'a> {
        return TerminatingRewriter {
            rules: rules,
            exprs: vec!(expr)
        };
    }
}

fn full_simplify(expr : AST) -> AST {
    let mut res = expr;
    loop {
        let old_res = res.clone();
        res = simplify_tree(res);
        if res == old_res {
            break;
        }
    }
    return res;
}

impl <'a> Iterator for TerminatingRewriter<'a> {
    type Item = AST;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.exprs.pop() {
                None => return None,

                Some(expr) => {
                    let mut changed = false;
                    for new_expr in single_rewrite(self.rules, &expr) {
                        if new_expr != expr {
                            self.exprs.push(full_simplify(new_expr));
                            changed = true;
                        }
                    }
                    if !changed {
                        return Some(expr);
                    }
                }
            }
        }
    }
}

pub fn now_millis() -> u128 {
    let start = SystemTime::now();
    return start.duration_since(UNIX_EPOCH)
        .expect("Time went backwards")
        .as_millis();
}

struct Nat {
    n : BigInt
}
impl Iterator for Nat {
    type Item = BigInt;

    fn next(&mut self) -> Option<Self::Item> {
        let v = self.n.clone();
        self.n += 1;
        return Some(v);
    }
}

fn nat() -> Nat {
    return Nat { n : Zero::zero() };
}

struct Assignments {
    vars : Vec<String>,
    items : VecDeque<HashMap<String, AST>>,
    found_vals : HashMap<String, Vec<AST>>,
    var_its : HashMap<String, Box<dyn Iterator<Item=AST>>>,
    cur_idx : usize,
    done: bool
}

impl Assignments {
    fn new(vars : Vec<String>) -> Assignments {
        let mut found_vals = HashMap::new();
        let mut var_its : HashMap<String, Box<dyn Iterator<Item=AST>>> = HashMap::new();
        // TODO: Eventually not all variables will be natural numbers...
        for x in &vars {
            found_vals.insert(x.clone(), vec!());
            var_its.insert(x.clone(), Box::new(nat().map(|n| AST::Int(n))));
        }
        return Assignments {
            vars: vars,
            items: VecDeque::new(),
            found_vals: found_vals,
            var_its: var_its,
            cur_idx: 0,
            done: false
        };
    }

    fn gen_product(&self, xi : usize, e : &AST, i : usize) -> Box<dyn Iterator<Item=HashMap<String, AST>>> {
        if i == xi {
            let mut a = HashMap::new();
            a.insert(self.vars[xi].clone(), e.clone());
            return Box::new(std::iter::once(a));
        }

        let x = self.vars[i].clone();
        let vals = self.found_vals[&self.vars[i]].clone();
        return Box::new(self.gen_product(xi, e, (i + 1) % self.vars.len()).flat_map(move |a| {
            let x2 = x.clone();
            return vals.clone().into_iter().map(move |vi| {
                let mut b = a.clone();
                b.insert(x2.clone(), vi);
                return b;
            })
        }));
    }
}

impl Iterator for Assignments {
    type Item = HashMap<String, AST>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        // See if there's any items left in the queue to pop
        match self.items.pop_front() {
            None => (),
            Some(a) => return Some(a)
        }

        let orig_idx = self.cur_idx;
        loop {
            let x = self.vars[self.cur_idx].clone();
            match (*self.var_its.entry(x.clone()).or_insert_with(|| Box::new(std::iter::empty()))).next() {
                None => (), // continue and increment to the next to get a new item
                Some(e) => {
                    // Generate new items for the queue
                    self.items.extend(self.gen_product(self.cur_idx, &e, (self.cur_idx + 1) % self.vars.len()));
                    (*self.found_vals.entry(x).or_insert(vec!())).push(e.clone());
                    self.cur_idx = (self.cur_idx + 1) % self.var_its.len();
                    return self.next();
                }
            }
            self.cur_idx = (self.cur_idx + 1) % self.var_its.len();
            if self.cur_idx == orig_idx {
                self.done = true;
                return None;
            }
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let contents = fs::read_to_string(&args[1])
        .expect("Something went wrong reading the file");

    let parse_start = now_millis();
    let parsed = parse(&contents);
    let parse_end = now_millis();
    println!("Parse time: {}ms", parse_end - parse_start);

    match parsed {
        Ok(exprs) => {
            let mut defs = HashMap::new();
            defs.insert("p".to_string(), AST::Seq("primes".to_string(), Rc::new(RefCell::new(PrimeSeq::new()))));

            let mut rules = Vec::new();
            let mut proof_rules = Vec::new();

            let mut assumptions = Vec::new();

            for expr in exprs {
                // println!("{:?}", defs.clone());
                match expr.clone() {
                    AST::Skip() => continue,
                    other => println!("> {}.", other)
                }

                match expr {
                    AST::Definition(name, body) => {
                        match *body {
                            AST::Function(_, args, func_body) => {
                                defs.insert(name.clone(), subs(AST::Function(Some(name), args, func_body), &defs));
                            }

                            other => {
                                defs.insert(name, subs(other, &defs));
                            }
                        }
                    }

                    AST::Assumption(t) => assumptions.push(*t),

                    AST::Prove(t) => {
                        let to_prove = subs(AST::Bin(Op::Prove, Box::new(AST::FinSet(assumptions.clone())), t), &defs);
                        let mut proof_tree = HashMap::new();
                        let mut todo = VecDeque::new();
                        proof_tree.insert(to_prove.clone(), None);
                        todo.push_back(subs(to_prove.clone(), &defs));

                        let mut assignment_it = Assignments::new(vars(&to_prove).into_iter().collect());

                        let expr_start = now_millis();
                        loop {
                            match assignment_it.next() {
                                Some(a) => {
                                    print!("... Trying: {:?}", a);
                                    match eval(subs(to_prove.clone(), &a)) {
                                        Ok(AST::Int(n)) => {
                                            if n == Zero::zero() {
                                                println!("\nFound counterexample: {:?}", a);
                                                break;
                                            }
                                        }

                                        _ => ()
                                    }
                                }
                                None => ()
                            }

                            match todo.pop_front() {
                                None => {
                                    println!("\nFailure!");
                                    break;
                                }

                                Some(new_t) => {
                                    if new_t == AST::Int(One::one()) {
                                        println!("\nFound proof:");
                                        let mut cur_term = Some(new_t);
                                        while cur_term != None {
                                            println!("{}", cur_term.as_ref().unwrap());
                                            cur_term = proof_tree[&cur_term.unwrap()].clone();
                                        }
                                        break;
                                    }

                                    // println!("\n{} tried, {} left: {}", proof_tree.len() - todo.len(), todo.len(), new_t);
                                    print!("\r{} tried, {} left", proof_tree.len() - todo.len(), todo.len());

                                    for new_expr in single_rewrite(&proof_rules, &new_t).map(full_simplify) {
                                        if !proof_tree.contains_key(&new_expr) {
                                            proof_tree.insert(new_expr.clone(), Some(new_t.clone()));
                                            todo.push_back(new_expr);
                                        }
                                    }
                                }
                            }
                        }
                        let expr_end = now_millis();
                        println!("Elapsed: {}ms", expr_end - expr_start);
                    }

                    AST::Rule(attrs, lhs, rhs) => {
                        let mut to_subs = HashMap::new();
                        for x in vars(&lhs) {
                            if !x.starts_with('$') && x.chars().next().unwrap().is_alphabetic() {
                                unsafe {
                                    fresh_counter += 1;
                                    to_subs.insert(x.clone(), AST::Var(format!("v_{}", fresh_counter)));
                                }
                            }
                        }
                        let fresh_rule = AST::Rule(attrs.clone(), Box::new(subs(*lhs, &to_subs)),
                                                                  Box::new(subs(*rhs, &to_subs)));
                        if !attrs.contains(&"proof rule".to_string()) {
                            rules.push(fresh_rule.clone());
                        }
                        proof_rules.push(fresh_rule);
                    }

                    _ => {
                        let expr_start = now_millis();
                        // println!("{:?}", eval(subs(expr, &defs)));
                        let mut exprs = HashSet::new();
                        for res in TerminatingRewriter::new(&rules, subs(expr, &defs)) {
                            if !exprs.contains(&res) {
                                println!("{:?}", res.clone());
                                exprs.insert(res);
                            }
                        }
                        let expr_end = now_millis();
                        println!("Elapsed: {}ms", expr_end - expr_start);
                    }
                }
            }
        }
        Err(err) => println!("Error: {}", err)
    }
}


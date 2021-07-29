#![feature(int_log)]
#![feature(box_patterns)]

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
use std::cmp::max;
use std::env;
use std::fs;
use std::fmt::Debug;
use std::hash::Hash;
use std::iter::Iterator;
use std::time::{SystemTime, UNIX_EPOCH};
use std::rc::Rc;

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
}

impl Sequence for PrimeSeq {
    fn nth(&mut self, n : usize) -> Result<AST, String> {
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

        return Ok(AST::Int(self.primes[n].clone()));
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
            if self.primes[guess] < n {
                min_idx = guess;
            } else if self.primes[guess] > n {
                max_idx = guess;
            } else {
                return Some(guess);
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
    Imp
}

#[derive(Clone, Educe)]
#[educe(Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum AST {
    Skip(),

    Definition(String, Box<AST>),
    Rule(Vec<String>, Box<AST>, Box<AST>),

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

        Rule::compare => {
            let mut it = pair.into_inner();
            let lhs = primary(it.next().unwrap())?;
            let op = primary(it.next().unwrap())?;
            let rhs = primary(it.next().unwrap())?;

            let op_str = match op {
                AST::Var(s) => Ok(s),
                _ => Err(format!("Unknown operator {:?} in compare operation", op))
            }?;

            return match op_str.as_str() {
                "<" => Ok(AST::Bin(Op::Lt, Box::new(lhs), Box::new(rhs))),
                "<=" => Ok(AST::Bin(Op::Le, Box::new(lhs), Box::new(rhs))),
                ">" => Ok(AST::Bin(Op::Gt, Box::new(lhs), Box::new(rhs))),
                ">=" => Ok(AST::Bin(Op::Ge, Box::new(lhs), Box::new(rhs))),
                "=" => Ok(AST::Bin(Op::Equals, Box::new(lhs), Box::new(rhs))),
                "!=" => Ok(AST::Bin(Op::NotEquals, Box::new(lhs), Box::new(rhs))),
                s => Err(format!("Unknown operator {:?} in compare operation", s))
            };
        }

        Rule::lt_sym => Ok(AST::Var("<".to_string())),
        Rule::le_sym => Ok(AST::Var("<=".to_string())),
        Rule::gt_sym => Ok(AST::Var(">".to_string())),
        Rule::ge_sym => Ok(AST::Var(">=".to_string())),
        Rule::eq_sym => Ok(AST::Var("=".to_string())),
        Rule::ne_sym => Ok(AST::Var("!=".to_string())),

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

            return Ok(bool_climber.climb(pair.into_inner(), primary, infix)?);
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

            return Ok(arith_climber.climb(pair.into_inner(), primary, infix)?);
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
            Operator::new(Rule::elem, Assoc::Left),
            Operator::new(Rule::and_op, Assoc::Left),
            Operator::new(Rule::or_op, Assoc::Left)));

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

pub fn subs(expr : AST, to_subs : &HashMap<String, AST>) -> AST {
    match expr {
        AST::Definition(name, body) => AST::Definition(name, Box::new(subs(*body, to_subs))),
        AST::Rule(attrs, lhs, rhs) => AST::Rule(attrs, Box::new(subs(*lhs, to_subs)),
                                                       Box::new(subs(*rhs, to_subs))),

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
                new_subs.remove(&x);
                new_var_doms.push((x, subs(dom, &new_subs)));
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

        AST::App(f, args) => AST::App(Box::new(subs(*f, to_subs)),
                                      args.into_iter().map(| e | subs(e, to_subs)).collect()),

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
                var_doms : &Vec<(String, AST)>) -> AST {
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

            if aval.clone() % bval.clone() == Zero::zero() {
                return Ok(AST::Int(aval / bval));
            } else {
                return Err(format!("Cannot do {} / {} (rational numbers not implemented)", aval, bval));
            }
        }

        AST::Bin(Op::Mod, a, b) => {
            return Ok(AST::Int(as_int(eval(*a)?)? % as_int(eval(*b)?)?));
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
                    match name {
                        Some(ref f_name) => {
                            to_subs.insert(f_name.clone(), AST::Function(name.clone(), formal_args.clone(), body.clone()));
                        }
                        None => {}
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
                    match name {
                        Some(ref f_name) => {
                            to_subs.insert(f_name.clone(), AST::Memo(name.clone(), formal_args.clone(), body.clone(), memo.clone()));
                        }
                        None => {}
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

        AST::Var(x) => vec!(x.clone()).into_iter().collect(),
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
            let arg_vars : HashSet<String> = args.into_iter().map(|x| x.clone()).collect();
            return diff(vars(body), &arg_vars);
        }

        AST::Memo(_, args, body, _) => {
            let arg_vars : HashSet<String> = args.into_iter().map(|x| x.clone()).collect();
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
                        if x.starts_with("$") {
                            let name = x[1..].to_string();
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

                    (AST::App(f, xs), AST::App(g, ys)) => {
                        if f != g {
                            return UnificationStatus::Failed;
                        } else {
                            for (x, y) in xs.into_iter().zip(ys) {
                                self.eqs.push((x, y));
                            }
                            return UnificationStatus::Running;
                        }
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

struct ASTMapper {
    expr : AST,
    cur_pos : usize,
    running : Box<dyn Iterator<Item = AST>>,
    f : Box<dyn Fn(&AST) -> Box<dyn Iterator<Item=AST>>>,
    con : Box<dyn Fn(AST) -> AST>
}

impl ASTMapper {
    fn new(expr : AST, f : Box<dyn Fn(&AST) -> Box<dyn Iterator<Item=AST>>>) -> ASTMapper {
        let running = f(&expr);
        return ASTMapper {
            expr: expr,
            cur_pos: 0,
            running: running,
            f: f,
            con: Box::new(|x| x),
        };
    }
}

impl Iterator for ASTMapper {
    type Item = AST;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            loop {
                match self.running.next() {
                    None => {
                        self.cur_pos += 1;
                        break;
                    }

                    Some(t) => return Some((self.con)(t)),
                }
            }

            if self.cur_pos == 0 {
                self.running = (self.f)(&self.expr);
                self.cur_pos += 1;
                continue;
            }

            match self.expr.clone() {
                AST::Skip() => return None,
                AST::Int(_) => return None,
                AST::Var(_) => return None,

                AST::Seq(_, _) => return None,

                AST::FinSet(elems) => {
                    if self.cur_pos > elems.len() {
                        return None;
                    }

                    let idx = self.cur_pos - 1;
                    self.running = (self.f)(&elems[idx]);
                    self.con = Box::new(move |x| {
                        let mut new_elems = elems.clone();
                        new_elems[idx] = x;
                        return AST::FinSet(new_elems);
                    });
                }

                AST::Memo(name, args, body, memo) => {
                    if self.cur_pos == 1 {
                        self.running = (self.f)(&body);
                        self.con = Box::new(move |x| AST::Memo(name.clone(), args.clone(), Box::new(x), memo.clone()));
                    } else {
                        return None;
                    }
                }

                AST::Function(name, args, body) => {
                    if self.cur_pos == 1 {
                        self.running = (self.f)(&body);
                        self.con = Box::new(move |x| AST::Function(name.clone(), args.clone(), Box::new(x)));
                    } else {
                        return None;
                    }
                }

                AST::List(elems) => {
                    if self.cur_pos > elems.len() {
                        return None;
                    }

                    let idx = self.cur_pos - 1;
                    self.running = (self.f)(&elems[idx]);
                    self.con = Box::new(move |x| {
                        let mut new_elems = elems.clone();
                        new_elems[idx] = x;
                        return AST::FinSet(new_elems);
                    });
                }

                AST::App(f, xs) => {
                    if self.cur_pos > xs.len() + 1 {
                        return None;
                    }

                    if self.cur_pos == 1 {
                        self.running = (self.f)(&f);
                        self.con = Box::new(move |x| AST::App(Box::new(x), xs.clone()));
                    } else {
                        let idx = self.cur_pos - 2;
                        self.running = (self.f)(&xs[idx]);
                        self.con = Box::new(move |x| {
                            let mut new_xs = xs.clone();
                            new_xs[idx] = x;
                            return AST::App(f.clone(), new_xs);
                        });
                    }
                }

                AST::RangeSet(start, end, step) => {
                    if self.cur_pos == 1 {
                        self.running = (self.f)(&start);
                        self.con = Box::new(move |x| AST::RangeSet(Box::new(x), end.clone(), step.clone()));
                    } else if self.cur_pos == 2 {
                        self.running = (self.f)(&end);
                        self.con = Box::new(move |x| AST::RangeSet(start.clone(), Box::new(x), step.clone()));
                    } else if self.cur_pos == 3 {
                        self.running = (self.f)(&step);
                        self.con = Box::new(move |x| AST::RangeSet(start.clone(), end.clone(), Box::new(x)));
                    } else {
                        return None;
                    }
                }

                AST::IfThenElse(cond, then_expr, else_expr) => {
                    if self.cur_pos == 1 {
                        self.running = (self.f)(&cond);
                        self.con = Box::new(move |x| AST::IfThenElse(Box::new(x), then_expr.clone(), else_expr.clone()));
                    } else if self.cur_pos == 2 {
                        self.running = (self.f)(&then_expr);
                        self.con = Box::new(move |x| AST::IfThenElse(cond.clone(), Box::new(x), else_expr.clone()));
                    } else if self.cur_pos == 3 {
                        self.running = (self.f)(&else_expr);
                        self.con = Box::new(move |x| AST::IfThenElse(cond.clone(), then_expr.clone(), Box::new(x)));
                    } else {
                        return None;
                    }
                }

                AST::CompSet(var_doms, clauses) => {
                    if self.cur_pos > var_doms.len() + clauses.len() {
                        return None;
                    }

                    let mut idx = self.cur_pos - 1;

                    if idx < var_doms.len() {
                        self.running = (self.f)(&var_doms[idx].1);
                        self.con = Box::new(move |x| {
                            let mut new_var_doms = var_doms.clone();
                            new_var_doms[idx] = (var_doms[idx].0.clone(), x);
                            return AST::CompSet(new_var_doms, clauses.clone());
                        });
                    } else {
                        idx -= var_doms.len();
                        self.running = (self.f)(&clauses[idx]);
                        self.con = Box::new(move |x| {
                            let mut new_clauses = clauses.clone();
                            new_clauses[idx] = x;
                            return AST::CompSet(var_doms.clone(), new_clauses);
                        });
                    }
                }

                AST::Bin(op, a, b) => {
                    if self.cur_pos == 1 {
                        self.running = (self.f)(&a);
                        self.con = Box::new(move |x| AST::Bin(op, Box::new(x), b.clone()));
                    } else if self.cur_pos == 2 {
                        self.running = (self.f)(&b);
                        self.con = Box::new(move |x| AST::Bin(op, a.clone(), Box::new(x)));
                    } else {
                        return None;
                    }
                }


                AST::Image(a, b) => {
                    if self.cur_pos == 1 {
                        self.running = (self.f)(&a);
                        self.con = Box::new(move |x| AST::Image(Box::new(x), b.clone()));
                    } else if self.cur_pos == 2 {
                        self.running = (self.f)(&b);
                        self.con = Box::new(move |x| AST::Image(a.clone(), Box::new(x)));
                    } else {
                        return None;
                    }
                }

                AST::Complement(a) => {
                    if self.cur_pos == 1 {
                        self.running = (self.f)(&a);
                        self.con = Box::new(|x| AST::Complement(Box::new(x)));
                    } else {
                        return None;
                    }
                }

                AST::Sum(a) => {
                    if self.cur_pos == 1 {
                        self.running = (self.f)(&a);
                        self.con = Box::new(|x| AST::Sum(Box::new(x)));
                    } else {
                        return None;
                    }
                }

                AST::Negate(a) => {
                    if self.cur_pos == 1 {
                        self.running = (self.f)(&a);
                        self.con = Box::new(|x| AST::Negate(Box::new(x)));
                    } else {
                        return None;
                    }
                }

                AST::Factorial(a) => {
                    if self.cur_pos == 1 {
                        self.running = (self.f)(&a);
                        self.con = Box::new(|x| AST::Factorial(Box::new(x)));
                    } else {
                        return None;
                    }
                }

                AST::Definition(name, body) => {
                    if self.cur_pos == 1 {
                        self.running = (self.f)(&body);
                        self.con = Box::new(move |t| AST::Definition(name.clone(), Box::new(t)));
                    } else {
                        return None;
                    }
                }

                AST::Rule(attrs, lhs, rhs) => {
                    if self.cur_pos == 1 {
                        self.running = (self.f)(&lhs);
                        self.con = Box::new(move |t| AST::Rule(attrs.clone(), Box::new(t), rhs.clone()));
                    } else if self.cur_pos == 2 {
                        self.running = (self.f)(&rhs);
                        self.con = Box::new(move |t| AST::Rule(attrs.clone(), lhs.clone(), Box::new(t)));
                    } else {
                        return None;
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
        loop {
            match self.pos_queue.pop_front() {
                None => return None,
                Some((expr, pos)) => {
                    match expr {
                        AST::Skip() => (),
                        AST::Int(_) => (),
                        AST::Var(_) => (),
                        AST::Seq(_, _) => (),

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
}

fn map<F>(expr : AST, pos : Vec<usize>, i : usize, f : F) -> Box<dyn Iterator<Item=AST>> where F : Fn(AST) -> Box<dyn Iterator<Item=AST>> {
    if i >= pos.len() {
        return f(expr);
    }
    let idx = pos[i];
    match expr {
        AST::Skip() => Box::new(std::iter::empty()),
        AST::Int(_) => Box::new(std::iter::empty()),
        AST::Var(_) => Box::new(std::iter::empty()),
        AST::Seq(_, _) => Box::new(std::iter::empty()),

        AST::FinSet(elems) =>
            Box::new(map(elems[idx].clone(), pos, i + 1, f).map(move |t| {
                let mut new_elems = elems.clone();
                new_elems[idx] = t;
                return AST::FinSet(new_elems);
            })),

        AST::List(elems) =>
            Box::new(map(elems[idx].clone(), pos, i + 1, f).map(move |t| {
                let mut new_elems = elems.clone();
                new_elems[idx] = t;
                return AST::FinSet(new_elems);
            })),

        AST::Memo(name, args, body, memo) =>
            Box::new(map(*body, pos, i + 1, f).map(move |t| AST::Memo(name.clone(), args.clone(), Box::new(t), memo.clone()))),
        AST::Function(name, args, body) =>
            Box::new(map(*body, pos, i + 1, f).map(move |t| AST::Function(name.clone(), args.clone(), Box::new(t)))),

        AST::App(func, xs) => {
            if idx == 0 {
                return Box::new(map(*func, pos, i + 1, f).map(move |t| AST::App(Box::new(t), xs.clone())));
            } else {
                let xs_idx = idx - 1;
                return Box::new(map(xs[xs_idx].clone(), pos, i + 1, f).map(move |t| {
                    let mut new_xs = xs.clone();
                    new_xs[xs_idx] = t;
                    return AST::App(func.clone(), new_xs);
                }));
            }
        }

        AST::RangeSet(start, end, step) => {
            if idx == 0 {
                return Box::new(map(*start, pos, i + 1, f).map(move |t| AST::RangeSet(Box::new(t), end.clone(), step.clone())));
            } else if idx == 1 {
                return Box::new(map(*end, pos, i + 1, f).map(move |t| AST::RangeSet(start.clone(), Box::new(t), step.clone())));
            } else {
                return Box::new(map(*step, pos, i + 1, f).map(move |t| AST::RangeSet(start.clone(), end.clone(), Box::new(t))));
            }
        }

        AST::IfThenElse(cond, then_expr, else_expr) => {
            if idx == 0 {
                return Box::new(map(*cond, pos, i + 1, f).map(move |t| AST::IfThenElse(Box::new(t), then_expr.clone(), else_expr.clone())));
            } else if idx == 1 {
                return Box::new(map(*then_expr, pos, i + 1, f).map(move |t| AST::IfThenElse(cond.clone(), Box::new(t), else_expr.clone())));
            } else {
                return Box::new(map(*else_expr, pos, i + 1, f).map(move |t| AST::IfThenElse(cond.clone(), then_expr.clone(), Box::new(t))));
            }
        }

        AST::CompSet(var_doms, clauses) => {
            if idx < var_doms.len() {
                return Box::new(map(var_doms[idx].1.clone(), pos, i + 1, f).map(move |t| {
                    let mut new_var_doms = var_doms.clone();
                    new_var_doms[idx] = (new_var_doms[idx].0.clone(), t);
                    return AST::CompSet(new_var_doms, clauses.clone());
                }));
            } else {
                let clause_idx = idx - var_doms.len();
                return Box::new(map(clauses[idx].clone(), pos, i + 1, f).map(move |t| {
                    let mut new_clauses = clauses.clone();
                    new_clauses[clause_idx] = t;
                    return AST::CompSet(var_doms.clone(), new_clauses);
                }));
            }
        }

        AST::Bin(op, a, b) => {
            if idx == 0 {
                return Box::new(map(*a, pos, i + 1, f).map(move |t| AST::Bin(op, Box::new(t), b.clone())));
            } else {
                return Box::new(map(*b, pos, i + 1, f).map(move |t| AST::Bin(op, a.clone(), Box::new(t))));
            }
        }

        AST::Image(a, b) => {
            if idx == 0 {
                return Box::new(map(*a, pos, i + 1, f).map(move |t| AST::Image(Box::new(t), b.clone())));
            } else {
                return Box::new(map(*b, pos, i + 1, f).map(move |t| AST::Image(a.clone(), Box::new(t))));
            }
        }

        AST::Complement(a) => Box::new(map(*a, pos, i + 1, f).map(|t| AST::Complement(Box::new(t)))),
        AST::Sum(a) => Box::new(map(*a, pos, i + 1, f).map(|t| AST::Sum(Box::new(t)))),
        AST::Negate(a) => Box::new(map(*a, pos, i + 1, f).map(|t| AST::Negate(Box::new(t)))),
        AST::Factorial(a) => Box::new(map(*a, pos, i + 1, f).map(|t| AST::Factorial(Box::new(t)))),

        AST::Definition(name, body) => Box::new(map(*body, pos, i + 1, f).map(move |t| AST::Definition(name.clone(), Box::new(t)))),

        AST::Rule(attrs, lhs, rhs) => {
            if idx == 0 {
                return Box::new(map(*lhs, pos, i + 1, f).map(move |t| AST::Rule(attrs.clone(), Box::new(t), rhs.clone())));
            } else {
                return Box::new(map(*rhs, pos, i + 1, f).map(move |t| AST::Rule(attrs.clone(), lhs.clone(), Box::new(t))));
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

fn rewrite_with(lhs : AST, rhs : AST, expr : AST) -> Box<dyn Iterator<Item=AST>> {
    return Box::new(expr.positions().flat_map(move |pos| {
        let l = lhs.clone();
        let r = rhs.clone();
        return map(expr.clone(), pos, 0, move |t| {
            let r2 = r.clone();
            let f = move |to_subs| subs(r2.clone(), &to_subs);
            return Box::new(UnificationIterator::new(l.clone(), t.clone()).map(f));
        });
    }));
}

fn single_rewrite(rules : Vec<AST>, expr : AST) -> Box<dyn Iterator<Item=AST>> {
    return Box::new(rules.into_iter().flat_map(move |rule| match rule {
        AST::Rule(_, lhs, rhs) => rewrite_with(*lhs.clone(), *rhs.clone(), expr.clone()),
        _ => Box::new(std::iter::empty()),
    }));
}

fn rewrite(lhs : AST, rhs : AST, expr : AST) -> Box<dyn Iterator<Item=AST>> {
    return Box::new(ASTMapper::new(expr, Box::new(move |t| {
        let r = rhs.clone();
        let f = move |to_subs| subs(r.clone(), &to_subs);
        Box::new(UnificationIterator::new(lhs.clone(), t.clone()).map(f))
    })));
}

pub fn simplify_tree(expr : AST) -> AST {
    // println!("e: {:?}, pos: {:?}", expr, expr.positions().collect::<Vec<Vec<usize>>>());
    for pos in expr.positions() {
        for new_expr in map(expr.clone(), pos, 0, |t| Box::new(std::iter::once(simplify(t)))) {
            if new_expr != expr {
                return new_expr;
            }
        }
    }
    return expr;
}

pub fn coerce_int(expr : &AST) -> BigInt {
    match expr {
        AST::Int(n) => n.clone(),
        _ => unreachable!()
    }
}

pub fn simplify(expr : AST) -> AST {
    match expr {
        AST::Bin(Op::Add, box AST::Int(n), box AST::Int(m)) => AST::Int(n + m),
        AST::Bin(Op::Sub, box AST::Int(n), box AST::Int(m)) => AST::Int(n - m),
        AST::Bin(Op::Mul, box AST::Int(n), box AST::Int(m)) => AST::Int(n * m),
        AST::Bin(Op::Div, box AST::Int(n), box AST::Int(m)) => AST::Int(n / m),
        AST::Bin(Op::Mod, box AST::Int(n), box AST::Int(m)) => AST::Int(n % m),
        AST::App(f, xs) => {
            if *f == AST::Var("subs".to_string()) {
                match &xs[..] {
                    [e, v, AST::Var(x)] => {
                        let mut new_subs = HashMap::new();
                        new_subs.insert(x.clone(), v.clone());
                        return subs(e.clone(), &new_subs);
                    }
                    _ => AST::App(f, xs)
                }
            } else {
                AST::App(f, xs)
            }
        }
        other => other
    }
}

struct Rewriter<'a> {
    cur_rule : usize,
    rules : &'a Vec<AST>,
    expr : AST,
    expr_it : Box<dyn Iterator<Item=AST>>,
}

impl <'a> Rewriter<'a> {
    fn new(rules : &'a Vec<AST>, expr : AST) -> Rewriter<'a> {
        return Rewriter {
            cur_rule: 0,
            rules: rules,
            expr: expr.clone(),
            expr_it: Box::new(std::iter::empty())
        };
    }
}

impl <'a> Iterator for Rewriter<'a> {
    type Item = AST;

    fn next(&mut self) -> Option<Self::Item> {
        while self.cur_rule <= self.rules.len() {
            loop {
                match self.expr_it.next() {
                    None => break,
                    Some(t) => {
                        // self.cur_rule = 0;
                        return Some(t);
                    }
                }
            }

            if self.cur_rule >= self.rules.len() {
                break;
            }

            match &self.rules[self.cur_rule] {
                AST::Rule(_, lhs, rhs) => {
                    self.expr_it = rewrite(*lhs.clone(), *rhs.clone(), self.expr.clone());
                }

                _ => (),
            }

            self.cur_rule += 1;
        }

        return None;
    }
}

struct TerminatingRewriter<'a> {
    rules : &'a Vec<AST>,
    exprs : Vec<AST>
}

impl <'a> TerminatingRewriter<'a> {
    fn new(rules : &'a Vec<AST>, expr : AST) -> TerminatingRewriter<'a> {
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
                    for new_expr in single_rewrite(self.rules.clone(), expr.clone()) {
                        if new_expr != expr {
                            self.exprs.push(full_simplify(new_expr));
                            changed = true;
                        }
                    }
                    if !changed {
                        return Some(expr.clone());
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

fn main() {
    let args: Vec<String> = env::args().collect();
    let contents = fs::read_to_string(&args[1])
        .expect("Something went wrong reading the file");

    let parse_start = now_millis();
    let parsed = parse(&contents);
    let parse_end = now_millis();
    println!("Parse time: {}ms", parse_end - parse_start);

    let mut fresh_counter = 0;

    match parsed {
        Ok(exprs) => {
            let mut defs = HashMap::new();
            defs.insert("p".to_string(), AST::Seq("primes".to_string(), Rc::new(RefCell::new(PrimeSeq::new()))));

            let mut rules = Vec::new();

            for expr in exprs {
                // println!("{:?}", defs.clone());
                match expr.clone() {
                    AST::Skip() => continue,
                    other => println!("> {:?}", other)
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

                    AST::Rule(attrs, lhs, rhs) => {
                        let mut to_subs = HashMap::new();
                        for x in vars(&lhs) {
                            if !x.starts_with("$") {
                                to_subs.insert(x.clone(), AST::Var(fresh_counter.to_string()));
                                fresh_counter += 1;
                            }
                        }
                        rules.push(AST::Rule(attrs, Box::new(subs(*lhs, &to_subs)),
                                                    Box::new(subs(*rhs, &to_subs))));
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


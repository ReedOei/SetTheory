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
use std::collections::{BinaryHeap, HashSet, HashMap, VecDeque};
use std::cmp::{max, Ordering, Reverse};
use std::env;
use std::fs;
use std::fmt::Debug;
use std::hash::Hash;
use std::iter::Iterator;
use std::time::{SystemTime, UNIX_EPOCH};
use std::rc::Rc;

mod math;
use math::*;
mod ast;
use ast::*;

static mut FRESH_COUNTER : usize = 0;

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct LangParser;

pub fn to_usize(n : &BigInt) -> Result<usize, String> {
    match ToBigUint::to_biguint(n) {
        Some(m) => Ok(m.iter_u64_digits()
            .map(|d| d as usize)
            .fold(0, |accum, d| accum * (std::u64::MAX as usize) + d)),
        None => Err(format!("Could not convert {:?} to usize", n))
    }
}

impl Sequence for Naturals {
    fn nth(&mut self, n : usize) -> Result<AST, String> {
        return Ok(AST::Int(BigInt::from(n)));
    }

    fn increasing(&self) -> bool {
        return true;
    }

    fn index_of(&mut self, v : AST) -> Option<usize> {
        match v {
            AST::Int(n) => to_usize(&n).ok(),
            _ => None
        }
    }
}

pub struct Integers;
impl Integers {
    fn new() -> Integers {
        return Integers;
    }
}

pub fn int_nth(n : usize) -> BigInt {
    if n % 2 == 0 {
        return BigInt::from(n / 2);
    } else {
        return -BigInt::from((n + 1) / 2);
    }
}

impl Sequence for Integers {
    // Enumerate the integers as 0,-1,1,-2,2,...
    fn nth(&mut self, n : usize) -> Result<AST, String> {
        return Ok(AST::Int(int_nth(n)));
    }

    fn increasing(&self) -> bool {
        return false;
    }

    fn index_of(&mut self, v : AST) -> Option<usize> {
        match v {
            AST::Int(n) =>
                if n < Zero::zero() {
                    match to_usize(&-n) {
                        Ok(m) => Some(2*m - 1),
                        _ => None
                    }
                } else {
                    match to_usize(&n) {
                        Ok(m) => Some(2*m),
                        _ => None
                    }
                }
            _ => None
        }
    }
}

pub fn prime_factor(n_in : BigInt, ps : &mut PrimeSeq) -> std::collections::hash_map::IntoIter<BigInt, BigInt> {
    let mut n = n_in;
    let mut powers = HashMap::new();
    let mut m = 0;
    loop {
        let p = ps.at(m);
        if p.clone()*p.clone() > n {
            break;
        }
        if n.clone() % p.clone() == Zero::zero() {
            *powers.entry(p.clone()).or_insert(Zero::zero()) += 1;
            n /= p;
            m = 0;
        } else {
            m += 1;
        }
    }
    *powers.entry(n).or_insert(Zero::zero()) += 1;
    return powers.into_iter();
}

pub struct Rationals {
    ps : PrimeSeq
}
impl Rationals {
    fn new() -> Rationals {
        return Rationals { ps : PrimeSeq::new() };
    }

    fn calc_nth(&mut self, n : usize) -> Result<Rat, String> {
        let mut res = Rat::from_usize(1);
        for (p,a) in prime_factor(BigInt::from(n), &mut self.ps) {
            let b = int_nth(to_usize(&a)?);
            let r = Rat::new(p.clone(), One::one()).pow(&b);
            // println!("{}: {}^({} => {}) = {}", n, p, a, b, r);
            res *= r;
        }
        return Ok(res);
    }
}
impl Sequence for Rationals {
    fn nth(&mut self, n : usize) -> Result<AST, String> {
        if n == 0 {
            return Ok(AST::Rat(Rat::from_usize(0)));
        }

        if n % 2 == 0 {
            return Ok(AST::Rat(self.calc_nth(n / 2)?));
        } else {
            return Ok(AST::Rat(-self.calc_nth((n + 1) / 2)?));
        }
    }

    fn increasing(&self) -> bool {
        return false;
    }

    fn index_of(&mut self, v : AST) -> Option<usize> {
        let (mut n,d) = match v {
            AST::Int(n) => (n, One::one()),
            AST::Rat(Rat{n,d}) => (n,d),
            _ => return None
        };

        let neg = n < Zero::zero();
        if neg {
            n = -n;
        }

        let mut powers : HashMap<BigInt, BigInt> = HashMap::new();
        for (p,a) in prime_factor(n, &mut self.ps) {
            *powers.entry(p).or_insert(Zero::zero()) += a;
        }
        for (p,a) in prime_factor(d, &mut self.ps) {
            *powers.entry(p).or_insert(Zero::zero()) -= a;
        }

        let mut res = 1;

        for (p,a) in powers.into_iter() {
            res *= Pow::pow(to_usize(&p).ok()?, Integers.index_of(AST::Int(a))?);
        }

        if neg {
            return Some(2*res - 1);
        } else {
            return Some(2*res);
        }
    }
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

        println!("\nRunning sieve to {}", increment + self.max);

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

struct MatrixGen {
    generated : Vec<AST>,
    keys : Vec<Vec<String>>,
    items : Assignments,
}

impl MatrixGen {
    fn new(n : usize, seq : AST) -> Result<MatrixGen, String> {
        let mut keys = Vec::new();
        let mut var_doms = Vec::new();
        let mut k = 0;
        for _ in 0..n {
            let mut key_row = Vec::new();
            for _ in 0..n {
                key_row.push(k.to_string());
                var_doms.push((k.to_string(), seq.clone()));
                k += 1;
            }
            keys.push(key_row);
        }
        return Ok(MatrixGen {
            generated: Vec::new(),
            keys: keys,
            items: Assignments::from(var_doms)?
        });
    }
}

impl Sequence for MatrixGen {
    fn nth(&mut self, n : usize) -> Result<AST, String> {
        while n >= self.generated.len() {
            match self.items.next() {
                None => return Err("No more items to generate!".to_string()),
                Some(kvs) => {
                    let mut rows = Vec::new();

                    for i in &self.keys {
                        let mut row = Vec::new();
                        for k in i {
                            row.push(kvs[k].clone());
                        }
                        rows.push(AST::List(row));
                    }
                    self.generated.push(AST::List(rows));
                }
            }
        }

        return Ok(self.generated[n].clone());
    }

    fn increasing(&self) -> bool {
        return false;
    }

    fn index_of(&mut self, v : AST) -> Option<usize> {
        return self.generated.iter().position(|w| &v == w);
    }
}

struct MakeMatrixGen;
impl MakeMatrixGen {
    fn new() -> MakeMatrixGen {
        return MakeMatrixGen;
    }
}

impl BuiltinFunc for MakeMatrixGen {
    fn apply(&self, args : Vec<AST>) -> Result<AST, String> {
        let n = to_usize(&as_int(eval(args[0].clone())?)?)?;
        let seq = eval(args[1].clone())?;
        return Ok(AST::Seq("matrix_generator".to_string(), Rc::new(RefCell::new(MatrixGen::new(n, seq)?))));
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
        if &n > self.primes.last().unwrap() {
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

fn format_assignment(a : &HashMap<String, AST>) -> String {
    let mut s = String::new();
    s.push('{');
    s.push_str(a.iter().map(|(k, v)| format!("{} -> {}", k, v)).collect::<Vec<String>>().join(", ").as_str());
    s.push('}');
    return s;
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
        Rule::counterexample => Ok(AST::Counterexample(Box::new(primary(pair.into_inner().next().unwrap())?))),

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

pub fn as_rat(expr : AST) -> Result<Rat, String> {
    match expr {
        AST::Int(n) => Ok(Rat::new(n, One::one())),
        AST::Rat(r) => Ok(r),
        _ => Err(format!("Expected rational number but got {:?}", expr))
    }
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
        AST::Counterexample(t) => AST::Counterexample(Box::new(subs_expr(*t, rep, pat))),

        AST::FinSet(elems) => AST::FinSet(elems.into_iter().map(| e | subs_expr(e, rep, pat)).collect()),

        AST::Memo(name, args, body, memo) => AST::Memo(name, args, body, memo),

        AST::List(elems) => AST::List(elems.into_iter().map(| e | subs_expr(e, rep, pat)).collect()),

        AST::Seq(name, implementation) => AST::Seq(name, implementation),
        AST::Builtin(name, implementation) => AST::Builtin(name, implementation),

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
        AST::Rat(r) => AST::Rat(r),
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
        AST::Counterexample(t) => AST::Counterexample(Box::new(subs(*t, to_subs))),

        AST::FinSet(elems) => AST::FinSet(elems.into_iter().map(| e | subs(e, to_subs)).collect()),

        AST::Memo(name, args, body, memo) => AST::Memo(name, args, body, memo),

        AST::List(elems) => AST::List(elems.into_iter().map(| e | subs(e, to_subs)).collect()),

        AST::Seq(name, implementation) => AST::Seq(name, implementation),
        AST::Builtin(name, implementation) => AST::Builtin(name, implementation),

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
                return subs(subs_expr(args[1].clone(), &AST::Var(fresh()), &args[0]), to_subs);
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
        AST::Rat(r) => AST::Rat(r),
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

        AST::Seq(_, implementation) => Ok(Box::new((0..).map(move |n| implementation.borrow_mut().nth(n)))),

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

pub fn wrap_num(r : Rat) -> AST {
    if r.d == One::one() {
        return AST::Int(r.n);
    } else {
        return AST::Rat(r);
    }
}

pub fn scalar_matrix(a : &AST, n : usize) -> AST {
    let mut rows = Vec::new();
    for i in 0..n {
        let mut row = Vec::new();

        for j in 0..n {
            if i == j {
                row.push(a.clone());
            } else {
                row.push(AST::Int(Zero::zero()));
            }
        }

        rows.push(AST::List(row));
    }

    return AST::List(rows);
}

pub fn full_matrix(a : &AST, n : usize) -> AST {
    let mut rows = Vec::new();
    for _ in 0..n {
        let mut row = Vec::new();

        for _ in 0..n {
            row.push(a.clone());
        }

        rows.push(AST::List(row));
    }

    return AST::List(rows);
}

pub fn lift_operands(a : AST, b : AST, full_mat : bool) -> (AST, AST) {
    let make_matrix = |x, n| if full_mat { full_matrix(x, n) } else { scalar_matrix(x, n) };
    match (a,b) {
        (AST::Int(n), AST::Rat(r)) => (AST::Rat(Rat::new(n, One::one())), AST::Rat(r)),
        (AST::Rat(r), AST::Int(n)) => (AST::Rat(r), AST::Rat(Rat::new(n, One::one()))),
        (AST::Int(n), AST::List(m)) => (make_matrix(&AST::Int(n), m.len()), AST::List(m)),
        (AST::Rat(r), AST::List(m)) => (make_matrix(&AST::Rat(r), m.len()), AST::List(m)),
        (AST::List(m), AST::Int(n)) => {
            let d = m.len();
            (AST::List(m), make_matrix(&AST::Int(n), d))
        }
        (AST::List(m), AST::Rat(r)) => {
            let d = m.len();
            (AST::List(m), make_matrix(&AST::Rat(r), d))
        }
        (x,y) => (x,y)
    }
}

pub fn as_matrix(xs : Vec<AST>) -> Result<Vec<Vec<AST>>, String> {
    let mut rows = Vec::new();
    for x in xs {
        match x {
            AST::List(ys) => rows.push(ys),
            _ => return Err(format!("Expected matrix (list of lists) but one 'row' was: {}", x))
        }
    }
    return Ok(rows);
}

pub fn eval(expr : AST) -> Result<AST, String> {
    match expr {
        AST::Int(n) => Ok(AST::Int(n)),
        AST::Rat(r) => Ok(AST::Rat(r)),

        AST::Seq(name, implementation) => Ok(AST::Seq(name, implementation)),
        AST::Builtin(name, implementation) => Ok(AST::Builtin(name, implementation)),

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
            match lift_operands(eval(*a)?, eval(*b)?, true) {
                (AST::Int(n), AST::Int(m)) => Ok(AST::Int(n + m)),
                (AST::Rat(n), AST::Rat(m)) => Ok(AST::Rat(n + m)),
                (AST::List(n), AST::List(m)) => {
                    if n.len() != m.len() {
                        return Err(format!("Tried to add matrixes of different lengths ({:?} and {:?})", n, m));
                    }

                    let mut res = Vec::new();
                    for (a,b) in n.into_iter().zip(m) {
                        res.push(eval(AST::Bin(Op::Add, Box::new(a), Box::new(b)))?);
                    }
                    return Ok(AST::List(res));
                }
                (x,y) => return Err(format!("I don't know how to add {} and {}", x, y))
            }
        }

        AST::Bin(Op::Sub, a, b) => {
            match lift_operands(eval(*a)?, eval(*b)?, true) {
                (AST::Int(n), AST::Int(m)) => Ok(AST::Int(n - m)),
                (AST::Rat(n), AST::Rat(m)) => Ok(AST::Rat(n - m)),
                (AST::List(n), AST::List(m)) => {
                    if n.len() != m.len() {
                        return Err(format!("Tried to subtract matrixes of different lengths ({:?} and {:?})", n, m));
                    }

                    let mut res = Vec::new();
                    for (a,b) in n.into_iter().zip(m) {
                        res.push(eval(AST::Bin(Op::Sub, Box::new(a), Box::new(b)))?);
                    }
                    return Ok(AST::List(res));
                }
                (x,y) => return Err(format!("I don't know how to add {} and {}", x, y))
            }
        }

        AST::Bin(Op::Mul, a, b) => {
            match lift_operands(eval(*a)?, eval(*b)?, false) {
                (AST::Int(n), AST::Int(m)) => Ok(AST::Int(n * m)),
                (AST::Rat(n), AST::Rat(m)) => Ok(AST::Rat(n * m)),
                (AST::List(n), AST::List(m)) => {
                    let n_mat = as_matrix(n)?;
                    let m_mat = as_matrix(m)?;
                    if m_mat.is_empty() || n_mat.is_empty() || n_mat.len() != m_mat[0].len() {
                        return Err(format!("Tried to multiply matrixes of wrong dimensions ({:?} and {:?})", n_mat, m_mat));
                    }

                    let mut rows = Vec::new();
                    for i in 0..n_mat.len() {
                        let mut row = Vec::new();
                        for j in 0..m_mat[0].len() {
                            let mut val = AST::Int(Zero::zero());
                            for k in 0..n_mat[0].len() {
                                let n_val = Box::new(n_mat[i][k].clone());
                                let m_val = Box::new(m_mat[k][j].clone());
                                val = eval(AST::Bin(Op::Add, Box::new(val), Box::new(AST::Bin(Op::Mul, n_val, m_val))))?;
                            }
                            row.push(val);
                        }
                        rows.push(AST::List(row));
                    }
                    return Ok(AST::List(rows));
                }
                (x,y) => return Err(format!("I don't know how to add {} and {}", x, y))
            }
        }

        AST::Bin(Op::Div, a, b) => {
            let aval = as_rat(eval(*a)?)?;
            let bval = as_rat(eval(*b)?)?;

            if bval.n == Zero::zero() {
                return Err("Cannot divide by 0".to_string());
            }

            return Ok(wrap_num(aval / bval));
        }

        AST::Bin(Op::Mod, a, b) => {
            let bval = as_int(eval(*b)?)?;
            if bval == Zero::zero() {
                return Err("Cannot divide by 0".to_string());
            }
            return Ok(AST::Int(as_int(eval(*a)?)? % bval));
        }

        AST::Bin(Op::Exp, a, b) => {
            match eval(*a)? {
                AST::Int(n) => Ok(wrap_num(Rat::new(n, One::one()).pow(&as_int(eval(*b)?)?))),
                AST::Rat(r) => Ok(wrap_num(r.pow(&as_int(eval(*b)?)?))),
                t => {
                    let orig = t.clone();
                    let mut val = t;
                    let bval = to_usize(&as_int(eval(*b)?)?)?;
                    for _ in 1..bval {
                        val = eval(AST::Bin(Op::Mul, Box::new(val), Box::new(orig.clone())))?;
                    }
                    return Ok(val);
                }
            }
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
            if as_rat(eval(*a)?)? < as_rat(eval(*b)?)? {
                return Ok(AST::Int(One::one()));
            } else {
                return Ok(AST::Int(Zero::zero()));
            }
        }

        AST::Bin(Op::Le, a, b) => {
            if as_rat(eval(*a)?)? <= as_rat(eval(*b)?)? {
                return Ok(AST::Int(One::one()));
            } else {
                return Ok(AST::Int(Zero::zero()));
            }
        }

        AST::Bin(Op::Gt, a, b) => {
            if as_rat(eval(*a)?)? > as_rat(eval(*b)?)? {
                return Ok(AST::Int(One::one()));
            } else {
                return Ok(AST::Int(Zero::zero()));
            }
        }

        AST::Bin(Op::Ge, a, b) => {
            if as_rat(eval(*a)?)? >= as_rat(eval(*b)?)? {
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

        AST::Var(name) if name.as_str() == "|" => Ok(AST::Var(name)),

        AST::App(func, args) => {
            match eval(*func)? {
                AST::Function(name, formal_args, body) => {
                    let mut to_subs = HashMap::new();
                    if let Some(ref f_name) = name {
                        to_subs.insert(f_name.clone(), AST::Function(name.clone(), formal_args.clone(), body.clone()));
                    }
                    for (formal, actual) in formal_args.into_iter().zip(args) {
                        to_subs.insert(formal, eval(actual)?);
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

                    if let Some(ref f_name) = name {
                        to_subs.insert(f_name.clone(), AST::Memo(name.clone(), formal_args.clone(), body.clone(), memo.clone()));
                    }

                    for (formal, val) in formal_args.into_iter().zip(vals.clone()) {
                        to_subs.insert(formal, val);
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

                AST::Builtin(_, implementation) => implementation.borrow_mut().apply(args),

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

                        "gcd" => Ok(AST::Int(gcd(as_int(eval(args[0].clone())?)?, as_int(eval(args[1].clone())?)?))),

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

pub fn union<'a>(a : HashSet<&'a str>, b : HashSet<&'a str>) -> HashSet<&'a str> {
    let mut new_a = a;
    new_a.extend(b);
    return new_a;
}

pub fn diff<'a>(a : HashSet<&'a str>, b : &HashSet<&'a str>) -> HashSet<&'a str> {
    let mut new_a = a;
    new_a.retain(|v| !b.contains(v));
    return new_a;
}

pub fn vars(expr : &AST) -> HashSet<&str> {
    match expr {
        AST::Skip() => HashSet::new(),
        AST::Int(_) => HashSet::new(),
        AST::Rat(_) => HashSet::new(),

        AST::Assumption(t) => vars(t),
        AST::Prove(t) => vars(t),
        AST::Counterexample(t) => vars(t),

        AST::Var(x) => {
            let mut vs = HashSet::new();
            let c = x.chars().next().unwrap();
            if c.is_alphabetic() || c == '?' {
                vs.insert(x.as_str());
            }
            return vs;
        }
        AST::Definition(_, body) => vars(body),
        AST::Rule(_, lhs, rhs) => union(vars(lhs), vars(rhs)),

        AST::Seq(_, _) => HashSet::new(),
        AST::Builtin(_, _) => HashSet::new(),

        AST::FinSet(elems) => elems.iter().flat_map(|e| vars(e).into_iter()).collect(),
        AST::List(elems) => elems.iter().flat_map(|e| vars(e).into_iter()).collect(),

        AST::RangeSet(start, end, step) => union(vars(start), union(vars(end), vars(step))),
        AST::Image(f, s) => union(vars(f), vars(s)),
        AST::CompSet(var_doms, clauses) => {
            let mut bound_vars = HashSet::new();
            let mut res = HashSet::new();
            for (x, dom) in var_doms {
                res.extend(diff(vars(dom), &bound_vars));
                bound_vars.insert(x.as_str());
            }
            for clause in clauses {
                res.extend(diff(vars(clause), &bound_vars));
            }
            return res;
        }

        AST::App(f, xs) => union(vars(f), xs.iter().flat_map(|x| vars(x).into_iter()).collect()),

        AST::Bin(_, a, b) => union(vars(a), vars(b)),

        AST::Function(_, args, body) => {
            let arg_vars = args.iter().map(|x| x.as_str()).collect();
            return diff(vars(body), &arg_vars);
        }

        AST::Memo(_, args, body, _) => {
            let arg_vars = args.iter().map(|x| x.as_str()).collect();
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
    Done,
    Failed
}

#[derive(PartialEq, Eq, Debug, Clone)]
struct Unification<'a> {
    eqs : Vec<(AST, AST)>,
    lhs_vars : &'a HashSet<String>,
    subs : HashMap<String, AST>,
}

impl <'a> Unification<'a> {
    fn process_eq(&mut self, lhs : AST, rhs : AST, unifs : &mut Vec<Unification<'a>>) -> bool {
        if lhs == rhs {
            return true;
        }

        match (lhs, rhs) {
            (AST::Var(x), t) => {
                if !self.lhs_vars.contains(&x) {
                    return AST::Var(x) == t;
                } else {
                    let vx = AST::Var(x.clone());
                    for (a,b) in &mut self.eqs {
                        *a = subs_expr(std::mem::take(a), &t, &vx);
                        *b = subs_expr(std::mem::take(b), &t, &vx);
                    }
                    for (_, cur_t) in self.subs.iter_mut() {
                        *cur_t = subs_expr(std::mem::take(cur_t), &t, &vx);
                    }
                    self.subs.insert(x, t);
                }
            }

            (AST::FinSet(es1), AST::FinSet(es2)) => {
                self.eqs.extend(es1.into_iter().zip(es2));
            }

            (AST::List(es1), AST::List(es2)) => {
                self.eqs.extend(es1.into_iter().zip(es2));
            }

            (AST::Bin(op1, a, b), AST::Bin(op2, c, d)) => {
                if op1 != op2 {
                    return false;
                }
                self.eqs.push((*a, *c));
                self.eqs.push((*b, *d));
            }

            (AST::App(f, mut xs), rhs) => match *f {
                AST::Var(fname) if fname == "$var" => match rhs {
                    AST::Var(y) => return self.process_eq(xs.pop().unwrap(), AST::Var(y), unifs),
                    _ => return false
                }

                AST::Var(fname) if fname == "$free_var" => {
                    for y in vars(&rhs) {
                        let mut new_unif = self.clone();
                        new_unif.eqs.push((xs[0].clone(), AST::Var(y.to_string())));
                        new_unif.eqs.push((xs[1].clone(), rhs.clone()));
                        unifs.push(new_unif);
                    }
                    return false;
                }

                AST::Var(fname) if fname == "$coeff" => match rhs {
                    AST::Var(y) => {
                        self.eqs.push((xs.pop().unwrap(), AST::Var(y)));
                        self.eqs.push((xs.pop().unwrap(), AST::Int(One::one())));
                    }
                    AST::Bin(Op::Mul, a, b) => {
                        self.eqs.push((xs.pop().unwrap(), *b));
                        self.eqs.push((xs.pop().unwrap(), *a));
                    }
                    _ => return false
                }

                AST::Var(fname) if fname == "$int" => match rhs {
                    AST::Int(n) => return self.process_eq(xs.pop().unwrap(), AST::Int(n), unifs),
                    _ => return false
                }

                AST::Var(fname) if fname == "$s" => match rhs {
                    AST::Int(n) if n > Zero::zero() => {
                        return self.process_eq(xs.pop().unwrap(), AST::Int(n - 1), unifs);
                    }
                    _ => return false
                }

                AST::Var(fname) if fname == "$prime_factor" => match rhs {
                    AST::Int(n) => {
                        for p in factor(n.clone()) {
                            if p == n {
                                break;
                            }
                            let mut new_unif = self.clone();
                            new_unif.eqs.push((xs[0].clone(), AST::Int(p.clone())));
                            new_unif.eqs.push((xs[1].clone(), AST::Int(n.clone() / p)));
                            unifs.push(new_unif);
                        }
                        // We say failed because we transferred all the other possibilities to the other unifications we created above.
                        return false;
                    }
                    _ => return false
                }

                AST::Var(fname) if fname == "$power" => match rhs {
                    AST::Int(n) if n == One::one() => {
                        return self.process_eq(xs.pop().unwrap(), AST::Int(Zero::zero()), unifs);
                    }
                    _ => return false
                }

                AST::Var(fname) if fname == "$elem" => match rhs {
                    AST::FinSet(elems) => {
                        let rest_var = xs.pop().unwrap();
                        let elem_var = xs.pop().unwrap();

                        for (i, e) in elems.iter().enumerate() {
                            if i == elems.len() - 1 {
                                self.eqs.push((elem_var, e.clone()));
                                let mut new_elems = elems;
                                new_elems.remove(i);
                                self.eqs.push((rest_var, AST::FinSet(new_elems)));
                                return true;
                            } else {
                                let mut new_unif = self.clone();
                                new_unif.eqs.push((elem_var.clone(), e.clone()));
                                new_unif.eqs.push((rest_var.clone(), AST::FinSet(drop_idx(&elems, i))));
                                unifs.push(new_unif);
                            }
                        }

                        // This will only occur if the set is empty, otherwise we return in
                        // the for loop on the last element.
                        return false;
                    }
                    _ => return false
                }

                AST::Var(fname) if fname == "$union" => match rhs {
                    // TODO: Should allow matching all possible partitions of the set into
                    // two nonempty subsets.
                    AST::FinSet(_) => unreachable!(),
                    _ => return false
                }

                _ => match rhs {
                    AST::App(g, ys) => {
                        self.eqs.push((*f, *g));
                        self.eqs.extend(xs.into_iter().zip(ys));
                    }
                    _ => return false
                }
            }

            (AST::IfThenElse(c1, t1, e1), AST::IfThenElse(c2, t2, e2)) => {
                self.eqs.push((*c1, *c2));
                self.eqs.push((*t1, *t2));
                self.eqs.push((*e1, *e2));
            }

            (AST::Factorial(a), AST::Factorial(b)) => return self.process_eq(*a, *b, unifs),
            (AST::Sum(a), AST::Sum(b)) => return self.process_eq(*a, *b, unifs),
            (AST::Complement(a), AST::Complement(b)) => return self.process_eq(*a, *b, unifs),
            (AST::Negate(a), AST::Negate(b)) => return self.process_eq(*a, *b, unifs),

            (AST::RangeSet(s1, e1, st1), AST::RangeSet(s2, e2, st2)) => {
                self.eqs.push((*s1, *s2));
                self.eqs.push((*e1, *e2));
                self.eqs.push((*st1, *st2));
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
            }

            (a, b) => return a == b
        }

        return true;
    }

    fn step(&mut self, unifs : &mut Vec<Unification<'a>>) -> UnificationStatus {
        // println!("Equations: {:?}", self.eqs);
        // println!("Substitution: {:?}", self.subs);
        loop {
            match self.eqs.pop() {
                None => return UnificationStatus::Done,
                Some((lhs, rhs)) =>
                    if !self.process_eq(lhs, rhs, unifs) {
                        return UnificationStatus::Failed;
                    }
            }
        }
    }
}

struct UnificationIterator<'a> {
    unifs : Vec<Unification<'a>>
}

impl <'a> Iterator for UnificationIterator<'a> {
    type Item = HashMap<String, AST>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.unifs.pop() {
                None => return None,
                Some(mut unif) => {
                    match unif.step(&mut self.unifs) {
                        UnificationStatus::Failed => continue,
                        UnificationStatus::Done => return Some(unif.subs),
                    }
                }
            }
        }
    }
}

struct Unifier {
    lhs : AST,
    lhs_vars : HashSet<String>
}

impl Unifier {
    fn new(lhs : AST) -> Unifier {
        let lhs_vars = vars(&lhs).iter().filter(|x| x.starts_with('?')).map(|x| x.to_string()).collect();
        return Unifier {
            lhs: lhs,
            lhs_vars: lhs_vars
        };
    }

    fn unify(&self, rhs : AST) -> UnificationIterator {
        return UnificationIterator {
            unifs: vec!(Unification { eqs : vec!((self.lhs.clone(), rhs)), lhs_vars: &self.lhs_vars, subs: HashMap::new() })
        };
    }
}

struct Positions {
    pos_queue : Vec<(AST, Vec<usize>)>
}

#[allow(clippy::ptr_arg)]
fn add_elem<T>(xs : &Vec<T>, x : T) -> Vec<T> where T : Clone {
    let mut new_xs = xs.clone();
    new_xs.push(x);
    return new_xs;
}

impl Iterator for Positions {
    type Item = Vec<usize>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.pos_queue.pop() {
            None => return None,
            Some((expr, pos)) => {
                match expr {
                    AST::Skip() => (),
                    AST::Int(_) => (),
                    AST::Rat(_) => (),
                    AST::Var(_) => (),
                    AST::Seq(_, _) => (),
                    AST::Builtin(_, _) => (),

                    AST::Assumption(t) => self.pos_queue.push((*t, add_elem(&pos, 0))),
                    AST::Prove(t) => self.pos_queue.push((*t, add_elem(&pos, 0))),
                    AST::Counterexample(t) => self.pos_queue.push((*t, add_elem(&pos, 0))),

                    AST::FinSet(elems) => {
                        for (i, e) in elems.into_iter().enumerate() {
                            self.pos_queue.push((e, add_elem(&pos, i)));
                        }
                    }

                    AST::List(elems) => {
                        for (i, e) in elems.into_iter().enumerate() {
                            self.pos_queue.push((e, add_elem(&pos, i)));
                        }
                    }

                    AST::Memo(_, _, body, _) => self.pos_queue.push((*body, add_elem(&pos, 0))),
                    AST::Function(_, _, body) => self.pos_queue.push((*body, add_elem(&pos, 0))),

                    AST::App(func, xs) => {
                        self.pos_queue.push((*func, add_elem(&pos, 0)));
                        for (i, x) in xs.into_iter().enumerate() {
                            self.pos_queue.push((x, add_elem(&pos, i + 1)));
                        }
                    }

                    AST::RangeSet(start, end, step) => {
                        self.pos_queue.push((*start, add_elem(&pos, 0)));
                        self.pos_queue.push((*end, add_elem(&pos, 1)));
                        self.pos_queue.push((*step, add_elem(&pos, 2)));
                    }

                    AST::IfThenElse(cond, then_expr, else_expr) => {
                        self.pos_queue.push((*cond, add_elem(&pos, 0)));
                        self.pos_queue.push((*then_expr, add_elem(&pos, 1)));
                        self.pos_queue.push((*else_expr, add_elem(&pos, 2)));
                    }

                    AST::CompSet(var_doms, clauses) => {
                        let n = var_doms.len();
                        for (i, (_, dom)) in var_doms.into_iter().enumerate() {
                            self.pos_queue.push((dom, add_elem(&pos, i)));
                        }
                        for (i, clause) in clauses.into_iter().enumerate() {
                            self.pos_queue.push((clause, add_elem(&pos, n + i)));
                        }
                    }

                    AST::Bin(_, a, b) => {
                        self.pos_queue.push((*a, add_elem(&pos, 0)));
                        self.pos_queue.push((*b, add_elem(&pos, 1)));
                    }

                    AST::Image(a, b) => {
                        self.pos_queue.push((*a, add_elem(&pos, 0)));
                        self.pos_queue.push((*b, add_elem(&pos, 1)));
                    }

                    AST::Complement(a) => self.pos_queue.push((*a, add_elem(&pos, 0))),
                    AST::Sum(a) => self.pos_queue.push((*a, add_elem(&pos, 0))),
                    AST::Negate(a) => self.pos_queue.push((*a, add_elem(&pos, 0))),
                    AST::Factorial(a) => self.pos_queue.push((*a, add_elem(&pos, 0))),

                    AST::Definition(_, body) => self.pos_queue.push((*body, add_elem(&pos, 0))),

                    AST::Rule(_, lhs, rhs) => {
                        self.pos_queue.push((*lhs, add_elem(&pos, 0)));
                        self.pos_queue.push((*rhs, add_elem(&pos, 1)));
                    }
                }

                return Some(pos);
            }
        }
    }
}

fn drop_idx<T>(xs : &[T], idx : usize) -> Vec<T> where T : Clone {
    let mut new_xs = Vec::with_capacity(xs.len());
    new_xs.extend_from_slice(&xs[0..idx]);
    new_xs.extend_from_slice(&xs[idx + 1..]);
    return new_xs;
}

fn at<'a>(expr : &'a AST, pos : &Vec<usize>, i : usize) -> &'a AST {
    if i >= pos.len() {
        return expr;
    }
    let idx = pos[i];
    match expr {
        AST::Skip() => expr,
        AST::Int(_) => expr,
        AST::Rat(_) => expr,
        AST::Var(_) => expr,
        AST::Seq(_, _) => expr,
        AST::Builtin(_, _) => expr,

        AST::Assumption(t) => at(t, pos, i + 1),
        AST::Prove(t) => at(t, pos, i + 1),
        AST::Counterexample(t) => at(t, pos, i + 1),

        AST::FinSet(elems) => at(&elems[idx], pos, i + 1),
        AST::List(elems) => at(&elems[idx], pos, i + 1),

        AST::Memo(_, _, body, _) => at(body, pos, i + 1),
        AST::Function(_, _, body) => at(body, pos, i + 1),

        AST::App(func, xs) => {
            if idx == 0 {
                return at(func, pos, i + 1);
            } else {
                let xs_idx = idx - 1;
                return at(&xs[xs_idx], pos, i + 1);
            }
        }

        AST::RangeSet(start, end, step) => {
            if idx == 0 {
                return at(start, pos, i + 1);
            } else if idx == 1 {
                return at(end, pos, i + 1);
            } else {
                return at(step, pos, i + 1);
            }
        }

        AST::IfThenElse(cond, then_expr, else_expr) => {
            if idx == 0 {
                return at(cond, pos, i + 1);
            } else if idx == 1 {
                return at(then_expr, pos, i + 1);
            } else {
                return at(else_expr, pos, i + 1);
            }
        }

        AST::CompSet(var_doms, clauses) => {
            if idx < var_doms.len() {
                return at(&var_doms[idx].1, pos, i + 1);
            } else {
                let clause_idx = idx - var_doms.len();
                return at(&clauses[clause_idx], pos, i + 1);
            }
        }

        AST::Bin(_, a, b) => {
            if idx == 0 {
                return at(a, pos, i + 1);
            } else {
                return at(b, pos, i + 1);
            }
        }

        AST::Image(a, b) => {
            if idx == 0 {
                return at(a, pos, i + 1);
            } else {
                return at(b, pos, i + 1);
            }
        }

        AST::Complement(a) => at(a, pos, i + 1),
        AST::Sum(a) => at(a, pos, i + 1),
        AST::Negate(a) => at(a, pos, i + 1),
        AST::Factorial(a) => at(a, pos, i + 1),

        AST::Definition(_, body) => at(body, pos, i + 1),

        AST::Rule(_, lhs, rhs) => {
            if idx == 0 {
                return at(lhs, pos, i + 1);
            } else {
                return at(rhs, pos, i + 1);
            }
        }
    }
}

fn at_mut<'a>(expr : &'a mut AST, pos : &Vec<usize>, i : usize) -> &'a mut AST {
    if i >= pos.len() {
        return expr;
    }
    let idx = pos[i];
    match expr {
        AST::Skip() => expr,
        AST::Int(_) => expr,
        AST::Rat(_) => expr,
        AST::Var(_) => expr,
        AST::Seq(_, _) => expr,
        AST::Builtin(_, _) => expr,

        AST::Assumption(t) => at_mut(t, pos, i + 1),
        AST::Prove(t) => at_mut(t, pos, i + 1),
        AST::Counterexample(t) => at_mut(t, pos, i + 1),

        AST::FinSet(elems) => at_mut(&mut elems[idx], pos, i + 1),
        AST::List(elems) => at_mut(&mut elems[idx], pos, i + 1),

        AST::Memo(_, _, body, _) => at_mut(body, pos, i + 1),
        AST::Function(_, _, body) => at_mut(body, pos, i + 1),

        AST::App(func, xs) => {
            if idx == 0 {
                return at_mut(func, pos, i + 1);
            } else {
                let xs_idx = idx - 1;
                return at_mut(&mut xs[xs_idx], pos, i + 1);
            }
        }

        AST::RangeSet(start, end, step) => {
            if idx == 0 {
                return at_mut(start, pos, i + 1);
            } else if idx == 1 {
                return at_mut(end, pos, i + 1);
            } else {
                return at_mut(step, pos, i + 1);
            }
        }

        AST::IfThenElse(cond, then_expr, else_expr) => {
            if idx == 0 {
                return at_mut(cond, pos, i + 1);
            } else if idx == 1 {
                return at_mut(then_expr, pos, i + 1);
            } else {
                return at_mut(else_expr, pos, i + 1);
            }
        }

        AST::CompSet(var_doms, clauses) => {
            if idx < var_doms.len() {
                return at_mut(&mut var_doms[idx].1, pos, i + 1);
            } else {
                let clause_idx = idx - var_doms.len();
                return at_mut(&mut clauses[clause_idx], pos, i + 1);
            }
        }

        AST::Bin(_, a, b) => {
            if idx == 0 {
                return at_mut(a, pos, i + 1);
            } else {
                return at_mut(b, pos, i + 1);
            }
        }

        AST::Image(a, b) => {
            if idx == 0 {
                return at_mut(a, pos, i + 1);
            } else {
                return at_mut(b, pos, i + 1);
            }
        }

        AST::Complement(a) => at_mut(a, pos, i + 1),
        AST::Sum(a) => at_mut(a, pos, i + 1),
        AST::Negate(a) => at_mut(a, pos, i + 1),
        AST::Factorial(a) => at_mut(a, pos, i + 1),

        AST::Definition(_, body) => at_mut(body, pos, i + 1),

        AST::Rule(_, lhs, rhs) => {
            if idx == 0 {
                return at_mut(lhs, pos, i + 1);
            } else {
                return at_mut(rhs, pos, i + 1);
            }
        }
    }
}

impl AST {
    fn positions(&self) -> Positions {
        return Positions { pos_queue: vec!((self.clone(), vec!())) };
    }

    fn size(&self) -> usize {
        match self {
            AST::Skip() => 1,
            AST::Int(_) => 1,
            AST::Rat(_) => 1,
            AST::Var(_) => 1,
            AST::Seq(_, _) => 1,

            AST::Builtin(_, _) => 1,

            AST::Assumption(t) => 1 + t.size(),
            AST::Prove(t) => 1 + t.size(),
            AST::Counterexample(t) => 1 + t.size(),

            AST::FinSet(elems) => elems.iter().map(|e| e.size()).sum::<usize>() + 1,
            AST::List(elems) => elems.iter().map(|e| e.size()).sum::<usize>() + 1,

            AST::Memo(_, _, body, _) => 1 + body.size(),
            AST::Function(_, _, body) => 1 + body.size(),

            AST::App(func, xs) => func.size() + xs.iter().map(|x| x.size()).sum::<usize>() + 1,

            AST::RangeSet(start, end, step) => 1 + start.size() + end.size() + step.size(),

            AST::IfThenElse(cond, then_expr, else_expr) => 1 + cond.size() + then_expr.size() + else_expr.size(),

            AST::CompSet(var_doms, clauses) =>
                var_doms.iter().map(|(_, dom)| 1 + dom.size()).sum::<usize>() +
                clauses.iter().map(|c| c.size()).sum::<usize>() + 1,

            AST::Bin(_, a, b) => 1 + a.size() + b.size(),

            AST::Image(a, b) => 1 + a.size() + b.size(),
            AST::Complement(a) => 1 + a.size(),
            AST::Sum(a) => 1 + a.size(),
            AST::Negate(a) => 1 + a.size(),
            AST::Factorial(a) => 1 + a.size(),

            AST::Definition(_, body) => 1 + body.size(),

            AST::Rule(_, lhs, rhs) => 1 + lhs.size() + rhs.size()
        }
    }
}

struct RewriteRule {
    unifier : Unifier,
    rhs : AST
}

impl RewriteRule {
    fn new(lhs : AST, rhs : AST) -> RewriteRule {
        return RewriteRule {
            unifier: Unifier::new(lhs),
            rhs: rhs
        };
    }

    fn rewrite<'a>(&'a self, expr : &'a AST) -> Box<dyn Iterator<Item=AST> + 'a> {
        return Box::new(expr.positions().flat_map(move |pos| {
            let sub_expr = at(expr, &pos, 0).clone();
            let f = move |to_subs| {
                let mut temp = expr.clone();
                *at_mut(&mut temp, &pos, 0) = subs(self.rhs.clone(), &to_subs);
                return temp;
            };
            return self.unifier.unify(sub_expr).map(f);
        }));
    }
}

pub fn truth_val(b : bool) -> AST {
    AST::Int(if b { One::one() } else { Zero::zero() })
}

pub fn simplify(expr : &AST) -> Option<AST> {
    match expr {
        AST::Rat(Rat {n, d}) if d == &One::one() => Some(AST::Int(n.clone())),

        AST::Bin(Op::Add, box AST::Int(n), box AST::Int(m)) => Some(AST::Int(n + m)),
        AST::Bin(Op::Add, box AST::Rat(n), box AST::Rat(m)) => Some(AST::Rat(n.clone() + m.clone())),
        AST::Bin(Op::Add, box AST::Rat(n), box AST::Int(m)) => Some(AST::Rat(n.clone() + m.clone())),
        AST::Bin(Op::Add, box AST::Int(n), box AST::Rat(m)) => Some(AST::Rat(m.clone() + n.clone())),
        AST::Bin(Op::Add, box AST::Int(n), b) if n == &Zero::zero() => Some(*b.clone()),
        AST::Bin(Op::Add, a, box AST::Int(m)) if m == &Zero::zero() => Some(*a.clone()),

        AST::Bin(Op::Sub, box AST::Int(n), box AST::Int(m)) => Some(AST::Int(n - m)),
        AST::Bin(Op::Sub, box AST::Rat(n), box AST::Rat(m)) => Some(AST::Rat(n.clone() - m.clone())),
        AST::Bin(Op::Sub, box AST::Int(n), box AST::Rat(m)) => Some(AST::Rat(Rat::new(n.clone(), One::one()) - m.clone())),
        AST::Bin(Op::Sub, box AST::Rat(n), box AST::Int(m)) => Some(AST::Rat(n.clone() - m.clone())),

        AST::Bin(Op::Mul, box AST::Int(n), box AST::Int(m)) => Some(AST::Int(n * m)),
        AST::Bin(Op::Mul, box AST::Rat(n), box AST::Rat(m)) => Some(AST::Rat(n.clone() * m.clone())),
        AST::Bin(Op::Mul, box AST::Rat(n), box AST::Int(m)) => Some(AST::Rat(n.clone() * m.clone())),
        AST::Bin(Op::Mul, box AST::Int(n), box AST::Rat(m)) => Some(AST::Rat(m.clone() * n.clone())),
        AST::Bin(Op::Mul, box AST::Int(n), _) if n == &Zero::zero() => Some(AST::Int(Zero::zero())),
        AST::Bin(Op::Mul, box AST::Int(n), b) if n == &One::one() => Some(*b.clone()),
        AST::Bin(Op::Mul, _, box AST::Int(m)) if m == &Zero::zero() => Some(AST::Int(Zero::zero())),
        AST::Bin(Op::Mul, a, box AST::Int(m)) if m == &One::one() => Some(*a.clone()),

        AST::Bin(Op::And, box AST::Int(n), _) if n == &Zero::zero() => Some(AST::Int(Zero::zero())),
        AST::Bin(Op::And, box AST::Int(n), b) if n == &One::one() => Some(*b.clone()),
        AST::Bin(Op::And, _, box AST::Int(m)) if m == &Zero::zero() => Some(AST::Int(Zero::zero())),
        AST::Bin(Op::And, a, box AST::Int(m)) if m == &One::one() => Some(*a.clone()),

        AST::Bin(Op::Or, box AST::Int(n), b) if n == &Zero::zero() => Some(*b.clone()),
        AST::Bin(Op::Or, box AST::Int(n), _) if n == &One::one() => Some(AST::Int(One::one())),
        AST::Bin(Op::Or, a, box AST::Int(m)) if m == &Zero::zero() => Some(*a.clone()),
        AST::Bin(Op::Or, _, box AST::Int(m)) if m == &One::one() => Some(AST::Int(One::one())),

        AST::Bin(Op::Div, box AST::Int(n), box AST::Int(m)) if m != &Zero::zero() => {
            if n % m == Zero::zero() {
                Some(AST::Int(n / m))
            } else {
                Some(AST::Rat(Rat::new(n.clone(), m.clone())))
            }
        }

        AST::Bin(Op::Div, box AST::Rat(n), box AST::Rat(m)) => Some(AST::Rat(n.clone() / m.clone())),
        AST::Bin(Op::Div, box AST::Rat(n), box AST::Int(m)) => Some(AST::Rat(n.clone() / m.clone())),
        AST::Bin(Op::Div, box AST::Int(n), box AST::Rat(m)) => Some(AST::Rat(Rat::new(n.clone(), One::one()) / m.clone())),

        AST::Bin(Op::Mod, box AST::Int(n), box AST::Int(m)) if m != &Zero::zero() => Some(AST::Int(n % m)),
        AST::Bin(Op::Mod, box AST::Bin(Op::Mod, a, b), c) if b == c => Some(AST::Bin(Op::Mod, a.clone(), b.clone())),

        AST::Bin(Op::Exp, box AST::Int(n), box AST::Int(m)) => {
            if m >= &Zero::zero() {
                Some(AST::Int(Pow::pow(n.clone(), m.clone().to_biguint().unwrap())))
            } else {
                Some(AST::Rat(Rat::new(n.clone(), One::one()).pow(m)))
            }
        }
        AST::Bin(Op::Exp, box AST::Rat(n), box AST::Int(m)) => Some(AST::Rat(n.clone().pow(m))),

        // AST::Bin(Op::Prove, box AST::FinSet(assms), p) if assms.is_empty() => Some(*p.clone()),

        AST::Bin(Op::Equals, box AST::Int(n), box AST::Int(m)) => Some(truth_val(n == m)),
        AST::Bin(Op::Equals, box AST::Rat(n), box AST::Rat(m)) => Some(truth_val(n == m)),
        AST::Bin(Op::Equals, box AST::Int(n), box AST::Rat(m)) => Some(truth_val(&Rat::new(n.clone(), One::one()) == m)),
        AST::Bin(Op::Equals, box AST::Rat(n), box AST::Int(m)) => Some(truth_val(n == &Rat::new(m.clone(), One::one()))),
        AST::Bin(Op::Equals, a, b) if a == b => Some(AST::Int(One::one())),

        AST::Bin(Op::Lt, box AST::Int(n), box AST::Int(m)) => Some(truth_val(n < m)),
        AST::Bin(Op::Le, box AST::Int(n), box AST::Int(m)) => Some(truth_val(n <= m)),
        AST::Bin(Op::Gt, box AST::Int(n), box AST::Int(m)) => Some(truth_val(n > m)),
        AST::Bin(Op::Ge, box AST::Int(n), box AST::Int(m)) => Some(truth_val(n >= m)),
        AST::Bin(Op::NotEquals, box AST::Int(n), box AST::Int(m)) => Some(truth_val(n != m)),

        AST::Bin(Op::Lt, box AST::Rat(n), box AST::Rat(m)) => Some(truth_val(n < m)),
        AST::Bin(Op::Le, box AST::Rat(n), box AST::Rat(m)) => Some(truth_val(n <= m)),
        AST::Bin(Op::Gt, box AST::Rat(n), box AST::Rat(m)) => Some(truth_val(n > m)),
        AST::Bin(Op::Ge, box AST::Rat(n), box AST::Rat(m)) => Some(truth_val(n >= m)),
        AST::Bin(Op::NotEquals, box AST::Rat(n), box AST::Rat(m)) => Some(truth_val(n != m)),

        AST::App(box AST::Seq(_, implementation), xs) => {
            match &xs[0] {
                AST::Int(n) => match to_usize(&n) {
                    Ok(m) => implementation.borrow_mut().nth(m).ok(),
                    _ => None
                }
                _ => None
            }
        }

        AST::App(f, xs) => {
            if **f == AST::Var("subs".to_string()) {
                match &xs[..] {
                    [e, rep, pat] => Some(subs_expr(e.clone(), rep, pat)),
                    _ => None
                }
            } else if **f == AST::Var("∪".to_string()) {
                match (&xs[0], &xs[1]) {
                    (AST::FinSet(es1), AST::FinSet(es2)) => {
                        let mut new_elems = es1.clone();
                        new_elems.extend(es2.clone());
                        Some(AST::FinSet(new_elems))
                    }
                    _ => None
                }
            } else {
                None
            }
        }

        _ => None
    }
}

pub fn simplify_tree(expr : &AST) -> Option<AST> {
    let mut new_expr = expr.clone();
    for pos in expr.positions() {
        let sub_expr = at_mut(&mut new_expr, &pos, 0);
        if let Some(new) = simplify(sub_expr) {
            *sub_expr = new;
            return Some(new_expr);
        }
    }
    return None;
}

fn full_simplify(expr : AST) -> AST {
    let mut res = expr;
    loop {
        match simplify_tree(&res) {
            None => return res,
            Some(new_res) => res = new_res
        }
    }
}

struct TerminatingRewriter<'a> {
    rules : &'a [RewriteRule],
    exprs : Vec<AST>
}

impl <'a> TerminatingRewriter<'a> {
    fn new(rules : &'a [RewriteRule], expr : AST) -> TerminatingRewriter<'a> {
        return TerminatingRewriter {
            rules: rules,
            exprs: vec!(full_simplify(expr))
        };
    }
}

impl <'a> Iterator for TerminatingRewriter<'a> {
    type Item = AST;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.exprs.pop() {
                None => return None,

                Some(expr) => {
                    let mut changed = false;

                    for rule in self.rules {
                        for new_expr in rule.rewrite(&expr) {
                            if new_expr != expr {
                                self.exprs.push(full_simplify(new_expr));
                                changed = true;
                            }
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

struct Assignments {
    vars : Vec<String>,
    items : VecDeque<HashMap<String, AST>>,
    found_vals : HashMap<String, Vec<AST>>,
    var_its : HashMap<String, Box<dyn Iterator<Item=Result<AST, String>>>>,
    cur_idx : usize,
    done: bool
}

impl Assignments {
    fn from(var_doms : Vec<(String, AST)>) -> Result<Assignments, String> {
        let mut found_vals = HashMap::new();
        let mut var_its : HashMap<String, Box<dyn Iterator<Item=Result<AST, String>>>> = HashMap::new();
        let mut vars = Vec::new();
        // TODO: Eventually not all variables will be natural numbers...
        for (x, dom) in var_doms {
            found_vals.insert(x.clone(), vec!());
            var_its.insert(x.clone(), enumerate(dom)?);
            vars.push(x);
        }

        return Ok(Assignments {
            done: vars.is_empty(),
            vars: vars,
            items: VecDeque::new(),
            found_vals: found_vals,
            var_its: var_its,
            cur_idx: 0,
        });
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
            let x = &self.vars[self.cur_idx];
            match self.var_its.get_mut(x).unwrap().next() {
                Some(Ok(e)) => {
                    // Generate new items for the queue
                    self.items.extend(self.gen_product(self.cur_idx, &e, (self.cur_idx + 1) % self.vars.len()));
                    self.found_vals.get_mut(x).unwrap().push(e);
                    self.cur_idx = (self.cur_idx + 1) % self.var_its.len();
                    return self.next();
                }
                _ => (), // continue and increment to the next to get a new item
            }
            self.cur_idx = (self.cur_idx + 1) % self.var_its.len();
            if self.cur_idx == orig_idx {
                self.done = true;
                return None;
            }
        }
    }
}

pub fn fresh() -> String {
    unsafe {
        FRESH_COUNTER += 1;
        return format!("v{}", FRESH_COUNTER);
    }
}

pub fn setup_proof(assumptions : &Vec<AST>, expr : AST)
    -> (AST, Box<dyn Iterator<Item=HashMap<String, AST>>>) {

    let rhs_vars = vars(&expr);

    let relevant_assms : Vec<AST> = assumptions.iter()
        .filter(|assm| !vars(assm).is_disjoint(&rhs_vars))
        .cloned()
        .collect();

    let mut to_find = rhs_vars.clone();
    let mut var_doms = Vec::new();
    for assm in relevant_assms.iter() {
        if let AST::Bin(Op::Elem, box AST::Var(y), box dom) = assm {
            if to_find.contains(y.as_str()) {
                var_doms.push((y.clone(), dom.clone()));
                to_find.remove(y.as_str());
            }
        }
    }

    let to_prove = full_simplify(AST::Bin(Op::Prove, Box::new(AST::FinSet(relevant_assms)), Box::new(expr.clone())));

    if !to_find.is_empty() {
        println!("Not trying to generate counterexamples: Could not find domain for variables {:?}", to_find);
        return (to_prove, Box::new(std::iter::empty()));
    } else {
        match Assignments::from(var_doms) {
            Ok(it) => return (to_prove, Box::new(it)),
            Err(err) => {
                println!("Not trying to generate counterexamples: {}", err);
                return (to_prove, Box::new(std::iter::empty()));
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
            defs.insert("Prime".to_string(), AST::Seq("Prime".to_string(), Rc::new(RefCell::new(PrimeSeq::new()))));
            defs.insert("ℕ".to_string(), AST::Seq("ℕ".to_string(), Rc::new(RefCell::new(Naturals::new()))));
            defs.insert("ℤ".to_string(), AST::Seq("ℤ".to_string(), Rc::new(RefCell::new(Integers::new()))));
            defs.insert("ℚ".to_string(), AST::Seq("ℚ".to_string(), Rc::new(RefCell::new(Rationals::new()))));

            defs.insert("M".to_string(), AST::Builtin("M".to_string(), Rc::new(RefCell::new(MakeMatrixGen::new()))));

            let mut rules = Vec::new();
            let mut proof_rules = Vec::new();

            fn add_rule(rules : &mut Vec<RewriteRule>, proof_rules : &mut Vec<RewriteRule>, attrs : Vec<String>, lhs : AST, rhs : AST) {
                let mut to_subs = HashMap::new();
                for x in vars(&lhs) {
                    if x.starts_with('?') {
                        to_subs.insert(x.to_string(), AST::Var(format!("?{}", fresh())));
                    }
                }
                let fresh_lhs = subs(lhs, &to_subs);
                let fresh_rhs = subs(rhs, &to_subs);
                if !attrs.contains(&"proof rule".to_string()) {
                    rules.push(RewriteRule::new(fresh_lhs.clone(), fresh_rhs.clone()));
                }
                proof_rules.push(RewriteRule::new(fresh_lhs, fresh_rhs));
            }

            let mut assumptions = Vec::new();

            for expr in exprs {
                match &expr {
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

                    AST::Assumption(t) => assumptions.push(subs(*t, &defs)),

                    AST::Counterexample(t) => {
                        let (to_prove, mut assignment_it) = setup_proof(&assumptions, subs(*t, &defs));

                        let expr_start = now_millis();
                        let mut n = 0;
                        loop {
                            if let Some(a) = assignment_it.next() {
                                print!("\r{} tried... Trying: {}", n, format_assignment(&a));
                                if let Ok(AST::Int(n)) = eval(subs(to_prove.clone(), &a)) {
                                    if n == Zero::zero() {
                                        println!("\nFound counterexample: {}", format_assignment(&a));
                                        break;
                                    }
                                }
                            } else {
                                println!("No more counterexamples to generate!");
                                break;
                            }
                            n += 1;
                        }
                        let expr_end = now_millis();
                        println!("Elapsed: {}ms", expr_end - expr_start);
                    }

                    AST::Prove(t) => {
                        let (to_prove, mut assignment_it) = setup_proof(&assumptions, subs(*t, &defs));

                        let mut proof_tree = HashMap::new();
                        let mut todo = BinaryHeap::new();
                        let mut age = 0;
                        proof_tree.insert(to_prove.clone(), None);
                        todo.push((Reverse(0), subs(to_prove.clone(), &defs)));

                        let expr_start = now_millis();
                        loop {
                            if let Some(a) = assignment_it.next() {
                                // print!("... Trying: {} => {:?}", format_assignment(&a), eval(subs(to_prove.clone(), &a)));
                                print!("... Trying: {}", format_assignment(&a));
                                if let Ok(AST::Int(n)) = eval(subs(to_prove.clone(), &a)) {
                                    if n == Zero::zero() {
                                        println!("\nFound counterexample: {}", format_assignment(&a));
                                        break;
                                    }
                                }
                            }

                            match todo.pop() {
                                None => {
                                    println!("\nFailure!");
                                    break;
                                }

                                Some((_, AST::Bin(Op::Prove, assms, box AST::Int(n)))) if n == One::one() => {
                                    let new_t = AST::Bin(Op::Prove, assms, Box::new(AST::Int(n)));

                                    println!();
                                    println!("Found proof:");
                                    let mut cur_term = Some(new_t);
                                    while cur_term != None {
                                        println!("{}", cur_term.as_ref().unwrap());
                                        cur_term = proof_tree[&cur_term.unwrap()].clone();
                                    }

                                    // If we're proving some equality, add it as a rule.
                                    match to_prove {
                                        AST::Bin(Op::Equals, lhs, rhs) => {
                                            println!("Adding proof rule: {} => {}", lhs, rhs);
                                            add_rule(&mut rules, &mut proof_rules, vec!("proof rule".to_string()), *lhs, *rhs);
                                        }

                                        AST::Bin(Op::Prove, box AST::FinSet(mut assms), box AST::Bin(Op::Equals, lhs, rhs)) => {
                                            let new_lhs;
                                            let new_rhs;
                                            if assms.is_empty() {
                                                new_lhs = *lhs;
                                                new_rhs = *rhs;
                                            } else {
                                                let rest = AST::Var(fresh());

                                                let mut context = AST::App(Box::new(AST::Var("$elem".to_string())), vec!(assms[0].clone(), rest.clone()));
                                                for assm in &assms[1..assms.len()] {
                                                    context = AST::App(Box::new(AST::Var("$elem".to_string())), vec!(assm.clone(), context));
                                                }

                                                assms.push(AST::Bin(Op::Equals, lhs, rhs));
                                                let unbuild_context = AST::App(Box::new(AST::Var("∪".to_string())), vec!(AST::FinSet(assms), rest));

                                                let prop_var = Box::new(AST::Var(fresh()));
                                                new_lhs = AST::Bin(Op::Prove, Box::new(context), prop_var.clone());
                                                new_rhs = AST::Bin(Op::Prove, Box::new(unbuild_context), prop_var);
                                            }

                                            println!("Adding proof rule: {} => {}", new_lhs, new_rhs);
                                            add_rule(&mut rules, &mut proof_rules, vec!("proof rule".to_string()), new_lhs, new_rhs);
                                        }

                                        _ => ()
                                    }

                                    break;
                                }

                                Some((priority, new_t)) => {
                                    // println!("\n{} tried, {} left, priority {}: {}", proof_tree.len() - todo.len(), todo.len(), priority.0, new_t);
                                    print!("\r{} tried, {} left, priority {}", proof_tree.len() - todo.len(), todo.len(), priority.0);

                                    for rule in &proof_rules {
                                        for t in rule.rewrite(&new_t) {
                                            // let temp = t.clone();
                                            let new_expr = full_simplify(t);
                                            // println!("{} => {} =>* {}", new_t, temp, new_expr);
                                            if !proof_tree.contains_key(&new_expr) {
                                                proof_tree.insert(new_expr.clone(), Some(new_t.clone()));
                                                todo.push((Reverse(age + new_expr.size()), new_expr));
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        let expr_end = now_millis();
                        println!("Elapsed: {}ms", expr_end - expr_start);
                    }

                    AST::Rule(attrs, lhs, rhs) =>
                        add_rule(&mut rules, &mut proof_rules, attrs, subs(*lhs, &defs), subs(*rhs, &defs)),

                    _ => {
                        let expr_start = now_millis();
                        let mut exprs = HashSet::new();
                        for res in TerminatingRewriter::new(&rules, subs(expr, &defs)) {
                            if !exprs.contains(&res) {
                                println!("{}", res);
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


extern crate pest;
#[macro_use]
extern crate pest_derive;

use pest::Parser;
use pest::iterators::Pair;
use pest::prec_climber::{Assoc, Operator, PrecClimber};
use num_bigint::BigInt;
use num_traits::{Zero, One, Pow};

use std::collections::{HashSet, HashMap};
use std::env;
use std::fs;
use std::iter::Iterator;
use std::time::{SystemTime, UNIX_EPOCH};

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct LangParser;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum AST {
    Skip(),

    Definition(String, Box<AST>),

    Int(BigInt),

    Var(String),

    Builtin(String),

    FinSet(Vec<AST>),
    List(Vec<AST>),
    RangeSet(Box<AST>, Box<AST>, Box<AST>),
    Image(Box<AST>, Box<AST>),
    CompSet(Vec<(String, AST)>, Vec<AST>),

    Elem(Box<AST>, Box<AST>),

    Add(Box<AST>, Box<AST>),
    Sub(Box<AST>, Box<AST>),
    Mul(Box<AST>, Box<AST>),
    Div(Box<AST>, Box<AST>),
    Mod(Box<AST>, Box<AST>),
    Exp(Box<AST>, Box<AST>),

    Lt(Box<AST>, Box<AST>),
    Le(Box<AST>, Box<AST>),
    Gt(Box<AST>, Box<AST>),
    Ge(Box<AST>, Box<AST>),
    Equals(Box<AST>, Box<AST>),
    NotEquals(Box<AST>, Box<AST>),

    And(Box<AST>, Box<AST>),
    Or(Box<AST>, Box<AST>),

    App(Box<AST>, Vec<AST>),
    Function(Vec<String>, Box<AST>),

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
                "<" => Ok(AST::Lt(Box::new(lhs), Box::new(rhs))),
                "<=" => Ok(AST::Le(Box::new(lhs), Box::new(rhs))),
                ">" => Ok(AST::Gt(Box::new(lhs), Box::new(rhs))),
                ">=" => Ok(AST::Ge(Box::new(lhs), Box::new(rhs))),
                "=" => Ok(AST::Equals(Box::new(lhs), Box::new(rhs))),
                "!=" => Ok(AST::NotEquals(Box::new(lhs), Box::new(rhs))),
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
                                    Box::new(AST::Sub(Box::new(second), Box::new(start)))));
        }

        Rule::comp_set => {
            let mut it = pair.into_inner();

            let quant = match primary(it.next().unwrap())? {
                AST::Elem(x, dom) =>
                    match *x {
                        AST::Var(name) => Ok(vec!((name, *dom))),
                        other_x => Err(format!("Expected var on LHS of elem in CompSet, but got: {:?}", other_x))
                    }
                other => Err(format!("Expected Elem, but got: {:?}", other))
            }?;

            let mut clauses = Vec::new();
            for term in it {
                clauses.push(primary(term)?);
            }

            return Ok(AST::CompSet(quant, clauses));
        }

        Rule::bool_term => {
            let infix = |lhs : Result<AST, String>, op : Pair<Rule>, rhs : Result<AST, String>|
                match op.as_rule() {
                    Rule::elem => Ok(AST::Elem(Box::new(lhs?), Box::new(rhs?))),
                    Rule::and_op => Ok(AST::And(Box::new(lhs?), Box::new(rhs?))),
                    Rule::or_op => Ok(AST::Or(Box::new(lhs?), Box::new(rhs?))),
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
            return Ok(AST::Function(vec![arg], Box::new(body)));
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
            return Ok(AST::Function(args, Box::new(last.unwrap())));
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
                    Rule::add => Ok(AST::Add(Box::new(lhs?), Box::new(rhs?))),
                    Rule::sub => Ok(AST::Sub(Box::new(lhs?), Box::new(rhs?))),
                    Rule::mul => Ok(AST::Mul(Box::new(lhs?), Box::new(rhs?))),
                    Rule::div => Ok(AST::Div(Box::new(lhs?), Box::new(rhs?))),
                    Rule::mod_op => Ok(AST::Mod(Box::new(lhs?), Box::new(rhs?))),
                    Rule::exp => Ok(AST::Exp(Box::new(lhs?), Box::new(rhs?))),
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
            Operator::new(Rule::add, Assoc::Left)
            | Operator::new(Rule::sub, Assoc::Left),
            Operator::new(Rule::mul, Assoc::Left)
            | Operator::new(Rule::div, Assoc::Left)
            | Operator::new(Rule::mod_op, Assoc::Left),
            Operator::new(Rule::exp, Assoc::Right)));

    let bool_climber = PrecClimber::new(vec!(
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

        AST::FinSet(elems) => AST::FinSet(elems.into_iter().map(| e | subs(e, to_subs)).collect()),

        AST::List(elems) => AST::List(elems.into_iter().map(| e | subs(e, to_subs)).collect()),

        AST::RangeSet(start, end, step) =>
                AST::RangeSet(Box::new(subs(*start, to_subs)),
                              Box::new(subs(*end, to_subs)),
                              Box::new(subs(*step, to_subs))),

        AST::Builtin(name) => AST::Builtin(name),

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

        AST::Elem(a, b) => AST::Elem(Box::new(subs(*a, to_subs)),
                                     Box::new(subs(*b, to_subs))),

        AST::IfThenElse(cond, then_expr, else_expr) =>
                AST::IfThenElse(Box::new(subs(*cond, to_subs)),
                                Box::new(subs(*then_expr, to_subs)),
                                Box::new(subs(*else_expr, to_subs))),

        AST::Add(a, b) => AST::Add(Box::new(subs(*a, to_subs)),
                                   Box::new(subs(*b, to_subs))),
        AST::Sub(a, b) => AST::Sub(Box::new(subs(*a, to_subs)),
                                   Box::new(subs(*b, to_subs))),
        AST::Mul(a, b) => AST::Mul(Box::new(subs(*a, to_subs)),
                                   Box::new(subs(*b, to_subs))),
        AST::Div(a, b) => AST::Div(Box::new(subs(*a, to_subs)),
                                   Box::new(subs(*b, to_subs))),
        AST::Mod(a, b) => AST::Mod(Box::new(subs(*a, to_subs)),
                                   Box::new(subs(*b, to_subs))),
        AST::Exp(a, b) => AST::Exp(Box::new(subs(*a, to_subs)),
                                   Box::new(subs(*b, to_subs))),

        AST::Lt(a, b) => AST::Lt(Box::new(subs(*a, to_subs)),
                                 Box::new(subs(*b, to_subs))),
        AST::Le(a, b) => AST::Le(Box::new(subs(*a, to_subs)),
                                 Box::new(subs(*b, to_subs))),
        AST::Gt(a, b) => AST::Gt(Box::new(subs(*a, to_subs)),
                                 Box::new(subs(*b, to_subs))),
        AST::Ge(a, b) => AST::Ge(Box::new(subs(*a, to_subs)),
                                 Box::new(subs(*b, to_subs))),
        AST::Equals(a, b) => AST::Equals(Box::new(subs(*a, to_subs)),
                                         Box::new(subs(*b, to_subs))),
        AST::NotEquals(a, b) => AST::NotEquals(Box::new(subs(*a, to_subs)),
                                               Box::new(subs(*b, to_subs))),

        AST::And(a, b) => AST::And(Box::new(subs(*a, to_subs)),
                                   Box::new(subs(*b, to_subs))),
        AST::Or(a, b) => AST::Or(Box::new(subs(*a, to_subs)),
                                 Box::new(subs(*b, to_subs))),

        AST::App(f, args) => AST::App(Box::new(subs(*f, to_subs)),
                                      args.into_iter().map(| e | subs(e, to_subs)).collect()),

        AST::Function(formal_args, body) => {
            let mut new_subs = to_subs.clone();
            for formal_arg in &formal_args {
                new_subs.remove(formal_arg.as_str());
            }
            return AST::Function(formal_args, Box::new(subs(*body, &new_subs)));
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
        AST::Lt(_, _) => true,
        AST::Le(_, _) => true,
        AST::Gt(_, _) => true,
        AST::Ge(_, _) => true,
        AST::Equals(_, _) => true,
        AST::NotEquals(_, _) => true,

        AST::IfThenElse(_, then_expr, else_expr) => is_finite(then_expr) && is_finite(else_expr),

        AST::Factorial(n) => is_finite(n),
        AST::Negate(n) => is_finite(n),
        AST::Complement(b) => is_finite(b),

        // TODO: not really right, we need to make sure every element of s is finite too...
        AST::Sum(s) => is_finite(s),

        AST::Image(_, arg) => is_finite(arg),
        AST::Add(a, b) => is_finite(a) && is_finite(b),
        AST::Sub(a, b) => is_finite(a) && is_finite(b),
        AST::Mul(a, b) => is_finite(a) && is_finite(b),
        AST::Div(a, b) => is_finite(a) && is_finite(b),
        AST::Mod(a, b) => is_finite(a) && is_finite(b),
        AST::Exp(a, b) => is_finite(a) && is_finite(b),

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

        AST::Add(a, b) => enumerate(eval(AST::Add(a, b))?),
        AST::Sub(a, b) => enumerate(eval(AST::Sub(a, b))?),
        AST::Mul(a, b) => enumerate(eval(AST::Mul(a, b))?),
        AST::Div(a, b) => enumerate(eval(AST::Div(a, b))?),
        AST::Mod(a, b) => enumerate(eval(AST::Mod(a, b))?),

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

pub fn eval_comp_set(i : usize,
                     to_subs : &mut HashMap<String, AST>,
                     var_doms : &Vec<(String, AST)>,
                     clauses : &Vec<AST>) -> Result<Vec<AST>, String> {
    let (x, dom) = &var_doms[i];
    let mut vals = Vec::new();

    if i == var_doms.len() - 1 {
        for x_val in enumerate(dom.clone())? {
            to_subs.insert(x.clone(), x_val?);
            let mut res = true;
            for clause in clauses {
                if as_int(eval(subs(clause.clone(), to_subs))?)? == Zero::zero() {
                    res = false;
                    break;
                }
            }
            if res {
                vals.push(make_val(to_subs, var_doms));
            }
        }
        return Ok(vals);
    }

    for x_val in enumerate(dom.clone())? {
        to_subs.insert(x.clone(), x_val?);
        for val in eval_comp_set(i + 1, to_subs, var_doms, clauses)? {
            vals.push(val);
        }
    }

    return Ok(vals);
}

pub fn eval(expr : AST) -> Result<AST, String> {
    match expr {
        AST::Int(n) => Ok(AST::Int(n)),

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

        AST::CompSet(var_doms, clauses) =>
            Ok(AST::FinSet(eval_comp_set(0, &mut HashMap::new(), &var_doms, &clauses)?)),

        AST::IfThenElse(cond, then_expr, else_expr) => {
            if as_int(eval(*cond)?)? != Zero::zero() {
                return eval(*then_expr);
            } else {
                return eval(*else_expr);
            }
        }

        AST::Add(a, b) => {
            return Ok(AST::Int(as_int(eval(*a)?)? + as_int(eval(*b)?)?));
        }

        AST::Sub(a, b) => {
            return Ok(AST::Int(as_int(eval(*a)?)? - as_int(eval(*b)?)?));
        }

        AST::Mul(a, b) => {
            return Ok(AST::Int(as_int(eval(*a)?)? * as_int(eval(*b)?)?));
        }

        AST::Mod(a, b) => {
            return Ok(AST::Int(as_int(eval(*a)?)? % as_int(eval(*b)?)?));
        }

        AST::Exp(a, b) => {
            return match as_int(eval(*b)?)?.to_biguint() {
                Some(n) => Ok(AST::Int(Pow::pow(as_int(eval(*a)?)?, n))),
                None => Err("Cannot raise integer to negative power!".to_string())
            };
        }

        AST::Equals(a, b) => {
            if eval(*a)? == eval(*b)? {
                return Ok(AST::Int(One::one()));
            } else {
                return Ok(AST::Int(Zero::zero()));
            }
        }

        AST::NotEquals(a, b) => {
            if eval(*a)? != eval(*b)? {
                return Ok(AST::Int(One::one()));
            } else {
                return Ok(AST::Int(Zero::zero()));
            }
        }

        AST::Lt(a, b) => {
            if as_int(eval(*a)?)? < as_int(eval(*b)?)? {
                return Ok(AST::Int(One::one()));
            } else {
                return Ok(AST::Int(Zero::zero()));
            }
        }

        AST::Le(a, b) => {
            if as_int(eval(*a)?)? <= as_int(eval(*b)?)? {
                return Ok(AST::Int(One::one()));
            } else {
                return Ok(AST::Int(Zero::zero()));
            }
        }

        AST::Gt(a, b) => {
            if as_int(eval(*a)?)? > as_int(eval(*b)?)? {
                return Ok(AST::Int(One::one()));
            } else {
                return Ok(AST::Int(Zero::zero()));
            }
        }

        AST::Ge(a, b) => {
            if as_int(eval(*a)?)? >= as_int(eval(*b)?)? {
                return Ok(AST::Int(One::one()));
            } else {
                return Ok(AST::Int(Zero::zero()));
            }
        }

        AST::Or(a, b) => {
            let lval = as_int(eval(*a)?)?;
            if lval != Zero::zero() {
                return Ok(AST::Int(lval));
            } else {
                return eval(*b);
            }
        }

        AST::And(a, b) => {
            let lval = as_int(eval(*a)?)?;

            if lval == Zero::zero() {
                return Ok(AST::Int(lval));
            } else {
                return eval(*b);
            }
        }

        AST::App(func, args) => {
            match eval(*func)? {
                AST::Function(formal_args, body) => {
                    let mut to_subs = HashMap::new();
                    for (formal, actual) in formal_args.into_iter().zip(args) {
                        to_subs.insert(formal, actual);
                    }
                    return eval(subs(*body, &to_subs));
                }

                AST::Builtin(name) => {
                    match name.as_str() {
                        "set" => {
                            let mut res = Vec::new();
                            for val in enumerate(args[0].clone())? {
                                res.push(val?);
                            }
                            return Ok(AST::FinSet(res));
                        }

                        "list" => {
                            let mut res = Vec::new();
                            for val in enumerate(args[0].clone())? {
                                res.push(val?);
                            }
                            return Ok(AST::List(res));
                        }

                        _ => Err(format!("Unknown Builtin: {}", name))
                    }
                }

                res => Err(format!("Expected a function in function application expression, got {:?}", res))
            }
        }

        AST::Var(x) => Ok(AST::Var(x)),

        AST::Function(formal_args, body) => Ok(AST::Function(formal_args, body)),

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
    println!("Parse elapsed: {}ms", parse_end - parse_start);

    match parsed {
        Ok(exprs) => {
            let mut defs = HashMap::new();

            for expr in exprs {
                // println!("{:?}", defs.clone());
                match expr.clone() {
                    AST::Skip() => continue,
                    other => println!("> {:?}", other)
                }

                match expr {
                    AST::Definition(name, body) => {
                        defs.insert(name, subs(*body, &defs));
                    }

                    _ => {
                        let expr_start = now_millis();
                        println!("{:?}", eval(subs(expr, &defs)));
                        let expr_end = now_millis();
                        println!("Elapsed: {}ms", expr_end - expr_start);
                    }
                }
            }
        }
        Err(err) => println!("Error: {}", err)
    }
}


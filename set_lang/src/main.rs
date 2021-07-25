extern crate pest;
#[macro_use]
extern crate pest_derive;

use pest::Parser;
use pest::error::Error;
use pest::iterators::Pair;
use num_bigint::BigInt;
use num_traits::{Zero, One};
use num_traits::Pow;

use std::collections::{HashSet, HashMap};
use std::env;
use std::fs;

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct LangParser;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum AST {
    Skip(),

    Definition(String, Box<AST>),

    Int(BigInt),

    Var(String),

    FinSet(Vec<AST>),
    List(Vec<AST>),
    RangeSet(Box<AST>, Box<AST>, Box<AST>),

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
    Function(Vec<AST>, Box<AST>),
    Image(Box<AST>, Box<AST>),

    Factorial(Box<AST>),
    Negate(Box<AST>),
    Complement(Box<AST>)
}

pub fn to_ast(pair : Pair<Rule>) -> Result<AST, String> {
    println!("Rule:    {:?}", pair.as_rule());
    println!("Span:    {:?}", pair.as_span());
    println!("Text:    {:?}", pair.as_str());
    match pair.as_rule() {
        Rule::definition => {
            let mut it = pair.into_inner();
            let var = match to_ast(it.next().unwrap())? {
                AST::Var(x) => Ok(x),
                expr => Err(format!("Unexpected term {:?} on LHS of definition", expr))
            }?;
            let body = to_ast(it.next().unwrap())?;

            return Ok(AST::Definition(var, Box::new(body)));
        }

        Rule::compare => {
            let mut it = pair.into_inner();
            let lhs = to_ast(it.next().unwrap())?;
            let op = to_ast(it.next().unwrap())?;
            let rhs = to_ast(it.next().unwrap())?;

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

        Rule::int => {
            return match BigInt::parse_bytes(pair.as_str().as_bytes(), 10) {
                Some(n) => Ok(AST::Int(n)),
                None => Err(format!("Failed to parse string '{}' as integer", pair.as_str()))
            }
        }

        Rule::finset => {
            let mut elems = Vec::new();
            for elem in pair.into_inner() {
                elems.push(to_ast(elem)?);
            }
            return Ok(AST::FinSet(elems));
        }

        Rule::rangeset => {
            let mut it = pair.into_inner();
            let start = to_ast(it.next().unwrap())?;
            let end = to_ast(it.next().unwrap())?;
            return Ok(AST::RangeSet(Box::new(start), Box::new(end), Box::new(AST::Int(One::one()))));
        }

        Rule::rangeset_step => {
            let mut it = pair.into_inner();
            let start = to_ast(it.next().unwrap())?;
            let second = to_ast(it.next().unwrap())?;
            let end = to_ast(it.next().unwrap())?;
            return Ok(AST::RangeSet(Box::new(start.clone()),
                                    Box::new(end),
                                    Box::new(AST::Sub(Box::new(second), Box::new(start)))));
        }

        Rule::list => {
            let mut elems = Vec::new();
            for elem in pair.into_inner() {
                elems.push(to_ast(elem)?);
            }
            return Ok(AST::List(elems));
        }

        Rule::call => {
            let mut it = pair.into_inner();
            let func = to_ast(it.next().unwrap())?;
            let mut args = Vec::new();

            for arg in it {
                args.push(to_ast(arg)?);
            }

            return Ok(AST::App(Box::new(func), args));
        }

        Rule::var => Ok(AST::Var(pair.as_str().to_string())),

        Rule::fun_single_arg => {
            let mut it = pair.into_inner();
            let arg = to_ast(it.next().unwrap())?;
            let body = to_ast(it.next().unwrap())?;
            return Ok(AST::Function(vec![arg], Box::new(body)));
        }

        Rule::fun_multi_arg => {
            let mut args = Vec::new();
            for arg in pair.into_inner() {
                args.push(to_ast(arg)?);
            }
            let last = args.pop().unwrap();
            return Ok(AST::Function(args, Box::new(last)));
        }

        Rule::image => {
            let mut it = pair.into_inner();
            let f = to_ast(it.next().unwrap())?;
            let arg = to_ast(it.next().unwrap())?;
            return Ok(AST::Image(Box::new(f), Box::new(arg)));
        }

        Rule::factorial => {
            let mut it = pair.into_inner();
            let arg = to_ast(it.next().unwrap())?;
            return Ok(AST::Factorial(Box::new(arg)));
        }

        Rule::negate => {
            let mut it = pair.into_inner();
            let arg = to_ast(it.next().unwrap())?;
            return Ok(AST::Negate(Box::new(arg)));
        }

        Rule::complement => {
            let mut it = pair.into_inner();
            let arg = to_ast(it.next().unwrap())?;
            return Ok(AST::Complement(Box::new(arg)));
        }

        Rule::EOI => Ok(AST::Skip()),

        Rule::and_op => {
            let mut it = pair.into_inner();
            let mut res = to_ast(it.next().unwrap())?;

            for term in it {
                res = AST::And(Box::new(res), Box::new(to_ast(term)?));
            }

            return Ok(res);
        }

        Rule::or_op => {
            let mut it = pair.into_inner();
            let mut res = to_ast(it.next().unwrap())?;

            for term in it {
                res = AST::Or(Box::new(res), Box::new(to_ast(term)?));
            }

            return Ok(res);
        }

        Rule::add => {
            let mut it = pair.into_inner();
            let mut res = to_ast(it.next().unwrap())?;

            for term in it {
                res = AST::Add(Box::new(res), Box::new(to_ast(term)?));
            }

            return Ok(res);
        }

        Rule::sub => {
            let mut it = pair.into_inner();
            let mut res = to_ast(it.next().unwrap())?;

            for term in it {
                res = AST::Sub(Box::new(res), Box::new(to_ast(term)?));
            }

            return Ok(res);
        }

        Rule::mul => {
            let mut it = pair.into_inner();
            let mut res = to_ast(it.next().unwrap())?;

            for term in it {
                res = AST::Mul(Box::new(res), Box::new(to_ast(term)?));
            }

            return Ok(res);
        }

        Rule::div => {
            let mut it = pair.into_inner();
            let mut res = to_ast(it.next().unwrap())?;

            for term in it {
                res = AST::Div(Box::new(res), Box::new(to_ast(term)?));
            }

            return Ok(res);
        }

        Rule::mod_term => {
            let mut it = pair.into_inner();
            let mut res = to_ast(it.next().unwrap())?;

            for term in it {
                res = AST::Mod(Box::new(res), Box::new(to_ast(term)?));
            }

            return Ok(res);
        }

        Rule::exp => {
            let mut it = pair.into_inner();
            let mut res = to_ast(it.next().unwrap())?;

            for term in it {
                res = AST::Exp(Box::new(res), Box::new(to_ast(term)?));
            }

            return Ok(res);
        }

        Rule::is => Ok(AST::Skip()),

        _ => Err(format!("Unimplemented: {:?}", pair))
    }
}

pub fn parse(source : &str) -> Result<Vec<AST>, String> {
    let pairs = LangParser::parse(Rule::main, source).expect("parse error");

    let mut res = Vec::new();

    for pair in pairs {
        res.push(to_ast(pair)?);
    }

    return Ok(res);
}

pub fn as_int(expr : AST) -> Result<BigInt, String> {
    match expr {
        AST::Int(n) => Ok(n),
        _ => Err(format!("Expected integer but got {:?}", expr))
    }
}

pub fn subs(expr : AST, to_subs : &AST, var : &AST) -> AST {
    if expr == *var {
        return to_subs.clone();
    }

    match expr {
        AST::Definition(name, body) => AST::Definition(name, Box::new(subs(*body, to_subs, var))),

        AST::FinSet(elems) => AST::FinSet(elems.into_iter().map(| e | subs(e, to_subs, var)).collect()),

        AST::List(elems) => AST::List(elems.into_iter().map(| e | subs(e, to_subs, var)).collect()),

        AST::RangeSet(start, end, step) => AST::RangeSet(Box::new(subs(*start, to_subs, var)),
                                                         Box::new(subs(*end, to_subs, var)),
                                                         Box::new(subs(*step, to_subs, var))),

        AST::Add(a, b) => AST::Add(Box::new(subs(*a, to_subs, var)),
                                   Box::new(subs(*b, to_subs, var))),
        AST::Sub(a, b) => AST::Sub(Box::new(subs(*a, to_subs, var)),
                                   Box::new(subs(*b, to_subs, var))),
        AST::Mul(a, b) => AST::Mul(Box::new(subs(*a, to_subs, var)),
                                   Box::new(subs(*b, to_subs, var))),
        AST::Div(a, b) => AST::Div(Box::new(subs(*a, to_subs, var)),
                                   Box::new(subs(*b, to_subs, var))),
        AST::Mod(a, b) => AST::Mod(Box::new(subs(*a, to_subs, var)),
                                   Box::new(subs(*b, to_subs, var))),
        AST::Exp(a, b) => AST::Exp(Box::new(subs(*a, to_subs, var)),
                                   Box::new(subs(*b, to_subs, var))),

        AST::Lt(a, b) => AST::Lt(Box::new(subs(*a, to_subs, var)),
                                 Box::new(subs(*b, to_subs, var))),
        AST::Le(a, b) => AST::Le(Box::new(subs(*a, to_subs, var)),
                                 Box::new(subs(*b, to_subs, var))),
        AST::Gt(a, b) => AST::Gt(Box::new(subs(*a, to_subs, var)),
                                 Box::new(subs(*b, to_subs, var))),
        AST::Ge(a, b) => AST::Ge(Box::new(subs(*a, to_subs, var)),
                                 Box::new(subs(*b, to_subs, var))),
        AST::Equals(a, b) => AST::Equals(Box::new(subs(*a, to_subs, var)),
                                         Box::new(subs(*b, to_subs, var))),
        AST::NotEquals(a, b) => AST::NotEquals(Box::new(subs(*a, to_subs, var)),
                                               Box::new(subs(*b, to_subs, var))),

        AST::And(a, b) => AST::And(Box::new(subs(*a, to_subs, var)),
                                   Box::new(subs(*b, to_subs, var))),
        AST::Or(a, b) => AST::Or(Box::new(subs(*a, to_subs, var)),
                                 Box::new(subs(*b, to_subs, var))),

        AST::App(f, args) => AST::App(Box::new(subs(*f, to_subs, var)),
                                      args.into_iter().map(| e | subs(e, to_subs, var)).collect()),

        AST::Function(formal_args, body) => {
            if !formal_args.contains(var) {
                AST::Function(formal_args, Box::new(subs(*body, to_subs, var)))
            } else {
                AST::Function(formal_args, body)
            }
        }

        AST::Image(f, arg) => AST::Image(Box::new(subs(*f, to_subs, var)),
                                         Box::new(subs(*arg, to_subs, var))),

        AST::Factorial(arg) => AST::Factorial(Box::new(subs(*arg, to_subs, var))),
        AST::Negate(arg) => AST::Negate(Box::new(subs(*arg, to_subs, var))),
        AST::Complement(arg) => AST::Complement(Box::new(subs(*arg, to_subs, var))),

        AST::Int(n) => AST::Int(n),
        AST::Var(x) => AST::Var(x),
        AST::Skip() => AST::Skip()
    }
}

pub fn subs_many(expr : AST, subs_pairs : Vec<(&AST, &AST)>) -> AST {
    let mut new_expr = expr;

    for (to_subs, var) in subs_pairs {
        new_expr = subs(new_expr, to_subs, var);
    }

    return new_expr;
}

pub fn subs_many_owned(expr : AST, subs_pairs : &Vec<(AST, AST)>) -> AST {
    let mut new_expr = expr;

    for (to_subs, var) in subs_pairs {
        new_expr = subs(new_expr, to_subs, var);
    }

    return new_expr;
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
        AST::Skip() => true,
        AST::Lt(_, _) => true,
        AST::Le(_, _) => true,
        AST::Gt(_, _) => true,
        AST::Ge(_, _) => true,
        AST::Equals(_, _) => true,
        AST::NotEquals(_, _) => true,

        AST::Factorial(n) => is_finite(n),
        AST::Negate(n) => is_finite(n),
        AST::Image(_, arg) => is_finite(arg),
        AST::Add(a, b) => is_finite(a) && is_finite(b),
        AST::Sub(a, b) => is_finite(a) && is_finite(b),
        AST::Mul(a, b) => is_finite(a) && is_finite(b),
        AST::Div(a, b) => is_finite(a) && is_finite(b),
        AST::Mod(a, b) => is_finite(a) && is_finite(b),
        AST::Exp(a, b) => is_finite(a) && is_finite(b),
        AST::RangeSet(start, end, _) => is_finite(start) && is_finite(end),

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

pub fn enumerate(expr : AST) -> Result<Box<dyn std::iter::Iterator<Item=Result<AST, String>>>, String> {
    match expr {
        AST::FinSet(elems) => Ok(Box::new(elems.into_iter().map(Ok))),
        AST::List(elems) => Ok(Box::new(elems.into_iter().map(Ok))),

        AST::RangeSet(start, end, step) => {
            let start_val = as_int(eval(*start)?)?;
            let end_val = as_int(eval(*end)?)?;
            let step_val = as_int(eval(*step)?)?;
            return Ok(Box::new(RangeSetIterator::new(start_val, end_val, step_val).map(Ok)));
        }

        AST::Add(a, b) => enumerate(eval(AST::Add(a, b))?),
        AST::Mul(a, b) => enumerate(eval(AST::Mul(a, b))?),
        AST::Sub(a, b) => enumerate(eval(AST::Sub(a, b))?),
        AST::App(f, args) => enumerate(eval(AST::App(f, args))?),

        AST::Image(f, arg) => {
            let func = eval(*f)?;
            return Ok(Box::new(
                        enumerate(*arg)?
                        .map(move |x| eval(AST::App(Box::new(func.clone()), vec!(x?))))));
        }

        expr => Err(format!("Cannot enumerate: {:?}", expr)),
    }
}

pub fn eval(expr : AST) -> Result<AST, String> {
    match expr {
        AST::Skip() => Ok(AST::Skip()),

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
                    let mut new_body = *body;
                    for (formal, actual) in formal_args.iter().zip(args) {
                        new_body = subs(new_body, &actual, &formal);
                    }
                    return eval(new_body);
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
                vals.push(eval(AST::App(Box::new(func.clone()), vec!(val?.clone())))?);
            }

            if arg_is_list && arg_is_finite {
                return Ok(AST::List(vals));
            } else {
                return Ok(AST::FinSet(vals));
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

fn main() {
    let args: Vec<String> = env::args().collect();
    let contents = fs::read_to_string(&args[1])
        .expect("Something went wrong reading the file");

    match parse(&contents) {
        Ok(exprs) => {
            let mut defs = Vec::new();

            for expr in exprs {
                // println!("{:?}", defs.clone());
                println!("> {:?}", expr.clone());
                match expr {
                    AST::Definition(name, body) => {
                        defs.push((subs_many_owned(*body, &defs), AST::Var(name)));
                    }

                    _ => {
                        println!("{:?}", eval(subs_many_owned(expr, &defs)));
                    }
                }
            }
        }
        Err(err) => println!("Error: {}", err)
    }
}


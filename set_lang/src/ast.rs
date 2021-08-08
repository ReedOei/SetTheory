use num_bigint::{BigInt, ToBigUint};
use num_traits::{Zero, One, Pow};
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::fmt::Debug;
use std::rc::Rc;

use crate::math::{Rat, Sequence};

pub trait BuiltinFunc {
    fn apply(&self, args : Vec<AST>) -> Result<AST, String>;
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
    Counterexample(Box<AST>),

    Int(BigInt),
    Rat(Rat),

    Var(String),

    Seq(String,
        #[educe(Debug(ignore))]
        #[educe(Hash(ignore))]
        #[educe(Eq(ignore))]
        #[educe(PartialEq(ignore))]
        #[educe(Ord(ignore))]
        #[educe(PartialOrd(ignore))]
        Rc<RefCell<dyn Sequence>>),

    Builtin(String,
        #[educe(Debug(ignore))]
        #[educe(Hash(ignore))]
        #[educe(Eq(ignore))]
        #[educe(PartialEq(ignore))]
        #[educe(Ord(ignore))]
        #[educe(PartialOrd(ignore))]
        Rc<RefCell<dyn BuiltinFunc>>),

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

impl Default for AST {
    fn default() -> AST {
        AST::Skip()
    }
}

impl fmt::Display for AST {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AST::Skip() => write!(f, "skip"),
            AST::Int(n) => write!(f, "{}", n),
            AST::Rat(r) => write!(f, "{}", r),
            AST::Var(x) => write!(f, "{}", x),
            AST::Definition(name, body) => write!(f, "Let {} := {}", name, body),
            AST::Rule(attrs, lhs, rhs) => write!(f, "Rule {} => {} {:?}", lhs, rhs, attrs),
            AST::Assumption(t) => write!(f, "Assume {}", t),
            AST::Prove(t) => write!(f, "Prove {}", t),
            AST::Counterexample(t) => write!(f, "Counterexample {}", t),
            AST::Seq(name, _) => write!(f, "{}", name),
            AST::Builtin(name, _) => write!(f, "{}", name),
            AST::FinSet(elems) => {
                let mut s = String::new();
                s.push('{');
                if !elems.is_empty() {
                    for e in &elems[..elems.len() - 1] {
                        s.push_str(format!("{}, ", e).as_str());
                    }
                    s.push_str(format!("{}", elems[elems.len() - 1]).as_str());
                }
                s.push('}');
                write!(f, "{}", s)
            }
            AST::List(elems) => {
                let mut s = String::new();
                s.push('[');
                if !elems.is_empty() {
                    for e in &elems[..elems.len() - 1] {
                        s.push_str(format!("{}, ", e).as_str());
                    }
                    s.push_str(format!("{}", elems[elems.len() - 1]).as_str());
                }
                s.push(']');
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
                s.push('{');
                s.push_str(var_doms.iter().map(|(x, dom)| format!("{} ∈ {}", x, dom)).collect::<Vec<String>>().join(", ").as_str());
                s.push_str(" : ");
                s.push_str(clauses.iter().map(|clause| format!("{}", clause)).collect::<Vec<String>>().join(", ").as_str());
                s.push('}');
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


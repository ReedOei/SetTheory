use num_bigint::{BigInt, ToBigUint};
use num_traits::{Zero, One, Pow};

use std::hash::Hash;
use std::ops;
use std::fmt;

use crate::ast::AST;

pub trait Sequence {
    fn nth(&mut self, n : usize) -> Result<AST, String>;
    fn increasing(&self) -> bool;
    fn index_of(&mut self, v : AST) -> Option<usize>;
}

pub struct Naturals;
impl Naturals {
    pub fn new() -> Naturals {
        return Naturals;
    }
}

#[derive(Debug, Clone)]
pub struct Rat {
    pub n : BigInt,
    pub d : BigInt
}

impl PartialEq for Rat {
    fn eq(&self, other : &Rat) -> bool {
        return self.n.clone() * other.d.clone() == other.n.clone() * self.d.clone();
    }
}

impl PartialOrd for Rat {
    fn partial_cmp(&self, other : &Rat) -> Option<std::cmp::Ordering> {
        return (self.n.clone() * other.d.clone()).partial_cmp(&(other.n.clone() * self.d.clone()));
    }
}

impl Eq for Rat {

}

impl Ord for Rat {
    fn cmp(&self, other: &Rat) -> std::cmp::Ordering {
        return (self.n.clone() * other.d.clone()).cmp(&(other.n.clone() * self.d.clone()));
    }
}

impl Hash for Rat {
    fn hash<H>(&self, state : &mut H) where H: std::hash::Hasher {
        let r = self.clone().simplify();
        r.n.hash(state);
        r.d.hash(state);
    }
}

impl fmt::Display for Rat {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}/{}", self.n, self.d)
    }
}

pub fn gcd(a : BigInt, b : BigInt) -> BigInt {
    let mut x = a;
    let mut y = b;
    while y != Zero::zero() {
        let temp = y.clone();
        y = x % y;
        x = temp;
    }
    return x;
}

impl Rat {
    pub fn new(n : BigInt, d : BigInt) -> Rat {
        let r = Rat { n, d };
        return r.simplify();
    }

    pub fn from_usize(n : usize) -> Rat {
        return Rat::new(BigInt::from(n), One::one());
    }

    pub fn simplify(mut self) -> Rat {
        let g = gcd(self.n.clone(), self.d.clone());
        self.n /= g.clone();
        self.d /= g;
        if self.d < Zero::zero() && self.n < Zero::zero() {
            std::mem::swap(&mut self.n, &mut self.d);
        }
        return self;
    }

    pub fn pow(mut self, a : &BigInt) -> Rat {
        if a > &Zero::zero() {
            let mut n : BigInt = One::one();
            let orig_n = self.n.clone();
            let orig_d = self.d.clone();
            while &n < a {
                self.n *= orig_n.clone();
                self.d *= orig_d.clone();
                n += 1;
            }
            return self;
        } else if a < &Zero::zero() {
            std::mem::swap(&mut self.n, &mut self.d);
            return self.pow(&-a);
        } else {
            return Rat { n: One::one(), d: One::one() };
        }
    }
}

impl ops::Add<BigInt> for Rat {
    type Output = Rat;

    fn add(self, b : BigInt) -> Rat {
        return Rat::new(self.n + b * self.d.clone(), self.d);
    }
}

impl ops::Sub<BigInt> for Rat {
    type Output = Rat;

    fn sub(self, b : BigInt) -> Rat {
        return Rat::new(self.n - b * self.d.clone(), self.d);
    }
}

impl ops::Mul<BigInt> for Rat {
    type Output = Rat;

    fn mul(self, b : BigInt) -> Rat {
        return Rat::new(self.n * b, self.d);
    }
}

impl ops::Div<BigInt> for Rat {
    type Output = Rat;

    fn div(self, b : BigInt) -> Rat {
        return Rat::new(self.n, self.d * b);
    }
}

impl ops::Add<Rat> for Rat {
    type Output = Rat;

    fn add(self, b : Rat) -> Rat {
        return Rat::new(self.n * b.d.clone() + b.n * self.d.clone(), self.d * b.d);
    }
}

impl ops::Sub<Rat> for Rat {
    type Output = Rat;

    fn sub(self, b : Rat) -> Rat {
        return Rat::new(self.n * b.d.clone() - b.n * self.d.clone(), self.d * b.d);
    }
}

impl ops::Mul<Rat> for Rat {
    type Output = Rat;

    fn mul(self, b : Rat) -> Rat {
        return Rat::new(self.n * b.n, self.d * b.d);
    }
}

impl ops::Div<Rat> for Rat {
    type Output = Rat;

    fn div(self, b : Rat) -> Rat {
        return Rat::new(self.n * b.d, self.d * b.n);
    }
}

impl ops::MulAssign<Rat> for Rat {
    fn mul_assign(&mut self, b : Rat) {
        self.n *= b.n;
        self.d *= b.d;
    }
}

impl ops::Neg for Rat {
    type Output = Rat;

    fn neg(self) -> Rat {
        return Rat { n: -self.n, d: self.d };
    }
}


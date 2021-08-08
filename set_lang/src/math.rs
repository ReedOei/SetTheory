use num_bigint::{BigInt, ToBigUint};
use num_traits::{Zero, One, Pow};

use std::collections::{BinaryHeap, HashSet, HashMap, VecDeque};
use std::cmp::{max, Ordering};
use std::hash::Hash;
use std::ops;
use std::fmt;

use crate::ast::{AST, as_int};

pub fn to_usize(n : &BigInt) -> Result<usize, String> {
    match ToBigUint::to_biguint(n) {
        Some(m) => Ok(m.iter_u64_digits()
            .map(|d| d as usize)
            .fold(0, |accum, d| accum * (std::u64::MAX as usize) + d)),
        None => Err(format!("Could not convert {:?} to usize", n))
    }
}

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

pub struct Integers;
impl Integers {
    pub fn new() -> Integers {
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
    pub fn new() -> Rationals {
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
    pub fn new() -> PrimeSeq {
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

pub struct PrimeIt {
    n : usize,
    seq : PrimeSeq
}

pub fn primes() -> PrimeIt {
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

pub struct Factors {
    n : BigInt,
    m : usize,
    ps : PrimeSeq
}

pub fn factor(n : BigInt) -> Factors {
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



extern crate pest;
#[macro_use]
extern crate pest_derive;

use pest::Parser;
use pest::error::Error;
use num_bigint::BigInt;

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct LangParser;

pub enum AST {
    Int(BigInt)
}

pub fn parse(source: &str) { // -> Result<Vec<AST>, Error<Rule>> {
    let pairs = LangParser::parse(Rule::main, source).unwrap();

    for pair in pairs {
        println!("Rule:    {:?}", pair.as_rule());
        println!("Span:    {:?}", pair.as_span());
        println!("Text:    {}", BigInt::new(pair.as_str()));
    }
}

fn main() {
    parse("1239")
}


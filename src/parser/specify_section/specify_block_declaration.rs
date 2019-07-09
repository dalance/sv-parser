use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct SpecifyBlock<'a> {
    pub nodes: (Identifier<'a>,),
}

// -----------------------------------------------------------------------------

pub fn specify_block(s: &str) -> IResult<&str, SpecifyBlock> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

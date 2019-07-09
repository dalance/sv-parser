use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct GateInstantiation<'a> {
    pub nodes: (Identifier<'a>,),
}

// -----------------------------------------------------------------------------

pub fn gate_instantiation(s: Span) -> IResult<Span, GateInstantiation> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

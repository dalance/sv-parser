use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct EdgeIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

// -----------------------------------------------------------------------------

pub fn edge_identifier(s: &str) -> IResult<&str, EdgeIdentifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

use crate::ast::*;
use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct SpecifyBlock<'a> {
    pub nodes: (Identifier<'a>,),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn specify_block(s: Span) -> IResult<Span, SpecifyBlock> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

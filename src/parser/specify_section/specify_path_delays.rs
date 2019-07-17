use crate::ast::*;
use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct EdgeIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

// -----------------------------------------------------------------------------

#[trace]
pub fn edge_identifier(s: Span) -> IResult<Span, EdgeIdentifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

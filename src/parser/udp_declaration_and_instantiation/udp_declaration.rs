use crate::ast::*;
use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct UdpDeclaration<'a> {
    pub nodes: (Identifier<'a>,),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn udp_declaration(s: Span) -> IResult<Span, UdpDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

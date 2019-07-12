use crate::ast::*;
use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct UdpInstantiation<'a> {
    pub nodes: (Identifier<'a>,),
}

// -----------------------------------------------------------------------------

pub fn udp_instantiation(s: Span) -> IResult<Span, UdpInstantiation> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

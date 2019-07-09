use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct UdpInstantiation<'a> {
    pub nodes: (Identifier<'a>,),
}

// -----------------------------------------------------------------------------

pub fn udp_instantiation(s: &str) -> IResult<&str, UdpInstantiation> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

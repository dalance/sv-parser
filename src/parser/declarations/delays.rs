use crate::ast::*;
use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum Delay3<'a> {
    Single(Delay3Single<'a>),
    Mintypmax(Delay3Mintypmax<'a>),
}

#[derive(Debug, Node)]
pub struct Delay3Single<'a> {
    pub nodes: (Symbol<'a>, DelayValue<'a>),
}

#[derive(Debug)]
pub struct Delay3Mintypmax<'a> {
    pub nodes: (
        Symbol<'a>,
        Paren<
            'a,
            (
                MintypmaxExpression<'a>,
                Option<(MintypmaxExpression<'a>, Option<MintypmaxExpression<'a>>)>,
            ),
        >,
    ),
}

#[derive(Debug)]
pub enum Delay2<'a> {
    Single(Delay2Single<'a>),
    Mintypmax(Delay2Mintypmax<'a>),
}

#[derive(Debug, Node)]
pub struct Delay2Single<'a> {
    pub nodes: (Symbol<'a>, DelayValue<'a>),
}

#[derive(Debug)]
pub struct Delay2Mintypmax<'a> {
    pub nodes: (
        Symbol<'a>,
        Paren<'a, (MintypmaxExpression<'a>, Option<MintypmaxExpression<'a>>)>,
    ),
}

#[derive(Debug, Node)]
pub enum DelayValue<'a> {
    UnsignedNumber(UnsignedNumber<'a>),
    RealNumber(RealNumber<'a>),
    Identifier(Identifier<'a>),
    TimeLiteral(TimeLiteral<'a>),
    Step1(Symbol<'a>),
}

// -----------------------------------------------------------------------------

pub fn delay3(s: Span) -> IResult<Span, Delay3> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn delay2(s: Span) -> IResult<Span, Delay2> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn delay_value(s: Span) -> IResult<Span, DelayValue> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

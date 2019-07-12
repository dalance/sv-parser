use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum Delay3<'a> {
    Single(Delay3Single<'a>),
    Mintypmax(Delay3Mintypmax<'a>),
}

#[derive(Debug, Node)]
pub struct Delay3Single<'a> {
    pub nodes: (Symbol<'a>, DelayValue<'a>),
}

#[derive(Debug, Node)]
pub struct Delay3Mintypmax<'a> {
    pub nodes: (
        Symbol<'a>,
        Paren<
            'a,
            (
                MintypmaxExpression<'a>,
                Option<(
                    Symbol<'a>,
                    MintypmaxExpression<'a>,
                    Option<(Symbol<'a>, MintypmaxExpression<'a>)>,
                )>,
            ),
        >,
    ),
}

#[derive(Debug, Node)]
pub enum Delay2<'a> {
    Single(Delay2Single<'a>),
    Mintypmax(Delay2Mintypmax<'a>),
}

#[derive(Debug, Node)]
pub struct Delay2Single<'a> {
    pub nodes: (Symbol<'a>, DelayValue<'a>),
}

#[derive(Debug, Node)]
pub struct Delay2Mintypmax<'a> {
    pub nodes: (
        Symbol<'a>,
        Paren<
            'a,
            (
                MintypmaxExpression<'a>,
                Option<(Symbol<'a>, MintypmaxExpression<'a>)>,
            ),
        >,
    ),
}

#[derive(Debug, Node)]
pub enum DelayValue<'a> {
    UnsignedNumber(UnsignedNumber<'a>),
    RealNumber(RealNumber<'a>),
    PsIdentifier(PsIdentifier<'a>),
    TimeLiteral(TimeLiteral<'a>),
    Step1(Symbol<'a>),
}

// -----------------------------------------------------------------------------

pub fn delay3(s: Span) -> IResult<Span, Delay3> {
    alt((delay3_single, delay3_mintypmax))(s)
}

pub fn delay3_single(s: Span) -> IResult<Span, Delay3> {
    let (s, a) = symbol("#")(s)?;
    let (s, b) = delay_value(s)?;
    Ok((s, Delay3::Single(Delay3Single { nodes: (a, b) })))
}

pub fn delay3_mintypmax(s: Span) -> IResult<Span, Delay3> {
    let (s, a) = symbol("#")(s)?;
    let (s, b) = paren(pair(
        mintypmax_expression,
        opt(triple(
            symbol(","),
            mintypmax_expression,
            opt(pair(symbol(","), mintypmax_expression)),
        )),
    ))(s)?;
    Ok((s, Delay3::Mintypmax(Delay3Mintypmax { nodes: (a, b) })))
}

pub fn delay2(s: Span) -> IResult<Span, Delay2> {
    alt((delay2_single, delay2_mintypmax))(s)
}

pub fn delay2_single(s: Span) -> IResult<Span, Delay2> {
    let (s, a) = symbol("#")(s)?;
    let (s, b) = delay_value(s)?;
    Ok((s, Delay2::Single(Delay2Single { nodes: (a, b) })))
}

pub fn delay2_mintypmax(s: Span) -> IResult<Span, Delay2> {
    let (s, a) = symbol("#")(s)?;
    let (s, b) = paren(pair(
        mintypmax_expression,
        opt(pair(symbol(","), mintypmax_expression)),
    ))(s)?;
    Ok((s, Delay2::Mintypmax(Delay2Mintypmax { nodes: (a, b) })))
}

pub fn delay_value(s: Span) -> IResult<Span, DelayValue> {
    alt((
        map(unsigned_number, |x| DelayValue::UnsignedNumber(x)),
        map(real_number, |x| DelayValue::RealNumber(x)),
        map(ps_identifier, |x| DelayValue::PsIdentifier(x)),
        map(time_literal, |x| DelayValue::TimeLiteral(x)),
        map(symbol("1step"), |x| DelayValue::Step1(x)),
    ))(s)
}

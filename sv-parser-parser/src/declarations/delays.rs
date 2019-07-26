use crate::*;

// -----------------------------------------------------------------------------

#[parser]
pub(crate) fn delay3(s: Span) -> IResult<Span, Delay3> {
    alt((delay3_single, delay3_mintypmax))(s)
}

#[parser]
pub(crate) fn delay3_single(s: Span) -> IResult<Span, Delay3> {
    let (s, a) = symbol("#")(s)?;
    let (s, b) = delay_value(s)?;
    Ok((s, Delay3::Single(Box::new(Delay3Single { nodes: (a, b) }))))
}

#[parser]
pub(crate) fn delay3_mintypmax(s: Span) -> IResult<Span, Delay3> {
    let (s, a) = symbol("#")(s)?;
    let (s, b) = paren(pair(
        mintypmax_expression,
        opt(triple(
            symbol(","),
            mintypmax_expression,
            opt(pair(symbol(","), mintypmax_expression)),
        )),
    ))(s)?;
    Ok((
        s,
        Delay3::Mintypmax(Box::new(Delay3Mintypmax { nodes: (a, b) })),
    ))
}

#[parser]
pub(crate) fn delay2(s: Span) -> IResult<Span, Delay2> {
    alt((delay2_single, delay2_mintypmax))(s)
}

#[parser]
pub(crate) fn delay2_single(s: Span) -> IResult<Span, Delay2> {
    let (s, a) = symbol("#")(s)?;
    let (s, b) = delay_value(s)?;
    Ok((s, Delay2::Single(Box::new(Delay2Single { nodes: (a, b) }))))
}

#[parser]
pub(crate) fn delay2_mintypmax(s: Span) -> IResult<Span, Delay2> {
    let (s, a) = symbol("#")(s)?;
    let (s, b) = paren(pair(
        mintypmax_expression,
        opt(pair(symbol(","), mintypmax_expression)),
    ))(s)?;
    Ok((
        s,
        Delay2::Mintypmax(Box::new(Delay2Mintypmax { nodes: (a, b) })),
    ))
}

#[parser]
pub(crate) fn delay_value(s: Span) -> IResult<Span, DelayValue> {
    alt((
        map(unsigned_number, |x| DelayValue::UnsignedNumber(Box::new(x))),
        map(real_number, |x| DelayValue::RealNumber(Box::new(x))),
        map(ps_identifier, |x| DelayValue::PsIdentifier(Box::new(x))),
        map(time_literal, |x| DelayValue::TimeLiteral(Box::new(x))),
        map(keyword("1step"), |x| DelayValue::Step1(Box::new(x))),
    ))(s)
}

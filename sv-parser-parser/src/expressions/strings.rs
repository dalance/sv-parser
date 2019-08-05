use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
#[packrat_parser]
pub(crate) fn string_literal(s: Span) -> IResult<Span, StringLiteral> {
    let (s, a) = ws(string_literal_impl)(s)?;
    Ok((s, StringLiteral { nodes: a }))
}

#[tracable_parser]
pub(crate) fn string_literal_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = tag("\"")(s)?;
    let (s, b) = many0(alt((
        is_not("\\\""),
        map(pair(tag("\\"), take(1usize)), |(x, y)| {
            concat(x, y).unwrap()
        }),
    )))(s)?;
    let (s, c) = tag("\"")(s)?;

    let mut ret = None;
    for x in b {
        ret = if let Some(ret) = ret {
            Some(concat(ret, x).unwrap())
        } else {
            Some(x)
        };
    }

    let a = if let Some(b) = ret {
        let a = concat(a, b).unwrap();
        let a = concat(a, c).unwrap();
        a
    } else {
        let a = concat(a, c).unwrap();
        a
    };

    Ok((s, into_locate(a)))
}

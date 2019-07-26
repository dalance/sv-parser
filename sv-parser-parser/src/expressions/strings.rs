use crate::*;

// -----------------------------------------------------------------------------

#[parser]
pub(crate) fn string_literal(s: Span) -> IResult<Span, StringLiteral> {
    let (s, a) = ws(string_literal_impl)(s)?;
    Ok((s, StringLiteral { nodes: a }))
}

#[parser]
pub(crate) fn string_literal_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = tag("\"")(s)?;
    let (s, b) = many1(pair(is_not("\\\""), opt(pair(tag("\\"), take(1usize)))))(s)?;
    let (s, c) = tag("\"")(s)?;

    let mut ret = None;
    for (x, y) in b {
        ret = if let Some(ret) = ret {
            Some(concat(ret, x).unwrap())
        } else {
            Some(x)
        };
        if let Some((y, z)) = y {
            ret = if let Some(ret) = ret {
                Some(concat(ret, y).unwrap())
            } else {
                Some(y)
            };
            ret = if let Some(ret) = ret {
                Some(concat(ret, z).unwrap())
            } else {
                Some(z)
            };
        }
    }

    let b = ret.unwrap();
    let a = concat(a, b).unwrap();
    let a = concat(a, c).unwrap();

    Ok((s, a.into()))
}

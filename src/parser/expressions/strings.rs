use crate::parser::*;
use nom::bytes::complete::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct StringLiteral<'a> {
    pub nodes: (Span<'a>, Vec<WhiteSpace<'a>>),
}

// -----------------------------------------------------------------------------

pub fn string_literal(s: Span) -> IResult<Span, StringLiteral> {
    let (s, a) = ws(string_literal_impl)(s)?;
    Ok((s, StringLiteral { nodes: a }))
}

pub fn string_literal_impl(s: Span) -> IResult<Span, Span> {
    let (s, _) = tag("\"")(s)?;
    let (s, x) = many1(pair(is_not("\\\""), opt(pair(tag("\\"), take(1usize)))))(s)?;
    let (s, _) = tag("\"")(s)?;

    let mut ret = None;
    for (x, y) in x {
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

    let ret = ret.unwrap();

    Ok((s, ret))
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        assert_eq!(
            format!(
                "{:?}",
                all_consuming(string_literal)(Span::new("\"aaa aaaa\""))
            ),
            "Ok((LocatedSpanEx { offset: 10, line: 1, fragment: \"\", extra: () }, StringLiteral { nodes: (LocatedSpanEx { offset: 1, line: 1, fragment: \"aaa aaaa\", extra: () }, []) }))"
        );
        assert_eq!(
            format!(
                "{:?}",
                all_consuming(string_literal)(Span::new(r#""aaa\" aaaa""#))
            ),
            "Ok((LocatedSpanEx { offset: 12, line: 1, fragment: \"\", extra: () }, StringLiteral { nodes: (LocatedSpanEx { offset: 1, line: 1, fragment: \"aaa\\\\\\\" aaaa\", extra: () }, []) }))"
        );
        assert_eq!(
            format!(
                "{:?}",
                all_consuming(string_literal)(Span::new(r#""aaa\"""#))
            ),
            "Ok((LocatedSpanEx { offset: 7, line: 1, fragment: \"\", extra: () }, StringLiteral { nodes: (LocatedSpanEx { offset: 1, line: 1, fragment: \"aaa\\\\\\\"\", extra: () }, []) }))"
        );
    }
}

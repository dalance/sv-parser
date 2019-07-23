use crate::ast::*;
use crate::parser::*;
use nom::bytes::complete::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct StringLiteral {
    pub nodes: (Locate, Vec<WhiteSpace>),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn string_literal(s: Span) -> IResult<Span, StringLiteral> {
    let (s, a) = ws(string_literal_impl)(s)?;
    Ok((s, StringLiteral { nodes: a }))
}

#[parser]
pub fn string_literal_impl(s: Span) -> IResult<Span, Locate> {
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

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_string_literal() {
        parser_test!(string_literal, "\"aaa aaaa\"", Ok((_, _)));
        parser_test!(string_literal, r#""aaa\" aaaa""#, Ok((_, _)));
        parser_test!(string_literal, r#""aaa\"""#, Ok((_, _)));
    }
}

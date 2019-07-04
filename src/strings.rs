use crate::util::*;
use nom::bytes::complete::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct StringLiteral<'a> {
    pub raw: &'a str,
}

// -----------------------------------------------------------------------------

pub fn string_literal(s: &str) -> IResult<&str, StringLiteral> {
    ws(string_literal_impl)(s)
}

pub fn string_literal_impl(s: &str) -> IResult<&str, StringLiteral> {
    let (s, _) = tag("\"")(s)?;
    let (s, x) = many1(pair(is_not("\\\""), opt(pair(tag("\\"), take(1usize)))))(s)?;
    let (s, _) = tag("\"")(s)?;

    let mut raw = None;
    for (x, y) in x {
        raw = if let Some(raw) = raw {
            Some(str_concat::concat(raw, x).unwrap())
        } else {
            Some(x)
        };
        if let Some((y, z)) = y {
            raw = if let Some(raw) = raw {
                Some(str_concat::concat(raw, y).unwrap())
            } else {
                Some(y)
            };
            raw = if let Some(raw) = raw {
                Some(str_concat::concat(raw, z).unwrap())
            } else {
                Some(z)
            };
        }
    }

    let raw = raw.unwrap();

    Ok((s, StringLiteral { raw }))
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        assert_eq!(
            format!("{:?}", all_consuming(string_literal)("\"aaa aaaa\"")),
            "Ok((\"\", StringLiteral { raw: \"aaa aaaa\" }))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(string_literal)(r#""aaa\" aaaa""#)),
            "Ok((\"\", StringLiteral { raw: \"aaa\\\\\\\" aaaa\" }))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(string_literal)(r#""aaa\"""#)),
            "Ok((\"\", StringLiteral { raw: \"aaa\\\\\\\"\" }))"
        );
    }
}

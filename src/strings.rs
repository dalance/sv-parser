use nom::bytes::complete::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct StringLiteral<'a> {
    pub raw: Vec<&'a str>,
}

// -----------------------------------------------------------------------------

pub fn string_literal(s: &str) -> IResult<&str, StringLiteral> {
    let (s, _) = tag("\"")(s)?;
    let (s, x) = many1(pair(is_not("\\\""), opt(pair(tag("\\"), take(1usize)))))(s)?;
    let (s, _) = tag("\"")(s)?;

    let mut raw = Vec::new();
    for (x, y) in x {
        raw.push(x);
        if let Some((y, z)) = y {
            raw.push(y);
            raw.push(z);
        }
    }

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
            "Ok((\"\", StringLiteral { raw: [\"aaa aaaa\"] }))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(string_literal)(r#""aaa\" aaaa""#)),
            "Ok((\"\", StringLiteral { raw: [\"aaa\", \"\\\\\", \"\\\"\", \" aaaa\"] }))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(string_literal)(r#""aaa\"""#)),
            "Ok((\"\", StringLiteral { raw: [\"aaa\", \"\\\\\", \"\\\"\"] }))"
        );
    }
}

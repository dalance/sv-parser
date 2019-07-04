use nom::branch::*;
use nom::bytes::complete::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct Comment<'a> {
    pub raw: &'a str,
}

// -----------------------------------------------------------------------------

pub fn comment(s: &str) -> IResult<&str, Comment> {
    alt((one_line_comment, block_comment))(s)
}

pub fn one_line_comment(s: &str) -> IResult<&str, Comment> {
    let (s, x) = tag("//")(s)?;
    let (s, y) = is_not("\n")(s)?;
    let raw = str_concat::concat(x, y).unwrap();
    Ok((s, Comment { raw }))
}

pub fn block_comment(s: &str) -> IResult<&str, Comment> {
    let (s, x) = tag("/*")(s)?;
    let (s, y) = is_not("*/")(s)?;
    let (s, z) = tag("*/")(s)?;
    let raw = str_concat::concat(x, y).unwrap();
    let raw = str_concat::concat(raw, z).unwrap();
    Ok((s, Comment { raw }))
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use nom::combinator::*;

    #[test]
    fn test() {
        assert_eq!(
            format!("{:?}", all_consuming(comment)("// comment")),
            "Ok((\"\", Comment { raw: \"// comment\" }))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(comment)("/* comment\n\n */")),
            "Ok((\"\", Comment { raw: \"/* comment\\n\\n */\" }))"
        );
    }
}

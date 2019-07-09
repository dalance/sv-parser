use crate::parser::*;
use nom::branch::*;
use nom::bytes::complete::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct Comment<'a> {
    nodes: (Span<'a>,),
}

// -----------------------------------------------------------------------------

pub fn comment(s: Span) -> IResult<Span, Comment> {
    alt((one_line_comment, block_comment))(s)
}

pub fn one_line_comment(s: Span) -> IResult<Span, Comment> {
    let (s, x) = tag("//")(s)?;
    let (s, y) = is_not("\n")(s)?;
    let x = concat(x, y).unwrap();
    Ok((s, Comment { nodes: (x,) }))
}

pub fn block_comment(s: Span) -> IResult<Span, Comment> {
    let (s, x) = tag("/*")(s)?;
    let (s, y) = is_not("*/")(s)?;
    let (s, z) = tag("*/")(s)?;
    let x = concat(x, y).unwrap();
    let x = concat(x, z).unwrap();
    Ok((s, Comment { nodes: (x,) }))
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use nom::combinator::*;

    #[test]
    fn test_comment() {
        parser_test!(comment, "// comment", Ok((_, _)));
        parser_test!(comment, "/* comment\n\n */", Ok((_, _)));
    }
}

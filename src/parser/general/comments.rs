use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::bytes::complete::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct Comment<'a> {
    nodes: (Span<'a>,),
}

// -----------------------------------------------------------------------------

pub fn comment(s: Span) -> IResult<Span, Comment> {
    alt((one_line_comment, block_comment))(s)
}

pub fn one_line_comment(s: Span) -> IResult<Span, Comment> {
    let (s, a) = tag("//")(s)?;
    let (s, b) = is_not("\n")(s)?;
    let a = concat(a, b).unwrap();
    Ok((s, Comment { nodes: (a,) }))
}

pub fn block_comment(s: Span) -> IResult<Span, Comment> {
    let (s, a) = tag("/*")(s)?;
    let (s, b) = is_not("*/")(s)?;
    let (s, c) = tag("*/")(s)?;
    let a = concat(a, b).unwrap();
    let a = concat(a, c).unwrap();
    Ok((s, Comment { nodes: (a,) }))
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

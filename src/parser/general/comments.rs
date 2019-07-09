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
    fn test() {
        assert_eq!(
            format!("{:?}", all_consuming(comment)(Span::new("// comment"))),
            "Ok((LocatedSpanEx { offset: 10, line: 1, fragment: \"\", extra: () }, Comment { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"// comment\", extra: () },) }))"
        );
        assert_eq!(
            format!(
                "{:?}",
                all_consuming(comment)(Span::new("/* comment\n\n */"))
            ),
            "Ok((LocatedSpanEx { offset: 15, line: 3, fragment: \"\", extra: () }, Comment { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"/* comment\\n\\n */\", extra: () },) }))"
        );
    }
}

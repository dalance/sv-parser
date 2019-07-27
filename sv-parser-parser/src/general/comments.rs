use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
pub(crate) fn comment(s: Span) -> IResult<Span, Comment> {
    alt((one_line_comment, block_comment))(s)
}

#[tracable_parser]
pub(crate) fn one_line_comment(s: Span) -> IResult<Span, Comment> {
    let (s, a) = tag("//")(s)?;
    let (s, b) = is_not("\n")(s)?;
    let a = concat(a, b).unwrap();
    Ok((
        s,
        Comment {
            nodes: (into_locate(a),),
        },
    ))
}

#[tracable_parser]
pub(crate) fn block_comment(s: Span) -> IResult<Span, Comment> {
    let (s, a) = tag("/*")(s)?;
    let (s, b) = is_not("*/")(s)?;
    let (s, c) = tag("*/")(s)?;
    let a = concat(a, b).unwrap();
    let a = concat(a, c).unwrap();
    Ok((
        s,
        Comment {
            nodes: (into_locate(a),),
        },
    ))
}
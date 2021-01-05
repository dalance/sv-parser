use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
#[packrat_parser]
pub(crate) fn action_block(s: Span) -> IResult<Span, ActionBlock> {
    alt((
        action_block_else,
        map(statement_or_null, |x| {
            ActionBlock::StatementOrNull(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn action_block_else(s: Span) -> IResult<Span, ActionBlock> {
    let (s, a) = opt(statement)(s)?;
    let (s, b) = keyword("else")(s)?;
    let (s, c) = statement_or_null(s)?;
    Ok((
        s,
        ActionBlock::Else(Box::new(ActionBlockElse { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn seq_block(s: Span) -> IResult<Span, SeqBlock> {
    let (s, a) = keyword("begin")(s)?;
    let (s, b) = opt(pair(symbol(":"), block_identifier))(s)?;
    let (s, c) = many0(block_item_declaration)(s)?;
    let (s, (d, e)) = many_till(statement_or_null, keyword("end"))(s)?;
    let (s, f) = opt(pair(symbol(":"), block_identifier))(s)?;
    Ok((
        s,
        SeqBlock {
            nodes: (a, b, c, d, e, f),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn par_block(s: Span) -> IResult<Span, ParBlock> {
    let (s, a) = keyword("fork")(s)?;
    let (s, b) = opt(pair(symbol(":"), block_identifier))(s)?;
    let (s, c) = many0(block_item_declaration)(s)?;
    let (s, (d, e)) = many_till(statement_or_null, join_keyword)(s)?;
    let (s, f) = opt(pair(symbol(":"), block_identifier))(s)?;
    Ok((
        s,
        ParBlock {
            nodes: (a, b, c, d, e, f),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn join_keyword(s: Span) -> IResult<Span, JoinKeyword> {
    alt((
        map(keyword("join_any"), |x| JoinKeyword::JoinAny(Box::new(x))),
        map(keyword("join_none"), |x| JoinKeyword::JoinNone(Box::new(x))),
        map(keyword("join"), |x| JoinKeyword::Join(Box::new(x))),
    ))(s)
}

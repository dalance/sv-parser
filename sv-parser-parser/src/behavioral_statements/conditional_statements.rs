use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
#[packrat_parser]
pub(crate) fn conditional_statement(s: Span) -> IResult<Span, ConditionalStatement> {
    let (s, a) = opt(unique_priority)(s)?;
    let (s, b) = keyword("if")(s)?;
    let (s, c) = paren(cond_predicate)(s)?;
    let (s, d) = statement_or_null(s)?;
    let (s, e) = many0(tuple((
        keyword("else"),
        keyword("if"),
        paren(cond_predicate),
        statement_or_null,
    )))(s)?;
    let (s, f) = opt(pair(keyword("else"), statement_or_null))(s)?;

    Ok((
        s,
        ConditionalStatement {
            nodes: (a, b, c, d, e, f),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn unique_priority(s: Span) -> IResult<Span, UniquePriority> {
    alt((
        map(keyword("unique0"), |x| UniquePriority::Unique0(Box::new(x))),
        map(keyword("unique"), |x| UniquePriority::Unique(Box::new(x))),
        map(keyword("priority"), |x| {
            UniquePriority::Priority(Box::new(x))
        }),
    ))(s)
}

#[recursive_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn cond_predicate(s: Span) -> IResult<Span, CondPredicate> {
    let (s, a) = list(symbol("&&&"), expression_or_cond_pattern)(s)?;
    Ok((s, CondPredicate { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn expression_or_cond_pattern(s: Span) -> IResult<Span, ExpressionOrCondPattern> {
    alt((
        map(expression, |x| {
            ExpressionOrCondPattern::Expression(Box::new(x))
        }),
        map(cond_pattern, |x| {
            ExpressionOrCondPattern::CondPattern(Box::new(x))
        }),
    ))(s)
}

#[recursive_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn cond_pattern(s: Span) -> IResult<Span, CondPattern> {
    let (s, a) = expression(s)?;
    let (s, b) = keyword("matches")(s)?;
    let (s, c) = pattern(s)?;
    Ok((s, CondPattern { nodes: (a, b, c) }))
}

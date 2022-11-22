use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
#[packrat_parser]
pub(crate) fn assertion_item(s: Span) -> IResult<Span, AssertionItem> {
    alt((
        map(concurrent_assertion_item, |x| {
            AssertionItem::Concurrent(Box::new(x))
        }),
        map(deferred_immediate_assertion_item, |x| {
            AssertionItem::Immediate(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn deferred_immediate_assertion_item(
    s: Span,
) -> IResult<Span, DeferredImmediateAssertionItem> {
    let (s, a) = opt(pair(block_identifier, symbol(":")))(s)?;
    let (s, b) = deferred_immediate_assertion_statement(s)?;
    Ok((s, DeferredImmediateAssertionItem { nodes: (a, b) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn procedural_assertion_statement(
    s: Span,
) -> IResult<Span, ProceduralAssertionStatement> {
    alt((
        map(concurrent_assertion_statement, |x| {
            ProceduralAssertionStatement::Concurrent(Box::new(x))
        }),
        map(immediate_assertion_statement, |x| {
            ProceduralAssertionStatement::Immediate(Box::new(x))
        }),
        map(checker_instantiation, |x| {
            ProceduralAssertionStatement::Checker(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn immediate_assertion_statement(s: Span) -> IResult<Span, ImmediateAssertionStatement> {
    alt((
        map(simple_immediate_assertion_statement, |x| {
            ImmediateAssertionStatement::Simple(Box::new(x))
        }),
        map(deferred_immediate_assertion_statement, |x| {
            ImmediateAssertionStatement::Deferred(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn simple_immediate_assertion_statement(
    s: Span,
) -> IResult<Span, SimpleImmediateAssertionStatement> {
    alt((
        map(simple_immediate_assert_statement, |x| {
            SimpleImmediateAssertionStatement::Assert(Box::new(x))
        }),
        map(simple_immediate_assume_statement, |x| {
            SimpleImmediateAssertionStatement::Assume(Box::new(x))
        }),
        map(simple_immediate_cover_statement, |x| {
            SimpleImmediateAssertionStatement::Cover(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn simple_immediate_assert_statement(
    s: Span,
) -> IResult<Span, SimpleImmediateAssertStatement> {
    let (s, a) = keyword("assert")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = action_block(s)?;
    Ok((s, SimpleImmediateAssertStatement { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn simple_immediate_assume_statement(
    s: Span,
) -> IResult<Span, SimpleImmediateAssumeStatement> {
    let (s, a) = keyword("assume")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = action_block(s)?;
    Ok((s, SimpleImmediateAssumeStatement { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn simple_immediate_cover_statement(
    s: Span,
) -> IResult<Span, SimpleImmediateCoverStatement> {
    let (s, a) = keyword("cover")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = statement_or_null(s)?;
    Ok((s, SimpleImmediateCoverStatement { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn deferred_immediate_assertion_statement(
    s: Span,
) -> IResult<Span, DeferredImmediateAssertionStatement> {
    alt((
        map(deferred_immediate_assert_statement, |x| {
            DeferredImmediateAssertionStatement::Assert(Box::new(x))
        }),
        map(deferred_immediate_assume_statement, |x| {
            DeferredImmediateAssertionStatement::Assume(Box::new(x))
        }),
        map(deferred_immediate_cover_statement, |x| {
            DeferredImmediateAssertionStatement::Cover(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn deferred_immediate_assert_statement(
    s: Span,
) -> IResult<Span, DeferredImmediateAssertStatement> {
    let (s, a) = keyword("assert")(s)?;
    let (s, b) = assert_timing(s)?;
    let (s, c) = paren(expression)(s)?;
    let (s, d) = action_block(s)?;
    Ok((
        s,
        DeferredImmediateAssertStatement {
            nodes: (a, b, c, d),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn deferred_immediate_assume_statement(
    s: Span,
) -> IResult<Span, DeferredImmediateAssumeStatement> {
    let (s, a) = keyword("assume")(s)?;
    let (s, b) = assert_timing(s)?;
    let (s, c) = paren(expression)(s)?;
    let (s, d) = action_block(s)?;
    Ok((
        s,
        DeferredImmediateAssumeStatement {
            nodes: (a, b, c, d),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn deferred_immediate_cover_statement(
    s: Span,
) -> IResult<Span, DeferredImmediateCoverStatement> {
    let (s, a) = keyword("cover")(s)?;
    let (s, b) = assert_timing(s)?;
    let (s, c) = paren(expression)(s)?;
    let (s, d) = statement_or_null(s)?;
    Ok((
        s,
        DeferredImmediateCoverStatement {
            nodes: (a, b, c, d),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn assert_timing(s: Span) -> IResult<Span, AssertTiming> {
    alt((
        map(symbol("#0"), |x| AssertTiming::Zero(Box::new(x))),
        map(keyword("final"), |x| AssertTiming::Final(Box::new(x))),
    ))(s)
}

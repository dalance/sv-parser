use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum AssertionItem {
    Concurrent(ConcurrentAssertionItem),
    Immediate(DeferredImmediateAssetionItem),
}

#[derive(Clone, Debug, Node)]
pub struct DeferredImmediateAssetionItem {
    pub nodes: (
        Option<(BlockIdentifier, Symbol)>,
        DeferredImmediateAssertionStatement,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum ProceduralAssertionStatement {
    Concurrent(ConcurrentAssertionStatement),
    Immediate(ImmediateAssetionStatement),
    Checker(CheckerInstantiation),
}

#[derive(Clone, Debug, Node)]
pub enum ImmediateAssetionStatement {
    Simple(SimpleImmediateAssertionStatement),
    Deferred(DeferredImmediateAssertionStatement),
}

#[derive(Clone, Debug, Node)]
pub enum SimpleImmediateAssertionStatement {
    Assert(SimpleImmediateAssertStatement),
    Assume(SimpleImmediateAssumeStatement),
    Cover(SimpleImmediateCoverStatement),
}

#[derive(Clone, Debug, Node)]
pub struct SimpleImmediateAssertStatement {
    pub nodes: (Keyword, Paren<Expression>, ActionBlock),
}

#[derive(Clone, Debug, Node)]
pub struct SimpleImmediateAssumeStatement {
    pub nodes: (Keyword, Paren<Expression>, ActionBlock),
}

#[derive(Clone, Debug, Node)]
pub struct SimpleImmediateCoverStatement {
    pub nodes: (Keyword, Paren<Expression>, StatementOrNull),
}

#[derive(Clone, Debug, Node)]
pub enum DeferredImmediateAssertionStatement {
    Assert(DeferredImmediateAssertStatement),
    Assume(DeferredImmediateAssumeStatement),
    Cover(DeferredImmediateCoverStatement),
}

#[derive(Clone, Debug, Node)]
pub struct DeferredImmediateAssertStatement {
    pub nodes: (Keyword, AssertTiming, Paren<Expression>, ActionBlock),
}

#[derive(Clone, Debug, Node)]
pub struct DeferredImmediateAssumeStatement {
    pub nodes: (Keyword, AssertTiming, Paren<Expression>, ActionBlock),
}

#[derive(Clone, Debug, Node)]
pub struct DeferredImmediateCoverStatement {
    pub nodes: (Keyword, AssertTiming, Paren<Expression>, StatementOrNull),
}

#[derive(Clone, Debug, Node)]
pub enum AssertTiming {
    Zero(Symbol),
    Final(Keyword),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn assertion_item(s: Span) -> IResult<Span, AssertionItem> {
    alt((
        map(concurrent_assertion_item, |x| AssertionItem::Concurrent(x)),
        map(deferred_immediate_assertion_item, |x| {
            AssertionItem::Immediate(x)
        }),
    ))(s)
}

#[parser]
pub fn deferred_immediate_assertion_item(s: Span) -> IResult<Span, DeferredImmediateAssetionItem> {
    let (s, a) = opt(pair(block_identifier, symbol(":")))(s)?;
    let (s, b) = deferred_immediate_assertion_statement(s)?;
    Ok((s, DeferredImmediateAssetionItem { nodes: (a, b) }))
}

#[parser]
pub fn procedural_assertion_statement(s: Span) -> IResult<Span, ProceduralAssertionStatement> {
    alt((
        map(concurrent_assertion_statement, |x| {
            ProceduralAssertionStatement::Concurrent(x)
        }),
        map(immediate_assertion_statement, |x| {
            ProceduralAssertionStatement::Immediate(x)
        }),
        map(checker_instantiation, |x| {
            ProceduralAssertionStatement::Checker(x)
        }),
    ))(s)
}

#[parser]
pub fn immediate_assertion_statement(s: Span) -> IResult<Span, ImmediateAssetionStatement> {
    alt((
        map(simple_immediate_assertion_statement, |x| {
            ImmediateAssetionStatement::Simple(x)
        }),
        map(deferred_immediate_assertion_statement, |x| {
            ImmediateAssetionStatement::Deferred(x)
        }),
    ))(s)
}

#[parser]
pub fn simple_immediate_assertion_statement(
    s: Span,
) -> IResult<Span, SimpleImmediateAssertionStatement> {
    alt((
        map(simple_immediate_assert_statement, |x| {
            SimpleImmediateAssertionStatement::Assert(x)
        }),
        map(simple_immediate_assume_statement, |x| {
            SimpleImmediateAssertionStatement::Assume(x)
        }),
        map(simple_immediate_cover_statement, |x| {
            SimpleImmediateAssertionStatement::Cover(x)
        }),
    ))(s)
}

#[parser]
pub fn simple_immediate_assert_statement(s: Span) -> IResult<Span, SimpleImmediateAssertStatement> {
    let (s, a) = keyword("assert")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = action_block(s)?;
    Ok((s, SimpleImmediateAssertStatement { nodes: (a, b, c) }))
}

#[parser]
pub fn simple_immediate_assume_statement(s: Span) -> IResult<Span, SimpleImmediateAssumeStatement> {
    let (s, a) = keyword("assume")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = action_block(s)?;
    Ok((s, SimpleImmediateAssumeStatement { nodes: (a, b, c) }))
}

#[parser]
pub fn simple_immediate_cover_statement(s: Span) -> IResult<Span, SimpleImmediateCoverStatement> {
    let (s, a) = keyword("cover")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = statement_or_null(s)?;
    Ok((s, SimpleImmediateCoverStatement { nodes: (a, b, c) }))
}

#[parser]
pub fn deferred_immediate_assertion_statement(
    s: Span,
) -> IResult<Span, DeferredImmediateAssertionStatement> {
    alt((
        map(deferred_immediate_assert_statement, |x| {
            DeferredImmediateAssertionStatement::Assert(x)
        }),
        map(deferred_immediate_assume_statement, |x| {
            DeferredImmediateAssertionStatement::Assume(x)
        }),
        map(deferred_immediate_cover_statement, |x| {
            DeferredImmediateAssertionStatement::Cover(x)
        }),
    ))(s)
}

#[parser]
pub fn deferred_immediate_assert_statement(
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

#[parser]
pub fn deferred_immediate_assume_statement(
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

#[parser]
pub fn deferred_immediate_cover_statement(
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

#[parser]
pub fn assert_timing(s: Span) -> IResult<Span, AssertTiming> {
    alt((
        map(symbol("#0"), |x| AssertTiming::Zero(x)),
        map(keyword("final"), |x| AssertTiming::Final(x)),
    ))(s)
}

// -----------------------------------------------------------------------------

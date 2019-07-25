use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum AssertionItem {
    Concurrent(Box<ConcurrentAssertionItem>),
    Immediate(Box<DeferredImmediateAssetionItem>),
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
    Concurrent(Box<ConcurrentAssertionStatement>),
    Immediate(Box<ImmediateAssetionStatement>),
    Checker(Box<CheckerInstantiation>),
}

#[derive(Clone, Debug, Node)]
pub enum ImmediateAssetionStatement {
    Simple(Box<SimpleImmediateAssertionStatement>),
    Deferred(Box<DeferredImmediateAssertionStatement>),
}

#[derive(Clone, Debug, Node)]
pub enum SimpleImmediateAssertionStatement {
    Assert(Box<SimpleImmediateAssertStatement>),
    Assume(Box<SimpleImmediateAssumeStatement>),
    Cover(Box<SimpleImmediateCoverStatement>),
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
    Assert(Box<DeferredImmediateAssertStatement>),
    Assume(Box<DeferredImmediateAssumeStatement>),
    Cover(Box<DeferredImmediateCoverStatement>),
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
    Zero(Box<Symbol>),
    Final(Box<Keyword>),
}

// -----------------------------------------------------------------------------

#[parser]
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

#[parser]
pub(crate) fn deferred_immediate_assertion_item(s: Span) -> IResult<Span, DeferredImmediateAssetionItem> {
    let (s, a) = opt(pair(block_identifier, symbol(":")))(s)?;
    let (s, b) = deferred_immediate_assertion_statement(s)?;
    Ok((s, DeferredImmediateAssetionItem { nodes: (a, b) }))
}

#[parser]
pub(crate) fn procedural_assertion_statement(s: Span) -> IResult<Span, ProceduralAssertionStatement> {
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

#[parser]
pub(crate) fn immediate_assertion_statement(s: Span) -> IResult<Span, ImmediateAssetionStatement> {
    alt((
        map(simple_immediate_assertion_statement, |x| {
            ImmediateAssetionStatement::Simple(Box::new(x))
        }),
        map(deferred_immediate_assertion_statement, |x| {
            ImmediateAssetionStatement::Deferred(Box::new(x))
        }),
    ))(s)
}

#[parser]
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

#[parser]
pub(crate) fn simple_immediate_assert_statement(s: Span) -> IResult<Span, SimpleImmediateAssertStatement> {
    let (s, a) = keyword("assert")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = action_block(s)?;
    Ok((s, SimpleImmediateAssertStatement { nodes: (a, b, c) }))
}

#[parser]
pub(crate) fn simple_immediate_assume_statement(s: Span) -> IResult<Span, SimpleImmediateAssumeStatement> {
    let (s, a) = keyword("assume")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = action_block(s)?;
    Ok((s, SimpleImmediateAssumeStatement { nodes: (a, b, c) }))
}

#[parser]
pub(crate) fn simple_immediate_cover_statement(s: Span) -> IResult<Span, SimpleImmediateCoverStatement> {
    let (s, a) = keyword("cover")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = statement_or_null(s)?;
    Ok((s, SimpleImmediateCoverStatement { nodes: (a, b, c) }))
}

#[parser]
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

#[parser]
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

#[parser]
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

#[parser]
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

#[parser]
pub(crate) fn assert_timing(s: Span) -> IResult<Span, AssertTiming> {
    alt((
        map(symbol("#0"), |x| AssertTiming::Zero(Box::new(x))),
        map(keyword("final"), |x| AssertTiming::Final(Box::new(x))),
    ))(s)
}

// -----------------------------------------------------------------------------

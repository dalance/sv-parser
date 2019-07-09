use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum AssertionItem<'a> {
    Concurrent(ConcurrentAssertionItem<'a>),
    Immediate(DeferredImmediateAssetionItem<'a>),
}

#[derive(Debug)]
pub struct DeferredImmediateAssetionItem<'a> {
    pub nodes: (
        Option<BlockIdentifier<'a>>,
        DeferredImmediateAssertionStatement<'a>,
    ),
}

#[derive(Debug)]
pub enum ProceduralAssertionStatement<'a> {
    Concurrent(ConcurrentAssertionStatement<'a>),
    Immediate(ImmediateAssetionStatement<'a>),
    Checker(CheckerInstantiation<'a>),
}

#[derive(Debug)]
pub enum ImmediateAssetionStatement<'a> {
    Simple(SimpleImmediateAssertionStatement<'a>),
    Deferred(DeferredImmediateAssertionStatement<'a>),
}

#[derive(Debug)]
pub enum SimpleImmediateAssertionStatement<'a> {
    Assert(SimpleImmediateAssertStatement<'a>),
    Assume(SimpleImmediateAssumeStatement<'a>),
    Cover(SimpleImmediateCoverStatement<'a>),
}

#[derive(Debug)]
pub struct SimpleImmediateAssertStatement<'a> {
    pub nodes: (Expression<'a>, ActionBlock<'a>),
}

#[derive(Debug)]
pub struct SimpleImmediateAssumeStatement<'a> {
    pub nodes: (Expression<'a>, ActionBlock<'a>),
}

#[derive(Debug)]
pub struct SimpleImmediateCoverStatement<'a> {
    pub nodes: (Expression<'a>, StatementOrNull<'a>),
}

#[derive(Debug)]
pub enum DeferredImmediateAssertionStatement<'a> {
    Assert(DeferredImmediateAssertStatement<'a>),
    Assume(DeferredImmediateAssumeStatement<'a>),
    Cover(DeferredImmediateCoverStatement<'a>),
}

#[derive(Debug)]
pub struct DeferredImmediateAssertStatement<'a> {
    pub nodes: (AssertTiming, Expression<'a>, ActionBlock<'a>),
}

#[derive(Debug)]
pub struct DeferredImmediateAssumeStatement<'a> {
    pub nodes: (AssertTiming, Expression<'a>, ActionBlock<'a>),
}

#[derive(Debug)]
pub struct DeferredImmediateCoverStatement<'a> {
    pub nodes: (AssertTiming, Expression<'a>, StatementOrNull<'a>),
}

#[derive(Debug)]
pub enum AssertTiming {
    Zero,
    Final,
}

// -----------------------------------------------------------------------------

pub fn assertion_item(s: Span) -> IResult<Span, AssertionItem> {
    alt((
        map(concurrent_assertion_item, |x| AssertionItem::Concurrent(x)),
        map(deferred_immediate_assertion_item, |x| {
            AssertionItem::Immediate(x)
        }),
    ))(s)
}

pub fn deferred_immediate_assertion_item(s: Span) -> IResult<Span, DeferredImmediateAssetionItem> {
    let (s, x) = opt(terminated(block_identifier, symbol(":")))(s)?;
    let (s, y) = deferred_immediate_assertion_statement(s)?;
    Ok((s, DeferredImmediateAssetionItem { nodes: (x, y) }))
}

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

pub fn simple_immediate_assert_statement(s: Span) -> IResult<Span, SimpleImmediateAssertStatement> {
    let (s, _) = symbol("assert")(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, x) = expression(s)?;
    let (s, _) = symbol(")")(s)?;
    let (s, y) = action_block(s)?;
    Ok((s, SimpleImmediateAssertStatement { nodes: (x, y) }))
}

pub fn simple_immediate_assume_statement(s: Span) -> IResult<Span, SimpleImmediateAssumeStatement> {
    let (s, _) = symbol("assume")(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, x) = expression(s)?;
    let (s, _) = symbol(")")(s)?;
    let (s, y) = action_block(s)?;
    Ok((s, SimpleImmediateAssumeStatement { nodes: (x, y) }))
}

pub fn simple_immediate_cover_statement(s: Span) -> IResult<Span, SimpleImmediateCoverStatement> {
    let (s, _) = symbol("cover")(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, x) = expression(s)?;
    let (s, _) = symbol(")")(s)?;
    let (s, y) = statement_or_null(s)?;
    Ok((s, SimpleImmediateCoverStatement { nodes: (x, y) }))
}

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

pub fn deferred_immediate_assert_statement(
    s: Span,
) -> IResult<Span, DeferredImmediateAssertStatement> {
    let (s, _) = symbol("assert")(s)?;
    let (s, x) = assert_timing(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, y) = expression(s)?;
    let (s, _) = symbol(")")(s)?;
    let (s, z) = action_block(s)?;
    Ok((s, DeferredImmediateAssertStatement { nodes: (x, y, z) }))
}

pub fn deferred_immediate_assume_statement(
    s: Span,
) -> IResult<Span, DeferredImmediateAssumeStatement> {
    let (s, _) = symbol("assume")(s)?;
    let (s, x) = assert_timing(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, y) = expression(s)?;
    let (s, _) = symbol(")")(s)?;
    let (s, z) = action_block(s)?;
    Ok((s, DeferredImmediateAssumeStatement { nodes: (x, y, z) }))
}

pub fn deferred_immediate_cover_statement(
    s: Span,
) -> IResult<Span, DeferredImmediateCoverStatement> {
    let (s, _) = symbol("cover")(s)?;
    let (s, x) = assert_timing(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, y) = expression(s)?;
    let (s, _) = symbol(")")(s)?;
    let (s, z) = statement_or_null(s)?;
    Ok((s, DeferredImmediateCoverStatement { nodes: (x, y, z) }))
}

pub fn assert_timing(s: Span) -> IResult<Span, AssertTiming> {
    alt((
        map(symbol("#0"), |_| AssertTiming::Zero),
        map(symbol("final"), |_| AssertTiming::Final),
    ))(s)
}

// -----------------------------------------------------------------------------

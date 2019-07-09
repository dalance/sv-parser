use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct ConditionalStatement<'a> {
    pub nodes: (
        Option<UniquePriority>,
        ConditionalStatementBody<'a>,
        Vec<ConditionalStatementBody<'a>>,
        Option<StatementOrNull<'a>>,
    ),
}

#[derive(Debug)]
pub enum UniquePriority {
    Unique,
    Unique0,
    Priority,
}

#[derive(Debug)]
pub struct ConditionalStatementBody<'a> {
    pub nodes: (CondPredicate<'a>, StatementOrNull<'a>),
}

#[derive(Debug)]
pub struct CondPredicate<'a> {
    pub nodes: (Vec<ExpressionOrCondPattern<'a>>,),
}

#[derive(Debug)]
pub enum ExpressionOrCondPattern<'a> {
    Expression(Expression<'a>),
    CondPattern(CondPattern<'a>),
}

#[derive(Debug)]
pub struct CondPattern<'a> {
    pub nodes: (Expression<'a>, Pattern<'a>),
}

// -----------------------------------------------------------------------------

pub fn conditional_statement(s: Span) -> IResult<Span, ConditionalStatement> {
    let (s, x) = opt(unique_priority)(s)?;
    let (s, _) = symbol("if")(s)?;
    let (s, y) = conditional_statement_body(s)?;
    let (s, z) = many0(preceded(
        pair(symbol("else"), symbol("if")),
        conditional_statement_body,
    ))(s)?;
    let (s, v) = opt(preceded(symbol("else"), statement_or_null))(s)?;

    Ok((
        s,
        ConditionalStatement {
            nodes: (x, y, z, v),
        },
    ))
}

pub fn conditional_statement_body(s: Span) -> IResult<Span, ConditionalStatementBody> {
    let (s, _) = symbol("(")(s)?;
    let (s, x) = cond_predicate(s)?;
    let (s, _) = symbol(")")(s)?;
    let (s, y) = statement_or_null(s)?;

    Ok((s, ConditionalStatementBody { nodes: (x, y) }))
}

pub fn unique_priority(s: Span) -> IResult<Span, UniquePriority> {
    alt((
        map(symbol("unique0"), |_| UniquePriority::Unique0),
        map(symbol("unique"), |_| UniquePriority::Unique),
        map(symbol("priority"), |_| UniquePriority::Priority),
    ))(s)
}

pub fn cond_predicate(s: Span) -> IResult<Span, CondPredicate> {
    let (s, x) = separated_nonempty_list(symbol("&&&"), expression_or_cond_pattern)(s)?;
    Ok((s, CondPredicate { nodes: (x,) }))
}

pub fn expression_or_cond_pattern(s: Span) -> IResult<Span, ExpressionOrCondPattern> {
    alt((
        map(expression, |x| ExpressionOrCondPattern::Expression(x)),
        map(cond_pattern, |x| ExpressionOrCondPattern::CondPattern(x)),
    ))(s)
}

pub fn cond_pattern(s: Span) -> IResult<Span, CondPattern> {
    let (s, x) = expression(s)?;
    let (s, _) = symbol("matches")(s)?;
    let (s, y) = pattern(s)?;
    Ok((s, CondPattern { nodes: (x, y) }))
}

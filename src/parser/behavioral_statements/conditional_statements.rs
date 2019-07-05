use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct ConditionalStatement<'a> {
    pub unique_priority: Option<UniquePriority>,
    pub if_statement: ConditionalStatementBody<'a>,
    pub else_if_statement: Vec<ConditionalStatementBody<'a>>,
    pub else_statement: Option<StatementOrNull<'a>>,
}

#[derive(Debug)]
pub enum UniquePriority {
    Unique,
    Unique0,
    Priority,
}

#[derive(Debug)]
pub struct ConditionalStatementBody<'a> {
    pub predicate: CondPredicate<'a>,
    pub statement: StatementOrNull<'a>,
}

#[derive(Debug)]
pub struct CondPredicate<'a> {
    pub pattern: Vec<ExpressionOrCondPattern<'a>>,
}

#[derive(Debug)]
pub enum ExpressionOrCondPattern<'a> {
    Expression(Expression<'a>),
    CondPattern(CondPattern<'a>),
}

#[derive(Debug)]
pub struct CondPattern<'a> {
    pub expression: Expression<'a>,
    pub pattern: Pattern<'a>,
}

// -----------------------------------------------------------------------------

pub fn conditional_statement(s: &str) -> IResult<&str, ConditionalStatement> {
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
            unique_priority: x,
            if_statement: y,
            else_if_statement: z,
            else_statement: v,
        },
    ))
}

pub fn conditional_statement_body(s: &str) -> IResult<&str, ConditionalStatementBody> {
    let (s, _) = symbol("(")(s)?;
    let (s, x) = cond_predicate(s)?;
    let (s, _) = symbol(")")(s)?;
    let (s, y) = statement_or_null(s)?;

    Ok((
        s,
        ConditionalStatementBody {
            predicate: x,
            statement: y,
        },
    ))
}

pub fn unique_priority(s: &str) -> IResult<&str, UniquePriority> {
    alt((
        map(symbol("unique0"), |_| UniquePriority::Unique0),
        map(symbol("unique"), |_| UniquePriority::Unique),
        map(symbol("priority"), |_| UniquePriority::Priority),
    ))(s)
}

pub fn cond_predicate(s: &str) -> IResult<&str, CondPredicate> {
    let (s, pattern) = separated_nonempty_list(symbol("&&&"), expression_or_cond_pattern)(s)?;
    Ok((s, CondPredicate { pattern }))
}

pub fn expression_or_cond_pattern(s: &str) -> IResult<&str, ExpressionOrCondPattern> {
    alt((
        map(expression, |x| ExpressionOrCondPattern::Expression(x)),
        map(cond_pattern, |x| ExpressionOrCondPattern::CondPattern(x)),
    ))(s)
}

pub fn cond_pattern(s: &str) -> IResult<&str, CondPattern> {
    let (s, x) = expression(s)?;
    let (s, _) = symbol("matches")(s)?;
    let (s, y) = pattern(s)?;
    Ok((
        s,
        CondPattern {
            expression: x,
            pattern: y,
        },
    ))
}

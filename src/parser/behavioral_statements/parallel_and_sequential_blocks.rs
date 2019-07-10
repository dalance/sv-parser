use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum ActionBlock<'a> {
    StatementOrNull(StatementOrNull<'a>),
    Else(ActionBlockElse<'a>),
}

#[derive(Debug)]
pub struct ActionBlockElse<'a> {
    pub nodes: (Option<Statement<'a>>, Symbol<'a>, StatementOrNull<'a>),
}

#[derive(Debug)]
pub struct SeqBlock<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<(Symbol<'a>, BlockIdentifier<'a>)>,
        Vec<BlockItemDeclaration<'a>>,
        Vec<StatementOrNull<'a>>,
        Symbol<'a>,
        Option<(Symbol<'a>, BlockIdentifier<'a>)>,
    ),
}

#[derive(Debug)]
pub struct ParBlock<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<(Symbol<'a>, BlockIdentifier<'a>)>,
        Vec<BlockItemDeclaration<'a>>,
        Vec<StatementOrNull<'a>>,
        JoinKeyword<'a>,
        Option<(Symbol<'a>, BlockIdentifier<'a>)>,
    ),
}

#[derive(Debug)]
pub enum JoinKeyword<'a> {
    Join(Symbol<'a>),
    JoinAny(Symbol<'a>),
    JoinNone(Symbol<'a>),
}

// -----------------------------------------------------------------------------

pub fn action_block(s: Span) -> IResult<Span, ActionBlock> {
    alt((
        map(statement_or_null, |x| ActionBlock::StatementOrNull(x)),
        action_block_else,
    ))(s)
}

pub fn action_block_else(s: Span) -> IResult<Span, ActionBlock> {
    let (s, a) = opt(statement)(s)?;
    let (s, b) = symbol("else")(s)?;
    let (s, c) = statement_or_null(s)?;
    Ok((s, ActionBlock::Else(ActionBlockElse { nodes: (a, b, c) })))
}

pub fn seq_block(s: Span) -> IResult<Span, SeqBlock> {
    let (s, a) = symbol("begin")(s)?;
    let (s, b) = opt(pair(symbol(":"), block_identifier))(s)?;
    let (s, c) = many0(block_item_declaration)(s)?;
    let (s, d) = many0(statement_or_null)(s)?;
    let (s, e) = symbol("end")(s)?;
    let (s, f) = opt(pair(symbol(":"), block_identifier))(s)?;
    Ok((
        s,
        SeqBlock {
            nodes: (a, b, c, d, e, f),
        },
    ))
}

pub fn par_block(s: Span) -> IResult<Span, ParBlock> {
    let (s, a) = symbol("fork")(s)?;
    let (s, b) = opt(pair(symbol(":"), block_identifier))(s)?;
    let (s, c) = many0(block_item_declaration)(s)?;
    let (s, d) = many0(statement_or_null)(s)?;
    let (s, e) = join_keyword(s)?;
    let (s, f) = opt(pair(symbol(":"), block_identifier))(s)?;
    Ok((
        s,
        ParBlock {
            nodes: (a, b, c, d, e, f),
        },
    ))
}

pub fn join_keyword(s: Span) -> IResult<Span, JoinKeyword> {
    alt((
        map(symbol("join_any"), |x| JoinKeyword::JoinAny(x)),
        map(symbol("join_none"), |x| JoinKeyword::JoinNone(x)),
        map(symbol("join"), |x| JoinKeyword::Join(x)),
    ))(s)
}

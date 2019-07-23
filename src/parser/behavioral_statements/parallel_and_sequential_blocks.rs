use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum ActionBlock {
    StatementOrNull(StatementOrNull),
    Else(ActionBlockElse),
}

#[derive(Debug, Node)]
pub struct ActionBlockElse {
    pub nodes: (Option<Statement>, Keyword, StatementOrNull),
}

#[derive(Debug, Node)]
pub struct SeqBlock {
    pub nodes: (
        Keyword,
        Option<(Symbol, BlockIdentifier)>,
        Vec<BlockItemDeclaration>,
        Vec<StatementOrNull>,
        Keyword,
        Option<(Symbol, BlockIdentifier)>,
    ),
}

#[derive(Debug, Node)]
pub struct ParBlock {
    pub nodes: (
        Keyword,
        Option<(Symbol, BlockIdentifier)>,
        Vec<BlockItemDeclaration>,
        Vec<StatementOrNull>,
        JoinKeyword,
        Option<(Symbol, BlockIdentifier)>,
    ),
}

#[derive(Debug, Node)]
pub enum JoinKeyword {
    Join(Keyword),
    JoinAny(Keyword),
    JoinNone(Keyword),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn action_block(s: Span) -> IResult<Span, ActionBlock> {
    alt((
        map(statement_or_null, |x| ActionBlock::StatementOrNull(x)),
        action_block_else,
    ))(s)
}

#[parser]
pub fn action_block_else(s: Span) -> IResult<Span, ActionBlock> {
    let (s, a) = opt(statement)(s)?;
    let (s, b) = keyword("else")(s)?;
    let (s, c) = statement_or_null(s)?;
    Ok((s, ActionBlock::Else(ActionBlockElse { nodes: (a, b, c) })))
}

#[parser]
pub fn seq_block(s: Span) -> IResult<Span, SeqBlock> {
    let (s, a) = keyword("begin")(s)?;
    let (s, b) = opt(pair(symbol(":"), block_identifier))(s)?;
    let (s, c) = many0(block_item_declaration)(s)?;
    let (s, d) = many0(statement_or_null)(s)?;
    let (s, e) = keyword("end")(s)?;
    let (s, f) = opt(pair(symbol(":"), block_identifier))(s)?;
    Ok((
        s,
        SeqBlock {
            nodes: (a, b, c, d, e, f),
        },
    ))
}

#[parser]
pub fn par_block(s: Span) -> IResult<Span, ParBlock> {
    let (s, a) = keyword("fork")(s)?;
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

#[parser]
pub fn join_keyword(s: Span) -> IResult<Span, JoinKeyword> {
    alt((
        map(keyword("join_any"), |x| JoinKeyword::JoinAny(x)),
        map(keyword("join_none"), |x| JoinKeyword::JoinNone(x)),
        map(keyword("join"), |x| JoinKeyword::Join(x)),
    ))(s)
}

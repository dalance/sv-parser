use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum ActionBlock<'a> {
    Statement(StatementOrNull<'a>),
    Else(ActionBlockElse<'a>),
}

#[derive(Debug)]
pub struct ActionBlockElse<'a> {
    pub statement: Option<Statement<'a>>,
    pub else_statement: StatementOrNull<'a>,
}

#[derive(Debug)]
pub struct SeqBlock<'a> {
    pub beg_identifier: Option<Identifier<'a>>,
    pub declaration: Vec<BlockItemDeclaration<'a>>,
    pub statement: Vec<StatementOrNull<'a>>,
    pub end_identifier: Option<Identifier<'a>>,
}

#[derive(Debug)]
pub struct ParBlock<'a> {
    pub beg_identifier: Option<Identifier<'a>>,
    pub declaration: Vec<BlockItemDeclaration<'a>>,
    pub statement: Vec<StatementOrNull<'a>>,
    pub keyword: JoinKeyword,
    pub end_identifier: Option<Identifier<'a>>,
}

#[derive(Debug)]
pub enum JoinKeyword {
    Join,
    JoinAny,
    JoinNone,
}

// -----------------------------------------------------------------------------

pub fn action_block(s: &str) -> IResult<&str, ActionBlock> {
    alt((
        map(statement_or_null, |x| ActionBlock::Statement(x)),
        action_block_else,
    ))(s)
}

pub fn action_block_else(s: &str) -> IResult<&str, ActionBlock> {
    let (s, statement) = opt(statement)(s)?;
    let (s, _) = symbol("else")(s)?;
    let (s, else_statement) = statement_or_null(s)?;
    Ok((
        s,
        ActionBlock::Else(ActionBlockElse {
            statement,
            else_statement,
        }),
    ))
}

pub fn seq_block(s: &str) -> IResult<&str, SeqBlock> {
    let (s, _) = symbol("begin")(s)?;
    let (s, beg_identifier) = opt(preceded(symbol(":"), block_identifier))(s)?;
    let (s, declaration) = many0(block_item_declaration)(s)?;
    let (s, statement) = many0(statement_or_null)(s)?;
    let (s, _) = symbol("end")(s)?;
    let (s, end_identifier) = opt(preceded(symbol(":"), block_identifier))(s)?;
    Ok((
        s,
        SeqBlock {
            beg_identifier,
            declaration,
            statement,
            end_identifier,
        },
    ))
}

pub fn par_block(s: &str) -> IResult<&str, ParBlock> {
    let (s, _) = symbol("fork")(s)?;
    let (s, beg_identifier) = opt(preceded(symbol(":"), block_identifier))(s)?;
    let (s, declaration) = many0(block_item_declaration)(s)?;
    let (s, statement) = many0(statement_or_null)(s)?;
    let (s, keyword) = join_keyword(s)?;
    let (s, end_identifier) = opt(preceded(symbol(":"), block_identifier))(s)?;
    Ok((
        s,
        ParBlock {
            beg_identifier,
            declaration,
            statement,
            keyword,
            end_identifier,
        },
    ))
}

pub fn join_keyword(s: &str) -> IResult<&str, JoinKeyword> {
    alt((
        map(symbol("join_any"), |_| JoinKeyword::JoinAny),
        map(symbol("join_none"), |_| JoinKeyword::JoinNone),
        map(symbol("join"), |_| JoinKeyword::Join),
    ))(s)
}

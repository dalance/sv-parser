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
    let (s, x) = opt(statement)(s)?;
    let (s, _) = symbol("else")(s)?;
    let (s, y) = statement_or_null(s)?;
    Ok((
        s,
        ActionBlock::Else(ActionBlockElse {
            statement: x,
            else_statement: y,
        }),
    ))
}

pub fn seq_block(s: &str) -> IResult<&str, SeqBlock> {
    let (s, _) = symbol("begin")(s)?;
    let (s, x) = opt(preceded(symbol(":"), block_identifier))(s)?;
    let (s, y) = many0(block_item_declaration)(s)?;
    let (s, z) = many0(statement_or_null)(s)?;
    let (s, _) = symbol("end")(s)?;
    let (s, v) = opt(preceded(symbol(":"), block_identifier))(s)?;
    Ok((
        s,
        SeqBlock {
            beg_identifier: x,
            declaration: y,
            statement: z,
            end_identifier: v,
        },
    ))
}

pub fn par_block(s: &str) -> IResult<&str, ParBlock> {
    let (s, _) = symbol("fork")(s)?;
    let (s, x) = opt(preceded(symbol(":"), block_identifier))(s)?;
    let (s, y) = many0(block_item_declaration)(s)?;
    let (s, z) = many0(statement_or_null)(s)?;
    let (s, v) = join_keyword(s)?;
    let (s, w) = opt(preceded(symbol(":"), block_identifier))(s)?;
    Ok((
        s,
        ParBlock {
            beg_identifier: x,
            declaration: y,
            statement: z,
            keyword: v,
            end_identifier: w,
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

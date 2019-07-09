use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum BlockItemDeclaration<'a> {
    Data(BlockItemDeclarationData<'a>),
    LocalParameter(BlockItemDeclarationLocalParameter<'a>),
    Parameter(BlockItemDeclarationParameter<'a>),
    Let(BlockItemDeclarationLet<'a>),
}

#[derive(Debug)]
pub struct BlockItemDeclarationData<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, DataDeclaration<'a>),
}

#[derive(Debug)]
pub struct BlockItemDeclarationLocalParameter<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, LocalParameterDeclaration<'a>),
}

#[derive(Debug)]
pub struct BlockItemDeclarationParameter<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ParameterDeclaration<'a>),
}

#[derive(Debug)]
pub struct BlockItemDeclarationLet<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, LetDeclaration<'a>),
}

// -----------------------------------------------------------------------------

pub fn block_item_declaration(s: Span) -> IResult<Span, BlockItemDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

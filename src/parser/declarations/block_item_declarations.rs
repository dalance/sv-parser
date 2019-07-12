use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::multi::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum BlockItemDeclaration<'a> {
    Data(BlockItemDeclarationData<'a>),
    LocalParameter(BlockItemDeclarationLocalParameter<'a>),
    Parameter(BlockItemDeclarationParameter<'a>),
    Let(BlockItemDeclarationLet<'a>),
}

#[derive(Debug, Node)]
pub struct BlockItemDeclarationData<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, DataDeclaration<'a>),
}

#[derive(Debug, Node)]
pub struct BlockItemDeclarationLocalParameter<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        LocalParameterDeclaration<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct BlockItemDeclarationParameter<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        ParameterDeclaration<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct BlockItemDeclarationLet<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, LetDeclaration<'a>),
}

// -----------------------------------------------------------------------------

pub fn block_item_declaration(s: Span) -> IResult<Span, BlockItemDeclaration> {
    alt((
        block_item_declaration_data,
        block_item_declaration_local_parameter,
        block_item_declaration_parameter,
        block_item_declaration_let,
    ))(s)
}

pub fn block_item_declaration_data(s: Span) -> IResult<Span, BlockItemDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = data_declaration(s)?;
    Ok((
        s,
        BlockItemDeclaration::Data(BlockItemDeclarationData { nodes: (a, b) }),
    ))
}

pub fn block_item_declaration_local_parameter(s: Span) -> IResult<Span, BlockItemDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = local_parameter_declaration(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        BlockItemDeclaration::LocalParameter(BlockItemDeclarationLocalParameter {
            nodes: (a, b, c),
        }),
    ))
}

pub fn block_item_declaration_parameter(s: Span) -> IResult<Span, BlockItemDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = parameter_declaration(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        BlockItemDeclaration::Parameter(BlockItemDeclarationParameter { nodes: (a, b, c) }),
    ))
}

pub fn block_item_declaration_let(s: Span) -> IResult<Span, BlockItemDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = let_declaration(s)?;
    Ok((
        s,
        BlockItemDeclaration::Let(BlockItemDeclarationLet { nodes: (a, b) }),
    ))
}

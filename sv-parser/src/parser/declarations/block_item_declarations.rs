use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::multi::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum BlockItemDeclaration {
    Data(Box<BlockItemDeclarationData>),
    LocalParameter(Box<BlockItemDeclarationLocalParameter>),
    Parameter(Box<BlockItemDeclarationParameter>),
    Let(Box<BlockItemDeclarationLet>),
}

#[derive(Clone, Debug, Node)]
pub struct BlockItemDeclarationData {
    pub nodes: (Vec<AttributeInstance>, DataDeclaration),
}

#[derive(Clone, Debug, Node)]
pub struct BlockItemDeclarationLocalParameter {
    pub nodes: (Vec<AttributeInstance>, LocalParameterDeclaration, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct BlockItemDeclarationParameter {
    pub nodes: (Vec<AttributeInstance>, ParameterDeclaration, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct BlockItemDeclarationLet {
    pub nodes: (Vec<AttributeInstance>, LetDeclaration),
}

// -----------------------------------------------------------------------------

#[parser]
pub(crate) fn block_item_declaration(s: Span) -> IResult<Span, BlockItemDeclaration> {
    alt((
        block_item_declaration_data,
        block_item_declaration_local_parameter,
        block_item_declaration_parameter,
        block_item_declaration_let,
    ))(s)
}

#[parser(MaybeRecursive)]
pub(crate) fn block_item_declaration_data(s: Span) -> IResult<Span, BlockItemDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = data_declaration(s)?;
    Ok((
        s,
        BlockItemDeclaration::Data(Box::new(BlockItemDeclarationData { nodes: (a, b) })),
    ))
}

#[parser]
pub(crate) fn block_item_declaration_local_parameter(s: Span) -> IResult<Span, BlockItemDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = local_parameter_declaration(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        BlockItemDeclaration::LocalParameter(Box::new(BlockItemDeclarationLocalParameter {
            nodes: (a, b, c),
        })),
    ))
}

#[parser]
pub(crate) fn block_item_declaration_parameter(s: Span) -> IResult<Span, BlockItemDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = parameter_declaration(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        BlockItemDeclaration::Parameter(Box::new(BlockItemDeclarationParameter {
            nodes: (a, b, c),
        })),
    ))
}

#[parser]
pub(crate) fn block_item_declaration_let(s: Span) -> IResult<Span, BlockItemDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = let_declaration(s)?;
    Ok((
        s,
        BlockItemDeclaration::Let(Box::new(BlockItemDeclarationLet { nodes: (a, b) })),
    ))
}

use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct LetDeclaration<'a> {
    pub nodes: (
        Symbol<'a>,
        LetIdentifier<'a>,
        Option<Paren<'a, Option<LetPortList<'a>>>>,
        Symbol<'a>,
        Expression<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct LetIdentifier<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug, Node)]
pub struct LetPortList<'a> {
    pub nodes: (List<Symbol<'a>, LetPortItem<'a>>,),
}

#[derive(Debug, Node)]
pub struct LetPortItem<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        LetFormalType<'a>,
        FormalPortIdentifier<'a>,
        Vec<VariableDimension<'a>>,
        Option<(Symbol<'a>, Expression<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub enum LetFormalType<'a> {
    DataTypeOrImplicit(DataTypeOrImplicit<'a>),
    Untyped(Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct LetExpression<'a> {
    pub nodes: (
        Option<PackageScope<'a>>,
        LetIdentifier<'a>,
        Option<Paren<'a, Option<LetListOfArguments<'a>>>>,
    ),
}

#[derive(Debug, Node)]
pub enum LetListOfArguments<'a> {
    Ordered(LetListOfArgumentsOrdered<'a>),
    Named(LetListOfArgumentsNamed<'a>),
}

#[derive(Debug, Node)]
pub struct LetListOfArgumentsOrdered<'a> {
    pub nodes: (
        List<Symbol<'a>, Option<LetActualArg<'a>>>,
        Vec<(
            Symbol<'a>,
            Symbol<'a>,
            Identifier<'a>,
            Paren<'a, Option<LetActualArg<'a>>>,
        )>,
    ),
}

#[derive(Debug, Node)]
pub struct LetListOfArgumentsNamed<'a> {
    pub nodes: (
        List<
            Symbol<'a>,
            (
                Symbol<'a>,
                Identifier<'a>,
                Paren<'a, Option<LetActualArg<'a>>>,
            ),
        >,
    ),
}

#[derive(Debug, Node)]
pub struct LetActualArg<'a> {
    pub nodes: (Expression<'a>,),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn let_declaration(s: Span) -> IResult<Span, LetDeclaration> {
    let (s, a) = symbol("let")(s)?;
    let (s, b) = let_identifier(s)?;
    let (s, c) = opt(paren(opt(let_port_list)))(s)?;
    let (s, d) = symbol("=")(s)?;
    let (s, e) = expression(s)?;
    let (s, f) = symbol(";")(s)?;
    Ok((
        s,
        LetDeclaration {
            nodes: (a, b, c, d, e, f),
        },
    ))
}

#[parser]
pub fn let_identifier(s: Span) -> IResult<Span, LetIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, LetIdentifier { nodes: (a,) }))
}

#[parser]
pub fn let_port_list(s: Span) -> IResult<Span, LetPortList> {
    let (s, a) = list(symbol(","), let_port_item)(s)?;
    Ok((s, LetPortList { nodes: (a,) }))
}

#[parser]
pub fn let_port_item(s: Span) -> IResult<Span, LetPortItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = let_formal_type(s)?;
    let (s, c) = formal_port_identifier(s)?;
    let (s, d) = many0(variable_dimension)(s)?;
    let (s, e) = opt(pair(symbol("="), expression))(s)?;
    Ok((
        s,
        LetPortItem {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[parser]
pub fn let_formal_type(s: Span) -> IResult<Span, LetFormalType> {
    alt((
        map(data_type_or_implicit, |x| {
            LetFormalType::DataTypeOrImplicit(x)
        }),
        map(symbol("untyped"), |x| LetFormalType::Untyped(x)),
    ))(s)
}

#[parser]
pub fn let_expression(s: Span) -> IResult<Span, LetExpression> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = let_identifier(s)?;
    let (s, c) = opt(paren(opt(let_list_of_arguments)))(s)?;
    Ok((s, LetExpression { nodes: (a, b, c) }))
}

#[parser]
pub fn let_list_of_arguments(s: Span) -> IResult<Span, LetListOfArguments> {
    alt((let_list_of_arguments_ordered, let_list_of_arguments_named))(s)
}

#[parser]
pub fn let_list_of_arguments_ordered(s: Span) -> IResult<Span, LetListOfArguments> {
    let (s, a) = list(symbol(","), opt(let_actual_arg))(s)?;
    let (s, b) = many0(tuple((
        symbol(","),
        symbol("."),
        identifier,
        paren(opt(let_actual_arg)),
    )))(s)?;
    Ok((
        s,
        LetListOfArguments::Ordered(LetListOfArgumentsOrdered { nodes: (a, b) }),
    ))
}

#[parser]
pub fn let_list_of_arguments_named(s: Span) -> IResult<Span, LetListOfArguments> {
    let (s, a) = list(
        symbol(","),
        triple(symbol("."), identifier, paren(opt(let_actual_arg))),
    )(s)?;
    Ok((
        s,
        LetListOfArguments::Named(LetListOfArgumentsNamed { nodes: (a,) }),
    ))
}

#[parser]
pub fn let_actual_arg(s: Span) -> IResult<Span, LetActualArg> {
    let (s, a) = expression(s)?;
    Ok((s, LetActualArg { nodes: (a,) }))
}

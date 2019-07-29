use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
pub(crate) fn let_declaration(s: Span) -> IResult<Span, LetDeclaration> {
    let (s, a) = keyword("let")(s)?;
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

#[tracable_parser]
pub(crate) fn let_identifier(s: Span) -> IResult<Span, LetIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, LetIdentifier { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn let_port_list(s: Span) -> IResult<Span, LetPortList> {
    let (s, a) = list(symbol(","), let_port_item)(s)?;
    Ok((s, LetPortList { nodes: (a,) }))
}

#[both_parser]
#[tracable_parser]
pub(crate) fn let_port_item(s: Span) -> IResult<Span, LetPortItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = both_opt(let_formal_type)(s)?;
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

#[tracable_parser]
pub(crate) fn let_formal_type(s: Span) -> IResult<Span, LetFormalType> {
    alt((
        map(data_type_or_implicit, |x| {
            LetFormalType::DataTypeOrImplicit(Box::new(x))
        }),
        map(keyword("untyped"), |x| LetFormalType::Untyped(Box::new(x))),
    ))(s)
}

#[tracable_parser]
pub(crate) fn let_expression(s: Span) -> IResult<Span, LetExpression> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = let_identifier(s)?;
    let (s, c) = opt(paren(opt(let_list_of_arguments)))(s)?;
    Ok((s, LetExpression { nodes: (a, b, c) }))
}

#[tracable_parser]
pub(crate) fn let_list_of_arguments(s: Span) -> IResult<Span, LetListOfArguments> {
    alt((let_list_of_arguments_ordered, let_list_of_arguments_named))(s)
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn let_list_of_arguments_ordered(s: Span) -> IResult<Span, LetListOfArguments> {
    let (s, a) = list(symbol(","), opt(let_actual_arg))(s)?;
    let (s, b) = many0(tuple((
        symbol(","),
        symbol("."),
        identifier,
        paren(opt(let_actual_arg)),
    )))(s)?;
    Ok((
        s,
        LetListOfArguments::Ordered(Box::new(LetListOfArgumentsOrdered { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn let_list_of_arguments_named(s: Span) -> IResult<Span, LetListOfArguments> {
    let (s, a) = list(
        symbol(","),
        triple(symbol("."), identifier, paren(opt(let_actual_arg))),
    )(s)?;
    Ok((
        s,
        LetListOfArguments::Named(Box::new(LetListOfArgumentsNamed { nodes: (a,) })),
    ))
}

#[tracable_parser]
pub(crate) fn let_actual_arg(s: Span) -> IResult<Span, LetActualArg> {
    let (s, a) = expression(s)?;
    Ok((s, LetActualArg { nodes: (a,) }))
}

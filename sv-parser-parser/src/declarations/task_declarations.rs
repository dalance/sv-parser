use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
pub(crate) fn task_declaration(s: Span) -> IResult<Span, TaskDeclaration> {
    let (s, a) = keyword("task")(s)?;
    let (s, b) = opt(lifetime)(s)?;
    let (s, c) = task_body_declaration(s)?;
    Ok((s, TaskDeclaration { nodes: (a, b, c) }))
}

#[tracable_parser]
pub(crate) fn task_body_declaration(s: Span) -> IResult<Span, TaskBodyDeclaration> {
    alt((
        task_body_declaration_without_port,
        task_body_declaration_with_port,
    ))(s)
}

#[tracable_parser]
pub(crate) fn task_body_declaration_without_port(s: Span) -> IResult<Span, TaskBodyDeclaration> {
    let (s, a) = opt(interface_identifier_or_class_scope)(s)?;
    let (s, b) = task_identifier(s)?;
    let (s, c) = symbol(";")(s)?;
    let (s, d) = many0(tf_item_declaration)(s)?;
    let (s, e) = many0(statement_or_null)(s)?;
    let (s, f) = keyword("endtask")(s)?;
    let (s, g) = opt(pair(symbol(":"), task_identifier))(s)?;
    Ok((
        s,
        TaskBodyDeclaration::WithoutPort(Box::new(TaskBodyDeclarationWithoutPort {
            nodes: (a, b, c, d, e, f, g),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn task_body_declaration_with_port(s: Span) -> IResult<Span, TaskBodyDeclaration> {
    let (s, a) = opt(interface_identifier_or_class_scope)(s)?;
    let (s, b) = task_identifier(s)?;
    let (s, c) = paren(opt(tf_port_list))(s)?;
    let (s, d) = symbol(";")(s)?;
    let (s, e) = many0(block_item_declaration)(s)?;
    let (s, f) = many0(statement_or_null)(s)?;
    let (s, g) = keyword("endtask")(s)?;
    let (s, h) = opt(pair(symbol(":"), task_identifier))(s)?;
    Ok((
        s,
        TaskBodyDeclaration::WithPort(Box::new(TaskBodyDeclarationWithPort {
            nodes: (a, b, c, d, e, f, g, h),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn tf_item_declaration(s: Span) -> IResult<Span, TfItemDeclaration> {
    alt((
        map(block_item_declaration, |x| {
            TfItemDeclaration::BlockItemDeclaration(Box::new(x))
        }),
        map(tf_port_declaration, |x| {
            TfItemDeclaration::TfPortDeclaration(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
pub(crate) fn tf_port_list(s: Span) -> IResult<Span, TfPortList> {
    let (s, a) = list(symbol(","), tf_port_item)(s)?;
    Ok((s, TfPortList { nodes: (a,) }))
}

#[both_parser]
#[tracable_parser]
pub(crate) fn tf_port_item(s: Span) -> IResult<Span, TfPortItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = opt(tf_port_direction)(s)?;
    let (s, c) = opt(var)(s)?;
    let (s, d) = both_opt(data_type_or_implicit)(s)?;
    let (s, e) = opt(triple(
        port_identifier,
        many0(variable_dimension),
        opt(pair(symbol(":"), expression)),
    ))(s)?;
    Ok((
        s,
        TfPortItem {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[tracable_parser]
pub(crate) fn tf_port_direction(s: Span) -> IResult<Span, TfPortDirection> {
    alt((
        map(port_direction, |x| {
            TfPortDirection::PortDirection(Box::new(x))
        }),
        map(pair(keyword("const"), keyword("ref")), |x| {
            TfPortDirection::ConstRef(Box::new(x))
        }),
    ))(s)
}

#[both_parser]
#[tracable_parser]
pub(crate) fn tf_port_declaration(s: Span) -> IResult<Span, TfPortDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = tf_port_direction(s)?;
    let (s, c) = opt(var)(s)?;
    let (s, d) = both_opt(data_type_or_implicit)(s)?;
    let (s, e) = list_of_tf_variable_identifiers(s)?;
    let (s, f) = symbol(";")(s)?;
    Ok((
        s,
        TfPortDeclaration {
            nodes: (a, b, c, d, e, f),
        },
    ))
}

#[tracable_parser]
pub(crate) fn task_prototype(s: Span) -> IResult<Span, TaskPrototype> {
    let (s, a) = keyword("task")(s)?;
    let (s, b) = task_identifier(s)?;
    let (s, c) = opt(paren(opt(tf_port_list)))(s)?;
    Ok((s, TaskPrototype { nodes: (a, b, c) }))
}

use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
pub(crate) fn modport_declaration(s: Span) -> IResult<Span, ModportDeclaration> {
    let (s, a) = keyword("modport")(s)?;
    let (s, b) = list(symbol(","), modport_item)(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((s, ModportDeclaration { nodes: (a, b, c) }))
}

#[tracable_parser]
pub(crate) fn modport_item(s: Span) -> IResult<Span, ModportItem> {
    let (s, a) = modport_identifier(s)?;
    let (s, b) = paren(list(symbol(","), modport_ports_declaration))(s)?;
    Ok((s, ModportItem { nodes: (a, b) }))
}

#[tracable_parser]
pub(crate) fn modport_ports_declaration(s: Span) -> IResult<Span, ModportPortsDeclaraton> {
    alt((
        modport_ports_declaration_simple,
        modport_ports_declaration_tf,
        modport_ports_declaration_clocking,
    ))(s)
}

#[tracable_parser]
pub(crate) fn modport_ports_declaration_simple(s: Span) -> IResult<Span, ModportPortsDeclaraton> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = modport_simple_ports_declaration(s)?;
    Ok((
        s,
        ModportPortsDeclaraton::Simple(Box::new(ModportPortsDeclaratonSimple { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn modport_ports_declaration_tf(s: Span) -> IResult<Span, ModportPortsDeclaraton> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = modport_tf_ports_declaration(s)?;
    Ok((
        s,
        ModportPortsDeclaraton::Tf(Box::new(ModportPortsDeclaratonTf { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn modport_ports_declaration_clocking(s: Span) -> IResult<Span, ModportPortsDeclaraton> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = modport_clocking_declaration(s)?;
    Ok((
        s,
        ModportPortsDeclaraton::Clocking(Box::new(ModportPortsDeclaratonClocking {
            nodes: (a, b),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn modport_clocking_declaration(s: Span) -> IResult<Span, ModportClockingDeclaration> {
    let (s, a) = keyword("clocking")(s)?;
    let (s, b) = clocking_identifier(s)?;
    Ok((s, ModportClockingDeclaration { nodes: (a, b) }))
}

#[tracable_parser]
pub(crate) fn modport_simple_ports_declaration(
    s: Span,
) -> IResult<Span, ModportSimplePortsDeclaration> {
    let (s, a) = port_direction(s)?;
    let (s, b) = list(symbol(","), modport_simple_port)(s)?;
    Ok((s, ModportSimplePortsDeclaration { nodes: (a, b) }))
}

#[tracable_parser]
pub(crate) fn modport_simple_port(s: Span) -> IResult<Span, ModportSimplePort> {
    alt((modport_simple_port_ordered, modport_simple_port_named))(s)
}

#[tracable_parser]
pub(crate) fn modport_simple_port_ordered(s: Span) -> IResult<Span, ModportSimplePort> {
    let (s, a) = port_identifier(s)?;
    Ok((
        s,
        ModportSimplePort::Ordered(Box::new(ModportSimplePortOrdered { nodes: (a,) })),
    ))
}

#[tracable_parser]
pub(crate) fn modport_simple_port_named(s: Span) -> IResult<Span, ModportSimplePort> {
    let (s, a) = symbol(".")(s)?;
    let (s, b) = port_identifier(s)?;
    let (s, c) = paren(opt(expression))(s)?;
    Ok((
        s,
        ModportSimplePort::Named(Box::new(ModportSimplePortNamed { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
pub(crate) fn modport_tf_ports_declaration(s: Span) -> IResult<Span, ModportTfPortsDeclaration> {
    let (s, a) = import_export(s)?;
    let (s, b) = list(symbol(","), modport_tf_port)(s)?;
    Ok((s, ModportTfPortsDeclaration { nodes: (a, b) }))
}

#[tracable_parser]
pub(crate) fn modport_tf_port(s: Span) -> IResult<Span, ModportTfPort> {
    alt((
        map(method_prototype, |x| {
            ModportTfPort::MethodPrototype(Box::new(x))
        }),
        map(tf_identifier, |x| ModportTfPort::TfIdentifier(Box::new(x))),
    ))(s)
}

#[tracable_parser]
pub(crate) fn import_export(s: Span) -> IResult<Span, ImportExport> {
    alt((
        map(keyword("import"), |x| ImportExport::Import(Box::new(x))),
        map(keyword("export"), |x| ImportExport::Export(Box::new(x))),
    ))(s)
}

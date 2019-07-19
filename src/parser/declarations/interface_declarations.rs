use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct ModportDeclaration<'a> {
    pub nodes: (Keyword<'a>, List<Symbol<'a>, ModportItem<'a>>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct ModportItem<'a> {
    pub nodes: (
        ModportIdentifier<'a>,
        Paren<'a, List<Symbol<'a>, ModportPortsDeclaraton<'a>>>,
    ),
}

#[derive(Debug, Node)]
pub enum ModportPortsDeclaraton<'a> {
    Simple(ModportPortsDeclaratonSimple<'a>),
    Tf(ModportPortsDeclaratonTf<'a>),
    Clocking(ModportPortsDeclaratonClocking<'a>),
}

#[derive(Debug, Node)]
pub struct ModportPortsDeclaratonSimple<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        ModportSimplePortsDeclaration<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct ModportPortsDeclaratonTf<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ModportTfPortsDeclaration<'a>),
}

#[derive(Debug, Node)]
pub struct ModportPortsDeclaratonClocking<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ModportClockingDeclaration<'a>),
}

#[derive(Debug, Node)]
pub struct ModportClockingDeclaration<'a> {
    pub nodes: (Keyword<'a>, ClockingIdentifier<'a>),
}

#[derive(Debug, Node)]
pub struct ModportSimplePortsDeclaration<'a> {
    pub nodes: (PortDirection<'a>, List<Symbol<'a>, ModportSimplePort<'a>>),
}

#[derive(Debug, Node)]
pub enum ModportSimplePort<'a> {
    Ordered(ModportSimplePortOrdered<'a>),
    Named(ModportSimplePortNamed<'a>),
}

#[derive(Debug, Node)]
pub struct ModportSimplePortOrdered<'a> {
    pub nodes: (PortIdentifier<'a>,),
}

#[derive(Debug, Node)]
pub struct ModportSimplePortNamed<'a> {
    pub nodes: (
        Symbol<'a>,
        PortIdentifier<'a>,
        Paren<'a, Option<Expression<'a>>>,
    ),
}

#[derive(Debug, Node)]
pub struct ModportTfPortsDeclaration<'a> {
    pub nodes: (ImportExport<'a>, List<Symbol<'a>, ModportTfPort<'a>>),
}

#[derive(Debug, Node)]
pub enum ModportTfPort<'a> {
    MethodPrototype(MethodPrototype<'a>),
    TfIdentifier(TfIdentifier<'a>),
}

#[derive(Debug, Node)]
pub enum ImportExport<'a> {
    Import(Keyword<'a>),
    Export(Keyword<'a>),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn modport_declaration(s: Span) -> IResult<Span, ModportDeclaration> {
    let (s, a) = keyword("modport")(s)?;
    let (s, b) = list(symbol(","), modport_item)(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((s, ModportDeclaration { nodes: (a, b, c) }))
}

#[parser]
pub fn modport_item(s: Span) -> IResult<Span, ModportItem> {
    let (s, a) = modport_identifier(s)?;
    let (s, b) = paren(list(symbol(","), modport_ports_declaration))(s)?;
    Ok((s, ModportItem { nodes: (a, b) }))
}

#[parser]
pub fn modport_ports_declaration(s: Span) -> IResult<Span, ModportPortsDeclaraton> {
    alt((
        modport_ports_declaration_simple,
        modport_ports_declaration_tf,
        modport_ports_declaration_clocking,
    ))(s)
}

#[parser]
pub fn modport_ports_declaration_simple(s: Span) -> IResult<Span, ModportPortsDeclaraton> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = modport_simple_ports_declaration(s)?;
    Ok((
        s,
        ModportPortsDeclaraton::Simple(ModportPortsDeclaratonSimple { nodes: (a, b) }),
    ))
}

#[parser]
pub fn modport_ports_declaration_tf(s: Span) -> IResult<Span, ModportPortsDeclaraton> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = modport_tf_ports_declaration(s)?;
    Ok((
        s,
        ModportPortsDeclaraton::Tf(ModportPortsDeclaratonTf { nodes: (a, b) }),
    ))
}

#[parser]
pub fn modport_ports_declaration_clocking(s: Span) -> IResult<Span, ModportPortsDeclaraton> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = modport_clocking_declaration(s)?;
    Ok((
        s,
        ModportPortsDeclaraton::Clocking(ModportPortsDeclaratonClocking { nodes: (a, b) }),
    ))
}

#[parser]
pub fn modport_clocking_declaration(s: Span) -> IResult<Span, ModportClockingDeclaration> {
    let (s, a) = keyword("clocking")(s)?;
    let (s, b) = clocking_identifier(s)?;
    Ok((s, ModportClockingDeclaration { nodes: (a, b) }))
}

#[parser]
pub fn modport_simple_ports_declaration(s: Span) -> IResult<Span, ModportSimplePortsDeclaration> {
    let (s, a) = port_direction(s)?;
    let (s, b) = list(symbol(","), modport_simple_port)(s)?;
    Ok((s, ModportSimplePortsDeclaration { nodes: (a, b) }))
}

#[parser]
pub fn modport_simple_port(s: Span) -> IResult<Span, ModportSimplePort> {
    alt((modport_simple_port_ordered, modport_simple_port_named))(s)
}

#[parser]
pub fn modport_simple_port_ordered(s: Span) -> IResult<Span, ModportSimplePort> {
    let (s, a) = port_identifier(s)?;
    Ok((
        s,
        ModportSimplePort::Ordered(ModportSimplePortOrdered { nodes: (a,) }),
    ))
}

#[parser]
pub fn modport_simple_port_named(s: Span) -> IResult<Span, ModportSimplePort> {
    let (s, a) = symbol(".")(s)?;
    let (s, b) = port_identifier(s)?;
    let (s, c) = paren(opt(expression))(s)?;
    Ok((
        s,
        ModportSimplePort::Named(ModportSimplePortNamed { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn modport_tf_ports_declaration(s: Span) -> IResult<Span, ModportTfPortsDeclaration> {
    let (s, a) = import_export(s)?;
    let (s, b) = list(symbol(","), modport_tf_port)(s)?;
    Ok((s, ModportTfPortsDeclaration { nodes: (a, b) }))
}

#[parser]
pub fn modport_tf_port(s: Span) -> IResult<Span, ModportTfPort> {
    alt((
        map(method_prototype, |x| ModportTfPort::MethodPrototype(x)),
        map(tf_identifier, |x| ModportTfPort::TfIdentifier(x)),
    ))(s)
}

#[parser]
pub fn import_export(s: Span) -> IResult<Span, ImportExport> {
    alt((
        map(keyword("import"), |x| ImportExport::Import(x)),
        map(keyword("export"), |x| ImportExport::Export(x)),
    ))(s)
}

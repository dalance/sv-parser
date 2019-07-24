use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct ModportDeclaration {
    pub nodes: (Keyword, List<Symbol, ModportItem>, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct ModportItem {
    pub nodes: (
        ModportIdentifier,
        Paren<List<Symbol, ModportPortsDeclaraton>>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum ModportPortsDeclaraton {
    Simple(Box<ModportPortsDeclaratonSimple>),
    Tf(Box<ModportPortsDeclaratonTf>),
    Clocking(Box<ModportPortsDeclaratonClocking>),
}

#[derive(Clone, Debug, Node)]
pub struct ModportPortsDeclaratonSimple {
    pub nodes: (Vec<AttributeInstance>, ModportSimplePortsDeclaration),
}

#[derive(Clone, Debug, Node)]
pub struct ModportPortsDeclaratonTf {
    pub nodes: (Vec<AttributeInstance>, ModportTfPortsDeclaration),
}

#[derive(Clone, Debug, Node)]
pub struct ModportPortsDeclaratonClocking {
    pub nodes: (Vec<AttributeInstance>, ModportClockingDeclaration),
}

#[derive(Clone, Debug, Node)]
pub struct ModportClockingDeclaration {
    pub nodes: (Keyword, ClockingIdentifier),
}

#[derive(Clone, Debug, Node)]
pub struct ModportSimplePortsDeclaration {
    pub nodes: (PortDirection, List<Symbol, ModportSimplePort>),
}

#[derive(Clone, Debug, Node)]
pub enum ModportSimplePort {
    Ordered(Box<ModportSimplePortOrdered>),
    Named(Box<ModportSimplePortNamed>),
}

#[derive(Clone, Debug, Node)]
pub struct ModportSimplePortOrdered {
    pub nodes: (PortIdentifier,),
}

#[derive(Clone, Debug, Node)]
pub struct ModportSimplePortNamed {
    pub nodes: (Symbol, PortIdentifier, Paren<Option<Expression>>),
}

#[derive(Clone, Debug, Node)]
pub struct ModportTfPortsDeclaration {
    pub nodes: (ImportExport, List<Symbol, ModportTfPort>),
}

#[derive(Clone, Debug, Node)]
pub enum ModportTfPort {
    MethodPrototype(Box<MethodPrototype>),
    TfIdentifier(Box<TfIdentifier>),
}

#[derive(Clone, Debug, Node)]
pub enum ImportExport {
    Import(Box<Keyword>),
    Export(Box<Keyword>),
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
        ModportPortsDeclaraton::Simple(Box::new(ModportPortsDeclaratonSimple { nodes: (a, b) })),
    ))
}

#[parser]
pub fn modport_ports_declaration_tf(s: Span) -> IResult<Span, ModportPortsDeclaraton> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = modport_tf_ports_declaration(s)?;
    Ok((
        s,
        ModportPortsDeclaraton::Tf(Box::new(ModportPortsDeclaratonTf { nodes: (a, b) })),
    ))
}

#[parser]
pub fn modport_ports_declaration_clocking(s: Span) -> IResult<Span, ModportPortsDeclaraton> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = modport_clocking_declaration(s)?;
    Ok((
        s,
        ModportPortsDeclaraton::Clocking(Box::new(ModportPortsDeclaratonClocking {
            nodes: (a, b),
        })),
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
        ModportSimplePort::Ordered(Box::new(ModportSimplePortOrdered { nodes: (a,) })),
    ))
}

#[parser]
pub fn modport_simple_port_named(s: Span) -> IResult<Span, ModportSimplePort> {
    let (s, a) = symbol(".")(s)?;
    let (s, b) = port_identifier(s)?;
    let (s, c) = paren(opt(expression))(s)?;
    Ok((
        s,
        ModportSimplePort::Named(Box::new(ModportSimplePortNamed { nodes: (a, b, c) })),
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
        map(method_prototype, |x| {
            ModportTfPort::MethodPrototype(Box::new(x))
        }),
        map(tf_identifier, |x| ModportTfPort::TfIdentifier(Box::new(x))),
    ))(s)
}

#[parser]
pub fn import_export(s: Span) -> IResult<Span, ImportExport> {
    alt((
        map(keyword("import"), |x| ImportExport::Import(Box::new(x))),
        map(keyword("export"), |x| ImportExport::Export(Box::new(x))),
    ))(s)
}

use crate::ast::*;
use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct ModportDeclaration<'a> {
    pub nodes: (Symbol<'a>, List<Symbol<'a>, ModportItem<'a>>, Symbol<'a>),
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
    Clocing(ModportPortsDeclaratonClocking<'a>),
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
    pub nodes: (Symbol<'a>, ClockingIdentifier<'a>),
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
    Import(Symbol<'a>),
    Export(Symbol<'a>),
}

// -----------------------------------------------------------------------------

pub fn modport_declaration(s: Span) -> IResult<Span, ModportDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn modport_item(s: Span) -> IResult<Span, ModportItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn modport_ports_declaration(s: Span) -> IResult<Span, ModportPortsDeclaraton> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn modport_clocking_declaration(s: Span) -> IResult<Span, ModportClockingDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn modport_simple_ports_declaration(s: Span) -> IResult<Span, ModportSimplePortsDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn modport_simple_port(s: Span) -> IResult<Span, ModportSimplePort> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn modport_tf_ports_declaration(s: Span) -> IResult<Span, ModportTfPortsDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn modport_tf_port(s: Span) -> IResult<Span, ModportTfPort> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn import_export(s: Span) -> IResult<Span, ImportExport> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

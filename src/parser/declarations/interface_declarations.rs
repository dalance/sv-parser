use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct ModportDeclaration<'a> {
    pub nodes: (Vec<ModportItem<'a>>,),
}

#[derive(Debug)]
pub struct ModportItem<'a> {
    pub nodes: (Identifier<'a>, Vec<ModportPortsDeclaraton<'a>>),
}

#[derive(Debug)]
pub enum ModportPortsDeclaraton<'a> {
    Simple(ModportPortsDeclaratonSimple<'a>),
    Tf(ModportPortsDeclaratonTf<'a>),
    Clocing(ModportPortsDeclaratonClocking<'a>),
}

#[derive(Debug)]
pub struct ModportPortsDeclaratonSimple<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        ModportSimplePortsDeclaration<'a>,
    ),
}

#[derive(Debug)]
pub struct ModportPortsDeclaratonTf<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ModportTfPortsDeclaration<'a>),
}

#[derive(Debug)]
pub struct ModportPortsDeclaratonClocking<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ModportClockingDeclaration<'a>),
}

#[derive(Debug)]
pub struct ModportClockingDeclaration<'a> {
    pub nodes: (Identifier<'a>),
}

#[derive(Debug)]
pub struct ModportSimplePortsDeclaration<'a> {
    pub nodes: (PortDirection, Vec<ModportSimplePort<'a>>),
}

#[derive(Debug)]
pub enum ModportSimplePort<'a> {
    Ordered(ModportSimplePortOrdered<'a>),
    Named(ModportSimplePortNamed<'a>),
}

#[derive(Debug)]
pub struct ModportSimplePortOrdered<'a> {
    pub nodes: (Identifier<'a>,),
}

#[derive(Debug)]
pub struct ModportSimplePortNamed<'a> {
    pub nodes: (Identifier<'a>, Option<Expression<'a>>),
}

#[derive(Debug)]
pub struct ModportTfPortsDeclaration<'a> {
    pub nodes: (ImportExport, Vec<ModportTfPort<'a>>),
}

#[derive(Debug)]
pub enum ModportTfPort<'a> {
    Prototype(MethodPrototype<'a>),
    Identifier(Identifier<'a>),
}

#[derive(Debug)]
pub enum ImportExport {
    Import,
    Export,
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

use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum InterfaceOrGenerateItem<'a> {
    Module(InterfaceOrGenerateItemModule<'a>),
    Extern(InterfaceOrGenerateItemExtern<'a>),
}

#[derive(Debug)]
pub struct InterfaceOrGenerateItemModule<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ModuleCommonItem<'a>),
}

#[derive(Debug)]
pub struct InterfaceOrGenerateItemExtern<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ExternTfDeclaration<'a>),
}

#[derive(Debug)]
pub enum ExternTfDeclaration<'a> {
    Method(ExternTfDeclarationMethod<'a>),
    Task(ExternTfDeclarationTask<'a>),
}

#[derive(Debug)]
pub struct ExternTfDeclarationMethod<'a> {
    pub nodes: (MethodPrototype<'a>),
}

#[derive(Debug)]
pub struct ExternTfDeclarationTask<'a> {
    pub nodes: (TaskPrototype<'a>),
}

#[derive(Debug)]
pub enum InterfaceItem<'a> {
    PortDeclaration(PortDeclaration<'a>),
    NonPortInterfaceItem(NonPortInterfaceItem<'a>),
}

#[derive(Debug)]
pub enum NonPortInterfaceItem<'a> {
    GenerateRegion(GenerateRegion<'a>),
    InterfaceOrGenerateItem(InterfaceOrGenerateItem<'a>),
    ProgramDeclaration(ProgramDeclaration<'a>),
    ModportDeclaration(ModportDeclaration<'a>),
    InterfaceDeclaration(InterfaceDeclaration<'a>),
    TimeunitsDeclaration(TimeunitsDeclaration<'a>),
}

// -----------------------------------------------------------------------------

pub fn interface_or_generate_item(s: Span) -> IResult<Span, InterfaceOrGenerateItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn extern_tf_declaration(s: Span) -> IResult<Span, ExternTfDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn interface_item(s: Span) -> IResult<Span, InterfaceItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn non_port_interface_item(s: Span) -> IResult<Span, NonPortInterfaceItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

use crate::ast::*;
use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct TaskDeclaration<'a> {
    pub nodes: (Option<Lifetime<'a>>, TaskBodyDeclaration<'a>),
}

#[derive(Debug, Node)]
pub enum TaskBodyDeclaration<'a> {
    WithoutPort(TaskBodyDeclarationWithoutPort<'a>),
    WithPort(TaskBodyDeclarationWithPort<'a>),
}

#[derive(Debug, Node)]
pub struct TaskBodyDeclarationWithoutPort<'a> {
    pub nodes: (
        Option<InterfaceIdentifierOrClassScope<'a>>,
        Identifier<'a>,
        Vec<TfItemDeclaration<'a>>,
        Vec<FunctionStatementOrNull<'a>>,
        Option<Identifier<'a>>,
    ),
}

#[derive(Debug, Node)]
pub struct TaskBodyDeclarationWithPort<'a> {
    pub nodes: (
        Option<InterfaceIdentifierOrClassScope<'a>>,
        Identifier<'a>,
        Option<TfPortList<'a>>,
        Vec<BlockItemDeclaration<'a>>,
        Vec<FunctionStatementOrNull<'a>>,
        Option<Identifier<'a>>,
    ),
}

#[derive(Debug, Node)]
pub enum InterfaceIdentifierOrClassScope<'a> {
    InterfaceIdentifier(InterfaceIdentifier<'a>),
    ClassScope(ClassScope<'a>),
}

#[derive(Debug, Node)]
pub enum TfItemDeclaration<'a> {
    Block(BlockItemDeclaration<'a>),
    Port(TfPortDeclaration<'a>),
}

#[derive(Debug, Node)]
pub struct TfPortList<'a> {
    pub nodes: (Vec<TfPortItem<'a>>,),
}

#[derive(Debug, Node)]
pub struct TfPortItem<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Option<TfPortDirection<'a>>,
        Option<Var<'a>>,
        DataTypeOrImplicit<'a>,
        Option<(
            Identifier<'a>,
            Vec<VariableDimension<'a>>,
            Option<Expression<'a>>,
        )>,
    ),
}

#[derive(Debug, Node)]
pub enum TfPortDirection<'a> {
    PortDirection(PortDirection<'a>),
    ConstRef(Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct TfPortDeclaration<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        TfPortDirection<'a>,
        Option<Var<'a>>,
        DataTypeOrImplicit<'a>,
        ListOfTfVariableIdentifiers<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct TaskPrototype<'a> {
    pub nodes: (Identifier<'a>, Option<TfPortList<'a>>),
}

// -----------------------------------------------------------------------------

pub fn task_declaration(s: Span) -> IResult<Span, TaskDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn task_body_declaration(s: Span) -> IResult<Span, TaskBodyDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn tf_item_declaration(s: Span) -> IResult<Span, TfItemDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn tf_port_list(s: Span) -> IResult<Span, TfPortList> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn tf_port_item(s: Span) -> IResult<Span, TfPortItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn tf_port_direction(s: Span) -> IResult<Span, TfPortDirection> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn tf_port_declaration(s: Span) -> IResult<Span, TfPortDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn task_prototype(s: Span) -> IResult<Span, TaskPrototype> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

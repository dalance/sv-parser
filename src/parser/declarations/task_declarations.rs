use crate::ast::*;
use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct TaskDeclaration<'a> {
    pub nodes: (Symbol<'a>, Option<Lifetime<'a>>, TaskBodyDeclaration<'a>),
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
        TaskIdentifier<'a>,
        Symbol<'a>,
        Vec<TfItemDeclaration<'a>>,
        Vec<StatementOrNull<'a>>,
        Symbol<'a>,
        Option<(Symbol<'a>, TaskIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct TaskBodyDeclarationWithPort<'a> {
    pub nodes: (
        Option<InterfaceIdentifierOrClassScope<'a>>,
        TaskIdentifier<'a>,
        Paren<'a, Option<TfPortList<'a>>>,
        Symbol<'a>,
        Vec<BlockItemDeclaration<'a>>,
        Vec<StatementOrNull<'a>>,
        Option<(Symbol<'a>, TaskIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub enum InterfaceIdentifierOrClassScope<'a> {
    InterfaceIdentifier((InterfaceIdentifier<'a>, Symbol<'a>)),
    ClassScope(ClassScope<'a>),
}

#[derive(Debug, Node)]
pub enum TfItemDeclaration<'a> {
    BlockItemDeclaration(BlockItemDeclaration<'a>),
    TfPortDeclaration(TfPortDeclaration<'a>),
}

#[derive(Debug, Node)]
pub struct TfPortList<'a> {
    pub nodes: (List<Symbol<'a>, TfPortItem<'a>>,),
}

#[derive(Debug, Node)]
pub struct TfPortItem<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Option<TfPortDirection<'a>>,
        Option<Var<'a>>,
        DataTypeOrImplicit<'a>,
        Option<(
            PortIdentifier<'a>,
            Vec<VariableDimension<'a>>,
            Option<(Symbol<'a>, Expression<'a>)>,
        )>,
    ),
}

#[derive(Debug, Node)]
pub enum TfPortDirection<'a> {
    PortDirection(PortDirection<'a>),
    ConstRef((Symbol<'a>, Symbol<'a>)),
}

#[derive(Debug, Node)]
pub struct TfPortDeclaration<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        TfPortDirection<'a>,
        Option<Var<'a>>,
        DataTypeOrImplicit<'a>,
        ListOfTfVariableIdentifiers<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct TaskPrototype<'a> {
    pub nodes: (
        Symbol<'a>,
        TaskIdentifier<'a>,
        Option<Paren<'a, Option<TfPortList<'a>>>>,
    ),
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

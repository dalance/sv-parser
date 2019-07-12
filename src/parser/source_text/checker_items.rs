use crate::ast::*;
use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct CheckerPortList<'a> {
    pub nodes: (Vec<CheckerPortItem<'a>>,),
}

#[derive(Debug, Node)]
pub struct CheckerPortItem<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Option<CheckerPortDirection<'a>>,
        PropertyFormalType<'a>,
        FormalPortIdentifier<'a>,
        Vec<VariableDimension<'a>>,
        Option<PropertyActualArg<'a>>,
    ),
}

#[derive(Debug, Node)]
pub enum CheckerPortDirection<'a> {
    Input(Symbol<'a>),
    Output(Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum CheckerOrGenerateItem<'a> {
    CheckerOrGenerateItemDeclaration(CheckerOrGenerateItemDeclaration<'a>),
    InitialConstruct(InitialConstruct<'a>),
    AlwaysConstruct(AlwaysConstruct<'a>),
    FinalConstruct(FinalConstruct<'a>),
    AssertionItem(AssertionItem<'a>),
    ContinuousAssign(ContinuousAssign<'a>),
    CheckerGenerateItem(CheckerGenerateItem<'a>),
}

#[derive(Debug, Node)]
pub enum CheckerOrGenerateItemDeclaration<'a> {
    Data(CheckerOrGenerateItemDeclarationData<'a>),
    FunctionDeclaration(FunctionDeclaration<'a>),
    CheckerDeclaration(CheckerDeclaration<'a>),
    AssertionItemDeclaration(AssertionItemDeclaration<'a>),
    CovergroupDeclaration(CovergroupDeclaration<'a>),
    GenvarDeclaration(GenvarDeclaration<'a>),
    ClockingDeclaration(ClockingDeclaration<'a>),
    Clocking(CheckerOrGenerateItemDeclarationClocking<'a>),
    Expression(CheckerOrGenerateItemDeclarationExpression<'a>),
    Empty(Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct CheckerOrGenerateItemDeclarationData<'a> {
    pub nodes: (Option<Rand<'a>>, DataDeclaration<'a>),
}

#[derive(Debug, Node)]
pub struct Rand<'a> {
    pub nodes: (Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct CheckerOrGenerateItemDeclarationClocking<'a> {
    pub nodes: (ClockingIdentifier<'a>,),
}

#[derive(Debug, Node)]
pub struct CheckerOrGenerateItemDeclarationExpression<'a> {
    pub nodes: (ExpressionOrDist<'a>,),
}

#[derive(Debug, Node)]
pub enum CheckerGenerateItem<'a> {
    LoopGenerateConstruct(Box<LoopGenerateConstruct<'a>>),
    ConditionalGenerateConstruct(Box<ConditionalGenerateConstruct<'a>>),
    GenerateRegion(GenerateRegion<'a>),
    ElaborationSystemTask(ElaborationSystemTask<'a>),
}

// -----------------------------------------------------------------------------

pub fn checker_port_list(s: Span) -> IResult<Span, CheckerPortList> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn checker_port_item(s: Span) -> IResult<Span, CheckerPortItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn checker_port_direction(s: Span) -> IResult<Span, CheckerPortDirection> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn checker_or_generate_item(s: Span) -> IResult<Span, CheckerOrGenerateItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn checker_or_generate_item_declaration(
    s: Span,
) -> IResult<Span, CheckerOrGenerateItemDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn checker_generate_item(s: Span) -> IResult<Span, CheckerGenerateItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

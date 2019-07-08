use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct CheckerPortList<'a> {
    pub nodes: (Vec<CheckerPortItem<'a>>,),
}

#[derive(Debug)]
pub struct CheckerPortItem<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Option<CheckerPortDirection>,
        PropertyFormalType<'a>,
        FormalPortIdentifier<'a>,
        Vec<VariableDimension<'a>>,
        Option<PropertyActualArg<'a>>,
    ),
}

#[derive(Debug)]
pub enum CheckerPortDirection {
    Input,
    Output,
}

#[derive(Debug)]
pub enum CheckerOrGenerateItem<'a> {
    CheckerOrGenerateItemDeclaration(CheckerOrGenerateItemDeclaration<'a>),
    InitialConstruct(InitialConstruct<'a>),
    AlwaysConstruct(AlwaysConstruct<'a>),
    FinalConstruct(FinalConstruct<'a>),
    AssertionItem(AssertionItem<'a>),
    ContinuousAssign(ContinuousAssign<'a>),
    CheckerGenerateItem(CheckerGenerateItem<'a>),
}

#[derive(Debug)]
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
    Empty,
}

#[derive(Debug)]
pub struct CheckerOrGenerateItemDeclarationData<'a> {
    pub nodes: (Option<Rand>, DataDeclaration<'a>),
}

#[derive(Debug)]
pub struct Rand {}

#[derive(Debug)]
pub struct CheckerOrGenerateItemDeclarationClocking<'a> {
    pub nodes: (ClockingIdentifier<'a>,),
}

#[derive(Debug)]
pub struct CheckerOrGenerateItemDeclarationExpression<'a> {
    pub nodes: (ExpressionOrDist<'a>,),
}

#[derive(Debug)]
pub enum CheckerGenerateItem<'a> {
    LoopGenerateConstruct(Box<LoopGenerateConstruct<'a>>),
    ConditionalGenerateConstruct(Box<ConditionalGenerateConstruct<'a>>),
    GenerateRegion(GenerateRegion<'a>),
    ElaborationSystemTask(ElaborationSystemTask<'a>),
}

// -----------------------------------------------------------------------------

pub fn checker_port_list(s: &str) -> IResult<&str, CheckerPortList> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn checker_port_item(s: &str) -> IResult<&str, CheckerPortItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn checker_port_direction(s: &str) -> IResult<&str, CheckerPortDirection> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn checker_or_generate_item(s: &str) -> IResult<&str, CheckerOrGenerateItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn checker_or_generate_item_declaration(
    s: &str,
) -> IResult<&str, CheckerOrGenerateItemDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn checker_generate_item(s: &str) -> IResult<&str, CheckerGenerateItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

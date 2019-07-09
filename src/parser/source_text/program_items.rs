use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum ProgramItem<'a> {
    PortDeclaration(PortDeclaration<'a>),
    NonPortProgramItem(NonPortProgramItem<'a>),
}

#[derive(Debug)]
pub enum NonPortProgramItem<'a> {
    Assign(NonPortProgramItemAssign<'a>),
    Module(NonPortProgramItemModule<'a>),
    Initial(NonPortProgramItemInitial<'a>),
    Final(NonPortProgramItemFinal<'a>),
    Assertion(NonPortProgramItemAssertion<'a>),
    TimeunitsDeclaration(TimeunitsDeclaration<'a>),
    ProgramGenerateItem(ProgramGenerateItem<'a>),
}

#[derive(Debug)]
pub struct NonPortProgramItemAssign<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ContinuousAssign<'a>),
}

#[derive(Debug)]
pub struct NonPortProgramItemModule<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        ModuleOrGenerateItemDeclaration<'a>,
    ),
}

#[derive(Debug)]
pub struct NonPortProgramItemInitial<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, InitialConstruct<'a>),
}

#[derive(Debug)]
pub struct NonPortProgramItemFinal<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, FinalConstruct<'a>),
}

#[derive(Debug)]
pub struct NonPortProgramItemAssertion<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ConcurrentAssertionItem<'a>),
}

#[derive(Debug)]
pub enum ProgramGenerateItem<'a> {
    LoopGenerateConstuct(LoopGenerateConstruct<'a>),
    ConditionalGenerateConstruct(ConditionalGenerateConstruct<'a>),
    GenerateRegion(GenerateRegion<'a>),
    ElaborationSystemTask(ElaborationSystemTask<'a>),
}

// -----------------------------------------------------------------------------

pub fn program_item(s: Span) -> IResult<Span, ProgramItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn non_port_program_item(s: Span) -> IResult<Span, NonPortProgramItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn program_generate_item(s: Span) -> IResult<Span, ProgramGenerateItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

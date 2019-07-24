use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum ProgramItem {
    PortDeclaration(Box<(PortDeclaration, Symbol)>),
    NonPortProgramItem(Box<NonPortProgramItem>),
}

#[derive(Clone, Debug, Node)]
pub enum NonPortProgramItem {
    Assign(Box<NonPortProgramItemAssign>),
    Module(Box<NonPortProgramItemModule>),
    Initial(Box<NonPortProgramItemInitial>),
    Final(Box<NonPortProgramItemFinal>),
    Assertion(Box<NonPortProgramItemAssertion>),
    TimeunitsDeclaration(Box<TimeunitsDeclaration>),
    ProgramGenerateItem(Box<ProgramGenerateItem>),
}

#[derive(Clone, Debug, Node)]
pub struct NonPortProgramItemAssign {
    pub nodes: (Vec<AttributeInstance>, ContinuousAssign),
}

#[derive(Clone, Debug, Node)]
pub struct NonPortProgramItemModule {
    pub nodes: (Vec<AttributeInstance>, ModuleOrGenerateItemDeclaration),
}

#[derive(Clone, Debug, Node)]
pub struct NonPortProgramItemInitial {
    pub nodes: (Vec<AttributeInstance>, InitialConstruct),
}

#[derive(Clone, Debug, Node)]
pub struct NonPortProgramItemFinal {
    pub nodes: (Vec<AttributeInstance>, FinalConstruct),
}

#[derive(Clone, Debug, Node)]
pub struct NonPortProgramItemAssertion {
    pub nodes: (Vec<AttributeInstance>, ConcurrentAssertionItem),
}

#[derive(Clone, Debug, Node)]
pub enum ProgramGenerateItem {
    LoopGenerateConstruct(Box<LoopGenerateConstruct>),
    ConditionalGenerateConstruct(Box<ConditionalGenerateConstruct>),
    GenerateRegion(Box<GenerateRegion>),
    ElaborationSystemTask(Box<ElaborationSystemTask>),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn program_item(s: Span) -> IResult<Span, ProgramItem> {
    alt((
        map(pair(port_declaration, symbol(";")), |x| {
            ProgramItem::PortDeclaration(Box::new(x))
        }),
        map(non_port_program_item, |x| {
            ProgramItem::NonPortProgramItem(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn non_port_program_item(s: Span) -> IResult<Span, NonPortProgramItem> {
    alt((
        non_port_program_item_assign,
        non_port_program_item_module,
        non_port_program_item_initial,
        non_port_program_item_final,
        non_port_program_item_assertion,
        map(timeunits_declaration, |x| {
            NonPortProgramItem::TimeunitsDeclaration(Box::new(x))
        }),
        map(program_generate_item, |x| {
            NonPortProgramItem::ProgramGenerateItem(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn non_port_program_item_assign(s: Span) -> IResult<Span, NonPortProgramItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = continuous_assign(s)?;
    Ok((
        s,
        NonPortProgramItem::Assign(Box::new(NonPortProgramItemAssign { nodes: (a, b) })),
    ))
}

#[parser(MaybeRecursive)]
pub fn non_port_program_item_module(s: Span) -> IResult<Span, NonPortProgramItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = module_or_generate_item_declaration(s)?;
    Ok((
        s,
        NonPortProgramItem::Module(Box::new(NonPortProgramItemModule { nodes: (a, b) })),
    ))
}

#[parser]
pub fn non_port_program_item_initial(s: Span) -> IResult<Span, NonPortProgramItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = initial_construct(s)?;
    Ok((
        s,
        NonPortProgramItem::Initial(Box::new(NonPortProgramItemInitial { nodes: (a, b) })),
    ))
}

#[parser]
pub fn non_port_program_item_final(s: Span) -> IResult<Span, NonPortProgramItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = final_construct(s)?;
    Ok((
        s,
        NonPortProgramItem::Final(Box::new(NonPortProgramItemFinal { nodes: (a, b) })),
    ))
}

#[parser]
pub fn non_port_program_item_assertion(s: Span) -> IResult<Span, NonPortProgramItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = concurrent_assertion_item(s)?;
    Ok((
        s,
        NonPortProgramItem::Assertion(Box::new(NonPortProgramItemAssertion { nodes: (a, b) })),
    ))
}

#[parser]
pub fn program_generate_item(s: Span) -> IResult<Span, ProgramGenerateItem> {
    alt((
        map(loop_generate_construct, |x| {
            ProgramGenerateItem::LoopGenerateConstruct(Box::new(x))
        }),
        map(conditional_generate_construct, |x| {
            ProgramGenerateItem::ConditionalGenerateConstruct(Box::new(x))
        }),
        map(generate_region, |x| {
            ProgramGenerateItem::GenerateRegion(Box::new(x))
        }),
        map(elaboration_system_task, |x| {
            ProgramGenerateItem::ElaborationSystemTask(Box::new(x))
        }),
    ))(s)
}

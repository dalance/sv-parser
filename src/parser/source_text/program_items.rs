use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum ProgramItem<'a> {
    PortDeclaration((PortDeclaration<'a>, Symbol<'a>)),
    NonPortProgramItem(NonPortProgramItem<'a>),
}

#[derive(Debug, Node)]
pub enum NonPortProgramItem<'a> {
    Assign(NonPortProgramItemAssign<'a>),
    Module(NonPortProgramItemModule<'a>),
    Initial(NonPortProgramItemInitial<'a>),
    Final(NonPortProgramItemFinal<'a>),
    Assertion(NonPortProgramItemAssertion<'a>),
    TimeunitsDeclaration(TimeunitsDeclaration<'a>),
    ProgramGenerateItem(ProgramGenerateItem<'a>),
}

#[derive(Debug, Node)]
pub struct NonPortProgramItemAssign<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ContinuousAssign<'a>),
}

#[derive(Debug, Node)]
pub struct NonPortProgramItemModule<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        ModuleOrGenerateItemDeclaration<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct NonPortProgramItemInitial<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, InitialConstruct<'a>),
}

#[derive(Debug, Node)]
pub struct NonPortProgramItemFinal<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, FinalConstruct<'a>),
}

#[derive(Debug, Node)]
pub struct NonPortProgramItemAssertion<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ConcurrentAssertionItem<'a>),
}

#[derive(Debug, Node)]
pub enum ProgramGenerateItem<'a> {
    LoopGenerateConstruct(LoopGenerateConstruct<'a>),
    ConditionalGenerateConstruct(ConditionalGenerateConstruct<'a>),
    GenerateRegion(GenerateRegion<'a>),
    ElaborationSystemTask(ElaborationSystemTask<'a>),
}

// -----------------------------------------------------------------------------

#[trace]
pub fn program_item(s: Span) -> IResult<Span, ProgramItem> {
    alt((
        map(pair(port_declaration, symbol(";")), |x| {
            ProgramItem::PortDeclaration(x)
        }),
        map(non_port_program_item, |x| {
            ProgramItem::NonPortProgramItem(x)
        }),
    ))(s)
}

#[trace]
pub fn non_port_program_item(s: Span) -> IResult<Span, NonPortProgramItem> {
    alt((
        non_port_program_item_assign,
        non_port_program_item_module,
        non_port_program_item_initial,
        non_port_program_item_final,
        non_port_program_item_assertion,
        map(timeunits_declaration, |x| {
            NonPortProgramItem::TimeunitsDeclaration(x)
        }),
        map(program_generate_item, |x| {
            NonPortProgramItem::ProgramGenerateItem(x)
        }),
    ))(s)
}

#[trace]
pub fn non_port_program_item_assign(s: Span) -> IResult<Span, NonPortProgramItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = continuous_assign(s)?;
    Ok((
        s,
        NonPortProgramItem::Assign(NonPortProgramItemAssign { nodes: (a, b) }),
    ))
}

#[trace]
pub fn non_port_program_item_module(s: Span) -> IResult<Span, NonPortProgramItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = module_or_generate_item_declaration(s)?;
    Ok((
        s,
        NonPortProgramItem::Module(NonPortProgramItemModule { nodes: (a, b) }),
    ))
}

#[trace]
pub fn non_port_program_item_initial(s: Span) -> IResult<Span, NonPortProgramItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = initial_construct(s)?;
    Ok((
        s,
        NonPortProgramItem::Initial(NonPortProgramItemInitial { nodes: (a, b) }),
    ))
}

#[trace]
pub fn non_port_program_item_final(s: Span) -> IResult<Span, NonPortProgramItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = final_construct(s)?;
    Ok((
        s,
        NonPortProgramItem::Final(NonPortProgramItemFinal { nodes: (a, b) }),
    ))
}

#[trace]
pub fn non_port_program_item_assertion(s: Span) -> IResult<Span, NonPortProgramItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = concurrent_assertion_item(s)?;
    Ok((
        s,
        NonPortProgramItem::Assertion(NonPortProgramItemAssertion { nodes: (a, b) }),
    ))
}

#[trace]
pub fn program_generate_item(s: Span) -> IResult<Span, ProgramGenerateItem> {
    alt((
        map(loop_generate_construct, |x| {
            ProgramGenerateItem::LoopGenerateConstruct(x)
        }),
        map(conditional_generate_construct, |x| {
            ProgramGenerateItem::ConditionalGenerateConstruct(x)
        }),
        map(generate_region, |x| ProgramGenerateItem::GenerateRegion(x)),
        map(elaboration_system_task, |x| {
            ProgramGenerateItem::ElaborationSystemTask(x)
        }),
    ))(s)
}

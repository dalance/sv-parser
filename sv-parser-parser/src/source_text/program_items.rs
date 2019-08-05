use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
#[packrat_parser]
pub(crate) fn program_item(s: Span) -> IResult<Span, ProgramItem> {
    alt((
        map(pair(port_declaration, symbol(";")), |x| {
            ProgramItem::PortDeclaration(Box::new(x))
        }),
        map(non_port_program_item, |x| {
            ProgramItem::NonPortProgramItem(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn non_port_program_item(s: Span) -> IResult<Span, NonPortProgramItem> {
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

#[tracable_parser]
#[packrat_parser]
pub(crate) fn non_port_program_item_assign(s: Span) -> IResult<Span, NonPortProgramItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = continuous_assign(s)?;
    Ok((
        s,
        NonPortProgramItem::Assign(Box::new(NonPortProgramItemAssign { nodes: (a, b) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn non_port_program_item_module(s: Span) -> IResult<Span, NonPortProgramItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = module_or_generate_item_declaration(s)?;
    Ok((
        s,
        NonPortProgramItem::Module(Box::new(NonPortProgramItemModule { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn non_port_program_item_initial(s: Span) -> IResult<Span, NonPortProgramItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = initial_construct(s)?;
    Ok((
        s,
        NonPortProgramItem::Initial(Box::new(NonPortProgramItemInitial { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn non_port_program_item_final(s: Span) -> IResult<Span, NonPortProgramItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = final_construct(s)?;
    Ok((
        s,
        NonPortProgramItem::Final(Box::new(NonPortProgramItemFinal { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn non_port_program_item_assertion(s: Span) -> IResult<Span, NonPortProgramItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = concurrent_assertion_item(s)?;
    Ok((
        s,
        NonPortProgramItem::Assertion(Box::new(NonPortProgramItemAssertion { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn program_generate_item(s: Span) -> IResult<Span, ProgramGenerateItem> {
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

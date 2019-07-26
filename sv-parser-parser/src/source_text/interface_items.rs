use crate::*;

// -----------------------------------------------------------------------------

#[parser]
pub(crate) fn interface_or_generate_item(s: Span) -> IResult<Span, InterfaceOrGenerateItem> {
    alt((
        interface_or_generate_item_module,
        interface_or_generate_item_extern,
    ))(s)
}

#[parser(MaybeRecursive)]
pub(crate) fn interface_or_generate_item_module(s: Span) -> IResult<Span, InterfaceOrGenerateItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = module_common_item(s)?;
    Ok((
        s,
        InterfaceOrGenerateItem::Module(Box::new(InterfaceOrGenerateItemModule { nodes: (a, b) })),
    ))
}

#[parser]
pub(crate) fn interface_or_generate_item_extern(s: Span) -> IResult<Span, InterfaceOrGenerateItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = extern_tf_declaration(s)?;
    Ok((
        s,
        InterfaceOrGenerateItem::Extern(Box::new(InterfaceOrGenerateItemExtern { nodes: (a, b) })),
    ))
}

#[parser]
pub(crate) fn extern_tf_declaration(s: Span) -> IResult<Span, ExternTfDeclaration> {
    alt((extern_tf_declaration_method, extern_tf_declaration_task))(s)
}

#[parser]
pub(crate) fn extern_tf_declaration_method(s: Span) -> IResult<Span, ExternTfDeclaration> {
    let (s, a) = keyword("extern")(s)?;
    let (s, b) = method_prototype(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ExternTfDeclaration::Method(Box::new(ExternTfDeclarationMethod { nodes: (a, b, c) })),
    ))
}

#[parser]
pub(crate) fn extern_tf_declaration_task(s: Span) -> IResult<Span, ExternTfDeclaration> {
    let (s, a) = keyword("extern")(s)?;
    let (s, b) = keyword("forkjoin")(s)?;
    let (s, c) = task_prototype(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        ExternTfDeclaration::Task(Box::new(ExternTfDeclarationTask {
            nodes: (a, b, c, d),
        })),
    ))
}

#[parser]
pub(crate) fn interface_item(s: Span) -> IResult<Span, InterfaceItem> {
    alt((
        map(pair(port_declaration, symbol(";")), |x| {
            InterfaceItem::PortDeclaration(Box::new(x))
        }),
        map(non_port_interface_item, |x| {
            InterfaceItem::NonPortInterfaceItem(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub(crate) fn non_port_interface_item(s: Span) -> IResult<Span, NonPortInterfaceItem> {
    alt((
        map(generate_region, |x| {
            NonPortInterfaceItem::GenerateRegion(Box::new(x))
        }),
        map(interface_or_generate_item, |x| {
            NonPortInterfaceItem::InterfaceOrGenerateItem(Box::new(x))
        }),
        map(program_declaration, |x| {
            NonPortInterfaceItem::ProgramDeclaration(Box::new(x))
        }),
        map(modport_declaration, |x| {
            NonPortInterfaceItem::ModportDeclaration(Box::new(x))
        }),
        map(interface_declaration, |x| {
            NonPortInterfaceItem::InterfaceDeclaration(Box::new(x))
        }),
        map(timeunits_declaration, |x| {
            NonPortInterfaceItem::TimeunitsDeclaration(Box::new(x))
        }),
    ))(s)
}

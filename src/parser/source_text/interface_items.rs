use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum InterfaceOrGenerateItem {
    Module(InterfaceOrGenerateItemModule),
    Extern(InterfaceOrGenerateItemExtern),
}

#[derive(Clone, Debug, Node)]
pub struct InterfaceOrGenerateItemModule {
    pub nodes: (Vec<AttributeInstance>, ModuleCommonItem),
}

#[derive(Clone, Debug, Node)]
pub struct InterfaceOrGenerateItemExtern {
    pub nodes: (Vec<AttributeInstance>, ExternTfDeclaration),
}

#[derive(Clone, Debug, Node)]
pub enum ExternTfDeclaration {
    Method(ExternTfDeclarationMethod),
    Task(ExternTfDeclarationTask),
}

#[derive(Clone, Debug, Node)]
pub struct ExternTfDeclarationMethod {
    pub nodes: (Keyword, MethodPrototype, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct ExternTfDeclarationTask {
    pub nodes: (Keyword, Keyword, TaskPrototype, Symbol),
}

#[derive(Clone, Debug, Node)]
pub enum InterfaceItem {
    PortDeclaration((PortDeclaration, Symbol)),
    NonPortInterfaceItem(NonPortInterfaceItem),
}

#[derive(Clone, Debug, Node)]
pub enum NonPortInterfaceItem {
    GenerateRegion(GenerateRegion),
    InterfaceOrGenerateItem(InterfaceOrGenerateItem),
    ProgramDeclaration(ProgramDeclaration),
    ModportDeclaration(ModportDeclaration),
    InterfaceDeclaration(InterfaceDeclaration),
    TimeunitsDeclaration(TimeunitsDeclaration),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn interface_or_generate_item(s: Span) -> IResult<Span, InterfaceOrGenerateItem> {
    alt((
        interface_or_generate_item_module,
        interface_or_generate_item_extern,
    ))(s)
}

#[parser(MaybeRecursive)]
pub fn interface_or_generate_item_module(s: Span) -> IResult<Span, InterfaceOrGenerateItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = module_common_item(s)?;
    Ok((
        s,
        InterfaceOrGenerateItem::Module(InterfaceOrGenerateItemModule { nodes: (a, b) }),
    ))
}

#[parser]
pub fn interface_or_generate_item_extern(s: Span) -> IResult<Span, InterfaceOrGenerateItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = extern_tf_declaration(s)?;
    Ok((
        s,
        InterfaceOrGenerateItem::Extern(InterfaceOrGenerateItemExtern { nodes: (a, b) }),
    ))
}

#[parser]
pub fn extern_tf_declaration(s: Span) -> IResult<Span, ExternTfDeclaration> {
    alt((extern_tf_declaration_method, extern_tf_declaration_task))(s)
}

#[parser]
pub fn extern_tf_declaration_method(s: Span) -> IResult<Span, ExternTfDeclaration> {
    let (s, a) = keyword("extern")(s)?;
    let (s, b) = method_prototype(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ExternTfDeclaration::Method(ExternTfDeclarationMethod { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn extern_tf_declaration_task(s: Span) -> IResult<Span, ExternTfDeclaration> {
    let (s, a) = keyword("extern")(s)?;
    let (s, b) = keyword("forkjoin")(s)?;
    let (s, c) = task_prototype(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        ExternTfDeclaration::Task(ExternTfDeclarationTask {
            nodes: (a, b, c, d),
        }),
    ))
}

#[parser]
pub fn interface_item(s: Span) -> IResult<Span, InterfaceItem> {
    alt((
        map(pair(port_declaration, symbol(";")), |x| {
            InterfaceItem::PortDeclaration(x)
        }),
        map(non_port_interface_item, |x| {
            InterfaceItem::NonPortInterfaceItem(x)
        }),
    ))(s)
}

#[parser]
pub fn non_port_interface_item(s: Span) -> IResult<Span, NonPortInterfaceItem> {
    alt((
        map(generate_region, |x| NonPortInterfaceItem::GenerateRegion(x)),
        map(interface_or_generate_item, |x| {
            NonPortInterfaceItem::InterfaceOrGenerateItem(x)
        }),
        map(program_declaration, |x| {
            NonPortInterfaceItem::ProgramDeclaration(x)
        }),
        map(modport_declaration, |x| {
            NonPortInterfaceItem::ModportDeclaration(x)
        }),
        map(interface_declaration, |x| {
            NonPortInterfaceItem::InterfaceDeclaration(x)
        }),
        map(timeunits_declaration, |x| {
            NonPortInterfaceItem::TimeunitsDeclaration(x)
        }),
    ))(s)
}

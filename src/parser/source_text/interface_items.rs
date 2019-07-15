use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum InterfaceOrGenerateItem<'a> {
    Module(InterfaceOrGenerateItemModule<'a>),
    Extern(InterfaceOrGenerateItemExtern<'a>),
}

#[derive(Debug, Node)]
pub struct InterfaceOrGenerateItemModule<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ModuleCommonItem<'a>),
}

#[derive(Debug, Node)]
pub struct InterfaceOrGenerateItemExtern<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ExternTfDeclaration<'a>),
}

#[derive(Debug, Node)]
pub enum ExternTfDeclaration<'a> {
    Method(ExternTfDeclarationMethod<'a>),
    Task(ExternTfDeclarationTask<'a>),
}

#[derive(Debug, Node)]
pub struct ExternTfDeclarationMethod<'a> {
    pub nodes: (Symbol<'a>, MethodPrototype<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct ExternTfDeclarationTask<'a> {
    pub nodes: (Symbol<'a>, Symbol<'a>, TaskPrototype<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum InterfaceItem<'a> {
    PortDeclaration((PortDeclaration<'a>, Symbol<'a>)),
    NonPortInterfaceItem(NonPortInterfaceItem<'a>),
}

#[derive(Debug, Node)]
pub enum NonPortInterfaceItem<'a> {
    GenerateRegion(GenerateRegion<'a>),
    InterfaceOrGenerateItem(InterfaceOrGenerateItem<'a>),
    ProgramDeclaration(ProgramDeclaration<'a>),
    ModportDeclaration(ModportDeclaration<'a>),
    InterfaceDeclaration(InterfaceDeclaration<'a>),
    TimeunitsDeclaration(TimeunitsDeclaration<'a>),
}

// -----------------------------------------------------------------------------

pub fn interface_or_generate_item(s: Span) -> IResult<Span, InterfaceOrGenerateItem> {
    alt((
        interface_or_generate_item_module,
        interface_or_generate_item_extern,
    ))(s)
}

pub fn interface_or_generate_item_module(s: Span) -> IResult<Span, InterfaceOrGenerateItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = module_common_item(s)?;
    Ok((
        s,
        InterfaceOrGenerateItem::Module(InterfaceOrGenerateItemModule { nodes: (a, b) }),
    ))
}

pub fn interface_or_generate_item_extern(s: Span) -> IResult<Span, InterfaceOrGenerateItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = extern_tf_declaration(s)?;
    Ok((
        s,
        InterfaceOrGenerateItem::Extern(InterfaceOrGenerateItemExtern { nodes: (a, b) }),
    ))
}

pub fn extern_tf_declaration(s: Span) -> IResult<Span, ExternTfDeclaration> {
    alt((extern_tf_declaration_method, extern_tf_declaration_task))(s)
}

pub fn extern_tf_declaration_method(s: Span) -> IResult<Span, ExternTfDeclaration> {
    let (s, a) = symbol("extern")(s)?;
    let (s, b) = method_prototype(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ExternTfDeclaration::Method(ExternTfDeclarationMethod { nodes: (a, b, c) }),
    ))
}

pub fn extern_tf_declaration_task(s: Span) -> IResult<Span, ExternTfDeclaration> {
    let (s, a) = symbol("extern")(s)?;
    let (s, b) = symbol("forkjoin")(s)?;
    let (s, c) = task_prototype(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        ExternTfDeclaration::Task(ExternTfDeclarationTask {
            nodes: (a, b, c, d),
        }),
    ))
}

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

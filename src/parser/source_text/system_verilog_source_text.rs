use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct SourceText<'a> {
    pub nodes: (Option<TimeunitsDeclaration<'a>>, Vec<Description<'a>>),
}

#[derive(Debug, Node)]
pub enum Description<'a> {
    ModuleDeclaration(ModuleDeclaration<'a>),
    UdpDeclaration(UdpDeclaration<'a>),
    InterfaceDeclaration(InterfaceDeclaration<'a>),
    ProgramDeclaration(ProgramDeclaration<'a>),
    PackageDeclaration(PackageDeclaration<'a>),
    PackageItem(DescriptionPackageItem<'a>),
    BindDirective(DescriptionBindDirective<'a>),
    ConfigDeclaration(ConfigDeclaration<'a>),
}

#[derive(Debug, Node)]
pub struct DescriptionPackageItem<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, PackageItem<'a>),
}

#[derive(Debug, Node)]
pub struct DescriptionBindDirective<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, BindDirective<'a>),
}

#[derive(Debug, Node)]
pub struct ModuleNonansiHeader<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        ModuleKeyword<'a>,
        Option<Lifetime<'a>>,
        ModuleIdentifier<'a>,
        Vec<PackageImportDeclaration<'a>>,
        Option<ParameterPortList<'a>>,
        ListOfPorts<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct ModuleAnsiHeader<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        ModuleKeyword<'a>,
        Option<Lifetime<'a>>,
        ModuleIdentifier<'a>,
        Vec<PackageImportDeclaration<'a>>,
        Option<ParameterPortList<'a>>,
        Option<ListOfPortDeclarations<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum ModuleDeclaration<'a> {
    Nonansi(ModuleDeclarationNonansi<'a>),
    Ansi(ModuleDeclarationAnsi<'a>),
    Wildcard(ModuleDeclarationWildcard<'a>),
    ExternNonansi(ModuleDeclarationExternNonansi<'a>),
    ExternAnsi(ModuleDeclarationExternAnsi<'a>),
}

#[derive(Debug, Node)]
pub struct ModuleDeclarationNonansi<'a> {
    pub nodes: (
        ModuleNonansiHeader<'a>,
        Option<TimeunitsDeclaration<'a>>,
        Vec<ModuleItem<'a>>,
        Symbol<'a>,
        Option<(Symbol<'a>, ModuleIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct ModuleDeclarationAnsi<'a> {
    pub nodes: (
        ModuleAnsiHeader<'a>,
        Option<TimeunitsDeclaration<'a>>,
        Vec<NonPortModuleItem<'a>>,
        Symbol<'a>,
        Option<(Symbol<'a>, ModuleIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct ModuleDeclarationWildcard<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        ModuleKeyword<'a>,
        Option<Lifetime<'a>>,
        ModuleIdentifier<'a>,
        Paren<'a, Symbol<'a>>,
        Symbol<'a>,
        Option<TimeunitsDeclaration<'a>>,
        Vec<ModuleItem<'a>>,
        Symbol<'a>,
        Option<(Symbol<'a>, ModuleIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct ModuleDeclarationExternNonansi<'a> {
    pub nodes: (Symbol<'a>, ModuleNonansiHeader<'a>),
}

#[derive(Debug, Node)]
pub struct ModuleDeclarationExternAnsi<'a> {
    pub nodes: (Symbol<'a>, ModuleAnsiHeader<'a>),
}

#[derive(Debug, Node)]
pub enum ModuleKeyword<'a> {
    Module(Symbol<'a>),
    Macromodule(Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum InterfaceDeclaration<'a> {
    Nonansi(InterfaceDeclarationNonansi<'a>),
    Ansi(InterfaceDeclarationAnsi<'a>),
    Wildcard(InterfaceDeclarationWildcard<'a>),
    ExternNonansi(InterfaceDeclarationExternNonansi<'a>),
    ExternAnsi(InterfaceDeclarationExternAnsi<'a>),
}

#[derive(Debug, Node)]
pub struct InterfaceDeclarationNonansi<'a> {
    pub nodes: (
        InterfaceNonansiHeader<'a>,
        Option<TimeunitsDeclaration<'a>>,
        Vec<InterfaceItem<'a>>,
        Symbol<'a>,
        Option<(Symbol<'a>, InterfaceIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct InterfaceDeclarationAnsi<'a> {
    pub nodes: (
        InterfaceAnsiHeader<'a>,
        Option<TimeunitsDeclaration<'a>>,
        Vec<NonPortInterfaceItem<'a>>,
        Symbol<'a>,
        Option<(Symbol<'a>, InterfaceIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct InterfaceDeclarationWildcard<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Symbol<'a>,
        Option<Lifetime<'a>>,
        InterfaceIdentifier<'a>,
        Paren<'a, Symbol<'a>>,
        Symbol<'a>,
        Option<TimeunitsDeclaration<'a>>,
        Vec<InterfaceItem<'a>>,
        Symbol<'a>,
        Option<(Symbol<'a>, InterfaceIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct InterfaceDeclarationExternNonansi<'a> {
    pub nodes: (Symbol<'a>, InterfaceNonansiHeader<'a>),
}

#[derive(Debug, Node)]
pub struct InterfaceDeclarationExternAnsi<'a> {
    pub nodes: (Symbol<'a>, InterfaceAnsiHeader<'a>),
}

#[derive(Debug, Node)]
pub struct InterfaceNonansiHeader<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Symbol<'a>,
        Option<Lifetime<'a>>,
        InterfaceIdentifier<'a>,
        Vec<PackageImportDeclaration<'a>>,
        Option<ParameterPortList<'a>>,
        ListOfPorts<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct InterfaceAnsiHeader<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Symbol<'a>,
        Option<Lifetime<'a>>,
        InterfaceIdentifier<'a>,
        Vec<PackageImportDeclaration<'a>>,
        Option<ParameterPortList<'a>>,
        Option<ListOfPortDeclarations<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum ProgramDeclaration<'a> {
    Nonansi(ProgramDeclarationNonansi<'a>),
    Ansi(ProgramDeclarationAnsi<'a>),
    Wildcard(ProgramDeclarationWildcard<'a>),
    ExternNonansi(ProgramDeclarationExternNonansi<'a>),
    ExternAnsi(ProgramDeclarationExternAnsi<'a>),
}

#[derive(Debug, Node)]
pub struct ProgramDeclarationNonansi<'a> {
    pub nodes: (
        ProgramNonansiHeader<'a>,
        Option<TimeunitsDeclaration<'a>>,
        Vec<ProgramItem<'a>>,
        Symbol<'a>,
        Option<(Symbol<'a>, ProgramIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct ProgramDeclarationAnsi<'a> {
    pub nodes: (
        ProgramAnsiHeader<'a>,
        Option<TimeunitsDeclaration<'a>>,
        Vec<NonPortProgramItem<'a>>,
        Symbol<'a>,
        Option<(Symbol<'a>, ProgramIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct ProgramDeclarationWildcard<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Symbol<'a>,
        ProgramIdentifier<'a>,
        Paren<'a, Symbol<'a>>,
        Symbol<'a>,
        Option<TimeunitsDeclaration<'a>>,
        Vec<ProgramItem<'a>>,
        Symbol<'a>,
        Option<(Symbol<'a>, ProgramIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct ProgramDeclarationExternNonansi<'a> {
    pub nodes: (Symbol<'a>, ProgramNonansiHeader<'a>),
}

#[derive(Debug, Node)]
pub struct ProgramDeclarationExternAnsi<'a> {
    pub nodes: (Symbol<'a>, ProgramAnsiHeader<'a>),
}

#[derive(Debug, Node)]
pub struct ProgramNonansiHeader<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Symbol<'a>,
        Option<Lifetime<'a>>,
        ProgramIdentifier<'a>,
        Vec<PackageImportDeclaration<'a>>,
        Option<ParameterPortList<'a>>,
        ListOfPorts<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct ProgramAnsiHeader<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Symbol<'a>,
        Option<Lifetime<'a>>,
        ProgramIdentifier<'a>,
        Vec<PackageImportDeclaration<'a>>,
        Option<ParameterPortList<'a>>,
        Option<ListOfPortDeclarations<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct CheckerDeclaration<'a> {
    pub nodes: (
        Symbol<'a>,
        CheckerIdentifier<'a>,
        Option<Paren<'a, Option<CheckerPortList<'a>>>>,
        Symbol<'a>,
        Vec<(Vec<AttributeInstance<'a>>, CheckerOrGenerateItem<'a>)>,
        Symbol<'a>,
        Option<(Symbol<'a>, CheckerIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct ClassDeclaration<'a> {
    pub nodes: (
        Option<Virtual<'a>>,
        Symbol<'a>,
        Option<Lifetime<'a>>,
        ClassIdentifier<'a>,
        Option<ParameterPortList<'a>>,
        Option<(
            Symbol<'a>,
            ClassType<'a>,
            Option<Paren<'a, ListOfArguments<'a>>>,
        )>,
        Option<(Symbol<'a>, List<Symbol<'a>, InterfaceClassType<'a>>)>,
        Symbol<'a>,
        Vec<ClassItem<'a>>,
        Symbol<'a>,
        Option<(Symbol<'a>, ClassIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct Virtual<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug, Node)]
pub struct InterfaceClassType<'a> {
    pub nodes: (PsClassIdentifier<'a>, Option<ParameterValueAssignment<'a>>),
}

#[derive(Debug, Node)]
pub struct InterfaceClassDeclaration<'a> {
    pub nodes: (
        Symbol<'a>,
        Symbol<'a>,
        ClassIdentifier<'a>,
        Option<ParameterPortList<'a>>,
        Option<(Symbol<'a>, List<Symbol<'a>, InterfaceClassType<'a>>)>,
        Symbol<'a>,
        Vec<InterfaceClassItem<'a>>,
        Symbol<'a>,
        Option<(Symbol<'a>, ClassIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub enum InterfaceClassItem<'a> {
    TypeDeclaration(TypeDeclaration<'a>),
    Method(InterfaceClassItemMethod<'a>),
    LocalParameterDeclaration((LocalParameterDeclaration<'a>, Symbol<'a>)),
    ParameterDeclaration((ParameterDeclaration<'a>, Symbol<'a>)),
    Null(Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct InterfaceClassItemMethod<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, InterfaceClassMethod<'a>),
}

#[derive(Debug, Node)]
pub struct InterfaceClassMethod<'a> {
    pub nodes: (Symbol<'a>, Symbol<'a>, MethodPrototype<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct PackageDeclaration<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Symbol<'a>,
        Option<Lifetime<'a>>,
        PackageIdentifier<'a>,
        Symbol<'a>,
        Option<TimeunitsDeclaration<'a>>,
        Vec<(Vec<AttributeInstance<'a>>, PackageItem<'a>)>,
        Symbol<'a>,
        Option<(Symbol<'a>, PackageIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub enum TimeunitsDeclaration<'a> {
    Timeunit(TimeunitsDeclarationTimeunit<'a>),
    Timeprecision(TimeunitsDeclarationTimeprecision<'a>),
    TimeunitTimeprecision(TimeunitsDeclarationTimeunitTimeprecision<'a>),
    TimeprecisionTimeunit(TimeunitsDeclarationTimeprecisionTimeunit<'a>),
}

#[derive(Debug, Node)]
pub struct TimeunitsDeclarationTimeunit<'a> {
    pub nodes: (
        Symbol<'a>,
        TimeLiteral<'a>,
        Option<(Symbol<'a>, TimeLiteral<'a>)>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct TimeunitsDeclarationTimeprecision<'a> {
    pub nodes: (Symbol<'a>, TimeLiteral<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct TimeunitsDeclarationTimeunitTimeprecision<'a> {
    pub nodes: (
        Symbol<'a>,
        TimeLiteral<'a>,
        Symbol<'a>,
        Symbol<'a>,
        TimeLiteral<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct TimeunitsDeclarationTimeprecisionTimeunit<'a> {
    pub nodes: (
        Symbol<'a>,
        TimeLiteral<'a>,
        Symbol<'a>,
        Symbol<'a>,
        TimeLiteral<'a>,
        Symbol<'a>,
    ),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn source_text(s: Span) -> IResult<Span, SourceText> {
    let (s, a) = opt(timeunits_declaration)(s)?;
    let (s, b) = many0(description)(s)?;
    Ok((s, SourceText { nodes: (a, b) }))
}

#[parser]
pub fn description(s: Span) -> IResult<Span, Description> {
    alt((
        map(module_declaration, |x| Description::ModuleDeclaration(x)),
        map(udp_declaration, |x| Description::UdpDeclaration(x)),
        map(interface_declaration, |x| {
            Description::InterfaceDeclaration(x)
        }),
        map(program_declaration, |x| Description::ProgramDeclaration(x)),
        map(package_declaration, |x| Description::PackageDeclaration(x)),
        description_package_item,
        description_bind_directive,
        map(config_declaration, |x| Description::ConfigDeclaration(x)),
    ))(s)
}

#[parser]
pub fn description_package_item(s: Span) -> IResult<Span, Description> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = package_item(s)?;
    Ok((
        s,
        Description::PackageItem(DescriptionPackageItem { nodes: (a, b) }),
    ))
}

#[parser]
pub fn description_bind_directive(s: Span) -> IResult<Span, Description> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = bind_directive(s)?;
    Ok((
        s,
        Description::BindDirective(DescriptionBindDirective { nodes: (a, b) }),
    ))
}

#[parser]
pub fn module_nonansi_header(s: Span) -> IResult<Span, ModuleNonansiHeader> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = module_keyword(s)?;
    let (s, c) = opt(lifetime)(s)?;
    let (s, d) = module_identifier(s)?;
    let (s, e) = many0(package_import_declaration)(s)?;
    let (s, f) = opt(parameter_port_list)(s)?;
    let (s, g) = list_of_ports(s)?;
    let (s, h) = symbol(";")(s)?;
    Ok((
        s,
        ModuleNonansiHeader {
            nodes: (a, b, c, d, e, f, g, h),
        },
    ))
}

#[parser]
pub fn module_ansi_header(s: Span) -> IResult<Span, ModuleAnsiHeader> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = module_keyword(s)?;
    let (s, c) = opt(lifetime)(s)?;
    let (s, d) = module_identifier(s)?;
    let (s, e) = many0(package_import_declaration)(s)?;
    let (s, f) = opt(parameter_port_list)(s)?;
    let (s, g) = opt(list_of_port_declarations)(s)?;
    let (s, h) = symbol(";")(s)?;
    Ok((
        s,
        ModuleAnsiHeader {
            nodes: (a, b, c, d, e, f, g, h),
        },
    ))
}

#[parser]
pub fn module_declaration(s: Span) -> IResult<Span, ModuleDeclaration> {
    alt((
        module_declaration_nonansi,
        module_declaration_ansi,
        module_declaration_wildcard,
        module_declaration_extern_nonansi,
        module_declaration_extern_ansi,
    ))(s)
}

#[parser]
pub fn module_declaration_nonansi(s: Span) -> IResult<Span, ModuleDeclaration> {
    let (s, a) = module_nonansi_header(s)?;
    let (s, b) = opt(timeunits_declaration)(s)?;
    let (s, c) = many0(module_item)(s)?;
    let (s, d) = symbol("endmodule")(s)?;
    let (s, e) = opt(pair(symbol(":"), module_identifier))(s)?;
    Ok((
        s,
        ModuleDeclaration::Nonansi(ModuleDeclarationNonansi {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[parser]
pub fn module_declaration_ansi(s: Span) -> IResult<Span, ModuleDeclaration> {
    let (s, a) = module_ansi_header(s)?;
    let (s, b) = opt(timeunits_declaration)(s)?;
    let (s, c) = many0(non_port_module_item)(s)?;
    let (s, d) = symbol("endmodule")(s)?;
    let (s, e) = opt(pair(symbol(":"), module_identifier))(s)?;
    Ok((
        s,
        ModuleDeclaration::Ansi(ModuleDeclarationAnsi {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[parser]
pub fn module_declaration_wildcard(s: Span) -> IResult<Span, ModuleDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = module_keyword(s)?;
    let (s, c) = opt(lifetime)(s)?;
    let (s, d) = module_identifier(s)?;
    let (s, e) = paren(symbol(".*"))(s)?;
    let (s, f) = symbol(";")(s)?;
    let (s, g) = opt(timeunits_declaration)(s)?;
    let (s, h) = many0(module_item)(s)?;
    let (s, i) = symbol("endmodule")(s)?;
    let (s, j) = opt(pair(symbol(":"), module_identifier))(s)?;
    Ok((
        s,
        ModuleDeclaration::Wildcard(ModuleDeclarationWildcard {
            nodes: (a, b, c, d, e, f, g, h, i, j),
        }),
    ))
}

#[parser]
pub fn module_declaration_extern_nonansi(s: Span) -> IResult<Span, ModuleDeclaration> {
    let (s, a) = symbol("extern")(s)?;
    let (s, b) = module_nonansi_header(s)?;
    Ok((
        s,
        ModuleDeclaration::ExternNonansi(ModuleDeclarationExternNonansi { nodes: (a, b) }),
    ))
}

#[parser]
pub fn module_declaration_extern_ansi(s: Span) -> IResult<Span, ModuleDeclaration> {
    let (s, a) = symbol("extern")(s)?;
    let (s, b) = module_ansi_header(s)?;
    Ok((
        s,
        ModuleDeclaration::ExternAnsi(ModuleDeclarationExternAnsi { nodes: (a, b) }),
    ))
}

#[parser]
pub fn module_keyword(s: Span) -> IResult<Span, ModuleKeyword> {
    alt((
        map(symbol("module"), |x| ModuleKeyword::Module(x)),
        map(symbol("macromodule"), |x| ModuleKeyword::Macromodule(x)),
    ))(s)
}

#[parser]
pub fn interface_declaration(s: Span) -> IResult<Span, InterfaceDeclaration> {
    alt((
        interface_declaration_nonansi,
        interface_declaration_ansi,
        interface_declaration_wildcard,
        interface_declaration_extern_nonansi,
        interface_declaration_extern_ansi,
    ))(s)
}

#[parser]
pub fn interface_declaration_nonansi(s: Span) -> IResult<Span, InterfaceDeclaration> {
    let (s, a) = interface_nonansi_header(s)?;
    let (s, b) = opt(timeunits_declaration)(s)?;
    let (s, c) = many0(interface_item)(s)?;
    let (s, d) = symbol("endinterface")(s)?;
    let (s, e) = opt(pair(symbol(":"), interface_identifier))(s)?;
    Ok((
        s,
        InterfaceDeclaration::Nonansi(InterfaceDeclarationNonansi {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[parser]
pub fn interface_declaration_ansi(s: Span) -> IResult<Span, InterfaceDeclaration> {
    let (s, a) = interface_ansi_header(s)?;
    let (s, b) = opt(timeunits_declaration)(s)?;
    let (s, c) = many0(non_port_interface_item)(s)?;
    let (s, d) = symbol("endinterface")(s)?;
    let (s, e) = opt(pair(symbol(":"), interface_identifier))(s)?;
    Ok((
        s,
        InterfaceDeclaration::Ansi(InterfaceDeclarationAnsi {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[parser]
pub fn interface_declaration_wildcard(s: Span) -> IResult<Span, InterfaceDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = symbol("interface")(s)?;
    let (s, c) = opt(lifetime)(s)?;
    let (s, d) = interface_identifier(s)?;
    let (s, e) = paren(symbol(".*"))(s)?;
    let (s, f) = symbol(";")(s)?;
    let (s, g) = opt(timeunits_declaration)(s)?;
    let (s, h) = many0(interface_item)(s)?;
    let (s, i) = symbol("endinterface")(s)?;
    let (s, j) = opt(pair(symbol(":"), interface_identifier))(s)?;
    Ok((
        s,
        InterfaceDeclaration::Wildcard(InterfaceDeclarationWildcard {
            nodes: (a, b, c, d, e, f, g, h, i, j),
        }),
    ))
}

#[parser]
pub fn interface_declaration_extern_nonansi(s: Span) -> IResult<Span, InterfaceDeclaration> {
    let (s, a) = symbol("extern")(s)?;
    let (s, b) = interface_nonansi_header(s)?;
    Ok((
        s,
        InterfaceDeclaration::ExternNonansi(InterfaceDeclarationExternNonansi { nodes: (a, b) }),
    ))
}

#[parser]
pub fn interface_declaration_extern_ansi(s: Span) -> IResult<Span, InterfaceDeclaration> {
    let (s, a) = symbol("extern")(s)?;
    let (s, b) = interface_ansi_header(s)?;
    Ok((
        s,
        InterfaceDeclaration::ExternAnsi(InterfaceDeclarationExternAnsi { nodes: (a, b) }),
    ))
}

#[parser]
pub fn interface_nonansi_header(s: Span) -> IResult<Span, InterfaceNonansiHeader> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = symbol("interface")(s)?;
    let (s, c) = opt(lifetime)(s)?;
    let (s, d) = interface_identifier(s)?;
    let (s, e) = many0(package_import_declaration)(s)?;
    let (s, f) = opt(parameter_port_list)(s)?;
    let (s, g) = list_of_ports(s)?;
    let (s, h) = symbol(";")(s)?;
    Ok((
        s,
        InterfaceNonansiHeader {
            nodes: (a, b, c, d, e, f, g, h),
        },
    ))
}

#[parser]
pub fn interface_ansi_header(s: Span) -> IResult<Span, InterfaceAnsiHeader> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = symbol("interface")(s)?;
    let (s, c) = opt(lifetime)(s)?;
    let (s, d) = interface_identifier(s)?;
    let (s, e) = many0(package_import_declaration)(s)?;
    let (s, f) = opt(parameter_port_list)(s)?;
    let (s, g) = opt(list_of_port_declarations)(s)?;
    let (s, h) = symbol(";")(s)?;
    Ok((
        s,
        InterfaceAnsiHeader {
            nodes: (a, b, c, d, e, f, g, h),
        },
    ))
}

#[parser]
pub fn program_declaration(s: Span) -> IResult<Span, ProgramDeclaration> {
    alt((
        program_declaration_nonansi,
        program_declaration_ansi,
        program_declaration_wildcard,
        program_declaration_extern_nonansi,
        program_declaration_extern_ansi,
    ))(s)
}

#[parser]
pub fn program_declaration_nonansi(s: Span) -> IResult<Span, ProgramDeclaration> {
    let (s, a) = program_nonansi_header(s)?;
    let (s, b) = opt(timeunits_declaration)(s)?;
    let (s, c) = many0(program_item)(s)?;
    let (s, d) = symbol("endprogram")(s)?;
    let (s, e) = opt(pair(symbol(":"), program_identifier))(s)?;
    Ok((
        s,
        ProgramDeclaration::Nonansi(ProgramDeclarationNonansi {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[parser]
pub fn program_declaration_ansi(s: Span) -> IResult<Span, ProgramDeclaration> {
    let (s, a) = program_ansi_header(s)?;
    let (s, b) = opt(timeunits_declaration)(s)?;
    let (s, c) = many0(non_port_program_item)(s)?;
    let (s, d) = symbol("endprogram")(s)?;
    let (s, e) = opt(pair(symbol(":"), program_identifier))(s)?;
    Ok((
        s,
        ProgramDeclaration::Ansi(ProgramDeclarationAnsi {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[parser]
pub fn program_declaration_wildcard(s: Span) -> IResult<Span, ProgramDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = symbol("program")(s)?;
    let (s, c) = program_identifier(s)?;
    let (s, d) = paren(symbol(".*"))(s)?;
    let (s, e) = symbol(";")(s)?;
    let (s, f) = opt(timeunits_declaration)(s)?;
    let (s, g) = many0(program_item)(s)?;
    let (s, h) = symbol("endprogram")(s)?;
    let (s, i) = opt(pair(symbol(":"), program_identifier))(s)?;
    Ok((
        s,
        ProgramDeclaration::Wildcard(ProgramDeclarationWildcard {
            nodes: (a, b, c, d, e, f, g, h, i),
        }),
    ))
}

#[parser]
pub fn program_declaration_extern_nonansi(s: Span) -> IResult<Span, ProgramDeclaration> {
    let (s, a) = symbol("extern")(s)?;
    let (s, b) = program_nonansi_header(s)?;
    Ok((
        s,
        ProgramDeclaration::ExternNonansi(ProgramDeclarationExternNonansi { nodes: (a, b) }),
    ))
}

#[parser]
pub fn program_declaration_extern_ansi(s: Span) -> IResult<Span, ProgramDeclaration> {
    let (s, a) = symbol("extern")(s)?;
    let (s, b) = program_ansi_header(s)?;
    Ok((
        s,
        ProgramDeclaration::ExternAnsi(ProgramDeclarationExternAnsi { nodes: (a, b) }),
    ))
}

#[parser]
pub fn program_nonansi_header(s: Span) -> IResult<Span, ProgramNonansiHeader> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = symbol("prgogram")(s)?;
    let (s, c) = opt(lifetime)(s)?;
    let (s, d) = program_identifier(s)?;
    let (s, e) = many0(package_import_declaration)(s)?;
    let (s, f) = opt(parameter_port_list)(s)?;
    let (s, g) = list_of_ports(s)?;
    let (s, h) = symbol(";")(s)?;
    Ok((
        s,
        ProgramNonansiHeader {
            nodes: (a, b, c, d, e, f, g, h),
        },
    ))
}

#[parser]
pub fn program_ansi_header(s: Span) -> IResult<Span, ProgramAnsiHeader> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = symbol("program")(s)?;
    let (s, c) = opt(lifetime)(s)?;
    let (s, d) = program_identifier(s)?;
    let (s, e) = many0(package_import_declaration)(s)?;
    let (s, f) = opt(parameter_port_list)(s)?;
    let (s, g) = opt(list_of_port_declarations)(s)?;
    let (s, h) = symbol(";")(s)?;
    Ok((
        s,
        ProgramAnsiHeader {
            nodes: (a, b, c, d, e, f, g, h),
        },
    ))
}

#[parser]
pub fn checker_declaration(s: Span) -> IResult<Span, CheckerDeclaration> {
    let (s, a) = symbol("checker")(s)?;
    let (s, b) = checker_identifier(s)?;
    let (s, c) = opt(paren(opt(checker_port_list)))(s)?;
    let (s, d) = symbol(";")(s)?;
    let (s, e) = many0(pair(many0(attribute_instance), checker_or_generate_item))(s)?;
    let (s, f) = symbol("endchecker")(s)?;
    let (s, g) = opt(pair(symbol(":"), checker_identifier))(s)?;
    Ok((
        s,
        CheckerDeclaration {
            nodes: (a, b, c, d, e, f, g),
        },
    ))
}

#[parser]
pub fn class_declaration(s: Span) -> IResult<Span, ClassDeclaration> {
    let (s, a) = opt(map(symbol("virtual"), |x| Virtual { nodes: (x,) }))(s)?;
    let (s, b) = symbol("class")(s)?;
    let (s, c) = opt(lifetime)(s)?;
    let (s, d) = class_identifier(s)?;
    let (s, e) = opt(parameter_port_list)(s)?;
    let (s, f) = opt(triple(
        symbol("extends"),
        class_type,
        opt(paren(list_of_arguments)),
    ))(s)?;
    let (s, g) = opt(pair(
        symbol("implements"),
        list(symbol(","), interface_class_type),
    ))(s)?;
    let (s, h) = symbol(";")(s)?;
    let (s, i) = many0(class_item)(s)?;
    let (s, j) = symbol("endclass")(s)?;
    let (s, k) = opt(pair(symbol(":"), class_identifier))(s)?;
    Ok((
        s,
        ClassDeclaration {
            nodes: (a, b, c, d, e, f, g, h, i, j, k),
        },
    ))
}

#[parser]
pub fn interface_class_type(s: Span) -> IResult<Span, InterfaceClassType> {
    let (s, a) = ps_class_identifier(s)?;
    let (s, b) = opt(parameter_value_assignment)(s)?;
    Ok((s, InterfaceClassType { nodes: (a, b) }))
}

#[parser]
pub fn interface_class_declaration(s: Span) -> IResult<Span, InterfaceClassDeclaration> {
    let (s, a) = symbol("interface")(s)?;
    let (s, b) = symbol("class")(s)?;
    let (s, c) = class_identifier(s)?;
    let (s, d) = opt(parameter_port_list)(s)?;
    let (s, e) = opt(pair(
        symbol("extends"),
        list(symbol(","), interface_class_type),
    ))(s)?;
    let (s, f) = symbol(";")(s)?;
    let (s, g) = many0(interface_class_item)(s)?;
    let (s, h) = symbol("endclass")(s)?;
    let (s, i) = opt(pair(symbol(":"), class_identifier))(s)?;
    Ok((
        s,
        InterfaceClassDeclaration {
            nodes: (a, b, c, d, e, f, g, h, i),
        },
    ))
}

#[parser]
pub fn interface_class_item(s: Span) -> IResult<Span, InterfaceClassItem> {
    alt((
        map(type_declaration, |x| InterfaceClassItem::TypeDeclaration(x)),
        interface_class_item_method,
        map(pair(local_parameter_declaration, symbol(";")), |x| {
            InterfaceClassItem::LocalParameterDeclaration(x)
        }),
        map(pair(parameter_declaration, symbol(";")), |x| {
            InterfaceClassItem::ParameterDeclaration(x)
        }),
        map(symbol(";"), |x| InterfaceClassItem::Null(x)),
    ))(s)
}

#[parser]
pub fn interface_class_item_method(s: Span) -> IResult<Span, InterfaceClassItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = interface_class_method(s)?;
    Ok((
        s,
        InterfaceClassItem::Method(InterfaceClassItemMethod { nodes: (a, b) }),
    ))
}

#[parser]
pub fn interface_class_method(s: Span) -> IResult<Span, InterfaceClassMethod> {
    let (s, a) = symbol("pure")(s)?;
    let (s, b) = symbol("virtual")(s)?;
    let (s, c) = method_prototype(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        InterfaceClassMethod {
            nodes: (a, b, c, d),
        },
    ))
}

#[parser]
pub fn package_declaration(s: Span) -> IResult<Span, PackageDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = symbol("package")(s)?;
    let (s, c) = opt(lifetime)(s)?;
    let (s, d) = package_identifier(s)?;
    let (s, e) = symbol(";")(s)?;
    let (s, f) = opt(timeunits_declaration)(s)?;
    let (s, g) = many0(pair(many0(attribute_instance), package_item))(s)?;
    let (s, h) = symbol("endpackage")(s)?;
    let (s, i) = opt(pair(symbol(":"), package_identifier))(s)?;
    Ok((
        s,
        PackageDeclaration {
            nodes: (a, b, c, d, e, f, g, h, i),
        },
    ))
}

#[parser]
pub fn timeunits_declaration(s: Span) -> IResult<Span, TimeunitsDeclaration> {
    alt((
        timeunits_declaration_timeunit_timeprecision,
        timeunits_declaration_timeunit,
        timeunits_declaration_timeprecision_timeunit,
        timeunits_declaration_timeprecision,
    ))(s)
}

#[parser]
pub fn timeunits_declaration_timeunit(s: Span) -> IResult<Span, TimeunitsDeclaration> {
    let (s, a) = symbol("timeunit")(s)?;
    let (s, b) = time_literal(s)?;
    let (s, c) = opt(pair(symbol("/"), time_literal))(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        TimeunitsDeclaration::Timeunit(TimeunitsDeclarationTimeunit {
            nodes: (a, b, c, d),
        }),
    ))
}

#[parser]
pub fn timeunits_declaration_timeprecision(s: Span) -> IResult<Span, TimeunitsDeclaration> {
    let (s, a) = symbol("timeprecision")(s)?;
    let (s, b) = time_literal(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        TimeunitsDeclaration::Timeprecision(TimeunitsDeclarationTimeprecision { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn timeunits_declaration_timeunit_timeprecision(
    s: Span,
) -> IResult<Span, TimeunitsDeclaration> {
    let (s, a) = symbol("timeunit")(s)?;
    let (s, b) = time_literal(s)?;
    let (s, c) = symbol(";")(s)?;
    let (s, d) = symbol("timeprecision")(s)?;
    let (s, e) = time_literal(s)?;
    let (s, f) = symbol(";")(s)?;
    Ok((
        s,
        TimeunitsDeclaration::TimeunitTimeprecision(TimeunitsDeclarationTimeunitTimeprecision {
            nodes: (a, b, c, d, e, f),
        }),
    ))
}

#[parser]
pub fn timeunits_declaration_timeprecision_timeunit(
    s: Span,
) -> IResult<Span, TimeunitsDeclaration> {
    let (s, a) = symbol("timeprecision")(s)?;
    let (s, b) = time_literal(s)?;
    let (s, c) = symbol(";")(s)?;
    let (s, d) = symbol("timeunit")(s)?;
    let (s, e) = time_literal(s)?;
    let (s, f) = symbol(";")(s)?;
    Ok((
        s,
        TimeunitsDeclaration::TimeprecisionTimeunit(TimeunitsDeclarationTimeprecisionTimeunit {
            nodes: (a, b, c, d, e, f),
        }),
    ))
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_timeunits_declaration() {
        parser_test!(timeunits_declaration, "timeunit 1.0ps;", Ok((_, _)));
        parser_test!(timeunits_declaration, "timeunit 1.0ps / 20ms;", Ok((_, _)));
        parser_test!(timeunits_declaration, "timeprecision 10.0fs;", Ok((_, _)));
        parser_test!(
            timeunits_declaration,
            "timeunit 10.0fs; timeprecision 20s;",
            Ok((_, _))
        );
        parser_test!(
            timeunits_declaration,
            "timeprecision 10.0fs; timeunit 20s \n;",
            Ok((_, _))
        );
    }
}

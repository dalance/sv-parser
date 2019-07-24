use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct SourceText {
    pub nodes: (Option<TimeunitsDeclaration>, Vec<Description>),
}

#[derive(Clone, Debug, Node)]
pub enum Description {
    ModuleDeclaration(ModuleDeclaration),
    UdpDeclaration(UdpDeclaration),
    InterfaceDeclaration(InterfaceDeclaration),
    ProgramDeclaration(ProgramDeclaration),
    PackageDeclaration(PackageDeclaration),
    PackageItem(DescriptionPackageItem),
    BindDirective(DescriptionBindDirective),
    ConfigDeclaration(ConfigDeclaration),
}

#[derive(Clone, Debug, Node)]
pub struct DescriptionPackageItem {
    pub nodes: (Vec<AttributeInstance>, PackageItem),
}

#[derive(Clone, Debug, Node)]
pub struct DescriptionBindDirective {
    pub nodes: (Vec<AttributeInstance>, BindDirective),
}

#[derive(Clone, Debug, Node)]
pub struct ModuleNonansiHeader {
    pub nodes: (
        Vec<AttributeInstance>,
        ModuleKeyword,
        Option<Lifetime>,
        ModuleIdentifier,
        Vec<PackageImportDeclaration>,
        Option<ParameterPortList>,
        ListOfPorts,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ModuleAnsiHeader {
    pub nodes: (
        Vec<AttributeInstance>,
        ModuleKeyword,
        Option<Lifetime>,
        ModuleIdentifier,
        Vec<PackageImportDeclaration>,
        Option<ParameterPortList>,
        Option<ListOfPortDeclarations>,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum ModuleDeclaration {
    Nonansi(ModuleDeclarationNonansi),
    Ansi(ModuleDeclarationAnsi),
    Wildcard(ModuleDeclarationWildcard),
    ExternNonansi(ModuleDeclarationExternNonansi),
    ExternAnsi(ModuleDeclarationExternAnsi),
}

#[derive(Clone, Debug, Node)]
pub struct ModuleDeclarationNonansi {
    pub nodes: (
        ModuleNonansiHeader,
        Option<TimeunitsDeclaration>,
        Vec<ModuleItem>,
        Keyword,
        Option<(Symbol, ModuleIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ModuleDeclarationAnsi {
    pub nodes: (
        ModuleAnsiHeader,
        Option<TimeunitsDeclaration>,
        Vec<NonPortModuleItem>,
        Keyword,
        Option<(Symbol, ModuleIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ModuleDeclarationWildcard {
    pub nodes: (
        Vec<AttributeInstance>,
        ModuleKeyword,
        Option<Lifetime>,
        ModuleIdentifier,
        Paren<Symbol>,
        Symbol,
        Option<TimeunitsDeclaration>,
        Vec<ModuleItem>,
        Keyword,
        Option<(Symbol, ModuleIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ModuleDeclarationExternNonansi {
    pub nodes: (Keyword, ModuleNonansiHeader),
}

#[derive(Clone, Debug, Node)]
pub struct ModuleDeclarationExternAnsi {
    pub nodes: (Keyword, ModuleAnsiHeader),
}

#[derive(Clone, Debug, Node)]
pub enum ModuleKeyword {
    Module(Keyword),
    Macromodule(Keyword),
}

#[derive(Clone, Debug, Node)]
pub enum InterfaceDeclaration {
    Nonansi(InterfaceDeclarationNonansi),
    Ansi(InterfaceDeclarationAnsi),
    Wildcard(InterfaceDeclarationWildcard),
    ExternNonansi(InterfaceDeclarationExternNonansi),
    ExternAnsi(InterfaceDeclarationExternAnsi),
}

#[derive(Clone, Debug, Node)]
pub struct InterfaceDeclarationNonansi {
    pub nodes: (
        InterfaceNonansiHeader,
        Option<TimeunitsDeclaration>,
        Vec<InterfaceItem>,
        Keyword,
        Option<(Symbol, InterfaceIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct InterfaceDeclarationAnsi {
    pub nodes: (
        InterfaceAnsiHeader,
        Option<TimeunitsDeclaration>,
        Vec<NonPortInterfaceItem>,
        Keyword,
        Option<(Symbol, InterfaceIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct InterfaceDeclarationWildcard {
    pub nodes: (
        Vec<AttributeInstance>,
        Keyword,
        Option<Lifetime>,
        InterfaceIdentifier,
        Paren<Symbol>,
        Symbol,
        Option<TimeunitsDeclaration>,
        Vec<InterfaceItem>,
        Keyword,
        Option<(Symbol, InterfaceIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct InterfaceDeclarationExternNonansi {
    pub nodes: (Keyword, InterfaceNonansiHeader),
}

#[derive(Clone, Debug, Node)]
pub struct InterfaceDeclarationExternAnsi {
    pub nodes: (Keyword, InterfaceAnsiHeader),
}

#[derive(Clone, Debug, Node)]
pub struct InterfaceNonansiHeader {
    pub nodes: (
        Vec<AttributeInstance>,
        Keyword,
        Option<Lifetime>,
        InterfaceIdentifier,
        Vec<PackageImportDeclaration>,
        Option<ParameterPortList>,
        ListOfPorts,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct InterfaceAnsiHeader {
    pub nodes: (
        Vec<AttributeInstance>,
        Keyword,
        Option<Lifetime>,
        InterfaceIdentifier,
        Vec<PackageImportDeclaration>,
        Option<ParameterPortList>,
        Option<ListOfPortDeclarations>,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum ProgramDeclaration {
    Nonansi(ProgramDeclarationNonansi),
    Ansi(ProgramDeclarationAnsi),
    Wildcard(ProgramDeclarationWildcard),
    ExternNonansi(ProgramDeclarationExternNonansi),
    ExternAnsi(ProgramDeclarationExternAnsi),
}

#[derive(Clone, Debug, Node)]
pub struct ProgramDeclarationNonansi {
    pub nodes: (
        ProgramNonansiHeader,
        Option<TimeunitsDeclaration>,
        Vec<ProgramItem>,
        Keyword,
        Option<(Symbol, ProgramIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ProgramDeclarationAnsi {
    pub nodes: (
        ProgramAnsiHeader,
        Option<TimeunitsDeclaration>,
        Vec<NonPortProgramItem>,
        Keyword,
        Option<(Symbol, ProgramIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ProgramDeclarationWildcard {
    pub nodes: (
        Vec<AttributeInstance>,
        Keyword,
        ProgramIdentifier,
        Paren<Symbol>,
        Symbol,
        Option<TimeunitsDeclaration>,
        Vec<ProgramItem>,
        Keyword,
        Option<(Symbol, ProgramIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ProgramDeclarationExternNonansi {
    pub nodes: (Keyword, ProgramNonansiHeader),
}

#[derive(Clone, Debug, Node)]
pub struct ProgramDeclarationExternAnsi {
    pub nodes: (Keyword, ProgramAnsiHeader),
}

#[derive(Clone, Debug, Node)]
pub struct ProgramNonansiHeader {
    pub nodes: (
        Vec<AttributeInstance>,
        Keyword,
        Option<Lifetime>,
        ProgramIdentifier,
        Vec<PackageImportDeclaration>,
        Option<ParameterPortList>,
        ListOfPorts,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ProgramAnsiHeader {
    pub nodes: (
        Vec<AttributeInstance>,
        Keyword,
        Option<Lifetime>,
        ProgramIdentifier,
        Vec<PackageImportDeclaration>,
        Option<ParameterPortList>,
        Option<ListOfPortDeclarations>,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct CheckerDeclaration {
    pub nodes: (
        Keyword,
        CheckerIdentifier,
        Option<Paren<Option<CheckerPortList>>>,
        Symbol,
        Vec<(Vec<AttributeInstance>, CheckerOrGenerateItem)>,
        Keyword,
        Option<(Symbol, CheckerIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ClassDeclaration {
    pub nodes: (
        Option<Virtual>,
        Keyword,
        Option<Lifetime>,
        ClassIdentifier,
        Option<ParameterPortList>,
        Option<(Keyword, ClassType, Option<Paren<ListOfArguments>>)>,
        Option<(Keyword, List<Symbol, InterfaceClassType>)>,
        Symbol,
        Vec<ClassItem>,
        Keyword,
        Option<(Symbol, ClassIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct Virtual {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, Node)]
pub struct InterfaceClassType {
    pub nodes: (PsClassIdentifier, Option<ParameterValueAssignment>),
}

#[derive(Clone, Debug, Node)]
pub struct InterfaceClassDeclaration {
    pub nodes: (
        Keyword,
        Keyword,
        ClassIdentifier,
        Option<ParameterPortList>,
        Option<(Keyword, List<Symbol, InterfaceClassType>)>,
        Symbol,
        Vec<InterfaceClassItem>,
        Keyword,
        Option<(Symbol, ClassIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum InterfaceClassItem {
    TypeDeclaration(TypeDeclaration),
    Method(InterfaceClassItemMethod),
    LocalParameterDeclaration((LocalParameterDeclaration, Symbol)),
    ParameterDeclaration((ParameterDeclaration, Symbol)),
    Null(Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct InterfaceClassItemMethod {
    pub nodes: (Vec<AttributeInstance>, InterfaceClassMethod),
}

#[derive(Clone, Debug, Node)]
pub struct InterfaceClassMethod {
    pub nodes: (Keyword, Keyword, MethodPrototype, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct PackageDeclaration {
    pub nodes: (
        Vec<AttributeInstance>,
        Keyword,
        Option<Lifetime>,
        PackageIdentifier,
        Symbol,
        Option<TimeunitsDeclaration>,
        Vec<(Vec<AttributeInstance>, PackageItem)>,
        Keyword,
        Option<(Symbol, PackageIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum TimeunitsDeclaration {
    Timeunit(TimeunitsDeclarationTimeunit),
    Timeprecision(TimeunitsDeclarationTimeprecision),
    TimeunitTimeprecision(TimeunitsDeclarationTimeunitTimeprecision),
    TimeprecisionTimeunit(TimeunitsDeclarationTimeprecisionTimeunit),
}

#[derive(Clone, Debug, Node)]
pub struct TimeunitsDeclarationTimeunit {
    pub nodes: (Keyword, TimeLiteral, Option<(Symbol, TimeLiteral)>, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct TimeunitsDeclarationTimeprecision {
    pub nodes: (Keyword, TimeLiteral, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct TimeunitsDeclarationTimeunitTimeprecision {
    pub nodes: (Keyword, TimeLiteral, Symbol, Keyword, TimeLiteral, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct TimeunitsDeclarationTimeprecisionTimeunit {
    pub nodes: (Keyword, TimeLiteral, Symbol, Keyword, TimeLiteral, Symbol),
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

#[parser(MaybeRecursive)]
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
    let (s, d) = keyword("endmodule")(s)?;
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
    let (s, d) = keyword("endmodule")(s)?;
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
    let (s, i) = keyword("endmodule")(s)?;
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
    let (s, a) = keyword("extern")(s)?;
    let (s, b) = module_nonansi_header(s)?;
    Ok((
        s,
        ModuleDeclaration::ExternNonansi(ModuleDeclarationExternNonansi { nodes: (a, b) }),
    ))
}

#[parser]
pub fn module_declaration_extern_ansi(s: Span) -> IResult<Span, ModuleDeclaration> {
    let (s, a) = keyword("extern")(s)?;
    let (s, b) = module_ansi_header(s)?;
    Ok((
        s,
        ModuleDeclaration::ExternAnsi(ModuleDeclarationExternAnsi { nodes: (a, b) }),
    ))
}

#[parser]
pub fn module_keyword(s: Span) -> IResult<Span, ModuleKeyword> {
    alt((
        map(keyword("module"), |x| ModuleKeyword::Module(x)),
        map(keyword("macromodule"), |x| ModuleKeyword::Macromodule(x)),
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
    let (s, d) = keyword("endinterface")(s)?;
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
    let (s, d) = keyword("endinterface")(s)?;
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
    let (s, b) = keyword("interface")(s)?;
    let (s, c) = opt(lifetime)(s)?;
    let (s, d) = interface_identifier(s)?;
    let (s, e) = paren(symbol(".*"))(s)?;
    let (s, f) = symbol(";")(s)?;
    let (s, g) = opt(timeunits_declaration)(s)?;
    let (s, h) = many0(interface_item)(s)?;
    let (s, i) = keyword("endinterface")(s)?;
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
    let (s, a) = keyword("extern")(s)?;
    let (s, b) = interface_nonansi_header(s)?;
    Ok((
        s,
        InterfaceDeclaration::ExternNonansi(InterfaceDeclarationExternNonansi { nodes: (a, b) }),
    ))
}

#[parser]
pub fn interface_declaration_extern_ansi(s: Span) -> IResult<Span, InterfaceDeclaration> {
    let (s, a) = keyword("extern")(s)?;
    let (s, b) = interface_ansi_header(s)?;
    Ok((
        s,
        InterfaceDeclaration::ExternAnsi(InterfaceDeclarationExternAnsi { nodes: (a, b) }),
    ))
}

#[parser]
pub fn interface_nonansi_header(s: Span) -> IResult<Span, InterfaceNonansiHeader> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = keyword("interface")(s)?;
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
    let (s, b) = keyword("interface")(s)?;
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
    let (s, d) = keyword("endprogram")(s)?;
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
    let (s, d) = keyword("endprogram")(s)?;
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
    let (s, b) = keyword("program")(s)?;
    let (s, c) = program_identifier(s)?;
    let (s, d) = paren(symbol(".*"))(s)?;
    let (s, e) = symbol(";")(s)?;
    let (s, f) = opt(timeunits_declaration)(s)?;
    let (s, g) = many0(program_item)(s)?;
    let (s, h) = keyword("endprogram")(s)?;
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
    let (s, a) = keyword("extern")(s)?;
    let (s, b) = program_nonansi_header(s)?;
    Ok((
        s,
        ProgramDeclaration::ExternNonansi(ProgramDeclarationExternNonansi { nodes: (a, b) }),
    ))
}

#[parser]
pub fn program_declaration_extern_ansi(s: Span) -> IResult<Span, ProgramDeclaration> {
    let (s, a) = keyword("extern")(s)?;
    let (s, b) = program_ansi_header(s)?;
    Ok((
        s,
        ProgramDeclaration::ExternAnsi(ProgramDeclarationExternAnsi { nodes: (a, b) }),
    ))
}

#[parser]
pub fn program_nonansi_header(s: Span) -> IResult<Span, ProgramNonansiHeader> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = keyword("prgogram")(s)?;
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
    let (s, b) = keyword("program")(s)?;
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
    let (s, a) = keyword("checker")(s)?;
    let (s, b) = checker_identifier(s)?;
    let (s, c) = opt(paren(opt(checker_port_list)))(s)?;
    let (s, d) = symbol(";")(s)?;
    let (s, e) = many0(pair(many0(attribute_instance), checker_or_generate_item))(s)?;
    let (s, f) = keyword("endchecker")(s)?;
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
    let (s, a) = opt(map(keyword("virtual"), |x| Virtual { nodes: (x,) }))(s)?;
    let (s, b) = keyword("class")(s)?;
    let (s, c) = opt(lifetime)(s)?;
    let (s, d) = class_identifier(s)?;
    let (s, e) = opt(parameter_port_list)(s)?;
    let (s, f) = opt(triple(
        keyword("extends"),
        class_type,
        opt(paren(list_of_arguments)),
    ))(s)?;
    let (s, g) = opt(pair(
        keyword("implements"),
        list(symbol(","), interface_class_type),
    ))(s)?;
    let (s, h) = symbol(";")(s)?;
    let (s, i) = many0(class_item)(s)?;
    let (s, j) = keyword("endclass")(s)?;
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
    let (s, a) = keyword("interface")(s)?;
    let (s, b) = keyword("class")(s)?;
    let (s, c) = class_identifier(s)?;
    let (s, d) = opt(parameter_port_list)(s)?;
    let (s, e) = opt(pair(
        keyword("extends"),
        list(symbol(","), interface_class_type),
    ))(s)?;
    let (s, f) = symbol(";")(s)?;
    let (s, g) = many0(interface_class_item)(s)?;
    let (s, h) = keyword("endclass")(s)?;
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
    let (s, a) = keyword("pure")(s)?;
    let (s, b) = keyword("virtual")(s)?;
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
    let (s, b) = keyword("package")(s)?;
    let (s, c) = opt(lifetime)(s)?;
    let (s, d) = package_identifier(s)?;
    let (s, e) = symbol(";")(s)?;
    let (s, f) = opt(timeunits_declaration)(s)?;
    let (s, g) = many0(pair(many0(attribute_instance), package_item))(s)?;
    let (s, h) = keyword("endpackage")(s)?;
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
    let (s, a) = keyword("timeunit")(s)?;
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
    let (s, a) = keyword("timeprecision")(s)?;
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
    let (s, a) = keyword("timeunit")(s)?;
    let (s, b) = time_literal(s)?;
    let (s, c) = symbol(";")(s)?;
    let (s, d) = keyword("timeprecision")(s)?;
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
    let (s, a) = keyword("timeprecision")(s)?;
    let (s, b) = time_literal(s)?;
    let (s, c) = symbol(";")(s)?;
    let (s, d) = keyword("timeunit")(s)?;
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

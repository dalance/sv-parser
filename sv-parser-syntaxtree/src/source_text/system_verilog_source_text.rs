use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct SourceText {
    pub nodes: (
        Vec<WhiteSpace>,
        Option<TimeunitsDeclaration>,
        Vec<Description>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum Description {
    ModuleDeclaration(Box<ModuleDeclaration>),
    UdpDeclaration(Box<UdpDeclaration>),
    InterfaceDeclaration(Box<InterfaceDeclaration>),
    InterfaceClassDeclaration(Box<InterfaceClassDeclaration>),
    ProgramDeclaration(Box<ProgramDeclaration>),
    PackageDeclaration(Box<PackageDeclaration>),
    PackageItem(Box<DescriptionPackageItem>),
    BindDirective(Box<DescriptionBindDirective>),
    ConfigDeclaration(Box<ConfigDeclaration>),
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
    Nonansi(Box<ModuleDeclarationNonansi>),
    Ansi(Box<ModuleDeclarationAnsi>),
    Wildcard(Box<ModuleDeclarationWildcard>),
    ExternNonansi(Box<ModuleDeclarationExternNonansi>),
    ExternAnsi(Box<ModuleDeclarationExternAnsi>),
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
    Module(Box<Keyword>),
    Macromodule(Box<Keyword>),
}

#[derive(Clone, Debug, Node)]
pub enum InterfaceDeclaration {
    Nonansi(Box<InterfaceDeclarationNonansi>),
    Ansi(Box<InterfaceDeclarationAnsi>),
    Wildcard(Box<InterfaceDeclarationWildcard>),
    ExternNonansi(Box<InterfaceDeclarationExternNonansi>),
    ExternAnsi(Box<InterfaceDeclarationExternAnsi>),
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
    Nonansi(Box<ProgramDeclarationNonansi>),
    Ansi(Box<ProgramDeclarationAnsi>),
    Wildcard(Box<ProgramDeclarationWildcard>),
    ExternNonansi(Box<ProgramDeclarationExternNonansi>),
    ExternAnsi(Box<ProgramDeclarationExternAnsi>),
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
    TypeDeclaration(Box<TypeDeclaration>),
    Method(Box<InterfaceClassItemMethod>),
    LocalParameterDeclaration(Box<(LocalParameterDeclaration, Symbol)>),
    ParameterDeclaration(Box<(ParameterDeclaration, Symbol)>),
    Null(Box<Symbol>),
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
    Timeunit(Box<TimeunitsDeclarationTimeunit>),
    Timeprecision(Box<TimeunitsDeclarationTimeprecision>),
    TimeunitTimeprecision(Box<TimeunitsDeclarationTimeunitTimeprecision>),
    TimeprecisionTimeunit(Box<TimeunitsDeclarationTimeprecisionTimeunit>),
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

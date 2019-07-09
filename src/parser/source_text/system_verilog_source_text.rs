use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct SourceText<'a> {
    pub nodes: (Option<TimeunitsDeclaration<'a>>, Vec<Description<'a>>),
}

#[derive(Debug)]
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

#[derive(Debug)]
pub struct DescriptionPackageItem<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, PackageItem<'a>),
}

#[derive(Debug)]
pub struct DescriptionBindDirective<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, BindDirective<'a>),
}

#[derive(Debug)]
pub struct ModuleNonansiHeader<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        ModuleKeyword,
        Option<Lifetime>,
        ModuleIdentifier<'a>,
        Vec<PackageImportDeclaration<'a>>,
        Option<ParameterPortList<'a>>,
        ListOfPorts<'a>,
    ),
}

#[derive(Debug)]
pub struct ModuleAnsiHeader<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        ModuleKeyword,
        Option<Lifetime>,
        ModuleIdentifier<'a>,
        Vec<PackageImportDeclaration<'a>>,
        Option<ParameterPortList<'a>>,
        Option<ListOfPortDeclarations<'a>>,
    ),
}

#[derive(Debug)]
pub enum ModuleDeclaration<'a> {
    Nonansi(ModuleDeclarationNonansi<'a>),
    Ansi(ModuleDeclarationAnsi<'a>),
    Wildcard(ModuleDeclarationWildcard<'a>),
    ExternNonansi(ModuleDeclarationExternNonansi<'a>),
    ExternAnsi(ModuleDeclarationExternAnsi<'a>),
}

#[derive(Debug)]
pub struct ModuleDeclarationNonansi<'a> {
    pub nodes: (
        ModuleNonansiHeader<'a>,
        Option<TimeunitsDeclaration<'a>>,
        Vec<ModuleItem<'a>>,
        Option<ModuleIdentifier<'a>>,
    ),
}

#[derive(Debug)]
pub struct ModuleDeclarationAnsi<'a> {
    pub nodes: (
        ModuleAnsiHeader<'a>,
        Option<TimeunitsDeclaration<'a>>,
        Vec<NonPortModuleItem<'a>>,
        Option<ModuleIdentifier<'a>>,
    ),
}

#[derive(Debug)]
pub struct ModuleDeclarationWildcard<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        ModuleKeyword,
        Option<Lifetime>,
        ModuleIdentifier<'a>,
        Option<TimeunitsDeclaration<'a>>,
        Vec<ModuleItem<'a>>,
        Option<ModuleIdentifier<'a>>,
    ),
}

#[derive(Debug)]
pub struct ModuleDeclarationExternNonansi<'a> {
    pub nodes: (ModuleNonansiHeader<'a>,),
}

#[derive(Debug)]
pub struct ModuleDeclarationExternAnsi<'a> {
    pub nodes: (ModuleAnsiHeader<'a>,),
}

#[derive(Debug)]
pub enum ModuleKeyword {
    Module,
    Macromodule,
}

#[derive(Debug)]
pub enum InterfaceDeclaration<'a> {
    Nonansi(InterfaceDeclarationNonansi<'a>),
    Ansi(InterfaceDeclarationAnsi<'a>),
    Wildcard(InterfaceDeclarationWildcard<'a>),
    ExternNonansi(InterfaceDeclarationExternNonansi<'a>),
    ExternAnsi(InterfaceDeclarationExternAnsi<'a>),
}

#[derive(Debug)]
pub struct InterfaceDeclarationNonansi<'a> {
    pub nodes: (
        InterfaceNonansiHeader<'a>,
        Option<TimeunitsDeclaration<'a>>,
        Vec<InterfaceItem<'a>>,
        Option<InterfaceIdentifier<'a>>,
    ),
}

#[derive(Debug)]
pub struct InterfaceDeclarationAnsi<'a> {
    pub nodes: (
        InterfaceAnsiHeader<'a>,
        Option<TimeunitsDeclaration<'a>>,
        Vec<NonPortInterfaceItem<'a>>,
        Option<InterfaceIdentifier<'a>>,
    ),
}

#[derive(Debug)]
pub struct InterfaceDeclarationWildcard<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        InterfaceIdentifier<'a>,
        Option<TimeunitsDeclaration<'a>>,
        Vec<InterfaceItem<'a>>,
        Option<InterfaceIdentifier<'a>>,
    ),
}

#[derive(Debug)]
pub struct InterfaceDeclarationExternNonansi<'a> {
    pub nodes: (InterfaceNonansiHeader<'a>,),
}

#[derive(Debug)]
pub struct InterfaceDeclarationExternAnsi<'a> {
    pub nodes: (InterfaceAnsiHeader<'a>,),
}

#[derive(Debug)]
pub struct InterfaceNonansiHeader<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Option<Lifetime>,
        InterfaceIdentifier<'a>,
        Vec<PackageImportDeclaration<'a>>,
        Option<ParameterPortList<'a>>,
        ListOfPorts<'a>,
    ),
}

#[derive(Debug)]
pub struct InterfaceAnsiHeader<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Option<Lifetime>,
        InterfaceIdentifier<'a>,
        Vec<PackageImportDeclaration<'a>>,
        Option<ParameterPortList<'a>>,
        Option<ListOfPortDeclarations<'a>>,
    ),
}

#[derive(Debug)]
pub enum ProgramDeclaration<'a> {
    Nonansi(ProgramDeclarationNonansi<'a>),
    Ansi(ProgramDeclarationAnsi<'a>),
    Wildcard(ProgramDeclarationWildcard<'a>),
    ExternNonansi(ProgramDeclarationExternNonansi<'a>),
    ExternAnsi(ProgramDeclarationExternAnsi<'a>),
}

#[derive(Debug)]
pub struct ProgramDeclarationNonansi<'a> {
    pub nodes: (
        ProgramNonansiHeader<'a>,
        Option<TimeunitsDeclaration<'a>>,
        Vec<ProgramItem<'a>>,
        Option<ProgramIdentifier<'a>>,
    ),
}

#[derive(Debug)]
pub struct ProgramDeclarationAnsi<'a> {
    pub nodes: (
        ProgramAnsiHeader<'a>,
        Option<TimeunitsDeclaration<'a>>,
        Vec<NonPortProgramItem<'a>>,
        Option<ProgramIdentifier<'a>>,
    ),
}

#[derive(Debug)]
pub struct ProgramDeclarationWildcard<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        ProgramIdentifier<'a>,
        Option<TimeunitsDeclaration<'a>>,
        Vec<ProgramItem<'a>>,
        Option<ProgramIdentifier<'a>>,
    ),
}

#[derive(Debug)]
pub struct ProgramDeclarationExternNonansi<'a> {
    pub nodes: (ProgramNonansiHeader<'a>,),
}

#[derive(Debug)]
pub struct ProgramDeclarationExternAnsi<'a> {
    pub nodes: (ProgramAnsiHeader<'a>,),
}

#[derive(Debug)]
pub struct ProgramNonansiHeader<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Option<Lifetime>,
        ProgramIdentifier<'a>,
        Vec<PackageImportDeclaration<'a>>,
        Option<ParameterPortList<'a>>,
        ListOfPorts<'a>,
    ),
}

#[derive(Debug)]
pub struct ProgramAnsiHeader<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Option<Lifetime>,
        ProgramIdentifier<'a>,
        Vec<PackageImportDeclaration<'a>>,
        Option<ParameterPortList<'a>>,
        Option<ListOfPortDeclarations<'a>>,
    ),
}

#[derive(Debug)]
pub struct CheckerDeclaration<'a> {
    pub nodes: (
        CheckerIdentifier<'a>,
        Option<CheckerPortList<'a>>,
        Vec<(Vec<AttributeInstance<'a>>, CheckerOrGenerateItem<'a>)>,
        Option<CheckerIdentifier<'a>>,
    ),
}

#[derive(Debug)]
pub struct ClassDeclaration<'a> {
    pub nodes: (
        Option<Virtual>,
        Option<Lifetime>,
        ClassIdentifier<'a>,
        Option<ParameterPortList<'a>>,
        Option<(ClassType<'a>, Option<ListOfArguments<'a>>)>,
        Option<Vec<InterfaceClassType<'a>>>,
        Vec<ClassItem<'a>>,
        Option<ClassIdentifier<'a>>,
    ),
}

#[derive(Debug)]
pub struct Virtual {}

#[derive(Debug)]
pub struct InterfaceClassType<'a> {
    pub nodes: (PsClassIdentifier<'a>, Option<ParameterValueAssignment<'a>>),
}

#[derive(Debug)]
pub struct InterfaceClassDeclaration<'a> {
    pub nodes: (
        ClassIdentifier<'a>,
        Option<ParameterPortList<'a>>,
        Option<Vec<InterfaceClassType<'a>>>,
        Vec<InterfaceClassItem<'a>>,
        Option<ClassIdentifier<'a>>,
    ),
}

#[derive(Debug)]
pub enum InterfaceClassItem<'a> {
    TypeDeclaration(TypeDeclaration<'a>),
    Method(InterfaceClassItemMethod<'a>),
    LocalParameterDeclaration(LocalParameterDeclaration<'a>),
    ParameterDeclaration(ParameterDeclaration<'a>),
    Empty,
}

#[derive(Debug)]
pub struct InterfaceClassItemMethod<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, InterfaceClassMethod<'a>),
}

#[derive(Debug)]
pub struct InterfaceClassMethod<'a> {
    pub nodes: (MethodPrototype<'a>,),
}

#[derive(Debug)]
pub struct PackageDeclaration<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Option<Lifetime>,
        PackageIdentifier<'a>,
        Option<TimeunitsDeclaration<'a>>,
        Vec<(Vec<AttributeInstance<'a>>, PackageItem<'a>)>,
        Option<PackageIdentifier<'a>>,
    ),
}

#[derive(Debug)]
pub enum TimeunitsDeclaration<'a> {
    Timeunit(TimeunitsDeclarationTimeunit<'a>),
    Timeprecision(TimeunitsDeclarationTimeprecision<'a>),
    TimeunitTimeprecision(TimeunitsDeclarationTimeunitTimeprecision<'a>),
    TimeprecisionTimeunit(TimeunitsDeclarationTimeprecisionTimeunit<'a>),
}

#[derive(Debug)]
pub struct TimeunitsDeclarationTimeunit<'a> {
    pub nodes: (TimeLiteral<'a>, Option<TimeLiteral<'a>>),
}

#[derive(Debug)]
pub struct TimeunitsDeclarationTimeprecision<'a> {
    pub nodes: (TimeLiteral<'a>,),
}

#[derive(Debug)]
pub struct TimeunitsDeclarationTimeunitTimeprecision<'a> {
    pub nodes: (TimeLiteral<'a>, TimeLiteral<'a>),
}

#[derive(Debug)]
pub struct TimeunitsDeclarationTimeprecisionTimeunit<'a> {
    pub nodes: (TimeLiteral<'a>, TimeLiteral<'a>),
}

// -----------------------------------------------------------------------------

pub fn source_text(s: Span) -> IResult<Span, SourceText> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn description(s: Span) -> IResult<Span, Description> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn module_nonansi_header(s: Span) -> IResult<Span, ModuleNonansiHeader> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn module_ansi_header(s: Span) -> IResult<Span, ModuleAnsiHeader> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn module_declaration(s: Span) -> IResult<Span, ModuleDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn module_keyword(s: Span) -> IResult<Span, ModuleKeyword> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn interface_declaration(s: Span) -> IResult<Span, InterfaceDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn interface_nonansi_header(s: Span) -> IResult<Span, InterfaceNonansiHeader> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn interface_ansi_header(s: Span) -> IResult<Span, InterfaceAnsiHeader> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn program_declaration(s: Span) -> IResult<Span, ProgramDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn program_nonansi_header(s: Span) -> IResult<Span, ProgramNonansiHeader> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn program_ansi_header(s: Span) -> IResult<Span, ProgramAnsiHeader> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn checker_declaration(s: Span) -> IResult<Span, CheckerDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn class_declaration(s: Span) -> IResult<Span, ClassDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn interface_class_type(s: Span) -> IResult<Span, InterfaceClassType> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn interface_class_declaration(s: Span) -> IResult<Span, InterfaceClassDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn interface_class_item(s: Span) -> IResult<Span, InterfaceClassItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn interface_class_method(s: Span) -> IResult<Span, InterfaceClassMethod> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn package_declaration(s: Span) -> IResult<Span, PackageDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn timeunit_declaration(s: Span) -> IResult<Span, TimeunitsDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

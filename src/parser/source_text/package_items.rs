use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum PackageItem {
    PackageOrGenerateItemDeclaration(PackageOrGenerateItemDeclaration),
    AnonymousProgram(AnonymousProgram),
    PackageExportDeclaration(PackageExportDeclaration),
    TimeunitsDeclaration(TimeunitsDeclaration),
}

#[derive(Clone, Debug, Node)]
pub enum PackageOrGenerateItemDeclaration {
    NetDeclaration(NetDeclaration),
    DataDeclaration(DataDeclaration),
    TaskDeclaration(TaskDeclaration),
    FunctionDeclaration(FunctionDeclaration),
    CheckerDeclaration(CheckerDeclaration),
    DpiImportExport(DpiImportExport),
    ExternConstraintDeclaration(ExternConstraintDeclaration),
    ClassDeclaration(ClassDeclaration),
    ClassConstructorDeclaration(ClassConstructorDeclaration),
    LocalParameterDeclaration((LocalParameterDeclaration, Symbol)),
    ParameterDeclaration((ParameterDeclaration, Symbol)),
    CovergroupDeclaration(CovergroupDeclaration),
    AssertionItemDeclaration(AssertionItemDeclaration),
    Empty(Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct AnonymousProgram {
    pub nodes: (
        Keyword,
        Symbol,
        Vec<AnonymousProgramItem>,
        Keyword,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum AnonymousProgramItem {
    TaskDeclaration(TaskDeclaration),
    FunctionDeclaration(FunctionDeclaration),
    ClassDeclaration(ClassDeclaration),
    CovergroupDeclaration(CovergroupDeclaration),
    ClassConstructorDeclaration(ClassConstructorDeclaration),
    Empty(Symbol),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn package_item(s: Span) -> IResult<Span, PackageItem> {
    alt((
        map(package_or_generate_item_declaration, |x| {
            PackageItem::PackageOrGenerateItemDeclaration(x)
        }),
        map(anonymous_program, |x| PackageItem::AnonymousProgram(x)),
        map(package_export_declaration, |x| {
            PackageItem::PackageExportDeclaration(x)
        }),
        map(timeunits_declaration, |x| {
            PackageItem::TimeunitsDeclaration(x)
        }),
    ))(s)
}

#[parser]
pub fn package_or_generate_item_declaration(
    s: Span,
) -> IResult<Span, PackageOrGenerateItemDeclaration> {
    alt((
        map(net_declaration, |x| {
            PackageOrGenerateItemDeclaration::NetDeclaration(x)
        }),
        map(data_declaration, |x| {
            PackageOrGenerateItemDeclaration::DataDeclaration(x)
        }),
        map(task_declaration, |x| {
            PackageOrGenerateItemDeclaration::TaskDeclaration(x)
        }),
        map(function_declaration, |x| {
            PackageOrGenerateItemDeclaration::FunctionDeclaration(x)
        }),
        map(checker_declaration, |x| {
            PackageOrGenerateItemDeclaration::CheckerDeclaration(x)
        }),
        map(dpi_import_export, |x| {
            PackageOrGenerateItemDeclaration::DpiImportExport(x)
        }),
        map(extern_constraint_declaration, |x| {
            PackageOrGenerateItemDeclaration::ExternConstraintDeclaration(x)
        }),
        map(class_declaration, |x| {
            PackageOrGenerateItemDeclaration::ClassDeclaration(x)
        }),
        map(class_constructor_declaration, |x| {
            PackageOrGenerateItemDeclaration::ClassConstructorDeclaration(x)
        }),
        map(pair(local_parameter_declaration, symbol(";")), |x| {
            PackageOrGenerateItemDeclaration::LocalParameterDeclaration(x)
        }),
        map(pair(parameter_declaration, symbol(";")), |x| {
            PackageOrGenerateItemDeclaration::ParameterDeclaration(x)
        }),
        map(covergroup_declaration, |x| {
            PackageOrGenerateItemDeclaration::CovergroupDeclaration(x)
        }),
        map(assertion_item_declaration, |x| {
            PackageOrGenerateItemDeclaration::AssertionItemDeclaration(x)
        }),
        map(symbol(";"), |x| PackageOrGenerateItemDeclaration::Empty(x)),
    ))(s)
}

#[parser]
pub fn anonymous_program(s: Span) -> IResult<Span, AnonymousProgram> {
    let (s, a) = keyword("program")(s)?;
    let (s, b) = symbol(";")(s)?;
    let (s, c) = many0(anonymous_program_item)(s)?;
    let (s, d) = keyword("endprogram")(s)?;
    Ok((
        s,
        AnonymousProgram {
            nodes: (a, b, c, d),
        },
    ))
}

#[parser]
pub fn anonymous_program_item(s: Span) -> IResult<Span, AnonymousProgramItem> {
    alt((
        map(task_declaration, |x| {
            AnonymousProgramItem::TaskDeclaration(x)
        }),
        map(function_declaration, |x| {
            AnonymousProgramItem::FunctionDeclaration(x)
        }),
        map(class_declaration, |x| {
            AnonymousProgramItem::ClassDeclaration(x)
        }),
        map(covergroup_declaration, |x| {
            AnonymousProgramItem::CovergroupDeclaration(x)
        }),
        map(class_constructor_declaration, |x| {
            AnonymousProgramItem::ClassConstructorDeclaration(x)
        }),
        map(symbol(";"), |x| AnonymousProgramItem::Empty(x)),
    ))(s)
}

use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum PackageItem<'a> {
    PackageOrGenerateItemDeclaration(PackageOrGenerateItemDeclaration<'a>),
    AnonymousProgram(AnonymousProgram<'a>),
    PackageExportDeclaration(PackageExportDeclaration<'a>),
    TimeunitsDeclaration(TimeunitsDeclaration<'a>),
}

#[derive(Debug, Node)]
pub enum PackageOrGenerateItemDeclaration<'a> {
    NetDeclaration(NetDeclaration<'a>),
    DataDeclaration(DataDeclaration<'a>),
    TaskDeclaration(TaskDeclaration<'a>),
    FunctionDeclaration(FunctionDeclaration<'a>),
    CheckerDeclaration(CheckerDeclaration<'a>),
    DpiImportExport(DpiImportExport<'a>),
    ExternConstraintDeclaration(ExternConstraintDeclaration<'a>),
    ClassDeclaration(ClassDeclaration<'a>),
    ClassConstructorDeclaration(ClassConstructorDeclaration<'a>),
    LocalParameterDeclaration((LocalParameterDeclaration<'a>, Symbol<'a>)),
    ParameterDeclaration((ParameterDeclaration<'a>, Symbol<'a>)),
    CovergroupDeclaration(CovergroupDeclaration<'a>),
    AssertionItemDeclaration(AssertionItemDeclaration<'a>),
    Empty(Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct AnonymousProgram<'a> {
    pub nodes: (
        Symbol<'a>,
        Symbol<'a>,
        Vec<AnonymousProgramItem<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum AnonymousProgramItem<'a> {
    TaskDeclaration(TaskDeclaration<'a>),
    FunctionDeclaration(FunctionDeclaration<'a>),
    ClassDeclaration(ClassDeclaration<'a>),
    CovergroupDeclaration(CovergroupDeclaration<'a>),
    ClassConstructorDeclaration(ClassConstructorDeclaration<'a>),
    Empty(Symbol<'a>),
}

// -----------------------------------------------------------------------------

#[trace]
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

#[trace]
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

#[trace]
pub fn anonymous_program(s: Span) -> IResult<Span, AnonymousProgram> {
    let (s, a) = symbol("program")(s)?;
    let (s, b) = symbol(";")(s)?;
    let (s, c) = many0(anonymous_program_item)(s)?;
    let (s, d) = symbol("endprogram")(s)?;
    Ok((
        s,
        AnonymousProgram {
            nodes: (a, b, c, d),
        },
    ))
}

#[trace]
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

use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct ConfigDeclaration<'a> {
    pub nodes: (
        Symbol<'a>,
        ConfigIdentifier<'a>,
        Symbol<'a>,
        Vec<(LocalParameterDeclaration<'a>, Symbol<'a>)>,
        DesignStatement<'a>,
        Vec<ConfigRuleStatement<'a>>,
        Symbol<'a>,
        Option<(Symbol<'a>, ConfigIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct DesignStatement<'a> {
    pub nodes: (
        Symbol<'a>,
        Vec<(
            Option<(LibraryIdentifier<'a>, Symbol<'a>)>,
            CellIdentifier<'a>,
        )>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum ConfigRuleStatement<'a> {
    Default(ConfigRuleStatementDefault<'a>),
    InstLib(ConfigRuleStatementInstLib<'a>),
    InstUse(ConfigRuleStatementInstUse<'a>),
    CellLib(ConfigRuleStatementCellLib<'a>),
    CellUse(ConfigRuleStatementCellUse<'a>),
}

#[derive(Debug, Node)]
pub struct ConfigRuleStatementDefault<'a> {
    pub nodes: (DefaultClause<'a>, LiblistClause<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct ConfigRuleStatementInstLib<'a> {
    pub nodes: (InstClause<'a>, LiblistClause<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct ConfigRuleStatementInstUse<'a> {
    pub nodes: (InstClause<'a>, UseClause<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct ConfigRuleStatementCellLib<'a> {
    pub nodes: (CellClause<'a>, LiblistClause<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct ConfigRuleStatementCellUse<'a> {
    pub nodes: (CellClause<'a>, UseClause<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct DefaultClause<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug, Node)]
pub struct InstClause<'a> {
    pub nodes: (Symbol<'a>, InstName<'a>),
}

#[derive(Debug, Node)]
pub struct InstName<'a> {
    pub nodes: (
        TopmoduleIdentifier<'a>,
        Vec<(Symbol<'a>, InstanceIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct CellClause<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<(LibraryIdentifier<'a>, Symbol<'a>)>,
        CellIdentifier<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct LiblistClause<'a> {
    pub nodes: (Symbol<'a>, Vec<LibraryIdentifier<'a>>),
}

#[derive(Debug, Node)]
pub enum UseClause<'a> {
    Cell(UseClauseCell<'a>),
    Named(UseClauseNamed<'a>),
    CellNamed(UseClauseCellNamed<'a>),
}

#[derive(Debug, Node)]
pub struct UseClauseCell<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<(LibraryIdentifier<'a>, Symbol<'a>)>,
        CellIdentifier<'a>,
        Option<(Symbol<'a>, Config<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct UseClauseNamed<'a> {
    pub nodes: (
        Symbol<'a>,
        List<Symbol<'a>, NamedParameterAssignment<'a>>,
        Option<(Symbol<'a>, Config<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct UseClauseCellNamed<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<(LibraryIdentifier<'a>, Symbol<'a>)>,
        CellIdentifier<'a>,
        List<Symbol<'a>, NamedParameterAssignment<'a>>,
        Option<(Symbol<'a>, Config<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct Config<'a> {
    pub nodes: (Symbol<'a>,),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn config_declaration(s: Span) -> IResult<Span, ConfigDeclaration> {
    let (s, a) = symbol("config")(s)?;
    let (s, b) = config_identifier(s)?;
    let (s, c) = symbol(";")(s)?;
    let (s, d) = many0(pair(local_parameter_declaration, symbol(";")))(s)?;
    let (s, e) = design_statement(s)?;
    let (s, f) = many0(config_rule_statement)(s)?;
    let (s, g) = symbol("endconfig")(s)?;
    let (s, h) = opt(pair(symbol(":"), config_identifier))(s)?;
    Ok((
        s,
        ConfigDeclaration {
            nodes: (a, b, c, d, e, f, g, h),
        },
    ))
}

#[parser]
pub fn design_statement(s: Span) -> IResult<Span, DesignStatement> {
    let (s, a) = symbol("design")(s)?;
    let (s, b) = many0(pair(
        opt(pair(library_identifier, symbol("."))),
        cell_identifier,
    ))(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((s, DesignStatement { nodes: (a, b, c) }))
}

#[parser]
pub fn config_rule_statement(s: Span) -> IResult<Span, ConfigRuleStatement> {
    alt((
        config_rule_statement_default,
        config_rule_statement_inst_lib,
        config_rule_statement_inst_use,
        config_rule_statement_cell_lib,
        config_rule_statement_cell_use,
    ))(s)
}

#[parser]
pub fn config_rule_statement_default(s: Span) -> IResult<Span, ConfigRuleStatement> {
    let (s, a) = default_clause(s)?;
    let (s, b) = liblist_clause(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ConfigRuleStatement::Default(ConfigRuleStatementDefault { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn config_rule_statement_inst_lib(s: Span) -> IResult<Span, ConfigRuleStatement> {
    let (s, a) = inst_clause(s)?;
    let (s, b) = liblist_clause(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ConfigRuleStatement::InstLib(ConfigRuleStatementInstLib { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn config_rule_statement_inst_use(s: Span) -> IResult<Span, ConfigRuleStatement> {
    let (s, a) = inst_clause(s)?;
    let (s, b) = use_clause(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ConfigRuleStatement::InstUse(ConfigRuleStatementInstUse { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn config_rule_statement_cell_lib(s: Span) -> IResult<Span, ConfigRuleStatement> {
    let (s, a) = cell_clause(s)?;
    let (s, b) = liblist_clause(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ConfigRuleStatement::CellLib(ConfigRuleStatementCellLib { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn config_rule_statement_cell_use(s: Span) -> IResult<Span, ConfigRuleStatement> {
    let (s, a) = cell_clause(s)?;
    let (s, b) = use_clause(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ConfigRuleStatement::CellUse(ConfigRuleStatementCellUse { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn default_clause(s: Span) -> IResult<Span, DefaultClause> {
    let (s, a) = symbol("default")(s)?;
    Ok((s, DefaultClause { nodes: (a,) }))
}

#[parser]
pub fn inst_clause(s: Span) -> IResult<Span, InstClause> {
    let (s, a) = symbol("instance")(s)?;
    let (s, b) = inst_name(s)?;
    Ok((s, InstClause { nodes: (a, b) }))
}

#[parser]
pub fn inst_name(s: Span) -> IResult<Span, InstName> {
    let (s, a) = topmodule_identifier(s)?;
    let (s, b) = many0(pair(symbol("."), instance_identifier))(s)?;
    Ok((s, InstName { nodes: (a, b) }))
}

#[parser]
pub fn cell_clause(s: Span) -> IResult<Span, CellClause> {
    let (s, a) = symbol("cell")(s)?;
    let (s, b) = opt(pair(library_identifier, symbol(".")))(s)?;
    let (s, c) = cell_identifier(s)?;
    Ok((s, CellClause { nodes: (a, b, c) }))
}

#[parser]
pub fn liblist_clause(s: Span) -> IResult<Span, LiblistClause> {
    let (s, a) = symbol("liblist")(s)?;
    let (s, b) = many0(library_identifier)(s)?;
    Ok((s, LiblistClause { nodes: (a, b) }))
}

#[parser]
pub fn use_clause(s: Span) -> IResult<Span, UseClause> {
    alt((use_clause_cell, use_clause_named, use_clause_cell_named))(s)
}

#[parser]
pub fn use_clause_cell(s: Span) -> IResult<Span, UseClause> {
    let (s, a) = symbol("use")(s)?;
    let (s, b) = opt(pair(library_identifier, symbol(".")))(s)?;
    let (s, c) = cell_identifier(s)?;
    let (s, d) = opt(pair(symbol(":"), config))(s)?;
    Ok((
        s,
        UseClause::Cell(UseClauseCell {
            nodes: (a, b, c, d),
        }),
    ))
}

#[parser]
pub fn use_clause_named(s: Span) -> IResult<Span, UseClause> {
    let (s, a) = symbol("use")(s)?;
    let (s, b) = list(symbol(","), named_parameter_assignment)(s)?;
    let (s, c) = opt(pair(symbol(":"), config))(s)?;
    Ok((s, UseClause::Named(UseClauseNamed { nodes: (a, b, c) })))
}

#[parser]
pub fn use_clause_cell_named(s: Span) -> IResult<Span, UseClause> {
    let (s, a) = symbol("use")(s)?;
    let (s, b) = opt(pair(library_identifier, symbol(".")))(s)?;
    let (s, c) = cell_identifier(s)?;
    let (s, d) = list(symbol(","), named_parameter_assignment)(s)?;
    let (s, e) = opt(pair(symbol(":"), config))(s)?;
    Ok((
        s,
        UseClause::CellNamed(UseClauseCellNamed {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[parser]
pub fn config(s: Span) -> IResult<Span, Config> {
    let (s, a) = symbol("config")(s)?;
    Ok((s, Config { nodes: (a,) }))
}

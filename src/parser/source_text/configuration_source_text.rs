use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct ConfigDeclaration {
    pub nodes: (
        Keyword,
        ConfigIdentifier,
        Symbol,
        Vec<(LocalParameterDeclaration, Symbol)>,
        DesignStatement,
        Vec<ConfigRuleStatement>,
        Keyword,
        Option<(Symbol, ConfigIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct DesignStatement {
    pub nodes: (
        Keyword,
        Vec<(Option<(LibraryIdentifier, Symbol)>, CellIdentifier)>,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum ConfigRuleStatement {
    Default(Box<ConfigRuleStatementDefault>),
    InstLib(Box<ConfigRuleStatementInstLib>),
    InstUse(Box<ConfigRuleStatementInstUse>),
    CellLib(Box<ConfigRuleStatementCellLib>),
    CellUse(Box<ConfigRuleStatementCellUse>),
}

#[derive(Clone, Debug, Node)]
pub struct ConfigRuleStatementDefault {
    pub nodes: (DefaultClause, LiblistClause, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct ConfigRuleStatementInstLib {
    pub nodes: (InstClause, LiblistClause, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct ConfigRuleStatementInstUse {
    pub nodes: (InstClause, UseClause, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct ConfigRuleStatementCellLib {
    pub nodes: (CellClause, LiblistClause, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct ConfigRuleStatementCellUse {
    pub nodes: (CellClause, UseClause, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct DefaultClause {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, Node)]
pub struct InstClause {
    pub nodes: (Keyword, InstName),
}

#[derive(Clone, Debug, Node)]
pub struct InstName {
    pub nodes: (TopmoduleIdentifier, Vec<(Symbol, InstanceIdentifier)>),
}

#[derive(Clone, Debug, Node)]
pub struct CellClause {
    pub nodes: (Keyword, Option<(LibraryIdentifier, Symbol)>, CellIdentifier),
}

#[derive(Clone, Debug, Node)]
pub struct LiblistClause {
    pub nodes: (Keyword, Vec<LibraryIdentifier>),
}

#[derive(Clone, Debug, Node)]
pub enum UseClause {
    Cell(Box<UseClauseCell>),
    Named(Box<UseClauseNamed>),
    CellNamed(Box<UseClauseCellNamed>),
}

#[derive(Clone, Debug, Node)]
pub struct UseClauseCell {
    pub nodes: (
        Keyword,
        Option<(LibraryIdentifier, Symbol)>,
        CellIdentifier,
        Option<(Symbol, Config)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct UseClauseNamed {
    pub nodes: (
        Keyword,
        List<Symbol, NamedParameterAssignment>,
        Option<(Symbol, Config)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct UseClauseCellNamed {
    pub nodes: (
        Keyword,
        Option<(LibraryIdentifier, Symbol)>,
        CellIdentifier,
        List<Symbol, NamedParameterAssignment>,
        Option<(Symbol, Config)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct Config {
    pub nodes: (Keyword,),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn config_declaration(s: Span) -> IResult<Span, ConfigDeclaration> {
    let (s, a) = keyword("config")(s)?;
    let (s, b) = config_identifier(s)?;
    let (s, c) = symbol(";")(s)?;
    let (s, d) = many0(pair(local_parameter_declaration, symbol(";")))(s)?;
    let (s, e) = design_statement(s)?;
    let (s, f) = many0(config_rule_statement)(s)?;
    let (s, g) = keyword("endconfig")(s)?;
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
    let (s, a) = keyword("design")(s)?;
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
        ConfigRuleStatement::Default(Box::new(ConfigRuleStatementDefault { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn config_rule_statement_inst_lib(s: Span) -> IResult<Span, ConfigRuleStatement> {
    let (s, a) = inst_clause(s)?;
    let (s, b) = liblist_clause(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ConfigRuleStatement::InstLib(Box::new(ConfigRuleStatementInstLib { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn config_rule_statement_inst_use(s: Span) -> IResult<Span, ConfigRuleStatement> {
    let (s, a) = inst_clause(s)?;
    let (s, b) = use_clause(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ConfigRuleStatement::InstUse(Box::new(ConfigRuleStatementInstUse { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn config_rule_statement_cell_lib(s: Span) -> IResult<Span, ConfigRuleStatement> {
    let (s, a) = cell_clause(s)?;
    let (s, b) = liblist_clause(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ConfigRuleStatement::CellLib(Box::new(ConfigRuleStatementCellLib { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn config_rule_statement_cell_use(s: Span) -> IResult<Span, ConfigRuleStatement> {
    let (s, a) = cell_clause(s)?;
    let (s, b) = use_clause(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ConfigRuleStatement::CellUse(Box::new(ConfigRuleStatementCellUse { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn default_clause(s: Span) -> IResult<Span, DefaultClause> {
    let (s, a) = keyword("default")(s)?;
    Ok((s, DefaultClause { nodes: (a,) }))
}

#[parser]
pub fn inst_clause(s: Span) -> IResult<Span, InstClause> {
    let (s, a) = keyword("instance")(s)?;
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
    let (s, a) = keyword("cell")(s)?;
    let (s, b) = opt(pair(library_identifier, symbol(".")))(s)?;
    let (s, c) = cell_identifier(s)?;
    Ok((s, CellClause { nodes: (a, b, c) }))
}

#[parser]
pub fn liblist_clause(s: Span) -> IResult<Span, LiblistClause> {
    let (s, a) = keyword("liblist")(s)?;
    let (s, b) = many0(library_identifier)(s)?;
    Ok((s, LiblistClause { nodes: (a, b) }))
}

#[parser]
pub fn use_clause(s: Span) -> IResult<Span, UseClause> {
    alt((use_clause_cell, use_clause_named, use_clause_cell_named))(s)
}

#[parser]
pub fn use_clause_cell(s: Span) -> IResult<Span, UseClause> {
    let (s, a) = keyword("use")(s)?;
    let (s, b) = opt(pair(library_identifier, symbol(".")))(s)?;
    let (s, c) = cell_identifier(s)?;
    let (s, d) = opt(pair(symbol(":"), config))(s)?;
    Ok((
        s,
        UseClause::Cell(Box::new(UseClauseCell {
            nodes: (a, b, c, d),
        })),
    ))
}

#[parser]
pub fn use_clause_named(s: Span) -> IResult<Span, UseClause> {
    let (s, a) = keyword("use")(s)?;
    let (s, b) = list(symbol(","), named_parameter_assignment)(s)?;
    let (s, c) = opt(pair(symbol(":"), config))(s)?;
    Ok((
        s,
        UseClause::Named(Box::new(UseClauseNamed { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn use_clause_cell_named(s: Span) -> IResult<Span, UseClause> {
    let (s, a) = keyword("use")(s)?;
    let (s, b) = opt(pair(library_identifier, symbol(".")))(s)?;
    let (s, c) = cell_identifier(s)?;
    let (s, d) = list(symbol(","), named_parameter_assignment)(s)?;
    let (s, e) = opt(pair(symbol(":"), config))(s)?;
    Ok((
        s,
        UseClause::CellNamed(Box::new(UseClauseCellNamed {
            nodes: (a, b, c, d, e),
        })),
    ))
}

#[parser]
pub fn config(s: Span) -> IResult<Span, Config> {
    let (s, a) = keyword("config")(s)?;
    Ok((s, Config { nodes: (a,) }))
}

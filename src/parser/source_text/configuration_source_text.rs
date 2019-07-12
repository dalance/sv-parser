use crate::ast::*;
use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct ConfigDeclaration<'a> {
    pub nodes: (
        ConfigIdentifier<'a>,
        Vec<LocalParameterDeclaration<'a>>,
        DesignStatement<'a>,
        Vec<ConfigRuleStatement<'a>>,
        Option<ConfigIdentifier<'a>>,
    ),
}

#[derive(Debug, Node)]
pub struct DesignStatement<'a> {
    pub nodes: (Vec<(Option<LibraryIdentifier<'a>>, CellIdentifier<'a>)>,),
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
    pub nodes: (DefaultClause<'a>, LiblistClause<'a>),
}

#[derive(Debug, Node)]
pub struct ConfigRuleStatementInstLib<'a> {
    pub nodes: (InstClause<'a>, LiblistClause<'a>),
}

#[derive(Debug, Node)]
pub struct ConfigRuleStatementInstUse<'a> {
    pub nodes: (InstClause<'a>, UseClause<'a>),
}

#[derive(Debug, Node)]
pub struct ConfigRuleStatementCellLib<'a> {
    pub nodes: (CellClause<'a>, LiblistClause<'a>),
}

#[derive(Debug, Node)]
pub struct ConfigRuleStatementCellUse<'a> {
    pub nodes: (CellClause<'a>, UseClause<'a>),
}

#[derive(Debug, Node)]
pub struct DefaultClause<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug, Node)]
pub struct InstClause<'a> {
    pub nodes: (InstName<'a>,),
}

#[derive(Debug, Node)]
pub struct InstName<'a> {
    pub nodes: (TopmoduleIdentifier<'a>, Vec<InstanceIdentifier<'a>>),
}

#[derive(Debug, Node)]
pub struct CellClause<'a> {
    pub nodes: (Option<LibraryIdentifier<'a>>, CellIdentifier<'a>),
}

#[derive(Debug, Node)]
pub struct LiblistClause<'a> {
    pub nodes: (Vec<LibraryIdentifier<'a>>,),
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
        Option<LibraryIdentifier<'a>>,
        CellIdentifier<'a>,
        Option<Config<'a>>,
    ),
}

#[derive(Debug, Node)]
pub struct UseClauseNamed<'a> {
    pub nodes: (Vec<NamedParameterAssignment<'a>>, Option<Config<'a>>),
}

#[derive(Debug, Node)]
pub struct UseClauseCellNamed<'a> {
    pub nodes: (
        Option<LibraryIdentifier<'a>>,
        CellIdentifier<'a>,
        Vec<NamedParameterAssignment<'a>>,
        Option<Config<'a>>,
    ),
}

#[derive(Debug, Node)]
pub struct Config<'a> {
    pub nodes: (Symbol<'a>,),
}

// -----------------------------------------------------------------------------

pub fn config_declaration(s: Span) -> IResult<Span, ConfigDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn design_statement(s: Span) -> IResult<Span, DesignStatement> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn config_rule_statement(s: Span) -> IResult<Span, ConfigRuleStatement> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn default_clause(s: Span) -> IResult<Span, DefaultClause> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn inst_clause(s: Span) -> IResult<Span, InstClause> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn inst_name(s: Span) -> IResult<Span, InstName> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn cell_clause(s: Span) -> IResult<Span, CellClause> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn liblist_clause(s: Span) -> IResult<Span, LiblistClause> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn use_clause(s: Span) -> IResult<Span, UseClause> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

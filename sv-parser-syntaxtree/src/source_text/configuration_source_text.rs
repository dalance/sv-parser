use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
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

#[derive(Clone, Debug, PartialEq, Node)]
pub struct DesignStatement {
    pub nodes: (
        Keyword,
        Vec<(Option<(LibraryIdentifier, Symbol)>, CellIdentifier)>,
        Symbol,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ConfigRuleStatement {
    Default(Box<ConfigRuleStatementDefault>),
    InstLib(Box<ConfigRuleStatementInstLib>),
    InstUse(Box<ConfigRuleStatementInstUse>),
    CellLib(Box<ConfigRuleStatementCellLib>),
    CellUse(Box<ConfigRuleStatementCellUse>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ConfigRuleStatementDefault {
    pub nodes: (DefaultClause, LiblistClause, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ConfigRuleStatementInstLib {
    pub nodes: (InstClause, LiblistClause, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ConfigRuleStatementInstUse {
    pub nodes: (InstClause, UseClause, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ConfigRuleStatementCellLib {
    pub nodes: (CellClause, LiblistClause, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ConfigRuleStatementCellUse {
    pub nodes: (CellClause, UseClause, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct DefaultClause {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct InstClause {
    pub nodes: (Keyword, InstName),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct InstName {
    pub nodes: (TopmoduleIdentifier, Vec<(Symbol, InstanceIdentifier)>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CellClause {
    pub nodes: (Keyword, Option<(LibraryIdentifier, Symbol)>, CellIdentifier),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct LiblistClause {
    pub nodes: (Keyword, Vec<LibraryIdentifier>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum UseClause {
    Cell(Box<UseClauseCell>),
    Named(Box<UseClauseNamed>),
    CellNamed(Box<UseClauseCellNamed>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct UseClauseCell {
    pub nodes: (
        Keyword,
        Option<(LibraryIdentifier, Symbol)>,
        CellIdentifier,
        Option<(Symbol, Config)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct UseClauseNamed {
    pub nodes: (
        Keyword,
        List<Symbol, NamedParameterAssignment>,
        Option<(Symbol, Config)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct UseClauseCellNamed {
    pub nodes: (
        Keyword,
        Option<(LibraryIdentifier, Symbol)>,
        CellIdentifier,
        List<Symbol, NamedParameterAssignment>,
        Option<(Symbol, Config)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct Config {
    pub nodes: (Keyword,),
}

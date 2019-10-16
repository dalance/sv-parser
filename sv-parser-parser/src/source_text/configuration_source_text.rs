use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
#[packrat_parser]
pub(crate) fn config_declaration(s: Span) -> IResult<Span, ConfigDeclaration> {
    let (s, a) = context("config", keyword("config"))(s)?;
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

#[tracable_parser]
#[packrat_parser]
pub(crate) fn design_statement(s: Span) -> IResult<Span, DesignStatement> {
    let (s, a) = keyword("design")(s)?;
    let (s, b) = many0(pair(
        opt(pair(library_identifier, symbol("."))),
        cell_identifier,
    ))(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((s, DesignStatement { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn config_rule_statement(s: Span) -> IResult<Span, ConfigRuleStatement> {
    alt((
        config_rule_statement_default,
        config_rule_statement_inst_lib,
        config_rule_statement_inst_use,
        config_rule_statement_cell_lib,
        config_rule_statement_cell_use,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn config_rule_statement_default(s: Span) -> IResult<Span, ConfigRuleStatement> {
    let (s, a) = default_clause(s)?;
    let (s, b) = liblist_clause(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ConfigRuleStatement::Default(Box::new(ConfigRuleStatementDefault { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn config_rule_statement_inst_lib(s: Span) -> IResult<Span, ConfigRuleStatement> {
    let (s, a) = inst_clause(s)?;
    let (s, b) = liblist_clause(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ConfigRuleStatement::InstLib(Box::new(ConfigRuleStatementInstLib { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn config_rule_statement_inst_use(s: Span) -> IResult<Span, ConfigRuleStatement> {
    let (s, a) = inst_clause(s)?;
    let (s, b) = use_clause(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ConfigRuleStatement::InstUse(Box::new(ConfigRuleStatementInstUse { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn config_rule_statement_cell_lib(s: Span) -> IResult<Span, ConfigRuleStatement> {
    let (s, a) = cell_clause(s)?;
    let (s, b) = liblist_clause(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ConfigRuleStatement::CellLib(Box::new(ConfigRuleStatementCellLib { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn config_rule_statement_cell_use(s: Span) -> IResult<Span, ConfigRuleStatement> {
    let (s, a) = cell_clause(s)?;
    let (s, b) = use_clause(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ConfigRuleStatement::CellUse(Box::new(ConfigRuleStatementCellUse { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn default_clause(s: Span) -> IResult<Span, DefaultClause> {
    let (s, a) = keyword("default")(s)?;
    Ok((s, DefaultClause { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn inst_clause(s: Span) -> IResult<Span, InstClause> {
    let (s, a) = keyword("instance")(s)?;
    let (s, b) = inst_name(s)?;
    Ok((s, InstClause { nodes: (a, b) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn inst_name(s: Span) -> IResult<Span, InstName> {
    let (s, a) = topmodule_identifier(s)?;
    let (s, b) = many0(pair(symbol("."), instance_identifier))(s)?;
    Ok((s, InstName { nodes: (a, b) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn cell_clause(s: Span) -> IResult<Span, CellClause> {
    let (s, a) = keyword("cell")(s)?;
    let (s, b) = opt(pair(library_identifier, symbol(".")))(s)?;
    let (s, c) = cell_identifier(s)?;
    Ok((s, CellClause { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn liblist_clause(s: Span) -> IResult<Span, LiblistClause> {
    let (s, a) = keyword("liblist")(s)?;
    let (s, b) = many0(library_identifier)(s)?;
    Ok((s, LiblistClause { nodes: (a, b) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn use_clause(s: Span) -> IResult<Span, UseClause> {
    alt((use_clause_cell, use_clause_named, use_clause_cell_named))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn use_clause_cell(s: Span) -> IResult<Span, UseClause> {
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

#[tracable_parser]
#[packrat_parser]
pub(crate) fn use_clause_named(s: Span) -> IResult<Span, UseClause> {
    let (s, a) = keyword("use")(s)?;
    let (s, b) = list(symbol(","), named_parameter_assignment)(s)?;
    let (s, c) = opt(pair(symbol(":"), config))(s)?;
    Ok((
        s,
        UseClause::Named(Box::new(UseClauseNamed { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn use_clause_cell_named(s: Span) -> IResult<Span, UseClause> {
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

#[tracable_parser]
#[packrat_parser]
pub(crate) fn config(s: Span) -> IResult<Span, Config> {
    let (s, a) = keyword("config")(s)?;
    Ok((s, Config { nodes: (a,) }))
}

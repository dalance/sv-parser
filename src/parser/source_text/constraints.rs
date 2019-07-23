use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct ConstraintDeclaration {
    pub nodes: (
        Option<Static>,
        Keyword,
        ConstraintIdentifier,
        ConstraintBlock,
    ),
}

#[derive(Debug, Node)]
pub struct Static {
    pub nodes: (Keyword,),
}

#[derive(Debug, Node)]
pub struct ConstraintBlock {
    pub nodes: (Brace< Vec<ConstraintBlockItem>>,),
}

#[derive(Debug, Node)]
pub enum ConstraintBlockItem {
    Solve(ConstraintBlockItemSolve),
    ConstraintExpression(ConstraintExpression),
}

#[derive(Debug, Node)]
pub struct ConstraintBlockItemSolve {
    pub nodes: (
        Keyword,
        SolveBeforeList,
        Keyword,
        SolveBeforeList,
        Symbol,
    ),
}

#[derive(Debug, Node)]
pub struct SolveBeforeList {
    pub nodes: (List<Symbol, ConstraintPrimary>,),
}

#[derive(Debug, Node)]
pub struct ConstraintPrimary {
    pub nodes: (
        Option<ImplicitClassHandleOrClassScope>,
        HierarchicalIdentifier,
        Select,
    ),
}

#[derive(Debug, Node)]
pub enum ConstraintExpression {
    Expression(ConstraintExpressionExpression),
    UniquenessConstraint((UniquenessConstraint, Symbol)),
    Arrow(ConstraintExpressionArrow),
    If(ConstraintExpressionIf),
    Foreach(ConstraintExpressionForeach),
    Disable(ConstraintExpressionDisable),
}

#[derive(Debug, Node)]
pub struct ConstraintExpressionExpression {
    pub nodes: (Option<Soft>, ExpressionOrDist, Symbol),
}

#[derive(Debug, Node)]
pub struct Soft {
    pub nodes: (Keyword,),
}

#[derive(Debug, Node)]
pub struct ConstraintExpressionArrow {
    pub nodes: (Expression, Symbol, ConstraintSet),
}

#[derive(Debug, Node)]
pub struct ConstraintExpressionIf {
    pub nodes: (
        Keyword,
        Paren< Expression>,
        ConstraintSet,
        Option<(Keyword, ConstraintSet)>,
    ),
}

#[derive(Debug, Node)]
pub struct ConstraintExpressionForeach {
    pub nodes: (
        Keyword,
        Paren<
            
            (
                PsOrHierarchicalArrayIdentifier,
                Bracket< LoopVariables>,
            ),
        >,
        ConstraintSet,
    ),
}

#[derive(Debug, Node)]
pub struct ConstraintExpressionDisable {
    pub nodes: (Keyword, Keyword, ConstraintPrimary, Symbol),
}

#[derive(Debug, Node)]
pub struct UniquenessConstraint {
    pub nodes: (Keyword, Brace< OpenRangeList>),
}

#[derive(Debug, Node)]
pub enum ConstraintSet {
    ConstraintExpression(Box<ConstraintExpression>),
    Brace(ConstraintSetBrace),
}

#[derive(Debug, Node)]
pub struct ConstraintSetBrace {
    pub nodes: (Brace< Vec<ConstraintExpression>>,),
}

#[derive(Debug, Node)]
pub struct DistList {
    pub nodes: (List<Symbol, DistItem>,),
}

#[derive(Debug, Node)]
pub struct DistItem {
    pub nodes: (ValueRange, Option<DistWeight>),
}

#[derive(Debug, Node)]
pub enum DistWeight {
    Equal(DistWeightEqual),
    Divide(DistWeightDivide),
}

#[derive(Debug, Node)]
pub struct DistWeightEqual {
    pub nodes: (Symbol, Expression),
}

#[derive(Debug, Node)]
pub struct DistWeightDivide {
    pub nodes: (Symbol, Expression),
}

#[derive(Debug, Node)]
pub struct ConstraintPrototype {
    pub nodes: (
        Option<ConstraintPrototypeQualifier>,
        Option<Static>,
        Keyword,
        ConstraintIdentifier,
        Symbol,
    ),
}

#[derive(Debug, Node)]
pub enum ConstraintPrototypeQualifier {
    Extern(Keyword),
    Pure(Keyword),
}

#[derive(Debug, Node)]
pub struct ExternConstraintDeclaration {
    pub nodes: (
        Option<Static>,
        Keyword,
        ClassScope,
        ConstraintIdentifier,
        ConstraintBlock,
    ),
}

#[derive(Debug, Node)]
pub struct IdentifierList {
    pub nodes: (List<Symbol, Identifier>,),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn constraint_declaration(s: Span) -> IResult<Span, ConstraintDeclaration> {
    let (s, a) = opt(r#static)(s)?;
    let (s, b) = keyword("constraint")(s)?;
    let (s, c) = constraint_identifier(s)?;
    let (s, d) = constraint_block(s)?;
    Ok((
        s,
        ConstraintDeclaration {
            nodes: (a, b, c, d),
        },
    ))
}

#[parser]
pub fn r#static(s: Span) -> IResult<Span, Static> {
    let (s, a) = keyword("static")(s)?;
    Ok((s, Static { nodes: (a,) }))
}

#[parser]
pub fn constraint_block(s: Span) -> IResult<Span, ConstraintBlock> {
    let (s, a) = brace(many0(constraint_block_item))(s)?;
    Ok((s, ConstraintBlock { nodes: (a,) }))
}

#[parser]
pub fn constraint_block_item(s: Span) -> IResult<Span, ConstraintBlockItem> {
    alt((
        constraint_block_item_solve,
        map(constraint_expression, |x| {
            ConstraintBlockItem::ConstraintExpression(x)
        }),
    ))(s)
}

#[parser]
pub fn constraint_block_item_solve(s: Span) -> IResult<Span, ConstraintBlockItem> {
    let (s, a) = keyword("solve")(s)?;
    let (s, b) = solve_before_list(s)?;
    let (s, c) = keyword("before")(s)?;
    let (s, d) = solve_before_list(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        ConstraintBlockItem::Solve(ConstraintBlockItemSolve {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[parser]
pub fn solve_before_list(s: Span) -> IResult<Span, SolveBeforeList> {
    let (s, a) = list(symbol(","), constraint_primary)(s)?;
    Ok((s, SolveBeforeList { nodes: (a,) }))
}

#[parser]
pub fn constraint_primary(s: Span) -> IResult<Span, ConstraintPrimary> {
    let (s, a) = opt(implicit_class_handle_or_class_scope)(s)?;
    let (s, b) = hierarchical_identifier(s)?;
    let (s, c) = select(s)?;
    Ok((s, ConstraintPrimary { nodes: (a, b, c) }))
}

#[parser]
pub fn constraint_expression(s: Span) -> IResult<Span, ConstraintExpression> {
    alt((
        constraint_expression_expression,
        map(pair(uniqueness_constraint, symbol(";")), |x| {
            ConstraintExpression::UniquenessConstraint(x)
        }),
        constraint_expression_arrow,
        constraint_expression_if,
        constraint_expression_foreach,
        constraint_expression_disable,
    ))(s)
}

#[parser(MaybeRecursive)]
pub fn constraint_expression_expression(s: Span) -> IResult<Span, ConstraintExpression> {
    let (s, a) = opt(soft)(s)?;
    let (s, b) = expression_or_dist(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ConstraintExpression::Expression(ConstraintExpressionExpression { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn soft(s: Span) -> IResult<Span, Soft> {
    let (s, a) = keyword("soft")(s)?;
    Ok((s, Soft { nodes: (a,) }))
}

#[parser(MaybeRecursive)]
pub fn constraint_expression_arrow(s: Span) -> IResult<Span, ConstraintExpression> {
    let (s, a) = expression(s)?;
    let (s, b) = symbol("->")(s)?;
    let (s, c) = constraint_set(s)?;
    Ok((
        s,
        ConstraintExpression::Arrow(ConstraintExpressionArrow { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn constraint_expression_if(s: Span) -> IResult<Span, ConstraintExpression> {
    let (s, a) = keyword("if")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = constraint_set(s)?;
    let (s, d) = opt(pair(keyword("else"), constraint_set))(s)?;
    Ok((
        s,
        ConstraintExpression::If(ConstraintExpressionIf {
            nodes: (a, b, c, d),
        }),
    ))
}

#[parser]
pub fn constraint_expression_foreach(s: Span) -> IResult<Span, ConstraintExpression> {
    let (s, a) = keyword("foreach")(s)?;
    let (s, b) = paren(pair(
        ps_or_hierarchical_array_identifier,
        bracket(loop_variables),
    ))(s)?;
    let (s, c) = constraint_set(s)?;
    Ok((
        s,
        ConstraintExpression::Foreach(ConstraintExpressionForeach { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn constraint_expression_disable(s: Span) -> IResult<Span, ConstraintExpression> {
    let (s, a) = keyword("disable")(s)?;
    let (s, b) = keyword("soft")(s)?;
    let (s, c) = constraint_primary(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        ConstraintExpression::Disable(ConstraintExpressionDisable {
            nodes: (a, b, c, d),
        }),
    ))
}

#[parser]
pub fn uniqueness_constraint(s: Span) -> IResult<Span, UniquenessConstraint> {
    let (s, a) = keyword("unique")(s)?;
    let (s, b) = brace(open_range_list)(s)?;
    Ok((s, UniquenessConstraint { nodes: (a, b) }))
}

#[parser]
pub fn constraint_set(s: Span) -> IResult<Span, ConstraintSet> {
    alt((
        map(constraint_expression, |x| {
            ConstraintSet::ConstraintExpression(Box::new(x))
        }),
        constraint_set_brace,
    ))(s)
}

#[parser]
pub fn constraint_set_brace(s: Span) -> IResult<Span, ConstraintSet> {
    let (s, a) = brace(many0(constraint_expression))(s)?;
    Ok((s, ConstraintSet::Brace(ConstraintSetBrace { nodes: (a,) })))
}

#[parser(MaybeRecursive)]
pub fn dist_list(s: Span) -> IResult<Span, DistList> {
    let (s, a) = list(symbol(","), dist_item)(s)?;
    Ok((s, DistList { nodes: (a,) }))
}

#[parser(MaybeRecursive)]
pub fn dist_item(s: Span) -> IResult<Span, DistItem> {
    let (s, a) = value_range(s)?;
    let (s, b) = opt(dist_weight)(s)?;
    Ok((s, DistItem { nodes: (a, b) }))
}

#[parser]
pub fn dist_weight(s: Span) -> IResult<Span, DistWeight> {
    alt((dist_weight_equal, dist_weight_divide))(s)
}

#[parser]
pub fn dist_weight_equal(s: Span) -> IResult<Span, DistWeight> {
    let (s, a) = symbol(":=")(s)?;
    let (s, b) = expression(s)?;
    Ok((s, DistWeight::Equal(DistWeightEqual { nodes: (a, b) })))
}

#[parser]
pub fn dist_weight_divide(s: Span) -> IResult<Span, DistWeight> {
    let (s, a) = symbol(":/")(s)?;
    let (s, b) = expression(s)?;
    Ok((s, DistWeight::Divide(DistWeightDivide { nodes: (a, b) })))
}

#[parser]
pub fn constraint_prototype(s: Span) -> IResult<Span, ConstraintPrototype> {
    let (s, a) = opt(constraint_prototype_qualifier)(s)?;
    let (s, b) = opt(r#static)(s)?;
    let (s, c) = keyword("constraint")(s)?;
    let (s, d) = constraint_identifier(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        ConstraintPrototype {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[parser]
pub fn constraint_prototype_qualifier(s: Span) -> IResult<Span, ConstraintPrototypeQualifier> {
    alt((
        map(keyword("extern"), |x| {
            ConstraintPrototypeQualifier::Extern(x)
        }),
        map(keyword("pure"), |x| ConstraintPrototypeQualifier::Pure(x)),
    ))(s)
}

#[parser]
pub fn extern_constraint_declaration(s: Span) -> IResult<Span, ExternConstraintDeclaration> {
    let (s, a) = opt(r#static)(s)?;
    let (s, b) = keyword("constraint")(s)?;
    let (s, c) = class_scope(s)?;
    let (s, d) = constraint_identifier(s)?;
    let (s, e) = constraint_block(s)?;
    Ok((
        s,
        ExternConstraintDeclaration {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[parser]
pub fn identifier_list(s: Span) -> IResult<Span, IdentifierList> {
    let (s, a) = list(symbol(","), identifier)(s)?;
    Ok((s, IdentifierList { nodes: (a,) }))
}

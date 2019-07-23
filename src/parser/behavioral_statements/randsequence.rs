use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct RandsequenceStatement {
    pub nodes: (
        Keyword,
        Paren<Option<ProductionIdentifier>>,
        Production,
        Vec<Production>,
        Keyword,
    ),
}

#[derive(Debug, Node)]
pub struct Production {
    pub nodes: (
        Option<DataTypeOrVoid>,
        ProductionIdentifier,
        Option<Paren<TfPortList>>,
        Symbol,
        List<Symbol, RsRule>,
        Symbol,
    ),
}

#[derive(Debug, Node)]
pub struct RsRule {
    pub nodes: (
        RsProductionList,
        Option<(Symbol, WeightSpecification, Option<RsCodeBlock>)>,
    ),
}

#[derive(Debug, Node)]
pub enum RsProductionList {
    Prod(RsProductionListProd),
    Join(RsProductionListJoin),
}

#[derive(Debug, Node)]
pub struct RsProductionListProd {
    pub nodes: (RsProd, Vec<RsProd>),
}

#[derive(Debug, Node)]
pub struct RsProductionListJoin {
    pub nodes: (
        Keyword,
        Keyword,
        Option<Paren<Expression>>,
        ProductionItem,
        ProductionItem,
        Vec<ProductionItem>,
    ),
}

#[derive(Debug, Node)]
pub enum WeightSpecification {
    IntegralNumber(IntegralNumber),
    PsIdentifier(PsIdentifier),
    Expression(WeightSpecificationExpression),
}

#[derive(Debug, Node)]
pub struct WeightSpecificationExpression {
    pub nodes: (Paren<Expression>,),
}

#[derive(Debug, Node)]
pub struct RsCodeBlock {
    pub nodes: (Brace<(Vec<DataDeclaration>, Vec<StatementOrNull>)>,),
}

#[derive(Debug, Node)]
pub enum RsProd {
    ProductionItem(ProductionItem),
    RsCodeBlock(RsCodeBlock),
    RsIfElse(RsIfElse),
    RsRepeat(RsRepeat),
    RsCase(RsCase),
}

#[derive(Debug, Node)]
pub struct ProductionItem {
    pub nodes: (ProductionIdentifier, Option<Paren<ListOfArguments>>),
}

#[derive(Debug, Node)]
pub struct RsIfElse {
    pub nodes: (
        Keyword,
        Paren<Expression>,
        ProductionItem,
        Option<(Keyword, ProductionItem)>,
    ),
}

#[derive(Debug, Node)]
pub struct RsRepeat {
    pub nodes: (Keyword, Paren<Expression>, ProductionItem),
}

#[derive(Debug, Node)]
pub struct RsCase {
    pub nodes: (
        Keyword,
        Paren<CaseExpression>,
        RsCaseItem,
        Vec<RsCaseItem>,
        Keyword,
    ),
}

#[derive(Debug, Node)]
pub enum RsCaseItem {
    NonDefault(RsCaseItemNondefault),
    Default(RsCaseItemDefault),
}

#[derive(Debug, Node)]
pub struct RsCaseItemNondefault {
    pub nodes: (
        List<Symbol, CaseItemExpression>,
        Symbol,
        ProductionItem,
        Symbol,
    ),
}

#[derive(Debug, Node)]
pub struct RsCaseItemDefault {
    pub nodes: (Keyword, Option<Symbol>, ProductionItem, Symbol),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn randsequence_statement(s: Span) -> IResult<Span, RandsequenceStatement> {
    let (s, a) = keyword("randsequence")(s)?;
    let (s, b) = paren(opt(production_identifier))(s)?;
    let (s, c) = production(s)?;
    let (s, d) = many0(production)(s)?;
    let (s, e) = keyword("endsequence")(s)?;
    Ok((
        s,
        RandsequenceStatement {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[parser]
pub fn production(s: Span) -> IResult<Span, Production> {
    let (s, a) = opt(data_type_or_void)(s)?;
    let (s, b) = production_identifier(s)?;
    let (s, c) = opt(paren(tf_port_list))(s)?;
    let (s, d) = symbol(":")(s)?;
    let (s, e) = list(symbol("|"), rs_rule)(s)?;
    let (s, f) = symbol(";")(s)?;
    Ok((
        s,
        Production {
            nodes: (a, b, c, d, e, f),
        },
    ))
}

#[parser]
pub fn rs_rule(s: Span) -> IResult<Span, RsRule> {
    let (s, a) = rs_production_list(s)?;
    let (s, b) = opt(triple(
        symbol(":="),
        weight_specification,
        opt(rs_code_block),
    ))(s)?;
    Ok((s, RsRule { nodes: (a, b) }))
}

#[parser]
pub fn rs_production_list(s: Span) -> IResult<Span, RsProductionList> {
    alt((rs_production_list_prod, rs_production_list_join))(s)
}

#[parser]
pub fn rs_production_list_prod(s: Span) -> IResult<Span, RsProductionList> {
    let (s, a) = rs_prod(s)?;
    let (s, b) = many0(rs_prod)(s)?;
    Ok((
        s,
        RsProductionList::Prod(RsProductionListProd { nodes: (a, b) }),
    ))
}

#[parser]
pub fn rs_production_list_join(s: Span) -> IResult<Span, RsProductionList> {
    let (s, a) = keyword("rand")(s)?;
    let (s, b) = keyword("join")(s)?;
    let (s, c) = opt(paren(expression))(s)?;
    let (s, d) = production_item(s)?;
    let (s, e) = production_item(s)?;
    let (s, f) = many0(production_item)(s)?;
    Ok((
        s,
        RsProductionList::Join(RsProductionListJoin {
            nodes: (a, b, c, d, e, f),
        }),
    ))
}

#[parser]
pub fn weight_specification(s: Span) -> IResult<Span, WeightSpecification> {
    alt((
        map(integral_number, |x| WeightSpecification::IntegralNumber(x)),
        map(ps_identifier, |x| WeightSpecification::PsIdentifier(x)),
        weight_specification_expression,
    ))(s)
}

#[parser]
pub fn weight_specification_expression(s: Span) -> IResult<Span, WeightSpecification> {
    let (s, a) = paren(expression)(s)?;
    Ok((
        s,
        WeightSpecification::Expression(WeightSpecificationExpression { nodes: (a,) }),
    ))
}

#[parser]
pub fn rs_code_block(s: Span) -> IResult<Span, RsCodeBlock> {
    let (s, a) = brace(pair(many0(data_declaration), many0(statement_or_null)))(s)?;
    Ok((s, RsCodeBlock { nodes: (a,) }))
}

#[parser]
pub fn rs_prod(s: Span) -> IResult<Span, RsProd> {
    alt((
        map(production_item, |x| RsProd::ProductionItem(x)),
        map(rs_code_block, |x| RsProd::RsCodeBlock(x)),
        map(rs_if_else, |x| RsProd::RsIfElse(x)),
        map(rs_repeat, |x| RsProd::RsRepeat(x)),
        map(rs_case, |x| RsProd::RsCase(x)),
    ))(s)
}

#[parser]
pub fn production_item(s: Span) -> IResult<Span, ProductionItem> {
    let (s, a) = production_identifier(s)?;
    let (s, b) = opt(paren(list_of_arguments))(s)?;
    Ok((s, ProductionItem { nodes: (a, b) }))
}

#[parser]
pub fn rs_if_else(s: Span) -> IResult<Span, RsIfElse> {
    let (s, a) = keyword("if")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = production_item(s)?;
    let (s, d) = opt(pair(keyword("else"), production_item))(s)?;
    Ok((
        s,
        RsIfElse {
            nodes: (a, b, c, d),
        },
    ))
}

#[parser]
pub fn rs_repeat(s: Span) -> IResult<Span, RsRepeat> {
    let (s, a) = keyword("repeat")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = production_item(s)?;
    Ok((s, RsRepeat { nodes: (a, b, c) }))
}

#[parser]
pub fn rs_case(s: Span) -> IResult<Span, RsCase> {
    let (s, a) = keyword("case")(s)?;
    let (s, b) = paren(case_expression)(s)?;
    let (s, c) = rs_case_item(s)?;
    let (s, d) = many0(rs_case_item)(s)?;
    let (s, e) = keyword("endcase")(s)?;
    Ok((
        s,
        RsCase {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[parser]
pub fn rs_case_item(s: Span) -> IResult<Span, RsCaseItem> {
    alt((rs_case_item_nondefault, rs_case_item_default))(s)
}

#[parser(MaybeRecursive)]
pub fn rs_case_item_nondefault(s: Span) -> IResult<Span, RsCaseItem> {
    let (s, a) = list(symbol(","), case_item_expression)(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = production_item(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        RsCaseItem::NonDefault(RsCaseItemNondefault {
            nodes: (a, b, c, d),
        }),
    ))
}

#[parser]
pub fn rs_case_item_default(s: Span) -> IResult<Span, RsCaseItem> {
    let (s, a) = keyword("default")(s)?;
    let (s, b) = opt(symbol(":"))(s)?;
    let (s, c) = production_item(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        RsCaseItem::Default(RsCaseItemDefault {
            nodes: (a, b, c, d),
        }),
    ))
}

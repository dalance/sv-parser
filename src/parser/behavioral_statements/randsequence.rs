use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct RandsequenceStatement<'a> {
    pub nodes: (
        Symbol<'a>,
        Paren<'a, Option<ProductionIdentifier<'a>>>,
        Production<'a>,
        Vec<Production<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct Production<'a> {
    pub nodes: (
        Option<DataTypeOrVoid<'a>>,
        ProductionIdentifier<'a>,
        Option<Paren<'a, TfPortList<'a>>>,
        Symbol<'a>,
        List<Symbol<'a>, RsRule<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct RsRule<'a> {
    pub nodes: (
        RsProductionList<'a>,
        Option<(Symbol<'a>, WeightSpecification<'a>, Option<RsCodeBlock<'a>>)>,
    ),
}

#[derive(Debug, Node)]
pub enum RsProductionList<'a> {
    Prod(RsProductionListProd<'a>),
    Join(RsProductionListJoin<'a>),
}

#[derive(Debug, Node)]
pub struct RsProductionListProd<'a> {
    pub nodes: (RsProd<'a>, Vec<RsProd<'a>>),
}

#[derive(Debug, Node)]
pub struct RsProductionListJoin<'a> {
    pub nodes: (
        Symbol<'a>,
        Symbol<'a>,
        Option<Paren<'a, Expression<'a>>>,
        ProductionItem<'a>,
        ProductionItem<'a>,
        Vec<ProductionItem<'a>>,
    ),
}

#[derive(Debug, Node)]
pub enum WeightSpecification<'a> {
    IntegralNumber(IntegralNumber<'a>),
    PsIdentifier(PsIdentifier<'a>),
    Expression(WeightSpecificationExpression<'a>),
}

#[derive(Debug, Node)]
pub struct WeightSpecificationExpression<'a> {
    pub nodes: (Paren<'a, Expression<'a>>,),
}

#[derive(Debug, Node)]
pub struct RsCodeBlock<'a> {
    pub nodes: (Brace<'a, (Vec<DataDeclaration<'a>>, Vec<StatementOrNull<'a>>)>,),
}

#[derive(Debug, Node)]
pub enum RsProd<'a> {
    ProductionItem(ProductionItem<'a>),
    RsCodeBlock(RsCodeBlock<'a>),
    RsIfElse(RsIfElse<'a>),
    RsRepeat(RsRepeat<'a>),
    RsCase(RsCase<'a>),
}

#[derive(Debug, Node)]
pub struct ProductionItem<'a> {
    pub nodes: (
        ProductionIdentifier<'a>,
        Option<Paren<'a, ListOfArguments<'a>>>,
    ),
}

#[derive(Debug, Node)]
pub struct RsIfElse<'a> {
    pub nodes: (
        Symbol<'a>,
        Paren<'a, Expression<'a>>,
        ProductionItem<'a>,
        Option<(Symbol<'a>, ProductionItem<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct RsRepeat<'a> {
    pub nodes: (Symbol<'a>, Paren<'a, Expression<'a>>, ProductionItem<'a>),
}

#[derive(Debug, Node)]
pub struct RsCase<'a> {
    pub nodes: (
        Symbol<'a>,
        Paren<'a, CaseExpression<'a>>,
        RsCaseItem<'a>,
        Vec<RsCaseItem<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum RsCaseItem<'a> {
    NonDefault(RsCaseItemNondefault<'a>),
    Default(RsCaseItemDefault<'a>),
}

#[derive(Debug, Node)]
pub struct RsCaseItemNondefault<'a> {
    pub nodes: (
        List<Symbol<'a>, CaseItemExpression<'a>>,
        Symbol<'a>,
        ProductionItem<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct RsCaseItemDefault<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<Symbol<'a>>,
        ProductionItem<'a>,
        Symbol<'a>,
    ),
}

// -----------------------------------------------------------------------------

pub fn randsequence_statement(s: Span) -> IResult<Span, RandsequenceStatement> {
    let (s, a) = symbol("randsequence")(s)?;
    let (s, b) = paren(opt(production_identifier))(s)?;
    let (s, c) = production(s)?;
    let (s, d) = many0(production)(s)?;
    let (s, e) = symbol("endsequence")(s)?;
    Ok((
        s,
        RandsequenceStatement {
            nodes: (a, b, c, d, e),
        },
    ))
}

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

pub fn rs_rule(s: Span) -> IResult<Span, RsRule> {
    let (s, a) = rs_production_list(s)?;
    let (s, b) = opt(triple(
        symbol(":="),
        weight_specification,
        opt(rs_code_block),
    ))(s)?;
    Ok((s, RsRule { nodes: (a, b) }))
}

pub fn rs_production_list(s: Span) -> IResult<Span, RsProductionList> {
    alt((rs_production_list_prod, rs_production_list_join))(s)
}

pub fn rs_production_list_prod(s: Span) -> IResult<Span, RsProductionList> {
    let (s, a) = rs_prod(s)?;
    let (s, b) = many0(rs_prod)(s)?;
    Ok((
        s,
        RsProductionList::Prod(RsProductionListProd { nodes: (a, b) }),
    ))
}

pub fn rs_production_list_join(s: Span) -> IResult<Span, RsProductionList> {
    let (s, a) = symbol("rand")(s)?;
    let (s, b) = symbol("join")(s)?;
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

pub fn weight_specification(s: Span) -> IResult<Span, WeightSpecification> {
    alt((
        map(integral_number, |x| WeightSpecification::IntegralNumber(x)),
        map(ps_identifier, |x| WeightSpecification::PsIdentifier(x)),
        weight_specification_expression,
    ))(s)
}

pub fn weight_specification_expression(s: Span) -> IResult<Span, WeightSpecification> {
    let (s, a) = paren(expression)(s)?;
    Ok((
        s,
        WeightSpecification::Expression(WeightSpecificationExpression { nodes: (a,) }),
    ))
}

pub fn rs_code_block(s: Span) -> IResult<Span, RsCodeBlock> {
    let (s, a) = brace(pair(many0(data_declaration), many0(statement_or_null)))(s)?;
    Ok((s, RsCodeBlock { nodes: (a,) }))
}

pub fn rs_prod(s: Span) -> IResult<Span, RsProd> {
    alt((
        map(production_item, |x| RsProd::ProductionItem(x)),
        map(rs_code_block, |x| RsProd::RsCodeBlock(x)),
        map(rs_if_else, |x| RsProd::RsIfElse(x)),
        map(rs_repeat, |x| RsProd::RsRepeat(x)),
        map(rs_case, |x| RsProd::RsCase(x)),
    ))(s)
}

pub fn production_item(s: Span) -> IResult<Span, ProductionItem> {
    let (s, a) = production_identifier(s)?;
    let (s, b) = opt(paren(list_of_arguments))(s)?;
    Ok((s, ProductionItem { nodes: (a, b) }))
}

pub fn rs_if_else(s: Span) -> IResult<Span, RsIfElse> {
    let (s, a) = symbol("if")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = production_item(s)?;
    let (s, d) = opt(pair(symbol("else"), production_item))(s)?;
    Ok((
        s,
        RsIfElse {
            nodes: (a, b, c, d),
        },
    ))
}

pub fn rs_repeat(s: Span) -> IResult<Span, RsRepeat> {
    let (s, a) = symbol("repeat")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = production_item(s)?;
    Ok((s, RsRepeat { nodes: (a, b, c) }))
}

pub fn rs_case(s: Span) -> IResult<Span, RsCase> {
    let (s, a) = symbol("case")(s)?;
    let (s, b) = paren(case_expression)(s)?;
    let (s, c) = rs_case_item(s)?;
    let (s, d) = many0(rs_case_item)(s)?;
    let (s, e) = symbol("endcase")(s)?;
    Ok((
        s,
        RsCase {
            nodes: (a, b, c, d, e),
        },
    ))
}

pub fn rs_case_item(s: Span) -> IResult<Span, RsCaseItem> {
    alt((rs_case_item_nondefault, rs_case_item_default))(s)
}

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

pub fn rs_case_item_default(s: Span) -> IResult<Span, RsCaseItem> {
    let (s, a) = symbol("default")(s)?;
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

use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct RandsequenceStatement<'a> {
    pub nodes: (Option<ProductionIdentifier<'a>>, Vec<Production<'a>>),
}

#[derive(Debug)]
pub struct Production<'a> {
    pub nodes: (
        Option<DataTypeOrVoid<'a>>,
        ProductionIdentifier<'a>,
        Option<TfPortList<'a>>,
        Vec<RsRule<'a>>,
    ),
}

#[derive(Debug)]
pub struct RsRule<'a> {
    pub nodes: (
        RsProductionList<'a>,
        Option<WeightSpecification<'a>>,
        Option<RsCodeBlock<'a>>,
    ),
}

#[derive(Debug)]
pub enum RsProductionList<'a> {
    Prod(Vec<RsProd<'a>>),
    Join((Option<Expression<'a>>, Vec<ProductionItem<'a>>)),
}

#[derive(Debug)]
pub enum WeightSpecification<'a> {
    IntegralNumber(IntegralNumber<'a>),
    PsIdentifier(PsIdentifier<'a>),
    Expression(Expression<'a>),
}

#[derive(Debug)]
pub struct RsCodeBlock<'a> {
    pub nodes: (Vec<DataDeclaration<'a>>, Vec<StatementOrNull<'a>>),
}

#[derive(Debug)]
pub enum RsProd<'a> {
    Item(ProductionItem<'a>),
    CodeBlock(RsCodeBlock<'a>),
    IfElse(RsIfElse<'a>),
    Repeat(RsRepeat<'a>),
    Case(RsCase<'a>),
}

#[derive(Debug)]
pub struct ProductionItem<'a> {
    pub nodes: (ProductionIdentifier<'a>, Option<ListOfArguments<'a>>),
}

#[derive(Debug)]
pub struct RsIfElse<'a> {
    pub nodes: (
        Expression<'a>,
        ProductionItem<'a>,
        Option<ProductionItem<'a>>,
    ),
}

#[derive(Debug)]
pub struct RsRepeat<'a> {
    pub nodes: (Expression<'a>, ProductionItem<'a>),
}

#[derive(Debug)]
pub struct RsCase<'a> {
    pub nodes: (CaseExpression<'a>, Vec<RsCaseItem<'a>>),
}

#[derive(Debug)]
pub enum RsCaseItem<'a> {
    NonDefault(RsCaseItemNondefault<'a>),
    Default(RsCaseItemDefault<'a>),
}

#[derive(Debug)]
pub struct RsCaseItemDefault<'a> {
    pub nodes: (ProductionItem<'a>,),
}

#[derive(Debug)]
pub struct RsCaseItemNondefault<'a> {
    pub nodes: (Vec<CaseItemExpression<'a>>, ProductionItem<'a>),
}

// -----------------------------------------------------------------------------

pub fn randsequence_statement(s: Span) -> IResult<Span, RandsequenceStatement> {
    let (s, _) = symbol("randsequence")(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, x) = opt(production_identifier)(s)?;
    let (s, _) = symbol(")")(s)?;
    let (s, y) = many1(production)(s)?;
    let (s, _) = symbol("endsequence")(s)?;
    Ok((s, RandsequenceStatement { nodes: (x, y) }))
}

pub fn production(s: Span) -> IResult<Span, Production> {
    let (s, x) = opt(data_type_or_void)(s)?;
    let (s, y) = production_identifier(s)?;
    let (s, z) = opt(paren(tf_port_list))(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, v) = separated_nonempty_list(symbol("|"), rs_rule)(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((
        s,
        Production {
            nodes: (x, y, z, v),
        },
    ))
}

pub fn rs_rule(s: Span) -> IResult<Span, RsRule> {
    let (s, x) = rs_production_list(s)?;
    let (s, y) = opt(preceded(
        symbol(":="),
        pair(weight_specification, opt(rs_code_block)),
    ))(s)?;

    let (y, z) = if let Some((y, z)) = y {
        (Some(y), z)
    } else {
        (None, None)
    };
    Ok((s, RsRule { nodes: (x, y, z) }))
}

pub fn rs_production_list(s: Span) -> IResult<Span, RsProductionList> {
    alt((rs_production_list_prod, rs_production_list_join))(s)
}

pub fn rs_production_list_prod(s: Span) -> IResult<Span, RsProductionList> {
    let (s, x) = many1(rs_prod)(s)?;
    Ok((s, RsProductionList::Prod(x)))
}

pub fn rs_production_list_join(s: Span) -> IResult<Span, RsProductionList> {
    let (s, _) = symbol("rand")(s)?;
    let (s, _) = symbol("join")(s)?;
    let (s, x) = opt(paren(expression))(s)?;
    let (s, y) = production_item(s)?;
    let (s, z) = many1(production_item)(s)?;

    let mut y = vec![y];
    for z in z {
        y.push(z);
    }
    Ok((s, RsProductionList::Join((x, y))))
}

pub fn weight_specification(s: Span) -> IResult<Span, WeightSpecification> {
    alt((
        map(integral_number, |x| WeightSpecification::IntegralNumber(x)),
        map(ps_identifier, |x| WeightSpecification::PsIdentifier(x)),
        map(paren(expression), |x| WeightSpecification::Expression(x)),
    ))(s)
}

pub fn rs_code_block(s: Span) -> IResult<Span, RsCodeBlock> {
    let (s, _) = symbol("{")(s)?;
    let (s, x) = many0(data_declaration)(s)?;
    let (s, y) = many0(statement_or_null)(s)?;
    let (s, _) = symbol("}")(s)?;
    Ok((s, RsCodeBlock { nodes: (x, y) }))
}

pub fn rs_prod(s: Span) -> IResult<Span, RsProd> {
    alt((
        map(production_item, |x| RsProd::Item(x)),
        map(rs_code_block, |x| RsProd::CodeBlock(x)),
        map(rs_if_else, |x| RsProd::IfElse(x)),
        map(rs_repeat, |x| RsProd::Repeat(x)),
        map(rs_case, |x| RsProd::Case(x)),
    ))(s)
}

pub fn production_item(s: Span) -> IResult<Span, ProductionItem> {
    let (s, x) = production_identifier(s)?;
    let (s, y) = opt(paren(list_of_arguments))(s)?;
    Ok((s, ProductionItem { nodes: (x, y) }))
}

pub fn rs_if_else(s: Span) -> IResult<Span, RsIfElse> {
    let (s, _) = symbol("if")(s)?;
    let (s, x) = paren(expression)(s)?;
    let (s, y) = production_item(s)?;
    let (s, z) = opt(preceded(symbol("else"), production_item))(s)?;
    Ok((s, RsIfElse { nodes: (x, y, z) }))
}

pub fn rs_repeat(s: Span) -> IResult<Span, RsRepeat> {
    let (s, _) = symbol("repeat")(s)?;
    let (s, x) = paren(expression)(s)?;
    let (s, y) = production_item(s)?;
    Ok((s, RsRepeat { nodes: (x, y) }))
}

pub fn rs_case(s: Span) -> IResult<Span, RsCase> {
    let (s, _) = symbol("case")(s)?;
    let (s, x) = paren(case_expression)(s)?;
    let (s, y) = many1(rs_case_item)(s)?;
    Ok((s, RsCase { nodes: (x, y) }))
}

pub fn rs_case_item(s: Span) -> IResult<Span, RsCaseItem> {
    alt((rs_case_item_nondefault, rs_case_item_default))(s)
}

pub fn rs_case_item_nondefault(s: Span) -> IResult<Span, RsCaseItem> {
    let (s, x) = separated_nonempty_list(symbol(","), case_item_expression)(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, y) = production_item(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((
        s,
        RsCaseItem::NonDefault(RsCaseItemNondefault { nodes: (x, y) }),
    ))
}

pub fn rs_case_item_default(s: Span) -> IResult<Span, RsCaseItem> {
    let (s, _) = symbol("default")(s)?;
    let (s, _) = opt(symbol(":"))(s)?;
    let (s, x) = production_item(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((s, RsCaseItem::Default(RsCaseItemDefault { nodes: (x,) })))
}

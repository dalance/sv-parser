use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct RandsequenceStatement<'a> {
    pub identifier: Option<Identifier<'a>>,
    pub production: Vec<Production<'a>>,
}

#[derive(Debug)]
pub struct Production<'a> {
    pub r#type: Option<DataTypeOrVoid<'a>>,
    pub identifier: Identifier<'a>,
    pub tf_port_list: Option<TfPortList<'a>>,
    pub rs_rule: Vec<RsRule<'a>>,
}

#[derive(Debug)]
pub struct RsRule<'a> {
    pub production: RsProductionList<'a>,
    pub weight: Option<WeightSpecification<'a>>,
    pub block: Option<RsCodeBlock<'a>>,
}

#[derive(Debug)]
pub enum RsProductionList<'a> {
    Prod(Vec<RsProd<'a>>),
    Join((Option<Expression<'a>>, Vec<ProductionItem<'a>>)),
}

#[derive(Debug)]
pub enum WeightSpecification<'a> {
    Number(Number<'a>),
    Identifier(ScopedIdentifier<'a>),
    Expression(Expression<'a>),
}

#[derive(Debug)]
pub struct RsCodeBlock<'a> {
    pub declaration: Vec<DataDeclaration<'a>>,
    pub statement: Vec<StatementOrNull<'a>>,
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
    pub identifier: Identifier<'a>,
    pub argument: Option<ListOfArguments<'a>>,
}

#[derive(Debug)]
pub struct RsIfElse<'a> {
    pub expression: Expression<'a>,
    pub item: ProductionItem<'a>,
    pub else_item: Option<ProductionItem<'a>>,
}

#[derive(Debug)]
pub struct RsRepeat<'a> {
    pub expression: Expression<'a>,
    pub item: ProductionItem<'a>,
}

#[derive(Debug)]
pub struct RsCase<'a> {
    pub expression: Expression<'a>,
    pub item: Vec<RsCaseItem<'a>>,
}

#[derive(Debug)]
pub enum RsCaseItem<'a> {
    NonDefault(RsCaseItemNondefault<'a>),
    Default(RsCaseItemDefault<'a>),
}

#[derive(Debug)]
pub struct RsCaseItemDefault<'a> {
    pub item: ProductionItem<'a>,
}

#[derive(Debug)]
pub struct RsCaseItemNondefault<'a> {
    pub expression: Vec<Expression<'a>>,
    pub item: ProductionItem<'a>,
}

// -----------------------------------------------------------------------------

pub fn randsequence_statement(s: &str) -> IResult<&str, RandsequenceStatement> {
    let (s, _) = symbol("randsequence")(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, x) = opt(production_identifier)(s)?;
    let (s, _) = symbol(")")(s)?;
    let (s, y) = many1(production)(s)?;
    let (s, _) = symbol("endsequence")(s)?;
    Ok((
        s,
        RandsequenceStatement {
            identifier: x,
            production: y,
        },
    ))
}

pub fn production(s: &str) -> IResult<&str, Production> {
    let (s, x) = opt(data_type_or_void)(s)?;
    let (s, y) = production_identifier(s)?;
    let (s, z) = opt(paren(tf_port_list))(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, v) = separated_nonempty_list(symbol("|"), rs_rule)(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((
        s,
        Production {
            r#type: x,
            identifier: y,
            tf_port_list: z,
            rs_rule: v,
        },
    ))
}

pub fn rs_rule(s: &str) -> IResult<&str, RsRule> {
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
    Ok((
        s,
        RsRule {
            production: x,
            weight: y,
            block: z,
        },
    ))
}

pub fn rs_production_list(s: &str) -> IResult<&str, RsProductionList> {
    alt((rs_production_list_prod, rs_production_list_join))(s)
}

pub fn rs_production_list_prod(s: &str) -> IResult<&str, RsProductionList> {
    let (s, x) = many1(rs_prod)(s)?;
    Ok((s, RsProductionList::Prod(x)))
}

pub fn rs_production_list_join(s: &str) -> IResult<&str, RsProductionList> {
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

pub fn weight_specification(s: &str) -> IResult<&str, WeightSpecification> {
    alt((
        map(integral_number, |x| WeightSpecification::Number(x)),
        map(ps_identifier, |x| WeightSpecification::Identifier(x)),
        map(paren(expression), |x| WeightSpecification::Expression(x)),
    ))(s)
}

pub fn rs_code_block(s: &str) -> IResult<&str, RsCodeBlock> {
    let (s, _) = symbol("{")(s)?;
    let (s, x) = many0(data_declaration)(s)?;
    let (s, y) = many0(statement_or_null)(s)?;
    let (s, _) = symbol("}")(s)?;
    Ok((
        s,
        RsCodeBlock {
            declaration: x,
            statement: y,
        },
    ))
}

pub fn rs_prod(s: &str) -> IResult<&str, RsProd> {
    alt((
        map(production_item, |x| RsProd::Item(x)),
        map(rs_code_block, |x| RsProd::CodeBlock(x)),
        map(rs_if_else, |x| RsProd::IfElse(x)),
        map(rs_repeat, |x| RsProd::Repeat(x)),
        map(rs_case, |x| RsProd::Case(x)),
    ))(s)
}

pub fn production_item(s: &str) -> IResult<&str, ProductionItem> {
    let (s, x) = production_identifier(s)?;
    let (s, y) = opt(paren(list_of_arguments))(s)?;
    Ok((
        s,
        ProductionItem {
            identifier: x,
            argument: y,
        },
    ))
}

pub fn rs_if_else(s: &str) -> IResult<&str, RsIfElse> {
    let (s, _) = symbol("if")(s)?;
    let (s, x) = paren(expression)(s)?;
    let (s, y) = production_item(s)?;
    let (s, z) = opt(preceded(symbol("else"), production_item))(s)?;
    Ok((
        s,
        RsIfElse {
            expression: x,
            item: y,
            else_item: z,
        },
    ))
}

pub fn rs_repeat(s: &str) -> IResult<&str, RsRepeat> {
    let (s, _) = symbol("repeat")(s)?;
    let (s, x) = paren(expression)(s)?;
    let (s, y) = production_item(s)?;
    Ok((
        s,
        RsRepeat {
            expression: x,
            item: y,
        },
    ))
}

pub fn rs_case(s: &str) -> IResult<&str, RsCase> {
    let (s, _) = symbol("case")(s)?;
    let (s, x) = paren(case_expression)(s)?;
    let (s, y) = many1(rs_case_item)(s)?;
    Ok((
        s,
        RsCase {
            expression: x,
            item: y,
        },
    ))
}

pub fn rs_case_item(s: &str) -> IResult<&str, RsCaseItem> {
    alt((rs_case_item_nondefault, rs_case_item_default))(s)
}

pub fn rs_case_item_nondefault(s: &str) -> IResult<&str, RsCaseItem> {
    let (s, x) = separated_nonempty_list(symbol(","), case_item_expression)(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, y) = production_item(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((
        s,
        RsCaseItem::NonDefault(RsCaseItemNondefault {
            expression: x,
            item: y,
        }),
    ))
}

pub fn rs_case_item_default(s: &str) -> IResult<&str, RsCaseItem> {
    let (s, _) = symbol("default")(s)?;
    let (s, _) = opt(symbol(":"))(s)?;
    let (s, x) = production_item(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((s, RsCaseItem::Default(RsCaseItemDefault { item: x })))
}

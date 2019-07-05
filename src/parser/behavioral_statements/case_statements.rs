use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum CaseStatement<'a> {
    Normal(CaseStatementNormal<'a>),
    Matches(CaseStatementMatches<'a>),
    Inside(CaseStatementInside<'a>),
}

#[derive(Debug)]
pub struct CaseStatementNormal<'a> {
    pub unique_priority: Option<UniquePriority>,
    pub keyword: CaseKeyword,
    pub expression: Expression<'a>,
    pub item: Vec<CaseItem<'a>>,
}

#[derive(Debug)]
pub struct CaseStatementMatches<'a> {
    pub unique_priority: Option<UniquePriority>,
    pub keyword: CaseKeyword,
    pub expression: Expression<'a>,
    pub item: Vec<CasePatternItem<'a>>,
}

#[derive(Debug)]
pub struct CaseStatementInside<'a> {
    pub unique_priority: Option<UniquePriority>,
    pub keyword: CaseKeyword,
    pub expression: Expression<'a>,
    pub item: Vec<CaseInsideItem<'a>>,
}

#[derive(Debug)]
pub enum CaseKeyword {
    Case,
    Casez,
    Casex,
}

#[derive(Debug)]
pub enum CaseItem<'a> {
    NonDefault(CaseItemNondefault<'a>),
    Default(CaseItemDefault<'a>),
}

#[derive(Debug)]
pub enum CasePatternItem<'a> {
    NonDefault(CasePatternItemNondefault<'a>),
    Default(CaseItemDefault<'a>),
}

#[derive(Debug)]
pub enum CaseInsideItem<'a> {
    NonDefault(CaseInsideItemNondefault<'a>),
    Default(CaseItemDefault<'a>),
}

#[derive(Debug)]
pub struct CaseItemDefault<'a> {
    pub statement: StatementOrNull<'a>,
}

#[derive(Debug)]
pub struct CaseItemNondefault<'a> {
    pub expression: Vec<Expression<'a>>,
    pub statement: StatementOrNull<'a>,
}

#[derive(Debug)]
pub struct CasePatternItemNondefault<'a> {
    pub pattern: Pattern<'a>,
    pub expression: Option<Expression<'a>>,
    pub statement: StatementOrNull<'a>,
}

#[derive(Debug)]
pub struct CaseInsideItemNondefault<'a> {
    pub open_range_list: Vec<ValueRange<'a>>,
    pub statement: StatementOrNull<'a>,
}

#[derive(Debug)]
pub struct RandcaseStatement<'a> {
    pub item: Vec<RandcaseItem<'a>>,
}

#[derive(Debug)]
pub struct RandcaseItem<'a> {
    pub expression: Expression<'a>,
    pub statement: StatementOrNull<'a>,
}

// -----------------------------------------------------------------------------

pub fn case_statement(s: &str) -> IResult<&str, CaseStatement> {
    alt((
        case_statement_normal,
        case_statement_matches,
        case_statement_inside,
    ))(s)
}

pub fn case_statement_normal(s: &str) -> IResult<&str, CaseStatement> {
    let (s, x) = opt(unique_priority)(s)?;
    let (s, y) = case_keyword(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, z) = case_expression(s)?;
    let (s, _) = symbol(")")(s)?;
    let (s, v) = many1(case_item)(s)?;
    let (s, _) = symbol("endcase")(s)?;
    Ok((
        s,
        CaseStatement::Normal(CaseStatementNormal {
            unique_priority: x,
            keyword: y,
            expression: z,
            item: v,
        }),
    ))
}

pub fn case_statement_matches(s: &str) -> IResult<&str, CaseStatement> {
    let (s, x) = opt(unique_priority)(s)?;
    let (s, y) = case_keyword(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, z) = case_expression(s)?;
    let (s, _) = symbol(")")(s)?;
    let (s, _) = symbol("matches")(s)?;
    let (s, v) = many1(case_pattern_item)(s)?;
    let (s, _) = symbol("endcase")(s)?;
    Ok((
        s,
        CaseStatement::Matches(CaseStatementMatches {
            unique_priority: x,
            keyword: y,
            expression: z,
            item: v,
        }),
    ))
}

pub fn case_statement_inside(s: &str) -> IResult<&str, CaseStatement> {
    let (s, x) = opt(unique_priority)(s)?;
    let (s, y) = case_keyword(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, z) = case_expression(s)?;
    let (s, _) = symbol(")")(s)?;
    let (s, _) = symbol("inside")(s)?;
    let (s, v) = many1(case_inside_item)(s)?;
    let (s, _) = symbol("endcase")(s)?;
    Ok((
        s,
        CaseStatement::Inside(CaseStatementInside {
            unique_priority: x,
            keyword: y,
            expression: z,
            item: v,
        }),
    ))
}

pub fn case_keyword(s: &str) -> IResult<&str, CaseKeyword> {
    alt((
        map(symbol("casez"), |_| CaseKeyword::Casez),
        map(symbol("casex"), |_| CaseKeyword::Casex),
        map(symbol("case"), |_| CaseKeyword::Case),
    ))(s)
}

pub fn case_expression(s: &str) -> IResult<&str, Expression> {
    expression(s)
}

pub fn case_item(s: &str) -> IResult<&str, CaseItem> {
    alt((
        case_item_nondefault,
        map(case_item_default, |x| CaseItem::Default(x)),
    ))(s)
}

pub fn case_item_nondefault(s: &str) -> IResult<&str, CaseItem> {
    let (s, x) = separated_nonempty_list(symbol(","), case_item_expression)(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, y) = statement_or_null(s)?;
    Ok((
        s,
        CaseItem::NonDefault(CaseItemNondefault {
            expression: x,
            statement: y,
        }),
    ))
}

pub fn case_item_default(s: &str) -> IResult<&str, CaseItemDefault> {
    let (s, _) = symbol("default")(s)?;
    let (s, _) = opt(symbol(":"))(s)?;
    let (s, x) = statement_or_null(s)?;
    Ok((s, CaseItemDefault { statement: x }))
}

pub fn case_pattern_item(s: &str) -> IResult<&str, CasePatternItem> {
    alt((
        case_pattern_item_nondefault,
        map(case_item_default, |x| CasePatternItem::Default(x)),
    ))(s)
}

pub fn case_pattern_item_nondefault(s: &str) -> IResult<&str, CasePatternItem> {
    let (s, x) = pattern(s)?;
    let (s, y) = opt(preceded(symbol("&&&"), expression))(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, z) = statement_or_null(s)?;
    Ok((
        s,
        CasePatternItem::NonDefault(CasePatternItemNondefault {
            pattern: x,
            expression: y,
            statement: z,
        }),
    ))
}

pub fn case_inside_item(s: &str) -> IResult<&str, CaseInsideItem> {
    alt((
        case_inside_item_nondefault,
        map(case_item_default, |x| CaseInsideItem::Default(x)),
    ))(s)
}

pub fn case_inside_item_nondefault(s: &str) -> IResult<&str, CaseInsideItem> {
    let (s, x) = open_range_list(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, y) = statement_or_null(s)?;
    Ok((
        s,
        CaseInsideItem::NonDefault(CaseInsideItemNondefault {
            open_range_list: x,
            statement: y,
        }),
    ))
}

pub fn case_item_expression(s: &str) -> IResult<&str, Expression> {
    expression(s)
}

pub fn randcase_statement(s: &str) -> IResult<&str, RandcaseStatement> {
    let (s, _) = symbol("randcase")(s)?;
    let (s, x) = many1(randcase_item)(s)?;
    let (s, _) = symbol("endcase")(s)?;
    Ok((s, RandcaseStatement { item: x }))
}

pub fn randcase_item(s: &str) -> IResult<&str, RandcaseItem> {
    let (s, x) = expression(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, y) = statement_or_null(s)?;
    Ok((
        s,
        RandcaseItem {
            expression: x,
            statement: y,
        },
    ))
}

pub fn open_range_list(s: &str) -> IResult<&str, Vec<ValueRange>> {
    separated_nonempty_list(symbol(","), open_value_range)(s)
}

pub fn open_value_range(s: &str) -> IResult<&str, ValueRange> {
    value_range(s)
}

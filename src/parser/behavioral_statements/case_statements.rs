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
    pub nodes: (
        Option<UniquePriority>,
        CaseKeyword,
        Expression<'a>,
        Vec<CaseItem<'a>>,
    ),
}

#[derive(Debug)]
pub struct CaseStatementMatches<'a> {
    pub nodes: (
        Option<UniquePriority>,
        CaseKeyword,
        Expression<'a>,
        Vec<CasePatternItem<'a>>,
    ),
}

#[derive(Debug)]
pub struct CaseStatementInside<'a> {
    pub nodes: (
        Option<UniquePriority>,
        CaseKeyword,
        Expression<'a>,
        Vec<CaseInsideItem<'a>>,
    ),
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
    pub nodes: (StatementOrNull<'a>,),
}

#[derive(Debug)]
pub struct CaseItemNondefault<'a> {
    pub nodes: (Vec<Expression<'a>>, StatementOrNull<'a>),
}

#[derive(Debug)]
pub struct CasePatternItemNondefault<'a> {
    pub nodes: (Pattern<'a>, Option<Expression<'a>>, StatementOrNull<'a>),
}

#[derive(Debug)]
pub struct CaseInsideItemNondefault<'a> {
    pub nodes: (Vec<ValueRange<'a>>, StatementOrNull<'a>),
}

#[derive(Debug)]
pub struct RandcaseStatement<'a> {
    pub nodes: (Vec<RandcaseItem<'a>>,),
}

#[derive(Debug)]
pub struct RandcaseItem<'a> {
    pub nodes: (Expression<'a>, StatementOrNull<'a>),
}

#[derive(Debug)]
pub struct OpenRangeList<'a> {
    pub nodes: (Vec<OpenRangeValue<'a>>,),
}

#[derive(Debug)]
pub struct OpenRangeValue<'a> {
    pub nodes: (ValueRange<'a>,),
}

// -----------------------------------------------------------------------------

pub fn case_statement(s: Span) -> IResult<Span, CaseStatement> {
    alt((
        case_statement_normal,
        case_statement_matches,
        case_statement_inside,
    ))(s)
}

pub fn case_statement_normal(s: Span) -> IResult<Span, CaseStatement> {
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
            nodes: (x, y, z, v),
        }),
    ))
}

pub fn case_statement_matches(s: Span) -> IResult<Span, CaseStatement> {
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
            nodes: (x, y, z, v),
        }),
    ))
}

pub fn case_statement_inside(s: Span) -> IResult<Span, CaseStatement> {
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
            nodes: (x, y, z, v),
        }),
    ))
}

pub fn case_keyword(s: Span) -> IResult<Span, CaseKeyword> {
    alt((
        map(symbol("casez"), |_| CaseKeyword::Casez),
        map(symbol("casex"), |_| CaseKeyword::Casex),
        map(symbol("case"), |_| CaseKeyword::Case),
    ))(s)
}

pub fn case_expression(s: Span) -> IResult<Span, Expression> {
    expression(s)
}

pub fn case_item(s: Span) -> IResult<Span, CaseItem> {
    alt((
        case_item_nondefault,
        map(case_item_default, |x| CaseItem::Default(x)),
    ))(s)
}

pub fn case_item_nondefault(s: Span) -> IResult<Span, CaseItem> {
    let (s, x) = separated_nonempty_list(symbol(","), case_item_expression)(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, y) = statement_or_null(s)?;
    Ok((
        s,
        CaseItem::NonDefault(CaseItemNondefault { nodes: (x, y) }),
    ))
}

pub fn case_item_default(s: Span) -> IResult<Span, CaseItemDefault> {
    let (s, _) = symbol("default")(s)?;
    let (s, _) = opt(symbol(":"))(s)?;
    let (s, x) = statement_or_null(s)?;
    Ok((s, CaseItemDefault { nodes: (x,) }))
}

pub fn case_pattern_item(s: Span) -> IResult<Span, CasePatternItem> {
    alt((
        case_pattern_item_nondefault,
        map(case_item_default, |x| CasePatternItem::Default(x)),
    ))(s)
}

pub fn case_pattern_item_nondefault(s: Span) -> IResult<Span, CasePatternItem> {
    let (s, x) = pattern(s)?;
    let (s, y) = opt(preceded(symbol("&&&"), expression))(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, z) = statement_or_null(s)?;
    Ok((
        s,
        CasePatternItem::NonDefault(CasePatternItemNondefault { nodes: (x, y, z) }),
    ))
}

pub fn case_inside_item(s: Span) -> IResult<Span, CaseInsideItem> {
    alt((
        case_inside_item_nondefault,
        map(case_item_default, |x| CaseInsideItem::Default(x)),
    ))(s)
}

pub fn case_inside_item_nondefault(s: Span) -> IResult<Span, CaseInsideItem> {
    let (s, x) = open_range_list(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, y) = statement_or_null(s)?;
    Ok((
        s,
        CaseInsideItem::NonDefault(CaseInsideItemNondefault { nodes: (x, y) }),
    ))
}

pub fn case_item_expression(s: Span) -> IResult<Span, Expression> {
    expression(s)
}

pub fn randcase_statement(s: Span) -> IResult<Span, RandcaseStatement> {
    let (s, _) = symbol("randcase")(s)?;
    let (s, x) = many1(randcase_item)(s)?;
    let (s, _) = symbol("endcase")(s)?;
    Ok((s, RandcaseStatement { nodes: (x,) }))
}

pub fn randcase_item(s: Span) -> IResult<Span, RandcaseItem> {
    let (s, x) = expression(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, y) = statement_or_null(s)?;
    Ok((s, RandcaseItem { nodes: (x, y) }))
}

pub fn open_range_list(s: Span) -> IResult<Span, Vec<ValueRange>> {
    separated_nonempty_list(symbol(","), open_value_range)(s)
}

pub fn open_value_range(s: Span) -> IResult<Span, ValueRange> {
    value_range(s)
}

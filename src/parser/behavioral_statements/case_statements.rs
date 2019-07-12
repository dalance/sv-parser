use crate::ast::*;
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
        Option<UniquePriority<'a>>,
        CaseKeyword<'a>,
        Paren<'a, CaseExpression<'a>>,
        CaseItem<'a>,
        Vec<CaseItem<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug)]
pub struct CaseStatementMatches<'a> {
    pub nodes: (
        Option<UniquePriority<'a>>,
        CaseKeyword<'a>,
        Paren<'a, CaseExpression<'a>>,
        Symbol<'a>,
        CasePatternItem<'a>,
        Vec<CasePatternItem<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug)]
pub struct CaseStatementInside<'a> {
    pub nodes: (
        Option<UniquePriority<'a>>,
        Symbol<'a>,
        Paren<'a, CaseExpression<'a>>,
        Symbol<'a>,
        CaseInsideItem<'a>,
        Vec<CaseInsideItem<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum CaseKeyword<'a> {
    Case(Symbol<'a>),
    Casez(Symbol<'a>),
    Casex(Symbol<'a>),
}

#[derive(Debug)]
pub struct CaseExpression<'a> {
    pub nodes: (Expression<'a>,),
}

#[derive(Debug)]
pub enum CaseItem<'a> {
    NonDefault(CaseItemNondefault<'a>),
    Default(CaseItemDefault<'a>),
}

#[derive(Debug)]
pub struct CaseItemNondefault<'a> {
    pub nodes: (
        List<Symbol<'a>, CaseItemExpression<'a>>,
        Symbol<'a>,
        StatementOrNull<'a>,
    ),
}

#[derive(Debug)]
pub struct CaseItemDefault<'a> {
    pub nodes: (Symbol<'a>, Option<Symbol<'a>>, StatementOrNull<'a>),
}

#[derive(Debug)]
pub enum CasePatternItem<'a> {
    NonDefault(CasePatternItemNondefault<'a>),
    Default(CaseItemDefault<'a>),
}

#[derive(Debug)]
pub struct CasePatternItemNondefault<'a> {
    pub nodes: (
        Pattern<'a>,
        Option<(Symbol<'a>, Expression<'a>)>,
        Symbol<'a>,
        StatementOrNull<'a>,
    ),
}

#[derive(Debug)]
pub enum CaseInsideItem<'a> {
    NonDefault(CaseInsideItemNondefault<'a>),
    Default(CaseItemDefault<'a>),
}

#[derive(Debug)]
pub struct CaseInsideItemNondefault<'a> {
    pub nodes: (OpenRangeList<'a>, Symbol<'a>, StatementOrNull<'a>),
}

#[derive(Debug)]
pub struct CaseItemExpression<'a> {
    pub nodes: (Expression<'a>,),
}

#[derive(Debug)]
pub struct RandcaseStatement<'a> {
    pub nodes: (
        Symbol<'a>,
        RandcaseItem<'a>,
        Vec<RandcaseItem<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug)]
pub struct RandcaseItem<'a> {
    pub nodes: (Expression<'a>, Symbol<'a>, StatementOrNull<'a>),
}

#[derive(Debug)]
pub struct OpenRangeList<'a> {
    pub nodes: (List<Symbol<'a>, OpenValueRange<'a>>,),
}

#[derive(Debug)]
pub struct OpenValueRange<'a> {
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
    let (s, a) = opt(unique_priority)(s)?;
    let (s, b) = case_keyword(s)?;
    let (s, c) = paren(case_expression)(s)?;
    let (s, d) = case_item(s)?;
    let (s, e) = many0(case_item)(s)?;
    let (s, f) = symbol("endcase")(s)?;
    Ok((
        s,
        CaseStatement::Normal(CaseStatementNormal {
            nodes: (a, b, c, d, e, f),
        }),
    ))
}

pub fn case_statement_matches(s: Span) -> IResult<Span, CaseStatement> {
    let (s, a) = opt(unique_priority)(s)?;
    let (s, b) = case_keyword(s)?;
    let (s, c) = paren(case_expression)(s)?;
    let (s, d) = symbol("matches")(s)?;
    let (s, e) = case_pattern_item(s)?;
    let (s, f) = many0(case_pattern_item)(s)?;
    let (s, g) = symbol("endcase")(s)?;
    Ok((
        s,
        CaseStatement::Matches(CaseStatementMatches {
            nodes: (a, b, c, d, e, f, g),
        }),
    ))
}

pub fn case_statement_inside(s: Span) -> IResult<Span, CaseStatement> {
    let (s, a) = opt(unique_priority)(s)?;
    let (s, b) = symbol("case")(s)?;
    let (s, c) = paren(case_expression)(s)?;
    let (s, d) = symbol("inside")(s)?;
    let (s, e) = case_inside_item(s)?;
    let (s, f) = many0(case_inside_item)(s)?;
    let (s, g) = symbol("endcase")(s)?;
    Ok((
        s,
        CaseStatement::Inside(CaseStatementInside {
            nodes: (a, b, c, d, e, f, g),
        }),
    ))
}

pub fn case_keyword(s: Span) -> IResult<Span, CaseKeyword> {
    alt((
        map(symbol("casez"), |x| CaseKeyword::Casez(x)),
        map(symbol("casex"), |x| CaseKeyword::Casex(x)),
        map(symbol("case"), |x| CaseKeyword::Case(x)),
    ))(s)
}

pub fn case_expression(s: Span) -> IResult<Span, CaseExpression> {
    let (s, a) = expression(s)?;
    Ok((s, CaseExpression { nodes: (a,) }))
}

pub fn case_item(s: Span) -> IResult<Span, CaseItem> {
    alt((
        case_item_nondefault,
        map(case_item_default, |x| CaseItem::Default(x)),
    ))(s)
}

pub fn case_item_nondefault(s: Span) -> IResult<Span, CaseItem> {
    let (s, a) = list(symbol(","), case_item_expression)(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = statement_or_null(s)?;
    Ok((
        s,
        CaseItem::NonDefault(CaseItemNondefault { nodes: (a, b, c) }),
    ))
}

pub fn case_item_default(s: Span) -> IResult<Span, CaseItemDefault> {
    let (s, a) = symbol("default")(s)?;
    let (s, b) = opt(symbol(":"))(s)?;
    let (s, c) = statement_or_null(s)?;
    Ok((s, CaseItemDefault { nodes: (a, b, c) }))
}

pub fn case_pattern_item(s: Span) -> IResult<Span, CasePatternItem> {
    alt((
        case_pattern_item_nondefault,
        map(case_item_default, |x| CasePatternItem::Default(x)),
    ))(s)
}

pub fn case_pattern_item_nondefault(s: Span) -> IResult<Span, CasePatternItem> {
    let (s, a) = pattern(s)?;
    let (s, b) = opt(pair(symbol("&&&"), expression))(s)?;
    let (s, c) = symbol(":")(s)?;
    let (s, d) = statement_or_null(s)?;
    Ok((
        s,
        CasePatternItem::NonDefault(CasePatternItemNondefault {
            nodes: (a, b, c, d),
        }),
    ))
}

pub fn case_inside_item(s: Span) -> IResult<Span, CaseInsideItem> {
    alt((
        case_inside_item_nondefault,
        map(case_item_default, |x| CaseInsideItem::Default(x)),
    ))(s)
}

pub fn case_inside_item_nondefault(s: Span) -> IResult<Span, CaseInsideItem> {
    let (s, a) = open_range_list(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = statement_or_null(s)?;
    Ok((
        s,
        CaseInsideItem::NonDefault(CaseInsideItemNondefault { nodes: (a, b, c) }),
    ))
}

pub fn case_item_expression(s: Span) -> IResult<Span, CaseItemExpression> {
    let (s, a) = expression(s)?;
    Ok((s, CaseItemExpression { nodes: (a,) }))
}

pub fn randcase_statement(s: Span) -> IResult<Span, RandcaseStatement> {
    let (s, a) = symbol("randcase")(s)?;
    let (s, b) = randcase_item(s)?;
    let (s, c) = many0(randcase_item)(s)?;
    let (s, d) = symbol("endcase")(s)?;
    Ok((
        s,
        RandcaseStatement {
            nodes: (a, b, c, d),
        },
    ))
}

pub fn randcase_item(s: Span) -> IResult<Span, RandcaseItem> {
    let (s, a) = expression(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = statement_or_null(s)?;
    Ok((s, RandcaseItem { nodes: (a, b, c) }))
}

pub fn open_range_list(s: Span) -> IResult<Span, OpenRangeList> {
    let (s, a) = list(symbol(","), open_value_range)(s)?;
    Ok((s, OpenRangeList { nodes: (a,) }))
}

pub fn open_value_range(s: Span) -> IResult<Span, OpenValueRange> {
    let (s, a) = value_range(s)?;
    Ok((s, OpenValueRange { nodes: (a,) }))
}

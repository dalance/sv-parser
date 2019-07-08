use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct CovergroupDeclaration<'a> {
    pub nodes: (
        Identifier<'a>,
        Option<TfPortList<'a>>,
        Option<CoverageEvent<'a>>,
        Vec<CoverageSpecOrOption<'a>>,
        Identifier<'a>,
    ),
}

#[derive(Debug)]
pub enum CoverageSpecOrOption<'a> {
    Spec(CoverageSpecOrOptionSpec<'a>),
    Option(CoverageSpecOrOptionOption<'a>),
}

#[derive(Debug)]
pub struct CoverageSpecOrOptionSpec<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, CoverageSpec<'a>),
}

#[derive(Debug)]
pub struct CoverageSpecOrOptionOption<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, CoverageOption<'a>),
}

#[derive(Debug)]
pub enum CoverageOption<'a> {
    Option(CoverageOptionOption<'a>),
    TypeOption(CoverageOptionTypeOption<'a>),
}

#[derive(Debug)]
pub struct CoverageOptionOption<'a> {
    pub nodes: (Identifier<'a>, Expression<'a>),
}

#[derive(Debug)]
pub struct CoverageOptionTypeOption<'a> {
    pub nodes: (Identifier<'a>, ConstantExpression<'a>),
}

#[derive(Debug)]
pub enum CoverageSpec<'a> {
    CoverPoint(CoverPoint<'a>),
    CoverCross(CoverCross<'a>),
}

#[derive(Debug)]
pub enum CoverageEvent<'a> {
    ClockingEvent(ClockingEvent<'a>),
    Sample(CoverageEventSample<'a>),
    At(CoverageEventAt<'a>),
}

#[derive(Debug)]
pub struct CoverageEventSample<'a> {
    pub nodes: (Option<TfPortList<'a>>,),
}

#[derive(Debug)]
pub struct CoverageEventAt<'a> {
    pub nodes: (BlockEventExpression<'a>,),
}

#[derive(Debug)]
pub enum BlockEventExpression<'a> {
    Or(Box<BlockEventExpressionOr<'a>>),
    Begin(BlockEventExpressionBegin<'a>),
    End(BlockEventExpressionEnd<'a>),
}

#[derive(Debug)]
pub struct BlockEventExpressionOr<'a> {
    pub nodes: (BlockEventExpression<'a>, BlockEventExpression<'a>),
}

#[derive(Debug)]
pub struct BlockEventExpressionBegin<'a> {
    pub nodes: (HierarchicalBtfIdentifier<'a>,),
}

#[derive(Debug)]
pub struct BlockEventExpressionEnd<'a> {
    pub nodes: (HierarchicalBtfIdentifier<'a>,),
}

#[derive(Debug)]
pub enum HierarchicalBtfIdentifier<'a> {
    Tf(Identifier<'a>),
    Block(Identifier<'a>),
    Method(HierarchicalBtfIdentifierMethod<'a>),
}

#[derive(Debug)]
pub struct HierarchicalBtfIdentifierMethod<'a> {
    pub nodes: (
        Option<HierarchicalIdentifierOrClassScope<'a>>,
        Identifier<'a>,
    ),
}

#[derive(Debug)]
pub enum HierarchicalIdentifierOrClassScope<'a> {
    HierarchicalIdentifier(HierarchicalIdentifier<'a>),
    ClassScope(ClassScope<'a>),
}

#[derive(Debug)]
pub struct CoverPoint<'a> {
    pub nodes: (
        Option<(Option<DataTypeOrImplicit<'a>>, Identifier<'a>)>,
        Expression<'a>,
        Option<Expression<'a>>,
        BinsOrEmpty<'a>,
    ),
}

#[derive(Debug)]
pub enum BinsOrEmpty<'a> {
    NonEmpty(BinsOrEmptyNonEmpty<'a>),
    Empty,
}

#[derive(Debug)]
pub struct BinsOrEmptyNonEmpty<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, Vec<BinsOrOptions<'a>>),
}

#[derive(Debug)]
pub enum BinsOrOptions<'a> {
    Option(CoverageOption<'a>),
    Covergroup(BinsOrOptionsCovergroup<'a>),
    CoverPoint(BinsOrOptionsCoverPoint<'a>),
    SetCovergroup(BinsOrOptionsSetCovergroup<'a>),
    TransList(BinsOrOptionsTransList<'a>),
    Default(BinsOrOptionsDefault<'a>),
    DefaultSequence(BinsOrOptionsDefaultSequence<'a>),
}

#[derive(Debug)]
pub struct BinsOrOptionsCovergroup<'a> {
    pub nodes: (
        Option<Wildcard>,
        BinsKeyword,
        Identifier<'a>,
        Option<CovergroupExpression<'a>>,
        CovergroupRangeList<'a>,
        Option<WithCovergroupExpression<'a>>,
        Option<Expression<'a>>,
    ),
}

#[derive(Debug)]
pub struct Wildcard {}

#[derive(Debug)]
pub struct BinsOrOptionsCoverPoint<'a> {
    pub nodes: (
        Option<Wildcard>,
        BinsKeyword,
        Identifier<'a>,
        Option<CovergroupExpression<'a>>,
        Identifier<'a>,
        Option<WithCovergroupExpression<'a>>,
        Option<Expression<'a>>,
    ),
}

#[derive(Debug)]
pub struct BinsOrOptionsSetCovergroup<'a> {
    pub nodes: (
        Option<Wildcard>,
        BinsKeyword,
        Identifier<'a>,
        Option<CovergroupExpression<'a>>,
        SetCovergroupExpression<'a>,
        Option<Expression<'a>>,
    ),
}

#[derive(Debug)]
pub struct BinsOrOptionsTransList<'a> {
    pub nodes: (
        Option<Wildcard>,
        BinsKeyword,
        Identifier<'a>,
        TransList<'a>,
        Option<Expression<'a>>,
    ),
}

#[derive(Debug)]
pub struct BinsOrOptionsDefault<'a> {
    pub nodes: (
        BinsKeyword,
        Identifier<'a>,
        Option<CovergroupExpression<'a>>,
        Option<Expression<'a>>,
    ),
}

#[derive(Debug)]
pub struct BinsOrOptionsDefaultSequence<'a> {
    pub nodes: (BinsKeyword, Identifier<'a>, Option<Expression<'a>>),
}

#[derive(Debug)]
pub enum BinsKeyword {
    Bins,
    IllegalBins,
    IgnoreBins,
}

#[derive(Debug)]
pub struct TransList<'a> {
    pub nodes: (Vec<TransSet<'a>>,),
}

#[derive(Debug)]
pub struct TransSet<'a> {
    pub nodes: (TransRangeList<'a>, Vec<TransRangeList<'a>>),
}

#[derive(Debug)]
pub enum TransRangeList<'a> {
    Single(TransItem<'a>),
    Asterisk(TransRangeListAsterisk<'a>),
    Right(TransRangeListRight<'a>),
    Equal(TransRangeListEqual<'a>),
}

#[derive(Debug)]
pub struct TransRangeListAsterisk<'a> {
    pub nodes: (TransItem<'a>, RepeatRange<'a>),
}

#[derive(Debug)]
pub struct TransRangeListRight<'a> {
    pub nodes: (TransItem<'a>, RepeatRange<'a>),
}

#[derive(Debug)]
pub struct TransRangeListEqual<'a> {
    pub nodes: (TransItem<'a>, RepeatRange<'a>),
}

#[derive(Debug)]
pub struct TransItem<'a> {
    pub nodes: (CovergroupRangeList<'a>,),
}

#[derive(Debug)]
pub enum RepeatRange<'a> {
    Single(CovergroupExpression<'a>),
    Binary(RepeatRangeBinary<'a>),
}

#[derive(Debug)]
pub struct RepeatRangeBinary<'a> {
    pub nodes: (CovergroupExpression<'a>, CovergroupExpression<'a>),
}

#[derive(Debug)]
pub struct CoverCross<'a> {
    pub nodes: (
        Option<Identifier<'a>>,
        ListOfCrossItems<'a>,
        Option<Expression<'a>>,
        CrossBody<'a>,
    ),
}

#[derive(Debug)]
pub struct ListOfCrossItems<'a> {
    pub nodes: (CrossItem<'a>, CrossItem<'a>, Option<CrossItem<'a>>),
}

#[derive(Debug)]
pub enum CrossItem<'a> {
    CoverPointIdentifier(Identifier<'a>),
    VariableIdentifier(Identifier<'a>),
}

#[derive(Debug)]
pub enum CrossBody<'a> {
    NonEmpty(CrossBodyNonEmpty<'a>),
    Empty,
}

#[derive(Debug)]
pub struct CrossBodyNonEmpty<'a> {
    pub nodes: (Vec<CrossBodyItem<'a>>),
}

#[derive(Debug)]
pub enum CrossBodyItem<'a> {
    FunctionDeclaration(FunctionDeclaration<'a>),
    BinsSelectionOrOption(BinsSelectionOrOption<'a>),
}

#[derive(Debug)]
pub enum BinsSelectionOrOption<'a> {
    Coverage(BinsSelectionOrOptionCoverage<'a>),
    Bins(BinsSelectionOrOptionBins<'a>),
}

#[derive(Debug)]
pub struct BinsSelectionOrOptionCoverage<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, CoverageOption<'a>),
}

#[derive(Debug)]
pub struct BinsSelectionOrOptionBins<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, BinsSelection<'a>),
}

#[derive(Debug)]
pub struct BinsSelection<'a> {
    pub nodes: (
        BinsKeyword,
        Identifier<'a>,
        SelectExpression<'a>,
        Option<Expression<'a>>,
    ),
}

#[derive(Debug)]
pub enum SelectExpression<'a> {
    SelectCondition(SelectCondition<'a>),
    Not(SelectExpressionNot<'a>),
    And(Box<SelectExpressionAnd<'a>>),
    Or(Box<SelectExpressionOr<'a>>),
    Paren(Box<SelectExpressionParen<'a>>),
    With(Box<SelectExpressionWith<'a>>),
    CrossIdentifier(Identifier<'a>),
    CrossSet(SelectExpressionCrossSet<'a>),
}

#[derive(Debug)]
pub struct SelectExpressionNot<'a> {
    pub nodes: (SelectCondition<'a>,),
}

#[derive(Debug)]
pub struct SelectExpressionAnd<'a> {
    pub nodes: (SelectExpression<'a>, SelectExpression<'a>),
}

#[derive(Debug)]
pub struct SelectExpressionOr<'a> {
    pub nodes: (SelectExpression<'a>, SelectExpression<'a>),
}

#[derive(Debug)]
pub struct SelectExpressionParen<'a> {
    pub nodes: (SelectExpression<'a>,),
}

#[derive(Debug)]
pub struct SelectExpressionWith<'a> {
    pub nodes: (
        SelectExpression<'a>,
        WithCovergroupExpression<'a>,
        Option<IntegerCovergroupExpression<'a>>,
    ),
}

#[derive(Debug)]
pub struct SelectExpressionCrossSet<'a> {
    pub nodes: (
        CrossSetExpression<'a>,
        Option<IntegerCovergroupExpression<'a>>,
    ),
}

#[derive(Debug)]
pub struct SelectCondition<'a> {
    pub nodes: (BinsExpression<'a>, Option<CovergroupRangeList<'a>>),
}

#[derive(Debug)]
pub enum BinsExpression<'a> {
    VariableIdentifier(Identifier<'a>),
    CoverPoint(BinsExpressionCoverPoint<'a>),
}

#[derive(Debug)]
pub struct BinsExpressionCoverPoint<'a> {
    pub nodes: (Identifier<'a>, Option<Identifier<'a>>),
}

#[derive(Debug)]
pub struct CovergroupRangeList<'a> {
    pub nodes: (Vec<CovergroupValueRange<'a>>,),
}

#[derive(Debug)]
pub enum CovergroupValueRange<'a> {
    Single(CovergroupExpression<'a>),
    Binary(CovergroupValueRangeBinary<'a>),
}

#[derive(Debug)]
pub struct CovergroupValueRangeBinary<'a> {
    pub nodes: (CovergroupExpression<'a>, CovergroupExpression<'a>),
}

#[derive(Debug)]
pub struct WithCovergroupExpression<'a> {
    pub nodes: (CovergroupExpression<'a>,),
}

#[derive(Debug)]
pub struct SetCovergroupExpression<'a> {
    pub nodes: (CovergroupExpression<'a>,),
}

#[derive(Debug)]
pub struct IntegerCovergroupExpression<'a> {
    pub nodes: (CovergroupExpression<'a>,),
}

#[derive(Debug)]
pub struct CrossSetExpression<'a> {
    pub nodes: (CovergroupExpression<'a>,),
}

#[derive(Debug)]
pub struct CovergroupExpression<'a> {
    pub nodes: (Expression<'a>,),
}

// -----------------------------------------------------------------------------

pub fn covergroup_declaration(s: &str) -> IResult<&str, CovergroupDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn coverage_spec_or_option(s: &str) -> IResult<&str, CoverageSpecOrOption> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn coverage_option(s: &str) -> IResult<&str, CoverageOption> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn coverage_spec(s: &str) -> IResult<&str, CoverageSpec> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn coverage_event(s: &str) -> IResult<&str, CoverageEvent> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn block_event_expression(s: &str) -> IResult<&str, BlockEventExpression> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn hierarchical_btf_identifier(s: &str) -> IResult<&str, HierarchicalBtfIdentifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn cover_point(s: &str) -> IResult<&str, CoverPoint> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn bins_or_empty(s: &str) -> IResult<&str, BinsOrEmpty> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn bins_or_options(s: &str) -> IResult<&str, BinsOrOptions> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn bins_keyword(s: &str) -> IResult<&str, BinsKeyword> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn trans_list(s: &str) -> IResult<&str, TransList> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn trans_set(s: &str) -> IResult<&str, TransSet> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn trans_range_list(s: &str) -> IResult<&str, TransRangeList> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn trans_item(s: &str) -> IResult<&str, TransItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn repeat_range(s: &str) -> IResult<&str, RepeatRange> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn cover_cross(s: &str) -> IResult<&str, CoverCross> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn list_of_cross_items(s: &str) -> IResult<&str, ListOfCrossItems> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn cross_item(s: &str) -> IResult<&str, CrossItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn cross_body(s: &str) -> IResult<&str, CrossBody> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn cross_body_item(s: &str) -> IResult<&str, CrossBodyItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn bins_selection_or_option(s: &str) -> IResult<&str, BinsSelectionOrOption> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn bins_selection(s: &str) -> IResult<&str, BinsSelection> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn select_expression(s: &str) -> IResult<&str, SelectExpression> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn select_condition(s: &str) -> IResult<&str, SelectCondition> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn bins_expression(s: &str) -> IResult<&str, BinsExpression> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn covergroup_range_list(s: &str) -> IResult<&str, CovergroupRangeList> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn covergroup_value_range(s: &str) -> IResult<&str, CovergroupValueRange> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn with_covergroup_expression(s: &str) -> IResult<&str, WithCovergroupExpression> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn set_covergroup_expression(s: &str) -> IResult<&str, SetCovergroupExpression> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn integer_covergroup_expression(s: &str) -> IResult<&str, IntegerCovergroupExpression> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn cross_set_expression(s: &str) -> IResult<&str, CrossSetExpression> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn covergroup_expression(s: &str) -> IResult<&str, CovergroupExpression> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

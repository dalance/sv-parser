use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct CovergroupDeclaration {
    pub nodes: (
        Keyword,
        CovergroupIdentifier,
        Option<Paren<Option<TfPortList>>>,
        Option<CoverageEvent>,
        Symbol,
        Vec<CoverageSpecOrOption>,
        Keyword,
        Option<(Symbol, CovergroupIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum CoverageSpecOrOption {
    Spec(CoverageSpecOrOptionSpec),
    Option(CoverageSpecOrOptionOption),
}

#[derive(Clone, Debug, Node)]
pub struct CoverageSpecOrOptionSpec {
    pub nodes: (Vec<AttributeInstance>, CoverageSpec),
}

#[derive(Clone, Debug, Node)]
pub struct CoverageSpecOrOptionOption {
    pub nodes: (Vec<AttributeInstance>, CoverageOption, Symbol),
}

#[derive(Clone, Debug, Node)]
pub enum CoverageOption {
    Option(CoverageOptionOption),
    TypeOption(CoverageOptionTypeOption),
}

#[derive(Clone, Debug, Node)]
pub struct CoverageOptionOption {
    pub nodes: (Keyword, Symbol, MemberIdentifier, Symbol, Expression),
}

#[derive(Clone, Debug, Node)]
pub struct CoverageOptionTypeOption {
    pub nodes: (
        Keyword,
        Symbol,
        MemberIdentifier,
        Symbol,
        ConstantExpression,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum CoverageSpec {
    CoverPoint(CoverPoint),
    CoverCross(CoverCross),
}

#[derive(Clone, Debug, Node)]
pub enum CoverageEvent {
    ClockingEvent(ClockingEvent),
    Sample(CoverageEventSample),
    At(CoverageEventAt),
}

#[derive(Clone, Debug, Node)]
pub struct CoverageEventSample {
    pub nodes: (Keyword, Keyword, Keyword, Paren<Option<TfPortList>>),
}

#[derive(Clone, Debug, Node)]
pub struct CoverageEventAt {
    pub nodes: (Symbol, Paren<BlockEventExpression>),
}

#[derive(Clone, Debug, Node)]
pub enum BlockEventExpression {
    Or(Box<BlockEventExpressionOr>),
    Begin(BlockEventExpressionBegin),
    End(BlockEventExpressionEnd),
}

#[derive(Clone, Debug, Node)]
pub struct BlockEventExpressionOr {
    pub nodes: (BlockEventExpression, Keyword, BlockEventExpression),
}

#[derive(Clone, Debug, Node)]
pub struct BlockEventExpressionBegin {
    pub nodes: (Keyword, HierarchicalBtfIdentifier),
}

#[derive(Clone, Debug, Node)]
pub struct BlockEventExpressionEnd {
    pub nodes: (Keyword, HierarchicalBtfIdentifier),
}

#[derive(Clone, Debug, Node)]
pub enum HierarchicalBtfIdentifier {
    HierarchicalTfIdentifier(HierarchicalTfIdentifier),
    HierarchicalBlockIdentifier(HierarchicalBlockIdentifier),
    Method(HierarchicalBtfIdentifierMethod),
}

#[derive(Clone, Debug, Node)]
pub struct HierarchicalBtfIdentifierMethod {
    pub nodes: (Option<HierarchicalIdentifierOrClassScope>, MethodIdentifier),
}

#[derive(Clone, Debug, Node)]
pub enum HierarchicalIdentifierOrClassScope {
    HierarchicalIdentifier((HierarchicalIdentifier, Symbol)),
    ClassScope(ClassScope),
}

#[derive(Clone, Debug, Node)]
pub struct CoverPoint {
    pub nodes: (
        Option<(Option<DataTypeOrImplicit>, CoverPointIdentifier, Symbol)>,
        Keyword,
        Expression,
        Option<(Keyword, Paren<Expression>)>,
        BinsOrEmpty,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum BinsOrEmpty {
    NonEmpty(BinsOrEmptyNonEmpty),
    Empty(Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct BinsOrEmptyNonEmpty {
    pub nodes: (Brace<(Vec<AttributeInstance>, Vec<(BinsOrOptions, Symbol)>)>,),
}

#[derive(Clone, Debug, Node)]
pub enum BinsOrOptions {
    CoverageOption(CoverageOption),
    Covergroup(BinsOrOptionsCovergroup),
    CoverPoint(BinsOrOptionsCoverPoint),
    SetCovergroup(BinsOrOptionsSetCovergroup),
    TransList(BinsOrOptionsTransList),
    Default(BinsOrOptionsDefault),
    DefaultSequence(BinsOrOptionsDefaultSequence),
}

#[derive(Clone, Debug, Node)]
pub struct BinsOrOptionsCovergroup {
    pub nodes: (
        Option<Wildcard>,
        BinsKeyword,
        BinIdentifier,
        Option<Bracket<Option<CovergroupExpression>>>,
        Symbol,
        Brace<CovergroupRangeList>,
        Option<(Keyword, Paren<WithCovergroupExpression>)>,
        Option<(Keyword, Paren<Expression>)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct Wildcard {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, Node)]
pub struct BinsOrOptionsCoverPoint {
    pub nodes: (
        Option<Wildcard>,
        BinsKeyword,
        BinIdentifier,
        Option<Bracket<Option<CovergroupExpression>>>,
        Symbol,
        CoverPointIdentifier,
        Keyword,
        Paren<WithCovergroupExpression>,
        Option<(Keyword, Paren<Expression>)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct BinsOrOptionsSetCovergroup {
    pub nodes: (
        Option<Wildcard>,
        BinsKeyword,
        BinIdentifier,
        Option<Bracket<Option<CovergroupExpression>>>,
        Symbol,
        SetCovergroupExpression,
        Option<(Keyword, Paren<Expression>)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct BinsOrOptionsTransList {
    pub nodes: (
        Option<Wildcard>,
        BinsKeyword,
        BinIdentifier,
        Option<(Symbol, Symbol)>,
        Symbol,
        TransList,
        Option<(Keyword, Paren<Expression>)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct BinsOrOptionsDefault {
    pub nodes: (
        BinsKeyword,
        BinIdentifier,
        Option<Bracket<Option<CovergroupExpression>>>,
        Symbol,
        Keyword,
        Option<(Keyword, Paren<Expression>)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct BinsOrOptionsDefaultSequence {
    pub nodes: (
        BinsKeyword,
        BinIdentifier,
        Symbol,
        Keyword,
        Keyword,
        Option<(Keyword, Paren<Expression>)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum BinsKeyword {
    Bins(Keyword),
    IllegalBins(Keyword),
    IgnoreBins(Keyword),
}

#[derive(Clone, Debug, Node)]
pub struct TransList {
    pub nodes: (List<Symbol, Paren<TransSet>>,),
}

#[derive(Clone, Debug, Node)]
pub struct TransSet {
    pub nodes: (List<Symbol, TransRangeList>,),
}

#[derive(Clone, Debug, Node)]
pub enum TransRangeList {
    TransItem(TransItem),
    Asterisk(TransRangeListAsterisk),
    Arrow(TransRangeListArrow),
    Equal(TransRangeListEqual),
}

#[derive(Clone, Debug, Node)]
pub struct TransRangeListAsterisk {
    pub nodes: (TransItem, Bracket<(Symbol, RepeatRange)>),
}

#[derive(Clone, Debug, Node)]
pub struct TransRangeListArrow {
    pub nodes: (TransItem, Bracket<(Symbol, RepeatRange)>),
}

#[derive(Clone, Debug, Node)]
pub struct TransRangeListEqual {
    pub nodes: (TransItem, Bracket<(Symbol, RepeatRange)>),
}

#[derive(Clone, Debug, Node)]
pub struct TransItem {
    pub nodes: (CovergroupRangeList,),
}

#[derive(Clone, Debug, Node)]
pub enum RepeatRange {
    CovergroupExpression(CovergroupExpression),
    Binary(RepeatRangeBinary),
}

#[derive(Clone, Debug, Node)]
pub struct RepeatRangeBinary {
    pub nodes: (CovergroupExpression, Symbol, CovergroupExpression),
}

#[derive(Clone, Debug, Node)]
pub struct CoverCross {
    pub nodes: (
        Option<(CrossIdentifier, Symbol)>,
        Keyword,
        ListOfCrossItems,
        Option<(Keyword, Paren<Expression>)>,
        CrossBody,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ListOfCrossItems {
    pub nodes: (CrossItem, List<Symbol, CrossItem>),
}

#[derive(Clone, Debug, Node)]
pub enum CrossItem {
    CoverPointIdentifier(CoverPointIdentifier),
    VariableIdentifier(VariableIdentifier),
}

#[derive(Clone, Debug, Node)]
pub enum CrossBody {
    NonEmpty(CrossBodyNonEmpty),
    Empty(Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct CrossBodyNonEmpty {
    pub nodes: (Brace<Vec<(CrossBodyItem, Symbol)>>,),
}

#[derive(Clone, Debug, Node)]
pub enum CrossBodyItem {
    FunctionDeclaration(FunctionDeclaration),
    BinsSelectionOrOption((BinsSelectionOrOption, Symbol)),
}

#[derive(Clone, Debug, Node)]
pub enum BinsSelectionOrOption {
    Coverage(BinsSelectionOrOptionCoverage),
    Bins(BinsSelectionOrOptionBins),
}

#[derive(Clone, Debug, Node)]
pub struct BinsSelectionOrOptionCoverage {
    pub nodes: (Vec<AttributeInstance>, CoverageOption),
}

#[derive(Clone, Debug, Node)]
pub struct BinsSelectionOrOptionBins {
    pub nodes: (Vec<AttributeInstance>, BinsSelection),
}

#[derive(Clone, Debug, Node)]
pub struct BinsSelection {
    pub nodes: (
        BinsKeyword,
        BinIdentifier,
        Symbol,
        SelectExpression,
        Option<(Keyword, Paren<Expression>)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum SelectExpression {
    SelectCondition(SelectCondition),
    Not(SelectExpressionNot),
    And(Box<SelectExpressionAnd>),
    Or(Box<SelectExpressionOr>),
    Paren(Box<SelectExpressionParen>),
    With(Box<SelectExpressionWith>),
    CrossIdentifier(CrossIdentifier),
    CrossSet(SelectExpressionCrossSet),
}

#[derive(Clone, Debug, Node)]
pub struct SelectExpressionNot {
    pub nodes: (Symbol, SelectCondition),
}

#[derive(Clone, Debug, Node)]
pub struct SelectExpressionAnd {
    pub nodes: (SelectExpression, Symbol, SelectExpression),
}

#[derive(Clone, Debug, Node)]
pub struct SelectExpressionOr {
    pub nodes: (SelectExpression, Symbol, SelectExpression),
}

#[derive(Clone, Debug, Node)]
pub struct SelectExpressionParen {
    pub nodes: (Paren<SelectExpression>,),
}

#[derive(Clone, Debug, Node)]
pub struct SelectExpressionWith {
    pub nodes: (
        SelectExpression,
        Keyword,
        Paren<WithCovergroupExpression>,
        Option<(Keyword, IntegerCovergroupExpression)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct SelectExpressionCrossSet {
    pub nodes: (
        CrossSetExpression,
        Option<(Keyword, IntegerCovergroupExpression)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct SelectCondition {
    pub nodes: (
        Keyword,
        Paren<BinsExpression>,
        Option<(Keyword, Brace<CovergroupRangeList>)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum BinsExpression {
    VariableIdentifier(VariableIdentifier),
    CoverPoint(BinsExpressionCoverPoint),
}

#[derive(Clone, Debug, Node)]
pub struct BinsExpressionCoverPoint {
    pub nodes: (CoverPointIdentifier, Option<(Symbol, BinIdentifier)>),
}

#[derive(Clone, Debug, Node)]
pub struct CovergroupRangeList {
    pub nodes: (List<Symbol, CovergroupValueRange>,),
}

#[derive(Clone, Debug, Node)]
pub enum CovergroupValueRange {
    CovergroupExpression(CovergroupExpression),
    Binary(CovergroupValueRangeBinary),
}

#[derive(Clone, Debug, Node)]
pub struct CovergroupValueRangeBinary {
    pub nodes: (Bracket<(CovergroupExpression, Symbol, CovergroupExpression)>,),
}

#[derive(Clone, Debug, Node)]
pub struct WithCovergroupExpression {
    pub nodes: (CovergroupExpression,),
}

#[derive(Clone, Debug, Node)]
pub struct SetCovergroupExpression {
    pub nodes: (CovergroupExpression,),
}

#[derive(Clone, Debug, Node)]
pub struct IntegerCovergroupExpression {
    pub nodes: (CovergroupExpression,),
}

#[derive(Clone, Debug, Node)]
pub struct CrossSetExpression {
    pub nodes: (CovergroupExpression,),
}

#[derive(Clone, Debug, Node)]
pub struct CovergroupExpression {
    pub nodes: (Expression,),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn covergroup_declaration(s: Span) -> IResult<Span, CovergroupDeclaration> {
    let (s, a) = keyword("covergroup")(s)?;
    let (s, b) = covergroup_identifier(s)?;
    let (s, c) = opt(paren(opt(tf_port_list)))(s)?;
    let (s, d) = opt(coverage_event)(s)?;
    let (s, e) = symbol(";")(s)?;
    let (s, f) = many0(coverage_spec_or_option)(s)?;
    let (s, g) = keyword("endgroup")(s)?;
    let (s, h) = opt(pair(symbol(":"), covergroup_identifier))(s)?;
    Ok((
        s,
        CovergroupDeclaration {
            nodes: (a, b, c, d, e, f, g, h),
        },
    ))
}

#[parser]
pub fn coverage_spec_or_option(s: Span) -> IResult<Span, CoverageSpecOrOption> {
    alt((coverage_spec_or_option_spec, coverage_spec_or_option_option))(s)
}

#[parser]
pub fn coverage_spec_or_option_spec(s: Span) -> IResult<Span, CoverageSpecOrOption> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = coverage_spec(s)?;
    Ok((
        s,
        CoverageSpecOrOption::Spec(CoverageSpecOrOptionSpec { nodes: (a, b) }),
    ))
}

#[parser]
pub fn coverage_spec_or_option_option(s: Span) -> IResult<Span, CoverageSpecOrOption> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = coverage_option(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        CoverageSpecOrOption::Option(CoverageSpecOrOptionOption { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn coverage_option(s: Span) -> IResult<Span, CoverageOption> {
    alt((coverage_option_option, coverage_option_type_option))(s)
}

#[parser]
pub fn coverage_option_option(s: Span) -> IResult<Span, CoverageOption> {
    let (s, a) = keyword("option")(s)?;
    let (s, b) = symbol(".")(s)?;
    let (s, c) = member_identifier(s)?;
    let (s, d) = symbol("=")(s)?;
    let (s, e) = expression(s)?;
    Ok((
        s,
        CoverageOption::Option(CoverageOptionOption {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[parser]
pub fn coverage_option_type_option(s: Span) -> IResult<Span, CoverageOption> {
    let (s, a) = keyword("type_option")(s)?;
    let (s, b) = symbol(".")(s)?;
    let (s, c) = member_identifier(s)?;
    let (s, d) = symbol("=")(s)?;
    let (s, e) = constant_expression(s)?;
    Ok((
        s,
        CoverageOption::TypeOption(CoverageOptionTypeOption {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[parser]
pub fn coverage_spec(s: Span) -> IResult<Span, CoverageSpec> {
    alt((
        map(cover_point, |x| CoverageSpec::CoverPoint(x)),
        map(cover_cross, |x| CoverageSpec::CoverCross(x)),
    ))(s)
}

#[parser]
pub fn coverage_event(s: Span) -> IResult<Span, CoverageEvent> {
    alt((
        map(clocking_event, |x| CoverageEvent::ClockingEvent(x)),
        coverage_event_sample,
        coverage_event_at,
    ))(s)
}

#[parser]
pub fn coverage_event_sample(s: Span) -> IResult<Span, CoverageEvent> {
    let (s, a) = keyword("with")(s)?;
    let (s, b) = keyword("function")(s)?;
    let (s, c) = keyword("sample")(s)?;
    let (s, d) = paren(opt(tf_port_list))(s)?;
    Ok((
        s,
        CoverageEvent::Sample(CoverageEventSample {
            nodes: (a, b, c, d),
        }),
    ))
}

#[parser]
pub fn coverage_event_at(s: Span) -> IResult<Span, CoverageEvent> {
    let (s, a) = symbol("@@")(s)?;
    let (s, b) = paren(block_event_expression)(s)?;
    Ok((s, CoverageEvent::At(CoverageEventAt { nodes: (a, b) })))
}

#[parser]
pub fn block_event_expression(s: Span) -> IResult<Span, BlockEventExpression> {
    alt((
        block_event_expression_or,
        block_event_expression_begin,
        block_event_expression_end,
    ))(s)
}

#[parser(MaybeRecursive)]
pub fn block_event_expression_or(s: Span) -> IResult<Span, BlockEventExpression> {
    let (s, a) = block_event_expression(s)?;
    let (s, b) = keyword("or")(s)?;
    let (s, c) = block_event_expression(s)?;
    Ok((
        s,
        BlockEventExpression::Or(Box::new(BlockEventExpressionOr { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn block_event_expression_begin(s: Span) -> IResult<Span, BlockEventExpression> {
    let (s, a) = keyword("begin")(s)?;
    let (s, b) = hierarchical_btf_identifier(s)?;
    Ok((
        s,
        BlockEventExpression::Begin(BlockEventExpressionBegin { nodes: (a, b) }),
    ))
}

#[parser]
pub fn block_event_expression_end(s: Span) -> IResult<Span, BlockEventExpression> {
    let (s, a) = keyword("end")(s)?;
    let (s, b) = hierarchical_btf_identifier(s)?;
    Ok((
        s,
        BlockEventExpression::End(BlockEventExpressionEnd { nodes: (a, b) }),
    ))
}

#[parser]
pub fn hierarchical_btf_identifier(s: Span) -> IResult<Span, HierarchicalBtfIdentifier> {
    alt((
        map(hierarchical_tf_identifier, |x| {
            HierarchicalBtfIdentifier::HierarchicalTfIdentifier(x)
        }),
        map(hierarchical_block_identifier, |x| {
            HierarchicalBtfIdentifier::HierarchicalBlockIdentifier(x)
        }),
        hierarchical_btf_identifier_method,
    ))(s)
}

#[parser]
pub fn hierarchical_btf_identifier_method(s: Span) -> IResult<Span, HierarchicalBtfIdentifier> {
    let (s, a) = opt(hierarchical_identifier_or_class_scope)(s)?;
    let (s, b) = method_identifier(s)?;
    Ok((
        s,
        HierarchicalBtfIdentifier::Method(HierarchicalBtfIdentifierMethod { nodes: (a, b) }),
    ))
}

#[parser]
pub fn hierarchical_identifier_or_class_scope(
    s: Span,
) -> IResult<Span, HierarchicalIdentifierOrClassScope> {
    alt((
        map(pair(hierarchical_identifier, symbol(".")), |x| {
            HierarchicalIdentifierOrClassScope::HierarchicalIdentifier(x)
        }),
        map(class_scope, |x| {
            HierarchicalIdentifierOrClassScope::ClassScope(x)
        }),
    ))(s)
}

#[parser(Ambiguous)]
pub fn cover_point(s: Span) -> IResult<Span, CoverPoint> {
    let (s, a) = opt(triple(
        ambiguous_opt(data_type_or_implicit),
        cover_point_identifier,
        symbol(":"),
    ))(s)?;
    let (s, b) = keyword("coverpoint")(s)?;
    let (s, c) = expression(s)?;
    let (s, d) = opt(pair(keyword("iff"), paren(expression)))(s)?;
    let (s, e) = bins_or_empty(s)?;
    Ok((
        s,
        CoverPoint {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[parser]
pub fn bins_or_empty(s: Span) -> IResult<Span, BinsOrEmpty> {
    alt((
        bins_or_empty_non_empty,
        map(symbol(";"), |x| BinsOrEmpty::Empty(x)),
    ))(s)
}

#[parser]
pub fn bins_or_empty_non_empty(s: Span) -> IResult<Span, BinsOrEmpty> {
    let (s, a) = brace(pair(
        many0(attribute_instance),
        many0(pair(bins_or_options, symbol(";"))),
    ))(s)?;
    Ok((
        s,
        BinsOrEmpty::NonEmpty(BinsOrEmptyNonEmpty { nodes: (a,) }),
    ))
}

#[parser]
pub fn bins_or_options(s: Span) -> IResult<Span, BinsOrOptions> {
    alt((
        map(coverage_option, |x| BinsOrOptions::CoverageOption(x)),
        bins_or_options_covergroup,
        bins_or_options_cover_point,
        bins_or_options_set_covergroup,
        bins_or_options_trans_list,
        bins_or_options_default,
        bins_or_options_default_sequence,
    ))(s)
}

#[parser]
pub fn bins_or_options_covergroup(s: Span) -> IResult<Span, BinsOrOptions> {
    let (s, a) = opt(wildcard)(s)?;
    let (s, b) = bins_keyword(s)?;
    let (s, c) = bin_identifier(s)?;
    let (s, d) = opt(bracket(opt(covergroup_expression)))(s)?;
    let (s, e) = symbol("=")(s)?;
    let (s, f) = brace(covergroup_range_list)(s)?;
    let (s, g) = opt(pair(keyword("with"), paren(with_covergroup_expression)))(s)?;
    let (s, h) = opt(pair(keyword("iff"), paren(expression)))(s)?;
    Ok((
        s,
        BinsOrOptions::Covergroup(BinsOrOptionsCovergroup {
            nodes: (a, b, c, d, e, f, g, h),
        }),
    ))
}

#[parser]
pub fn wildcard(s: Span) -> IResult<Span, Wildcard> {
    let (s, a) = keyword("wildcard")(s)?;
    Ok((s, Wildcard { nodes: (a,) }))
}

#[parser]
pub fn bins_or_options_cover_point(s: Span) -> IResult<Span, BinsOrOptions> {
    let (s, a) = opt(wildcard)(s)?;
    let (s, b) = bins_keyword(s)?;
    let (s, c) = bin_identifier(s)?;
    let (s, d) = opt(bracket(opt(covergroup_expression)))(s)?;
    let (s, e) = symbol("=")(s)?;
    let (s, f) = cover_point_identifier(s)?;
    let (s, g) = keyword("with")(s)?;
    let (s, h) = paren(with_covergroup_expression)(s)?;
    let (s, i) = opt(pair(keyword("iff"), paren(expression)))(s)?;
    Ok((
        s,
        BinsOrOptions::CoverPoint(BinsOrOptionsCoverPoint {
            nodes: (a, b, c, d, e, f, g, h, i),
        }),
    ))
}

#[parser]
pub fn bins_or_options_set_covergroup(s: Span) -> IResult<Span, BinsOrOptions> {
    let (s, a) = opt(wildcard)(s)?;
    let (s, b) = bins_keyword(s)?;
    let (s, c) = bin_identifier(s)?;
    let (s, d) = opt(bracket(opt(covergroup_expression)))(s)?;
    let (s, e) = symbol("=")(s)?;
    let (s, f) = set_covergroup_expression(s)?;
    let (s, g) = opt(pair(keyword("iff"), paren(expression)))(s)?;
    Ok((
        s,
        BinsOrOptions::SetCovergroup(BinsOrOptionsSetCovergroup {
            nodes: (a, b, c, d, e, f, g),
        }),
    ))
}

#[parser]
pub fn bins_or_options_trans_list(s: Span) -> IResult<Span, BinsOrOptions> {
    let (s, a) = opt(wildcard)(s)?;
    let (s, b) = bins_keyword(s)?;
    let (s, c) = bin_identifier(s)?;
    let (s, d) = opt(pair(symbol("["), symbol("]")))(s)?;
    let (s, e) = symbol("=")(s)?;
    let (s, f) = trans_list(s)?;
    let (s, g) = opt(pair(keyword("iff"), paren(expression)))(s)?;
    Ok((
        s,
        BinsOrOptions::TransList(BinsOrOptionsTransList {
            nodes: (a, b, c, d, e, f, g),
        }),
    ))
}

#[parser]
pub fn bins_or_options_default(s: Span) -> IResult<Span, BinsOrOptions> {
    let (s, a) = bins_keyword(s)?;
    let (s, b) = bin_identifier(s)?;
    let (s, c) = opt(bracket(opt(covergroup_expression)))(s)?;
    let (s, d) = symbol("=")(s)?;
    let (s, e) = keyword("default")(s)?;
    let (s, f) = opt(pair(keyword("iff"), paren(expression)))(s)?;
    Ok((
        s,
        BinsOrOptions::Default(BinsOrOptionsDefault {
            nodes: (a, b, c, d, e, f),
        }),
    ))
}

#[parser]
pub fn bins_or_options_default_sequence(s: Span) -> IResult<Span, BinsOrOptions> {
    let (s, a) = bins_keyword(s)?;
    let (s, b) = bin_identifier(s)?;
    let (s, c) = symbol("=")(s)?;
    let (s, d) = keyword("default")(s)?;
    let (s, e) = keyword("sequence")(s)?;
    let (s, f) = opt(pair(keyword("iff"), paren(expression)))(s)?;
    Ok((
        s,
        BinsOrOptions::DefaultSequence(BinsOrOptionsDefaultSequence {
            nodes: (a, b, c, d, e, f),
        }),
    ))
}

#[parser]
pub fn bins_keyword(s: Span) -> IResult<Span, BinsKeyword> {
    alt((
        map(keyword("bins"), |x| BinsKeyword::Bins(x)),
        map(keyword("illegal_bins"), |x| BinsKeyword::IllegalBins(x)),
        map(keyword("ignore_bins"), |x| BinsKeyword::IgnoreBins(x)),
    ))(s)
}

#[parser]
pub fn trans_list(s: Span) -> IResult<Span, TransList> {
    let (s, a) = list(symbol(","), paren(trans_set))(s)?;
    Ok((s, TransList { nodes: (a,) }))
}

#[parser(MaybeRecursive)]
pub fn trans_set(s: Span) -> IResult<Span, TransSet> {
    let (s, a) = list(symbol("=>"), trans_range_list)(s)?;
    Ok((s, TransSet { nodes: (a,) }))
}

#[parser]
pub fn trans_range_list(s: Span) -> IResult<Span, TransRangeList> {
    alt((
        map(trans_item, |x| TransRangeList::TransItem(x)),
        trans_range_list_asterisk,
        trans_range_list_arrow,
        trans_range_list_equal,
    ))(s)
}

#[parser(MaybeRecursive)]
pub fn trans_range_list_asterisk(s: Span) -> IResult<Span, TransRangeList> {
    let (s, a) = trans_item(s)?;
    let (s, b) = bracket(pair(symbol("*"), repeat_range))(s)?;
    Ok((
        s,
        TransRangeList::Asterisk(TransRangeListAsterisk { nodes: (a, b) }),
    ))
}

#[parser(MaybeRecursive)]
pub fn trans_range_list_arrow(s: Span) -> IResult<Span, TransRangeList> {
    let (s, a) = trans_item(s)?;
    let (s, b) = bracket(pair(symbol("->"), repeat_range))(s)?;
    Ok((
        s,
        TransRangeList::Arrow(TransRangeListArrow { nodes: (a, b) }),
    ))
}

#[parser(MaybeRecursive)]
pub fn trans_range_list_equal(s: Span) -> IResult<Span, TransRangeList> {
    let (s, a) = trans_item(s)?;
    let (s, b) = bracket(pair(symbol("="), repeat_range))(s)?;
    Ok((
        s,
        TransRangeList::Equal(TransRangeListEqual { nodes: (a, b) }),
    ))
}

#[parser]
pub fn trans_item(s: Span) -> IResult<Span, TransItem> {
    let (s, a) = covergroup_range_list(s)?;
    Ok((s, TransItem { nodes: (a,) }))
}

#[parser]
pub fn repeat_range(s: Span) -> IResult<Span, RepeatRange> {
    alt((
        map(covergroup_expression, |x| {
            RepeatRange::CovergroupExpression(x)
        }),
        repeat_range_binary,
    ))(s)
}

#[parser(MaybeRecursive)]
pub fn repeat_range_binary(s: Span) -> IResult<Span, RepeatRange> {
    let (s, a) = covergroup_expression(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = covergroup_expression(s)?;
    Ok((
        s,
        RepeatRange::Binary(RepeatRangeBinary { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn cover_cross(s: Span) -> IResult<Span, CoverCross> {
    let (s, a) = opt(pair(cross_identifier, symbol(":")))(s)?;
    let (s, b) = keyword("cross")(s)?;
    let (s, c) = list_of_cross_items(s)?;
    let (s, d) = opt(pair(keyword("iff"), paren(expression)))(s)?;
    let (s, e) = cross_body(s)?;
    Ok((
        s,
        CoverCross {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[parser]
pub fn list_of_cross_items(s: Span) -> IResult<Span, ListOfCrossItems> {
    let (s, a) = cross_item(s)?;
    let (s, b) = list(symbol(","), cross_item)(s)?;
    Ok((s, ListOfCrossItems { nodes: (a, b) }))
}

#[parser]
pub fn cross_item(s: Span) -> IResult<Span, CrossItem> {
    alt((
        map(cover_point_identifier, |x| {
            CrossItem::CoverPointIdentifier(x)
        }),
        map(variable_identifier, |x| CrossItem::VariableIdentifier(x)),
    ))(s)
}

#[parser]
pub fn cross_body(s: Span) -> IResult<Span, CrossBody> {
    alt((
        cross_body_non_empty,
        map(symbol(";"), |x| CrossBody::Empty(x)),
    ))(s)
}

#[parser]
pub fn cross_body_non_empty(s: Span) -> IResult<Span, CrossBody> {
    let (s, a) = brace(many0(pair(cross_body_item, symbol(";"))))(s)?;
    Ok((s, CrossBody::NonEmpty(CrossBodyNonEmpty { nodes: (a,) })))
}

#[parser]
pub fn cross_body_item(s: Span) -> IResult<Span, CrossBodyItem> {
    alt((
        map(function_declaration, |x| {
            CrossBodyItem::FunctionDeclaration(x)
        }),
        map(pair(bins_selection_or_option, symbol(";")), |x| {
            CrossBodyItem::BinsSelectionOrOption(x)
        }),
    ))(s)
}

#[parser]
pub fn bins_selection_or_option(s: Span) -> IResult<Span, BinsSelectionOrOption> {
    alt((
        bins_selection_or_option_coverage,
        bins_selection_or_option_bins,
    ))(s)
}

#[parser]
pub fn bins_selection_or_option_coverage(s: Span) -> IResult<Span, BinsSelectionOrOption> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = coverage_option(s)?;
    Ok((
        s,
        BinsSelectionOrOption::Coverage(BinsSelectionOrOptionCoverage { nodes: (a, b) }),
    ))
}

#[parser]
pub fn bins_selection_or_option_bins(s: Span) -> IResult<Span, BinsSelectionOrOption> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = bins_selection(s)?;
    Ok((
        s,
        BinsSelectionOrOption::Bins(BinsSelectionOrOptionBins { nodes: (a, b) }),
    ))
}

#[parser]
pub fn bins_selection(s: Span) -> IResult<Span, BinsSelection> {
    let (s, a) = bins_keyword(s)?;
    let (s, b) = bin_identifier(s)?;
    let (s, c) = symbol("=")(s)?;
    let (s, d) = select_expression(s)?;
    let (s, e) = opt(pair(keyword("iff"), paren(expression)))(s)?;
    Ok((
        s,
        BinsSelection {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[parser]
pub fn select_expression(s: Span) -> IResult<Span, SelectExpression> {
    alt((
        map(select_condition, |x| SelectExpression::SelectCondition(x)),
        select_expression_not,
        select_expression_and,
        select_expression_or,
        select_expression_paren,
        select_expression_with,
        map(cross_identifier, |x| SelectExpression::CrossIdentifier(x)),
        select_expression_cross_set,
    ))(s)
}

#[parser]
pub fn select_expression_not(s: Span) -> IResult<Span, SelectExpression> {
    let (s, a) = symbol("!")(s)?;
    let (s, b) = select_condition(s)?;
    Ok((
        s,
        SelectExpression::Not(SelectExpressionNot { nodes: (a, b) }),
    ))
}

#[parser(MaybeRecursive)]
pub fn select_expression_and(s: Span) -> IResult<Span, SelectExpression> {
    let (s, a) = select_expression(s)?;
    let (s, b) = symbol("&&")(s)?;
    let (s, c) = select_expression(s)?;
    Ok((
        s,
        SelectExpression::And(Box::new(SelectExpressionAnd { nodes: (a, b, c) })),
    ))
}

#[parser(MaybeRecursive)]
pub fn select_expression_or(s: Span) -> IResult<Span, SelectExpression> {
    let (s, a) = select_expression(s)?;
    let (s, b) = symbol("||")(s)?;
    let (s, c) = select_expression(s)?;
    Ok((
        s,
        SelectExpression::Or(Box::new(SelectExpressionOr { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn select_expression_paren(s: Span) -> IResult<Span, SelectExpression> {
    let (s, a) = paren(select_expression)(s)?;
    Ok((
        s,
        SelectExpression::Paren(Box::new(SelectExpressionParen { nodes: (a,) })),
    ))
}

#[parser(MaybeRecursive)]
pub fn select_expression_with(s: Span) -> IResult<Span, SelectExpression> {
    let (s, a) = select_expression(s)?;
    let (s, b) = keyword("with")(s)?;
    let (s, c) = paren(with_covergroup_expression)(s)?;
    let (s, d) = opt(pair(keyword("matches"), integer_covergroup_expression))(s)?;
    Ok((
        s,
        SelectExpression::With(Box::new(SelectExpressionWith {
            nodes: (a, b, c, d),
        })),
    ))
}

#[parser(MaybeRecursive)]
pub fn select_expression_cross_set(s: Span) -> IResult<Span, SelectExpression> {
    let (s, a) = cross_set_expression(s)?;
    let (s, b) = opt(pair(keyword("matches"), integer_covergroup_expression))(s)?;
    Ok((
        s,
        SelectExpression::CrossSet(SelectExpressionCrossSet { nodes: (a, b) }),
    ))
}

#[parser]
pub fn select_condition(s: Span) -> IResult<Span, SelectCondition> {
    let (s, a) = keyword("binsof")(s)?;
    let (s, b) = paren(bins_expression)(s)?;
    let (s, c) = opt(pair(keyword("intersect"), brace(covergroup_range_list)))(s)?;
    Ok((s, SelectCondition { nodes: (a, b, c) }))
}

#[parser]
pub fn bins_expression(s: Span) -> IResult<Span, BinsExpression> {
    alt((
        map(variable_identifier, |x| {
            BinsExpression::VariableIdentifier(x)
        }),
        bins_expression_cover_point,
    ))(s)
}

#[parser]
pub fn bins_expression_cover_point(s: Span) -> IResult<Span, BinsExpression> {
    let (s, a) = cover_point_identifier(s)?;
    let (s, b) = opt(pair(symbol("."), bin_identifier))(s)?;
    Ok((
        s,
        BinsExpression::CoverPoint(BinsExpressionCoverPoint { nodes: (a, b) }),
    ))
}

#[parser(MaybeRecursive)]
pub fn covergroup_range_list(s: Span) -> IResult<Span, CovergroupRangeList> {
    let (s, a) = list(symbol(","), covergroup_value_range)(s)?;
    Ok((s, CovergroupRangeList { nodes: (a,) }))
}

#[parser]
pub fn covergroup_value_range(s: Span) -> IResult<Span, CovergroupValueRange> {
    alt((
        map(covergroup_expression, |x| {
            CovergroupValueRange::CovergroupExpression(x)
        }),
        covergroup_value_range_binary,
    ))(s)
}

#[parser]
pub fn covergroup_value_range_binary(s: Span) -> IResult<Span, CovergroupValueRange> {
    let (s, a) = bracket(triple(
        covergroup_expression,
        symbol(":"),
        covergroup_expression,
    ))(s)?;
    Ok((
        s,
        CovergroupValueRange::Binary(CovergroupValueRangeBinary { nodes: (a,) }),
    ))
}

#[parser]
pub fn with_covergroup_expression(s: Span) -> IResult<Span, WithCovergroupExpression> {
    let (s, a) = covergroup_expression(s)?;
    Ok((s, WithCovergroupExpression { nodes: (a,) }))
}

#[parser]
pub fn set_covergroup_expression(s: Span) -> IResult<Span, SetCovergroupExpression> {
    let (s, a) = covergroup_expression(s)?;
    Ok((s, SetCovergroupExpression { nodes: (a,) }))
}

#[parser]
pub fn integer_covergroup_expression(s: Span) -> IResult<Span, IntegerCovergroupExpression> {
    let (s, a) = covergroup_expression(s)?;
    Ok((s, IntegerCovergroupExpression { nodes: (a,) }))
}

#[parser]
pub fn cross_set_expression(s: Span) -> IResult<Span, CrossSetExpression> {
    let (s, a) = covergroup_expression(s)?;
    Ok((s, CrossSetExpression { nodes: (a,) }))
}

#[parser]
pub fn covergroup_expression(s: Span) -> IResult<Span, CovergroupExpression> {
    let (s, a) = expression(s)?;
    Ok((s, CovergroupExpression { nodes: (a,) }))
}

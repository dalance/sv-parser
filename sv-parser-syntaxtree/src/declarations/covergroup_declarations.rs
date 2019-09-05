use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
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

#[derive(Clone, Debug, PartialEq, Node)]
pub enum CoverageSpecOrOption {
    Spec(Box<CoverageSpecOrOptionSpec>),
    Option(Box<CoverageSpecOrOptionOption>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CoverageSpecOrOptionSpec {
    pub nodes: (Vec<AttributeInstance>, CoverageSpec),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CoverageSpecOrOptionOption {
    pub nodes: (Vec<AttributeInstance>, CoverageOption, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum CoverageOption {
    Option(Box<CoverageOptionOption>),
    TypeOption(Box<CoverageOptionTypeOption>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CoverageOptionOption {
    pub nodes: (Keyword, Symbol, MemberIdentifier, Symbol, Expression),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CoverageOptionTypeOption {
    pub nodes: (
        Keyword,
        Symbol,
        MemberIdentifier,
        Symbol,
        ConstantExpression,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum CoverageSpec {
    CoverPoint(Box<CoverPoint>),
    CoverCross(Box<CoverCross>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum CoverageEvent {
    ClockingEvent(Box<ClockingEvent>),
    Sample(Box<CoverageEventSample>),
    At(Box<CoverageEventAt>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CoverageEventSample {
    pub nodes: (Keyword, Keyword, Keyword, Paren<Option<TfPortList>>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CoverageEventAt {
    pub nodes: (Symbol, Paren<BlockEventExpression>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum BlockEventExpression {
    Or(Box<BlockEventExpressionOr>),
    Begin(Box<BlockEventExpressionBegin>),
    End(Box<BlockEventExpressionEnd>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct BlockEventExpressionOr {
    pub nodes: (BlockEventExpression, Keyword, BlockEventExpression),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct BlockEventExpressionBegin {
    pub nodes: (Keyword, HierarchicalBtfIdentifier),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct BlockEventExpressionEnd {
    pub nodes: (Keyword, HierarchicalBtfIdentifier),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum HierarchicalBtfIdentifier {
    HierarchicalTfIdentifier(Box<HierarchicalTfIdentifier>),
    HierarchicalBlockIdentifier(Box<HierarchicalBlockIdentifier>),
    Method(Box<HierarchicalBtfIdentifierMethod>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct HierarchicalBtfIdentifierMethod {
    pub nodes: (Option<HierarchicalIdentifierOrClassScope>, MethodIdentifier),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum HierarchicalIdentifierOrClassScope {
    HierarchicalIdentifier(Box<(HierarchicalIdentifier, Symbol)>),
    ClassScope(Box<ClassScope>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CoverPoint {
    pub nodes: (
        Option<(Option<DataTypeOrImplicit>, CoverPointIdentifier, Symbol)>,
        Keyword,
        Expression,
        Option<(Keyword, Paren<Expression>)>,
        BinsOrEmpty,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum BinsOrEmpty {
    NonEmpty(Box<BinsOrEmptyNonEmpty>),
    Empty(Box<Symbol>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct BinsOrEmptyNonEmpty {
    pub nodes: (Brace<(Vec<AttributeInstance>, Vec<(BinsOrOptions, Symbol)>)>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum BinsOrOptions {
    CoverageOption(Box<CoverageOption>),
    Covergroup(Box<BinsOrOptionsCovergroup>),
    CoverPoint(Box<BinsOrOptionsCoverPoint>),
    SetCovergroup(Box<BinsOrOptionsSetCovergroup>),
    TransList(Box<BinsOrOptionsTransList>),
    Default(Box<BinsOrOptionsDefault>),
    DefaultSequence(Box<BinsOrOptionsDefaultSequence>),
}

#[derive(Clone, Debug, PartialEq, Node)]
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

#[derive(Clone, Debug, PartialEq, Node)]
pub struct Wildcard {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, PartialEq, Node)]
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

#[derive(Clone, Debug, PartialEq, Node)]
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

#[derive(Clone, Debug, PartialEq, Node)]
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

#[derive(Clone, Debug, PartialEq, Node)]
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

#[derive(Clone, Debug, PartialEq, Node)]
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

#[derive(Clone, Debug, PartialEq, Node)]
pub enum BinsKeyword {
    Bins(Box<Keyword>),
    IllegalBins(Box<Keyword>),
    IgnoreBins(Box<Keyword>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct TransList {
    pub nodes: (List<Symbol, Paren<TransSet>>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct TransSet {
    pub nodes: (List<Symbol, TransRangeList>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum TransRangeList {
    TransItem(Box<TransItem>),
    Asterisk(Box<TransRangeListAsterisk>),
    Arrow(Box<TransRangeListArrow>),
    Equal(Box<TransRangeListEqual>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct TransRangeListAsterisk {
    pub nodes: (TransItem, Bracket<(Symbol, RepeatRange)>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct TransRangeListArrow {
    pub nodes: (TransItem, Bracket<(Symbol, RepeatRange)>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct TransRangeListEqual {
    pub nodes: (TransItem, Bracket<(Symbol, RepeatRange)>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct TransItem {
    pub nodes: (CovergroupRangeList,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum RepeatRange {
    CovergroupExpression(Box<CovergroupExpression>),
    Binary(Box<RepeatRangeBinary>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct RepeatRangeBinary {
    pub nodes: (CovergroupExpression, Symbol, CovergroupExpression),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CoverCross {
    pub nodes: (
        Option<(CrossIdentifier, Symbol)>,
        Keyword,
        ListOfCrossItems,
        Option<(Keyword, Paren<Expression>)>,
        CrossBody,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ListOfCrossItems {
    pub nodes: (CrossItem, Symbol, List<Symbol, CrossItem>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum CrossItem {
    CoverPointIdentifier(Box<CoverPointIdentifier>),
    VariableIdentifier(Box<VariableIdentifier>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum CrossBody {
    NonEmpty(Box<CrossBodyNonEmpty>),
    Empty(Box<Symbol>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CrossBodyNonEmpty {
    pub nodes: (Brace<Vec<CrossBodyItem>>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum CrossBodyItem {
    FunctionDeclaration(Box<FunctionDeclaration>),
    BinsSelectionOrOption(Box<(BinsSelectionOrOption, Symbol)>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum BinsSelectionOrOption {
    Coverage(Box<BinsSelectionOrOptionCoverage>),
    Bins(Box<BinsSelectionOrOptionBins>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct BinsSelectionOrOptionCoverage {
    pub nodes: (Vec<AttributeInstance>, CoverageOption),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct BinsSelectionOrOptionBins {
    pub nodes: (Vec<AttributeInstance>, BinsSelection),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct BinsSelection {
    pub nodes: (
        BinsKeyword,
        BinIdentifier,
        Symbol,
        SelectExpression,
        Option<(Keyword, Paren<Expression>)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum SelectExpression {
    SelectCondition(Box<SelectCondition>),
    Not(Box<SelectExpressionNot>),
    And(Box<SelectExpressionAnd>),
    Or(Box<SelectExpressionOr>),
    Paren(Box<SelectExpressionParen>),
    With(Box<SelectExpressionWith>),
    CrossIdentifier(Box<CrossIdentifier>),
    CrossSet(Box<SelectExpressionCrossSet>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SelectExpressionNot {
    pub nodes: (Symbol, SelectCondition),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SelectExpressionAnd {
    pub nodes: (SelectExpression, Symbol, SelectExpression),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SelectExpressionOr {
    pub nodes: (SelectExpression, Symbol, SelectExpression),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SelectExpressionParen {
    pub nodes: (Paren<SelectExpression>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SelectExpressionWith {
    pub nodes: (
        SelectExpression,
        Keyword,
        Paren<WithCovergroupExpression>,
        Option<(Keyword, IntegerCovergroupExpression)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SelectExpressionCrossSet {
    pub nodes: (
        CrossSetExpression,
        Option<(Keyword, IntegerCovergroupExpression)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SelectCondition {
    pub nodes: (
        Keyword,
        Paren<BinsExpression>,
        Option<(Keyword, Brace<CovergroupRangeList>)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum BinsExpression {
    VariableIdentifier(Box<VariableIdentifier>),
    CoverPoint(Box<BinsExpressionCoverPoint>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct BinsExpressionCoverPoint {
    pub nodes: (CoverPointIdentifier, Option<(Symbol, BinIdentifier)>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CovergroupRangeList {
    pub nodes: (List<Symbol, CovergroupValueRange>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum CovergroupValueRange {
    CovergroupExpression(Box<CovergroupExpression>),
    Binary(Box<CovergroupValueRangeBinary>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CovergroupValueRangeBinary {
    pub nodes: (Bracket<(CovergroupExpression, Symbol, CovergroupExpression)>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct WithCovergroupExpression {
    pub nodes: (CovergroupExpression,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SetCovergroupExpression {
    pub nodes: (CovergroupExpression,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct IntegerCovergroupExpression {
    pub nodes: (CovergroupExpression,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CrossSetExpression {
    pub nodes: (CovergroupExpression,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CovergroupExpression {
    pub nodes: (Expression,),
}

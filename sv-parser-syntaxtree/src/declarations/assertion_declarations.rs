use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ConcurrentAssertionItem {
    Statement(Box<ConcurrentAssertionItemStatement>),
    CheckerInstantiation(Box<CheckerInstantiation>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ConcurrentAssertionItemStatement {
    pub nodes: (
        Option<(BlockIdentifier, Symbol)>,
        ConcurrentAssertionStatement,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ConcurrentAssertionStatement {
    AssertPropertyStatement(Box<AssertPropertyStatement>),
    AssumePropertyStatement(Box<AssumePropertyStatement>),
    CoverPropertyStatement(Box<CoverPropertyStatement>),
    CoverSequenceStatement(Box<CoverSequenceStatement>),
    RestrictPropertyStatement(Box<RestrictPropertyStatement>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct AssertPropertyStatement {
    pub nodes: (Keyword, Keyword, Paren<PropertySpec>, ActionBlock),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct AssumePropertyStatement {
    pub nodes: (Keyword, Keyword, Paren<PropertySpec>, ActionBlock),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CoverPropertyStatement {
    pub nodes: (Keyword, Keyword, Paren<PropertySpec>, StatementOrNull),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ExpectPropertyStatement {
    pub nodes: (Keyword, Paren<PropertySpec>, ActionBlock),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CoverSequenceStatement {
    pub nodes: (
        Keyword,
        Keyword,
        Paren<(
            Option<ClockingEvent>,
            Option<(Keyword, Keyword, Paren<ExpressionOrDist>)>,
            SequenceExpr,
        )>,
        StatementOrNull,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct RestrictPropertyStatement {
    pub nodes: (Keyword, Keyword, Paren<PropertySpec>, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyInstance {
    pub nodes: (
        PsOrHierarchicalPropertyIdentifier,
        Option<Paren<Option<PropertyListOfArguments>>>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum PropertyListOfArguments {
    Ordered(Box<PropertyListOfArgumentsOrdered>),
    Named(Box<PropertyListOfArgumentsNamed>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyListOfArgumentsOrdered {
    pub nodes: (
        List<Symbol, Option<PropertyActualArg>>,
        Vec<(Symbol, Symbol, Identifier, Paren<Option<PropertyActualArg>>)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyListOfArgumentsNamed {
    pub nodes: (List<Symbol, (Symbol, Identifier, Paren<Option<PropertyActualArg>>)>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum PropertyActualArg {
    PropertyExpr(Box<PropertyExpr>),
    SequenceActualArg(Box<SequenceActualArg>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum AssertionItemDeclaration {
    PropertyDeclaration(Box<PropertyDeclaration>),
    SequenceDeclaration(Box<SequenceDeclaration>),
    LetDeclaration(Box<LetDeclaration>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyDeclaration {
    pub nodes: (
        Keyword,
        PropertyIdentifier,
        Option<Paren<Option<PropertyPortList>>>,
        Symbol,
        Vec<AssertionVariableDeclaration>,
        PropertySpec,
        Option<Symbol>,
        Keyword,
        Option<(Symbol, PropertyIdentifier)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyPortList {
    pub nodes: (List<Symbol, PropertyPortItem>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyPortItem {
    pub nodes: (
        Vec<AttributeInstance>,
        Option<(Keyword, Option<PropertyLvarPortDirection>)>,
        PropertyFormalType,
        FormalPortIdentifier,
        Vec<VariableDimension>,
        Option<(Symbol, PropertyActualArg)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum PropertyLvarPortDirection {
    Input(Box<Keyword>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum PropertyFormalType {
    SequenceFormalType(Box<SequenceFormalType>),
    Property(Box<Keyword>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertySpec {
    pub nodes: (
        Option<ClockingEvent>,
        Option<(Keyword, Keyword, Paren<ExpressionOrDist>)>,
        PropertyExpr,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum PropertyExpr {
    SequenceExpr(Box<SequenceExpr>),
    Strong(Box<PropertyExprStrong>),
    Weak(Box<PropertyExprWeak>),
    Paren(Box<PropertyExprParen>),
    Not(Box<PropertyExprNot>),
    BinaryProperty(Box<PropertyExprBinaryProperty>),
    BinarySequence(Box<PropertyExprBinarySequence>),
    If(Box<PropertyExprIf>),
    Case(Box<PropertyExprCase>),
    Nexttime(Box<PropertyExprNexttime>),
    SNexttime(Box<PropertyExprSNexttime>),
    Always(Box<PropertyExprAlways>),
    SAlways(Box<PropertyExprSAlways>),
    Eventually(Box<PropertyExprEventually>),
    SEventually(Box<PropertyExprSEventually>),
    AcceptOn(Box<PropertyExprAcceptOn>),
    RejectOn(Box<PropertyExprRejectOn>),
    SyncAcceptOn(Box<PropertyExprSyncAcceptOn>),
    SyncRejectOn(Box<PropertyExprSyncRejectOn>),
    PropertyInstance(Box<PropertyInstance>),
    ClockingEvent(Box<PropertyExprClockingEvent>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyExprStrong {
    pub nodes: (Keyword, Paren<SequenceExpr>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyExprWeak {
    pub nodes: (Keyword, Paren<SequenceExpr>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyExprParen {
    pub nodes: (Paren<PropertyExpr>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyExprNot {
    pub nodes: (Keyword, PropertyExpr),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyExprBinaryProperty {
    pub nodes: (PropertyExpr, Keyword, PropertyExpr),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyExprBinarySequence {
    pub nodes: (SequenceExpr, Symbol, PropertyExpr),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyExprIf {
    pub nodes: (
        Keyword,
        Paren<ExpressionOrDist>,
        PropertyExpr,
        Option<(Keyword, PropertyExpr)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyExprCase {
    pub nodes: (
        Keyword,
        Paren<ExpressionOrDist>,
        PropertyCaseItem,
        Vec<PropertyCaseItem>,
        Keyword,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyExprNexttime {
    pub nodes: (Keyword, Option<Bracket<ConstantExpression>>, PropertyExpr),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyExprSNexttime {
    pub nodes: (Keyword, Option<Bracket<ConstantExpression>>, PropertyExpr),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyExprAlways {
    pub nodes: (
        Keyword,
        Option<Bracket<CycleDelayConstRangeExpression>>,
        PropertyExpr,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyExprSAlways {
    pub nodes: (
        Keyword,
        Bracket<CycleDelayConstRangeExpression>,
        PropertyExpr,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyExprEventually {
    pub nodes: (Keyword, Bracket<ConstantRange>, PropertyExpr),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyExprSEventually {
    pub nodes: (
        Keyword,
        Option<Bracket<CycleDelayConstRangeExpression>>,
        PropertyExpr,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyExprAcceptOn {
    pub nodes: (Keyword, Paren<ExpressionOrDist>, PropertyExpr),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyExprRejectOn {
    pub nodes: (Keyword, Paren<ExpressionOrDist>, PropertyExpr),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyExprSyncAcceptOn {
    pub nodes: (Keyword, Paren<ExpressionOrDist>, PropertyExpr),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyExprSyncRejectOn {
    pub nodes: (Keyword, Paren<ExpressionOrDist>, PropertyExpr),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyExprClockingEvent {
    pub nodes: (ClockingEvent, PropertyExpr),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum PropertyCaseItem {
    Nondefault(Box<PropertyCaseItemNondefault>),
    Default(Box<PropertyCaseItemDefault>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyCaseItemNondefault {
    pub nodes: (List<Symbol, ExpressionOrDist>, Symbol, PropertyExpr, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PropertyCaseItemDefault {
    pub nodes: (Keyword, Option<Symbol>, PropertyExpr, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SequenceDeclaration {
    pub nodes: (
        Keyword,
        SequenceIdentifier,
        Option<Paren<Option<SequencePortList>>>,
        Symbol,
        Vec<AssertionVariableDeclaration>,
        SequenceExpr,
        Option<Symbol>,
        Keyword,
        Option<(Symbol, SequenceIdentifier)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SequencePortList {
    pub nodes: (List<Symbol, SequencePortItem>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SequencePortItem {
    pub nodes: (
        Vec<AttributeInstance>,
        Option<(Keyword, Option<SequenceLvarPortDirection>)>,
        SequenceFormalType,
        FormalPortIdentifier,
        Vec<VariableDimension>,
        Option<(Symbol, SequenceActualArg)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum SequenceLvarPortDirection {
    Input(Box<Keyword>),
    Inout(Box<Keyword>),
    Output(Box<Keyword>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum SequenceFormalType {
    DataTypeOrImplicit(Box<DataTypeOrImplicit>),
    Sequence(Box<Keyword>),
    Untyped(Box<Keyword>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum SequenceExpr {
    CycleDelayExpr(Box<SequenceExprCycleDelayExpr>),
    ExprCycleDelayExpr(Box<SequenceExprExprCycleDelayExpr>),
    Expression(Box<SequenceExprExpression>),
    Instance(Box<SequenceExprInstance>),
    Paren(Box<SequenceExprParen>),
    Binary(Box<SequenceExprBinary>),
    FirstMatch(Box<SequenceExprFirstMatch>),
    Throughout(Box<SequenceExprThroughout>),
    ClockingEvent(Box<SequenceExprClockingEvent>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SequenceExprCycleDelayExpr {
    pub nodes: (
        CycleDelayRange,
        SequenceExpr,
        Vec<(CycleDelayRange, SequenceExpr)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SequenceExprExprCycleDelayExpr {
    pub nodes: (
        SequenceExpr,
        CycleDelayRange,
        SequenceExpr,
        Vec<(CycleDelayRange, SequenceExpr)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SequenceExprExpression {
    pub nodes: (ExpressionOrDist, Option<BooleanAbbrev>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SequenceExprInstance {
    pub nodes: (SequenceInstance, Option<SequenceAbbrev>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SequenceExprParen {
    pub nodes: (
        Paren<(SequenceExpr, Vec<(Symbol, SequenceMatchItem)>)>,
        Option<SequenceAbbrev>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SequenceExprBinary {
    pub nodes: (SequenceExpr, Keyword, SequenceExpr),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SequenceExprFirstMatch {
    pub nodes: (
        Keyword,
        Paren<(SequenceExpr, Vec<(Symbol, SequenceMatchItem)>)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SequenceExprThroughout {
    pub nodes: (ExpressionOrDist, Keyword, SequenceExpr),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SequenceExprClockingEvent {
    pub nodes: (ClockingEvent, SequenceExpr),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum CycleDelayRange {
    Primary(Box<CycleDelayRangePrimary>),
    Expression(Box<CycleDelayRangeExpression>),
    Asterisk(Box<CycleDelayRangeAsterisk>),
    Plus(Box<CycleDelayRangePlus>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CycleDelayRangePrimary {
    pub nodes: (Symbol, ConstantPrimary),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CycleDelayRangeExpression {
    pub nodes: (Symbol, Bracket<CycleDelayConstRangeExpression>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CycleDelayRangeAsterisk {
    pub nodes: (Symbol, Bracket<Symbol>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CycleDelayRangePlus {
    pub nodes: (Symbol, Bracket<Symbol>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SequenceMethodCall {
    pub nodes: (SequenceInstance, Symbol, MethodIdentifier),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum SequenceMatchItem {
    OperatorAssignment(Box<OperatorAssignment>),
    IncOrDecExpression(Box<IncOrDecExpression>),
    SubroutineCall(Box<SubroutineCall>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SequenceInstance {
    pub nodes: (
        PsOrHierarchicalSequenceIdentifier,
        Option<Paren<Option<SequenceListOfArguments>>>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum SequenceListOfArguments {
    Ordered(Box<SequenceListOfArgumentsOrdered>),
    Named(Box<SequenceListOfArgumentsNamed>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SequenceListOfArgumentsOrdered {
    pub nodes: (
        List<Symbol, Option<SequenceActualArg>>,
        Vec<(Symbol, Symbol, Identifier, Paren<Option<SequenceActualArg>>)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SequenceListOfArgumentsNamed {
    pub nodes: (List<Symbol, (Symbol, Identifier, Paren<Option<SequenceActualArg>>)>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum SequenceActualArg {
    EventExpression(Box<EventExpression>),
    SequenceExpr(Box<SequenceExpr>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum BooleanAbbrev {
    ConsecutiveRepetition(Box<ConsecutiveRepetition>),
    NonConsecutiveRepetition(Box<NonConsecutiveRepetition>),
    GotoRepetition(Box<GotoRepetition>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SequenceAbbrev {
    pub nodes: (ConsecutiveRepetition,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ConsecutiveRepetition {
    Expression(Box<ConsecutiveRepetitionExpression>),
    Asterisk(Box<ConsecutiveRepetitionAsterisk>),
    Plus(Box<ConsecutiveRepetitionPlus>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ConsecutiveRepetitionExpression {
    pub nodes: (Bracket<(Symbol, ConstOrRangeExpression)>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ConsecutiveRepetitionAsterisk {
    pub nodes: (Bracket<Symbol>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ConsecutiveRepetitionPlus {
    pub nodes: (Bracket<Symbol>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct NonConsecutiveRepetition {
    pub nodes: (Bracket<(Symbol, ConstOrRangeExpression)>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct GotoRepetition {
    pub nodes: (Bracket<(Symbol, ConstOrRangeExpression)>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ConstOrRangeExpression {
    ConstantExpression(Box<ConstantExpression>),
    CycleDelayConstRangeExpression(Box<CycleDelayConstRangeExpression>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum CycleDelayConstRangeExpression {
    Binary(Box<CycleDelayConstRangeExpressionBinary>),
    Dollar(Box<CycleDelayConstRangeExpressionDollar>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CycleDelayConstRangeExpressionBinary {
    pub nodes: (ConstantExpression, Symbol, ConstantExpression),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CycleDelayConstRangeExpressionDollar {
    pub nodes: (ConstantExpression, Symbol, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ExpressionOrDist {
    pub nodes: (Expression, Option<(Keyword, Brace<DistList>)>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct AssertionVariableDeclaration {
    pub nodes: (VarDataType, ListOfVariableDeclAssignments, Symbol),
}

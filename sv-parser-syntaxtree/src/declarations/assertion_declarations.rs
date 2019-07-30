use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum ConcurrentAssertionItem {
    Statement(Box<ConcurrentAssertionItemStatement>),
    CheckerInstantiation(Box<CheckerInstantiation>),
}

#[derive(Clone, Debug, Node)]
pub struct ConcurrentAssertionItemStatement {
    pub nodes: (
        Option<(BlockIdentifier, Symbol)>,
        ConcurrentAssertionStatement,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum ConcurrentAssertionStatement {
    AssertPropertyStatement(Box<AssertPropertyStatement>),
    AssumePropertyStatement(Box<AssumePropertyStatement>),
    CoverPropertyStatement(Box<CoverPropertyStatement>),
    CoverSequenceStatement(Box<CoverSequenceStatement>),
    RestrictPropertyStatement(Box<RestrictPropertyStatement>),
}

#[derive(Clone, Debug, Node)]
pub struct AssertPropertyStatement {
    pub nodes: (Keyword, Keyword, Paren<PropertySpec>, ActionBlock),
}

#[derive(Clone, Debug, Node)]
pub struct AssumePropertyStatement {
    pub nodes: (Keyword, Keyword, Paren<PropertySpec>, ActionBlock),
}

#[derive(Clone, Debug, Node)]
pub struct CoverPropertyStatement {
    pub nodes: (Keyword, Keyword, Paren<PropertySpec>, StatementOrNull),
}

#[derive(Clone, Debug, Node)]
pub struct ExpectPropertyStatement {
    pub nodes: (Keyword, Paren<PropertySpec>, ActionBlock),
}

#[derive(Clone, Debug, Node)]
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

#[derive(Clone, Debug, Node)]
pub struct RestrictPropertyStatement {
    pub nodes: (Keyword, Keyword, Paren<PropertySpec>, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyInstance {
    pub nodes: (
        PsOrHierarchicalPropertyIdentifier,
        Option<Paren<Option<PropertyListOfArguments>>>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum PropertyListOfArguments {
    Ordered(Box<PropertyListOfArgumentsOrdered>),
    Named(Box<PropertyListOfArgumentsNamed>),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyListOfArgumentsOrdered {
    pub nodes: (
        List<Symbol, Option<PropertyActualArg>>,
        Vec<(Symbol, Symbol, Identifier, Paren<Option<PropertyActualArg>>)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyListOfArgumentsNamed {
    pub nodes: (List<Symbol, (Symbol, Identifier, Paren<Option<PropertyActualArg>>)>,),
}

#[derive(Clone, Debug, Node)]
pub enum PropertyActualArg {
    PropertyExpr(Box<PropertyExpr>),
    SequenceActualArg(Box<SequenceActualArg>),
}

#[derive(Clone, Debug, Node)]
pub enum AssertionItemDeclaration {
    PropertyDeclaration(Box<PropertyDeclaration>),
    SequenceDeclaration(Box<SequenceDeclaration>),
    LetDeclaration(Box<LetDeclaration>),
}

#[derive(Clone, Debug, Node)]
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

#[derive(Clone, Debug, Node)]
pub struct PropertyPortList {
    pub nodes: (List<Symbol, PropertyPortItem>,),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyPortItem {
    pub nodes: (
        Vec<AttributeInstance>,
        Option<(Local, Option<PropertyLvarPortDirection>)>,
        PropertyFormalType,
        FormalPortIdentifier,
        Vec<VariableDimension>,
        Option<(Symbol, PropertyActualArg)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum PropertyLvarPortDirection {
    Input(Box<Keyword>),
}

#[derive(Clone, Debug, Node)]
pub enum PropertyFormalType {
    SequenceFormalType(Box<SequenceFormalType>),
    Property(Box<Keyword>),
}

#[derive(Clone, Debug, Node)]
pub struct PropertySpec {
    pub nodes: (
        Option<ClockingEvent>,
        Option<(Keyword, Keyword, Paren<ExpressionOrDist>)>,
        PropertyExpr,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum PropertyExpr {
    SequenceExpr(Box<SequenceExpr>),
    Strong(Box<PropertyExprStrong>),
    Weak(Box<PropertyExprWeak>),
    Paren(Box<PropertyExprParen>),
    Not(Box<PropertyExprNot>),
    Or(Box<PropertyExprOr>),
    And(Box<PropertyExprAnd>),
    ImplicationOverlapped(Box<PropertyExprImplicationOverlapped>),
    ImplicationNonoverlapped(Box<PropertyExprImplicationNonoverlapped>),
    If(Box<PropertyExprIf>),
    Case(Box<PropertyExprCase>),
    FollowedByOverlapped(Box<PropertyExprFollowedByOverlapped>),
    FollowedByNonoverlapped(Box<PropertyExprFollowedByNonoverlapped>),
    Nexttime(Box<PropertyExprNexttime>),
    SNexttime(Box<PropertyExprSNexttime>),
    Always(Box<PropertyExprAlways>),
    SAlways(Box<PropertyExprSAlways>),
    Eventually(Box<PropertyExprEventually>),
    SEventually(Box<PropertyExprSEventually>),
    Until(Box<PropertyExprUntil>),
    SUntil(Box<PropertyExprSUntil>),
    UntilWith(Box<PropertyExprUntilWith>),
    SUntilWith(Box<PropertyExprSUntilWith>),
    Implies(Box<PropertyExprImplies>),
    Iff(Box<PropertyExprIff>),
    AcceptOn(Box<PropertyExprAcceptOn>),
    RejectOn(Box<PropertyExprRejectOn>),
    SyncAcceptOn(Box<PropertyExprSyncAcceptOn>),
    SyncRejectOn(Box<PropertyExprSyncRejectOn>),
    PropertyInstance(Box<PropertyInstance>),
    ClockingEvent(Box<PropertyExprClockingEvent>),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprStrong {
    pub nodes: (Keyword, Paren<SequenceExpr>),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprWeak {
    pub nodes: (Keyword, Paren<SequenceExpr>),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprParen {
    pub nodes: (Paren<SequenceExpr>,),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprNot {
    pub nodes: (Keyword, PropertyExpr),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprOr {
    pub nodes: (PropertyExpr, Keyword, PropertyExpr),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprAnd {
    pub nodes: (PropertyExpr, Keyword, PropertyExpr),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprImplicationOverlapped {
    pub nodes: (SequenceExpr, Symbol, PropertyExpr),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprImplicationNonoverlapped {
    pub nodes: (SequenceExpr, Symbol, PropertyExpr),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprIf {
    pub nodes: (
        Keyword,
        Paren<ExpressionOrDist>,
        PropertyExpr,
        Option<(Keyword, PropertyExpr)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprCase {
    pub nodes: (
        Keyword,
        Paren<ExpressionOrDist>,
        PropertyCaseItem,
        Vec<PropertyCaseItem>,
        Keyword,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprFollowedByOverlapped {
    pub nodes: (SequenceExpr, Symbol, PropertyExpr),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprFollowedByNonoverlapped {
    pub nodes: (SequenceExpr, Symbol, PropertyExpr),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprNexttime {
    pub nodes: (Keyword, Option<Bracket<ConstantExpression>>, PropertyExpr),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprSNexttime {
    pub nodes: (Keyword, Option<Bracket<ConstantExpression>>, PropertyExpr),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprAlways {
    pub nodes: (
        Keyword,
        Option<Bracket<CycleDelayConstRangeExpression>>,
        PropertyExpr,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprSAlways {
    pub nodes: (
        Keyword,
        Bracket<CycleDelayConstRangeExpression>,
        PropertyExpr,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprEventually {
    pub nodes: (Keyword, Bracket<ConstantRange>, PropertyExpr),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprSEventually {
    pub nodes: (
        Keyword,
        Option<Bracket<CycleDelayConstRangeExpression>>,
        PropertyExpr,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprUntil {
    pub nodes: (PropertyExpr, Keyword, PropertyExpr),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprSUntil {
    pub nodes: (PropertyExpr, Keyword, PropertyExpr),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprUntilWith {
    pub nodes: (PropertyExpr, Keyword, PropertyExpr),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprSUntilWith {
    pub nodes: (PropertyExpr, Keyword, PropertyExpr),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprImplies {
    pub nodes: (PropertyExpr, Keyword, PropertyExpr),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprIff {
    pub nodes: (PropertyExpr, Keyword, PropertyExpr),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprAcceptOn {
    pub nodes: (Keyword, Paren<ExpressionOrDist>, PropertyExpr),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprRejectOn {
    pub nodes: (Keyword, Paren<ExpressionOrDist>, PropertyExpr),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprSyncAcceptOn {
    pub nodes: (Keyword, Paren<ExpressionOrDist>, PropertyExpr),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprSyncRejectOn {
    pub nodes: (Keyword, Paren<ExpressionOrDist>, PropertyExpr),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyExprClockingEvent {
    pub nodes: (ClockingEvent, PropertyExpr),
}

#[derive(Clone, Debug, Node)]
pub enum PropertyCaseItem {
    Nondefault(Box<PropertyCaseItemNondefault>),
    Default(Box<PropertyCaseItemDefault>),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyCaseItemNondefault {
    pub nodes: (List<Symbol, ExpressionOrDist>, Symbol, PropertyExpr, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct PropertyCaseItemDefault {
    pub nodes: (Keyword, Option<Symbol>, PropertyExpr, Symbol),
}

#[derive(Clone, Debug, Node)]
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

#[derive(Clone, Debug, Node)]
pub struct SequencePortList {
    pub nodes: (List<Symbol, SequencePortItem>,),
}

#[derive(Clone, Debug, Node)]
pub struct SequencePortItem {
    pub nodes: (
        Vec<AttributeInstance>,
        Option<(Local, Option<SequenceLvarPortDirection>)>,
        SequenceFormalType,
        FormalPortIdentifier,
        Vec<VariableDimension>,
        Option<(Symbol, SequenceActualArg)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum SequenceLvarPortDirection {
    Input(Box<Keyword>),
    Inout(Box<Keyword>),
    Output(Box<Keyword>),
}

#[derive(Clone, Debug, Node)]
pub enum SequenceFormalType {
    DataTypeOrImplicit(Box<DataTypeOrImplicit>),
    Sequence(Box<Keyword>),
    Untyped(Box<Keyword>),
}

#[derive(Clone, Debug, Node)]
pub enum SequenceExpr {
    CycleDelayExpr(Box<SequenceExprCycleDelayExpr>),
    ExprCycleDelayExpr(Box<SequenceExprExprCycleDelayExpr>),
    Expression(Box<SequenceExprExpression>),
    Instance(Box<SequenceExprInstance>),
    Paren(Box<SequenceExprParen>),
    And(Box<SequenceExprAnd>),
    Intersect(Box<SequenceExprIntersect>),
    Or(Box<SequenceExprOr>),
    FirstMatch(Box<SequenceExprFirstMatch>),
    Throughout(Box<SequenceExprThroughout>),
    Within(Box<SequenceExprWithin>),
    ClockingEvent(Box<SequenceExprClockingEvent>),
}

#[derive(Clone, Debug, Node)]
pub struct SequenceExprCycleDelayExpr {
    pub nodes: (
        CycleDelayRange,
        SequenceExpr,
        Vec<(CycleDelayRange, SequenceExpr)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct SequenceExprExprCycleDelayExpr {
    pub nodes: (
        SequenceExpr,
        CycleDelayRange,
        SequenceExpr,
        Vec<(CycleDelayRange, SequenceExpr)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct SequenceExprExpression {
    pub nodes: (ExpressionOrDist, Option<BooleanAbbrev>),
}

#[derive(Clone, Debug, Node)]
pub struct SequenceExprInstance {
    pub nodes: (SequenceInstance, Option<SequenceAbbrev>),
}

#[derive(Clone, Debug, Node)]
pub struct SequenceExprParen {
    pub nodes: (
        Paren<(SequenceExpr, Vec<(Symbol, SequenceMatchItem)>)>,
        Option<SequenceAbbrev>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct SequenceExprAnd {
    pub nodes: (SequenceExpr, Keyword, SequenceExpr),
}

#[derive(Clone, Debug, Node)]
pub struct SequenceExprIntersect {
    pub nodes: (SequenceExpr, Keyword, SequenceExpr),
}

#[derive(Clone, Debug, Node)]
pub struct SequenceExprOr {
    pub nodes: (SequenceExpr, Keyword, SequenceExpr),
}

#[derive(Clone, Debug, Node)]
pub struct SequenceExprFirstMatch {
    pub nodes: (
        Keyword,
        Paren<(SequenceExpr, Vec<(Symbol, SequenceMatchItem)>)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct SequenceExprThroughout {
    pub nodes: (ExpressionOrDist, Keyword, SequenceExpr),
}

#[derive(Clone, Debug, Node)]
pub struct SequenceExprWithin {
    pub nodes: (SequenceExpr, Keyword, SequenceExpr),
}

#[derive(Clone, Debug, Node)]
pub struct SequenceExprClockingEvent {
    pub nodes: (ClockingEvent, SequenceExpr),
}

#[derive(Clone, Debug, Node)]
pub enum CycleDelayRange {
    Primary(Box<CycleDelayRangePrimary>),
    Expression(Box<CycleDelayRangeExpression>),
    Asterisk(Box<CycleDelayRangeAsterisk>),
    Plus(Box<CycleDelayRangePlus>),
}

#[derive(Clone, Debug, Node)]
pub struct CycleDelayRangePrimary {
    pub nodes: (Symbol, ConstantPrimary),
}

#[derive(Clone, Debug, Node)]
pub struct CycleDelayRangeExpression {
    pub nodes: (Symbol, Bracket<CycleDelayConstRangeExpression>),
}

#[derive(Clone, Debug, Node)]
pub struct CycleDelayRangeAsterisk {
    pub nodes: (Symbol, Bracket<Symbol>),
}

#[derive(Clone, Debug, Node)]
pub struct CycleDelayRangePlus {
    pub nodes: (Symbol, Bracket<Symbol>),
}

#[derive(Clone, Debug, Node)]
pub struct SequenceMethodCall {
    pub nodes: (SequenceInstance, Symbol, MethodIdentifier),
}

#[derive(Clone, Debug, Node)]
pub enum SequenceMatchItem {
    OperatorAssignment(Box<OperatorAssignment>),
    IncOrDecExpression(Box<IncOrDecExpression>),
    SubroutineCall(Box<SubroutineCall>),
}

#[derive(Clone, Debug, Node)]
pub struct SequenceInstance {
    pub nodes: (
        PsOrHierarchicalSequenceIdentifier,
        Option<Paren<Option<SequenceListOfArguments>>>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum SequenceListOfArguments {
    Ordered(Box<SequenceListOfArgumentsOrdered>),
    Named(Box<SequenceListOfArgumentsNamed>),
}

#[derive(Clone, Debug, Node)]
pub struct SequenceListOfArgumentsOrdered {
    pub nodes: (
        List<Symbol, Option<SequenceActualArg>>,
        Vec<(Symbol, Symbol, Identifier, Paren<Option<SequenceActualArg>>)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct SequenceListOfArgumentsNamed {
    pub nodes: (List<Symbol, (Symbol, Identifier, Paren<Option<SequenceActualArg>>)>,),
}

#[derive(Clone, Debug, Node)]
pub enum SequenceActualArg {
    EventExpression(Box<EventExpression>),
    SequenceExpr(Box<SequenceExpr>),
}

#[derive(Clone, Debug, Node)]
pub enum BooleanAbbrev {
    ConsecutiveRepetition(Box<ConsecutiveRepetition>),
    NonConsecutiveRepetition(Box<NonConsecutiveRepetition>),
    GotoRepetition(Box<GotoRepetition>),
}

#[derive(Clone, Debug, Node)]
pub struct SequenceAbbrev {
    pub nodes: (ConsecutiveRepetition,),
}

#[derive(Clone, Debug, Node)]
pub enum ConsecutiveRepetition {
    Expression(Box<ConsecutiveRepetitionExpression>),
    Asterisk(Box<ConsecutiveRepetitionAsterisk>),
    Plus(Box<ConsecutiveRepetitionPlus>),
}

#[derive(Clone, Debug, Node)]
pub struct ConsecutiveRepetitionExpression {
    pub nodes: (Bracket<(Symbol, ConstOrRangeExpression)>,),
}

#[derive(Clone, Debug, Node)]
pub struct ConsecutiveRepetitionAsterisk {
    pub nodes: (Bracket<Symbol>,),
}

#[derive(Clone, Debug, Node)]
pub struct ConsecutiveRepetitionPlus {
    pub nodes: (Bracket<Symbol>,),
}

#[derive(Clone, Debug, Node)]
pub struct NonConsecutiveRepetition {
    pub nodes: (Bracket<(Symbol, ConstOrRangeExpression)>,),
}

#[derive(Clone, Debug, Node)]
pub struct GotoRepetition {
    pub nodes: (Bracket<(Symbol, ConstOrRangeExpression)>,),
}

#[derive(Clone, Debug, Node)]
pub enum ConstOrRangeExpression {
    ConstantExpression(Box<ConstantExpression>),
    CycleDelayConstRangeExpression(Box<CycleDelayConstRangeExpression>),
}

#[derive(Clone, Debug, Node)]
pub enum CycleDelayConstRangeExpression {
    Binary(Box<CycleDelayConstRangeExpressionBinary>),
    Dollar(Box<CycleDelayConstRangeExpressionDollar>),
}

#[derive(Clone, Debug, Node)]
pub struct CycleDelayConstRangeExpressionBinary {
    pub nodes: (ConstantExpression, Symbol, ConstantExpression),
}

#[derive(Clone, Debug, Node)]
pub struct CycleDelayConstRangeExpressionDollar {
    pub nodes: (ConstantExpression, Symbol, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct ExpressionOrDist {
    pub nodes: (Expression, Option<(Keyword, Brace<DistList>)>),
}

#[derive(Clone, Debug, Node)]
pub struct AssertionVariableDeclaration {
    pub nodes: (VarDataType, ListOfVariableDeclAssignments, Symbol),
}

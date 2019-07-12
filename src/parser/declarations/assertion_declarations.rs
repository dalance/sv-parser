use crate::ast::*;
use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum ConcurrentAssertionItem<'a> {
    Statement(ConcurrentAssertionItemStatement<'a>),
    CheckerInstantiation(CheckerInstantiation<'a>),
}

#[derive(Debug, Node)]
pub struct ConcurrentAssertionItemStatement<'a> {
    pub nodes: (
        Option<(BlockIdentifier<'a>, Symbol<'a>)>,
        ConcurrentAssertionStatement<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum ConcurrentAssertionStatement<'a> {
    AssertProperty(AssertPropertyStatement<'a>),
    AssumeProperty(AssumePropertyStatement<'a>),
    CoverProperty(CoverPropertyStatement<'a>),
    CoverSequence(CoverSequenceStatement<'a>),
    RestrictProperty(RestrictPropertyStatement<'a>),
}

#[derive(Debug, Node)]
pub struct AssertPropertyStatement<'a> {
    pub nodes: (
        Symbol<'a>,
        Symbol<'a>,
        Paren<'a, PropertySpec<'a>>,
        ActionBlock<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct AssumePropertyStatement<'a> {
    pub nodes: (
        Symbol<'a>,
        Symbol<'a>,
        Paren<'a, PropertySpec<'a>>,
        ActionBlock<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct CoverPropertyStatement<'a> {
    pub nodes: (
        Symbol<'a>,
        Symbol<'a>,
        Paren<'a, PropertySpec<'a>>,
        StatementOrNull<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct ExpectPropertyStatement<'a> {
    pub nodes: (
        Symbol<'a>,
        Symbol<'a>,
        Paren<'a, PropertySpec<'a>>,
        ActionBlock<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct CoverSequenceStatement<'a> {
    pub nodes: (
        Symbol<'a>,
        Symbol<'a>,
        Paren<
            'a,
            (
                Option<ClockingEvent<'a>>,
                Option<(Symbol<'a>, Symbol<'a>, Paren<'a, ExpressionOrDist<'a>>)>,
                SequenceExpr<'a>,
            ),
        >,
        StatementOrNull<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct RestrictPropertyStatement<'a> {
    pub nodes: (
        Symbol<'a>,
        Symbol<'a>,
        Paren<'a, PropertySpec<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct PropertyInstance<'a> {
    pub nodes: (
        PsOrHierarchicalPropertyIdentifier<'a>,
        Option<Paren<'a, Option<PropertyListOfArguments<'a>>>>,
    ),
}

#[derive(Debug, Node)]
pub enum PropertyListOfArguments<'a> {
    Ordered(PropertyListOfArgumentsOrdered<'a>),
    Named(PropertyListOfArgumentsNamed<'a>),
}

#[derive(Debug, Node)]
pub struct PropertyListOfArgumentsOrdered<'a> {
    pub nodes: (
        List<Symbol<'a>, Option<PropertyActualArg<'a>>>,
        Vec<(
            Symbol<'a>,
            Symbol<'a>,
            Identifier<'a>,
            Paren<'a, Option<PropertyActualArg<'a>>>,
        )>,
    ),
}

#[derive(Debug, Node)]
pub struct PropertyListOfArgumentsNamed<'a> {
    pub nodes: (
        List<
            Symbol<'a>,
            (
                Symbol<'a>,
                Identifier<'a>,
                Paren<'a, Option<PropertyActualArg<'a>>>,
            ),
        >,
    ),
}

#[derive(Debug, Node)]
pub enum PropertyActualArg<'a> {
    PropertyExpr(PropertyExpr<'a>),
    SequenceActualArg(SequenceActualArg<'a>),
}

#[derive(Debug, Node)]
pub enum AssertionItemDeclaration<'a> {
    PropertyDeclaration(PropertyDeclaration<'a>),
    SequenceDeclaration(SequenceDeclaration<'a>),
    LetDeclaration(LetDeclaration<'a>),
}

#[derive(Debug, Node)]
pub struct PropertyDeclaration<'a> {
    pub nodes: (
        Symbol<'a>,
        PropertyIdentifier<'a>,
        Option<Paren<'a, Option<PropertyPortList<'a>>>>,
        Symbol<'a>,
        Vec<AssertionVariableDeclaration<'a>>,
        PropertySpec<'a>,
        Option<Symbol<'a>>,
        Symbol<'a>,
        Option<(Symbol<'a>, PropertyIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct PropertyPortList<'a> {
    pub nodes: (List<Symbol<'a>, PropertyPortItem<'a>>,),
}

#[derive(Debug, Node)]
pub struct PropertyPortItem<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Option<(Symbol<'a>, Option<PropertyLvarPortDirection<'a>>)>,
        PropertyFormalType<'a>,
        FormalPortIdentifier<'a>,
        Vec<VariableDimension<'a>>,
        Option<(Symbol<'a>, PropertyActualArg<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub enum PropertyLvarPortDirection<'a> {
    Input(Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum PropertyFormalType<'a> {
    SequenceFormalType(SequenceFormalType<'a>),
    Property(Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct PropertySpec<'a> {
    pub nodes: (
        Option<ClockingEvent<'a>>,
        Option<(Symbol<'a>, Symbol<'a>, Paren<'a, ExpressionOrDist<'a>>)>,
        PropertyExpr<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum PropertyExpr<'a> {
    SequenceExpr(SequenceExpr<'a>),
    Strong(PropertyExprStrong<'a>),
    Weak(PropertyExprWeak<'a>),
    Paren(Box<PropertyExprParen<'a>>),
    Not(Box<PropertyExprNot<'a>>),
    Or(Box<PropertyExprOr<'a>>),
    And(Box<PropertyExprAnd<'a>>),
    ImplicationOverlapped(Box<PropertyExprImplicationOverlapped<'a>>),
    ImplicationNonoverlapped(Box<PropertyExprImplicationNonoverlapped<'a>>),
    If(Box<PropertyExprIf<'a>>),
    Case(Box<PropertyExprCase<'a>>),
    FollowedByOverlapped(Box<PropertyExprFollowedByOverlapped<'a>>),
    FollowedByNonoverlapped(Box<PropertyExprFollowedByNonoverlapped<'a>>),
    Nexttime(Box<PropertyExprNexttime<'a>>),
    SNexttime(Box<PropertyExprSNexttime<'a>>),
    Always(Box<PropertyExprAlways<'a>>),
    SAlways(Box<PropertyExprSAlways<'a>>),
    Eventually(Box<PropertyExprEventually<'a>>),
    SEventually(Box<PropertyExprSEventually<'a>>),
    Until(Box<PropertyExprUntil<'a>>),
    SUntil(Box<PropertyExprSUntil<'a>>),
    UntilWith(Box<PropertyExprUntilWith<'a>>),
    SUntilWith(Box<PropertyExprSUntilWith<'a>>),
    Implies(Box<PropertyExprImplies<'a>>),
    Iff(Box<PropertyExprIff<'a>>),
    AcceptOn(Box<PropertyExprAcceptOn<'a>>),
    RejectOn(Box<PropertyExprRejectOn<'a>>),
    SyncAcceptOn(Box<PropertyExprSyncAcceptOn<'a>>),
    SyncRejectOn(Box<PropertyExprSyncRejectOn<'a>>),
    PropertyInstance(Box<PropertyInstance<'a>>),
    ClockingEvent(Box<PropertyExprClockingEvent<'a>>),
}

#[derive(Debug, Node)]
pub struct PropertyExprStrong<'a> {
    pub nodes: (Symbol<'a>, Paren<'a, SequenceExpr<'a>>),
}

#[derive(Debug, Node)]
pub struct PropertyExprWeak<'a> {
    pub nodes: (Symbol<'a>, Paren<'a, SequenceExpr<'a>>),
}

#[derive(Debug, Node)]
pub struct PropertyExprParen<'a> {
    pub nodes: (Paren<'a, SequenceExpr<'a>>,),
}

#[derive(Debug, Node)]
pub struct PropertyExprNot<'a> {
    pub nodes: (Symbol<'a>, PropertyExpr<'a>),
}

#[derive(Debug, Node)]
pub struct PropertyExprOr<'a> {
    pub nodes: (PropertyExpr<'a>, Symbol<'a>, PropertyExpr<'a>),
}

#[derive(Debug, Node)]
pub struct PropertyExprAnd<'a> {
    pub nodes: (PropertyExpr<'a>, Symbol<'a>, PropertyExpr<'a>),
}

#[derive(Debug, Node)]
pub struct PropertyExprImplicationOverlapped<'a> {
    pub nodes: (SequenceExpr<'a>, Symbol<'a>, PropertyExpr<'a>),
}

#[derive(Debug, Node)]
pub struct PropertyExprImplicationNonoverlapped<'a> {
    pub nodes: (SequenceExpr<'a>, Symbol<'a>, PropertyExpr<'a>),
}

#[derive(Debug, Node)]
pub struct PropertyExprIf<'a> {
    pub nodes: (
        Symbol<'a>,
        Paren<'a, ExpressionOrDist<'a>>,
        PropertyExpr<'a>,
        Option<(Symbol<'a>, PropertyExpr<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct PropertyExprCase<'a> {
    pub nodes: (
        Symbol<'a>,
        Paren<'a, ExpressionOrDist<'a>>,
        PropertyCaseItem<'a>,
        Vec<PropertyCaseItem<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct PropertyExprFollowedByOverlapped<'a> {
    pub nodes: (SequenceExpr<'a>, Symbol<'a>, PropertyExpr<'a>),
}

#[derive(Debug, Node)]
pub struct PropertyExprFollowedByNonoverlapped<'a> {
    pub nodes: (SequenceExpr<'a>, Symbol<'a>, PropertyExpr<'a>),
}

#[derive(Debug, Node)]
pub struct PropertyExprNexttime<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<Paren<'a, ConstantExpression<'a>>>,
        PropertyExpr<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct PropertyExprSNexttime<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<Paren<'a, ConstantExpression<'a>>>,
        PropertyExpr<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct PropertyExprAlways<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<Paren<'a, CycleDelayConstRangeExpression<'a>>>,
        PropertyExpr<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct PropertyExprSAlways<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<Paren<'a, CycleDelayConstRangeExpression<'a>>>,
        PropertyExpr<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct PropertyExprEventually<'a> {
    pub nodes: (Symbol<'a>, Paren<'a, ConstantRange<'a>>, PropertyExpr<'a>),
}

#[derive(Debug, Node)]
pub struct PropertyExprSEventually<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<Paren<'a, CycleDelayConstRangeExpression<'a>>>,
        PropertyExpr<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct PropertyExprUntil<'a> {
    pub nodes: (PropertyExpr<'a>, Symbol<'a>, PropertyExpr<'a>),
}

#[derive(Debug, Node)]
pub struct PropertyExprSUntil<'a> {
    pub nodes: (PropertyExpr<'a>, Symbol<'a>, PropertyExpr<'a>),
}

#[derive(Debug, Node)]
pub struct PropertyExprUntilWith<'a> {
    pub nodes: (PropertyExpr<'a>, Symbol<'a>, PropertyExpr<'a>),
}

#[derive(Debug, Node)]
pub struct PropertyExprSUntilWith<'a> {
    pub nodes: (PropertyExpr<'a>, Symbol<'a>, PropertyExpr<'a>),
}

#[derive(Debug, Node)]
pub struct PropertyExprImplies<'a> {
    pub nodes: (PropertyExpr<'a>, Symbol<'a>, PropertyExpr<'a>),
}

#[derive(Debug, Node)]
pub struct PropertyExprIff<'a> {
    pub nodes: (PropertyExpr<'a>, Symbol<'a>, PropertyExpr<'a>),
}

#[derive(Debug, Node)]
pub struct PropertyExprAcceptOn<'a> {
    pub nodes: (
        Symbol<'a>,
        Paren<'a, ExpressionOrDist<'a>>,
        PropertyExpr<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct PropertyExprRejectOn<'a> {
    pub nodes: (
        Symbol<'a>,
        Paren<'a, ExpressionOrDist<'a>>,
        PropertyExpr<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct PropertyExprSyncAcceptOn<'a> {
    pub nodes: (
        Symbol<'a>,
        Paren<'a, ExpressionOrDist<'a>>,
        PropertyExpr<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct PropertyExprSyncRejectOn<'a> {
    pub nodes: (
        Symbol<'a>,
        Paren<'a, ExpressionOrDist<'a>>,
        PropertyExpr<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct PropertyExprClockingEvent<'a> {
    pub nodes: (ClockingEvent<'a>, PropertyExpr<'a>),
}

#[derive(Debug, Node)]
pub enum PropertyCaseItem<'a> {
    Nondefault(PropertyCaseItemNondefault<'a>),
    Default(PropertyCaseItemDefault<'a>),
}

#[derive(Debug, Node)]
pub struct PropertyCaseItemNondefault<'a> {
    pub nodes: (
        List<Symbol<'a>, ExpressionOrDist<'a>>,
        Symbol<'a>,
        PropertyExpr<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct PropertyCaseItemDefault<'a> {
    pub nodes: (Symbol<'a>, Option<Symbol<'a>>, PropertyExpr<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct SequenceDeclaration<'a> {
    pub nodes: (
        Symbol<'a>,
        SequenceIdentifier<'a>,
        Option<Paren<'a, Option<SequencePortList<'a>>>>,
        Symbol<'a>,
        Vec<AssertionVariableDeclaration<'a>>,
        SequenceExpr<'a>,
        Option<Symbol<'a>>,
        Symbol<'a>,
        Option<(Symbol<'a>, SequenceIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct SequencePortList<'a> {
    pub nodes: (List<Symbol<'a>, SequencePortItem<'a>>,),
}

#[derive(Debug, Node)]
pub struct SequencePortItem<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Option<(Symbol<'a>, Option<SequenceLvarPortDirection<'a>>)>,
        SequenceFormalType<'a>,
        FormalPortIdentifier<'a>,
        Vec<VariableDimension<'a>>,
        Option<(Symbol<'a>, SequenceActualArg<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub enum SequenceLvarPortDirection<'a> {
    Input(Symbol<'a>),
    Inout(Symbol<'a>),
    Output(Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum SequenceFormalType<'a> {
    DataTypeOrImplicit(DataTypeOrImplicit<'a>),
    Sequence(Symbol<'a>),
    Untyped(Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum SequenceExpr<'a> {
    CycleDelayExpr(Box<SequenceExprCycleDelayExpr<'a>>),
    ExprCycleDelayExpr(Box<SequenceExprExprCycleDelayExpr<'a>>),
    Expression(SequenceExprExpression<'a>),
    Instance(Box<SequenceExprInstance<'a>>),
    Paren(Box<SequenceExprParen<'a>>),
    And(Box<SequenceExprAnd<'a>>),
    Intersect(Box<SequenceExprIntersect<'a>>),
    Or(Box<SequenceExprOr<'a>>),
    FirstMatch(Box<SequenceExprFirstMatch<'a>>),
    Throughout(Box<SequenceExprThroughout<'a>>),
    Within(Box<SequenceExprWithin<'a>>),
    ClockingEvent(Box<SequenceExprClockingEvent<'a>>),
}

#[derive(Debug, Node)]
pub struct SequenceExprCycleDelayExpr<'a> {
    pub nodes: (
        CycleDelayRange<'a>,
        SequenceExpr<'a>,
        Vec<(CycleDelayRange<'a>, SequenceExpr<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct SequenceExprExprCycleDelayExpr<'a> {
    pub nodes: (
        SequenceExpr<'a>,
        CycleDelayRange<'a>,
        SequenceExpr<'a>,
        Vec<(CycleDelayRange<'a>, SequenceExpr<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct SequenceExprExpression<'a> {
    pub nodes: (ExpressionOrDist<'a>, Option<BooleanAbbrev<'a>>),
}

#[derive(Debug, Node)]
pub struct SequenceExprInstance<'a> {
    pub nodes: (SequenceInstance<'a>, Option<SequenceAbbrev<'a>>),
}

#[derive(Debug, Node)]
pub struct SequenceExprParen<'a> {
    pub nodes: (
        Paren<'a, (SequenceExpr<'a>, Vec<(Symbol<'a>, SequenceMatchItem<'a>)>)>,
        Option<SequenceAbbrev<'a>>,
    ),
}

#[derive(Debug, Node)]
pub struct SequenceExprAnd<'a> {
    pub nodes: (SequenceExpr<'a>, Symbol<'a>, SequenceExpr<'a>),
}

#[derive(Debug, Node)]
pub struct SequenceExprIntersect<'a> {
    pub nodes: (SequenceExpr<'a>, Symbol<'a>, SequenceExpr<'a>),
}

#[derive(Debug, Node)]
pub struct SequenceExprOr<'a> {
    pub nodes: (SequenceExpr<'a>, Symbol<'a>, SequenceExpr<'a>),
}

#[derive(Debug, Node)]
pub struct SequenceExprFirstMatch<'a> {
    pub nodes: (
        Symbol<'a>,
        Paren<'a, (SequenceExpr<'a>, Vec<(Symbol<'a>, SequenceMatchItem<'a>)>)>,
    ),
}

#[derive(Debug, Node)]
pub struct SequenceExprThroughout<'a> {
    pub nodes: (ExpressionOrDist<'a>, Symbol<'a>, SequenceExpr<'a>),
}

#[derive(Debug, Node)]
pub struct SequenceExprWithin<'a> {
    pub nodes: (SequenceExpr<'a>, Symbol<'a>, SequenceExpr<'a>),
}

#[derive(Debug, Node)]
pub struct SequenceExprClockingEvent<'a> {
    pub nodes: (ClockingEvent<'a>, SequenceExpr<'a>),
}

#[derive(Debug, Node)]
pub enum CycleDelayRange<'a> {
    Primary(CycleDelayRangePrimary<'a>),
    Expression(CycleDelayRangeExpression<'a>),
    Asterisk(CycleDelayRangeAsterisk<'a>),
    Plus(CycleDelayRangePlus<'a>),
}

#[derive(Debug, Node)]
pub struct CycleDelayRangePrimary<'a> {
    pub nodes: (Symbol<'a>, ConstantPrimary<'a>),
}

#[derive(Debug, Node)]
pub struct CycleDelayRangeExpression<'a> {
    pub nodes: (Symbol<'a>, Bracket<'a, CycleDelayConstRangeExpression<'a>>),
}

#[derive(Debug, Node)]
pub struct CycleDelayRangeAsterisk<'a> {
    pub nodes: (Symbol<'a>, Bracket<'a, Symbol<'a>>),
}

#[derive(Debug, Node)]
pub struct CycleDelayRangePlus<'a> {
    pub nodes: (Symbol<'a>, Bracket<'a, Symbol<'a>>),
}

#[derive(Debug, Node)]
pub struct SequenceMethodCall<'a> {
    pub nodes: (SequenceInstance<'a>, Symbol<'a>, MethodIdentifier<'a>),
}

#[derive(Debug, Node)]
pub enum SequenceMatchItem<'a> {
    OperatorAssignment(OperatorAssignment<'a>),
    IncOrDecExpression(IncOrDecExpression<'a>),
    SubroutineCall(SubroutineCall<'a>),
}

#[derive(Debug, Node)]
pub struct SequenceInstance<'a> {
    pub nodes: (
        PsOrHierarchicalSequenceIdentifier<'a>,
        Option<Paren<'a, Option<SequenceListOfArguments<'a>>>>,
    ),
}

#[derive(Debug, Node)]
pub enum SequenceListOfArguments<'a> {
    Ordered(SequenceListOfArgumentsOrdered<'a>),
    Named(SequenceListOfArgumentsNamed<'a>),
}

#[derive(Debug, Node)]
pub struct SequenceListOfArgumentsOrdered<'a> {
    pub nodes: (
        List<Symbol<'a>, Option<SequenceActualArg<'a>>>,
        Vec<(
            Symbol<'a>,
            Symbol<'a>,
            Identifier<'a>,
            Paren<'a, Option<SequenceActualArg<'a>>>,
        )>,
    ),
}

#[derive(Debug, Node)]
pub struct SequenceListOfArgumentsNamed<'a> {
    pub nodes: (
        List<
            Symbol<'a>,
            (
                Symbol<'a>,
                Identifier<'a>,
                Paren<'a, Option<SequenceActualArg<'a>>>,
            ),
        >,
    ),
}

#[derive(Debug, Node)]
pub enum SequenceActualArg<'a> {
    EventExpression(EventExpression<'a>),
    SequenceExpr(SequenceExpr<'a>),
}

#[derive(Debug, Node)]
pub enum BooleanAbbrev<'a> {
    ConsecutiveRepetition(ConsecutiveRepetition<'a>),
    NonConsecutiveRepetition(NonConsecutiveRepetition<'a>),
    GotoRepetition(GotoRepetition<'a>),
}

#[derive(Debug, Node)]
pub struct SequenceAbbrev<'a> {
    pub nodes: (ConsecutiveRepetition<'a>,),
}

#[derive(Debug, Node)]
pub enum ConsecutiveRepetition<'a> {
    Expression(ConsecutiveRepetitionExpression<'a>),
    Asterisk(ConsecutiveRepetitionAsterisk<'a>),
    Plus(ConsecutiveRepetitionPlus<'a>),
}

#[derive(Debug, Node)]
pub struct ConsecutiveRepetitionExpression<'a> {
    pub nodes: (Bracket<'a, (Symbol<'a>, ConstOrRangeExpression<'a>)>),
}

#[derive(Debug, Node)]
pub struct ConsecutiveRepetitionAsterisk<'a> {
    pub nodes: (Bracket<'a, Symbol<'a>>,),
}

#[derive(Debug, Node)]
pub struct ConsecutiveRepetitionPlus<'a> {
    pub nodes: (Bracket<'a, Symbol<'a>>,),
}

#[derive(Debug, Node)]
pub struct NonConsecutiveRepetition<'a> {
    pub nodes: (Bracket<'a, (Symbol<'a>, ConstOrRangeExpression<'a>)>,),
}

#[derive(Debug, Node)]
pub struct GotoRepetition<'a> {
    pub nodes: (Bracket<'a, (Symbol<'a>, ConstOrRangeExpression<'a>)>,),
}

#[derive(Debug, Node)]
pub enum ConstOrRangeExpression<'a> {
    ConstantExpression(ConstantExpression<'a>),
    CycleDelayConstRangeExpression(CycleDelayConstRangeExpression<'a>),
}

#[derive(Debug, Node)]
pub enum CycleDelayConstRangeExpression<'a> {
    Binary(CycleDelayConstRangeExpressionBinary<'a>),
    Dollar(CycleDelayConstRangeExpressionDollar<'a>),
}

#[derive(Debug, Node)]
pub struct CycleDelayConstRangeExpressionBinary<'a> {
    pub nodes: (ConstantExpression<'a>, Symbol<'a>, ConstantExpression<'a>),
}

#[derive(Debug, Node)]
pub struct CycleDelayConstRangeExpressionDollar<'a> {
    pub nodes: (ConstantExpression<'a>, Symbol<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct ExpressionOrDist<'a> {
    pub nodes: (
        Expression<'a>,
        Option<(Symbol<'a>, Brace<'a, DistList<'a>>)>,
    ),
}

#[derive(Debug, Node)]
pub struct AssertionVariableDeclaration<'a> {
    pub nodes: (
        VarDataType<'a>,
        ListOfVariableDeclAssignments<'a>,
        Symbol<'a>,
    ),
}

// -----------------------------------------------------------------------------

pub fn concurrent_assertion_item(s: Span) -> IResult<Span, ConcurrentAssertionItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn concurrent_assertion_statement(s: Span) -> IResult<Span, ConcurrentAssertionStatement> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn assert_property_statement(s: Span) -> IResult<Span, AssertPropertyStatement> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn assume_property_statement(s: Span) -> IResult<Span, AssumePropertyStatement> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn cover_property_statement(s: Span) -> IResult<Span, CoverPropertyStatement> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn expect_property_statement(s: Span) -> IResult<Span, ExpectPropertyStatement> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn cover_sequence_statement(s: Span) -> IResult<Span, CoverSequenceStatement> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn restrict_property_statement(s: Span) -> IResult<Span, RestrictPropertyStatement> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn property_instance(s: Span) -> IResult<Span, PropertyInstance> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn property_list_of_arguments(s: Span) -> IResult<Span, PropertyListOfArguments> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn property_actual_arg(s: Span) -> IResult<Span, PropertyActualArg> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn assertion_item_declaration(s: Span) -> IResult<Span, AssertionItemDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn property_declaration(s: Span) -> IResult<Span, PropertyDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn property_port_list(s: Span) -> IResult<Span, PropertyPortList> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn property_port_item(s: Span) -> IResult<Span, PropertyPortItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn property_lvar_port_direction(s: Span) -> IResult<Span, PropertyLvarPortDirection> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn property_formal_type(s: Span) -> IResult<Span, PropertyFormalType> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn property_spec(s: Span) -> IResult<Span, PropertySpec> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn property_expr(s: Span) -> IResult<Span, PropertyExpr> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn property_case_item(s: Span) -> IResult<Span, PropertyCaseItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn sequence_declaration(s: Span) -> IResult<Span, SequenceDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn sequence_port_list(s: Span) -> IResult<Span, SequencePortList> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn sequence_port_item(s: Span) -> IResult<Span, SequencePortItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn sequence_lvar_port_direction(s: Span) -> IResult<Span, SequenceLvarPortDirection> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn sequence_formal_type(s: Span) -> IResult<Span, SequenceFormalType> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn sequence_expr(s: Span) -> IResult<Span, SequenceExpr> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn cycle_delay_range(s: Span) -> IResult<Span, CycleDelayRange> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn sequence_method_call(s: Span) -> IResult<Span, SequenceMethodCall> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn sequence_match_item(s: Span) -> IResult<Span, SequenceMatchItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn sequence_instance(s: Span) -> IResult<Span, SequenceInstance> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn sequence_list_of_arguments(s: Span) -> IResult<Span, SequenceListOfArguments> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn sequence_actual_arg(s: Span) -> IResult<Span, SequenceActualArg> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn boolean_abbrev(s: Span) -> IResult<Span, BooleanAbbrev> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn sequence_abbrev(s: Span) -> IResult<Span, SequenceAbbrev> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn consecutive_repetition(s: Span) -> IResult<Span, ConsecutiveRepetition> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn non_consecutive_repetition(s: Span) -> IResult<Span, NonConsecutiveRepetition> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn goto_repetition(s: Span) -> IResult<Span, GotoRepetition> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn const_or_range_expression(s: Span) -> IResult<Span, ConstOrRangeExpression> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn cycle_delay_const_range_expression(
    s: Span,
) -> IResult<Span, CycleDelayConstRangeExpression> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn expression_or_dist(s: Span) -> IResult<Span, ExpressionOrDist> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn assertion_variable_declaration(s: Span) -> IResult<Span, AssertionVariableDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

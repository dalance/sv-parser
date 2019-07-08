use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum ConcurrentAssertionItem<'a> {
    Statement(ConcurrentAssertionItemStatement<'a>),
    CheckerInstantiation(CheckerInstantiation<'a>),
}

#[derive(Debug)]
pub struct ConcurrentAssertionItemStatement<'a> {
    pub nodes: (Identifier<'a>, ConcurrentAssertionStatement<'a>),
}

#[derive(Debug)]
pub enum ConcurrentAssertionStatement<'a> {
    AssertProperty(AssertPropertyStatement<'a>),
    AssumeProperty(AssumePropertyStatement<'a>),
    CoverProperty(CoverPropertyStatement<'a>),
    CoverSequence(CoverSequenceStatement<'a>),
    RestrictProperty(RestrictPropertyStatement<'a>),
}

#[derive(Debug)]
pub struct AssertPropertyStatement<'a> {
    pub nodes: (PropertySpec<'a>, ActionBlock<'a>),
}

#[derive(Debug)]
pub struct AssumePropertyStatement<'a> {
    pub nodes: (PropertySpec<'a>, ActionBlock<'a>),
}

#[derive(Debug)]
pub struct CoverPropertyStatement<'a> {
    pub nodes: (PropertySpec<'a>, StatementOrNull<'a>),
}

#[derive(Debug)]
pub struct ExpectPropertyStatement<'a> {
    pub nodes: (PropertySpec<'a>, ActionBlock<'a>),
}

#[derive(Debug)]
pub struct CoverSequenceStatement<'a> {
    pub nodes: (
        Option<ClockingEvent<'a>>,
        Option<ExpressionOrDist<'a>>,
        SequenceExpr<'a>,
        StatementOrNull<'a>,
    ),
}

#[derive(Debug)]
pub struct RestrictPropertyStatement<'a> {
    pub nodes: (PropertySpec<'a>),
}

#[derive(Debug)]
pub struct PropertyInstance<'a> {
    pub nodes: (Identifier<'a>, Option<PropertyListOfArguments<'a>>),
}

#[derive(Debug)]
pub enum PropertyListOfArguments<'a> {
    Ordered(PropertyListOfArgumentsOrdered<'a>),
    Named(PropertyListOfArgumentsNamed<'a>),
}

#[derive(Debug)]
pub struct PropertyListOfArgumentsOrdered<'a> {
    pub nodes: (
        Vec<PropertyActualArg<'a>>,
        Vec<(Identifier<'a>, Option<PropertyActualArg<'a>>)>,
    ),
}

#[derive(Debug)]
pub struct PropertyListOfArgumentsNamed<'a> {
    pub nodes: (Vec<(Identifier<'a>, Option<PropertyActualArg<'a>>)>,),
}

#[derive(Debug)]
pub enum PropertyActualArg<'a> {
    PropertyExpr(PropertyExpr<'a>),
    SequenceActualArg(SequenceActualArg<'a>),
}

#[derive(Debug)]
pub enum AssertionItemDeclaration<'a> {
    PropertyDeclaration(PropertyDeclaration<'a>),
    SequenceDeclaration(SequenceDeclaration<'a>),
    LetDeclaration(LetDeclaration<'a>),
}

#[derive(Debug)]
pub struct PropertyDeclaration<'a> {
    pub nodes: (
        Identifier<'a>,
        Option<PropertyPortList<'a>>,
        Vec<AssertionVariableDeclaration<'a>>,
        PropertySpec<'a>,
    ),
}

#[derive(Debug)]
pub struct PropertyPortList<'a> {
    pub nodes: (Vec<PropertyPortItem<'a>>,),
}

#[derive(Debug)]
pub struct PropertyPortItem<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Option<PropertyLvarPortDirection>,
        PropertyFormalType<'a>,
        Identifier<'a>,
        Vec<VariableDimension<'a>>,
        Option<PropertyActualArg<'a>>,
    ),
}

#[derive(Debug)]
pub enum PropertyLvarPortDirection {
    Input,
}

#[derive(Debug)]
pub enum PropertyFormalType<'a> {
    SequenceFormalType(SequenceFormalType<'a>),
    Property,
}

#[derive(Debug)]
pub struct PropertySpec<'a> {
    pub nodes: (
        Option<ClockingEvent<'a>>,
        Option<ExpressionOrDist<'a>>,
        PropertyExpr<'a>,
    ),
}

#[derive(Debug)]
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
    Case(PropertyExprCase<'a>),
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

#[derive(Debug)]
pub struct PropertyExprStrong<'a> {
    pub nodes: (SequenceExpr<'a>,),
}

#[derive(Debug)]
pub struct PropertyExprWeak<'a> {
    pub nodes: (SequenceExpr<'a>,),
}

#[derive(Debug)]
pub struct PropertyExprParen<'a> {
    pub nodes: (PropertyExpr<'a>,),
}

#[derive(Debug)]
pub struct PropertyExprNot<'a> {
    pub nodes: (PropertyExpr<'a>,),
}

#[derive(Debug)]
pub struct PropertyExprOr<'a> {
    pub nodes: (PropertyExpr<'a>, PropertyExpr<'a>),
}

#[derive(Debug)]
pub struct PropertyExprAnd<'a> {
    pub nodes: (PropertyExpr<'a>, PropertyExpr<'a>),
}

#[derive(Debug)]
pub struct PropertyExprImplicationOverlapped<'a> {
    pub nodes: (SequenceExpr<'a>, PropertyExpr<'a>),
}

#[derive(Debug)]
pub struct PropertyExprImplicationNonoverlapped<'a> {
    pub nodes: (SequenceExpr<'a>, PropertyExpr<'a>),
}

#[derive(Debug)]
pub struct PropertyExprIf<'a> {
    pub nodes: (
        ExpressionOrDist<'a>,
        PropertyExpr<'a>,
        Option<PropertyExpr<'a>>,
    ),
}

#[derive(Debug)]
pub struct PropertyExprCase<'a> {
    pub nodes: (ExpressionOrDist<'a>, Vec<PropertyCaseItem<'a>>),
}

#[derive(Debug)]
pub struct PropertyExprFollowedByOverlapped<'a> {
    pub nodes: (SequenceExpr<'a>, PropertyExpr<'a>),
}

#[derive(Debug)]
pub struct PropertyExprFollowedByNonoverlapped<'a> {
    pub nodes: (SequenceExpr<'a>, PropertyExpr<'a>),
}

#[derive(Debug)]
pub struct PropertyExprNexttime<'a> {
    pub nodes: (Option<ConstantExpression<'a>>, PropertyExpr<'a>),
}

#[derive(Debug)]
pub struct PropertyExprSNexttime<'a> {
    pub nodes: (Option<ConstantExpression<'a>>, PropertyExpr<'a>),
}

#[derive(Debug)]
pub struct PropertyExprAlways<'a> {
    pub nodes: (Option<CycleDelayConstRangeExpression<'a>>, PropertyExpr<'a>),
}

#[derive(Debug)]
pub struct PropertyExprSAlways<'a> {
    pub nodes: (Option<CycleDelayConstRangeExpression<'a>>, PropertyExpr<'a>),
}

#[derive(Debug)]
pub struct PropertyExprEventually<'a> {
    pub nodes: (ConstantRange<'a>, PropertyExpr<'a>),
}

#[derive(Debug)]
pub struct PropertyExprSEventually<'a> {
    pub nodes: (Option<CycleDelayConstRangeExpression<'a>>, PropertyExpr<'a>),
}

#[derive(Debug)]
pub struct PropertyExprUntil<'a> {
    pub nodes: (PropertyExpr<'a>, PropertyExpr<'a>),
}

#[derive(Debug)]
pub struct PropertyExprSUntil<'a> {
    pub nodes: (PropertyExpr<'a>, PropertyExpr<'a>),
}

#[derive(Debug)]
pub struct PropertyExprUntilWith<'a> {
    pub nodes: (PropertyExpr<'a>, PropertyExpr<'a>),
}

#[derive(Debug)]
pub struct PropertyExprSUntilWith<'a> {
    pub nodes: (PropertyExpr<'a>, PropertyExpr<'a>),
}

#[derive(Debug)]
pub struct PropertyExprImplies<'a> {
    pub nodes: (PropertyExpr<'a>, PropertyExpr<'a>),
}

#[derive(Debug)]
pub struct PropertyExprIff<'a> {
    pub nodes: (PropertyExpr<'a>, PropertyExpr<'a>),
}

#[derive(Debug)]
pub struct PropertyExprAcceptOn<'a> {
    pub nodes: (ExpressionOrDist<'a>, PropertyExpr<'a>),
}

#[derive(Debug)]
pub struct PropertyExprRejectOn<'a> {
    pub nodes: (ExpressionOrDist<'a>, PropertyExpr<'a>),
}

#[derive(Debug)]
pub struct PropertyExprSyncAcceptOn<'a> {
    pub nodes: (ExpressionOrDist<'a>, PropertyExpr<'a>),
}

#[derive(Debug)]
pub struct PropertyExprSyncRejectOn<'a> {
    pub nodes: (ExpressionOrDist<'a>, PropertyExpr<'a>),
}

#[derive(Debug)]
pub struct PropertyExprClockingEvent<'a> {
    pub nodes: (ClockingEvent<'a>, PropertyExpr<'a>),
}

#[derive(Debug)]
pub enum PropertyCaseItem<'a> {
    Nondefault(PropertyCaseItemNondefault<'a>),
    Default(PropertyCaseItemDefault<'a>),
}

#[derive(Debug)]
pub struct PropertyCaseItemNondefault<'a> {
    pub nodes: (Vec<ExpressionOrDist<'a>>, PropertyExpr<'a>),
}

#[derive(Debug)]
pub struct PropertyCaseItemDefault<'a> {
    pub nodes: (PropertyExpr<'a>,),
}

#[derive(Debug)]
pub struct SequenceDeclaration<'a> {
    pub nodes: (
        Identifier<'a>,
        Option<SequencePortList<'a>>,
        Vec<AssertionVariableDeclaration<'a>>,
        SequenceExpr<'a>,
        Option<Identifier<'a>>,
    ),
}

#[derive(Debug)]
pub struct SequencePortList<'a> {
    pub nodes: (Vec<SequencePortItem<'a>>,),
}

#[derive(Debug)]
pub struct SequencePortItem<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Option<SequenceLvarPortDirection>,
        SequenceFormalType<'a>,
        Identifier<'a>,
        Vec<VariableDimension<'a>>,
        Option<SequenceActualArg<'a>>,
    ),
}

#[derive(Debug)]
pub enum SequenceLvarPortDirection {
    Input,
    Inout,
    Output,
}

#[derive(Debug)]
pub enum SequenceFormalType<'a> {
    DataTypeOrImplicit(DataTypeOrImplicit<'a>),
    Sequence,
    Untyped,
}

#[derive(Debug)]
pub enum SequenceExpr<'a> {
    CycleDelayExpr(SequenceExprCycleDelayExpr<'a>),
    ExprCycleDelayExpr(Box<SequenceExprExprCycleDelayExpr<'a>>),
    Expression(SequenceExprExpression<'a>),
    Instance(SequenceExprInstance<'a>),
    Paren(Box<SequenceExprParen<'a>>),
    And(Box<SequenceExprAnd<'a>>),
    Intersect(Box<SequenceExprIntersect<'a>>),
    Or(Box<SequenceExprOr<'a>>),
    FirstMatch(Box<SequenceExprFirstMatch<'a>>),
    Throughout(Box<SequenceExprThroughout<'a>>),
    Within(Box<SequenceExprWithin<'a>>),
    ClockingEvent(Box<SequenceExprClockingEvent<'a>>),
}

#[derive(Debug)]
pub struct SequenceExprCycleDelayExpr<'a> {
    pub nodes: (Vec<(CycleDelayRange<'a>, SequenceExpr<'a>)>,),
}

#[derive(Debug)]
pub struct SequenceExprExprCycleDelayExpr<'a> {
    pub nodes: (
        SequenceExpr<'a>,
        Vec<(CycleDelayRange<'a>, SequenceExpr<'a>)>,
    ),
}

#[derive(Debug)]
pub struct SequenceExprExpression<'a> {
    pub nodes: (ExpressionOrDist<'a>, Option<BooleanAbbrev<'a>>),
}

#[derive(Debug)]
pub struct SequenceExprInstance<'a> {
    pub nodes: (SequenceInstance<'a>, Option<SequenceAbbrev<'a>>),
}

#[derive(Debug)]
pub struct SequenceExprParen<'a> {
    pub nodes: (
        SequenceExpr<'a>,
        Vec<SequenceMatchItem<'a>>,
        Option<SequenceAbbrev<'a>>,
    ),
}

#[derive(Debug)]
pub struct SequenceExprAnd<'a> {
    pub nodes: (SequenceExpr<'a>, SequenceExpr<'a>),
}

#[derive(Debug)]
pub struct SequenceExprIntersect<'a> {
    pub nodes: (SequenceExpr<'a>, SequenceExpr<'a>),
}

#[derive(Debug)]
pub struct SequenceExprOr<'a> {
    pub nodes: (SequenceExpr<'a>, SequenceExpr<'a>),
}

#[derive(Debug)]
pub struct SequenceExprFirstMatch<'a> {
    pub nodes: (SequenceExpr<'a>, Vec<SequenceMatchItem<'a>>),
}

#[derive(Debug)]
pub struct SequenceExprThroughout<'a> {
    pub nodes: (ExpressionOrDist<'a>, SequenceExpr<'a>),
}

#[derive(Debug)]
pub struct SequenceExprWithin<'a> {
    pub nodes: (SequenceExpr<'a>, SequenceExpr<'a>),
}

#[derive(Debug)]
pub struct SequenceExprClockingEvent<'a> {
    pub nodes: (ClockingEvent<'a>, SequenceExpr<'a>),
}

#[derive(Debug)]
pub enum CycleDelayRange<'a> {
    ConstantPrimary(ConstantPrimary<'a>),
    CycleDelayConstRangeExpression(CycleDelayConstRangeExpression<'a>),
    Asterisk,
    Plus,
}

#[derive(Debug)]
pub struct SequenceMethodCall<'a> {
    pub nodes: (SequenceInstance<'a>, Identifier<'a>),
}

#[derive(Debug)]
pub enum SequenceMatchItem<'a> {
    OperatorAssignment(OperatorAssignment<'a>),
    IncOrDecExpression(IncOrDecExpression<'a>),
    SubroutineCall(SubroutineCall<'a>),
}

#[derive(Debug)]
pub struct SequenceInstance<'a> {
    pub nodes: (Identifier<'a>, Option<SequenceListOfArguments<'a>>),
}

#[derive(Debug)]
pub enum SequenceListOfArguments<'a> {
    Ordered(SequenceListOfArgumentsOrdered<'a>),
    Named(SequenceListOfArgumentsNamed<'a>),
}

#[derive(Debug)]
pub struct SequenceListOfArgumentsOrdered<'a> {
    pub nodes: (
        Vec<SequenceActualArg<'a>>,
        Vec<(Identifier<'a>, Option<SequenceActualArg<'a>>)>,
    ),
}

#[derive(Debug)]
pub struct SequenceListOfArgumentsNamed<'a> {
    pub nodes: (Vec<(Identifier<'a>, Option<SequenceActualArg<'a>>)>,),
}

#[derive(Debug)]
pub enum SequenceActualArg<'a> {
    EventExpression(EventExpression<'a>),
    SequenceExpr(SequenceExpr<'a>),
}

#[derive(Debug)]
pub enum BooleanAbbrev<'a> {
    ConsecutiveRepetition(ConsecutiveRepetition<'a>),
    NonConsecutiveRepetition(NonConsecutiveRepetition<'a>),
    GotoRepetition(GotoRepetition<'a>),
}

#[derive(Debug)]
pub struct SequenceAbbrev<'a> {
    pub nodes: (ConsecutiveRepetition<'a>,),
}

#[derive(Debug)]
pub enum ConsecutiveRepetition<'a> {
    ConstOrRangeExpression(ConstOrRangeExpression<'a>),
    Asterisk,
    Plus,
}

#[derive(Debug)]
pub struct NonConsecutiveRepetition<'a> {
    pub nodes: (ConstOrRangeExpression<'a>,),
}

#[derive(Debug)]
pub struct GotoRepetition<'a> {
    pub nodes: (ConstOrRangeExpression<'a>,),
}

#[derive(Debug)]
pub enum ConstOrRangeExpression<'a> {
    ConstantExpression(ConstantExpression<'a>),
    CycleDelayConstRangeExpression(CycleDelayConstRangeExpression<'a>),
}

#[derive(Debug)]
pub enum CycleDelayConstRangeExpression<'a> {
    Binary(CycleDelayConstRangeExpressionBinary<'a>),
    Dollar(CycleDelayConstRangeExpressionDollar<'a>),
}

#[derive(Debug)]
pub struct CycleDelayConstRangeExpressionBinary<'a> {
    pub nodes: (ConstantExpression<'a>, ConstantExpression<'a>),
}

#[derive(Debug)]
pub struct CycleDelayConstRangeExpressionDollar<'a> {
    pub nodes: (ConstantExpression<'a>,),
}

#[derive(Debug)]
pub struct ExpressionOrDist<'a> {
    pub nodes: (Expression<'a>, Option<DistList<'a>>),
}

#[derive(Debug)]
pub struct AssertionVariableDeclaration<'a> {
    pub nodes: (VarDataType<'a>, ListOfVariableDeclAssignments<'a>),
}

// -----------------------------------------------------------------------------

pub fn concurrent_assertion_item(s: &str) -> IResult<&str, ConcurrentAssertionItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn concurrent_assertion_statement(s: &str) -> IResult<&str, ConcurrentAssertionStatement> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn assert_property_statement(s: &str) -> IResult<&str, AssertPropertyStatement> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn assume_property_statement(s: &str) -> IResult<&str, AssumePropertyStatement> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn cover_property_statement(s: &str) -> IResult<&str, CoverPropertyStatement> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn expect_property_statement(s: &str) -> IResult<&str, ExpectPropertyStatement> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn cover_sequence_statement(s: &str) -> IResult<&str, CoverSequenceStatement> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn restrict_property_statement(s: &str) -> IResult<&str, RestrictPropertyStatement> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn property_instance(s: &str) -> IResult<&str, PropertyInstance> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn property_list_of_arguments(s: &str) -> IResult<&str, PropertyListOfArguments> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn property_actual_arg(s: &str) -> IResult<&str, PropertyActualArg> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn assertion_item_declaration(s: &str) -> IResult<&str, AssertionItemDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn property_declaration(s: &str) -> IResult<&str, PropertyDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn property_port_list(s: &str) -> IResult<&str, PropertyPortList> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn property_port_item(s: &str) -> IResult<&str, PropertyPortItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn property_lvar_port_direction(s: &str) -> IResult<&str, PropertyLvarPortDirection> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn property_formal_type(s: &str) -> IResult<&str, PropertyFormalType> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn property_spec(s: &str) -> IResult<&str, PropertySpec> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn property_expr(s: &str) -> IResult<&str, PropertyExpr> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn property_case_item(s: &str) -> IResult<&str, PropertyCaseItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn sequence_declaration(s: &str) -> IResult<&str, SequenceDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn sequence_port_list(s: &str) -> IResult<&str, SequencePortList> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn sequence_port_item(s: &str) -> IResult<&str, SequencePortItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn sequence_lvar_port_direction(s: &str) -> IResult<&str, SequenceLvarPortDirection> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn sequence_formal_type(s: &str) -> IResult<&str, SequenceFormalType> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn sequence_expr(s: &str) -> IResult<&str, SequenceExpr> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn cycle_delay_range(s: &str) -> IResult<&str, CycleDelayRange> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn sequence_method_call(s: &str) -> IResult<&str, SequenceMethodCall> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn sequence_match_item(s: &str) -> IResult<&str, SequenceMatchItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn sequence_instance(s: &str) -> IResult<&str, SequenceInstance> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn sequence_list_of_arguments(s: &str) -> IResult<&str, SequenceListOfArguments> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn sequence_actual_arg(s: &str) -> IResult<&str, SequenceActualArg> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn boolean_abbrev(s: &str) -> IResult<&str, BooleanAbbrev> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn sequence_abbrev(s: &str) -> IResult<&str, SequenceAbbrev> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn consecutive_repetition(s: &str) -> IResult<&str, ConsecutiveRepetition> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn non_consecutive_repetition(s: &str) -> IResult<&str, NonConsecutiveRepetition> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn goto_repetition(s: &str) -> IResult<&str, GotoRepetition> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn const_or_range_expression(s: &str) -> IResult<&str, ConstOrRangeExpression> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn cycle_delay_const_range_expression(
    s: &str,
) -> IResult<&str, CycleDelayConstRangeExpression> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn expression_or_dist(s: &str) -> IResult<&str, ExpressionOrDist> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn assertion_variable_declaration(s: &str) -> IResult<&str, AssertionVariableDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

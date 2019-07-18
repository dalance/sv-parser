use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

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
    AssertPropertyStatement(AssertPropertyStatement<'a>),
    AssumePropertyStatement(AssumePropertyStatement<'a>),
    CoverPropertyStatement(CoverPropertyStatement<'a>),
    CoverSequenceStatement(CoverSequenceStatement<'a>),
    RestrictPropertyStatement(RestrictPropertyStatement<'a>),
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
    pub nodes: (Symbol<'a>, Paren<'a, PropertySpec<'a>>, ActionBlock<'a>),
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
        Option<(Local<'a>, Option<PropertyLvarPortDirection<'a>>)>,
        Option<PropertyFormalType<'a>>,
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
        Option<Bracket<'a, ConstantExpression<'a>>>,
        PropertyExpr<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct PropertyExprSNexttime<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<Bracket<'a, ConstantExpression<'a>>>,
        PropertyExpr<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct PropertyExprAlways<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<Bracket<'a, CycleDelayConstRangeExpression<'a>>>,
        PropertyExpr<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct PropertyExprSAlways<'a> {
    pub nodes: (
        Symbol<'a>,
        Bracket<'a, CycleDelayConstRangeExpression<'a>>,
        PropertyExpr<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct PropertyExprEventually<'a> {
    pub nodes: (Symbol<'a>, Bracket<'a, ConstantRange<'a>>, PropertyExpr<'a>),
}

#[derive(Debug, Node)]
pub struct PropertyExprSEventually<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<Bracket<'a, CycleDelayConstRangeExpression<'a>>>,
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
        Option<(Local<'a>, Option<SequenceLvarPortDirection<'a>>)>,
        Option<SequenceFormalType<'a>>,
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
    pub nodes: (Bracket<'a, (Symbol<'a>, ConstOrRangeExpression<'a>)>,),
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

#[parser]
pub fn concurrent_assertion_item(s: Span) -> IResult<Span, ConcurrentAssertionItem> {
    alt((
        concurrent_assertion_item_statement,
        map(checker_instantiation, |x| {
            ConcurrentAssertionItem::CheckerInstantiation(x)
        }),
    ))(s)
}

#[parser]
pub fn concurrent_assertion_item_statement(s: Span) -> IResult<Span, ConcurrentAssertionItem> {
    let (s, a) = opt(pair(block_identifier, symbol(":")))(s)?;
    let (s, b) = concurrent_assertion_statement(s)?;
    Ok((
        s,
        ConcurrentAssertionItem::Statement(ConcurrentAssertionItemStatement { nodes: (a, b) }),
    ))
}

#[parser]
pub fn concurrent_assertion_statement(s: Span) -> IResult<Span, ConcurrentAssertionStatement> {
    alt((
        map(assert_property_statement, |x| {
            ConcurrentAssertionStatement::AssertPropertyStatement(x)
        }),
        map(assume_property_statement, |x| {
            ConcurrentAssertionStatement::AssumePropertyStatement(x)
        }),
        map(cover_property_statement, |x| {
            ConcurrentAssertionStatement::CoverPropertyStatement(x)
        }),
        map(cover_sequence_statement, |x| {
            ConcurrentAssertionStatement::CoverSequenceStatement(x)
        }),
        map(restrict_property_statement, |x| {
            ConcurrentAssertionStatement::RestrictPropertyStatement(x)
        }),
    ))(s)
}

#[parser]
pub fn assert_property_statement(s: Span) -> IResult<Span, AssertPropertyStatement> {
    let (s, a) = symbol("assert")(s)?;
    let (s, b) = symbol("property")(s)?;
    let (s, c) = paren(property_spec)(s)?;
    let (s, d) = action_block(s)?;
    Ok((
        s,
        AssertPropertyStatement {
            nodes: (a, b, c, d),
        },
    ))
}

#[parser]
pub fn assume_property_statement(s: Span) -> IResult<Span, AssumePropertyStatement> {
    let (s, a) = symbol("assume")(s)?;
    let (s, b) = symbol("property")(s)?;
    let (s, c) = paren(property_spec)(s)?;
    let (s, d) = action_block(s)?;
    Ok((
        s,
        AssumePropertyStatement {
            nodes: (a, b, c, d),
        },
    ))
}

#[parser]
pub fn cover_property_statement(s: Span) -> IResult<Span, CoverPropertyStatement> {
    let (s, a) = symbol("cover")(s)?;
    let (s, b) = symbol("property")(s)?;
    let (s, c) = paren(property_spec)(s)?;
    let (s, d) = statement_or_null(s)?;
    Ok((
        s,
        CoverPropertyStatement {
            nodes: (a, b, c, d),
        },
    ))
}

#[parser]
pub fn expect_property_statement(s: Span) -> IResult<Span, ExpectPropertyStatement> {
    let (s, a) = symbol("expect")(s)?;
    let (s, b) = paren(property_spec)(s)?;
    let (s, c) = action_block(s)?;
    Ok((s, ExpectPropertyStatement { nodes: (a, b, c) }))
}

#[parser]
pub fn cover_sequence_statement(s: Span) -> IResult<Span, CoverSequenceStatement> {
    let (s, a) = symbol("cover")(s)?;
    let (s, b) = symbol("sequence")(s)?;
    let (s, c) = paren(triple(
        opt(clocking_event),
        opt(triple(
            symbol("disable"),
            symbol("iff"),
            paren(expression_or_dist),
        )),
        sequence_expr,
    ))(s)?;
    let (s, d) = statement_or_null(s)?;
    Ok((
        s,
        CoverSequenceStatement {
            nodes: (a, b, c, d),
        },
    ))
}

#[parser]
pub fn restrict_property_statement(s: Span) -> IResult<Span, RestrictPropertyStatement> {
    let (s, a) = symbol("restrict")(s)?;
    let (s, b) = symbol("property")(s)?;
    let (s, c) = paren(property_spec)(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        RestrictPropertyStatement {
            nodes: (a, b, c, d),
        },
    ))
}

#[parser]
pub fn property_instance(s: Span) -> IResult<Span, PropertyInstance> {
    let (s, a) = ps_or_hierarchical_property_identifier(s)?;
    let (s, b) = opt(paren(opt(property_list_of_arguments)))(s)?;
    Ok((s, PropertyInstance { nodes: (a, b) }))
}

#[parser]
pub fn property_list_of_arguments(s: Span) -> IResult<Span, PropertyListOfArguments> {
    alt((
        property_list_of_arguments_ordered,
        property_list_of_arguments_named,
    ))(s)
}

#[parser(MaybeRecursive)]
pub fn property_list_of_arguments_ordered(s: Span) -> IResult<Span, PropertyListOfArguments> {
    let (s, a) = list(symbol(","), opt(property_actual_arg))(s)?;
    let (s, b) = many0(tuple((
        symbol(","),
        symbol("."),
        identifier,
        paren(opt(property_actual_arg)),
    )))(s)?;
    Ok((
        s,
        PropertyListOfArguments::Ordered(PropertyListOfArgumentsOrdered { nodes: (a, b) }),
    ))
}

#[parser]
pub fn property_list_of_arguments_named(s: Span) -> IResult<Span, PropertyListOfArguments> {
    let (s, a) = list(
        symbol(","),
        triple(symbol("."), identifier, paren(opt(property_actual_arg))),
    )(s)?;
    Ok((
        s,
        PropertyListOfArguments::Named(PropertyListOfArgumentsNamed { nodes: (a,) }),
    ))
}

#[parser]
pub fn property_actual_arg(s: Span) -> IResult<Span, PropertyActualArg> {
    alt((
        map(property_expr, |x| PropertyActualArg::PropertyExpr(x)),
        map(sequence_actual_arg, |x| {
            PropertyActualArg::SequenceActualArg(x)
        }),
    ))(s)
}

#[parser]
pub fn assertion_item_declaration(s: Span) -> IResult<Span, AssertionItemDeclaration> {
    alt((
        map(property_declaration, |x| {
            AssertionItemDeclaration::PropertyDeclaration(x)
        }),
        map(sequence_declaration, |x| {
            AssertionItemDeclaration::SequenceDeclaration(x)
        }),
        map(let_declaration, |x| {
            AssertionItemDeclaration::LetDeclaration(x)
        }),
    ))(s)
}

#[parser]
pub fn property_declaration(s: Span) -> IResult<Span, PropertyDeclaration> {
    let (s, a) = symbol("property")(s)?;
    let (s, b) = property_identifier(s)?;
    let (s, c) = opt(paren(opt(property_port_list)))(s)?;
    let (s, d) = symbol(";")(s)?;
    let (s, e) = many0(assertion_variable_declaration)(s)?;
    let (s, f) = property_spec(s)?;
    let (s, g) = opt(symbol(";"))(s)?;
    let (s, h) = symbol("endproperty")(s)?;
    let (s, i) = opt(pair(symbol(":"), property_identifier))(s)?;
    Ok((
        s,
        PropertyDeclaration {
            nodes: (a, b, c, d, e, f, g, h, i),
        },
    ))
}

#[parser]
pub fn property_port_list(s: Span) -> IResult<Span, PropertyPortList> {
    let (s, a) = list(symbol(","), property_port_item)(s)?;
    Ok((s, PropertyPortList { nodes: (a,) }))
}

#[parser(Ambiguous)]
pub fn property_port_item(s: Span) -> IResult<Span, PropertyPortItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = opt(pair(local, opt(property_lvar_port_direction)))(s)?;
    let (s, c) = ambiguous_opt(property_formal_type)(s)?;
    let (s, d) = formal_port_identifier(s)?;
    let (s, e) = many0(variable_dimension)(s)?;
    let (s, f) = opt(pair(symbol("="), property_actual_arg))(s)?;
    Ok((
        s,
        PropertyPortItem {
            nodes: (a, b, c, d, e, f),
        },
    ))
}

#[parser]
pub fn property_lvar_port_direction(s: Span) -> IResult<Span, PropertyLvarPortDirection> {
    let (s, a) = symbol("input")(s)?;
    Ok((s, PropertyLvarPortDirection::Input(a)))
}

#[parser]
pub fn property_formal_type(s: Span) -> IResult<Span, PropertyFormalType> {
    alt((
        map(sequence_formal_type, |x| {
            PropertyFormalType::SequenceFormalType(x)
        }),
        map(symbol("property"), |x| PropertyFormalType::Property(x)),
    ))(s)
}

#[parser(MaybeRecursive)]
pub fn property_spec(s: Span) -> IResult<Span, PropertySpec> {
    let (s, a) = opt(clocking_event)(s)?;
    let (s, b) = opt(triple(
        symbol("disable"),
        symbol("iff"),
        paren(expression_or_dist),
    ))(s)?;
    let (s, c) = property_expr(s)?;
    Ok((s, PropertySpec { nodes: (a, b, c) }))
}

#[parser]
pub fn property_expr(s: Span) -> IResult<Span, PropertyExpr> {
    alt((
        alt((
            map(sequence_expr, |x| PropertyExpr::SequenceExpr(x)),
            property_expr_strong,
            property_expr_weak,
            property_expr_paren,
            property_expr_not,
            property_expr_or,
            property_expr_and,
            property_expr_implication_overlapped,
            property_expr_implication_nonoverlapped,
            property_expr_if,
            property_expr_case,
            property_expr_followed_by_overlapped,
            property_expr_followed_by_nonoverlapped,
            property_expr_nexttime,
            property_expr_s_nexttime,
        )),
        alt((
            property_expr_always,
            property_expr_s_always,
            property_expr_eventually,
            property_expr_s_eventually,
            property_expr_until,
            property_expr_s_until,
            property_expr_until_with,
            property_expr_s_until_with,
            property_expr_implies,
            property_expr_iff,
            property_expr_accept_on,
            property_expr_reject_on,
            property_expr_sync_accept_on,
            property_expr_sync_reject_on,
            map(property_instance, |x| {
                PropertyExpr::PropertyInstance(Box::new(x))
            }),
            property_expr_clocking_event,
        )),
    ))(s)
}

#[parser]
pub fn property_expr_strong(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = symbol("strong")(s)?;
    let (s, b) = paren(sequence_expr)(s)?;
    Ok((
        s,
        PropertyExpr::Strong(PropertyExprStrong { nodes: (a, b) }),
    ))
}

#[parser]
pub fn property_expr_weak(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = symbol("weak")(s)?;
    let (s, b) = paren(sequence_expr)(s)?;
    Ok((
        s,
        PropertyExpr::Strong(PropertyExprStrong { nodes: (a, b) }),
    ))
}

#[parser]
pub fn property_expr_paren(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = paren(sequence_expr)(s)?;
    Ok((
        s,
        PropertyExpr::Paren(Box::new(PropertyExprParen { nodes: (a,) })),
    ))
}

#[parser]
pub fn property_expr_not(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = symbol("not")(s)?;
    let (s, b) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::Not(Box::new(PropertyExprNot { nodes: (a, b) })),
    ))
}

#[parser(MaybeRecursive)]
pub fn property_expr_or(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = property_expr(s)?;
    let (s, b) = symbol("or")(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::Or(Box::new(PropertyExprOr { nodes: (a, b, c) })),
    ))
}

#[parser(MaybeRecursive)]
pub fn property_expr_and(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = property_expr(s)?;
    let (s, b) = symbol("and")(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::And(Box::new(PropertyExprAnd { nodes: (a, b, c) })),
    ))
}

#[parser(MaybeRecursive)]
pub fn property_expr_implication_overlapped(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = sequence_expr(s)?;
    let (s, b) = symbol("|->")(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::ImplicationOverlapped(Box::new(PropertyExprImplicationOverlapped {
            nodes: (a, b, c),
        })),
    ))
}

#[parser(MaybeRecursive)]
pub fn property_expr_implication_nonoverlapped(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = sequence_expr(s)?;
    let (s, b) = symbol("|=>")(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::ImplicationNonoverlapped(Box::new(PropertyExprImplicationNonoverlapped {
            nodes: (a, b, c),
        })),
    ))
}

#[parser]
pub fn property_expr_if(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = symbol("if")(s)?;
    let (s, b) = paren(expression_or_dist)(s)?;
    let (s, c) = property_expr(s)?;
    let (s, d) = opt(pair(symbol("else"), property_expr))(s)?;
    Ok((
        s,
        PropertyExpr::If(Box::new(PropertyExprIf {
            nodes: (a, b, c, d),
        })),
    ))
}

#[parser]
pub fn property_expr_case(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = symbol("case")(s)?;
    let (s, b) = paren(expression_or_dist)(s)?;
    let (s, c) = property_case_item(s)?;
    let (s, d) = many0(property_case_item)(s)?;
    let (s, e) = symbol("endcase")(s)?;
    Ok((
        s,
        PropertyExpr::Case(Box::new(PropertyExprCase {
            nodes: (a, b, c, d, e),
        })),
    ))
}

#[parser(MaybeRecursive)]
pub fn property_expr_followed_by_overlapped(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = sequence_expr(s)?;
    let (s, b) = symbol("#-#")(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::FollowedByOverlapped(Box::new(PropertyExprFollowedByOverlapped {
            nodes: (a, b, c),
        })),
    ))
}

#[parser(MaybeRecursive)]
pub fn property_expr_followed_by_nonoverlapped(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = sequence_expr(s)?;
    let (s, b) = symbol("#=#")(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::FollowedByNonoverlapped(Box::new(PropertyExprFollowedByNonoverlapped {
            nodes: (a, b, c),
        })),
    ))
}

#[parser]
pub fn property_expr_nexttime(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = symbol("nexttime")(s)?;
    let (s, b) = opt(bracket(constant_expression))(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::Nexttime(Box::new(PropertyExprNexttime { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn property_expr_s_nexttime(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = symbol("s_nexttime")(s)?;
    let (s, b) = opt(bracket(constant_expression))(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::SNexttime(Box::new(PropertyExprSNexttime { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn property_expr_always(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = symbol("always")(s)?;
    let (s, b) = opt(bracket(cycle_delay_const_range_expression))(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::Always(Box::new(PropertyExprAlways { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn property_expr_s_always(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = symbol("s_always")(s)?;
    let (s, b) = bracket(cycle_delay_const_range_expression)(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::SAlways(Box::new(PropertyExprSAlways { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn property_expr_eventually(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = symbol("eventually")(s)?;
    let (s, b) = bracket(constant_range)(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::Eventually(Box::new(PropertyExprEventually { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn property_expr_s_eventually(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = symbol("s_eventually")(s)?;
    let (s, b) = opt(bracket(cycle_delay_const_range_expression))(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::SEventually(Box::new(PropertyExprSEventually { nodes: (a, b, c) })),
    ))
}

#[parser(MaybeRecursive)]
pub fn property_expr_until(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = property_expr(s)?;
    let (s, b) = symbol("until")(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::Until(Box::new(PropertyExprUntil { nodes: (a, b, c) })),
    ))
}

#[parser(MaybeRecursive)]
pub fn property_expr_s_until(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = property_expr(s)?;
    let (s, b) = symbol("s_until")(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::SUntil(Box::new(PropertyExprSUntil { nodes: (a, b, c) })),
    ))
}

#[parser(MaybeRecursive)]
pub fn property_expr_until_with(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = property_expr(s)?;
    let (s, b) = symbol("until_with")(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::UntilWith(Box::new(PropertyExprUntilWith { nodes: (a, b, c) })),
    ))
}

#[parser(MaybeRecursive)]
pub fn property_expr_s_until_with(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = property_expr(s)?;
    let (s, b) = symbol("s_until_with")(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::SUntilWith(Box::new(PropertyExprSUntilWith { nodes: (a, b, c) })),
    ))
}

#[parser(MaybeRecursive)]
pub fn property_expr_implies(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = property_expr(s)?;
    let (s, b) = symbol("implies")(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::Implies(Box::new(PropertyExprImplies { nodes: (a, b, c) })),
    ))
}

#[parser(MaybeRecursive)]
pub fn property_expr_iff(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = property_expr(s)?;
    let (s, b) = symbol("iff")(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::Iff(Box::new(PropertyExprIff { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn property_expr_accept_on(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = symbol("accept_on")(s)?;
    let (s, b) = paren(expression_or_dist)(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::AcceptOn(Box::new(PropertyExprAcceptOn { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn property_expr_reject_on(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = symbol("reject_on")(s)?;
    let (s, b) = paren(expression_or_dist)(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::RejectOn(Box::new(PropertyExprRejectOn { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn property_expr_sync_accept_on(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = symbol("sync_accept_on")(s)?;
    let (s, b) = paren(expression_or_dist)(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::SyncAcceptOn(Box::new(PropertyExprSyncAcceptOn { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn property_expr_sync_reject_on(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = symbol("sync_reject_on")(s)?;
    let (s, b) = paren(expression_or_dist)(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::SyncRejectOn(Box::new(PropertyExprSyncRejectOn { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn property_expr_clocking_event(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = clocking_event(s)?;
    let (s, b) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::ClockingEvent(Box::new(PropertyExprClockingEvent { nodes: (a, b) })),
    ))
}

#[parser]
pub fn property_case_item(s: Span) -> IResult<Span, PropertyCaseItem> {
    alt((property_case_item_nondefault, property_case_item_default))(s)
}

#[parser(MaybeRecursive)]
pub fn property_case_item_nondefault(s: Span) -> IResult<Span, PropertyCaseItem> {
    let (s, a) = list(symbol(","), expression_or_dist)(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = property_expr(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        PropertyCaseItem::Nondefault(PropertyCaseItemNondefault {
            nodes: (a, b, c, d),
        }),
    ))
}

#[parser]
pub fn property_case_item_default(s: Span) -> IResult<Span, PropertyCaseItem> {
    let (s, a) = symbol("default")(s)?;
    let (s, b) = opt(symbol(":"))(s)?;
    let (s, c) = property_expr(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        PropertyCaseItem::Default(PropertyCaseItemDefault {
            nodes: (a, b, c, d),
        }),
    ))
}

#[parser]
pub fn sequence_declaration(s: Span) -> IResult<Span, SequenceDeclaration> {
    let (s, a) = symbol("sequence")(s)?;
    let (s, b) = sequence_identifier(s)?;
    let (s, c) = opt(paren(opt(sequence_port_list)))(s)?;
    let (s, d) = symbol(";")(s)?;
    let (s, e) = many0(assertion_variable_declaration)(s)?;
    let (s, f) = sequence_expr(s)?;
    let (s, g) = opt(symbol(";"))(s)?;
    let (s, h) = symbol("endsequence")(s)?;
    let (s, i) = opt(pair(symbol(":"), sequence_identifier))(s)?;
    Ok((
        s,
        SequenceDeclaration {
            nodes: (a, b, c, d, e, f, g, h, i),
        },
    ))
}

#[parser]
pub fn sequence_port_list(s: Span) -> IResult<Span, SequencePortList> {
    let (s, a) = list(symbol(","), sequence_port_item)(s)?;
    Ok((s, SequencePortList { nodes: (a,) }))
}

#[parser(Ambiguous)]
pub fn sequence_port_item(s: Span) -> IResult<Span, SequencePortItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = opt(pair(local, opt(sequence_lvar_port_direction)))(s)?;
    let (s, c) = ambiguous_opt(sequence_formal_type)(s)?;
    let (s, d) = formal_port_identifier(s)?;
    let (s, e) = many0(variable_dimension)(s)?;
    let (s, f) = opt(pair(symbol("="), sequence_actual_arg))(s)?;
    Ok((
        s,
        SequencePortItem {
            nodes: (a, b, c, d, e, f),
        },
    ))
}

#[parser]
pub fn sequence_lvar_port_direction(s: Span) -> IResult<Span, SequenceLvarPortDirection> {
    alt((
        map(symbol("input"), |x| SequenceLvarPortDirection::Input(x)),
        map(symbol("inout"), |x| SequenceLvarPortDirection::Inout(x)),
        map(symbol("output"), |x| SequenceLvarPortDirection::Output(x)),
    ))(s)
}

#[parser]
pub fn sequence_formal_type(s: Span) -> IResult<Span, SequenceFormalType> {
    alt((
        map(data_type_or_implicit, |x| {
            SequenceFormalType::DataTypeOrImplicit(x)
        }),
        map(symbol("sequence"), |x| SequenceFormalType::Sequence(x)),
        map(symbol("untyped"), |x| SequenceFormalType::Untyped(x)),
    ))(s)
}

#[parser]
pub fn sequence_expr(s: Span) -> IResult<Span, SequenceExpr> {
    alt((
        sequence_expr_cycle_delay_expr,
        sequence_expr_expr_cycle_delay_expr,
        sequence_expr_expression,
        sequence_expr_instance,
        sequence_expr_paren,
        sequence_expr_and,
        sequence_expr_intersect,
        sequence_expr_or,
        sequence_expr_first_match,
        sequence_expr_throughout,
        sequence_expr_within,
        sequence_expr_clocking_event,
    ))(s)
}

#[parser]
pub fn sequence_expr_cycle_delay_expr(s: Span) -> IResult<Span, SequenceExpr> {
    let (s, a) = cycle_delay_range(s)?;
    let (s, b) = sequence_expr(s)?;
    let (s, c) = many0(pair(cycle_delay_range, sequence_expr))(s)?;
    Ok((
        s,
        SequenceExpr::CycleDelayExpr(Box::new(SequenceExprCycleDelayExpr { nodes: (a, b, c) })),
    ))
}

#[parser(MaybeRecursive)]
pub fn sequence_expr_expr_cycle_delay_expr(s: Span) -> IResult<Span, SequenceExpr> {
    let (s, a) = sequence_expr(s)?;
    let (s, b) = cycle_delay_range(s)?;
    let (s, c) = sequence_expr(s)?;
    let (s, d) = many0(pair(cycle_delay_range, sequence_expr))(s)?;
    Ok((
        s,
        SequenceExpr::ExprCycleDelayExpr(Box::new(SequenceExprExprCycleDelayExpr {
            nodes: (a, b, c, d),
        })),
    ))
}

#[parser(MaybeRecursive)]
pub fn sequence_expr_expression(s: Span) -> IResult<Span, SequenceExpr> {
    let (s, a) = expression_or_dist(s)?;
    let (s, b) = opt(boolean_abbrev)(s)?;
    Ok((
        s,
        SequenceExpr::Expression(SequenceExprExpression { nodes: (a, b) }),
    ))
}

#[parser]
pub fn sequence_expr_instance(s: Span) -> IResult<Span, SequenceExpr> {
    let (s, a) = sequence_instance(s)?;
    let (s, b) = opt(sequence_abbrev)(s)?;
    Ok((
        s,
        SequenceExpr::Instance(Box::new(SequenceExprInstance { nodes: (a, b) })),
    ))
}

#[parser]
pub fn sequence_expr_paren(s: Span) -> IResult<Span, SequenceExpr> {
    let (s, a) = paren(pair(
        sequence_expr,
        many0(pair(symbol(","), sequence_match_item)),
    ))(s)?;
    let (s, b) = opt(sequence_abbrev)(s)?;
    Ok((
        s,
        SequenceExpr::Paren(Box::new(SequenceExprParen { nodes: (a, b) })),
    ))
}

#[parser(MaybeRecursive)]
pub fn sequence_expr_and(s: Span) -> IResult<Span, SequenceExpr> {
    let (s, a) = sequence_expr(s)?;
    let (s, b) = symbol("and")(s)?;
    let (s, c) = sequence_expr(s)?;
    Ok((
        s,
        SequenceExpr::And(Box::new(SequenceExprAnd { nodes: (a, b, c) })),
    ))
}

#[parser(MaybeRecursive)]
pub fn sequence_expr_intersect(s: Span) -> IResult<Span, SequenceExpr> {
    let (s, a) = sequence_expr(s)?;
    let (s, b) = symbol("intersect")(s)?;
    let (s, c) = sequence_expr(s)?;
    Ok((
        s,
        SequenceExpr::Intersect(Box::new(SequenceExprIntersect { nodes: (a, b, c) })),
    ))
}

#[parser(MaybeRecursive)]
pub fn sequence_expr_or(s: Span) -> IResult<Span, SequenceExpr> {
    let (s, a) = sequence_expr(s)?;
    let (s, b) = symbol("or")(s)?;
    let (s, c) = sequence_expr(s)?;
    Ok((
        s,
        SequenceExpr::Or(Box::new(SequenceExprOr { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn sequence_expr_first_match(s: Span) -> IResult<Span, SequenceExpr> {
    let (s, a) = symbol("first_match")(s)?;
    let (s, b) = paren(pair(
        sequence_expr,
        many0(pair(symbol(","), sequence_match_item)),
    ))(s)?;
    Ok((
        s,
        SequenceExpr::FirstMatch(Box::new(SequenceExprFirstMatch { nodes: (a, b) })),
    ))
}

#[parser(MaybeRecursive)]
pub fn sequence_expr_throughout(s: Span) -> IResult<Span, SequenceExpr> {
    let (s, a) = expression_or_dist(s)?;
    let (s, b) = symbol("throughout")(s)?;
    let (s, c) = sequence_expr(s)?;
    Ok((
        s,
        SequenceExpr::Throughout(Box::new(SequenceExprThroughout { nodes: (a, b, c) })),
    ))
}

#[parser(MaybeRecursive)]
pub fn sequence_expr_within(s: Span) -> IResult<Span, SequenceExpr> {
    let (s, a) = sequence_expr(s)?;
    let (s, b) = symbol("within")(s)?;
    let (s, c) = sequence_expr(s)?;
    Ok((
        s,
        SequenceExpr::Within(Box::new(SequenceExprWithin { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn sequence_expr_clocking_event(s: Span) -> IResult<Span, SequenceExpr> {
    let (s, a) = clocking_event(s)?;
    let (s, b) = sequence_expr(s)?;
    Ok((
        s,
        SequenceExpr::ClockingEvent(Box::new(SequenceExprClockingEvent { nodes: (a, b) })),
    ))
}

#[parser]
pub fn cycle_delay_range(s: Span) -> IResult<Span, CycleDelayRange> {
    alt((
        cycle_delay_range_primary,
        cycle_delay_range_expression,
        cycle_delay_range_asterisk,
        cycle_delay_range_plus,
    ))(s)
}

#[parser]
pub fn cycle_delay_range_primary(s: Span) -> IResult<Span, CycleDelayRange> {
    let (s, a) = symbol("##")(s)?;
    let (s, b) = constant_primary(s)?;
    Ok((
        s,
        CycleDelayRange::Primary(CycleDelayRangePrimary { nodes: (a, b) }),
    ))
}

#[parser]
pub fn cycle_delay_range_expression(s: Span) -> IResult<Span, CycleDelayRange> {
    let (s, a) = symbol("##")(s)?;
    let (s, b) = bracket(cycle_delay_const_range_expression)(s)?;
    Ok((
        s,
        CycleDelayRange::Expression(CycleDelayRangeExpression { nodes: (a, b) }),
    ))
}

#[parser]
pub fn cycle_delay_range_asterisk(s: Span) -> IResult<Span, CycleDelayRange> {
    let (s, a) = symbol("##")(s)?;
    let (s, b) = bracket(symbol("*"))(s)?;
    Ok((
        s,
        CycleDelayRange::Asterisk(CycleDelayRangeAsterisk { nodes: (a, b) }),
    ))
}

#[parser]
pub fn cycle_delay_range_plus(s: Span) -> IResult<Span, CycleDelayRange> {
    let (s, a) = symbol("##")(s)?;
    let (s, b) = bracket(symbol("+"))(s)?;
    Ok((
        s,
        CycleDelayRange::Plus(CycleDelayRangePlus { nodes: (a, b) }),
    ))
}

#[parser]
pub fn sequence_method_call(s: Span) -> IResult<Span, SequenceMethodCall> {
    let (s, a) = sequence_instance(s)?;
    let (s, b) = symbol(".")(s)?;
    let (s, c) = method_identifier(s)?;
    Ok((s, SequenceMethodCall { nodes: (a, b, c) }))
}

#[parser]
pub fn sequence_match_item(s: Span) -> IResult<Span, SequenceMatchItem> {
    alt((
        map(operator_assignment, |x| {
            SequenceMatchItem::OperatorAssignment(x)
        }),
        map(inc_or_dec_expression, |x| {
            SequenceMatchItem::IncOrDecExpression(x)
        }),
        map(subroutine_call, |x| SequenceMatchItem::SubroutineCall(x)),
    ))(s)
}

#[parser]
pub fn sequence_instance(s: Span) -> IResult<Span, SequenceInstance> {
    let (s, a) = ps_or_hierarchical_sequence_identifier(s)?;
    let (s, b) = opt(paren(opt(sequence_list_of_arguments)))(s)?;
    Ok((s, SequenceInstance { nodes: (a, b) }))
}

#[parser]
pub fn sequence_list_of_arguments(s: Span) -> IResult<Span, SequenceListOfArguments> {
    alt((
        sequence_list_of_arguments_ordered,
        sequence_list_of_arguments_named,
    ))(s)
}

#[parser(MaybeRecursive)]
pub fn sequence_list_of_arguments_ordered(s: Span) -> IResult<Span, SequenceListOfArguments> {
    let (s, a) = list(symbol(","), opt(sequence_actual_arg))(s)?;
    let (s, b) = many0(tuple((
        symbol(","),
        symbol("."),
        identifier,
        paren(opt(sequence_actual_arg)),
    )))(s)?;
    Ok((
        s,
        SequenceListOfArguments::Ordered(SequenceListOfArgumentsOrdered { nodes: (a, b) }),
    ))
}

#[parser]
pub fn sequence_list_of_arguments_named(s: Span) -> IResult<Span, SequenceListOfArguments> {
    let (s, a) = list(
        symbol(","),
        triple(symbol("."), identifier, paren(opt(sequence_actual_arg))),
    )(s)?;
    Ok((
        s,
        SequenceListOfArguments::Named(SequenceListOfArgumentsNamed { nodes: (a,) }),
    ))
}

#[parser]
pub fn sequence_actual_arg(s: Span) -> IResult<Span, SequenceActualArg> {
    alt((
        map(event_expression, |x| SequenceActualArg::EventExpression(x)),
        map(sequence_expr, |x| SequenceActualArg::SequenceExpr(x)),
    ))(s)
}

#[parser]
pub fn boolean_abbrev(s: Span) -> IResult<Span, BooleanAbbrev> {
    alt((
        map(consecutive_repetition, |x| {
            BooleanAbbrev::ConsecutiveRepetition(x)
        }),
        map(non_consecutive_repetition, |x| {
            BooleanAbbrev::NonConsecutiveRepetition(x)
        }),
        map(goto_repetition, |x| BooleanAbbrev::GotoRepetition(x)),
    ))(s)
}

#[parser]
pub fn sequence_abbrev(s: Span) -> IResult<Span, SequenceAbbrev> {
    let (s, a) = consecutive_repetition(s)?;
    Ok((s, SequenceAbbrev { nodes: (a,) }))
}

#[parser]
pub fn consecutive_repetition(s: Span) -> IResult<Span, ConsecutiveRepetition> {
    alt((
        consecutive_repetition_expression,
        consecutive_repetition_asterisk,
        consecutive_repetition_plus,
    ))(s)
}

#[parser]
pub fn consecutive_repetition_expression(s: Span) -> IResult<Span, ConsecutiveRepetition> {
    let (s, a) = bracket(pair(symbol("*"), const_or_range_expression))(s)?;
    Ok((
        s,
        ConsecutiveRepetition::Expression(ConsecutiveRepetitionExpression { nodes: (a,) }),
    ))
}

#[parser]
pub fn consecutive_repetition_asterisk(s: Span) -> IResult<Span, ConsecutiveRepetition> {
    let (s, a) = bracket(symbol("*"))(s)?;
    Ok((
        s,
        ConsecutiveRepetition::Asterisk(ConsecutiveRepetitionAsterisk { nodes: (a,) }),
    ))
}

#[parser]
pub fn consecutive_repetition_plus(s: Span) -> IResult<Span, ConsecutiveRepetition> {
    let (s, a) = bracket(symbol("+"))(s)?;
    Ok((
        s,
        ConsecutiveRepetition::Plus(ConsecutiveRepetitionPlus { nodes: (a,) }),
    ))
}

#[parser]
pub fn non_consecutive_repetition(s: Span) -> IResult<Span, NonConsecutiveRepetition> {
    let (s, a) = bracket(pair(symbol("="), const_or_range_expression))(s)?;
    Ok((s, NonConsecutiveRepetition { nodes: (a,) }))
}

#[parser]
pub fn goto_repetition(s: Span) -> IResult<Span, GotoRepetition> {
    let (s, a) = bracket(pair(symbol("->"), const_or_range_expression))(s)?;
    Ok((s, GotoRepetition { nodes: (a,) }))
}

#[parser]
pub fn const_or_range_expression(s: Span) -> IResult<Span, ConstOrRangeExpression> {
    alt((
        map(constant_expression, |x| {
            ConstOrRangeExpression::ConstantExpression(x)
        }),
        map(cycle_delay_const_range_expression, |x| {
            ConstOrRangeExpression::CycleDelayConstRangeExpression(x)
        }),
    ))(s)
}

#[parser]
pub fn cycle_delay_const_range_expression(
    s: Span,
) -> IResult<Span, CycleDelayConstRangeExpression> {
    alt((
        cycle_delay_const_range_expression_binary,
        cycle_delay_const_range_expression_dollar,
    ))(s)
}

#[parser(MaybeRecursive)]
pub fn cycle_delay_const_range_expression_binary(
    s: Span,
) -> IResult<Span, CycleDelayConstRangeExpression> {
    let (s, a) = constant_expression(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = constant_expression(s)?;
    Ok((
        s,
        CycleDelayConstRangeExpression::Binary(CycleDelayConstRangeExpressionBinary {
            nodes: (a, b, c),
        }),
    ))
}

#[parser(MaybeRecursive)]
pub fn cycle_delay_const_range_expression_dollar(
    s: Span,
) -> IResult<Span, CycleDelayConstRangeExpression> {
    let (s, a) = constant_expression(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = symbol("$")(s)?;
    Ok((
        s,
        CycleDelayConstRangeExpression::Dollar(CycleDelayConstRangeExpressionDollar {
            nodes: (a, b, c),
        }),
    ))
}

#[parser(MaybeRecursive)]
pub fn expression_or_dist(s: Span) -> IResult<Span, ExpressionOrDist> {
    let (s, a) = expression(s)?;
    let (s, b) = opt(pair(symbol("dist"), brace(dist_list)))(s)?;
    Ok((s, ExpressionOrDist { nodes: (a, b) }))
}

#[parser]
pub fn assertion_variable_declaration(s: Span) -> IResult<Span, AssertionVariableDeclaration> {
    let (s, a) = var_data_type(s)?;
    let (s, b) = list_of_variable_decl_assignments(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((s, AssertionVariableDeclaration { nodes: (a, b, c) }))
}

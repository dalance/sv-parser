use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct InitialConstruct<'a> {
    pub nodes: (StatementOrNull<'a>,),
}

#[derive(Debug)]
pub struct AlwaysConstruct<'a> {
    pub nodes: (AlwaysKeyword, Statement<'a>),
}

#[derive(Debug)]
pub enum AlwaysKeyword {
    Always,
    AlwaysComb,
    AlwaysLatch,
    AlwaysFf,
}

#[derive(Debug)]
pub struct FinalConstruct<'a> {
    pub nodes: (FunctionStatement<'a>,),
}

#[derive(Debug)]
pub enum BlockingAssignment<'a> {
    Variable(BlockingAssignmentVariable<'a>),
    NonrangeVariable(BlockingAssignmentNonrangeVariable<'a>),
    HierarchicalVariable(BlockingAssignmentHierarchicalVariable<'a>),
    Operator(OperatorAssignment<'a>),
}

#[derive(Debug)]
pub struct BlockingAssignmentVariable<'a> {
    pub nodes: (VariableLvalue<'a>, DelayOrEventControl<'a>, Expression<'a>),
}

#[derive(Debug)]
pub struct BlockingAssignmentNonrangeVariable<'a> {
    pub nodes: (NonrangeVariableLvalue<'a>, DynamicArrayNew<'a>),
}

#[derive(Debug)]
pub struct BlockingAssignmentHierarchicalVariable<'a> {
    pub nodes: (
        Option<ImplicitClassHandleOrClassScopeOrPackageScope<'a>>,
        HierarchicalVariableIdentifier<'a>,
        Select<'a>,
        ClassNew<'a>,
    ),
}

#[derive(Debug)]
pub struct OperatorAssignment<'a> {
    pub nodes: (VariableLvalue<'a>, AssignmentOperator<'a>, Expression<'a>),
}

#[derive(Debug)]
pub struct AssignmentOperator<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug)]
pub struct NonblockingAssignment<'a> {
    pub nodes: (
        VariableLvalue<'a>,
        Option<DelayOrEventControl<'a>>,
        Expression<'a>,
    ),
}

#[derive(Debug)]
pub enum ProceduralContinuousAssignment<'a> {
    Assign(VariableAssignment<'a>),
    Deassign(VariableLvalue<'a>),
    ForceVariable(VariableAssignment<'a>),
    ForceNet(NetAssignment<'a>),
    ReleaseVariable(VariableLvalue<'a>),
    ReleaseNet(NetLvalue<'a>),
}

#[derive(Debug)]
pub struct VariableAssignment<'a> {
    pub nodes: (VariableLvalue<'a>, Expression<'a>),
}

// -----------------------------------------------------------------------------

pub fn initial_construct(s: Span) -> IResult<Span, InitialConstruct> {
    let (s, _) = symbol("initial")(s)?;
    let (s, x) = statement_or_null(s)?;
    Ok((s, InitialConstruct { nodes: (x,) }))
}

pub fn always_construct(s: Span) -> IResult<Span, AlwaysConstruct> {
    let (s, x) = always_keyword(s)?;
    let (s, y) = statement(s)?;
    Ok((s, AlwaysConstruct { nodes: (x, y) }))
}

pub fn always_keyword(s: Span) -> IResult<Span, AlwaysKeyword> {
    alt((
        map(symbol("always_comb"), |_| AlwaysKeyword::AlwaysComb),
        map(symbol("always_latch"), |_| AlwaysKeyword::AlwaysLatch),
        map(symbol("always_ff"), |_| AlwaysKeyword::AlwaysFf),
        map(symbol("always"), |_| AlwaysKeyword::Always),
    ))(s)
}

pub fn final_construct(s: Span) -> IResult<Span, FinalConstruct> {
    let (s, _) = symbol("final")(s)?;
    let (s, x) = function_statement(s)?;
    Ok((s, FinalConstruct { nodes: (x,) }))
}

pub fn blocking_assignment(s: Span) -> IResult<Span, BlockingAssignment> {
    alt((
        blocking_assignment_variable,
        blocking_assignment_nonrange_variable,
        blocking_assignment_hierarchical_variable,
        map(operator_assignment, |x| BlockingAssignment::Operator(x)),
    ))(s)
}

pub fn blocking_assignment_variable(s: Span) -> IResult<Span, BlockingAssignment> {
    let (s, x) = variable_lvalue(s)?;
    let (s, _) = symbol("=")(s)?;
    let (s, y) = delay_or_event_control(s)?;
    let (s, z) = expression(s)?;
    Ok((
        s,
        BlockingAssignment::Variable(BlockingAssignmentVariable { nodes: (x, y, z) }),
    ))
}

pub fn blocking_assignment_nonrange_variable(s: Span) -> IResult<Span, BlockingAssignment> {
    let (s, x) = nonrange_variable_lvalue(s)?;
    let (s, _) = symbol("=")(s)?;
    let (s, y) = dynamic_array_new(s)?;
    Ok((
        s,
        BlockingAssignment::NonrangeVariable(BlockingAssignmentNonrangeVariable { nodes: (x, y) }),
    ))
}

pub fn blocking_assignment_hierarchical_variable(s: Span) -> IResult<Span, BlockingAssignment> {
    let (s, x) = opt(implicit_class_handle_or_class_scope_or_package_scope)(s)?;
    let (s, y) = hierarchical_variable_identifier(s)?;
    let (s, z) = select(s)?;
    let (s, _) = symbol("=")(s)?;
    let (s, v) = class_new(s)?;
    Ok((
        s,
        BlockingAssignment::HierarchicalVariable(BlockingAssignmentHierarchicalVariable {
            nodes: (x, y, z, v),
        }),
    ))
}

pub fn operator_assignment(s: Span) -> IResult<Span, OperatorAssignment> {
    let (s, x) = variable_lvalue(s)?;
    let (s, y) = assignment_operator(s)?;
    let (s, z) = expression(s)?;
    Ok((s, OperatorAssignment { nodes: (x, y, z) }))
}

pub fn assignment_operator(s: Span) -> IResult<Span, AssignmentOperator> {
    alt((
        map(symbol("="), |x| AssignmentOperator { nodes: (x,) }),
        map(symbol("+="), |x| AssignmentOperator { nodes: (x,) }),
        map(symbol("-="), |x| AssignmentOperator { nodes: (x,) }),
        map(symbol("*="), |x| AssignmentOperator { nodes: (x,) }),
        map(symbol("/="), |x| AssignmentOperator { nodes: (x,) }),
        map(symbol("%="), |x| AssignmentOperator { nodes: (x,) }),
        map(symbol("&="), |x| AssignmentOperator { nodes: (x,) }),
        map(symbol("|="), |x| AssignmentOperator { nodes: (x,) }),
        map(symbol("^="), |x| AssignmentOperator { nodes: (x,) }),
        map(symbol("<<<="), |x| AssignmentOperator { nodes: (x,) }),
        map(symbol(">>>="), |x| AssignmentOperator { nodes: (x,) }),
        map(symbol("<<="), |x| AssignmentOperator { nodes: (x,) }),
        map(symbol(">>="), |x| AssignmentOperator { nodes: (x,) }),
    ))(s)
}

pub fn nonblocking_assignment(s: Span) -> IResult<Span, NonblockingAssignment> {
    let (s, x) = variable_lvalue(s)?;
    let (s, _) = symbol("<=")(s)?;
    let (s, y) = opt(delay_or_event_control)(s)?;
    let (s, z) = expression(s)?;
    Ok((s, NonblockingAssignment { nodes: (x, y, z) }))
}

pub fn procedural_continuous_assignment(s: Span) -> IResult<Span, ProceduralContinuousAssignment> {
    alt((
        map(preceded(symbol("assign"), variable_assignment), |x| {
            ProceduralContinuousAssignment::Assign(x)
        }),
        map(preceded(symbol("deassign"), variable_lvalue), |x| {
            ProceduralContinuousAssignment::Deassign(x)
        }),
        map(preceded(symbol("force"), variable_assignment), |x| {
            ProceduralContinuousAssignment::ForceVariable(x)
        }),
        map(preceded(symbol("force"), net_assignment), |x| {
            ProceduralContinuousAssignment::ForceNet(x)
        }),
        map(preceded(symbol("release"), variable_lvalue), |x| {
            ProceduralContinuousAssignment::ReleaseVariable(x)
        }),
        map(preceded(symbol("release"), net_lvalue), |x| {
            ProceduralContinuousAssignment::ReleaseNet(x)
        }),
    ))(s)
}

pub fn variable_assignment(s: Span) -> IResult<Span, VariableAssignment> {
    let (s, x) = variable_lvalue(s)?;
    let (s, _) = symbol("=")(s)?;
    let (s, y) = expression(s)?;
    Ok((s, VariableAssignment { nodes: (x, y) }))
}

use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct InitialConstruct<'a> {
    pub nodes: (Keyword<'a>, StatementOrNull<'a>),
}

#[derive(Debug, Node)]
pub struct AlwaysConstruct<'a> {
    pub nodes: (AlwaysKeyword<'a>, Statement<'a>),
}

#[derive(Debug, Node)]
pub enum AlwaysKeyword<'a> {
    Always(Keyword<'a>),
    AlwaysComb(Keyword<'a>),
    AlwaysLatch(Keyword<'a>),
    AlwaysFf(Keyword<'a>),
}

#[derive(Debug, Node)]
pub struct FinalConstruct<'a> {
    pub nodes: (Keyword<'a>, FunctionStatement<'a>),
}

#[derive(Debug, Node)]
pub enum BlockingAssignment<'a> {
    Variable(BlockingAssignmentVariable<'a>),
    NonrangeVariable(BlockingAssignmentNonrangeVariable<'a>),
    HierarchicalVariable(BlockingAssignmentHierarchicalVariable<'a>),
    OperatorAssignment(OperatorAssignment<'a>),
}

#[derive(Debug, Node)]
pub struct BlockingAssignmentVariable<'a> {
    pub nodes: (
        VariableLvalue<'a>,
        Symbol<'a>,
        DelayOrEventControl<'a>,
        Expression<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct BlockingAssignmentNonrangeVariable<'a> {
    pub nodes: (NonrangeVariableLvalue<'a>, Symbol<'a>, DynamicArrayNew<'a>),
}

#[derive(Debug, Node)]
pub struct BlockingAssignmentHierarchicalVariable<'a> {
    pub nodes: (
        Option<ImplicitClassHandleOrClassScopeOrPackageScope<'a>>,
        HierarchicalVariableIdentifier<'a>,
        Select<'a>,
        Symbol<'a>,
        ClassNew<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct OperatorAssignment<'a> {
    pub nodes: (VariableLvalue<'a>, AssignmentOperator<'a>, Expression<'a>),
}

#[derive(Debug, Node)]
pub struct AssignmentOperator<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug, Node)]
pub struct NonblockingAssignment<'a> {
    pub nodes: (
        VariableLvalue<'a>,
        Symbol<'a>,
        Option<DelayOrEventControl<'a>>,
        Expression<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum ProceduralContinuousAssignment<'a> {
    Assign(ProceduralContinuousAssignmentAssign<'a>),
    Deassign(ProceduralContinuousAssignmentDeassign<'a>),
    ForceVariable(ProceduralContinuousAssignmentForceVariable<'a>),
    ForceNet(ProceduralContinuousAssignmentForceNet<'a>),
    ReleaseVariable(ProceduralContinuousAssignmentReleaseVariable<'a>),
    ReleaseNet(ProceduralContinuousAssignmentReleaseNet<'a>),
}

#[derive(Debug, Node)]
pub struct ProceduralContinuousAssignmentAssign<'a> {
    pub nodes: (Keyword<'a>, VariableAssignment<'a>),
}

#[derive(Debug, Node)]
pub struct ProceduralContinuousAssignmentDeassign<'a> {
    pub nodes: (Keyword<'a>, VariableLvalue<'a>),
}

#[derive(Debug, Node)]
pub struct ProceduralContinuousAssignmentForceVariable<'a> {
    pub nodes: (Keyword<'a>, VariableAssignment<'a>),
}

#[derive(Debug, Node)]
pub struct ProceduralContinuousAssignmentForceNet<'a> {
    pub nodes: (Keyword<'a>, NetAssignment<'a>),
}

#[derive(Debug, Node)]
pub struct ProceduralContinuousAssignmentReleaseVariable<'a> {
    pub nodes: (Keyword<'a>, VariableLvalue<'a>),
}

#[derive(Debug, Node)]
pub struct ProceduralContinuousAssignmentReleaseNet<'a> {
    pub nodes: (Keyword<'a>, NetLvalue<'a>),
}

#[derive(Debug, Node)]
pub struct VariableAssignment<'a> {
    pub nodes: (VariableLvalue<'a>, Symbol<'a>, Expression<'a>),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn initial_construct(s: Span) -> IResult<Span, InitialConstruct> {
    let (s, a) = keyword("initial")(s)?;
    let (s, b) = statement_or_null(s)?;
    Ok((s, InitialConstruct { nodes: (a, b) }))
}

#[parser]
pub fn always_construct(s: Span) -> IResult<Span, AlwaysConstruct> {
    let (s, a) = always_keyword(s)?;
    let (s, b) = statement(s)?;
    Ok((s, AlwaysConstruct { nodes: (a, b) }))
}

#[parser]
pub fn always_keyword(s: Span) -> IResult<Span, AlwaysKeyword> {
    alt((
        map(keyword("always_comb"), |x| AlwaysKeyword::AlwaysComb(x)),
        map(keyword("always_latch"), |x| AlwaysKeyword::AlwaysLatch(x)),
        map(keyword("always_ff"), |x| AlwaysKeyword::AlwaysFf(x)),
        map(keyword("always"), |x| AlwaysKeyword::Always(x)),
    ))(s)
}

#[parser]
pub fn final_construct(s: Span) -> IResult<Span, FinalConstruct> {
    let (s, a) = keyword("final")(s)?;
    let (s, b) = function_statement(s)?;
    Ok((s, FinalConstruct { nodes: (a, b) }))
}

#[parser]
pub fn blocking_assignment(s: Span) -> IResult<Span, BlockingAssignment> {
    alt((
        blocking_assignment_variable,
        blocking_assignment_nonrange_variable,
        blocking_assignment_hierarchical_variable,
        map(operator_assignment, |x| {
            BlockingAssignment::OperatorAssignment(x)
        }),
    ))(s)
}

#[parser(MaybeRecursive)]
pub fn blocking_assignment_variable(s: Span) -> IResult<Span, BlockingAssignment> {
    let (s, a) = variable_lvalue(s)?;
    let (s, b) = symbol("=")(s)?;
    let (s, c) = delay_or_event_control(s)?;
    let (s, d) = expression(s)?;
    Ok((
        s,
        BlockingAssignment::Variable(BlockingAssignmentVariable {
            nodes: (a, b, c, d),
        }),
    ))
}

#[parser(MaybeRecursive)]
pub fn blocking_assignment_nonrange_variable(s: Span) -> IResult<Span, BlockingAssignment> {
    let (s, a) = nonrange_variable_lvalue(s)?;
    let (s, b) = symbol("=")(s)?;
    let (s, c) = dynamic_array_new(s)?;
    Ok((
        s,
        BlockingAssignment::NonrangeVariable(BlockingAssignmentNonrangeVariable {
            nodes: (a, b, c),
        }),
    ))
}

#[parser]
pub fn blocking_assignment_hierarchical_variable(s: Span) -> IResult<Span, BlockingAssignment> {
    let (s, a) = opt(implicit_class_handle_or_class_scope_or_package_scope)(s)?;
    let (s, b) = hierarchical_variable_identifier(s)?;
    let (s, c) = select(s)?;
    let (s, d) = symbol("=")(s)?;
    let (s, e) = class_new(s)?;
    Ok((
        s,
        BlockingAssignment::HierarchicalVariable(BlockingAssignmentHierarchicalVariable {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[parser(MaybeRecursive)]
pub fn operator_assignment(s: Span) -> IResult<Span, OperatorAssignment> {
    let (s, a) = variable_lvalue(s)?;
    let (s, b) = assignment_operator(s)?;
    let (s, c) = expression(s)?;
    Ok((s, OperatorAssignment { nodes: (a, b, c) }))
}

#[parser]
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

#[parser(MaybeRecursive)]
pub fn nonblocking_assignment(s: Span) -> IResult<Span, NonblockingAssignment> {
    let (s, a) = variable_lvalue(s)?;
    let (s, b) = symbol("<=")(s)?;
    let (s, c) = opt(delay_or_event_control)(s)?;
    let (s, d) = expression(s)?;
    Ok((
        s,
        NonblockingAssignment {
            nodes: (a, b, c, d),
        },
    ))
}

#[parser]
pub fn procedural_continuous_assignment(s: Span) -> IResult<Span, ProceduralContinuousAssignment> {
    alt((
        procedural_continuous_assignment_assign,
        procedural_continuous_assignment_deassign,
        procedural_continuous_assignment_force_variable,
        procedural_continuous_assignment_force_net,
        procedural_continuous_assignment_release_variable,
        procedural_continuous_assignment_release_net,
    ))(s)
}

#[parser]
pub fn procedural_continuous_assignment_assign(
    s: Span,
) -> IResult<Span, ProceduralContinuousAssignment> {
    let (s, a) = keyword("assign")(s)?;
    let (s, b) = variable_assignment(s)?;
    Ok((
        s,
        ProceduralContinuousAssignment::Assign(ProceduralContinuousAssignmentAssign {
            nodes: (a, b),
        }),
    ))
}

#[parser]
pub fn procedural_continuous_assignment_deassign(
    s: Span,
) -> IResult<Span, ProceduralContinuousAssignment> {
    let (s, a) = keyword("deassign")(s)?;
    let (s, b) = variable_lvalue(s)?;
    Ok((
        s,
        ProceduralContinuousAssignment::Deassign(ProceduralContinuousAssignmentDeassign {
            nodes: (a, b),
        }),
    ))
}

#[parser]
pub fn procedural_continuous_assignment_force_variable(
    s: Span,
) -> IResult<Span, ProceduralContinuousAssignment> {
    let (s, a) = keyword("force")(s)?;
    let (s, b) = variable_assignment(s)?;
    Ok((
        s,
        ProceduralContinuousAssignment::ForceVariable(
            ProceduralContinuousAssignmentForceVariable { nodes: (a, b) },
        ),
    ))
}

#[parser]
pub fn procedural_continuous_assignment_force_net(
    s: Span,
) -> IResult<Span, ProceduralContinuousAssignment> {
    let (s, a) = keyword("force")(s)?;
    let (s, b) = net_assignment(s)?;
    Ok((
        s,
        ProceduralContinuousAssignment::ForceNet(ProceduralContinuousAssignmentForceNet {
            nodes: (a, b),
        }),
    ))
}

#[parser]
pub fn procedural_continuous_assignment_release_variable(
    s: Span,
) -> IResult<Span, ProceduralContinuousAssignment> {
    let (s, a) = keyword("release")(s)?;
    let (s, b) = variable_lvalue(s)?;
    Ok((
        s,
        ProceduralContinuousAssignment::ReleaseVariable(
            ProceduralContinuousAssignmentReleaseVariable { nodes: (a, b) },
        ),
    ))
}

#[parser]
pub fn procedural_continuous_assignment_release_net(
    s: Span,
) -> IResult<Span, ProceduralContinuousAssignment> {
    let (s, a) = keyword("release")(s)?;
    let (s, b) = net_lvalue(s)?;
    Ok((
        s,
        ProceduralContinuousAssignment::ReleaseNet(ProceduralContinuousAssignmentReleaseNet {
            nodes: (a, b),
        }),
    ))
}

#[parser(MaybeRecursive)]
pub fn variable_assignment(s: Span) -> IResult<Span, VariableAssignment> {
    let (s, a) = variable_lvalue(s)?;
    let (s, b) = symbol("=")(s)?;
    let (s, c) = expression(s)?;
    Ok((s, VariableAssignment { nodes: (a, b, c) }))
}

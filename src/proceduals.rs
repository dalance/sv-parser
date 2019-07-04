use crate::continuous_assignments::*;
use crate::expressions::*;
use crate::identifiers::*;
use crate::lvalues::*;
use crate::operators::*;
use crate::primaries::*;
use crate::utils::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct InitialConstruct<'a> {
    pub statement: StatementOrNull<'a>,
}

#[derive(Debug)]
pub struct AlwaysConstruct<'a> {
    pub keyword: AlwaysKeyword,
    pub statement: Statement<'a>,
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
    pub statement: FunctionStatement<'a>,
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
    pub lvalue: VariableLvalue<'a>,
    pub control: DelayOrEventControl<'a>,
    pub rvalue: Expression<'a>,
}

#[derive(Debug)]
pub struct BlockingAssignmentNonrangeVariable<'a> {
    pub lvalue: NonrangeVariableLvalue<'a>,
    pub rvalue: DynamicArrayNew<'a>,
}

#[derive(Debug)]
pub struct BlockingAssignmentHierarchicalVariable<'a> {
    pub scope: Option<Scope<'a>>,
    pub lvalue: HierarchicalIdentifier<'a>,
    pub select: Select<'a>,
    pub rvalue: ClassNew<'a>,
}

#[derive(Debug)]
pub struct OperatorAssignment<'a> {
    pub lvalue: VariableLvalue<'a>,
    pub operator: Operator<'a>,
    pub rvalue: Expression<'a>,
}

#[derive(Debug)]
pub struct NonblockingAssignment<'a> {
    pub lvalue: VariableLvalue<'a>,
    pub control: Option<DelayOrEventControl<'a>>,
    pub rvalue: Expression<'a>,
}

#[derive(Debug)]
pub enum ProcedualContinuousAssignment<'a> {
    Assign(VariableAssignment<'a>),
    Deassign(VariableLvalue<'a>),
    ForceVariable(VariableAssignment<'a>),
    ForceNet(NetAssignment<'a>),
    ReleaseVariable(VariableLvalue<'a>),
    ReleaseNet(NetLvalue<'a>),
}

#[derive(Debug)]
pub struct VariableAssignment<'a> {
    pub lvalue: VariableLvalue<'a>,
    pub rvalue: Expression<'a>,
}

// -----------------------------------------------------------------------------

pub fn initial_construct(s: &str) -> IResult<&str, InitialConstruct> {
    let (s, _) = symbol("initial")(s)?;
    let (s, statement) = statement_or_null(s)?;
    Ok((s, InitialConstruct { statement }))
}

pub fn always_construct(s: &str) -> IResult<&str, AlwaysConstruct> {
    let (s, keyword) = always_keyword(s)?;
    let (s, statement) = statement(s)?;
    Ok((s, AlwaysConstruct { keyword, statement }))
}

pub fn always_keyword(s: &str) -> IResult<&str, AlwaysKeyword> {
    alt((
        map(symbol("always_comb"), |_| AlwaysKeyword::AlwaysComb),
        map(symbol("always_latch"), |_| AlwaysKeyword::AlwaysLatch),
        map(symbol("always_ff"), |_| AlwaysKeyword::AlwaysFf),
        map(symbol("always"), |_| AlwaysKeyword::Always),
    ))(s)
}

pub fn final_construct(s: &str) -> IResult<&str, FinalConstruct> {
    let (s, _) = symbol("final")(s)?;
    let (s, statement) = function_statement(s)?;
    Ok((s, FinalConstruct { statement }))
}

pub fn blocking_assignment(s: &str) -> IResult<&str, BlockingAssignment> {
    alt((
        blocking_assignment_variable,
        blocking_assignment_nonrange_variable,
        blocking_assignment_hierarchical_variable,
        map(operator_assignment, |x| BlockingAssignment::Operator(x)),
    ))(s)
}

pub fn blocking_assignment_variable(s: &str) -> IResult<&str, BlockingAssignment> {
    let (s, lvalue) = variable_lvalue(s)?;
    let (s, _) = symbol("=")(s)?;
    let (s, control) = delay_or_event_control(s)?;
    let (s, rvalue) = expression(s)?;
    Ok((
        s,
        BlockingAssignment::Variable(BlockingAssignmentVariable {
            lvalue,
            control,
            rvalue,
        }),
    ))
}

pub fn blocking_assignment_nonrange_variable(s: &str) -> IResult<&str, BlockingAssignment> {
    let (s, lvalue) = nonrange_variable_lvalue(s)?;
    let (s, _) = symbol("=")(s)?;
    let (s, rvalue) = dynamic_array_new(s)?;
    Ok((
        s,
        BlockingAssignment::NonrangeVariable(BlockingAssignmentNonrangeVariable { lvalue, rvalue }),
    ))
}

pub fn blocking_assignment_hierarchical_variable(s: &str) -> IResult<&str, BlockingAssignment> {
    let (s, scope) = opt(alt((
        terminated(implicit_class_handle, symbol(".")),
        class_scope,
        package_scope,
    )))(s)?;
    let (s, lvalue) = hierarchical_variable_identifier(s)?;
    let (s, select) = select(s)?;
    let (s, _) = symbol("=")(s)?;
    let (s, rvalue) = class_new(s)?;
    Ok((
        s,
        BlockingAssignment::HierarchicalVariable(BlockingAssignmentHierarchicalVariable {
            scope,
            lvalue,
            select,
            rvalue,
        }),
    ))
}

pub fn operator_assignment(s: &str) -> IResult<&str, OperatorAssignment> {
    let (s, lvalue) = variable_lvalue(s)?;
    let (s, operator) = assignment_operator(s)?;
    let (s, rvalue) = expression(s)?;
    Ok((
        s,
        OperatorAssignment {
            lvalue,
            operator,
            rvalue,
        },
    ))
}

pub fn assignment_operator(s: &str) -> IResult<&str, Operator> {
    alt((
        map(symbol("="), |raw| Operator { raw }),
        map(symbol("+="), |raw| Operator { raw }),
        map(symbol("-="), |raw| Operator { raw }),
        map(symbol("*="), |raw| Operator { raw }),
        map(symbol("/="), |raw| Operator { raw }),
        map(symbol("%="), |raw| Operator { raw }),
        map(symbol("&="), |raw| Operator { raw }),
        map(symbol("|="), |raw| Operator { raw }),
        map(symbol("^="), |raw| Operator { raw }),
        map(symbol("<<<="), |raw| Operator { raw }),
        map(symbol(">>>="), |raw| Operator { raw }),
        map(symbol("<<="), |raw| Operator { raw }),
        map(symbol(">>="), |raw| Operator { raw }),
    ))(s)
}

pub fn nonblocking_assignment(s: &str) -> IResult<&str, NonblockingAssignment> {
    let (s, lvalue) = variable_lvalue(s)?;
    let (s, _) = symbol("<=")(s)?;
    let (s, control) = opt(delay_or_event_control)(s)?;
    let (s, rvalue) = expression(s)?;
    Ok((
        s,
        NonblockingAssignment {
            lvalue,
            control,
            rvalue,
        },
    ))
}

pub fn procedual_continuous_assignment(s: &str) -> IResult<&str, ProcedualContinuousAssignment> {
    alt((
        map(preceded(symbol("assign"), variable_assignment), |x| {
            ProcedualContinuousAssignment::Assign(x)
        }),
        map(preceded(symbol("deassign"), variable_lvalue), |x| {
            ProcedualContinuousAssignment::Deassign(x)
        }),
        map(preceded(symbol("force"), variable_assignment), |x| {
            ProcedualContinuousAssignment::ForceVariable(x)
        }),
        map(preceded(symbol("force"), net_assignment), |x| {
            ProcedualContinuousAssignment::ForceNet(x)
        }),
        map(preceded(symbol("release"), variable_lvalue), |x| {
            ProcedualContinuousAssignment::ReleaseVariable(x)
        }),
        map(preceded(symbol("release"), net_lvalue), |x| {
            ProcedualContinuousAssignment::ReleaseNet(x)
        }),
    ))(s)
}

pub fn variable_assignment(s: &str) -> IResult<&str, VariableAssignment> {
    let (s, lvalue) = variable_lvalue(s)?;
    let (s, _) = symbol("=")(s)?;
    let (s, rvalue) = expression(s)?;
    Ok((s, VariableAssignment { lvalue, rvalue }))
}

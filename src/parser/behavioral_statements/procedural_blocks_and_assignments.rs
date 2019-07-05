use crate::parser::*;
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
    pub statement: Statement<'a>,
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
    pub lvalue: VariableLvalue<'a>,
    pub rvalue: Expression<'a>,
}

// -----------------------------------------------------------------------------

pub fn initial_construct(s: &str) -> IResult<&str, InitialConstruct> {
    let (s, _) = symbol("initial")(s)?;
    let (s, x) = statement_or_null(s)?;
    Ok((s, InitialConstruct { statement: x }))
}

pub fn always_construct(s: &str) -> IResult<&str, AlwaysConstruct> {
    let (s, x) = always_keyword(s)?;
    let (s, y) = statement(s)?;
    Ok((
        s,
        AlwaysConstruct {
            keyword: x,
            statement: y,
        },
    ))
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
    let (s, x) = function_statement(s)?;
    Ok((s, FinalConstruct { statement: x }))
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
    let (s, x) = variable_lvalue(s)?;
    let (s, _) = symbol("=")(s)?;
    let (s, y) = delay_or_event_control(s)?;
    let (s, z) = expression(s)?;
    Ok((
        s,
        BlockingAssignment::Variable(BlockingAssignmentVariable {
            lvalue: x,
            control: y,
            rvalue: z,
        }),
    ))
}

pub fn blocking_assignment_nonrange_variable(s: &str) -> IResult<&str, BlockingAssignment> {
    let (s, x) = nonrange_variable_lvalue(s)?;
    let (s, _) = symbol("=")(s)?;
    let (s, y) = dynamic_array_new(s)?;
    Ok((
        s,
        BlockingAssignment::NonrangeVariable(BlockingAssignmentNonrangeVariable {
            lvalue: x,
            rvalue: y,
        }),
    ))
}

pub fn blocking_assignment_hierarchical_variable(s: &str) -> IResult<&str, BlockingAssignment> {
    let (s, x) = opt(alt((
        terminated(implicit_class_handle, symbol(".")),
        class_scope,
        package_scope,
    )))(s)?;
    let (s, y) = hierarchical_variable_identifier(s)?;
    let (s, z) = select(s)?;
    let (s, _) = symbol("=")(s)?;
    let (s, v) = class_new(s)?;
    Ok((
        s,
        BlockingAssignment::HierarchicalVariable(BlockingAssignmentHierarchicalVariable {
            scope: x,
            lvalue: y,
            select: z,
            rvalue: v,
        }),
    ))
}

pub fn operator_assignment(s: &str) -> IResult<&str, OperatorAssignment> {
    let (s, x) = variable_lvalue(s)?;
    let (s, y) = assignment_operator(s)?;
    let (s, z) = expression(s)?;
    Ok((
        s,
        OperatorAssignment {
            lvalue: x,
            operator: y,
            rvalue: z,
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
    let (s, x) = variable_lvalue(s)?;
    let (s, _) = symbol("<=")(s)?;
    let (s, y) = opt(delay_or_event_control)(s)?;
    let (s, z) = expression(s)?;
    Ok((
        s,
        NonblockingAssignment {
            lvalue: x,
            control: y,
            rvalue: z,
        },
    ))
}

pub fn procedural_continuous_assignment(s: &str) -> IResult<&str, ProceduralContinuousAssignment> {
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

pub fn variable_assignment(s: &str) -> IResult<&str, VariableAssignment> {
    let (s, x) = variable_lvalue(s)?;
    let (s, _) = symbol("=")(s)?;
    let (s, y) = expression(s)?;
    Ok((
        s,
        VariableAssignment {
            lvalue: x,
            rvalue: y,
        },
    ))
}

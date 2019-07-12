use crate::ast::*;
use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct DefparamAssignment<'a> {
    pub nodes: (
        HierarchicalParameterIdentifier<'a>,
        Symbol<'a>,
        ConstantMintypmaxExpression<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct NetDeclAssignment<'a> {
    pub nodes: (
        NetIdentifier<'a>,
        Vec<UnpackedDimension<'a>>,
        Option<(Symbol<'a>, Expression<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct ParamAssignment<'a> {
    pub nodes: (
        ParameterIdentifier<'a>,
        Vec<UnpackedDimension<'a>>,
        Option<(Symbol<'a>, ConstantParamExpression<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub enum SpecparamAssignment<'a> {
    Mintypmax(SpecparamAssignmentMintypmax<'a>),
    PulseControl(PulseControlSpecparam<'a>),
}

#[derive(Debug, Node)]
pub struct SpecparamAssignmentMintypmax<'a> {
    pub nodes: (
        SpecparamIdentifier<'a>,
        Symbol<'a>,
        ConstantMintypmaxExpression<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct TypeAssignment<'a> {
    pub nodes: (TypeIdentifier<'a>, Option<(Symbol<'a>, DataType<'a>)>),
}

#[derive(Debug, Node)]
pub enum PulseControlSpecparam<'a> {
    WithoutDescriptor(PulseControlSpecparamWithoutDescriptor<'a>),
    WithDescriptor(PulseControlSpecparamWithDescriptor<'a>),
}

#[derive(Debug, Node)]
pub struct PulseControlSpecparamWithoutDescriptor<'a> {
    pub nodes: (
        Symbol<'a>,
        Symbol<'a>,
        Paren<
            'a,
            (
                RejectLimitValue<'a>,
                Option<(Symbol<'a>, ErrorLimitValue<'a>)>,
            ),
        >,
    ),
}

#[derive(Debug, Node)]
pub struct PulseControlSpecparamWithDescriptor<'a> {
    pub nodes: (
        Symbol<'a>,
        SpecifyInputTerminalDescriptor<'a>,
        Symbol<'a>,
        SpecifyOutputTerminalDescriptor<'a>,
        Symbol<'a>,
        Paren<
            'a,
            (
                RejectLimitValue<'a>,
                Option<(Symbol<'a>, ErrorLimitValue<'a>)>,
            ),
        >,
    ),
}

#[derive(Debug, Node)]
pub struct ErrorLimitValue<'a> {
    pub nodes: (LimitValue<'a>,),
}

#[derive(Debug, Node)]
pub struct RejectLimitValue<'a> {
    pub nodes: (LimitValue<'a>,),
}

#[derive(Debug, Node)]
pub struct LimitValue<'a> {
    pub nodes: (ConstantMintypmaxExpression<'a>,),
}

#[derive(Debug, Node)]
pub enum VariableDeclAssignment<'a> {
    Variable(VariableDeclAssignmentVariable<'a>),
    DynamicArray(VariableDeclAssignmentDynamicArray<'a>),
    Class(VariableDeclAssignmentClass<'a>),
}

#[derive(Debug, Node)]
pub struct VariableDeclAssignmentVariable<'a> {
    pub nodes: (
        VariableIdentifier<'a>,
        Vec<VariableDimension<'a>>,
        Option<(Symbol<'a>, Expression<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct VariableDeclAssignmentDynamicArray<'a> {
    pub nodes: (
        DynamicArrayVariableIdentifier<'a>,
        UnsizedDimension<'a>,
        Vec<VariableDimension<'a>>,
        Option<(Symbol<'a>, DynamicArrayNew<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct VariableDeclAssignmentClass<'a> {
    pub nodes: (
        ClassVariableIdentifier<'a>,
        Option<(Symbol<'a>, ClassNew<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub enum ClassNew<'a> {
    Argument(ClassNewArgument<'a>),
    Expression(ClassNewExpression<'a>),
}

#[derive(Debug, Node)]
pub struct ClassNewArgument<'a> {
    pub nodes: (
        Option<ClassScope<'a>>,
        Symbol<'a>,
        Option<Paren<'a, ListOfArguments<'a>>>,
    ),
}

#[derive(Debug, Node)]
pub struct ClassNewExpression<'a> {
    pub nodes: (Symbol<'a>, Expression<'a>),
}

#[derive(Debug, Node)]
pub struct DynamicArrayNew<'a> {
    pub nodes: (
        Symbol<'a>,
        Bracket<'a, Expression<'a>>,
        Option<Bracket<'a, Expression<'a>>>,
    ),
}

// -----------------------------------------------------------------------------

pub fn defparam_assignment(s: Span) -> IResult<Span, DefparamAssignment> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn net_decl_assignment(s: Span) -> IResult<Span, NetDeclAssignment> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn param_assignment(s: Span) -> IResult<Span, ParamAssignment> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn specparam_assignment(s: Span) -> IResult<Span, SpecparamAssignment> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn type_assignment(s: Span) -> IResult<Span, TypeAssignment> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn pulse_control_specparam(s: Span) -> IResult<Span, PulseControlSpecparam> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn error_limit_value(s: Span) -> IResult<Span, ErrorLimitValue> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn reject_limit_value(s: Span) -> IResult<Span, RejectLimitValue> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn limit_value(s: Span) -> IResult<Span, LimitValue> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn variable_decl_assignment(s: Span) -> IResult<Span, VariableDeclAssignment> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn class_new(s: Span) -> IResult<Span, ClassNew> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn dynamic_array_new(s: Span) -> IResult<Span, DynamicArrayNew> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

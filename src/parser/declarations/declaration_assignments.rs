use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct DefparamAssignment {
    pub nodes: (
        HierarchicalParameterIdentifier,
        Symbol,
        ConstantMintypmaxExpression,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct NetDeclAssignment {
    pub nodes: (
        NetIdentifier,
        Vec<UnpackedDimension>,
        Option<(Symbol, Expression)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ParamAssignment {
    pub nodes: (
        ParameterIdentifier,
        Vec<UnpackedDimension>,
        Option<(Symbol, ConstantParamExpression)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum SpecparamAssignment {
    Mintypmax(SpecparamAssignmentMintypmax),
    PulseControlSpecparam(PulseControlSpecparam),
}

#[derive(Clone, Debug, Node)]
pub struct SpecparamAssignmentMintypmax {
    pub nodes: (SpecparamIdentifier, Symbol, ConstantMintypmaxExpression),
}

#[derive(Clone, Debug, Node)]
pub struct TypeAssignment {
    pub nodes: (TypeIdentifier, Option<(Symbol, DataType)>),
}

#[derive(Clone, Debug, Node)]
pub enum PulseControlSpecparam {
    WithoutDescriptor(PulseControlSpecparamWithoutDescriptor),
    WithDescriptor(PulseControlSpecparamWithDescriptor),
}

#[derive(Clone, Debug, Node)]
pub struct PulseControlSpecparamWithoutDescriptor {
    pub nodes: (
        Symbol,
        Symbol,
        Paren<(RejectLimitValue, Option<(Symbol, ErrorLimitValue)>)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct PulseControlSpecparamWithDescriptor {
    pub nodes: (
        Symbol,
        SpecifyInputTerminalDescriptor,
        Symbol,
        SpecifyOutputTerminalDescriptor,
        Symbol,
        Paren<(RejectLimitValue, Option<(Symbol, ErrorLimitValue)>)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ErrorLimitValue {
    pub nodes: (LimitValue,),
}

#[derive(Clone, Debug, Node)]
pub struct RejectLimitValue {
    pub nodes: (LimitValue,),
}

#[derive(Clone, Debug, Node)]
pub struct LimitValue {
    pub nodes: (ConstantMintypmaxExpression,),
}

#[derive(Clone, Debug, Node)]
pub enum VariableDeclAssignment {
    Variable(VariableDeclAssignmentVariable),
    DynamicArray(VariableDeclAssignmentDynamicArray),
    Class(VariableDeclAssignmentClass),
}

#[derive(Clone, Debug, Node)]
pub struct VariableDeclAssignmentVariable {
    pub nodes: (
        VariableIdentifier,
        Vec<VariableDimension>,
        Option<(Symbol, Expression)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct VariableDeclAssignmentDynamicArray {
    pub nodes: (
        DynamicArrayVariableIdentifier,
        UnsizedDimension,
        Vec<VariableDimension>,
        Option<(Symbol, DynamicArrayNew)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct VariableDeclAssignmentClass {
    pub nodes: (ClassVariableIdentifier, Option<(Symbol, ClassNew)>),
}

#[derive(Clone, Debug, Node)]
pub enum ClassNew {
    Argument(ClassNewArgument),
    Expression(ClassNewExpression),
}

#[derive(Clone, Debug, Node)]
pub struct ClassNewArgument {
    pub nodes: (Option<ClassScope>, Keyword, Option<Paren<ListOfArguments>>),
}

#[derive(Clone, Debug, Node)]
pub struct ClassNewExpression {
    pub nodes: (Keyword, Expression),
}

#[derive(Clone, Debug, Node)]
pub struct DynamicArrayNew {
    pub nodes: (Keyword, Bracket<Expression>, Option<Paren<Expression>>),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn defparam_assignment(s: Span) -> IResult<Span, DefparamAssignment> {
    let (s, a) = hierarchical_parameter_identifier(s)?;
    let (s, b) = symbol("=")(s)?;
    let (s, c) = constant_mintypmax_expression(s)?;
    Ok((s, DefparamAssignment { nodes: (a, b, c) }))
}

#[parser]
pub fn net_decl_assignment(s: Span) -> IResult<Span, NetDeclAssignment> {
    let (s, a) = net_identifier(s)?;
    let (s, b) = many0(unpacked_dimension)(s)?;
    let (s, c) = opt(pair(symbol("="), expression))(s)?;
    Ok((s, NetDeclAssignment { nodes: (a, b, c) }))
}

#[parser]
pub fn param_assignment(s: Span) -> IResult<Span, ParamAssignment> {
    let (s, a) = parameter_identifier(s)?;
    let (s, b) = many0(unpacked_dimension)(s)?;
    let (s, c) = opt(pair(symbol("="), constant_param_expression))(s)?;
    Ok((s, ParamAssignment { nodes: (a, b, c) }))
}

#[parser]
pub fn specparam_assignment(s: Span) -> IResult<Span, SpecparamAssignment> {
    alt((
        specparam_assignment_mintypmax,
        map(pulse_control_specparam, |x| {
            SpecparamAssignment::PulseControlSpecparam(x)
        }),
    ))(s)
}

#[parser]
pub fn specparam_assignment_mintypmax(s: Span) -> IResult<Span, SpecparamAssignment> {
    let (s, a) = specparam_identifier(s)?;
    let (s, b) = symbol("=")(s)?;
    let (s, c) = constant_mintypmax_expression(s)?;
    Ok((
        s,
        SpecparamAssignment::Mintypmax(SpecparamAssignmentMintypmax { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn type_assignment(s: Span) -> IResult<Span, TypeAssignment> {
    let (s, a) = type_identifier(s)?;
    let (s, b) = opt(pair(symbol("="), data_type))(s)?;
    Ok((s, TypeAssignment { nodes: (a, b) }))
}

#[parser]
pub fn pulse_control_specparam(s: Span) -> IResult<Span, PulseControlSpecparam> {
    alt((
        pulse_control_specparam_without_descriptor,
        pulse_control_specparam_with_descriptor,
    ))(s)
}

#[parser]
pub fn pulse_control_specparam_without_descriptor(s: Span) -> IResult<Span, PulseControlSpecparam> {
    let (s, a) = symbol("PATHPULSE$")(s)?;
    let (s, b) = symbol("=")(s)?;
    let (s, c) = paren(pair(
        reject_limit_value,
        opt(pair(symbol(","), error_limit_value)),
    ))(s)?;
    Ok((
        s,
        PulseControlSpecparam::WithoutDescriptor(PulseControlSpecparamWithoutDescriptor {
            nodes: (a, b, c),
        }),
    ))
}

#[parser]
pub fn pulse_control_specparam_with_descriptor(s: Span) -> IResult<Span, PulseControlSpecparam> {
    let (s, a) = symbol("PATHPULSE$")(s)?;
    let (s, b) = specify_input_terminal_descriptor(s)?;
    let (s, c) = symbol("$")(s)?;
    let (s, d) = specify_output_terminal_descriptor(s)?;
    let (s, e) = symbol("=")(s)?;
    let (s, f) = paren(pair(
        reject_limit_value,
        opt(pair(symbol(","), error_limit_value)),
    ))(s)?;
    Ok((
        s,
        PulseControlSpecparam::WithDescriptor(PulseControlSpecparamWithDescriptor {
            nodes: (a, b, c, d, e, f),
        }),
    ))
}

#[parser]
pub fn error_limit_value(s: Span) -> IResult<Span, ErrorLimitValue> {
    let (s, a) = limit_value(s)?;
    Ok((s, ErrorLimitValue { nodes: (a,) }))
}

#[parser]
pub fn reject_limit_value(s: Span) -> IResult<Span, RejectLimitValue> {
    let (s, a) = limit_value(s)?;
    Ok((s, RejectLimitValue { nodes: (a,) }))
}

#[parser]
pub fn limit_value(s: Span) -> IResult<Span, LimitValue> {
    let (s, a) = constant_mintypmax_expression(s)?;
    Ok((s, LimitValue { nodes: (a,) }))
}

#[parser]
pub fn variable_decl_assignment(s: Span) -> IResult<Span, VariableDeclAssignment> {
    alt((
        variable_decl_assignment_variable,
        variable_decl_assignment_dynamic_array,
        variable_decl_assignment_class,
    ))(s)
}

#[parser]
pub fn variable_decl_assignment_variable(s: Span) -> IResult<Span, VariableDeclAssignment> {
    let (s, a) = variable_identifier(s)?;
    let (s, b) = many0(variable_dimension)(s)?;
    let (s, c) = opt(pair(symbol("="), expression))(s)?;
    Ok((
        s,
        VariableDeclAssignment::Variable(VariableDeclAssignmentVariable { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn variable_decl_assignment_dynamic_array(s: Span) -> IResult<Span, VariableDeclAssignment> {
    let (s, a) = dynamic_array_variable_identifier(s)?;
    let (s, b) = unsized_dimension(s)?;
    let (s, c) = many0(variable_dimension)(s)?;
    let (s, d) = opt(pair(symbol("="), dynamic_array_new))(s)?;
    Ok((
        s,
        VariableDeclAssignment::DynamicArray(VariableDeclAssignmentDynamicArray {
            nodes: (a, b, c, d),
        }),
    ))
}

#[parser]
pub fn variable_decl_assignment_class(s: Span) -> IResult<Span, VariableDeclAssignment> {
    let (s, a) = class_variable_identifier(s)?;
    let (s, b) = opt(pair(symbol("="), class_new))(s)?;
    Ok((
        s,
        VariableDeclAssignment::Class(VariableDeclAssignmentClass { nodes: (a, b) }),
    ))
}

#[parser]
pub fn class_new(s: Span) -> IResult<Span, ClassNew> {
    alt((class_new_argument, class_new_expression))(s)
}

#[parser]
pub fn class_new_argument(s: Span) -> IResult<Span, ClassNew> {
    let (s, a) = opt(class_scope)(s)?;
    let (s, b) = keyword("new")(s)?;
    let (s, c) = opt(paren(list_of_arguments))(s)?;
    Ok((s, ClassNew::Argument(ClassNewArgument { nodes: (a, b, c) })))
}

#[parser]
pub fn class_new_expression(s: Span) -> IResult<Span, ClassNew> {
    let (s, a) = keyword("new")(s)?;
    let (s, b) = expression(s)?;
    Ok((
        s,
        ClassNew::Expression(ClassNewExpression { nodes: (a, b) }),
    ))
}

#[parser]
pub fn dynamic_array_new(s: Span) -> IResult<Span, DynamicArrayNew> {
    let (s, a) = keyword("new")(s)?;
    let (s, b) = bracket(expression)(s)?;
    let (s, c) = opt(paren(expression))(s)?;
    Ok((s, DynamicArrayNew { nodes: (a, b, c) }))
}

use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

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
    PulseControlSpecparam(PulseControlSpecparam<'a>),
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
        Option<Paren<'a, Expression<'a>>>,
    ),
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
    let (s, b) = symbol("new")(s)?;
    let (s, c) = opt(paren(list_of_arguments))(s)?;
    Ok((s, ClassNew::Argument(ClassNewArgument { nodes: (a, b, c) })))
}

#[parser]
pub fn class_new_expression(s: Span) -> IResult<Span, ClassNew> {
    let (s, a) = symbol("new")(s)?;
    let (s, b) = expression(s)?;
    Ok((
        s,
        ClassNew::Expression(ClassNewExpression { nodes: (a, b) }),
    ))
}

#[parser]
pub fn dynamic_array_new(s: Span) -> IResult<Span, DynamicArrayNew> {
    let (s, a) = symbol("new")(s)?;
    let (s, b) = bracket(expression)(s)?;
    let (s, c) = opt(paren(expression))(s)?;
    Ok((s, DynamicArrayNew { nodes: (a, b, c) }))
}

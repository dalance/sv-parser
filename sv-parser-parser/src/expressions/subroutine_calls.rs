use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
#[packrat_parser]
pub(crate) fn constant_function_call(s: Span) -> IResult<Span, ConstantFunctionCall> {
    let (s, a) = function_subroutine_call(s)?;
    Ok((s, ConstantFunctionCall { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn tf_call(s: Span) -> IResult<Span, TfCall> {
    let (s, a) = ps_or_hierarchical_tf_identifier(s)?;
    let (s, b) = many0(attribute_instance)(s)?;
    let (s, c) = opt(paren(list_of_arguments))(s)?;
    Ok((s, TfCall { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn system_tf_call(s: Span) -> IResult<Span, SystemTfCall> {
    alt((
        system_tf_call_arg_expression,
        system_tf_call_arg_data_type,
        system_tf_call_arg_optional,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn system_tf_call_arg_optional(s: Span) -> IResult<Span, SystemTfCall> {
    let (s, a) = system_tf_identifier(s)?;
    let (s, b) = opt(paren(list_of_arguments))(s)?;
    Ok((
        s,
        SystemTfCall::ArgOptionl(Box::new(SystemTfCallArgOptional { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn system_tf_call_arg_data_type(s: Span) -> IResult<Span, SystemTfCall> {
    let (s, a) = system_tf_identifier(s)?;
    let (s, b) = paren(pair(data_type, opt(pair(symbol(","), expression))))(s)?;
    Ok((
        s,
        SystemTfCall::ArgDataType(Box::new(SystemTfCallArgDataType { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn system_tf_call_arg_expression(s: Span) -> IResult<Span, SystemTfCall> {
    let (s, a) = system_tf_identifier(s)?;
    let (s, b) = paren(pair(
        list(
            terminated(symbol(","), peek(not(clocking_event))),
            opt(expression),
        ),
        opt(pair(symbol(","), opt(clocking_event))),
    ))(s)?;
    Ok((
        s,
        SystemTfCall::ArgExpression(Box::new(SystemTfCallArgExpression { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn subroutine_call(s: Span) -> IResult<Span, SubroutineCall> {
    alt((
        subroutine_call_randomize,
        map(method_call, |x| SubroutineCall::MethodCall(Box::new(x))),
        map(tf_call, |x| SubroutineCall::TfCall(Box::new(x))),
        map(system_tf_call, |x| {
            SubroutineCall::SystemTfCall(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn subroutine_call_randomize(s: Span) -> IResult<Span, SubroutineCall> {
    let (s, a) = opt(pair(keyword("std"), symbol("::")))(s)?;
    let (s, b) = randomize_call(s)?;
    Ok((
        s,
        SubroutineCall::Randomize(Box::new(SubroutineCallRandomize { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn function_subroutine_call(s: Span) -> IResult<Span, FunctionSubroutineCall> {
    map(subroutine_call, |x| FunctionSubroutineCall { nodes: (x,) })(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn list_of_arguments(s: Span) -> IResult<Span, ListOfArguments> {
    alt((list_of_arguments_named, list_of_arguments_ordered))(s)
}

#[recursive_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn list_of_arguments_ordered(s: Span) -> IResult<Span, ListOfArguments> {
    let (s, a) = list(
        terminated(symbol(","), peek(not(symbol(".")))),
        opt(expression),
    )(s)?;
    let (s, b) = many0(tuple((
        symbol(","),
        symbol("."),
        identifier,
        paren(opt(expression)),
    )))(s)?;
    Ok((
        s,
        ListOfArguments::Ordered(Box::new(ListOfArgumentsOrdered { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn list_of_arguments_named(s: Span) -> IResult<Span, ListOfArguments> {
    let (s, a) = symbol(".")(s)?;
    let (s, b) = identifier(s)?;
    let (s, c) = paren(opt(expression))(s)?;
    let (s, d) = many0(tuple((
        symbol(","),
        symbol("."),
        identifier,
        paren(opt(expression)),
    )))(s)?;
    Ok((
        s,
        ListOfArguments::Named(Box::new(ListOfArgumentsNamed {
            nodes: (a, b, c, d),
        })),
    ))
}

#[recursive_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn method_call(s: Span) -> IResult<Span, MethodCall> {
    let (s, a) = method_call_root(s)?;
    let (s, b) = symbol(".")(s)?;
    let (s, c) = method_call_body(s)?;

    Ok((s, MethodCall { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn method_call_body(s: Span) -> IResult<Span, MethodCallBody> {
    alt((
        map(built_in_method_call, |x| {
            MethodCallBody::BuiltInMethodCall(Box::new(x))
        }),
        method_call_body_user,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn method_call_body_user(s: Span) -> IResult<Span, MethodCallBody> {
    let (s, a) = method_identifier(s)?;
    let (s, b) = many0(attribute_instance)(s)?;
    let (s, c) = opt(paren(list_of_arguments))(s)?;
    Ok((
        s,
        MethodCallBody::User(Box::new(MethodCallBodyUser { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn built_in_method_call(s: Span) -> IResult<Span, BuiltInMethodCall> {
    alt((
        map(array_manipulation_call, |x| {
            BuiltInMethodCall::ArrayManipulationCall(Box::new(x))
        }),
        map(randomize_call, |x| {
            BuiltInMethodCall::RandomizeCall(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn array_manipulation_call(s: Span) -> IResult<Span, ArrayManipulationCall> {
    let (s, a) = array_method_name(s)?;
    let (s, b) = many0(attribute_instance)(s)?;
    let (s, c) = opt(paren(list_of_arguments))(s)?;
    let (s, d) = opt(pair(keyword("with"), paren(expression)))(s)?;
    Ok((
        s,
        ArrayManipulationCall {
            nodes: (a, b, c, d),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn randomize_call(s: Span) -> IResult<Span, RandomizeCall> {
    let (s, a) = keyword("randomize")(s)?;
    let (s, b) = many0(attribute_instance)(s)?;
    let (s, c) = opt(paren(opt(variable_identifier_list_or_null)))(s)?;
    let (s, d) = opt(triple(
        keyword("with"),
        opt(paren(opt(identifier_list))),
        constraint_block,
    ))(s)?;
    Ok((
        s,
        RandomizeCall {
            nodes: (a, b, c, d),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn variable_identifier_list_or_null(
    s: Span,
) -> IResult<Span, VariableIdentifierListOrNull> {
    alt((
        map(variable_identifier_list, |x| {
            VariableIdentifierListOrNull::VariableIdentifierList(Box::new(x))
        }),
        map(keyword("null"), |x| {
            VariableIdentifierListOrNull::Null(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn method_call_root(s: Span) -> IResult<Span, MethodCallRoot> {
    alt((
        map(primary_method_call_root, |x| {
            MethodCallRoot::Primary(Box::new(x))
        }),
        map(implicit_class_handle, |x| {
            MethodCallRoot::ImplicitClassHandle(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn primary_method_call_root(s: Span) -> IResult<Span, Primary> {
    alt((
        map(keyword("this"), |x| Primary::This(Box::new(x))),
        map(keyword("$"), |x| Primary::Dollar(Box::new(x))),
        map(keyword("null"), |x| Primary::Null(Box::new(x))),
        map(assignment_pattern_expression, |x| {
            Primary::AssignmentPatternExpression(Box::new(x))
        }),
        map(primary_literal, |x| Primary::PrimaryLiteral(Box::new(x))),
        map(cast, |x| Primary::Cast(Box::new(x))),
        terminated(primary_hierarchical_method_call_root, peek(none_of("("))),
        map(empty_unpacked_array_concatenation, |x| {
            Primary::EmptyUnpackedArrayConcatenation(Box::new(x))
        }),
        primary_concatenation,
        primary_multiple_concatenation,
        map(function_subroutine_call, |x| {
            Primary::FunctionSubroutineCall(Box::new(x))
        }),
        map(let_expression, |x| Primary::LetExpression(Box::new(x))),
        primary_mintypmax_expression,
        map(streaming_concatenation, |x| {
            Primary::StreamingConcatenation(Box::new(x))
        }),
        map(sequence_method_call, |x| {
            Primary::SequenceMethodCall(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn primary_hierarchical_method_call_root(s: Span) -> IResult<Span, Primary> {
    let (s, a) = opt(class_qualifier_or_package_scope)(s)?;
    let (s, b) = hierarchical_identifier_method_call_root(s)?;
    let (s, c) = select_method_call_root(s)?;
    Ok((
        s,
        Primary::Hierarchical(Box::new(PrimaryHierarchical { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn hierarchical_identifier_method_call_root(
    s: Span,
) -> IResult<Span, HierarchicalIdentifier> {
    let (s, a) = opt(root)(s)?;
    let (s, b) = many0(terminated(
        triple(identifier, constant_bit_select, symbol(".")),
        peek(pair(identifier, symbol("."))),
    ))(s)?;
    let (s, c) = identifier(s)?;
    Ok((s, HierarchicalIdentifier { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn select_method_call_root(s: Span) -> IResult<Span, Select> {
    let (s, a) = opt(terminated(
        triple(
            many0(terminated(
                triple(symbol("."), member_identifier, bit_select),
                peek(triple(symbol("."), member_identifier, symbol("."))),
            )),
            symbol("."),
            member_identifier,
        ),
        peek(symbol(".")),
    ))(s)?;
    let (s, b) = bit_select(s)?;
    let (s, c) = opt(bracket(part_select_range))(s)?;
    Ok((s, Select { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn array_method_name(s: Span) -> IResult<Span, ArrayMethodName> {
    alt((
        map(keyword("unique"), |x| ArrayMethodName::Unique(Box::new(x))),
        map(keyword("and"), |x| ArrayMethodName::And(Box::new(x))),
        map(keyword("or"), |x| ArrayMethodName::Or(Box::new(x))),
        map(keyword("xor"), |x| ArrayMethodName::Xor(Box::new(x))),
        map(method_identifier, |x| {
            ArrayMethodName::MethodIdentifier(Box::new(x))
        }),
    ))(s)
}

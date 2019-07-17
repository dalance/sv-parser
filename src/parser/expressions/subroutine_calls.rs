use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct ConstantFunctionCall<'a> {
    pub nodes: (FunctionSubroutineCall<'a>,),
}

#[derive(Debug, Node)]
pub struct TfCall<'a> {
    pub nodes: (
        PsOrHierarchicalTfIdentifier<'a>,
        Vec<AttributeInstance<'a>>,
        Option<Paren<'a, ListOfArguments<'a>>>,
    ),
}

#[derive(Debug, Node)]
pub enum SystemTfCall<'a> {
    ArgOptionl(SystemTfCallArgOptional<'a>),
    ArgDataType(SystemTfCallArgDataType<'a>),
    ArgExpression(SystemTfCallArgExpression<'a>),
}

#[derive(Debug, Node)]
pub struct SystemTfCallArgOptional<'a> {
    pub nodes: (
        SystemTfIdentifier<'a>,
        Option<Paren<'a, ListOfArguments<'a>>>,
    ),
}

#[derive(Debug, Node)]
pub struct SystemTfCallArgDataType<'a> {
    pub nodes: (
        SystemTfIdentifier<'a>,
        Paren<'a, (DataType<'a>, Option<(Symbol<'a>, Expression<'a>)>)>,
    ),
}

#[derive(Debug, Node)]
pub struct SystemTfCallArgExpression<'a> {
    pub nodes: (
        SystemTfIdentifier<'a>,
        Paren<
            'a,
            (
                List<Symbol<'a>, Option<Expression<'a>>>,
                Option<(Symbol<'a>, Option<ClockingEvent<'a>>)>,
            ),
        >,
    ),
}

#[derive(Debug, Node)]
pub enum SubroutineCall<'a> {
    TfCall(Box<TfCall<'a>>),
    SystemTfCall(Box<SystemTfCall<'a>>),
    MethodCall(Box<MethodCall<'a>>),
    Randomize(Box<SubroutineCallRandomize<'a>>),
}

#[derive(Debug, Node)]
pub struct SubroutineCallRandomize<'a> {
    pub nodes: (Option<(Symbol<'a>, Symbol<'a>)>, RandomizeCall<'a>),
}

#[derive(Debug, Node)]
pub struct FunctionSubroutineCall<'a> {
    pub nodes: (SubroutineCall<'a>,),
}

#[derive(Debug, Node)]
pub enum ListOfArguments<'a> {
    Ordered(ListOfArgumentsOrdered<'a>),
    Named(ListOfArgumentsNamed<'a>),
}

#[derive(Debug, Node)]
pub struct ListOfArgumentsOrdered<'a> {
    pub nodes: (
        List<Symbol<'a>, Option<Expression<'a>>>,
        Vec<(
            Symbol<'a>,
            Symbol<'a>,
            Identifier<'a>,
            Paren<'a, Option<Expression<'a>>>,
        )>,
    ),
}

#[derive(Debug, Node)]
pub struct ListOfArgumentsNamed<'a> {
    pub nodes: (
        Symbol<'a>,
        Identifier<'a>,
        Paren<'a, Option<Expression<'a>>>,
        Vec<(
            Symbol<'a>,
            Symbol<'a>,
            Identifier<'a>,
            Paren<'a, Option<Expression<'a>>>,
        )>,
    ),
}

#[derive(Debug, Node)]
pub struct MethodCall<'a> {
    pub nodes: (MethodCallRoot<'a>, Symbol<'a>, MethodCallBody<'a>),
}

#[derive(Debug, Node)]
pub enum MethodCallBody<'a> {
    User(MethodCallBodyUser<'a>),
    BuiltInMethodCall(BuiltInMethodCall<'a>),
}

#[derive(Debug, Node)]
pub struct MethodCallBodyUser<'a> {
    pub nodes: (
        MethodIdentifier<'a>,
        Vec<AttributeInstance<'a>>,
        Option<Paren<'a, ListOfArguments<'a>>>,
    ),
}

#[derive(Debug, Node)]
pub enum BuiltInMethodCall<'a> {
    ArrayManipulationCall(ArrayManipulationCall<'a>),
    RandomizeCall(RandomizeCall<'a>),
}

#[derive(Debug, Node)]
pub struct ArrayManipulationCall<'a> {
    pub nodes: (
        ArrayMethodName<'a>,
        Vec<AttributeInstance<'a>>,
        Option<Paren<'a, ListOfArguments<'a>>>,
        Option<(Symbol<'a>, Paren<'a, Expression<'a>>)>,
    ),
}

#[derive(Debug, Node)]
pub struct RandomizeCall<'a> {
    pub nodes: (
        Symbol<'a>,
        Vec<AttributeInstance<'a>>,
        Option<Paren<'a, Option<VariableIdentifierListOrNull<'a>>>>,
        Option<(
            Symbol<'a>,
            Option<Paren<'a, Option<IdentifierList<'a>>>>,
            ConstraintBlock<'a>,
        )>,
    ),
}

#[derive(Debug, Node)]
pub enum VariableIdentifierListOrNull<'a> {
    VariableIdentifierList(VariableIdentifierList<'a>),
    Null(Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum MethodCallRoot<'a> {
    Primary(Primary<'a>),
    ImplicitClassHandle(ImplicitClassHandle<'a>),
}

#[derive(Debug, Node)]
pub enum ArrayMethodName<'a> {
    MethodIdentifier(MethodIdentifier<'a>),
    Unique(Symbol<'a>),
    And(Symbol<'a>),
    Or(Symbol<'a>),
    Xor(Symbol<'a>),
}

// -----------------------------------------------------------------------------

#[trace]
pub fn constant_function_call(s: Span) -> IResult<Span, ConstantFunctionCall> {
    let (s, a) = function_subroutine_call(s)?;
    Ok((s, ConstantFunctionCall { nodes: (a,) }))
}

#[trace]
pub fn tf_call(s: Span) -> IResult<Span, TfCall> {
    let (s, a) = ps_or_hierarchical_tf_identifier(s)?;
    let (s, b) = many0(attribute_instance)(s)?;
    let (s, c) = opt(paren(list_of_arguments))(s)?;
    Ok((s, TfCall { nodes: (a, b, c) }))
}

#[trace]
pub fn system_tf_call(s: Span) -> IResult<Span, SystemTfCall> {
    alt((
        system_tf_call_arg_optional,
        system_tf_call_arg_data_type,
        system_tf_call_arg_expression,
    ))(s)
}

#[trace]
pub fn system_tf_call_arg_optional(s: Span) -> IResult<Span, SystemTfCall> {
    let (s, a) = system_tf_identifier(s)?;
    let (s, b) = opt(paren(list_of_arguments))(s)?;
    Ok((
        s,
        SystemTfCall::ArgOptionl(SystemTfCallArgOptional { nodes: (a, b) }),
    ))
}

#[trace]
pub fn system_tf_call_arg_data_type(s: Span) -> IResult<Span, SystemTfCall> {
    let (s, a) = system_tf_identifier(s)?;
    let (s, b) = paren(pair(data_type, opt(pair(symbol(","), expression))))(s)?;
    Ok((
        s,
        SystemTfCall::ArgDataType(SystemTfCallArgDataType { nodes: (a, b) }),
    ))
}

#[trace]
pub fn system_tf_call_arg_expression(s: Span) -> IResult<Span, SystemTfCall> {
    let (s, a) = system_tf_identifier(s)?;
    let (s, b) = paren(pair(
        list(symbol(","), opt(expression)),
        opt(pair(symbol(","), opt(clocking_event))),
    ))(s)?;
    Ok((
        s,
        SystemTfCall::ArgExpression(SystemTfCallArgExpression { nodes: (a, b) }),
    ))
}

#[trace]
pub fn subroutine_call(s: Span) -> IResult<Span, SubroutineCall> {
    alt((
        map(tf_call, |x| SubroutineCall::TfCall(Box::new(x))),
        map(system_tf_call, |x| {
            SubroutineCall::SystemTfCall(Box::new(x))
        }),
        map(method_call, |x| SubroutineCall::MethodCall(Box::new(x))),
        subroutine_call_randomize,
    ))(s)
}

#[trace]
pub fn subroutine_call_randomize(s: Span) -> IResult<Span, SubroutineCall> {
    let (s, a) = opt(pair(symbol("std"), symbol("::")))(s)?;
    let (s, b) = randomize_call(s)?;
    Ok((
        s,
        SubroutineCall::Randomize(Box::new(SubroutineCallRandomize { nodes: (a, b) })),
    ))
}

#[trace]
pub fn function_subroutine_call(s: Span) -> IResult<Span, FunctionSubroutineCall> {
    map(subroutine_call, |x| FunctionSubroutineCall { nodes: (x,) })(s)
}

#[trace]
pub fn list_of_arguments(s: Span) -> IResult<Span, ListOfArguments> {
    alt((list_of_arguments_ordered, list_of_arguments_named))(s)
}

#[trace]
pub fn list_of_arguments_ordered(s: Span) -> IResult<Span, ListOfArguments> {
    let (s, a) = list(symbol(","), opt(expression))(s)?;
    let (s, b) = many0(tuple((
        symbol(","),
        symbol("."),
        identifier,
        paren(opt(expression)),
    )))(s)?;
    Ok((
        s,
        ListOfArguments::Ordered(ListOfArgumentsOrdered { nodes: (a, b) }),
    ))
}

#[trace]
pub fn list_of_arguments_named(s: Span) -> IResult<Span, ListOfArguments> {
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
        ListOfArguments::Named(ListOfArgumentsNamed {
            nodes: (a, b, c, d),
        }),
    ))
}

#[trace]
pub fn method_call(s: Span) -> IResult<Span, MethodCall> {
    let (s, a) = method_call_root(s)?;
    let (s, b) = symbol(".")(s)?;
    let (s, c) = method_call_body(s)?;

    Ok((s, MethodCall { nodes: (a, b, c) }))
}

#[trace]
pub fn method_call_body(s: Span) -> IResult<Span, MethodCallBody> {
    alt((
        method_call_body_user,
        map(built_in_method_call, |x| {
            MethodCallBody::BuiltInMethodCall(x)
        }),
    ))(s)
}

#[trace]
pub fn method_call_body_user(s: Span) -> IResult<Span, MethodCallBody> {
    let (s, a) = method_identifier(s)?;
    let (s, b) = many0(attribute_instance)(s)?;
    let (s, c) = opt(paren(list_of_arguments))(s)?;
    Ok((
        s,
        MethodCallBody::User(MethodCallBodyUser { nodes: (a, b, c) }),
    ))
}

#[trace]
pub fn built_in_method_call(s: Span) -> IResult<Span, BuiltInMethodCall> {
    alt((
        map(array_manipulation_call, |x| {
            BuiltInMethodCall::ArrayManipulationCall(x)
        }),
        map(randomize_call, |x| BuiltInMethodCall::RandomizeCall(x)),
    ))(s)
}

#[trace]
pub fn array_manipulation_call(s: Span) -> IResult<Span, ArrayManipulationCall> {
    let (s, a) = array_method_name(s)?;
    let (s, b) = many0(attribute_instance)(s)?;
    let (s, c) = opt(paren(list_of_arguments))(s)?;
    let (s, d) = opt(pair(symbol("with"), paren(expression)))(s)?;
    Ok((
        s,
        ArrayManipulationCall {
            nodes: (a, b, c, d),
        },
    ))
}

#[trace]
pub fn randomize_call(s: Span) -> IResult<Span, RandomizeCall> {
    let (s, a) = symbol("randomize")(s)?;
    let (s, b) = many0(attribute_instance)(s)?;
    let (s, c) = opt(paren(opt(variable_identifier_list_or_null)))(s)?;
    let (s, d) = opt(triple(
        symbol("with"),
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

#[trace]
pub fn variable_identifier_list_or_null(s: Span) -> IResult<Span, VariableIdentifierListOrNull> {
    alt((
        map(variable_identifier_list, |x| {
            VariableIdentifierListOrNull::VariableIdentifierList(x)
        }),
        map(symbol("null"), |x| VariableIdentifierListOrNull::Null(x)),
    ))(s)
}

#[trace]
pub fn method_call_root(s: Span) -> IResult<Span, MethodCallRoot> {
    alt((
        map(primary, |x| MethodCallRoot::Primary(x)),
        map(implicit_class_handle, |x| {
            MethodCallRoot::ImplicitClassHandle(x)
        }),
    ))(s)
}

#[trace]
pub fn array_method_name(s: Span) -> IResult<Span, ArrayMethodName> {
    alt((
        map(symbol("unique"), |x| ArrayMethodName::Unique(x)),
        map(symbol("and"), |x| ArrayMethodName::And(x)),
        map(symbol("or"), |x| ArrayMethodName::Or(x)),
        map(symbol("xor"), |x| ArrayMethodName::Xor(x)),
        map(method_identifier, |x| ArrayMethodName::MethodIdentifier(x)),
    ))(s)
}

// -----------------------------------------------------------------------------

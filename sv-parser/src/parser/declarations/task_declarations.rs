use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct TaskDeclaration {
    pub nodes: (Keyword, Option<Lifetime>, TaskBodyDeclaration),
}

#[derive(Clone, Debug, Node)]
pub enum TaskBodyDeclaration {
    WithoutPort(Box<TaskBodyDeclarationWithoutPort>),
    WithPort(Box<TaskBodyDeclarationWithPort>),
}

#[derive(Clone, Debug, Node)]
pub struct TaskBodyDeclarationWithoutPort {
    pub nodes: (
        Option<InterfaceIdentifierOrClassScope>,
        TaskIdentifier,
        Symbol,
        Vec<TfItemDeclaration>,
        Vec<StatementOrNull>,
        Keyword,
        Option<(Symbol, TaskIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct TaskBodyDeclarationWithPort {
    pub nodes: (
        Option<InterfaceIdentifierOrClassScope>,
        TaskIdentifier,
        Paren<Option<TfPortList>>,
        Symbol,
        Vec<BlockItemDeclaration>,
        Vec<StatementOrNull>,
        Keyword,
        Option<(Symbol, TaskIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum TfItemDeclaration {
    BlockItemDeclaration(Box<BlockItemDeclaration>),
    TfPortDeclaration(Box<TfPortDeclaration>),
}

#[derive(Clone, Debug, Node)]
pub struct TfPortList {
    pub nodes: (List<Symbol, TfPortItem>,),
}

#[derive(Clone, Debug, Node)]
pub struct TfPortItem {
    pub nodes: (
        Vec<AttributeInstance>,
        Option<TfPortDirection>,
        Option<Var>,
        Option<DataTypeOrImplicit>,
        Option<(
            PortIdentifier,
            Vec<VariableDimension>,
            Option<(Symbol, Expression)>,
        )>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum TfPortDirection {
    PortDirection(Box<PortDirection>),
    ConstRef(Box<(Keyword, Keyword)>),
}

#[derive(Clone, Debug, Node)]
pub struct TfPortDeclaration {
    pub nodes: (
        Vec<AttributeInstance>,
        TfPortDirection,
        Option<Var>,
        Option<DataTypeOrImplicit>,
        ListOfTfVariableIdentifiers,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct TaskPrototype {
    pub nodes: (Keyword, TaskIdentifier, Option<Paren<Option<TfPortList>>>),
}

// -----------------------------------------------------------------------------

#[parser]
pub(crate) fn task_declaration(s: Span) -> IResult<Span, TaskDeclaration> {
    let (s, a) = keyword("task")(s)?;
    let (s, b) = opt(lifetime)(s)?;
    let (s, c) = task_body_declaration(s)?;
    Ok((s, TaskDeclaration { nodes: (a, b, c) }))
}

#[parser]
pub(crate) fn task_body_declaration(s: Span) -> IResult<Span, TaskBodyDeclaration> {
    alt((
        task_body_declaration_without_port,
        task_body_declaration_with_port,
    ))(s)
}

#[parser]
pub(crate) fn task_body_declaration_without_port(s: Span) -> IResult<Span, TaskBodyDeclaration> {
    let (s, a) = opt(interface_identifier_or_class_scope)(s)?;
    let (s, b) = task_identifier(s)?;
    let (s, c) = symbol(";")(s)?;
    let (s, d) = many0(tf_item_declaration)(s)?;
    let (s, e) = many0(statement_or_null)(s)?;
    let (s, f) = keyword("endtask")(s)?;
    let (s, g) = opt(pair(symbol(":"), task_identifier))(s)?;
    Ok((
        s,
        TaskBodyDeclaration::WithoutPort(Box::new(TaskBodyDeclarationWithoutPort {
            nodes: (a, b, c, d, e, f, g),
        })),
    ))
}

#[parser]
pub(crate) fn task_body_declaration_with_port(s: Span) -> IResult<Span, TaskBodyDeclaration> {
    let (s, a) = opt(interface_identifier_or_class_scope)(s)?;
    let (s, b) = task_identifier(s)?;
    let (s, c) = paren(opt(tf_port_list))(s)?;
    let (s, d) = symbol(";")(s)?;
    let (s, e) = many0(block_item_declaration)(s)?;
    let (s, f) = many0(statement_or_null)(s)?;
    let (s, g) = keyword("endtask")(s)?;
    let (s, h) = opt(pair(symbol(":"), task_identifier))(s)?;
    Ok((
        s,
        TaskBodyDeclaration::WithPort(Box::new(TaskBodyDeclarationWithPort {
            nodes: (a, b, c, d, e, f, g, h),
        })),
    ))
}

#[parser]
pub(crate) fn tf_item_declaration(s: Span) -> IResult<Span, TfItemDeclaration> {
    alt((
        map(block_item_declaration, |x| {
            TfItemDeclaration::BlockItemDeclaration(Box::new(x))
        }),
        map(tf_port_declaration, |x| {
            TfItemDeclaration::TfPortDeclaration(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub(crate) fn tf_port_list(s: Span) -> IResult<Span, TfPortList> {
    let (s, a) = list(symbol(","), tf_port_item)(s)?;
    Ok((s, TfPortList { nodes: (a,) }))
}

#[parser(Ambiguous)]
pub(crate) fn tf_port_item(s: Span) -> IResult<Span, TfPortItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = opt(tf_port_direction)(s)?;
    let (s, c) = opt(var)(s)?;
    let (s, d) = ambiguous_opt(data_type_or_implicit)(s)?;
    let (s, e) = opt(triple(
        port_identifier,
        many0(variable_dimension),
        opt(pair(symbol(":"), expression)),
    ))(s)?;
    Ok((
        s,
        TfPortItem {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[parser]
pub(crate) fn tf_port_direction(s: Span) -> IResult<Span, TfPortDirection> {
    alt((
        map(port_direction, |x| {
            TfPortDirection::PortDirection(Box::new(x))
        }),
        map(pair(keyword("const"), keyword("ref")), |x| {
            TfPortDirection::ConstRef(Box::new(x))
        }),
    ))(s)
}

#[parser(Ambiguous)]
pub(crate) fn tf_port_declaration(s: Span) -> IResult<Span, TfPortDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = tf_port_direction(s)?;
    let (s, c) = opt(var)(s)?;
    let (s, d) = ambiguous_opt(data_type_or_implicit)(s)?;
    let (s, e) = list_of_tf_variable_identifiers(s)?;
    let (s, f) = symbol(";")(s)?;
    Ok((
        s,
        TfPortDeclaration {
            nodes: (a, b, c, d, e, f),
        },
    ))
}

#[parser]
pub(crate) fn task_prototype(s: Span) -> IResult<Span, TaskPrototype> {
    let (s, a) = keyword("task")(s)?;
    let (s, b) = task_identifier(s)?;
    let (s, c) = opt(paren(opt(tf_port_list)))(s)?;
    Ok((s, TaskPrototype { nodes: (a, b, c) }))
}

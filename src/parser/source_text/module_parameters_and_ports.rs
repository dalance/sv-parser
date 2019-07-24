use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum ParameterPortList {
    Assignment(Box<ParameterPortListAssignment>),
    Declaration(Box<ParameterPortListDeclaration>),
    Empty(Box<(Symbol, Symbol, Symbol)>),
}

#[derive(Clone, Debug, Node)]
pub struct ParameterPortListAssignment {
    pub nodes: (
        Symbol,
        Paren<(
            ListOfParamAssignments,
            Vec<(Symbol, ParameterPortDeclaration)>,
        )>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ParameterPortListDeclaration {
    pub nodes: (Symbol, Paren<List<Symbol, ParameterPortDeclaration>>),
}

#[derive(Clone, Debug, Node)]
pub enum ParameterPortDeclaration {
    ParameterDeclaration(Box<ParameterDeclaration>),
    LocalParameterDeclaration(Box<LocalParameterDeclaration>),
    ParamList(Box<ParameterPortDeclarationParamList>),
    TypeList(Box<ParameterPortDeclarationTypeList>),
}

#[derive(Clone, Debug, Node)]
pub struct ParameterPortDeclarationParamList {
    pub nodes: (DataType, ListOfParamAssignments),
}

#[derive(Clone, Debug, Node)]
pub struct ParameterPortDeclarationTypeList {
    pub nodes: (Keyword, ListOfTypeAssignments),
}

#[derive(Clone, Debug, Node)]
pub struct ListOfPorts {
    pub nodes: (Paren<List<Symbol, Port>>,),
}

#[derive(Clone, Debug, Node)]
pub struct ListOfPortDeclarations {
    pub nodes: (Paren<Option<List<Symbol, (Vec<AttributeInstance>, AnsiPortDeclaration)>>>,),
}

#[derive(Clone, Debug, Node)]
pub enum PortDeclaration {
    Inout(Box<PortDeclarationInout>),
    Input(Box<PortDeclarationInput>),
    Output(Box<PortDeclarationOutput>),
    Ref(Box<PortDeclarationRef>),
    Interface(Box<PortDeclarationInterface>),
}

#[derive(Clone, Debug, Node)]
pub struct PortDeclarationInout {
    pub nodes: (Vec<AttributeInstance>, InoutDeclaration),
}

#[derive(Clone, Debug, Node)]
pub struct PortDeclarationInput {
    pub nodes: (Vec<AttributeInstance>, InputDeclaration),
}

#[derive(Clone, Debug, Node)]
pub struct PortDeclarationOutput {
    pub nodes: (Vec<AttributeInstance>, OutputDeclaration),
}

#[derive(Clone, Debug, Node)]
pub struct PortDeclarationRef {
    pub nodes: (Vec<AttributeInstance>, RefDeclaration),
}

#[derive(Clone, Debug, Node)]
pub struct PortDeclarationInterface {
    pub nodes: (Vec<AttributeInstance>, InterfacePortDeclaration),
}

#[derive(Clone, Debug, Node)]
pub enum Port {
    NonNamed(Box<PortNonNamed>),
    Named(Box<PortNamed>),
}

#[derive(Clone, Debug, Node)]
pub struct PortNonNamed {
    pub nodes: (Option<PortExpression>,),
}

#[derive(Clone, Debug, Node)]
pub struct PortNamed {
    pub nodes: (Symbol, PortIdentifier, Paren<Option<PortExpression>>),
}

#[derive(Clone, Debug, Node)]
pub enum PortExpression {
    PortReference(Box<PortReference>),
    Brace(Box<PortExpressionBrace>),
}

#[derive(Clone, Debug, Node)]
pub struct PortExpressionBrace {
    pub nodes: (Brace<List<Symbol, PortReference>>,),
}

#[derive(Clone, Debug, Node)]
pub struct PortReference {
    pub nodes: (PortIdentifier, ConstantSelect),
}

#[derive(Clone, Debug, Node)]
pub enum PortDirection {
    Input(Box<Keyword>),
    Output(Box<Keyword>),
    Inout(Box<Keyword>),
    Ref(Box<Keyword>),
}

#[derive(Clone, Debug, Node)]
pub struct NetPortHeader {
    pub nodes: (Option<PortDirection>, NetPortType),
}

#[derive(Clone, Debug, Node)]
pub struct VariablePortHeader {
    pub nodes: (Option<PortDirection>, VariablePortType),
}

#[derive(Clone, Debug, Node)]
pub enum InterfacePortHeader {
    Identifier(Box<InterfacePortHeaderIdentifier>),
    Interface(Box<InterfacePortHeaderInterface>),
}

#[derive(Clone, Debug, Node)]
pub struct InterfacePortHeaderIdentifier {
    pub nodes: (InterfaceIdentifier, Option<(Symbol, ModportIdentifier)>),
}

#[derive(Clone, Debug, Node)]
pub struct InterfacePortHeaderInterface {
    pub nodes: (Keyword, Option<(Symbol, ModportIdentifier)>),
}

#[derive(Clone, Debug, Node)]
pub enum NetPortHeaderOrInterfacePortHeader {
    NetPortHeader(Box<NetPortHeader>),
    InterfacePortHeader(Box<InterfacePortHeader>),
}
#[derive(Clone, Debug, Node)]
pub enum AnsiPortDeclaration {
    Net(Box<AnsiPortDeclarationNet>),
    Variable(Box<AnsiPortDeclarationVariable>),
    Paren(Box<AnsiPortDeclarationParen>),
}

#[derive(Clone, Debug, Node)]
pub struct AnsiPortDeclarationNet {
    pub nodes: (
        Option<NetPortHeaderOrInterfacePortHeader>,
        PortIdentifier,
        Vec<UnpackedDimension>,
        Option<(Symbol, ConstantExpression)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct AnsiPortDeclarationVariable {
    pub nodes: (
        Option<VariablePortHeader>,
        PortIdentifier,
        Vec<VariableDimension>,
        Option<(Symbol, ConstantExpression)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct AnsiPortDeclarationParen {
    pub nodes: (
        Option<PortDirection>,
        Symbol,
        PortIdentifier,
        Paren<Option<Expression>>,
    ),
}

// -----------------------------------------------------------------------------

#[parser]
pub(crate) fn parameter_port_list(s: Span) -> IResult<Span, ParameterPortList> {
    alt((
        parameter_port_list_assignment,
        parameter_port_list_declaration,
        parameter_port_list_empty,
    ))(s)
}

#[parser]
pub(crate) fn parameter_port_list_assignment(s: Span) -> IResult<Span, ParameterPortList> {
    let (s, a) = symbol("#")(s)?;
    let (s, b) = paren(pair(
        list_of_param_assignments,
        many0(pair(symbol(","), parameter_port_declaration)),
    ))(s)?;
    Ok((
        s,
        ParameterPortList::Assignment(Box::new(ParameterPortListAssignment { nodes: (a, b) })),
    ))
}

#[parser]
pub(crate) fn parameter_port_list_declaration(s: Span) -> IResult<Span, ParameterPortList> {
    let (s, a) = symbol("#")(s)?;
    let (s, b) = paren(list(symbol(","), parameter_port_declaration))(s)?;
    Ok((
        s,
        ParameterPortList::Declaration(Box::new(ParameterPortListDeclaration { nodes: (a, b) })),
    ))
}

#[parser]
pub(crate) fn parameter_port_list_empty(s: Span) -> IResult<Span, ParameterPortList> {
    let (s, a) = symbol("#")(s)?;
    let (s, b) = symbol("(")(s)?;
    let (s, c) = symbol(")")(s)?;
    Ok((s, ParameterPortList::Empty(Box::new((a, b, c)))))
}

#[parser]
pub(crate) fn parameter_port_declaration(s: Span) -> IResult<Span, ParameterPortDeclaration> {
    alt((
        map(parameter_declaration, |x| {
            ParameterPortDeclaration::ParameterDeclaration(Box::new(x))
        }),
        map(local_parameter_declaration, |x| {
            ParameterPortDeclaration::LocalParameterDeclaration(Box::new(x))
        }),
        parameter_port_declaration_param_list,
        parameter_port_declaration_type_list,
    ))(s)
}

#[parser]
pub(crate) fn parameter_port_declaration_param_list(s: Span) -> IResult<Span, ParameterPortDeclaration> {
    let (s, a) = data_type(s)?;
    let (s, b) = list_of_param_assignments(s)?;
    Ok((
        s,
        ParameterPortDeclaration::ParamList(Box::new(ParameterPortDeclarationParamList {
            nodes: (a, b),
        })),
    ))
}

#[parser]
pub(crate) fn parameter_port_declaration_type_list(s: Span) -> IResult<Span, ParameterPortDeclaration> {
    let (s, a) = keyword("type")(s)?;
    let (s, b) = list_of_type_assignments(s)?;
    Ok((
        s,
        ParameterPortDeclaration::TypeList(Box::new(ParameterPortDeclarationTypeList {
            nodes: (a, b),
        })),
    ))
}

#[parser]
pub(crate) fn list_of_ports(s: Span) -> IResult<Span, ListOfPorts> {
    let (s, a) = paren(list(symbol(","), port))(s)?;
    Ok((s, ListOfPorts { nodes: (a,) }))
}

#[parser]
pub(crate) fn list_of_port_declarations(s: Span) -> IResult<Span, ListOfPortDeclarations> {
    let (s, a) = paren(opt(list(
        symbol(","),
        pair(many0(attribute_instance), ansi_port_declaration),
    )))(s)?;
    Ok((s, ListOfPortDeclarations { nodes: (a,) }))
}

#[parser]
pub(crate) fn port_declaration(s: Span) -> IResult<Span, PortDeclaration> {
    alt((
        port_declaration_inout,
        port_declaration_input,
        port_declaration_output,
        port_declaration_ref,
        port_declaration_interface,
    ))(s)
}

#[parser]
pub(crate) fn port_declaration_inout(s: Span) -> IResult<Span, PortDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = inout_declaration(s)?;
    Ok((
        s,
        PortDeclaration::Inout(Box::new(PortDeclarationInout { nodes: (a, b) })),
    ))
}

#[parser]
pub(crate) fn port_declaration_input(s: Span) -> IResult<Span, PortDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = input_declaration(s)?;
    Ok((
        s,
        PortDeclaration::Input(Box::new(PortDeclarationInput { nodes: (a, b) })),
    ))
}

#[parser]
pub(crate) fn port_declaration_output(s: Span) -> IResult<Span, PortDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = output_declaration(s)?;
    Ok((
        s,
        PortDeclaration::Output(Box::new(PortDeclarationOutput { nodes: (a, b) })),
    ))
}

#[parser]
pub(crate) fn port_declaration_ref(s: Span) -> IResult<Span, PortDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = ref_declaration(s)?;
    Ok((
        s,
        PortDeclaration::Ref(Box::new(PortDeclarationRef { nodes: (a, b) })),
    ))
}

#[parser]
pub(crate) fn port_declaration_interface(s: Span) -> IResult<Span, PortDeclaration> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = interface_port_declaration(s)?;
    Ok((
        s,
        PortDeclaration::Interface(Box::new(PortDeclarationInterface { nodes: (a, b) })),
    ))
}

#[parser]
pub(crate) fn port(s: Span) -> IResult<Span, Port> {
    alt((port_non_named, port_named))(s)
}

#[parser(MaybeRecursive)]
pub(crate) fn port_non_named(s: Span) -> IResult<Span, Port> {
    let (s, a) = opt(port_expression)(s)?;
    Ok((s, Port::NonNamed(Box::new(PortNonNamed { nodes: (a,) }))))
}

#[parser]
pub(crate) fn port_named(s: Span) -> IResult<Span, Port> {
    let (s, a) = symbol(".")(s)?;
    let (s, b) = port_identifier(s)?;
    let (s, c) = paren(opt(port_expression))(s)?;
    Ok((s, Port::Named(Box::new(PortNamed { nodes: (a, b, c) }))))
}

#[parser]
pub(crate) fn port_expression(s: Span) -> IResult<Span, PortExpression> {
    alt((
        map(port_reference, |x| {
            PortExpression::PortReference(Box::new(x))
        }),
        port_expressio_named,
    ))(s)
}

#[parser]
pub(crate) fn port_expressio_named(s: Span) -> IResult<Span, PortExpression> {
    let (s, a) = brace(list(symbol(","), port_reference))(s)?;
    Ok((
        s,
        PortExpression::Brace(Box::new(PortExpressionBrace { nodes: (a,) })),
    ))
}

#[parser]
pub(crate) fn port_reference(s: Span) -> IResult<Span, PortReference> {
    let (s, a) = port_identifier(s)?;
    let (s, b) = constant_select(s)?;
    Ok((s, PortReference { nodes: (a, b) }))
}

#[parser]
pub(crate) fn port_direction(s: Span) -> IResult<Span, PortDirection> {
    alt((
        map(keyword("input"), |x| PortDirection::Input(Box::new(x))),
        map(keyword("output"), |x| PortDirection::Output(Box::new(x))),
        map(keyword("inout"), |x| PortDirection::Inout(Box::new(x))),
        map(keyword("ref"), |x| PortDirection::Ref(Box::new(x))),
    ))(s)
}

#[parser]
pub(crate) fn net_port_header(s: Span) -> IResult<Span, NetPortHeader> {
    let (s, a) = opt(port_direction)(s)?;
    let (s, b) = net_port_type(s)?;
    Ok((s, NetPortHeader { nodes: (a, b) }))
}

#[parser]
pub(crate) fn variable_port_header(s: Span) -> IResult<Span, VariablePortHeader> {
    let (s, a) = opt(port_direction)(s)?;
    let (s, b) = variable_port_type(s)?;
    Ok((s, VariablePortHeader { nodes: (a, b) }))
}

#[parser]
pub(crate) fn interface_port_header(s: Span) -> IResult<Span, InterfacePortHeader> {
    alt((
        interface_port_header_identifier,
        interface_port_header_interface,
    ))(s)
}

#[parser]
pub(crate) fn interface_port_header_identifier(s: Span) -> IResult<Span, InterfacePortHeader> {
    let (s, a) = interface_identifier(s)?;
    let (s, b) = opt(pair(symbol("."), modport_identifier))(s)?;
    Ok((
        s,
        InterfacePortHeader::Identifier(Box::new(InterfacePortHeaderIdentifier { nodes: (a, b) })),
    ))
}

#[parser]
pub(crate) fn interface_port_header_interface(s: Span) -> IResult<Span, InterfacePortHeader> {
    let (s, a) = keyword("interface")(s)?;
    let (s, b) = opt(pair(symbol("."), modport_identifier))(s)?;
    Ok((
        s,
        InterfacePortHeader::Interface(Box::new(InterfacePortHeaderInterface { nodes: (a, b) })),
    ))
}

#[parser]
pub(crate) fn ansi_port_declaration(s: Span) -> IResult<Span, AnsiPortDeclaration> {
    alt((
        ansi_port_declaration_net,
        ansi_port_declaration_port,
        ansi_port_declaration_paren,
    ))(s)
}

#[parser]
pub(crate) fn ansi_port_declaration_net(s: Span) -> IResult<Span, AnsiPortDeclaration> {
    let (s, a) = opt(net_port_header_or_interface_port_header)(s)?;
    let (s, b) = port_identifier(s)?;
    let (s, c) = many0(unpacked_dimension)(s)?;
    let (s, d) = opt(pair(symbol("="), constant_expression))(s)?;
    Ok((
        s,
        AnsiPortDeclaration::Net(Box::new(AnsiPortDeclarationNet {
            nodes: (a, b, c, d),
        })),
    ))
}

#[parser]
pub(crate) fn net_port_header_or_interface_port_header(
    s: Span,
) -> IResult<Span, NetPortHeaderOrInterfacePortHeader> {
    alt((
        map(net_port_header, |x| {
            NetPortHeaderOrInterfacePortHeader::NetPortHeader(Box::new(x))
        }),
        map(interface_port_header, |x| {
            NetPortHeaderOrInterfacePortHeader::InterfacePortHeader(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub(crate) fn ansi_port_declaration_port(s: Span) -> IResult<Span, AnsiPortDeclaration> {
    let (s, a) = opt(variable_port_header)(s)?;
    let (s, b) = port_identifier(s)?;
    let (s, c) = many0(variable_dimension)(s)?;
    let (s, d) = opt(pair(symbol("="), constant_expression))(s)?;
    Ok((
        s,
        AnsiPortDeclaration::Variable(Box::new(AnsiPortDeclarationVariable {
            nodes: (a, b, c, d),
        })),
    ))
}

#[parser]
pub(crate) fn ansi_port_declaration_paren(s: Span) -> IResult<Span, AnsiPortDeclaration> {
    let (s, a) = opt(port_direction)(s)?;
    let (s, b) = symbol(".")(s)?;
    let (s, c) = port_identifier(s)?;
    let (s, d) = paren(opt(expression))(s)?;
    Ok((
        s,
        AnsiPortDeclaration::Paren(Box::new(AnsiPortDeclarationParen {
            nodes: (a, b, c, d),
        })),
    ))
}

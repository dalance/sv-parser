use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ParameterPortList {
    Assignment(Box<ParameterPortListAssignment>),
    Declaration(Box<ParameterPortListDeclaration>),
    Empty(Box<(Symbol, Symbol, Symbol)>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ParameterPortListAssignment {
    pub nodes: (
        Symbol,
        Paren<(
            ListOfParamAssignments,
            Vec<(Symbol, ParameterPortDeclaration)>,
        )>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ParameterPortListDeclaration {
    pub nodes: (Symbol, Paren<List<Symbol, ParameterPortDeclaration>>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ParameterPortDeclaration {
    ParameterDeclaration(Box<ParameterDeclaration>),
    LocalParameterDeclaration(Box<LocalParameterDeclaration>),
    ParamList(Box<ParameterPortDeclarationParamList>),
    TypeList(Box<ParameterPortDeclarationTypeList>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ParameterPortDeclarationParamList {
    pub nodes: (DataType, ListOfParamAssignments),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ParameterPortDeclarationTypeList {
    pub nodes: (Keyword, ListOfTypeAssignments),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ListOfPorts {
    pub nodes: (Paren<List<Symbol, Port>>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ListOfPortDeclarations {
    pub nodes: (Paren<Option<List<Symbol, (Vec<AttributeInstance>, AnsiPortDeclaration)>>>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum PortDeclaration {
    Inout(Box<PortDeclarationInout>),
    Input(Box<PortDeclarationInput>),
    Output(Box<PortDeclarationOutput>),
    Ref(Box<PortDeclarationRef>),
    Interface(Box<PortDeclarationInterface>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PortDeclarationInout {
    pub nodes: (Vec<AttributeInstance>, InoutDeclaration),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PortDeclarationInput {
    pub nodes: (Vec<AttributeInstance>, InputDeclaration),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PortDeclarationOutput {
    pub nodes: (Vec<AttributeInstance>, OutputDeclaration),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PortDeclarationRef {
    pub nodes: (Vec<AttributeInstance>, RefDeclaration),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PortDeclarationInterface {
    pub nodes: (Vec<AttributeInstance>, InterfacePortDeclaration),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum Port {
    NonNamed(Box<PortNonNamed>),
    Named(Box<PortNamed>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PortNonNamed {
    pub nodes: (Option<PortExpression>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PortNamed {
    pub nodes: (Symbol, PortIdentifier, Paren<Option<PortExpression>>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum PortExpression {
    PortReference(Box<PortReference>),
    Brace(Box<PortExpressionBrace>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PortExpressionBrace {
    pub nodes: (Brace<List<Symbol, PortReference>>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PortReference {
    pub nodes: (PortIdentifier, ConstantSelect),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum PortDirection {
    Input(Box<Keyword>),
    Output(Box<Keyword>),
    Inout(Box<Keyword>),
    Ref(Box<Keyword>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct NetPortHeader {
    pub nodes: (Option<PortDirection>, NetPortType),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct VariablePortHeader {
    pub nodes: (Option<PortDirection>, VariablePortType),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum InterfacePortHeader {
    Identifier(Box<InterfacePortHeaderIdentifier>),
    Interface(Box<InterfacePortHeaderInterface>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct InterfacePortHeaderIdentifier {
    pub nodes: (InterfaceIdentifier, Option<(Symbol, ModportIdentifier)>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct InterfacePortHeaderInterface {
    pub nodes: (Keyword, Option<(Symbol, ModportIdentifier)>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum NetPortHeaderOrInterfacePortHeader {
    NetPortHeader(Box<NetPortHeader>),
    InterfacePortHeader(Box<InterfacePortHeader>),
}
#[derive(Clone, Debug, PartialEq, Node)]
pub enum AnsiPortDeclaration {
    Net(Box<AnsiPortDeclarationNet>),
    Variable(Box<AnsiPortDeclarationVariable>),
    Paren(Box<AnsiPortDeclarationParen>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct AnsiPortDeclarationNet {
    pub nodes: (
        Option<NetPortHeaderOrInterfacePortHeader>,
        PortIdentifier,
        Vec<UnpackedDimension>,
        Option<(Symbol, ConstantExpression)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct AnsiPortDeclarationVariable {
    pub nodes: (
        Option<VariablePortHeader>,
        PortIdentifier,
        Vec<VariableDimension>,
        Option<(Symbol, ConstantExpression)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct AnsiPortDeclarationParen {
    pub nodes: (
        Option<PortDirection>,
        Symbol,
        PortIdentifier,
        Paren<Option<Expression>>,
    ),
}

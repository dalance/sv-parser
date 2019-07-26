use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct ConstantFunctionCall {
    pub nodes: (FunctionSubroutineCall,),
}

#[derive(Clone, Debug, Node)]
pub struct TfCall {
    pub nodes: (
        PsOrHierarchicalTfIdentifier,
        Vec<AttributeInstance>,
        Option<Paren<ListOfArguments>>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum SystemTfCall {
    ArgOptionl(Box<SystemTfCallArgOptional>),
    ArgDataType(Box<SystemTfCallArgDataType>),
    ArgExpression(Box<SystemTfCallArgExpression>),
}

#[derive(Clone, Debug, Node)]
pub struct SystemTfCallArgOptional {
    pub nodes: (SystemTfIdentifier, Option<Paren<ListOfArguments>>),
}

#[derive(Clone, Debug, Node)]
pub struct SystemTfCallArgDataType {
    pub nodes: (
        SystemTfIdentifier,
        Paren<(DataType, Option<(Symbol, Expression)>)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct SystemTfCallArgExpression {
    pub nodes: (
        SystemTfIdentifier,
        Paren<(
            List<Symbol, Option<Expression>>,
            Option<(Symbol, Option<ClockingEvent>)>,
        )>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum SubroutineCall {
    TfCall(Box<TfCall>),
    SystemTfCall(Box<SystemTfCall>),
    MethodCall(Box<MethodCall>),
    Randomize(Box<SubroutineCallRandomize>),
}

#[derive(Clone, Debug, Node)]
pub struct SubroutineCallRandomize {
    pub nodes: (Option<(Keyword, Symbol)>, RandomizeCall),
}

#[derive(Clone, Debug, Node)]
pub struct FunctionSubroutineCall {
    pub nodes: (SubroutineCall,),
}

#[derive(Clone, Debug, Node)]
pub enum ListOfArguments {
    Ordered(Box<ListOfArgumentsOrdered>),
    Named(Box<ListOfArgumentsNamed>),
}

#[derive(Clone, Debug, Node)]
pub struct ListOfArgumentsOrdered {
    pub nodes: (
        List<Symbol, Option<Expression>>,
        Vec<(Symbol, Symbol, Identifier, Paren<Option<Expression>>)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ListOfArgumentsNamed {
    pub nodes: (
        Symbol,
        Identifier,
        Paren<Option<Expression>>,
        Vec<(Symbol, Symbol, Identifier, Paren<Option<Expression>>)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct MethodCall {
    pub nodes: (MethodCallRoot, Symbol, MethodCallBody),
}

#[derive(Clone, Debug, Node)]
pub enum MethodCallBody {
    User(Box<MethodCallBodyUser>),
    BuiltInMethodCall(Box<BuiltInMethodCall>),
}

#[derive(Clone, Debug, Node)]
pub struct MethodCallBodyUser {
    pub nodes: (
        MethodIdentifier,
        Vec<AttributeInstance>,
        Option<Paren<ListOfArguments>>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum BuiltInMethodCall {
    ArrayManipulationCall(Box<ArrayManipulationCall>),
    RandomizeCall(Box<RandomizeCall>),
}

#[derive(Clone, Debug, Node)]
pub struct ArrayManipulationCall {
    pub nodes: (
        ArrayMethodName,
        Vec<AttributeInstance>,
        Option<Paren<ListOfArguments>>,
        Option<(Keyword, Paren<Expression>)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct RandomizeCall {
    pub nodes: (
        Keyword,
        Vec<AttributeInstance>,
        Option<Paren<Option<VariableIdentifierListOrNull>>>,
        Option<(
            Keyword,
            Option<Paren<Option<IdentifierList>>>,
            ConstraintBlock,
        )>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum VariableIdentifierListOrNull {
    VariableIdentifierList(Box<VariableIdentifierList>),
    Null(Box<Keyword>),
}

#[derive(Clone, Debug, Node)]
pub enum MethodCallRoot {
    Primary(Box<Primary>),
    ImplicitClassHandle(Box<ImplicitClassHandle>),
}

#[derive(Clone, Debug, Node)]
pub enum ArrayMethodName {
    MethodIdentifier(Box<MethodIdentifier>),
    Unique(Box<Keyword>),
    And(Box<Keyword>),
    Or(Box<Keyword>),
    Xor(Box<Keyword>),
}

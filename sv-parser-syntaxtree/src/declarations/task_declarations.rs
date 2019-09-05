use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub struct TaskDeclaration {
    pub nodes: (Keyword, Option<Lifetime>, TaskBodyDeclaration),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum TaskBodyDeclaration {
    WithoutPort(Box<TaskBodyDeclarationWithoutPort>),
    WithPort(Box<TaskBodyDeclarationWithPort>),
}

#[derive(Clone, Debug, PartialEq, Node)]
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

#[derive(Clone, Debug, PartialEq, Node)]
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

#[derive(Clone, Debug, PartialEq, Node)]
pub enum TfItemDeclaration {
    BlockItemDeclaration(Box<BlockItemDeclaration>),
    TfPortDeclaration(Box<TfPortDeclaration>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct TfPortList {
    pub nodes: (List<Symbol, TfPortItem>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct TfPortItem {
    pub nodes: (
        Vec<AttributeInstance>,
        Option<TfPortDirection>,
        Option<Var>,
        DataTypeOrImplicit,
        Option<(
            PortIdentifier,
            Vec<VariableDimension>,
            Option<(Symbol, Expression)>,
        )>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum TfPortDirection {
    PortDirection(Box<PortDirection>),
    ConstRef(Box<(Keyword, Keyword)>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct TfPortDeclaration {
    pub nodes: (
        Vec<AttributeInstance>,
        TfPortDirection,
        Option<Var>,
        DataTypeOrImplicit,
        ListOfTfVariableIdentifiers,
        Symbol,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct TaskPrototype {
    pub nodes: (Keyword, TaskIdentifier, Option<Paren<Option<TfPortList>>>),
}

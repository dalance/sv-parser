use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct ModuleInstantiation {
    pub nodes: (
        ModuleIdentifier,
        Option<ParameterValueAssignment>,
        List<Symbol, HierarchicalInstance>,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ParameterValueAssignment {
    pub nodes: (Symbol, Paren<Option<ListOfParameterAssignments>>),
}

#[derive(Clone, Debug, Node)]
pub enum ListOfParameterAssignments {
    Ordered(Box<ListOfParameterAssignmentsOrdered>),
    Named(Box<ListOfParameterAssignmentsNamed>),
}

#[derive(Clone, Debug, Node)]
pub struct ListOfParameterAssignmentsOrdered {
    pub nodes: (List<Symbol, OrderedParameterAssignment>,),
}

#[derive(Clone, Debug, Node)]
pub struct ListOfParameterAssignmentsNamed {
    pub nodes: (List<Symbol, NamedParameterAssignment>,),
}

#[derive(Clone, Debug, Node)]
pub struct OrderedParameterAssignment {
    pub nodes: (ParamExpression,),
}

#[derive(Clone, Debug, Node)]
pub struct NamedParameterAssignment {
    pub nodes: (Symbol, ParameterIdentifier, Paren<Option<ParamExpression>>),
}

#[derive(Clone, Debug, Node)]
pub struct HierarchicalInstance {
    pub nodes: (NameOfInstance, Paren<Option<ListOfPortConnections>>),
}

#[derive(Clone, Debug, Node)]
pub struct NameOfInstance {
    pub nodes: (InstanceIdentifier, Vec<UnpackedDimension>),
}

#[derive(Clone, Debug, Node)]
pub enum ListOfPortConnections {
    Ordered(Box<ListOfPortConnectionsOrdered>),
    Named(Box<ListOfPortConnectionsNamed>),
}

#[derive(Clone, Debug, Node)]
pub struct ListOfPortConnectionsOrdered {
    pub nodes: (List<Symbol, OrderedPortConnection>,),
}

#[derive(Clone, Debug, Node)]
pub struct ListOfPortConnectionsNamed {
    pub nodes: (List<Symbol, NamedPortConnection>,),
}

#[derive(Clone, Debug, Node)]
pub struct OrderedPortConnection {
    pub nodes: (Vec<AttributeInstance>, Option<Expression>),
}

#[derive(Clone, Debug, Node)]
pub enum NamedPortConnection {
    Identifier(Box<NamedPortConnectionIdentifier>),
    Asterisk(Box<NamedPortConnectionAsterisk>),
}

#[derive(Clone, Debug, Node)]
pub struct NamedPortConnectionIdentifier {
    pub nodes: (
        Vec<AttributeInstance>,
        Symbol,
        PortIdentifier,
        Option<Paren<Option<Expression>>>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct NamedPortConnectionAsterisk {
    pub nodes: (Vec<AttributeInstance>, Symbol),
}

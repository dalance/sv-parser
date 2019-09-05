use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub struct DefparamAssignment {
    pub nodes: (
        HierarchicalParameterIdentifier,
        Symbol,
        ConstantMintypmaxExpression,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct NetDeclAssignment {
    pub nodes: (
        NetIdentifier,
        Vec<UnpackedDimension>,
        Option<(Symbol, Expression)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ParamAssignment {
    pub nodes: (
        ParameterIdentifier,
        Vec<UnpackedDimension>,
        Option<(Symbol, ConstantParamExpression)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum SpecparamAssignment {
    Mintypmax(Box<SpecparamAssignmentMintypmax>),
    PulseControlSpecparam(Box<PulseControlSpecparam>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct SpecparamAssignmentMintypmax {
    pub nodes: (SpecparamIdentifier, Symbol, ConstantMintypmaxExpression),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct TypeAssignment {
    pub nodes: (TypeIdentifier, Option<(Symbol, DataType)>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum PulseControlSpecparam {
    WithoutDescriptor(Box<PulseControlSpecparamWithoutDescriptor>),
    WithDescriptor(Box<PulseControlSpecparamWithDescriptor>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PulseControlSpecparamWithoutDescriptor {
    pub nodes: (
        Symbol,
        Symbol,
        Paren<(RejectLimitValue, Option<(Symbol, ErrorLimitValue)>)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
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

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ErrorLimitValue {
    pub nodes: (LimitValue,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct RejectLimitValue {
    pub nodes: (LimitValue,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct LimitValue {
    pub nodes: (ConstantMintypmaxExpression,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum VariableDeclAssignment {
    Variable(Box<VariableDeclAssignmentVariable>),
    DynamicArray(Box<VariableDeclAssignmentDynamicArray>),
    Class(Box<VariableDeclAssignmentClass>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct VariableDeclAssignmentVariable {
    pub nodes: (
        VariableIdentifier,
        Vec<VariableDimension>,
        Option<(Symbol, Expression)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct VariableDeclAssignmentDynamicArray {
    pub nodes: (
        DynamicArrayVariableIdentifier,
        UnsizedDimension,
        Vec<VariableDimension>,
        Option<(Symbol, DynamicArrayNew)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct VariableDeclAssignmentClass {
    pub nodes: (ClassVariableIdentifier, (Symbol, ClassNew)),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ClassNew {
    Argument(Box<ClassNewArgument>),
    Expression(Box<ClassNewExpression>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ClassNewArgument {
    pub nodes: (Option<ClassScope>, Keyword, Option<Paren<ListOfArguments>>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ClassNewExpression {
    pub nodes: (Keyword, Expression),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct DynamicArrayNew {
    pub nodes: (Keyword, Bracket<Expression>, Option<Paren<Expression>>),
}

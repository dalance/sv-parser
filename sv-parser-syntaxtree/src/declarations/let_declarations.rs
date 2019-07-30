use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct LetDeclaration {
    pub nodes: (
        Keyword,
        LetIdentifier,
        Option<Paren<Option<LetPortList>>>,
        Symbol,
        Expression,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct LetIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct LetPortList {
    pub nodes: (List<Symbol, LetPortItem>,),
}

#[derive(Clone, Debug, Node)]
pub struct LetPortItem {
    pub nodes: (
        Vec<AttributeInstance>,
        LetFormalType,
        FormalPortIdentifier,
        Vec<VariableDimension>,
        Option<(Symbol, Expression)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum LetFormalType {
    DataTypeOrImplicit(Box<DataTypeOrImplicit>),
    Untyped(Box<Keyword>),
}

#[derive(Clone, Debug, Node)]
pub struct LetExpression {
    pub nodes: (
        Option<PackageScope>,
        LetIdentifier,
        Option<Paren<Option<LetListOfArguments>>>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum LetListOfArguments {
    Ordered(Box<LetListOfArgumentsOrdered>),
    Named(Box<LetListOfArgumentsNamed>),
}

#[derive(Clone, Debug, Node)]
pub struct LetListOfArgumentsOrdered {
    pub nodes: (
        List<Symbol, Option<LetActualArg>>,
        Vec<(Symbol, Symbol, Identifier, Paren<Option<LetActualArg>>)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct LetListOfArgumentsNamed {
    pub nodes: (List<Symbol, (Symbol, Identifier, Paren<Option<LetActualArg>>)>,),
}

#[derive(Clone, Debug, Node)]
pub struct LetActualArg {
    pub nodes: (Expression,),
}

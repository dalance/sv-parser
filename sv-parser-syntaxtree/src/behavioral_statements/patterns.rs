use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum Pattern {
    Variable(Box<PatternVariable>),
    Asterisk(Box<Symbol>),
    ConstantExpression(Box<ConstantExpression>),
    Tagged(Box<PatternTagged>),
    List(Box<PatternList>),
    IdentifierList(Box<PatternIdentifierList>),
}

#[derive(Clone, Debug, Node)]
pub struct PatternVariable {
    pub nodes: (Symbol, VariableIdentifier),
}

#[derive(Clone, Debug, Node)]
pub struct PatternTagged {
    pub nodes: (Keyword, MemberIdentifier, Option<Pattern>),
}

#[derive(Clone, Debug, Node)]
pub struct PatternList {
    pub nodes: (ApostropheBrace<List<Symbol, Pattern>>,),
}

#[derive(Clone, Debug, Node)]
pub struct PatternIdentifierList {
    pub nodes: (ApostropheBrace<List<Symbol, (MemberIdentifier, Symbol, Pattern)>>,),
}

#[derive(Clone, Debug, Node)]
pub enum AssignmentPattern {
    List(Box<AssignmentPatternList>),
    Structure(Box<AssignmentPatternStructure>),
    Array(Box<AssignmentPatternArray>),
    Repeat(Box<AssignmentPatternRepeat>),
}

#[derive(Clone, Debug, Node)]
pub struct AssignmentPatternList {
    pub nodes: (ApostropheBrace<List<Symbol, Expression>>,),
}

#[derive(Clone, Debug, Node)]
pub struct AssignmentPatternStructure {
    pub nodes: (ApostropheBrace<List<Symbol, (StructurePatternKey, Symbol, Expression)>>,),
}

#[derive(Clone, Debug, Node)]
pub struct AssignmentPatternArray {
    pub nodes: (ApostropheBrace<List<Symbol, (ArrayPatternKey, Symbol, Expression)>>,),
}

#[derive(Clone, Debug, Node)]
pub struct AssignmentPatternRepeat {
    pub nodes: (ApostropheBrace<(ConstantExpression, Brace<List<Symbol, Expression>>)>,),
}

#[derive(Clone, Debug, Node)]
pub enum StructurePatternKey {
    MemberIdentifier(Box<MemberIdentifier>),
    AssignmentPatternKey(Box<AssignmentPatternKey>),
}

#[derive(Clone, Debug, Node)]
pub enum ArrayPatternKey {
    ConstantExpression(Box<ConstantExpression>),
    AssignmentPatternKey(Box<AssignmentPatternKey>),
}

#[derive(Clone, Debug, Node)]
pub enum AssignmentPatternKey {
    SimpleType(Box<SimpleType>),
    Default(Box<Keyword>),
}

#[derive(Clone, Debug, Node)]
pub struct AssignmentPatternExpression {
    pub nodes: (Option<AssignmentPatternExpressionType>, AssignmentPattern),
}

#[derive(Clone, Debug, Node)]
pub enum AssignmentPatternExpressionType {
    PsTypeIdentifier(Box<PsTypeIdentifier>),
    PsParameterIdentifier(Box<PsParameterIdentifier>),
    IntegerAtomType(Box<IntegerAtomType>),
    TypeReference(Box<TypeReference>),
}

#[derive(Clone, Debug, Node)]
pub struct ConstantAssignmentPatternExpression {
    pub nodes: (AssignmentPatternExpression,),
}

#[derive(Clone, Debug, Node)]
pub struct AssignmentPatternNetLvalue {
    pub nodes: (ApostropheBrace<List<Symbol, NetLvalue>>,),
}

#[derive(Clone, Debug, Node)]
pub struct AssignmentPatternVariableLvalue {
    pub nodes: (ApostropheBrace<List<Symbol, VariableLvalue>>,),
}

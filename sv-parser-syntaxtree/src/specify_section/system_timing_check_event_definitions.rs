use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub struct TimingCheckEvent {
    pub nodes: (
        Option<TimingCheckEventControl>,
        SpecifyTerminalDescriptor,
        Option<(Symbol, TimingCheckCondition)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ControlledTimingCheckEvent {
    pub nodes: (
        TimingCheckEventControl,
        SpecifyTerminalDescriptor,
        Option<(Symbol, TimingCheckCondition)>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum TimingCheckEventControl {
    Posedge(Box<Keyword>),
    Negedge(Box<Keyword>),
    Edge(Box<Keyword>),
    EdgeControlSpecifier(Box<EdgeControlSpecifier>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum SpecifyTerminalDescriptor {
    SpecifyInputTerminalDescriptor(Box<SpecifyInputTerminalDescriptor>),
    SpecifyOutputTerminalDescriptor(Box<SpecifyOutputTerminalDescriptor>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct EdgeControlSpecifier {
    pub nodes: (Keyword, Bracket<List<Symbol, EdgeDescriptor>>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct EdgeDescriptor {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum TimingCheckCondition {
    ScalarTimingCheckCondition(Box<ScalarTimingCheckCondition>),
    Paren(Box<TimingCheckConditionParen>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct TimingCheckConditionParen {
    pub nodes: (Paren<ScalarTimingCheckCondition>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ScalarTimingCheckCondition {
    Expression(Box<Expression>),
    Unary(Box<ScalarTimingCheckConditionUnary>),
    Binary(Box<ScalarTimingCheckConditionBinary>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ScalarTimingCheckConditionUnary {
    pub nodes: (Symbol, Expression),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ScalarTimingCheckConditionBinary {
    pub nodes: (Expression, Symbol, ScalarConstant),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ScalarConstant {
    pub nodes: (Keyword,),
}

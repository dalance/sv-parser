use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum CompilerDirective {
    ResetallCompilerDirective(Box<ResetallCompilerDirective>),
    TextMacroDefinition(Box<TextMacroDefinition>),
    UndefineCompilerDirective(Box<UndefineCompilerDirective>),
    UndefineallCompilerDirective(Box<UndefineallCompilerDirective>),
    TimescaleCompilerDirective(Box<TimescaleCompilerDirective>),
    DefaultNettypeCompilerDirective(Box<DefaultNettypeCompilerDirective>),
    UnconnectedDriveCompilerDirective(Box<UnconnectedDriveCompilerDirective>),
    NounconnectedDriveCompilerDirective(Box<NounconnectedDriveCompilerDirective>),
    CelldefineDriveCompilerDirective(Box<CelldefineDriveCompilerDirective>),
    EndcelldefineDriveCompilerDirective(Box<EndcelldefineDriveCompilerDirective>),
    Pragma(Box<Pragma>),
    LineCompilerDirective(Box<LineCompilerDirective>),
    KeywordsDirective(Box<KeywordsDirective>),
    EndkeywordsDirective(Box<EndkeywordsDirective>),
}

#[derive(Clone, Debug, Node)]
pub struct ResetallCompilerDirective {
    pub nodes: (Symbol, Keyword),
}

#[derive(Clone, Debug, Node)]
pub struct TextMacroDefinition {
    pub nodes: (Symbol, Keyword, TextMacroName, Option<MacroText>),
}

#[derive(Clone, Debug, Node)]
pub struct TextMacroName {
    pub nodes: (TextMacroIdentifier, Option<Paren<ListOfFormalArguments>>),
}

#[derive(Clone, Debug, Node)]
pub struct ListOfFormalArguments {
    pub nodes: (List<Symbol, FormalArgument>,),
}

#[derive(Clone, Debug, Node)]
pub struct FormalArgument {
    pub nodes: (SimpleIdentifier, Option<(Symbol, DefaultText)>),
}

#[derive(Clone, Debug, Node)]
pub struct TextMacroIdentifier {
    pub nodes: (Identifier,),
}

#[derive(Clone, Debug, Node)]
pub struct MacroText {
    pub nodes: (Locate,),
}

#[derive(Clone, Debug, Node)]
pub struct DefaultText {
    pub nodes: (Locate,),
}

#[derive(Clone, Debug, Node)]
pub struct UndefineCompilerDirective {
    pub nodes: (Symbol, Keyword, TextMacroIdentifier),
}

#[derive(Clone, Debug, Node)]
pub struct UndefineallCompilerDirective {
    pub nodes: (Symbol, Keyword),
}

#[derive(Clone, Debug, Node)]
pub struct TimescaleCompilerDirective {
    pub nodes: (Symbol, Keyword, TimeLiteral, Symbol, TimeLiteral),
}

#[derive(Clone, Debug, Node)]
pub struct DefaultNettypeCompilerDirective {
    pub nodes: (Symbol, Keyword, DefaultNettypeValue),
}

#[derive(Clone, Debug, Node)]
pub struct DefaultNettypeValue {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, Node)]
pub struct UnconnectedDriveCompilerDirective {
    pub nodes: (Symbol, Keyword, Keyword),
}

#[derive(Clone, Debug, Node)]
pub struct NounconnectedDriveCompilerDirective {
    pub nodes: (Symbol, Keyword),
}

#[derive(Clone, Debug, Node)]
pub struct CelldefineDriveCompilerDirective {
    pub nodes: (Symbol, Keyword),
}

#[derive(Clone, Debug, Node)]
pub struct EndcelldefineDriveCompilerDirective {
    pub nodes: (Symbol, Keyword),
}

#[derive(Clone, Debug, Node)]
pub struct Pragma {
    pub nodes: (
        Symbol,
        Keyword,
        PragmaName,
        Option<List<Symbol, PragmaExpression>>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct PragmaName {
    pub nodes: (SimpleIdentifier,),
}

#[derive(Clone, Debug, Node)]
pub enum PragmaExpression {
    PragmaKeyword(Box<PragmaKeyword>),
    Assignment(Box<PragmaExpressionAssignment>),
    PragmaValue(Box<PragmaValue>),
}

#[derive(Clone, Debug, Node)]
pub struct PragmaExpressionAssignment {
    pub nodes: (PragmaKeyword, Symbol, PragmaValue),
}

#[derive(Clone, Debug, Node)]
pub enum PragmaValue {
    Paren(Box<PragmaValueParen>),
    Number(Box<Number>),
    StringLiteral(Box<StringLiteral>),
    Identifier(Box<Identifier>),
}

#[derive(Clone, Debug, Node)]
pub struct PragmaValueParen {
    pub nodes: (Paren<List<Symbol, PragmaExpression>>,),
}

#[derive(Clone, Debug, Node)]
pub struct PragmaKeyword {
    pub nodes: (SimpleIdentifier,),
}

#[derive(Clone, Debug, Node)]
pub struct LineCompilerDirective {
    pub nodes: (Symbol, Keyword, Number, StringLiteral, Level),
}

#[derive(Clone, Debug, Node)]
pub struct Level {
    pub nodes: (Symbol,),
}

#[derive(Clone, Debug, Node)]
pub struct KeywordsDirective {
    pub nodes: (Symbol, Keyword, Symbol, VersionSpecifier, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct VersionSpecifier {
    pub nodes: (Keyword,),
}

#[derive(Clone, Debug, Node)]
pub struct EndkeywordsDirective {
    pub nodes: (Symbol, Keyword),
}

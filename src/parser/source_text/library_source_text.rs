use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct LibraryText<'a> {
    pub nodes: (Vec<LibraryDescription<'a>>,),
}

#[derive(Debug, Node)]
pub enum LibraryDescription<'a> {
    LibraryDeclaration(LibraryDeclaration<'a>),
    IncludeStatement(IncludeStatement<'a>),
    ConfigDeclaration(ConfigDeclaration<'a>),
    Null(Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct LibraryDeclaration<'a> {
    pub nodes: (
        Symbol<'a>,
        LibraryIdentifier<'a>,
        List<Symbol<'a>, FilePathSpec<'a>>,
        Option<(Symbol<'a>, List<Symbol<'a>, FilePathSpec<'a>>)>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct IncludeStatement<'a> {
    pub nodes: (Symbol<'a>, FilePathSpec<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct FilePathSpec<'a> {
    pub nodes: (StringLiteral<'a>,),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn library_text(s: Span) -> IResult<Span, LibraryText> {
    let (s, a) = many0(library_description)(s)?;
    Ok((s, LibraryText { nodes: (a,) }))
}

#[parser]
pub fn library_description(s: Span) -> IResult<Span, LibraryDescription> {
    alt((
        map(library_declaration, |x| {
            LibraryDescription::LibraryDeclaration(x)
        }),
        map(include_statement, |x| {
            LibraryDescription::IncludeStatement(x)
        }),
        map(config_declaration, |x| {
            LibraryDescription::ConfigDeclaration(x)
        }),
        map(symbol(";"), |x| LibraryDescription::Null(x)),
    ))(s)
}

#[parser]
pub fn library_declaration(s: Span) -> IResult<Span, LibraryDeclaration> {
    let (s, a) = symbol("library")(s)?;
    let (s, b) = library_identifier(s)?;
    let (s, c) = list(symbol(","), file_path_spec)(s)?;
    let (s, d) = opt(pair(symbol("-incdir"), list(symbol(","), file_path_spec)))(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        LibraryDeclaration {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[parser]
pub fn include_statement(s: Span) -> IResult<Span, IncludeStatement> {
    let (s, a) = symbol("include")(s)?;
    let (s, b) = file_path_spec(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((s, IncludeStatement { nodes: (a, b, c) }))
}

//TODO support non literal path
#[parser]
pub fn file_path_spec(s: Span) -> IResult<Span, FilePathSpec> {
    let (s, a) = string_literal(s)?;
    Ok((s, FilePathSpec { nodes: (a,) }))
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_library_text() {
        parser_test!(
            library_text,
            "library rtlLib \"*.v\" -incdir \"aaa\";\ninclude \"bbb\";;",
            Ok((_, _))
        );
    }
}

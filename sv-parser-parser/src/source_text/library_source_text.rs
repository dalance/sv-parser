use crate::*;

// -----------------------------------------------------------------------------

#[parser]
pub(crate) fn library_text(s: Span) -> IResult<Span, LibraryText> {
    let (s, a) = many0(library_description)(s)?;
    Ok((s, LibraryText { nodes: (a,) }))
}

#[parser]
pub(crate) fn library_description(s: Span) -> IResult<Span, LibraryDescription> {
    alt((
        map(library_declaration, |x| {
            LibraryDescription::LibraryDeclaration(Box::new(x))
        }),
        map(include_statement, |x| {
            LibraryDescription::IncludeStatement(Box::new(x))
        }),
        map(config_declaration, |x| {
            LibraryDescription::ConfigDeclaration(Box::new(x))
        }),
        map(symbol(";"), |x| LibraryDescription::Null(Box::new(x))),
    ))(s)
}

#[parser]
pub(crate) fn library_declaration(s: Span) -> IResult<Span, LibraryDeclaration> {
    let (s, a) = keyword("library")(s)?;
    let (s, b) = library_identifier(s)?;
    let (s, c) = list(symbol(","), file_path_spec)(s)?;
    let (s, d) = opt(pair(keyword("-incdir"), list(symbol(","), file_path_spec)))(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        LibraryDeclaration {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[parser]
pub(crate) fn include_statement(s: Span) -> IResult<Span, IncludeStatement> {
    let (s, a) = keyword("include")(s)?;
    let (s, b) = file_path_spec(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((s, IncludeStatement { nodes: (a, b, c) }))
}

//TODO support non literal path
#[parser]
pub(crate) fn file_path_spec(s: Span) -> IResult<Span, FilePathSpec> {
    let (s, a) = string_literal(s)?;
    Ok((s, FilePathSpec { nodes: (a,) }))
}

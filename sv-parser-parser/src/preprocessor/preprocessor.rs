use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
#[packrat_parser]
pub(crate) fn preprocessor_text(s: Span) -> IResult<Span, PreprocessorText> {
    let (s, a) = many0(source_description)(s)?;
    Ok((s, PreprocessorText { nodes: (a,) }))
}

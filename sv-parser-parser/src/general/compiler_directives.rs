use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
#[packrat_parser]
pub(crate) fn compiler_directive(s: Span) -> IResult<Span, CompilerDirective> {
    alt((
        map(resetall_compiler_directive, |x| {
            CompilerDirective::ResetallCompilerDirective(Box::new(x))
        }),
        map(text_macro_definition, |x| {
            CompilerDirective::TextMacroDefinition(Box::new(x))
        }),
        map(undefine_compiler_directive, |x| {
            CompilerDirective::UndefineCompilerDirective(Box::new(x))
        }),
        map(undefineall_compiler_directive, |x| {
            CompilerDirective::UndefineallCompilerDirective(Box::new(x))
        }),
        map(timescale_compiler_directive, |x| {
            CompilerDirective::TimescaleCompilerDirective(Box::new(x))
        }),
        map(default_nettype_compiler_directive, |x| {
            CompilerDirective::DefaultNettypeCompilerDirective(Box::new(x))
        }),
        map(unconnected_drive_compiler_directive, |x| {
            CompilerDirective::UnconnectedDriveCompilerDirective(Box::new(x))
        }),
        map(nounconnected_drive_compiler_directive, |x| {
            CompilerDirective::NounconnectedDriveCompilerDirective(Box::new(x))
        }),
        map(celldefine_compiler_directive, |x| {
            CompilerDirective::CelldefineDriveCompilerDirective(Box::new(x))
        }),
        map(endcelldefine_compiler_directive, |x| {
            CompilerDirective::EndcelldefineDriveCompilerDirective(Box::new(x))
        }),
        map(pragma, |x| CompilerDirective::Pragma(Box::new(x))),
        map(line_compiler_directive, |x| {
            CompilerDirective::LineCompilerDirective(Box::new(x))
        }),
        map(keywords_directive, |x| {
            CompilerDirective::KeywordsDirective(Box::new(x))
        }),
        map(endkeywords_directive, |x| {
            CompilerDirective::EndkeywordsDirective(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn resetall_compiler_directive(s: Span) -> IResult<Span, ResetallCompilerDirective> {
    let (s, a) = symbol("`")(s)?;
    let (s, b) = keyword("resetall")(s)?;
    Ok((s, ResetallCompilerDirective { nodes: (a, b) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn text_macro_definition(s: Span) -> IResult<Span, TextMacroDefinition> {
    let (s, a) = symbol("`")(s)?;
    let (s, b) = keyword("define")(s)?;
    let (s, c) = text_macro_name(s)?;
    let (s, d) = opt(macro_text)(s)?;
    Ok((
        s,
        TextMacroDefinition {
            nodes: (a, b, c, d),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn text_macro_name(s: Span) -> IResult<Span, TextMacroName> {
    let (s, a) = text_macro_identifier(s)?;
    let (s, b) = opt(paren(list_of_formal_arguments))(s)?;
    Ok((s, TextMacroName { nodes: (a, b) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn list_of_formal_arguments(s: Span) -> IResult<Span, ListOfFormalArguments> {
    let (s, a) = list(symbol(","), formal_argument)(s)?;
    Ok((s, ListOfFormalArguments { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn formal_argument(s: Span) -> IResult<Span, FormalArgument> {
    let (s, a) = simple_identifier(s)?;
    let (s, b) = opt(pair(symbol("="), default_text))(s)?;
    Ok((s, FormalArgument { nodes: (a, b) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn text_macro_identifier(s: Span) -> IResult<Span, TextMacroIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, TextMacroIdentifier { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn macro_text(s: Span) -> IResult<Span, MacroText> {
    let (s, a) = many1(alt((tag("\\\n"), tag("\\"), is_not("\\\n"))))(s)?;

    let mut ret = None;
    for x in a {
        ret = if let Some(ret) = ret {
            Some(concat(ret, x).unwrap())
        } else {
            Some(x)
        }
    }
    let a = ret.unwrap();
    Ok((
        s,
        MacroText {
            nodes: (into_locate(a),),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn default_text(s: Span) -> IResult<Span, DefaultText> {
    let (s, a) = is_not(",)")(s)?;
    Ok((
        s,
        DefaultText {
            nodes: (into_locate(a),),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn undefine_compiler_directive(s: Span) -> IResult<Span, UndefineCompilerDirective> {
    let (s, a) = symbol("`")(s)?;
    let (s, b) = keyword("undef")(s)?;
    let (s, c) = text_macro_identifier(s)?;
    Ok((s, UndefineCompilerDirective { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn undefineall_compiler_directive(
    s: Span,
) -> IResult<Span, UndefineallCompilerDirective> {
    let (s, a) = symbol("`")(s)?;
    let (s, b) = keyword("undefineall")(s)?;
    Ok((s, UndefineallCompilerDirective { nodes: (a, b) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn timescale_compiler_directive(s: Span) -> IResult<Span, TimescaleCompilerDirective> {
    let (s, a) = symbol("`")(s)?;
    let (s, b) = keyword("timescale")(s)?;
    let (s, c) = time_literal(s)?;
    let (s, d) = symbol("/")(s)?;
    let (s, e) = time_literal(s)?;
    Ok((
        s,
        TimescaleCompilerDirective {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn default_nettype_compiler_directive(
    s: Span,
) -> IResult<Span, DefaultNettypeCompilerDirective> {
    let (s, a) = symbol("`")(s)?;
    let (s, b) = keyword("default_nettype")(s)?;
    let (s, c) = default_nettype_value(s)?;
    Ok((s, DefaultNettypeCompilerDirective { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn default_nettype_value(s: Span) -> IResult<Span, DefaultNettypeValue> {
    let (s, a) = alt((
        keyword("none"),
        keyword("tri0"),
        keyword("tri1"),
        keyword("trior"),
        keyword("trireg"),
        keyword("triwand"),
        keyword("tri"),
        keyword("uwire"),
        keyword("wand"),
        keyword("wire"),
        keyword("wor"),
    ))(s)?;
    Ok((s, DefaultNettypeValue { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn unconnected_drive_compiler_directive(
    s: Span,
) -> IResult<Span, UnconnectedDriveCompilerDirective> {
    let (s, a) = symbol("`")(s)?;
    let (s, b) = keyword("unconnected_drive")(s)?;
    let (s, c) = alt((keyword("pull0"), keyword("pull1")))(s)?;
    Ok((s, UnconnectedDriveCompilerDirective { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn nounconnected_drive_compiler_directive(
    s: Span,
) -> IResult<Span, NounconnectedDriveCompilerDirective> {
    let (s, a) = symbol("`")(s)?;
    let (s, b) = keyword("nounconnected_drive")(s)?;
    Ok((s, NounconnectedDriveCompilerDirective { nodes: (a, b) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn celldefine_compiler_directive(
    s: Span,
) -> IResult<Span, CelldefineDriveCompilerDirective> {
    let (s, a) = symbol("`")(s)?;
    let (s, b) = keyword("celldefine")(s)?;
    Ok((s, CelldefineDriveCompilerDirective { nodes: (a, b) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn endcelldefine_compiler_directive(
    s: Span,
) -> IResult<Span, EndcelldefineDriveCompilerDirective> {
    let (s, a) = symbol("`")(s)?;
    let (s, b) = keyword("endcelldefine")(s)?;
    Ok((s, EndcelldefineDriveCompilerDirective { nodes: (a, b) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn pragma(s: Span) -> IResult<Span, Pragma> {
    let (s, a) = symbol("`")(s)?;
    let (s, b) = keyword("pragma")(s)?;
    let (s, c) = pragma_name(s)?;
    let (s, d) = opt(list(symbol(","), pragma_expression))(s)?;
    Ok((
        s,
        Pragma {
            nodes: (a, b, c, d),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn pragma_name(s: Span) -> IResult<Span, PragmaName> {
    let (s, a) = simple_identifier(s)?;
    Ok((s, PragmaName { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn pragma_expression(s: Span) -> IResult<Span, PragmaExpression> {
    alt((
        pragma_expression_assignment,
        map(pragma_keyword, |x| {
            PragmaExpression::PragmaKeyword(Box::new(x))
        }),
        map(pragma_value, |x| PragmaExpression::PragmaValue(Box::new(x))),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn pragma_expression_assignment(s: Span) -> IResult<Span, PragmaExpression> {
    let (s, a) = pragma_keyword(s)?;
    let (s, b) = symbol("=")(s)?;
    let (s, c) = pragma_value(s)?;
    Ok((
        s,
        PragmaExpression::Assignment(Box::new(PragmaExpressionAssignment { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn pragma_value(s: Span) -> IResult<Span, PragmaValue> {
    alt((
        pragma_value_paren,
        map(number, |x| PragmaValue::Number(Box::new(x))),
        map(string_literal, |x| PragmaValue::StringLiteral(Box::new(x))),
        map(identifier_pragma, |x| PragmaValue::Identifier(Box::new(x))),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn pragma_value_paren(s: Span) -> IResult<Span, PragmaValue> {
    let (s, a) = paren(list(symbol(","), pragma_expression))(s)?;
    Ok((
        s,
        PragmaValue::Paren(Box::new(PragmaValueParen { nodes: (a,) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn pragma_keyword(s: Span) -> IResult<Span, PragmaKeyword> {
    let (s, a) = simple_identifier_pragma(s)?;
    Ok((s, PragmaKeyword { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn identifier_pragma(s: Span) -> IResult<Span, Identifier> {
    alt((
        map(escaped_identifier, |x| {
            Identifier::EscapedIdentifier(Box::new(x))
        }),
        map(simple_identifier_pragma, |x| {
            Identifier::SimpleIdentifier(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn simple_identifier_pragma(s: Span) -> IResult<Span, SimpleIdentifier> {
    let (s, a) = ws(simple_identifier_pragma_impl)(s)?;
    Ok((s, SimpleIdentifier { nodes: a }))
}

#[tracable_parser]
pub(crate) fn simple_identifier_pragma_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = is_a(AZ_)(s)?;
    let (s, b) = opt(is_a(AZ09_DOLLAR))(s)?;
    let a = if let Some(b) = b {
        concat(a, b).unwrap()
    } else {
        a
    };
    Ok((s, into_locate(a)))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn line_compiler_directive(s: Span) -> IResult<Span, LineCompilerDirective> {
    let (s, a) = symbol("`")(s)?;
    let (s, b) = keyword("line")(s)?;
    let (s, c) = number(s)?;
    let (s, d) = string_literal(s)?;
    let (s, e) = level(s)?;
    Ok((
        s,
        LineCompilerDirective {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn level(s: Span) -> IResult<Span, Level> {
    let (s, a) = alt((symbol("0"), symbol("1"), symbol("2")))(s)?;
    Ok((s, Level { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn keywords_directive(s: Span) -> IResult<Span, KeywordsDirective> {
    let (s, a) = symbol("`")(s)?;
    let (s, b) = keyword("begin_keywords")(s)?;
    let (s, c) = symbol("\"")(s)?;
    let (s, d) = version_specifier(s)?;
    let (s, e) = symbol("\"")(s)?;
    Ok((
        s,
        KeywordsDirective {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn version_specifier(s: Span) -> IResult<Span, VersionSpecifier> {
    let (s, a) = alt((
        map(keyword("1800-2017"), |x| {
            begin_keywords("1800-2017");
            x
        }),
        map(keyword("1800-2012"), |x| {
            begin_keywords("1800-2012");
            x
        }),
        map(keyword("1800-2009"), |x| {
            begin_keywords("1800-2009");
            x
        }),
        map(keyword("1800-2005"), |x| {
            begin_keywords("1800-2005");
            x
        }),
        map(keyword("1364-2005"), |x| {
            begin_keywords("1364-2005");
            x
        }),
        map(keyword("1364-2001"), |x| {
            begin_keywords("1364-2001");
            x
        }),
        map(keyword("1364-2001-noconfig"), |x| {
            begin_keywords("1364-2001-noconfig");
            x
        }),
        map(keyword("1364-1995"), |x| {
            begin_keywords("1364-1995");
            x
        }),
    ))(s)?;
    Ok((s, VersionSpecifier { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn endkeywords_directive(s: Span) -> IResult<Span, EndkeywordsDirective> {
    let (s, a) = symbol("`")(s)?;
    let (s, b) = keyword("end_keywords")(s)?;
    end_keywords();
    Ok((s, EndkeywordsDirective { nodes: (a, b) }))
}

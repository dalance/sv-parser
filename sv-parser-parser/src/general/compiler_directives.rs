use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
#[packrat_parser]
pub(crate) fn compiler_directive(s: Span) -> IResult<Span, CompilerDirective> {
    begin_directive();
    let ret = alt((
        map(resetall_compiler_directive, |x| {
            CompilerDirective::ResetallCompilerDirective(Box::new(x))
        }),
        map(include_compiler_directive, |x| {
            CompilerDirective::IncludeCompilerDirective(Box::new(x))
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
        map(conditional_compiler_directive, |x| {
            CompilerDirective::ConditionalCompilerDirective(Box::new(x))
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
        map(position_compiler_directive, |x| {
            CompilerDirective::PositionCompilerDirective(Box::new(x))
        }),
        map(keywords_directive, |x| {
            CompilerDirective::KeywordsDirective(Box::new(x))
        }),
        map(endkeywords_directive, |x| {
            CompilerDirective::EndkeywordsDirective(Box::new(x))
        }),
        map(text_macro_usage, |x| {
            CompilerDirective::TextMacroUsage(Box::new(x))
        }),
    ))(s);
    end_directive();
    ret
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn compiler_directive_without_resetall(s: Span) -> IResult<Span, CompilerDirective> {
    begin_directive();
    let ret = alt((
        map(include_compiler_directive, |x| {
            CompilerDirective::IncludeCompilerDirective(Box::new(x))
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
        map(conditional_compiler_directive, |x| {
            CompilerDirective::ConditionalCompilerDirective(Box::new(x))
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
        map(position_compiler_directive, |x| {
            CompilerDirective::PositionCompilerDirective(Box::new(x))
        }),
        map(keywords_directive, |x| {
            CompilerDirective::KeywordsDirective(Box::new(x))
        }),
        map(endkeywords_directive, |x| {
            CompilerDirective::EndkeywordsDirective(Box::new(x))
        }),
        map(text_macro_usage, |x| {
            CompilerDirective::TextMacroUsage(Box::new(x))
        }),
    ))(s);
    end_directive();
    ret
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
pub(crate) fn include_compiler_directive(s: Span) -> IResult<Span, IncludeCompilerDirective> {
    alt((
        include_compiler_directive_double_quote,
        include_compiler_directive_angle_bracket,
        include_compiler_directive_text_macro_usage,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn include_compiler_directive_double_quote(
    s: Span,
) -> IResult<Span, IncludeCompilerDirective> {
    let (s, a) = symbol("`")(s)?;
    let (s, b) = keyword("include")(s)?;
    let (s, c) = string_literal(s)?;
    Ok((
        s,
        IncludeCompilerDirective::DoubleQuote(Box::new(IncludeCompilerDirectiveDoubleQuote {
            nodes: (a, b, c),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn include_compiler_directive_angle_bracket(
    s: Span,
) -> IResult<Span, IncludeCompilerDirective> {
    let (s, a) = symbol("`")(s)?;
    let (s, b) = keyword("include")(s)?;
    let (s, c) = angle_bracket_literal(s)?;
    Ok((
        s,
        IncludeCompilerDirective::AngleBracket(Box::new(IncludeCompilerDirectiveAngleBracket {
            nodes: (a, b, c),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn include_compiler_directive_text_macro_usage(
    s: Span,
) -> IResult<Span, IncludeCompilerDirective> {
    let (s, a) = symbol("`")(s)?;
    let (s, b) = keyword("include")(s)?;
    let (s, c) = text_macro_usage(s)?;
    Ok((
        s,
        IncludeCompilerDirective::TextMacroUsage(Box::new(
            IncludeCompilerDirectiveTextMacroUsage { nodes: (a, b, c) },
        )),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn angle_bracket_literal(s: Span) -> IResult<Span, AngleBracketLiteral> {
    let (s, a) = ws(angle_bracket_literal_impl)(s)?;
    Ok((s, AngleBracketLiteral { nodes: a }))
}

#[tracable_parser]
pub(crate) fn angle_bracket_literal_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = tag("<")(s)?;
    let (s, b) = is_not(">")(s)?;
    let (s, c) = tag(">")(s)?;

    let a = concat(a, b).unwrap();
    let a = concat(a, c).unwrap();

    Ok((s, into_locate(a)))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn text_macro_definition(s: Span) -> IResult<Span, TextMacroDefinition> {
    let (s, a) = symbol("`")(s)?;
    let (s, b) = keyword("define")(s)?;
    begin_keywords("directive");
    let (s, c) = text_macro_name(s)?;
    end_keywords();
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
    let (s, a) = text_macro_identifier_exact(s)?;
    let (s, b) = opt(paren_exact(list_of_formal_arguments))(s)?;
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
pub(crate) fn text_macro_identifier_exact(s: Span) -> IResult<Span, TextMacroIdentifier> {
    let (s, a) = identifier_exact(s)?;
    Ok((s, TextMacroIdentifier { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn macro_text(s: Span) -> IResult<Span, MacroText> {
    let (s, a) = many1(alt((
        tag("\\\n"),
        tag("\\\r\n"),
        tag("\\\r"),
        tag("\\"),
        is_not("\\\r\n"),
    )))(s)?;

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
    let (s, a) = define_argument(s)?;
    Ok((
        s,
        DefaultText {
            nodes: (into_locate(a),),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn text_macro_usage(s: Span) -> IResult<Span, TextMacroUsage> {
    let (s, a) = symbol("`")(s)?;
    begin_keywords("directive");
    let (s, b) = text_macro_identifier(s)?;
    end_keywords();
    let (s, c) = opt(paren(list_of_actual_arguments))(s)?;
    Ok((s, TextMacroUsage { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn list_of_actual_arguments(s: Span) -> IResult<Span, ListOfActualArguments> {
    let (s, a) = list(symbol(","), opt(actual_argument))(s)?;
    Ok((s, ListOfActualArguments { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn actual_argument(s: Span) -> IResult<Span, ActualArgument> {
    let (s, a) = define_argument(s)?;
    Ok((
        s,
        ActualArgument {
            nodes: (into_locate(a),),
        },
    ))
}

#[tracable_parser]
pub(crate) fn define_argument(s: Span) -> IResult<Span, Span> {
    let (s, a) = many1(alt((
        is_not(",([{}])\""),
        define_argument_str,
        define_argument_paren,
        define_argument_bracket,
        define_argument_brace,
    )))(s)?;
    let mut ret = None;
    for x in a {
        ret = if let Some(ret) = ret {
            Some(concat(ret, x).unwrap())
        } else {
            Some(x)
        }
    }
    let a = ret.unwrap();
    Ok((s, a))
}

#[tracable_parser]
pub(crate) fn define_argument_inner(s: Span) -> IResult<Span, Span> {
    let (s, a) = many1(alt((
        is_not("([{}])\""),
        define_argument_str,
        define_argument_paren,
        define_argument_bracket,
        define_argument_brace,
    )))(s)?;
    let mut ret = None;
    for x in a {
        ret = if let Some(ret) = ret {
            Some(concat(ret, x).unwrap())
        } else {
            Some(x)
        }
    }
    let a = ret.unwrap();
    Ok((s, a))
}

#[tracable_parser]
pub(crate) fn define_argument_str(s: Span) -> IResult<Span, Span> {
    let (s, (a, b, c)) = triple(tag("\""), opt(is_not("\"")), tag("\""))(s)?;
    let a = if let Some(b) = b {
        concat(concat(a, b).unwrap(), c).unwrap()
    } else {
        concat(a, c).unwrap()
    };
    Ok((s, a))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn define_argument_paren(s: Span) -> IResult<Span, Span> {
    let (s, (a, b, c)) = triple(tag("("), opt(define_argument_inner), tag(")"))(s)?;
    let a = if let Some(b) = b {
        concat(concat(a, b).unwrap(), c).unwrap()
    } else {
        concat(a, c).unwrap()
    };
    Ok((s, a))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn define_argument_bracket(s: Span) -> IResult<Span, Span> {
    let (s, (a, b, c)) = triple(tag("["), opt(define_argument_inner), tag("]"))(s)?;
    let a = if let Some(b) = b {
        concat(concat(a, b).unwrap(), c).unwrap()
    } else {
        concat(a, c).unwrap()
    };
    Ok((s, a))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn define_argument_brace(s: Span) -> IResult<Span, Span> {
    let (s, (a, b, c)) = triple(tag("{"), opt(define_argument_inner), tag("}"))(s)?;
    let a = if let Some(b) = b {
        concat(concat(a, b).unwrap(), c).unwrap()
    } else {
        concat(a, c).unwrap()
    };
    Ok((s, a))
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
pub(crate) fn conditional_compiler_directive(
    s: Span,
) -> IResult<Span, ConditionalCompilerDirective> {
    alt((
        map(ifdef_directive, |x| {
            ConditionalCompilerDirective::IfdefDirective(Box::new(x))
        }),
        map(ifndef_directive, |x| {
            ConditionalCompilerDirective::IfndefDirective(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn ifdef_directive(s: Span) -> IResult<Span, IfdefDirective> {
    let (s, a) = symbol("`")(s)?;
    let (s, b) = keyword("ifdef")(s)?;
    let (s, c) = text_macro_identifier(s)?;
    let (s, d) = ifdef_group_of_lines(s)?;
    let (s, e) = many0(tuple((
        symbol("`"),
        keyword("elsif"),
        text_macro_identifier,
        elsif_group_of_lines,
    )))(s)?;
    let (s, f) = opt(tuple((symbol("`"), keyword("else"), else_group_of_lines)))(s)?;
    let (s, g) = symbol("`")(s)?;
    let (s, h) = keyword("endif")(s)?;
    Ok((
        s,
        IfdefDirective {
            nodes: (a, b, c, d, e, f, g, h),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn ifndef_directive(s: Span) -> IResult<Span, IfndefDirective> {
    let (s, a) = symbol("`")(s)?;
    let (s, b) = keyword("ifndef")(s)?;
    let (s, c) = text_macro_identifier(s)?;
    let (s, d) = ifndef_group_of_lines(s)?;
    let (s, e) = many0(tuple((
        symbol("`"),
        keyword("elsif"),
        text_macro_identifier,
        elsif_group_of_lines,
    )))(s)?;
    let (s, f) = opt(tuple((symbol("`"), keyword("else"), else_group_of_lines)))(s)?;
    let (s, g) = symbol("`")(s)?;
    let (s, h) = keyword("endif")(s)?;
    Ok((
        s,
        IfndefDirective {
            nodes: (a, b, c, d, e, f, g, h),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn ifdef_group_of_lines(s: Span) -> IResult<Span, IfdefGroupOfLines> {
    let (s, a) = many0(preceded(
        peek(not(alt((tag("`elsif"), tag("`else"), tag("`endif"))))),
        source_description,
    ))(s)?;
    Ok((s, IfdefGroupOfLines { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn ifndef_group_of_lines(s: Span) -> IResult<Span, IfndefGroupOfLines> {
    let (s, a) = many0(preceded(
        peek(not(alt((tag("`elsif"), tag("`else"), tag("`endif"))))),
        source_description,
    ))(s)?;
    Ok((s, IfndefGroupOfLines { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn elsif_group_of_lines(s: Span) -> IResult<Span, ElsifGroupOfLines> {
    let (s, a) = many0(preceded(
        peek(not(alt((tag("`elsif"), tag("`else"), tag("`endif"))))),
        source_description,
    ))(s)?;
    Ok((s, ElsifGroupOfLines { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn else_group_of_lines(s: Span) -> IResult<Span, ElseGroupOfLines> {
    let (s, a) = many0(preceded(peek(not(tag("`endif"))), source_description))(s)?;
    Ok((s, ElseGroupOfLines { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn source_description(s: Span) -> IResult<Span, SourceDescription> {
    alt((
        map(comment, |x| SourceDescription::Comment(Box::new(x))),
        map(string_literal, |x| {
            SourceDescription::StringLiteral(Box::new(x))
        }),
        map(escaped_identifier, |x| {
            SourceDescription::EscapedIdentifier(Box::new(x))
        }),
        source_description_not_directive,
        map(compiler_directive, |x| {
            SourceDescription::CompilerDirective(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn source_description_not_directive(s: Span) -> IResult<Span, SourceDescription> {
    let (s, a) = many1(alt((
        is_not("`/\"\\"),
        terminated(tag("/"), peek(not(alt((tag("/"), tag("*")))))),
    )))(s)?;

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
        SourceDescription::NotDirective(Box::new(SourceDescriptionNotDirective {
            nodes: (into_locate(a),),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn timescale_compiler_directive(s: Span) -> IResult<Span, TimescaleCompilerDirective> {
    let (s, a) = symbol("`")(s)?;
    let (s, b) = keyword("timescale")(s)?;
    let (s, c) = unsigned_number(s)?;
    let (s, d) = time_unit(s)?;
    let (s, e) = symbol("/")(s)?;
    let (s, f) = unsigned_number(s)?;
    let (s, g) = time_unit(s)?;
    Ok((
        s,
        TimescaleCompilerDirective {
            nodes: (a, b, c, d, e, f, g),
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
        keyword("triand"),
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
pub(crate) fn position_compiler_directive(s: Span) -> IResult<Span, PositionCompilerDirective> {
    let (s, a) = symbol("`")(s)?;
    let (s, b) = alt((keyword("__FILE__"), keyword("__LINE__")))(s)?;
    Ok((s, PositionCompilerDirective { nodes: (a, b) }))
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
        map(keyword("1364-2001-noconfig"), |x| {
            begin_keywords("1364-2001-noconfig");
            x
        }),
        map(keyword("1364-2001"), |x| {
            begin_keywords("1364-2001");
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

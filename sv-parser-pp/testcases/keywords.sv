// IEEE1800-2017 Clause 22.14
// A pair of directives, `begin_keywords and `end_keywords, can be used to
// specify what identifiers are reserved as keywords within a block of source
// code, based on a specific version of IEEE Std 1364 or IEEE Std 1800.
// The `begin_keywords and `end_keywords directives only specify the set of
// identifiers that are reserved as keywords. The directives do not affect the
// semantics, tokens, and other aspects of the SystemVerilog language.
// The `begin_keywords and `end_keywords directives can only be specified
// outside a design element. The `begin_keywords directive affects all source
// code that follows the directive, even across source code file boundaries,
// until the matching `end_keywords directive or the end of the compilation
// unit. The results of these directives are not affected by the `resetall
// directive.
`begin_keywords "1800-2017"
`end_keywords
`begin_keywords "1800-2012"
`end_keywords
`begin_keywords "1800-2009"
`end_keywords
`begin_keywords "1800-2005"
`end_keywords
`begin_keywords "1364-2005"
`end_keywords
`begin_keywords "1364-2001"
`end_keywords
`begin_keywords "1364-2001-noconfig"
`end_keywords
`begin_keywords "1364-1995"
`end_keywords
// The `begin_keywords `end_keywords directive pair can be nested. Each nested
// pair is stacked so that when an `end_keywords directive is encountered, the
// implementation returns to using the version_ specifier that was in effect
// prior to the matching `begin_keywords directive.
`begin_keywords "1800-2017"
`begin_keywords "1800-2012"
`begin_keywords "1800-2009"
`begin_keywords "1800-2005"
`begin_keywords "1364-2005"
`begin_keywords "1364-2001"
`begin_keywords "1364-2001-noconfig"
`begin_keywords "1364-1995"
`end_keywords
`end_keywords
`end_keywords
`end_keywords
`end_keywords
`end_keywords
`end_keywords
`end_keywords
// This file should be emitted from the preprocessor unchanged.

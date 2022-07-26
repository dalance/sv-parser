// IEEE1800-2017 Clause 22.8
// The directive `default_nettype controls the net type created for implicit
// net declarations. It can be used only outside design elements. Multiple
// `default_nettype directives are allowed. The latest occurrence of this
// directive in the source controls the type of nets that will be implicitly
// declared.
// When no `default_nettype directive is present or if the `resetall directive
// is specified, implicit nets are of type wire. When the `default_nettype is
// set to none, all nets shall be explicitly declared. If a net is not
// explicitly declared, an error is generated.
`default_nettype wire // Comment immmediately after keyword+space
`default_nettype tri
`default_nettype tri0
`default_nettype tri1
`default_nettype wand
`default_nettype triand
`default_nettype wor
`default_nettype trior
`default_nettype trireg
`default_nettype uwire
`default_nettype none// Comment immmediately after keyword
// This file should be emitted from the preprocessor unchanged.

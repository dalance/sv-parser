// IEEE1800-2017 Clause 22.3
// When `resetall compiler directive is encountered during compilation, all
// compiler directives are set to the default values. This is useful for
// ensuring that only directives that are desired in compiling a particular
// source file are active.
// The recommended usage is to place `resetall at the beginning of each source
// text file, followed immediately by the directives desired in the file.
// It shall be illegal for the `resetall directive to be specified within
// a design element.
// Not all compiler directives have a default value (e.g., `define and
// `include). Directives that do not have a default are not affected by
// `resetall.
`resetall // Comment
`resetall// Comment
`resetall
// This file should be emitted from the preprocessor unchanged.

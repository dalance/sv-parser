// IEEE1800-2017 Clause 22.5.2
// The directive `undef shall undefine the specified text macro if previously
// defined by a `define compiler directive within the compilation unit. An
// attempt to undefine a text macro that was not previously defined using a
// `define compiler directive can issue a warning.
`undef FOO
`undef FOO// Comment
`undef FOO // Comment

`define FOO foo
`ifdef FOO
// AAA
// This block SHOULD be emitted from the preprocessor.
`endif
`ifndef FOO
// AAA
// This block should NOT be emitted from the preprocessor.
`endif

`undef FOO
`ifdef FOO
// BBB
// This block should NOT be emitted from the preprocessor.
`endif
`ifndef FOO
// BBB
// This block SHOULD be emitted from the preprocessor.
`endif

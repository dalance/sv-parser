// IEEE1800-2017 Clause 22.5.3
// The directive `undefineall directive shall undefine all text macros
// previously defined by `define compiler directives within the compilation
// unit. This directive takes no argument and may appear anywhere in the source
// description.
`undefineall
`undefineall// Comment
`undefineall // Comment

`define FOO foo
`define BAR bar
`ifdef FOO
// AAA
// This block SHOULD be emitted from the preprocessor.
`endif
`ifndef FOO
// AAA
// This block should NOT be emitted from the preprocessor.
`endif
`ifdef BAR
// BBB
// This block SHOULD be emitted from the preprocessor.
`endif
`ifndef BAR
// BBB
// This block should NOT be emitted from the preprocessor.
`endif

`undefineall
`ifdef FOO
// CCC
// This block should NOT be emitted from the preprocessor.
`endif
`ifndef FOO
// CCC
// This block SHOULD be emitted from the preprocessor.
`endif
`ifdef BAR
// DDD
// This block should NOT be emitted from the preprocessor.
`endif
`ifndef BAR
// DDD
// This block SHOULD be emitted from the preprocessor.
`endif

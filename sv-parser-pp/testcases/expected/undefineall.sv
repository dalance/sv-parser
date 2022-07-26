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
// AAA
// This block SHOULD be emitted from the preprocessor.


// BBB
// This block SHOULD be emitted from the preprocessor.



`undefineall

// CCC
// This block SHOULD be emitted from the preprocessor.


// DDD
// This block SHOULD be emitted from the preprocessor.


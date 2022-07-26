// IEEE1800-2017 Clause 22.12
// The `line compiler directive can be used to specify the original source code
// line number and file name.
// This allows the location in the original file to be maintained if another
// process modifies the source. After the new line number and file name are
// specified, the compiler can correctly refer to the original source location.
// However, a tool is not required to produce `line directives. These
// directives are not intended to be inserted manually into the code, although
// they can be.
// The compiler shall maintain the current line number and file name of the
// file being compiled. The `line directive shall set the line number and file
// name of the following line to those specified in the directive.
// The directive can be specified anywhere within the SystemVerilog source
// description. However, only white space may appear on the same line as the
// `line directive. Comments are not allowed on the same line as a `line
// directive. All parameters in the `line directive are required. The results
// of this directive are not affected by the `resetall directive.
//
// The number parameter shall be a positive integer that specifies the new line
// number of the following text line. The filename parameter shall be a string
// literal that is treated as the new name of the file. The filename can also
// be a full or relative path name. The level parameter shall be 0, 1, or 2.
// The value 1 indicates that the following line is the first line after an
// include file has been entered. The value 2 indicates that the following
// line is the first line after an include file has been exited. The value
// 0 indicates any other line.

`line 3 "orig.v" 2
// This line is line 3 of orig.v after exiting include file

`line 999 "foo.sv" 2
`line 888 "foo.sv" 1
`line 777 "foo.sv" 0
// This file should be emitted from the preprocessor unchanged.

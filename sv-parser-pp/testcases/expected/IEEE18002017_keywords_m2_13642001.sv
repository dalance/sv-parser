
`begin_keywords "1364-2001"
module m2 ();
  // "logic" is NOT a reserved keyword in IEEE1364-2001.
  // This module should pass both the preprocessor, AND the main parser.
  reg [63:0] logic;
endmodule
`end_keywords

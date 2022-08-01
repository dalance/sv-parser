
`begin_keywords "1800-2005"
module m2 ();
  // "logic" IS a reserved keyword in IEEE1800-2005.
  // This module should pass both the preprocessor, but NOT the main parser.
  reg [63:0] logic;
endmodule
`end_keywords

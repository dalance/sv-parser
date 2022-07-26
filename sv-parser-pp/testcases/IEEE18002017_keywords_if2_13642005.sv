
`begin_keywords "1364-2005" // use IEEE Std 1364-2005 Verilog keywords
interface if2 (); // ERROR: "interface" is not a keyword in 1364-2005
  // This interface should pass the preprocessor, but not the main parser
  // because the identifiers `interface` and `endinterface` are not reserved
  // keywords in IEEE1364-2005.
endinterface // ERROR: "endinterface" is not a keyword in 1364-2005
`end_keywords

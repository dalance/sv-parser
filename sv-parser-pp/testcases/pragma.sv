// IEEE1800-2017 Clause 22.11
// The `pragma directive is a structured specification that alters
// interpretation of the SystemVerilog source. The specification introduced by
// this directive is referred to as a pragma. The effect of pragmas other than
// those specified in this standard is implementation-specific.
`pragma foo
`pragma foo bar
`pragma foo bar,baz
`pragma foo bar, baz
// The reset and resetall pragmas shall restore the default values and state of
// pragma_keywords associated with the affected pragmas. These default values
// shall be the values that the tool defines before any SystemVerilog text has
// been processed. The reset pragma shall reset the state for all pragma_names
// that appear as pragma_keywords in the directive. The resetall pragma shall
// reset the state of all pragma_names recognized by the implementation.
`pragma reset bar
`pragma reset bar,baz
`pragma reset bar, baz

// Protected envelopes specify a region of text that shall be transformed prior
// to analysis by the source language processor. These regions of text are
// structured to provide the source language processor with the specification
// of the cryptographic algorithm, key, envelope attributes, and textual design
// data.
// The following example shows the use of the protect pragma to specify
// encryption of design data. The encryption method is a simple substitution
// cipher where each alphabetic character is replaced with the 13th character
// in alphabetic sequence, commonly referred to as "rot13." Nonalphabetic
// characters are not substituted. The following design data contain an
// encryption envelope that specifies the desired protection.
module secret (a, b);
  input a;
  output b;
`pragma protect encoding=(enctype="raw")
`pragma protect data_method="x-caesar", data_keyname="rot13", begin
`pragma protect runtime_license=(library="lic.so",feature="runSecret",entry="chk", match=42)
  logic b;
  initial begin
    b = 0;
  end
  always begin
    #5 b = a;
  end
`pragma protect end
endmodule
// This file should be emitted from the preprocessor unchanged.

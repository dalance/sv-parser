// __LINE__ = `__LINE__

`ifdef __LINE__
// This block SHOULD be emitted from the preprocessor.
`elsif UNDEFINED
// NOT emitted.
`endif

`ifndef __LINE__
// This block should NOT be emitted from the preprocessor.
// However, following (conditional) definition should make it through the
// preprocessor parsing stage without error.
`define __LINE__ -1
`elsif UNDEFINED
// Emitted instead.
`endif

// The following define should have no effect.
`define __LINE__ -2

// The following undef should have no effect.
`undef __LINE__

module M;
  initial
    if (`__LINE__ == 28)      // Should be "26 == 28".
       $display("PASS");
    else if (`__LINE__ == 28) // Should be "28 == 28".
       $display("FAIL");
endmodule

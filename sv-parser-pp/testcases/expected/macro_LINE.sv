// __LINE__ = `__LINE__

// This block SHOULD be emitted from the preprocessor.




// The following define should have no effect.
`define __LINE__ -2

// The following undef should have no effect.
`undef __LINE__

module M;
  initial
    if (26 == 28)      // Should be "26 == 28".
       $display("PASS");
    else if (28 == 28) // Should be "28 == 28".
       $display("FAIL");
endmodule

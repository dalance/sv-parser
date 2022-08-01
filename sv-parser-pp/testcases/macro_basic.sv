`define A aaa
module M;
`A#() a0 (.*); // No trailing whitespace.
`A #() a1 (.*); // Trailing 1 space.
`A  #() a2 (.*); // Trailing 2 spaces.
endmodule

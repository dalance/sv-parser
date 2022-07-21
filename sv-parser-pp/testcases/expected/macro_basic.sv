`define A aaa
module M;
aaa#() a0 (.*); // No trailing whitespace.
aaa #() a1 (.*); // Trailing 1 space.
aaa  #() a2 (.*); // Trailing 2 spaces.
endmodule

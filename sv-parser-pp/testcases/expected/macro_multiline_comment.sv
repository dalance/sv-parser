//                                  Leading whitespace on 4 lines.
//  initial \                       Space before line continuation.
//    begin\                        No space before line continuation.
//      $display(); // comment \    Continuation at end of comment.
//    end
// NOTE: Trailing whitespace on lines ending `initial ` and `$display(); `.

`define A \
  initial \
    begin\
      $display(); // comment \
    end

module M;
  initial 
    begin
      $display(); 
    end
endmodule

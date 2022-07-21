`define disp(clk, exp, msg) \
    always @(posedge clk) begin \
        if (!(exp)) begin \
            $display msg; \
        end \
    end \

module a ();

`disp(
    clk,
    !(a[i].b && c[i]),
    ("xxx(()[]]{}}}", a[i].b, c[i])
);

endmodule

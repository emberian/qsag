module qsag_ass2_add64 (
    input wire [63:0] a, b,
    input wire cin,
    output wire [63:0] sum,
    output wire cout
);
    assign {cout,sum} = {1'b0,a} + {1'b0,b} + 65'(cin);
endmodule

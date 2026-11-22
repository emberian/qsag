module add64_equiv(input wire [63:0] a, b, input wire cin, output wire equal);
    wire [64:0] result;
    qsag_ass2_add64 dut (.a(a), .b(b), .cin(cin), .cout(result[64]), .sum(result[63:0]));
    assign equal = result == ({1'b0,a} + {1'b0,b} + {64'b0,cin});
endmodule

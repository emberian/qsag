// FPGA implementation uses one clock and the native carry chain.
module qsag_ass2_ripple_cnt #(parameter int N = 20) (
    input wire clk, rst_n,
    output logic [N-1:0] q
);
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) q <= '0;
        else q <= q + 1'b1;
endmodule

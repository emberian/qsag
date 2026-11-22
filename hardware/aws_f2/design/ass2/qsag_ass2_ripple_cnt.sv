module qsag_ass2_ripple_cnt #(parameter int N = 20) (
    input wire clk, rst_n,
    output logic [N-1:0] q
);
    for (genvar k = 0; k < N; k++) begin : g_bit
        wire ck;
        if (k == 0) begin : g_first
            assign ck = clk;
        end else begin : g_next
            assign ck = ~q[k-1];
        end
        logic toggle;
        assign q[k] = toggle;
        always_ff @(posedge ck or negedge rst_n)
            if (!rst_n) toggle <= 1'b0;
            else toggle <= ~toggle;
    end
endmodule

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
`ifdef GF180_SRAM_MACRO
        wire d_in, q_out;
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__inv_1 u_inv (.I(q_out), .ZN(d_in));
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__dffrnq_1 u_ff (.CLK(ck), .D(d_in), .RN(rst_n), .Q(q_out));
        assign q[k] = q_out;
`else
        logic toggle;
        assign q[k] = toggle;
        always_ff @(posedge ck or negedge rst_n)
            if (!rst_n) toggle <= 1'b0;
            else toggle <= ~toggle;
`endif
    end
endmodule

// Explicit GF180MCU integrated clock-gated (`icgtp_2`) register primitive.
// Eliminates the 28.53 um^2/bit recirculation `mux2_1` overhead on GF180MCU (which has
// no native DFFE standard cell) while keeping <= 16 FFs per `icgtp_2` (no series clkbuf)
// for < 0.35 ns gated-clock insertion skew and clean 3-corner hold margin.
module qsag_ass2_cg_dff #(parameter int W = 64) (
    input  logic         clk,
    input  logic         rst_n,
    input  logic         en,
    input  logic [W-1:0] d,
    output logic [W-1:0] q
);
`ifdef GF180_SRAM_MACRO
    localparam int N_GRP = (W + 15) / 16;
    wire [N_GRP-1:0] gclk;
    for (genvar g = 0; g < N_GRP; g++) begin : g_icg
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__icgtp_2 u_icg (
            .CLK(clk), .E(en), .TE(1'b0), .Q(gclk[g])
        );
    end
    for (genvar i = 0; i < W; i++) begin : g_ff
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__dffrnq_1 u_ff (
            .CLK(gclk[i / 16]), .D(d[i]), .RN(rst_n), .Q(q[i])
        );
    end
`else
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) q <= '0;
        else if (en) q <= d;
    end
`endif
endmodule

// Clock-gated asynchronous-reset (`RN = rst_n`) register bank:
//   - Default (`KEEP_EN = 0`) exposes clean `$adffe` to Yosys `opt_dff` + `share` + `clockgate`
//     so redundant recirculation muxes are stripped automatically before `icgtp_2` insertion.
//   - `KEEP_EN = 1` (used on `u_instret`) preserves hierarchical `.en` net for 4-state GL probing.
module qsag_ass2_cg_dff #(parameter int W = 64, parameter bit KEEP_EN = 1'b0) (
    input  logic         clk,
    input  logic         rst_n,
    input  logic         en,
    input  logic [W-1:0] d,
    output logic [W-1:0] q
);
    generate
        if (KEEP_EN) begin : g_keep_en
`ifdef GF180_SRAM_MACRO
            localparam int N_GRP = (W + 31) / 32;
            wire [N_GRP-1:0] gclk;
            for (genvar g = 0; g < N_GRP; g++) begin : g_icg
                (* keep *) gf180mcu_fd_sc_mcu7t5v0__icgtp_2 u_icg (
                    .CLK(clk), .E(en), .TE(1'b0), .Q(gclk[g])
                );
            end
            for (genvar i = 0; i < W; i++) begin : g_ff
                (* keep *) gf180mcu_fd_sc_mcu7t5v0__dffrnq_1 u_ff (
                    .CLK(gclk[i / 32]), .D(d[i]), .RN(rst_n), .Q(q[i])
                );
            end
`else
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) q <= '0;
                else if (en) q <= d;
            end
`endif
        end else begin : g_auto
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) q <= '0;
                else if (en) q <= d;
            end
        end
    endgenerate
endmodule

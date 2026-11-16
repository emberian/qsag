// Dregg-180 (QSAG-NI-180) symmetric clockless 2-phase Sutherland bundled-data stages.
//
// GOTCHA #4 silicon fix:
//   * `qsag_mpipe_stage`    (ingress: 16-bit two-phase bundled data -> core domain)
//   * `qsag_mpipe_tx_stage` (egress:  core domain -> 8-bit two-phase bundled data with genuine
//                            AOI222 Muller C-element + 2-delay-cell data-before-REQ_OUT bundling!)
`default_nettype none
`timescale 1ps / 1ps

module qsag_muller_c (
    input  wire a,
    input  wire b,
    input  wire rst_n,
    output wire q
);
`ifdef QSAG_GF180_CELLS
    wire zn, rst;
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__inv_1    u_ri  (.I(rst_n), .ZN(rst));
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__aoi222_1 u_maj (.A1(a), .A2(b), .B1(a), .B2(q), .C1(b), .C2(q), .ZN(zn));
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__nor2_2   u_q   (.A1(zn), .A2(rst), .ZN(q));
`else
    logic qr;
    /* verilator lint_off LATCH */
    /* verilator lint_off COMBDLY */
    always_latch begin
        if (!rst_n) qr <= 1'b0;
        else if (a == b) qr <= a;
    end
    /* verilator lint_on COMBDLY */
    /* verilator lint_on LATCH */
    assign q = qr;
`endif
endmodule

// Ingress Sutherland capture stage (external REQ_IN -> ACK_OUT, core observes c_out).
// Uses 6 x dlya_1 bundling stages (~1.6 ns FF, ~2.7 ns TT, ~4.9 ns SS) to cover West-to-East
// cross-chip pad arrival skew across bidir[37], bidir[6:0], and bidir[18], plus non-dont_touch
// isolation buffers on external inputs to prevent RSZ-3006.
module qsag_mpipe_stage #(
    parameter int W = 16
) (
    input  wire         rst_n,
    input  wire         req_in,
    input  wire [W-1:0] din,
    output wire         ack_out,
    input  wire         taken,
    output wire         c_out,
    output wire [W-1:0] dout
);
    wire req_iso, taken_iso, rst_iso;
    qsag_iso_buf u_ireq (.a(req_in), .y(req_iso));
    qsag_iso_buf u_itak (.a(taken),  .y(taken_iso));
    qsag_iso_buf u_irst (.a(rst_n),  .y(rst_iso));

    wire ntaken, c, c_d, c_dn, c_a;
    qsag_clkinv   u_nt (.a(taken_iso), .y(ntaken));
    qsag_muller_c u_c  (.a(req_iso), .b(ntaken), .rst_n(rst_iso), .q(c));
    wire c_d0, c_d1, c_d2, c_d3, c_d4;
    qsag_dly_buf #(.TD(400)) u_d0 (.a(c),    .y(c_d0));
    qsag_dly_buf #(.TD(400)) u_d1 (.a(c_d0), .y(c_d1));
    qsag_dly_buf #(.TD(400)) u_d2 (.a(c_d1), .y(c_d2));
    qsag_dly_buf #(.TD(400)) u_d3 (.a(c_d2), .y(c_d3));
    qsag_dly_buf #(.TD(400)) u_d4 (.a(c_d3), .y(c_d4));
    qsag_dly_buf #(.TD(400)) u_d5 (.a(c_d4), .y(c_d));
    qsag_clkinv  u_cn (.a(c_d), .y(c_dn));
    qsag_dly_buf #(.TD(400)) u_d6 (.a(c_d),  .y(c_a));

    wire ck_r, ck_f;
    qsag_clkbuf u_br (.a(c_d),  .y(ck_r));
    qsag_clkbuf u_bf (.a(c_dn), .y(ck_f));
    logic [W-1:0] bank_r, bank_f;
    always_ff @(posedge ck_r or negedge rst_iso)
        if (!rst_iso) bank_r <= '0;
        else          bank_r <= din;
    always_ff @(posedge ck_f or negedge rst_iso)
        if (!rst_iso) bank_f <= '0;
        else          bank_f <= din;

    assign ack_out = c_a;
    assign c_out   = c_a;
    assign dout    = c_a ? bank_r : bank_f;
endmodule

// Egress Sutherland launch stage (core toggles src_req with stable din -> Muller-C waits for
// ~ack_in -> captures din into dual-edge bank -> 4-delay-cell bundling delay -> toggles REQ_OUT!).
module qsag_mpipe_tx_stage #(
    parameter int W = 8
) (
    input  wire         rst_n,
    input  wire         src_req,   // toggle from core after din is valid
    input  wire [W-1:0] din,
    output wire         c_done,    // toggle back to core (item captured & launched)
    output wire         req_out,   // external REQ_OUT pad (trails dout by 4 delay cells!)
    input  wire         ack_in,    // external ACK_IN pad
    output wire [W-1:0] dout
);
    wire src_iso, ack_iso, rst_iso;
    qsag_iso_buf u_isrc (.a(src_req), .y(src_iso));
    qsag_iso_buf u_iack (.a(ack_in),  .y(ack_iso));
    qsag_iso_buf u_irst (.a(rst_n),   .y(rst_iso));

    wire nack, c, cn, ck_r, ck_f, c_d0, c_d1, c_d2, c_req;
    qsag_clkinv   u_na (.a(ack_iso), .y(nack));
    qsag_muller_c u_c  (.a(src_iso), .b(nack), .rst_n(rst_iso), .q(c));
    qsag_clkinv   u_cn (.a(c), .y(cn));

    qsag_clkbuf u_br (.a(c),  .y(ck_r));
    qsag_clkbuf u_bf (.a(cn), .y(ck_f));
    logic [W-1:0] bank_r, bank_f;
    always_ff @(posedge ck_r or negedge rst_iso)
        if (!rst_iso) bank_r <= '0;
        else          bank_r <= din;
    always_ff @(posedge ck_f or negedge rst_iso)
        if (!rst_iso) bank_f <= '0;
        else          bank_f <= din;

    assign dout = c ? bank_r : bank_f;

    // Bundling margin: REQ_OUT toggles 4 delay cells (~1.6 ns TT) AFTER bank_r/bank_f mux settles!
    qsag_dly_buf #(.TD(400)) u_d0 (.a(c),    .y(c_d0));
    qsag_dly_buf #(.TD(400)) u_d1 (.a(c_d0), .y(c_d1));
    qsag_dly_buf #(.TD(400)) u_d2 (.a(c_d1), .y(c_d2));
    qsag_dly_buf #(.TD(400)) u_d3 (.a(c_d2), .y(c_req));

    assign req_out = c_req;
    assign c_done  = c_req;
endmodule
`default_nettype wire

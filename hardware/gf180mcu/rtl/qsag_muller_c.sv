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
    wire ntaken, c, c_d, c_dn, c_a;
    qsag_clkinv u_nt (.a(taken), .y(ntaken));
    qsag_muller_c u_c (.a(req_in), .b(ntaken), .rst_n(rst_n), .q(c));
    wire c_d0;
    qsag_dly_buf #(.TD(400)) u_d0 (.a(c),    .y(c_d0));
    qsag_dly_buf #(.TD(400)) u_d1 (.a(c_d0), .y(c_d));
    qsag_clkinv  u_cn (.a(c_d), .y(c_dn));
    qsag_dly_buf #(.TD(400)) u_d2 (.a(c_d),  .y(c_a));

    wire ck_r, ck_f;
    qsag_clkbuf u_br (.a(c_d),  .y(ck_r));
    qsag_clkbuf u_bf (.a(c_dn), .y(ck_f));
    logic [W-1:0] bank_r, bank_f;
    always_ff @(posedge ck_r) bank_r <= din;
    always_ff @(posedge ck_f) bank_f <= din;

    assign ack_out = c_a;
    assign c_out   = c_a;
    assign dout    = c_a ? bank_r : bank_f;
endmodule

// Egress Sutherland launch stage (core toggles src_req with stable din -> Muller-C waits for
// ~ack_in -> captures din into dual-edge bank -> 800 ps bundling delay -> toggles REQ_OUT!).
module qsag_mpipe_tx_stage #(
    parameter int W = 8
) (
    input  wire         rst_n,
    input  wire         src_req,   // toggle from core after din is valid
    input  wire [W-1:0] din,
    output wire         c_done,    // toggle back to core (item captured & launched)
    output wire         req_out,   // external REQ_OUT pad (trails dout by 2 delay cells!)
    input  wire         ack_in,    // external ACK_IN pad
    output wire [W-1:0] dout
);
    wire nack, c, cn, ck_r, ck_f, c_d0, c_req;
    qsag_clkinv   u_na (.a(ack_in), .y(nack));
    qsag_muller_c u_c  (.a(src_req), .b(nack), .rst_n(rst_n), .q(c));
    qsag_clkinv   u_cn (.a(c), .y(cn));

    qsag_clkbuf u_br (.a(c),  .y(ck_r));
    qsag_clkbuf u_bf (.a(cn), .y(ck_f));
    logic [W-1:0] bank_r, bank_f;
    always_ff @(posedge ck_r or negedge rst_n)
        if (!rst_n) bank_r <= '0;
        else        bank_r <= din;
    always_ff @(posedge ck_f or negedge rst_n)
        if (!rst_n) bank_f <= '0;
        else        bank_f <= din;

    assign dout = c ? bank_r : bank_f;

    // Bundling margin: REQ_OUT toggles 2 delay cells (~800 ps) AFTER bank_r/bank_f mux settles!
    qsag_dly_buf #(.TD(400)) u_d0 (.a(c),    .y(c_d0));
    qsag_dly_buf #(.TD(400)) u_d1 (.a(c_d0), .y(c_req));

    assign req_out = c_req;
    assign c_done  = c_req;
endmodule
`default_nettype wire

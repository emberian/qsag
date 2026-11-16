// QSAG-NI-180 clockless ingress: Muller C-element and one two-phase (transition-signalled)
// bundled-data micropipeline stage in front of the core clock domain.
`default_nettype none
`timescale 1ps / 1ps

// Muller C-element with active-low reset: q follows a and b when they agree, holds otherwise.
//   q+ = a b + q (a + b)
// All three prime implicants are present, so the function has no static hazard for single
// input changes; in silicon it is one AOI222 complex gate with its own output fed back.
module qsag_muller_c (
    input  wire a,
    input  wire b,
    input  wire rst_n,
    output wire q
);
`ifdef QSAG_GF180_CELLS
    wire zn, rst;
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__inv_1    u_ri (.I(rst_n), .ZN(rst));
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__aoi222_1 u_maj (.A1(a), .A2(b), .B1(a), .B2(q), .C1(b), .C2(q), .ZN(zn));
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__nor2_2   u_q (.A1(zn), .A2(rst), .ZN(q));
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

// Sutherland-style capture stage. Every transition of req_in (rising or falling) is one item.
//   c = C(req_in, ~taken)      fires when a new request is pending and the previous item has
//                              been taken by the core
//   capture on both edges of the (delayed) c; ack_out = c delayed once more
// The sender may change the data as soon as it sees ack_out toggle; the stage holds the item
// until the core toggles `taken`. No clock is involved in the handshake itself.
module qsag_mpipe_stage #(
    parameter int W = 16
) (
    input  wire         rst_n,
    input  wire         req_in,
    input  wire [W-1:0] din,
    output wire         ack_out,
    // towards the clocked domain
    input  wire         taken,     // toggle, driven by the core after it copied `dout`
    output wire         c_out,     // toggle: an item is present when c_out != taken
    output wire [W-1:0] dout
);
    wire ntaken, c, c_d, c_dn, c_a;
    qsag_clkinv u_nt (.a(taken), .y(ntaken));
    qsag_muller_c u_c (.a(req_in), .b(ntaken), .rst_n(rst_n), .q(c));
    // bundling margin: the capture clock trails the request by two delay cells
    wire c_d0;
    qsag_dly_buf #(.TD(400)) u_d0 (.a(c),    .y(c_d0));
    qsag_dly_buf #(.TD(400)) u_d1 (.a(c_d0), .y(c_d));
    qsag_clkinv u_cn (.a(c_d), .y(c_dn));
    qsag_dly_buf #(.TD(400)) u_d2 (.a(c_d),  .y(c_a));

    // capture clocks through explicit buffers (each drives one bank of W flip-flops)
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
`default_nettype wire

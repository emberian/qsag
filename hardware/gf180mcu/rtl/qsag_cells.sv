// Dregg-180 (QSAG-NI-180) technology cell wrappers for gf180mcu_fd_sc_mcu7t5v0.
//
// Every place where the design depends on a specific physical gate (clock gates, clock muxes,
// delay stages, C-elements, synchronizers, Vernier TDC taps, rapid-bit responder mux, shield
// buffers) goes through one of these modules.
//   * default            behavioural, simulated by Verilator (delays under QSAG_SIM_DELAYS);
//   * QSAG_GF180_CELLS   direct gf180mcu_fd_sc_mcu7t5v0 instances, kept through synthesis.
`default_nettype none
`timescale 1ps / 1ps
/* verilator lint_off UNUSEDPARAM */
/* verilator lint_off SYNCASYNCNET */
/* verilator lint_off ZERODLY */

// Integrated clock gate (latch-and-AND). en is sampled while clk is low.
module qsag_clkgate (
    input  wire clk,
    input  wire en,
    output wire gclk
);
`ifdef QSAG_GF180_CELLS
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__icgtp_2 u_icg (.CLK(clk), .E(en), .TE(1'b0), .Q(gclk));
`else
    logic lat;
    /* verilator lint_off LATCH */
    /* verilator lint_off COMBDLY */
    always_latch if (!clk) lat <= en;
    /* verilator lint_on COMBDLY */
    /* verilator lint_on LATCH */
    assign gclk = clk & lat;
`endif
endmodule

module qsag_clkgate_1 (
    input  wire clk,
    input  wire en,
    output wire gclk
);
`ifdef QSAG_GF180_CELLS
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__icgtp_1 u_icg (.CLK(clk), .E(en), .TE(1'b0), .Q(gclk));
`else
    logic lat;
    /* verilator lint_off LATCH */
    /* verilator lint_off COMBDLY */
    always_latch if (!clk) lat <= en;
    /* verilator lint_on COMBDLY */
    /* verilator lint_on LATCH */
    assign gclk = clk & lat;
`endif
endmodule

// Enable register with asynchronous active-low clear (secret-bearing state).
module qsag_ereg #(
    parameter int W = 64
) (
    input  wire          clk,
    input  wire          rst_n,
    input  wire          en,
    input  wire  [W-1:0] d,
    output logic [W-1:0] q
);
`ifdef QSAG_ICG
    wire gclk;
    qsag_clkgate u_cg (.clk(clk), .en(en), .gclk(gclk));
    always_ff @(posedge gclk or negedge rst_n)
        if (!rst_n) q <= '0;
        else q <= d;
`else
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) q <= '0;
        else if (en) q <= d;
`endif
endmodule

// Enable register without reset (public / wiped datapath state).
module qsag_ereg_nr #(
    parameter int W = 64
) (
    input  wire          clk,
    input  wire          en,
    input  wire  [W-1:0] d,
    output logic [W-1:0] q
);
`ifdef QSAG_ICG
    wire gclk;
    qsag_clkgate u_cg (.clk(clk), .en(en), .gclk(gclk));
    always_ff @(posedge gclk) q <= d;
`else
    always_ff @(posedge clk) if (en) q <= d;
`endif
endmodule

// Level-sensitive transparent latch word (gf180mcu_fd_sc_mcu7t5v0__latq_1).
// Used with posedge-captured write data + icgtp_1 high-phase clock gate so reads see a full
// clock cycle and no combinational loop exists across read/write ports.
module qsag_latch_word #(parameter int W = 64) (
    input  wire         gate,
    input  wire [W-1:0] d,
    output wire [W-1:0] q
);
`ifdef QSAG_GF180_CELLS
    for (genvar i = 0; i < W; i++) begin : g_bit
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__latq_1 u_l (.D(d[i]), .E(gate), .Q(q[i]));
    end
`else
    logic [W-1:0] qr;
    /* verilator lint_off LATCH */
    /* verilator lint_off COMBDLY */
    always_latch if (gate) qr <= d;
    /* verilator lint_on COMBDLY */
    /* verilator lint_on LATCH */
    assign q = qr;
`endif
endmodule

// Two-flop synchronizer with asynchronous clear.
module qsag_sync2 #(
    parameter bit RV = 1'b0
) (
    input  wire clk,
    input  wire rst_n,
    input  wire d,
    output wire q
);
    (* ASYNC_REG = "TRUE", keep *) logic m;
    (* ASYNC_REG = "TRUE", keep *) logic s;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) begin
            m <= RV;
            s <= RV;
        end else begin
            m <= d;
            s <= m;
        end
    assign q = s;
endmodule

// Reset synchronizer: asynchronous assert, two-flop synchronous release.
module qsag_rst_sync (
    input  wire clk,
    input  wire arst_n,
    output wire rst_n
);
    qsag_sync2 #(.RV(1'b0)) u_s (.clk(clk), .rst_n(arst_n), .d(1'b1), .q(rst_n));
endmodule

// Static (strap-selected) clock multiplexer.
module qsag_clkmux2 (
    input  wire a,
    input  wire b,
    input  wire sel,
    output wire y
);
`ifdef QSAG_GF180_CELLS
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__mux2_2 u_mux (.I0(a), .I1(b), .S(sel), .Z(y));
`else
    assign y = sel ? b : a;
`endif
endmodule

// High-drive single-gate 2:1 mux for < 6 ns Brands-Chaum pad-to-pad turnaround.
module qsag_fast_mux2 #(
    parameter int TD = 240
) (
    input  wire a,
    input  wire b,
    input  wire sel,
    output wire y
);
`ifdef QSAG_GF180_CELLS
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__mux2_4 u_fast_mux (.I0(a), .I1(b), .S(sel), .Z(y));
`elsif QSAG_SIM_DELAYS
    logic yr;
    initial yr = #(TD) (sel ? b : a);
    always @(a or b or sel) yr <= #(TD) (sel ? b : a);
    assign y = yr;
`else
    assign y = sel ? b : a;
`endif
endmodule

module qsag_clkinv (
    input  wire a,
    output wire y
);
`ifdef QSAG_GF180_CELLS
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__clkinv_2 u_inv (.I(a), .ZN(y));
`else
    assign y = ~a;
`endif
endmodule

module qsag_clkand2 (
    input  wire a,
    input  wire b,
    output wire y
);
`ifdef QSAG_GF180_CELLS
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__and2_2 u_and (.A1(a), .A2(b), .Z(y));
`else
    assign y = a & b;
`endif
endmodule

module qsag_clkor2 (
    input  wire a,
    input  wire b,
    output wire y
);
`ifdef QSAG_GF180_CELLS
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__or2_2 u_or (.A1(a), .A2(b), .Z(y));
`else
    assign y = a | b;
`endif
endmodule

module qsag_dly_nand #(
    parameter int TD = 180
) (
    input  wire a,
    input  wire en,
    output wire y
);
`ifdef QSAG_GF180_CELLS
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__nand2_1 u_nand (.A1(a), .A2(en), .ZN(y));
`elsif QSAG_SIM_DELAYS
    logic yr;
    initial yr = #(TD) ~(a & en);
    always @(a or en) yr <= #(TD) ~(a & en);
    assign y = yr;
`else
    assign y = ~(a & en);
`endif
endmodule

module qsag_dly_buf #(
    parameter int TD = 400
) (
    input  wire a,
    output wire y
);
`ifdef QSAG_GF180_CELLS
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__dlya_1 u_dly (.I(a), .Z(y));
`elsif QSAG_SIM_DELAYS
    logic yr;
    initial yr = #(TD) a;
    always @(a) yr <= #(TD) a;
    assign y = yr;
`else
    assign y = a;
`endif
endmodule

// Fast Vernier stop-line stage (~220 ps vs ~450 ps dlya_1 -> ~230 ps differential Vernier step).
module qsag_vernier_fast #(
    parameter int TD = 220
) (
    input  wire a,
    output wire y
);
`ifdef QSAG_GF180_CELLS
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__buf_2 u_vf (.I(a), .Z(y));
`elsif QSAG_SIM_DELAYS
    logic yr;
    initial yr = #(TD) a;
    always @(a) yr <= #(TD) a;
    assign y = yr;
`else
    assign y = a;
`endif
endmodule

// Active Metal5 serpentine shield spine buffer.
module qsag_shield_buf #(
    parameter int TD = 200
) (
    input  wire a,
    output wire y
);
`ifdef QSAG_GF180_CELLS
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__buf_4 u_sh (.I(a), .Z(y));
`elsif QSAG_SIM_DELAYS
    logic yr;
    initial yr = #(TD) a;
    always @(a) yr <= #(TD) a;
    assign y = yr;
`else
    assign y = a;
`endif
endmodule

module qsag_dly_mux2 #(
    parameter int TD = 220
) (
    input  wire a,
    input  wire b,
    input  wire sel,
    output wire y
);
`ifdef QSAG_GF180_CELLS
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__mux2_1 u_mux (.I0(a), .I1(b), .S(sel), .Z(y));
`elsif QSAG_SIM_DELAYS
    logic yr;
    initial yr = #(TD) (sel ? b : a);
    always @(a or b or sel) yr <= #(TD) (sel ? b : a);
    assign y = yr;
`else
    assign y = sel ? b : a;
`endif
endmodule

module qsag_dly_fine #(
    parameter int TD = 130
) (
    input  wire a,
    output wire y
);
`ifdef QSAG_GF180_CELLS
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__buf_1 u_buf (.I(a), .Z(y));
`elsif QSAG_SIM_DELAYS
    logic yr;
    initial yr = #(TD) a;
    always @(a) yr <= #(TD) a;
    assign y = yr;
`else
    assign y = a;
`endif
endmodule

module qsag_dffsr (
    input  wire clk,
    input  wire rn,
    input  wire sn,
    input  wire d,
    output logic q
);
    always_ff @(posedge clk or negedge rn or negedge sn)
        if (!rn) q <= 1'b0;
        else if (!sn) q <= 1'b1;
        else q <= d;
endmodule

module qsag_osc_nand #(
    parameter int TD = 180
) (
    input  wire a,
    input  wire en,
    output wire y
);
`ifdef QSAG_GF180_CELLS
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__nand2_1 u_nand (.A1(a), .A2(en), .ZN(y));
`elsif QSAG_SIM_DELAYS
    logic yr;
    initial yr = #(TD) ~(a & en);
    always @(a or en) yr <= #(TD) ~(a & en);
    assign y = yr;
`else
    assign y = 1'b1;
    wire unused = &{1'b0, a, en};
`endif
endmodule

module qsag_clkbuf (
    input  wire a,
    output wire y
);
`ifdef QSAG_GF180_CELLS
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__clkbuf_2 u_buf (.I(a), .Z(y));
`else
    assign y = a;
`endif
endmodule

module qsag_srlatch (
    input  wire rn,
    input  wire sn,
    output wire q
);
`ifdef QSAG_GF180_CELLS
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__dffrsnq_1 u_ff (.CLK(1'b0), .D(1'b0), .SETN(sn), .RN(rn), .Q(q));
`else
    logic qr;
    always_ff @(negedge rn or negedge sn)
        if (!rn) qr <= 1'b0;
        else qr <= 1'b1;
    assign q = qr;
`endif
endmodule

module qsag_dly_inv #(
    parameter int TD = 180
) (
    input  wire a,
    output wire y
);
`ifdef QSAG_GF180_CELLS
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__nand2_1 u_nand (.A1(a), .A2(a), .ZN(y));
`elsif QSAG_SIM_DELAYS
    logic yr;
    initial yr = #(TD) ~a;
    always @(a) yr <= #(TD) ~a;
    assign y = yr;
`else
    assign y = ~a;
`endif
endmodule
`default_nettype wire

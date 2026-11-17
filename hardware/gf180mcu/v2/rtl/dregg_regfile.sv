// Dregg-180 v2 register file (ARCHITECTURE.md 5.2), written as the array the floorplan places:
// NROWS x 64 latches, one write-hold register, one read port. Every cell of the array is instantiated
// by name, with the cell list and instance names of v2/phys/proxy/px_rf.sv, so that
// v2/phys/floorplan/rf_array.tcl places it unchanged (instance u_rf of the core).
//
//   slot p (one standard-cell row):  bits 0..31 | u_wen u_cg u_sel | bits 32..63
//       bit b: u_lat (latrnq_1) + u_rd (nand2_1)
//       u_cg  (icgtp_4): the word line of this row. One sized driver per row, for every row, the
//             Keccak work rows included (latch enables are not clock-tree sinks)
//       u_sel (and2_4): the read select line of this row
//   group k = slots 8k..8k+7:  per column u_na, u_nb (nand4_1), u_gn (nor2_1);  centre u_ckb (clkbuf_4)
//   column b:  u_wd (buf_8) write bit line;  u_rn (buf_4) clear line, from g_half[b/32].u_rnh (buf_8);
//              u_f0..u_f2 (nand3_1) + u_or (or3_1): the nine group lines into rdata[b]
//
// Slots and rows. g_row[p] is array slot p, bottom (p = 0) to top, as rf_array.tcl places it. Which
// logical row sits in which slot is the localparam R below and nothing else in the design depends on it:
//   slots 0 .. N_KWORK-1                 the Keccak work rows (bottom edge, next to the Keccak unit)
//   slots N_KWORK .. N_KWORK+N_OUT-1     the out rows
//   the other slots                      lanes, scratch, key, pin and state rows in address order
// The physical lane may choose another order by changing that one mapping.
//
// Direct rows (Keccak work rows, out rows) are not on the read port: the input of the column tree that
// belongs to their slot is tied high, so no select value can bring them to rdata. Their u_rd gate is the
// row's output driver (select tied high): the work rows leave on kw_q to the Keccak unit, the out rows
// on out_q to the egress. The work rows take their data from private lines (kc_d, kb_d), not from the
// write bit lines.
//
// Two-phase discipline: the hold register captures on the rising edge; a row whose enable was high in
// the clock before that edge is transparent in the high phase after it and closed at the falling edge.
//   h_en, h_d, h_q   the hold register (also the accumulator of the word unit)
//   we, waddr        open one addressed row;  out_we  open an out row (PUSH)
//   wipe             class-wise clear through the write path: the rows of the selected classes open on
//                    data lines forced to zero; the hold register keeps its value.
//                      bit 0 rows 0..7; bit 1 rows 8..31 (lanes 8..24, Keccak work rows); bit 2 scratch; bit 3 out
//   kw_we            open Keccak work rows: column parities 0..4 from kc_d, saved lanes 5, 6 from kb_d
//   srst_n           secret reset: reaches RN of every latch through u_rnh -> u_rn only, and the hold
//                    register directly. No clock is involved.
// The module has no parameters (a parameterised kept module is counted as unmapped cells by LibreLane).
`default_nettype none

(* keep_hierarchy *)
module dregg_regfile (
    input  wire          clk,
    input  wire          srst_n,
    input  wire          h_en,
    input  wire  [63:0]  h_d,
    output wire  [63:0]  h_q,
    input  wire          we,
    input  wire  [6:0]   waddr,
    input  wire  [1:0]   out_we,
    input  wire  [3:0]   wipe,
    input  wire  [6:0]   kw_we,
    input  wire  [319:0] kc_d,
    input  wire  [63:0]  kb_d,
    output wire  [447:0] kw_q,
    input  wire  [6:0]   raddr,
    output wire  [63:0]  rdata,
    output wire  [127:0] out_q,
    output wire  [71:0]  wl_en_o      // word-line enables of this clock, by logical row (assertions)
);
`include "dregg_defs.svh"
    localparam int NG  = NROWS / 8;
    localparam int NDR = N_KWORK + N_OUT;           // direct rows

    // ------------------------------------------------------------ hold register, data lines
    qsag_ereg #(.W(64)) u_hold (.clk(clk), .rst_n(srst_n), .en(h_en), .d(h_d), .q(h_q));
    logic wipe_q;                                   // a wipe opens its rows on zero data lines
    always_ff @(posedge clk or negedge srst_n)
        if (!srst_n) wipe_q <= 1'b0;
        else         wipe_q <= |wipe;
    wire [63:0] wd  = h_q & {64{~wipe_q}};
    wire [63:0] kbd = kb_d & {64{~wipe_q}};
    wire [319:0] kcd = kc_d & {320{~wipe_q}};

    // ------------------------------------------------------------ predecode (placed by the tool)
    // logical row of a slot
    function automatic logic [6:0] slot_row(input logic [6:0] p);
        if (p < 7'(N_KWORK))  slot_row = 7'(KWORK0) + p;
        else if (p < 7'(NDR)) slot_row = 7'(OUT0) + (p - 7'(N_KWORK));
        else if ((p - 7'(NDR)) < 7'(KWORK0)) slot_row = p - 7'(NDR);
        else slot_row = p - 7'(N_OUT);
    endfunction
    logic [71:0] en_a, en_b, sel_a, sel_b;
    logic [71:0] wl_en;
    logic [6:0] lr;
    logic       lw;
    always_comb begin
        lr    = '0;
        lw    = 1'b0;
        en_a  = '0;
        en_b  = '0;
        sel_a = '0;
        sel_b = '0;
        wl_en = '0;
        for (int p = 0; p < NROWS; p++) begin
            lr = slot_row(7'(p));
            lw = 1'b0;
            if (p < N_KWORK) begin
                en_a[p]  = kw_we[p] | wipe[W_LANES_HI_B];
                en_b[p]  = en_a[p];
                sel_a[p] = 1'b1;
                sel_b[p] = 1'b1;
            end else if (p < NDR) begin
                en_a[p]  = out_we[p - N_KWORK] | wipe[W_OUT_B];
                en_b[p]  = en_a[p];
                sel_a[p] = 1'b1;
                sel_b[p] = 1'b1;
            end else begin
                lw = (lr <= 7'(WIPE_LO_LAST)) ? wipe[W_LANES_LO_B]
                   : (lr <= 7'(WIPE_HI_LAST)) ? wipe[W_LANES_HI_B]
                   : ((lr >= 7'(SCRATCH0)) && (lr < 7'(SCRATCH0 + N_SCRATCH))) ? wipe[W_SCRATCH_B] : 1'b0;
                en_a[p]  = (we && (waddr[6:3] == lr[6:3])) | lw;
                en_b[p]  = (waddr[2:0] == lr[2:0]) | lw;
                sel_a[p] = (raddr[6:3] == lr[6:3]);
                sel_b[p] = (raddr[2:0] == lr[2:0]);
            end
            wl_en[lr] = en_a[p] & en_b[p];
        end
    end
    assign wl_en_o = wl_en;

    // ------------------------------------------------------------ the array
    wire [63:0] wbl;                 // write bit lines
    wire [63:0] rn;                  // per-column clear
    wire [1:0]  rnh;
    wire [63:0] n   [72];            // row-local read gates into the column tree, active low
    wire [63:0] dn  [72];            // row outputs of the direct rows, active low
    wire [63:0] gn  [9];             // group lines, active low
    wire [8:0]  gck;
    wire [63:0] q_row [72];          // by logical row (test bench read-out only)

    genvar r, b, k, h;
    generate
        for (h = 0; h < 2; h++) begin : g_half
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__buf_8 u_rnh (.I(srst_n), .Z(rnh[h]));
        end
        for (b = 0; b < 64; b++) begin : g_col
            wire f0, f1, f2;
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__buf_8   u_wd (.I(wd[b]), .Z(wbl[b]));
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__buf_4   u_rn (.I(rnh[b / 32]), .Z(rn[b]));
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__nand3_1 u_f0 (.A1(gn[0][b]), .A2(gn[1][b]), .A3(gn[2][b]), .ZN(f0));
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__nand3_1 u_f1 (.A1(gn[3][b]), .A2(gn[4][b]), .A3(gn[5][b]), .ZN(f1));
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__nand3_1 u_f2 (.A1(gn[6][b]), .A2(gn[7][b]), .A3(gn[8][b]), .ZN(f2));
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__or3_1   u_or (.A1(f0), .A2(f1), .A3(f2), .Z(rdata[b]));
        end
        for (k = 0; k < 9; k++) begin : g_grp
            if (k < NG) begin : g_on
                (* keep *) gf180mcu_fd_sc_mcu7t5v0__clkbuf_4 u_ckb (.I(clk), .Z(gck[k]));
                for (b = 0; b < 64; b++) begin : g_bit
                    wire a, bb;
                    (* keep *) gf180mcu_fd_sc_mcu7t5v0__nand4_1 u_na (.A1(n[8*k+0][b]), .A2(n[8*k+1][b]),
                                                                      .A3(n[8*k+2][b]), .A4(n[8*k+3][b]), .ZN(a));
                    (* keep *) gf180mcu_fd_sc_mcu7t5v0__nand4_1 u_nb (.A1(n[8*k+4][b]), .A2(n[8*k+5][b]),
                                                                      .A3(n[8*k+6][b]), .A4(n[8*k+7][b]), .ZN(bb));
                    (* keep *) gf180mcu_fd_sc_mcu7t5v0__nor2_1  u_gn (.A1(a), .A2(bb), .ZN(gn[k][b]));
                end
            end else begin : g_off                   // a 64-row file has eight groups
                assign gck[k] = 1'b0;
                assign gn[k]  = '1;
            end
        end
        for (r = 0; r < 72; r++) begin : g_row
            if (r < NROWS) begin : g_on
                // logical row of this slot (the same mapping as slot_row above)
                localparam int R = (r < N_KWORK) ? KWORK0 + r : (r < NDR) ? OUT0 + (r - N_KWORK)
                                 : ((r - NDR) < KWORK0) ? r - NDR : r - N_OUT;
                wire wen, gate, sel;
                wire [63:0] dl;
                if (r < 5)            begin : g_kc assign dl = kcd[64*r +: 64]; end
                else if (r < N_KWORK) begin : g_kb assign dl = kbd; end
                else                  begin : g_wb assign dl = wbl; end
                (* keep *) gf180mcu_fd_sc_mcu7t5v0__and2_1  u_wen (.A1(en_a[r]), .A2(en_b[r]), .Z(wen));
                (* keep *) gf180mcu_fd_sc_mcu7t5v0__icgtp_4 u_cg  (.CLK(gck[r / 8]), .E(wen), .TE(1'b0), .Q(gate));
                (* keep *) gf180mcu_fd_sc_mcu7t5v0__and2_4  u_sel (.A1(sel_a[r]), .A2(sel_b[r]), .Z(sel));
                for (b = 0; b < 64; b++) begin : g_bit
                    wire q, nrd;
`ifdef DREGG_TB_BACKDOOR
                    dregg_tb_latrnq u_lat (.D(dl[b]), .E(gate), .RN(rn[b]), .Q(q),
                                           .bd_we(`DREGG_TB_BACKDOOR.bd_rf_we && `DREGG_TB_BACKDOOR.bd_row == 7'(R)),
                                           .bd_d(`DREGG_TB_BACKDOOR.bd_data[b]));
`else
                    (* keep *) gf180mcu_fd_sc_mcu7t5v0__latrnq_1 u_lat (.D(dl[b]), .E(gate), .RN(rn[b]), .Q(q));
`endif
                    (* keep *) gf180mcu_fd_sc_mcu7t5v0__nand2_1  u_rd  (.A1(q), .A2(sel), .ZN(nrd));
                    assign q_row[R][b] = q;
                    if (r < NDR) begin : g_direct
                        assign n[r][b]  = 1'b1;          // not on the read port
                        assign dn[r][b] = nrd;
                    end else begin : g_read
                        assign n[r][b]  = nrd;
                        assign dn[r][b] = 1'b1;
                    end
                end
            end else begin : g_off
                assign n[r]     = '1;
                assign dn[r]    = '1;
                assign q_row[r] = '0;
            end
        end
        for (k = 0; k < N_KWORK; k++) begin : g_kq
            assign kw_q[64*k +: 64] = ~dn[k];
        end
        for (k = 0; k < N_OUT; k++) begin : g_oq
            assign out_q[64*k +: 64] = ~dn[N_KWORK + k];
        end
    endgenerate

    /* verilator lint_off UNUSEDSIGNAL */
    wire unused = &{1'b0, q_row[0], gck, en_a, en_b, sel_a, sel_b};
    /* verilator lint_on UNUSEDSIGNAL */
endmodule
`default_nettype wire

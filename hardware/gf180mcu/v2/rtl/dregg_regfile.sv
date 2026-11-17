// Dregg-180 v2 register file (ARCHITECTURE.md 5.2): NROWS x 64 latches, one write-hold register,
// one read port.
//
// Two-phase discipline. The hold register (H) captures on the rising edge. A row whose write enable
// was high in the clock before that edge is transparent during the high phase after it and closed at
// the falling edge, so it settles to the word the hold register took on that same edge. A row is never
// read in the clock in which it is transparent: the sequencer stalls instead (dregg_seq), and the
// assertion at the bottom of this file checks it.
//
//   h_en, h_d, h_q   the hold register. It is also the accumulator of the word unit.
//   we, waddr        open one lane, scratch, key, pin or state row on the next high phase
//   out_we           open an out row (PUSH); out rows are written by nothing else and are not readable
//   wipe             class-wise clear through the write path: every row of the selected classes opens on
//                    a data line forced to zero. The hold register keeps its value.
//                      bit 0 rows 0..7; bit 1 rows 8..31 (lanes 8..24 and the Keccak work rows);
//                      bit 2 scratch; bit 3 out
//   kw_we, kc_d, kb_d, kw_q   the seven Keccak work rows: column parities 0..4 load from kc_d,
//                    saved lanes 5 and 6 from kb_d; all seven read out directly to the Keccak unit
//   raddr, rdata     read port (lane, scratch, key, pin, state rows)
//   out_q            the two out rows, for the egress and nothing else
//   srst_n           secret reset: RN of every latch and of the hold register; asynchronous, works with
//                    the clock stopped. Key, pin and state rows are cleared by nothing else.
`default_nettype none

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
    output wire  [71:0]  wl_en_o      // word-line enables of this clock (for assertions and the phys lane)
);
`include "dregg_defs.svh"

    // ------------------------------------------------------------ hold register
    qsag_ereg #(.W(64)) u_hold (.clk(clk), .rst_n(srst_n), .en(h_en), .d(h_d), .q(h_q));

    // a wipe opens its rows on a zero data line; wipe_q marks that high phase
    logic wipe_q;
    always_ff @(posedge clk or negedge srst_n)
        if (!srst_n) wipe_q <= 1'b0;
        else         wipe_q <= |wipe;
    wire [63:0] wd = h_q & {64{~wipe_q}};

    // ------------------------------------------------------------ word lines
    logic [71:0] wl_en;
    always_comb begin
        wl_en = '0;
        for (int r = 0; r < NROWS; r++) begin
            if (r >= KWORK0 && r < KWORK0 + N_KWORK)
                wl_en[r] = kw_we[r - KWORK0] | wipe[W_LANES_HI_B];
            else if (r >= OUT0 && r < OUT0 + N_OUT)
                wl_en[r] = out_we[r - OUT0] | wipe[W_OUT_B];
            else begin
                wl_en[r] = we && (waddr == 7'(r));
                if (r <= WIPE_LO_LAST)                             wl_en[r] = wl_en[r] | wipe[W_LANES_LO_B];
                else if (r <= WIPE_HI_LAST)                        wl_en[r] = wl_en[r] | wipe[W_LANES_HI_B];
                else if (r >= SCRATCH0 && r < SCRATCH0 + N_SCRATCH) wl_en[r] = wl_en[r] | wipe[W_SCRATCH_B];
            end
        end
    end
    assign wl_en_o = wl_en;

    wire [71:0] wl;
    genvar r, b;
    generate
        for (r = 0; r < 72; r++) begin : g_wl
            if (r < NROWS) begin : g_on
                qsag_latgate u_cg (.clk(clk), .en(wl_en[r]), .gclk(wl[r]));
            end else begin : g_off
                assign wl[r] = 1'b0;
            end
        end
    endgenerate

    // ------------------------------------------------------------ read select
    logic [71:0] rsel;
    always_comb begin
        rsel = '0;
        for (int i = 0; i < NROWS; i++) rsel[i] = (raddr == 7'(i));
    end

    // ------------------------------------------------------------ bit columns
    wire [63:0] kq [7];
    wire [63:0] oq [2];
    generate
        for (b = 0; b < 64; b++) begin : g_bit
            wire [6:0] kd_b;
            wire [6:0] kq_b;
            wire [1:0] oq_b;
            assign kd_b[0] = kc_d[64*0 + b] & ~wipe_q;
            assign kd_b[1] = kc_d[64*1 + b] & ~wipe_q;
            assign kd_b[2] = kc_d[64*2 + b] & ~wipe_q;
            assign kd_b[3] = kc_d[64*3 + b] & ~wipe_q;
            assign kd_b[4] = kc_d[64*4 + b] & ~wipe_q;
            assign kd_b[5] = kb_d[b] & ~wipe_q;
            assign kd_b[6] = kd_b[5];
            dregg_rf_slice u_s (
                .rst_n(srst_n), .d(wd[b]), .kd(kd_b), .wl(wl), .rsel(rsel),
                .rd(rdata[b]), .kq(kq_b), .oq(oq_b)
`ifdef DREGG_TB_BACKDOOR
                , .bd_d(`DREGG_TB_BACKDOOR.bd_data[b])
`endif
            );
            assign kq[0][b] = kq_b[0];
            assign kq[1][b] = kq_b[1];
            assign kq[2][b] = kq_b[2];
            assign kq[3][b] = kq_b[3];
            assign kq[4][b] = kq_b[4];
            assign kq[5][b] = kq_b[5];
            assign kq[6][b] = kq_b[6];
            assign oq[0][b] = oq_b[0];
            assign oq[1][b] = oq_b[1];
        end
    endgenerate
    assign kw_q  = {kq[6], kq[5], kq[4], kq[3], kq[2], kq[1], kq[0]};
    assign out_q = {oq[1], oq[0]};

endmodule
`default_nettype wire

// Dregg-180 v2 register file, one bit column (ARCHITECTURE.md 5.2).
//
// NROWS latches (latrnq_1) on one data line, one word line (gated clock) per row, and this bit of the
// read port. A physical lane places 64 of these side by side; the word lines run across them.
//
//   d      write-data line: the hold register bit (forced to 0 by the register file while a wipe is open)
//   kd     private data lines of the seven Keccak work rows (column parities 0..4, saved lanes 5, 6)
//   wl     word lines, one per row: the row is transparent while its line is high
//   rsel   one-hot read select. Only lane, scratch, key, pin and state rows have a read gate: the
//          Keccak work rows leave on kq, the out rows on oq, and neither can reach rd.
//   rst_n  secret reset, wired to RN of every latch: it clears the column with the clock stopped.
//
// The module has no parameters (LibreLane counts a parameterised kept module as unmapped cells).
`default_nettype none

module dregg_rf_slice (
    input  wire         rst_n,
    input  wire         d,
    input  wire  [6:0]  kd,
    input  wire  [71:0] wl,
    input  wire  [71:0] rsel,
    output wire         rd,
    output wire  [6:0]  kq,
    output wire  [1:0]  oq
`ifdef DREGG_TB_BACKDOOR
    , input wire        bd_d        // test bench only: this column's bit of the backdoor word
`endif
);
`include "dregg_defs.svh"
    // synthesis translate_off
    if (NROWS > 72) begin : g_too_many_rows
        $error("dregg_rf_slice: the port width is fixed at 72 rows");
    end
    // synthesis translate_on

    wire [NROWS-1:0] q_all;
    wire [NROWS-1:0] d_row;
    genvar r;
    generate
        for (r = 0; r < NROWS; r++) begin : g_d
            if (r >= KWORK0 && r < KWORK0 + N_KWORK) begin : g_k
                assign d_row[r] = kd[r - KWORK0];
            end else begin : g_h
                assign d_row[r] = d;
            end
        end
    endgenerate

`ifdef QSAG_GF180_CELLS
    generate
        for (r = 0; r < NROWS; r++) begin : g_row
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__latrnq_1 u_lat (.D(d_row[r]), .E(wl[r]), .RN(rst_n), .Q(q_all[r]));
        end
    endgenerate
`else
    logic [NROWS-1:0] qr;
    /* verilator lint_off LATCH */
    /* verilator lint_off COMBDLY */
    generate
        for (r = 0; r < NROWS; r++) begin : g_row
            always_latch begin
                if (!rst_n)     qr[r] <= 1'b0;
                else if (wl[r]) qr[r] <= d_row[r];
`ifdef DREGG_TB_BACKDOOR
                // test bench only: place a row directly (fixtures that put keys into the key rows)
                else if (`DREGG_TB_BACKDOOR.bd_rf_we && `DREGG_TB_BACKDOOR.bd_row == 7'(r))
                    qr[r] <= bd_d;
`endif
            end
        end
    endgenerate
    /* verilator lint_on COMBDLY */
    /* verilator lint_on LATCH */
    assign q_all = qr;
`endif

    // read port: AND-OR over the rows that have a read gate
    logic [NROWS-1:0] rmask;
    always_comb begin
        rmask = '0;
        for (int i = 0; i < NROWS; i++)
            rmask[i] = !((i >= KWORK0 && i < KWORK0 + N_KWORK) || (i >= OUT0 && i < OUT0 + N_OUT));
    end
    assign rd = |(q_all & rsel[NROWS-1:0] & rmask);
    assign kq = q_all[KWORK0 +: N_KWORK];
    assign oq = q_all[OUT0 +: N_OUT];

    /* verilator lint_off UNUSEDSIGNAL */
    wire unused = &{1'b0, wl, rsel};
    /* verilator lint_on UNUSEDSIGNAL */
endmodule
`default_nettype wire

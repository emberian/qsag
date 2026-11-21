// QSAG-NI-180 dual-clock FIFO with registered Gray pointers (flip-flop storage, depth 2^AW).
//
// Only the registered Gray pointers cross domains, each through a two-flop synchronizer; the
// storage word selected by the read pointer is stable from one write-clock cycle before the
// read side can see it non-empty. Occupancy is exported in both domains (conservative on the
// side that computes it): `wcount` never under-reports, `rcount` never over-reports.
`default_nettype none

module qsag_async_fifo_gray #(
    parameter int W  = 64,
    parameter int AW = 3
) (
    input  wire          wclk,
    input  wire          wrst_n,
    input  wire          winc,
    input  wire [W-1:0]  wdata,
    output wire          wfull,
    output wire [AW:0]   wcount,
    input  wire          rclk,
    input  wire          rrst_n,
    input  wire          rinc,
    output logic [W-1:0] rdata,
    output wire          rempty,
    output wire [AW:0]   rcount
);
    localparam int DEPTH = 1 << AW;

    logic [AW:0] wbin, wgray, rbin, rgray;
    wire  [AW:0] rgray_w, wgray_r;
    wire  [W-1:0] mem [DEPTH];

    // write side
    wire [AW:0] wbin_n  = wbin + {{AW{1'b0}}, (winc & ~wfull)};
    wire [AW:0] wgray_n = (wbin_n >> 1) ^ wbin_n;
    always_ff @(posedge wclk or negedge wrst_n)
        if (!wrst_n) begin
            wbin  <= '0;
            wgray <= '0;
        end else begin
            wbin  <= wbin_n;
            wgray <= wgray_n;
        end
    wire [AW:0] rbin_w, wbin_r;   // Gray to binary
    assign rbin_w[AW] = rgray_w[AW];
    assign wbin_r[AW] = wgray_r[AW];
    assign wcount = wbin - rbin_w;
    assign wfull  = wcount[AW];

    genvar i;
`ifdef QSAG_LATCH_RF
    wire         any_we = winc && !wfull;
    wire [W-1:0] wd_hold_q;
    qsag_ereg_nr #(.W(W)) u_wh (.clk(wclk), .en(any_we), .d(wdata), .q(wd_hold_q));
    generate
        for (i = 0; i < DEPTH; i++) begin : g_mem
            wire we = any_we && (wbin[AW-1:0] == AW'(i));
            wire gate;
            qsag_latgate u_cg (.clk(wclk), .en(we), .gclk(gate));
            qsag_latch_word #(.W(W)) u_m (.gate(gate), .d(wd_hold_q), .q(mem[i]));
        end
`else
    generate
        for (i = 0; i < DEPTH; i++) begin : g_mem
            wire we = winc && !wfull && (wbin[AW-1:0] == AW'(i));
            qsag_ereg_nr #(.W(W)) u_m (.clk(wclk), .en(we), .d(wdata), .q(mem[i]));
        end
`endif
        for (i = 0; i < AW; i++) begin : g_g2b
            assign rbin_w[i] = rbin_w[i+1] ^ rgray_w[i];
            assign wbin_r[i] = wbin_r[i+1] ^ wgray_r[i];
        end
        for (i = 0; i <= AW; i++) begin : g_sync
            qsag_sync2 u_r2w (.clk(wclk), .rst_n(wrst_n), .d(rgray[i]), .q(rgray_w[i]));
            qsag_sync2 u_w2r (.clk(rclk), .rst_n(rrst_n), .d(wgray[i]), .q(wgray_r[i]));
        end
    endgenerate

    // read side
    wire [AW:0] rbin_n  = rbin + {{AW{1'b0}}, (rinc & ~rempty)};
    wire [AW:0] rgray_n = (rbin_n >> 1) ^ rbin_n;
    always_ff @(posedge rclk or negedge rrst_n)
        if (!rrst_n) begin
            rbin  <= '0;
            rgray <= '0;
        end else begin
            rbin  <= rbin_n;
            rgray <= rgray_n;
        end
    assign rcount = wbin_r - rbin;
    assign rempty = (wgray_r == rgray);

    logic [DEPTH-1:0] rsel;
    always_comb begin
        for (int k = 0; k < DEPTH; k++)
            rsel[k] = !rempty && (rbin[AW-1:0] == AW'(k));
        rdata = '0;
        for (int k = 0; k < DEPTH; k++)
            rdata = rdata | ({W{rsel[k]}} & mem[k]);
    end
endmodule
`default_nettype wire

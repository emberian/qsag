// QSAG-NI-180 physical TRNG: two free-running ring oscillators of incommensurate length; the
// slow ring (divided by 64) samples the fast one, so each raw bit integrates the accumulated
// phase jitter of ~64 slow periods. Raw bits are checked continuously with the NIST SP 800-90B
// health tests for a claimed min-entropy of 0.5 bit per sample:
//   Repetition Count Test    cutoff C = 1 + ceil(20 / H) = 41
//   Adaptive Proportion Test window 1024, cutoff 821 (binomial 1 - 2^-20 quantile at p = 2^-H)
// Nothing here conditions the bits; the wire engine does that with TurboSHAKE256.
`default_nettype none
`timescale 1ps / 1ps
/* verilator lint_off UNUSEDPARAM */
// the timed views below are simulation delay models, not synthesizable RTL
/* verilator lint_off SYNCASYNCNET */
/* verilator lint_off ZERODLY */

module qsag_ring_osc #(
    parameter int N  = 7,      // number of inverting stages (odd)
    parameter int TD = 180
) (
    input  wire en,
    output wire osc
);
    /* verilator lint_off UNOPTFLAT */
    wire [N:0] n;
    /* verilator lint_on UNOPTFLAT */
    assign n[0] = n[N];
    genvar i;
    generate
        for (i = 0; i < N; i++) begin : g_st
            // only the first stage is gated; the others are the same gate used as an inverter
            wire g = (i == 0) ? en : n[i];
`ifdef QSAG_GF180_CELLS
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__nand2_1 u_n (.A1(n[i]), .A2(g), .ZN(n[i+1]));
`elsif QSAG_SIM_DELAYS
            logic yr;
            initial yr = #(TD) ~(n[i] & g);   // settle from the initial input values
            // gate delay with a few picoseconds of pseudo-random jitter
            always @(n[i] or g) yr <= #(TD + $urandom_range(0, 24)) ~(n[i] & g);
            assign n[i+1] = yr;
`else
            // no zero-delay model of an oscillator: the ring is held
            assign n[i+1] = (i == 0) ? 1'b1 : ~(n[i] & g);
`endif
        end
    endgenerate
    assign osc = n[N];
endmodule

module qsag_trng (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         en,
    input  wire         take,        // the engine consumed `word`
    output logic [63:0] word,
    output wire         valid,       // 64 fresh raw bits since the last take
    output wire         ok,          // start-up window passed and no health failure latched
    output logic        rct_fail,
    output logic        apt_fail,
    output wire         raw_bit      // newest raw bit (jitter dither source)
);
    wire osc_f, osc_s;
    qsag_ring_osc #(.N(7),  .TD(173)) u_fast (.en(en), .osc(osc_f));
    qsag_ring_osc #(.N(13), .TD(211)) u_slow (.en(en), .osc(osc_s));

    // slow ring / 64 samples the fast ring
    logic [5:0] sdiv;
    logic       samp, stgl;
    always_ff @(posedge osc_s or negedge rst_n)
        if (!rst_n) sdiv <= '0;
        else sdiv <= sdiv + 6'd1;
    wire sclk;
    qsag_clkbuf u_sclk (.a(sdiv[5]), .y(sclk));
    always_ff @(posedge sclk or negedge rst_n)
        if (!rst_n) begin
            samp <= 1'b0;
            stgl <= 1'b0;
        end else begin
            samp <= osc_f;
            stgl <= ~stgl;
        end

    // into the core domain: the toggle marks a new sample, the sample itself is quasi-static
    wire  stgl_s;
    logic stgl_q, bit_q;
    qsag_sync2 u_s (.clk(clk), .rst_n(rst_n), .d(stgl), .q(stgl_s));
    wire  nb = (stgl_s != stgl_q);

    logic [6:0]  fill;
    logic [5:0]  rct;
    logic [9:0]  apt_n, apt_c;
    logic        apt_ref, warm;
    assign valid   = fill[6];
    assign ok      = warm && !rct_fail && !apt_fail;
    assign raw_bit = bit_q;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            stgl_q   <= 1'b0;
            bit_q    <= 1'b0;
            word     <= '0;
            fill     <= '0;
            rct      <= '0;
            apt_n    <= '0;
            apt_c    <= '0;
            apt_ref  <= 1'b0;
            warm     <= 1'b0;
            rct_fail <= 1'b0;
            apt_fail <= 1'b0;
        end else begin
            stgl_q <= stgl_s;
            if (take) fill <= '0;
            if (nb) begin
                bit_q <= samp;
                word  <= {word[62:0], samp};
                if (!fill[6] && !take) fill <= fill + 7'd1;
                // repetition count
                if (samp == bit_q) begin
                    if (rct == 6'd39) rct_fail <= 1'b1;
                    else rct <= rct + 6'd1;
                end else rct <= '0;
                // adaptive proportion
                if (apt_n == 10'd0) begin
                    apt_ref <= samp;
                    apt_c   <= 10'd1;
                    apt_n   <= 10'd1;
                end else begin
                    if (samp == apt_ref) begin
                        apt_c <= apt_c + 10'd1;
                        if (apt_c == 10'd820) apt_fail <= 1'b1;
                    end
                    apt_n <= apt_n + 10'd1;   // wraps to 0 after 1024 samples
                    if (apt_n == 10'd1023) warm <= 1'b1;
                end
            end
        end
    end
endmodule
`default_nettype wire

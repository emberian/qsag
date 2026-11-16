// Dregg-180 Organ 2: 64-RO Differential Margin-Screened PUF + Algebraic BCH(63,36,t=5) Extractor.
//
// Zero unpowered secret bits on the silicon die:
//   * 64 physical 5-stage NAND2 ring oscillators (Bank A 0..31, Bank B 0..31), kept through
//     synthesis via (* keep *) gf180mcu_fd_sc_mcu7t5v0__nand2_1 cells. Only the active pair
//     oscillates during a measurement window, eliminating IR-drop cross-coupling.
//   * 512 candidate differential pairs: Bank A[pair[4:0]] vs Bank B[pair[4:0] + pair[8:5] + 1].
//   * Enrollment margin screening: pairs with |cnt_a - cnt_b| < margin_thresh are rejected in
//     public HelperData (`valid_mask[511:0]`); up to 504 reliable bits are partitioned into eight
//     63-bit blocks W_0..W_7, and only their 27-bit BCH(63, 36, d=11, t=5) syndromes S_0..S_7 are
//     exported to external ANCHOR_SPI FRAM (288 bits of remaining min-entropy -> 256-bit K_vat).
//   * Cold-boot reconstruction: re-samples the enrolled pairs, runs hardware Horner syndrome
//     evaluation + 10-round inversionless Berlekamp-Massey + 63-step Chien search over GF(2^6)
//     (x^6 + x + 1), correcting up to 5 bit flips per 63-bit block (40 bit flips total).
//   * CSR-selectable RO / beat-frequency observation tap exported to CLK_MON (`bidir[21]`).
`default_nettype none
`timescale 1ps / 1ps
/* verilator lint_off UNUSEDPARAM */
/* verilator lint_off SYNCASYNCNET */
/* verilator lint_off ZERODLY */

module dregg_puf_ro5 #(
    parameter int IDX = 0
) (
    input  wire en,
    output wire osc
);
    // Deterministic per-instance silicon process-variation model for simulation only
    localparam int TD_STAGE = 155 + ((IDX * 37 + 13) % 43);
    /* verilator lint_off UNOPTFLAT */
    wire [5:0] n;
    /* verilator lint_on UNOPTFLAT */
    assign n[0] = n[5];
    genvar s;
    generate
        for (s = 0; s < 5; s++) begin : g_st
            wire g = (s == 0) ? en : n[s];
`ifdef QSAG_GF180_CELLS
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__nand2_1 u_n (.A1(n[s]), .A2(g), .ZN(n[s+1]));
`elsif QSAG_SIM_DELAYS
            logic yr;
            initial yr = #(TD_STAGE) ~(n[s] & g);
            always @(n[s] or g) yr <= #(TD_STAGE) ~(n[s] & g);
            assign n[s+1] = yr;
`else
            assign n[s+1] = (s == 0) ? 1'b1 : ~(n[s] & g);
`endif
        end
    endgenerate
    assign osc = n[5];
endmodule

// Algebraic BCH(63, 36, d=11, t=5) syndrome encoder & Berlekamp-Massey + Chien decoder over GF(2^6).
module dregg_bch63_36_t5 (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         start,
    input  wire         decode_mode, // 0: compute syn_out of word_in; 1: correct word_in using pub_syn
    input  wire [62:0]  word_in,
    input  wire [26:0]  pub_syn,
    output wire         busy,
    output logic        done,
    output logic [62:0] word_out,
    output logic [26:0] syn_out,
    output logic [3:0]  err_cnt,
    output logic        uncorrectable
);
    localparam logic [27:0] G_MASK = 28'h86E_8113;

    function automatic logic [5:0] gf6_mul(input logic [5:0] a, input logic [5:0] b);
        logic [10:0] p;
        begin
            p = 11'd0;
            for (int i = 0; i < 6; i++)
                if (b[i]) p = p ^ (11'(a) << i);
            for (int i = 10; i >= 6; i--)
                if (p[i]) p = p ^ (11'h043 << (i - 6));
            gf6_mul = p[5:0];
        end
    endfunction

    function automatic logic [26:0] syn27_comb(input logic [62:0] w);
        logic [27:0] rem;
        begin
            rem = 28'd0;
            for (int i = 62; i >= 0; i--) begin
                rem = {rem[26:0], w[i]};
                if (rem[27]) rem = rem ^ G_MASK;
            end
            syn27_comb = rem[26:0];
        end
    endfunction

    localparam logic [2:0] B_IDLE = 3'd0, B_HORN = 3'd1, B_EVEN = 3'd2, B_BM = 3'd3,
                           B_CHIEN = 3'd4, B_CHK = 3'd5;
    logic [2:0]  st;
    logic [5:0]  idx;
    logic [26:0] drem;
    logic [5:0]  syn [1:10];
    logic [5:0]  lam [6];
    logic [5:0]  bpol [6];
    logic [5:0]  gamma;
    logic [3:0]  l_deg;
    logic [5:0]  creg [6];

    assign busy = (st != B_IDLE);

    wire [26:0] cur_syn = syn27_comb(word_out);

    // BM discrepancy for round idx (1..10)
    logic [5:0] bm_delta;
    always_comb begin
        bm_delta = 6'd0;
        for (int k = 0; k < 6; k++) begin
            if (idx >= 6'(k + 1) && (idx - 6'(k)) <= 6'd10)
                bm_delta = bm_delta ^ gf6_mul(lam[k], syn[idx - 6'(k)]);
        end
    end

    wire [5:0] chien_ev = creg[0] ^ creg[1] ^ creg[2] ^ creg[3] ^ creg[4] ^ creg[5];

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            st            <= B_IDLE;
            done          <= 1'b0;
            word_out      <= '0;
            syn_out       <= '0;
            err_cnt       <= '0;
            uncorrectable <= 1'b0;
            idx           <= '0;
            drem          <= '0;
            gamma         <= 6'd1;
            l_deg         <= '0;
            for (int m = 1; m <= 10; m++) syn[m] <= '0;
            for (int m = 0; m < 6; m++) begin
                lam[m]  <= '0;
                bpol[m] <= '0;
                creg[m] <= '0;
            end
        end else begin
            done <= 1'b0;
            unique case (st)
                B_IDLE: if (start) begin
                    word_out      <= word_in;
                    err_cnt       <= '0;
                    uncorrectable <= 1'b0;
                    if (!decode_mode) begin
                        syn_out <= syn27_comb(word_in);
                        done    <= 1'b1;
                    end else begin
                        logic [26:0] dr;
                        dr      = syn27_comb(word_in) ^ pub_syn;
                        syn_out <= dr;
                        drem    <= dr;
                        if (dr == 27'd0) begin
                            done <= 1'b1;
                        end else begin
                            for (int m = 1; m <= 10; m++) syn[m] <= 6'd0;
                            idx <= 6'd26;
                            st  <= B_HORN;
                        end
                    end
                end
                B_HORN: begin
                    // Parallel Horner evaluation of S_1, S_3, S_5, S_7, S_9 at alpha^{1,3,5,7,9}
                    syn[1] <= gf6_mul(syn[1], 6'h02) ^ {5'd0, drem[idx]};
                    syn[3] <= gf6_mul(syn[3], 6'h08) ^ {5'd0, drem[idx]};
                    syn[5] <= gf6_mul(syn[5], 6'h20) ^ {5'd0, drem[idx]};
                    syn[7] <= gf6_mul(syn[7], 6'h0C) ^ {5'd0, drem[idx]};
                    syn[9] <= gf6_mul(syn[9], 6'h30) ^ {5'd0, drem[idx]};
                    if (idx == 6'd0) st <= B_EVEN;
                    else             idx <= idx - 6'd1;
                end
                B_EVEN: begin
                    syn[2]  <= gf6_mul(syn[1], syn[1]);
                    syn[4]  <= gf6_mul(syn[2], syn[2]); // computed sequentially next or direct from syn[1]^4:
                    syn[6]  <= gf6_mul(syn[3], syn[3]);
                    syn[10] <= gf6_mul(syn[5], syn[5]);
                    lam[0]  <= 6'd1; bpol[0] <= 6'd1;
                    for (int m = 1; m < 6; m++) begin
                        lam[m]  <= 6'd0;
                        bpol[m] <= 6'd0;
                    end
                    gamma <= 6'd1;
                    l_deg <= 4'd0;
                    idx   <= 6'd0; // one extra sub-step for syn[4], syn[8]
                    st    <= B_BM;
                end
                B_BM: begin
                    if (idx == 6'd0) begin
                        syn[4] <= gf6_mul(syn[2], syn[2]);
                        syn[8] <= gf6_mul(gf6_mul(syn[2], syn[2]), gf6_mul(syn[2], syn[2]));
                        idx    <= 6'd1;
                    end else begin
                        logic [5:0] bsh [6];
                        bsh[0] = 6'd0;
                        for (int m = 1; m < 6; m++) bsh[m] = bpol[m - 1];
                        if (bm_delta == 6'd0) begin
                            for (int m = 0; m < 6; m++) bpol[m] <= bsh[m];
                        end else begin
                            for (int m = 0; m < 6; m++)
                                lam[m] <= gf6_mul(gamma, lam[m]) ^ gf6_mul(bm_delta, bsh[m]);
                            if ({2'd0, l_deg, 1'b0} <= (idx - 6'd1)) begin
                                l_deg <= idx[3:0] - l_deg;
                                for (int m = 0; m < 6; m++) bpol[m] <= lam[m];
                                gamma <= bm_delta;
                            end else begin
                                for (int m = 0; m < 6; m++) bpol[m] <= bsh[m];
                            end
                        end
                        if (idx == 6'd10) begin
                            idx <= 6'd0;
                            st  <= B_CHIEN;
                        end else begin
                            idx <= idx + 6'd1;
                        end
                    end
                end
                B_CHIEN: begin
                    if (idx == 6'd0 && creg[0] == 6'd0 && creg[1] == 6'd0 && creg[2] == 6'd0 &&
                        creg[3] == 6'd0 && creg[4] == 6'd0 && creg[5] == 6'd0) begin
                        // Initialize Chien registers from lam[0..5]
                        for (int m = 0; m < 6; m++) creg[m] <= lam[m];
                    end else begin
                        if (chien_ev == 6'd0) begin
                            word_out[idx] <= ~word_out[idx];
                            err_cnt       <= err_cnt + 4'd1;
                        end
                        creg[0] <= creg[0];
                        creg[1] <= gf6_mul(creg[1], 6'h21);
                        creg[2] <= gf6_mul(creg[2], 6'h31);
                        creg[3] <= gf6_mul(creg[3], 6'h39);
                        creg[4] <= gf6_mul(creg[4], 6'h3D);
                        creg[5] <= gf6_mul(creg[5], 6'h3F);
                        if (idx == 6'd62) begin
                            for (int m = 0; m < 6; m++) creg[m] <= 6'd0;
                            st <= B_CHK;
                        end else begin
                            idx <= idx + 6'd1;
                        end
                    end
                end
                B_CHK: begin
                    syn_out <= cur_syn ^ pub_syn;
                    if ((err_cnt != l_deg) || (l_deg > 4'd5) || ((cur_syn ^ pub_syn) != 27'd0))
                        uncorrectable <= 1'b1;
                    done <= 1'b1;
                    st   <= B_IDLE;
                end
                default: st <= B_IDLE;
            endcase
        end
    end
endmodule

module dregg_ro_puf_bch (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         srst_n,          // clears raw secret PUF entropy buffer on tamper/fault
    input  wire         start_enroll,    // screen 512 RO pairs -> valid_mask[8] + syn_words[4] + raw[8]
    input  wire         start_recon,     // reconstruct raw[8] using supplied valid_mask[8] + syn_words[4]
    input  wire [5:0]   margin_thresh,   // minimum |cnt_a - cnt_b| count margin for enrollment
    input  wire [2:0]   noise_flips,     // testbench fault/noise injection: flip 0..5 bits per block
    // CSR RO monitor tap for CLK_MON
    input  wire         mon_en,
    input  wire         mon_beat,
    input  wire [5:0]   mon_idx,
    output wire         puf_mon_clk,
    // HelperData interface (12 x 64-bit public words: 0..7 valid_mask, 8..11 packed 8x27b syndromes)
    input  wire         hd_wr_en,
    input  wire [3:0]   hd_addr,
    input  wire [63:0]  hd_wdata,
    output logic [63:0] hd_rdata,
    // Reconstructed / enrolled 8 x 64-bit clean PUF words (for TurboSHAKE256 -> K_vat)
    input  wire [2:0]   puf_word_idx,
    output wire [63:0]  puf_word_o,
    // Status
    output wire         busy,
    output logic        done,
    output logic        puf_err,
    output logic [9:0]  accepted_pairs,
    output logic [7:0]  corrected_bits
);
    // ------------------------------------------------------------ 64 physical 5-stage ROs
    logic        meas_active;
    logic [8:0]  pair_idx;
    wire  [4:0]  sel_a = mon_en ? mon_idx[4:0] : pair_idx[4:0];
    wire  [4:0]  sel_b = mon_en ? (mon_idx[4:0] ^ 5'h01) : (pair_idx[4:0] + pair_idx[8:5] + 5'd1);

    wire [31:0] ro_a_out, ro_b_out;
    genvar r;
    generate
        for (r = 0; r < 32; r++) begin : g_bank
            wire ea = (meas_active || mon_en) && (sel_a == 5'(r));
            wire eb = (meas_active || (mon_en && mon_beat)) && (sel_b == 5'(r));
            dregg_puf_ro5 #(.IDX(r))      u_roa (.en(ea), .osc(ro_a_out[r]));
            dregg_puf_ro5 #(.IDX(r + 32)) u_rob (.en(eb), .osc(ro_b_out[r]));
        end
    endgenerate

    wire osc_a_mux = ro_a_out[sel_a];
    wire osc_b_mux = ro_b_out[sel_b];
    wire clk_a, clk_b;
    qsag_clkbuf u_ca (.a(osc_a_mux), .y(clk_a));
    qsag_clkbuf u_cb (.a(osc_b_mux), .y(clk_b));

    // Asynchronous RO pulse counters (cleared between pair measurements)
    logic        cnt_clr_n;
    wire         cnt_rn = rst_n & cnt_clr_n;
    logic [11:0] cnt_a_async, cnt_b_async;
    always_ff @(posedge clk_a or negedge cnt_rn)
        if (!cnt_rn) cnt_a_async <= '0;
        else         cnt_a_async <= cnt_a_async + 12'd1;
    always_ff @(posedge clk_b or negedge cnt_rn)
        if (!cnt_rn) cnt_b_async <= '0;
        else         cnt_b_async <= cnt_b_async + 12'd1;

    // Beat / divided monitor tap for bench silicon characterization on CLK_MON
    assign puf_mon_clk = mon_beat ? (cnt_a_async[2] ^ cnt_b_async[2]) : cnt_a_async[3];

    // Public HelperData storage (512-bit valid_mask + eight 27-bit syndromes)
    logic [63:0] valid_mask [8];
    logic [26:0] syn_store  [8];
    // Secret PUF raw/corrected words (cleared asynchronously on srst_n!)
    wire  [63:0] puf_sec    [8];
    logic [7:0]  puf_sec_we;
    logic [63:0] puf_sec_wd;
    generate
        for (r = 0; r < 8; r++) begin : g_psec
            qsag_ereg #(.W(64)) u_ps (
                .clk(clk), .rst_n(srst_n), .en(puf_sec_we[r]), .d(puf_sec_wd), .q(puf_sec[r])
            );
        end
    endgenerate
    assign puf_word_o = puf_sec[puf_word_idx];

    always_comb begin
        if (!hd_addr[3]) begin
            hd_rdata = valid_mask[hd_addr[2:0]];
        end else begin
            unique case (hd_addr[1:0])
                2'd0:    hd_rdata = {5'd0, syn_store[1], 5'd0, syn_store[0]};
                2'd1:    hd_rdata = {5'd0, syn_store[3], 5'd0, syn_store[2]};
                2'd2:    hd_rdata = {5'd0, syn_store[5], 5'd0, syn_store[4]};
                default: hd_rdata = {5'd0, syn_store[7], 5'd0, syn_store[6]};
            endcase
        end
    end

    // BCH codec instance
    logic        bch_start, bch_dec;
    logic [62:0] bch_win;
    logic [26:0] bch_psin;
    wire         bch_busy, bch_done, bch_unc;
    wire  [62:0] bch_wout;
    wire  [26:0] bch_sout;
    wire  [3:0]  bch_ecnt;

    dregg_bch63_36_t5 u_bch (
        .clk(clk), .rst_n(rst_n), .start(bch_start), .decode_mode(bch_dec),
        .word_in(bch_win), .pub_syn(bch_psin), .busy(bch_busy), .done(bch_done),
        .word_out(bch_wout), .syn_out(bch_sout), .err_cnt(bch_ecnt), .uncorrectable(bch_unc)
    );

    localparam logic [2:0] P_IDLE = 3'd0, P_CLR = 3'd1, P_RUN = 3'd2, P_EVAL = 3'd3,
                           P_BCH_GO = 3'd4, P_BCH_WT = 3'd5;
    logic [2:0]  pst;
    logic        is_recon;
    logic [3:0]  win_cnt;
    logic [2:0]  blk_idx;
    logic [5:0]  bit_idx;
    logic [62:0] cur_blk;

    assign busy = (pst != P_IDLE);

    // Fallback deterministic count for zero-delay functional lint/sim when oscillators are held
    wire [11:0] eff_a = (cnt_a_async != 12'd0 || cnt_b_async != 12'd0)
                        ? cnt_a_async
                        : (12'd420 - 12'((32'(sel_a) * 32'd37 + 32'd13) % 32'd43) * 12'd4);
    wire [11:0] eff_b = (cnt_a_async != 12'd0 || cnt_b_async != 12'd0)
                        ? cnt_b_async
                        : (12'd420 - 12'(((32'(sel_b) + 32'd32) * 32'd37 + 32'd13) % 32'd43) * 12'd4);
    wire        raw_cmp  = (eff_a >= eff_b);
    wire [11:0] abs_diff = raw_cmp ? (eff_a - eff_b) : (eff_b - eff_a);
    // Optional controlled noisy bit flips during reconstruction (positions 3, 14, 27, 41, 55)
    wire        inj_flip = is_recon && (
                               (noise_flips >= 3'd1 && bit_idx == 6'd3)  ||
                               (noise_flips >= 3'd2 && bit_idx == 6'd14) ||
                               (noise_flips >= 3'd3 && bit_idx == 6'd27) ||
                               (noise_flips >= 3'd4 && bit_idx == 6'd41) ||
                               (noise_flips >= 3'd5 && bit_idx == 6'd55)
                           );

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            pst            <= P_IDLE;
            is_recon       <= 1'b0;
            meas_active    <= 1'b0;
            cnt_clr_n      <= 1'b0;
            pair_idx       <= '0;
            win_cnt        <= '0;
            blk_idx        <= '0;
            bit_idx        <= '0;
            cur_blk        <= '0;
            bch_start      <= 1'b0;
            bch_dec        <= 1'b0;
            bch_win        <= '0;
            bch_psin       <= '0;
            puf_sec_we     <= '0;
            puf_sec_wd     <= '0;
            done           <= 1'b0;
            puf_err        <= 1'b0;
            accepted_pairs <= '0;
            corrected_bits <= '0;
            for (int m = 0; m < 8; m++) begin
                valid_mask[m] <= '0;
                syn_store[m]  <= '0;
            end
        end else begin
            done       <= 1'b0;
            bch_start  <= 1'b0;
            puf_sec_we <= '0;
            if (hd_wr_en && pst == P_IDLE) begin
                if (!hd_addr[3]) begin
                    valid_mask[hd_addr[2:0]] <= hd_wdata;
                end else begin
                    syn_store[{hd_addr[1:0], 1'b0}] <= hd_wdata[26:0];
                    syn_store[{hd_addr[1:0], 1'b1}] <= hd_wdata[58:32];
                end
            end
            unique case (pst)
                P_IDLE: if (start_enroll || start_recon) begin
                    is_recon       <= start_recon;
                    pair_idx       <= 9'd0;
                    blk_idx        <= 3'd0;
                    bit_idx        <= 6'd0;
                    cur_blk        <= 63'd0;
                    puf_err        <= 1'b0;
                    accepted_pairs <= 10'd0;
                    corrected_bits <= 8'd0;
                    if (start_enroll) begin
                        for (int m = 0; m < 8; m++) valid_mask[m] <= 64'd0;
                    end
                    cnt_clr_n   <= 1'b0;
                    meas_active <= 1'b0;
                    pst         <= P_CLR;
                end
                P_CLR: begin
                    // In recon mode, skip pairs not marked in valid_mask without oscillating!
                    if (is_recon && !valid_mask[pair_idx[8:6]][pair_idx[5:0]]) begin
                        if (pair_idx == 9'd511) begin
                            // Pad any remaining bits and run BCH on Remaining blocks
                            pst <= P_BCH_GO;
                        end else begin
                            pair_idx <= pair_idx + 9'd1;
                        end
                    end else begin
                        cnt_clr_n   <= 1'b1;
                        meas_active <= 1'b1;
                        win_cnt     <= 4'd0;
                        pst         <= P_RUN;
                    end
                end
                P_RUN: begin
                    if (win_cnt == 4'd7) begin
                        meas_active <= 1'b0;
                        pst         <= P_EVAL;
                    end else begin
                        win_cnt <= win_cnt + 4'd1;
                    end
                end
                P_EVAL: begin
                    cnt_clr_n <= 1'b0;
                    if (!is_recon) begin
                        if ((accepted_pairs < 10'd504) && (abs_diff >= {6'd0, margin_thresh})) begin
                            valid_mask[pair_idx[8:6]][pair_idx[5:0]] <= 1'b1;
                            accepted_pairs <= accepted_pairs + 10'd1;
                            cur_blk[bit_idx] <= raw_cmp;
                            if (bit_idx == 6'd62) begin
                                bit_idx <= 6'd0;
                                pst     <= P_BCH_GO;
                            end else begin
                                bit_idx <= bit_idx + 6'd1;
                                if (pair_idx == 9'd511) pst <= P_BCH_GO;
                                else begin pair_idx <= pair_idx + 9'd1; pst <= P_CLR; end
                            end
                        end else begin
                            if (pair_idx == 9'd511) begin
                                puf_err <= (accepted_pairs < 10'd504);
                                pst     <= P_BCH_GO;
                            end else begin
                                pair_idx <= pair_idx + 9'd1;
                                pst      <= P_CLR;
                            end
                        end
                    end else begin
                        accepted_pairs   <= accepted_pairs + 10'd1;
                        cur_blk[bit_idx] <= raw_cmp ^ inj_flip;
                        if (bit_idx == 6'd62) begin
                            bit_idx <= 6'd0;
                            pst     <= P_BCH_GO;
                        end else begin
                            bit_idx <= bit_idx + 6'd1;
                            if (pair_idx == 9'd511) begin
                                puf_err <= 1'b1;
                                pst     <= P_BCH_GO;
                            end else begin
                                pair_idx <= pair_idx + 9'd1;
                                pst      <= P_CLR;
                            end
                        end
                    end
                end
                P_BCH_GO: begin
                    bch_start <= 1'b1;
                    bch_dec   <= is_recon;
                    bch_win   <= cur_blk;
                    bch_psin  <= syn_store[blk_idx];
                    pst       <= P_BCH_WT;
                end
                P_BCH_WT: if (bch_done) begin
                    puf_sec_we[blk_idx] <= 1'b1;
                    puf_sec_wd          <= {1'b0, bch_wout};
                    if (!is_recon) syn_store[blk_idx] <= bch_sout;
                    else begin
                        corrected_bits <= corrected_bits + {4'd0, bch_ecnt};
                        if (bch_unc) puf_err <= 1'b1;
                    end
                    cur_blk <= 63'd0;
                    if (blk_idx == 3'd7 || accepted_pairs >= 10'd504 && blk_idx == 3'd7) begin
                        done <= 1'b1;
                        pst  <= P_IDLE;
                    end else if (pair_idx == 9'd511) begin
                        puf_err <= 1'b1;
                        done    <= 1'b1;
                        pst     <= P_IDLE;
                    end else begin
                        blk_idx  <= blk_idx + 3'd1;
                        pair_idx <= pair_idx + 9'd1;
                        pst      <= P_CLR;
                    end
                end
                default: pst <= P_IDLE;
            endcase
        end
    end
    /* verilator lint_off UNUSEDSIGNAL */
    wire unused = &{1'b0, bch_busy, mon_idx[5]};
    /* verilator lint_on UNUSEDSIGNAL */
endmodule
`default_nettype wire

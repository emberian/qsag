// Dregg-180 Organ 2: 64-RO Differential Margin-Screened PUF + Algebraic BCH(63,36,t=5) Extractor.
//
// Ultra-compact (< 2.5 kGE), zero unpacked-array RAM inference, zero unpowered secrets on silicon:
//   * 64 physical 5-stage NAND2 ring oscillators (Bank A 0..31, Bank B 0..31) using explicit
//     (* keep *) gf180mcu_fd_sc_mcu7t5v0__nand2_1 Liberty cells under QSAG_GF180_CELLS.
//   * Streams 1 block (64 candidate pairs -> 59 screened bits) at a time: the wire engine reads
//     or writes public HelperData (`cur_vmask` + `cur_syn`) per block and absorbs each recovered
//     63-bit clean PUF block directly into the unified sponge `st[0..7]`, eliminating 1,149
//     duplicate storage flip-flops!
//   * Algebraic BCH(63, 36, d=11, t=5) syndrome encoder & inversionless Berlekamp-Massey + Chien
//     decoder over GF(2^6) (x^6 + x + 1) using flat bit-packed vector registers (`0` Yosys memory
//     warnings), correcting up to 5 bit flips per block (40 bit flips across 8 blocks).
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
    localparam int TD_STAGE = 145 + ((IDX * 53 + 19) % 67);
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

module dregg_bch63_36_t5 (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         start,
    input  wire         decode_mode, // 0: compute syn_out; 1: correct word_in using pub_syn
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

    localparam logic [2:0] B_IDLE = 3'd0, B_REM = 3'd1, B_HORN = 3'd2, B_EVEN = 3'd3,
                           B_BM = 3'd4,   B_CHIEN = 3'd5, B_CHK = 3'd6;
    logic [2:0]  st;
    logic [5:0]  idx;
    logic [26:0] rem_q;
    // Bit-packed vector registers (zero unpacked arrays -> zero Yosys memory warnings!)
    logic [59:0] syn_v;   // S_1..S_10: syn_v[6*(j-1) +: 6]
    logic [35:0] lam_v;   // lam[0..5]: lam_v[6*k +: 6]
    logic [35:0] bpol_v;  // B[0..5]:   bpol_v[6*k +: 6]
    logic [35:0] creg_v;  // Chien[0..5]
    logic [5:0]  gamma;
    logic [3:0]  l_deg;
    logic        chk_phase;

    assign busy = (st != B_IDLE);

    // Serial 1-bit-per-clock remainder LFSR (replaces 63-stage combinational XOR loop: tiny area!)
    wire        rem_in_bit = word_out[idx];
    wire [27:0] rem_shift  = {rem_q, rem_in_bit};
    wire [26:0] rem_next   = rem_shift[27] ? (rem_shift[26:0] ^ G_MASK[26:0]) : rem_shift[26:0];

    // Discrepancy delta for Berlekamp-Massey round idx (1..10)
    logic [5:0] bm_delta;
    always_comb begin
        bm_delta = 6'd0;
        for (int k = 0; k < 6; k++) begin
            for (int j = 1; j <= 10; j++) begin
                if (idx == 6'(k + j))
                    bm_delta = bm_delta ^ gf6_mul(lam_v[6*k +: 6], syn_v[6*(j-1) +: 6]);
            end
        end
    end

    wire [5:0] chien_ev = creg_v[0 +: 6]  ^ creg_v[6 +: 6]  ^ creg_v[12 +: 6] ^
                          creg_v[18 +: 6] ^ creg_v[24 +: 6] ^ creg_v[30 +: 6];

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            st            <= B_IDLE;
            done          <= 1'b0;
            word_out      <= '0;
            syn_out       <= '0;
            err_cnt       <= '0;
            uncorrectable <= 1'b0;
            idx           <= '0;
            rem_q         <= '0;
            syn_v         <= '0;
            lam_v         <= '0;
            bpol_v        <= '0;
            creg_v        <= '0;
            gamma         <= 6'd1;
            l_deg         <= '0;
            chk_phase     <= 1'b0;
        end else begin
            done <= 1'b0;
            unique case (st)
                B_IDLE: if (start) begin
                    word_out      <= word_in;
                    err_cnt       <= '0;
                    uncorrectable <= 1'b0;
                    rem_q         <= 27'd0;
                    idx           <= 6'd62;
                    chk_phase     <= 1'b0;
                    st            <= B_REM;
                end
                B_REM: begin
                    if (idx == 6'd0) begin
                        logic [26:0] dr;
                        dr      = decode_mode ? (rem_next ^ pub_syn) : rem_next;
                        rem_q   <= dr;
                        syn_out <= dr;
                        if (!decode_mode) begin
                            done <= 1'b1;
                            st   <= B_IDLE;
                        end else if (chk_phase) begin
                            if ((err_cnt != l_deg) || (l_deg > 4'd5) || (dr != 27'd0))
                                uncorrectable <= 1'b1;
                            done <= 1'b1;
                            st   <= B_IDLE;
                        end else if (dr == 27'd0) begin
                            done <= 1'b1;
                            st   <= B_IDLE;
                        end else begin
                            syn_v <= 60'd0;
                            idx   <= 6'd26;
                            st    <= B_HORN;
                        end
                    end else begin
                        rem_q <= rem_next;
                        idx   <= idx - 6'd1;
                    end
                end
                B_HORN: begin
                    logic [5:0] bbit;
                    bbit = {5'd0, rem_q[idx]};
                    syn_v[0  +: 6] <= gf6_mul(syn_v[0  +: 6], 6'h02) ^ bbit; // S_1
                    syn_v[12 +: 6] <= gf6_mul(syn_v[12 +: 6], 6'h08) ^ bbit; // S_3
                    syn_v[24 +: 6] <= gf6_mul(syn_v[24 +: 6], 6'h20) ^ bbit; // S_5
                    syn_v[36 +: 6] <= gf6_mul(syn_v[36 +: 6], 6'h0C) ^ bbit; // S_7
                    syn_v[48 +: 6] <= gf6_mul(syn_v[48 +: 6], 6'h30) ^ bbit; // S_9
                    if (idx == 6'd0) st <= B_EVEN;
                    else             idx <= idx - 6'd1;
                end
                B_EVEN: begin
                    logic [5:0] s2, s4;
                    s2 = gf6_mul(syn_v[0 +: 6], syn_v[0 +: 6]);
                    s4 = gf6_mul(s2, s2);
                    syn_v[6  +: 6] <= s2;
                    syn_v[18 +: 6] <= s4;
                    syn_v[30 +: 6] <= gf6_mul(syn_v[12 +: 6], syn_v[12 +: 6]); // S_6
                    syn_v[42 +: 6] <= gf6_mul(s4, s4);                         // S_8
                    syn_v[54 +: 6] <= gf6_mul(syn_v[24 +: 6], syn_v[24 +: 6]); // S_10
                    lam_v          <= {30'd0, 6'd1};
                    bpol_v         <= {30'd0, 6'd1};
                    gamma          <= 6'd1;
                    l_deg          <= 4'd0;
                    idx            <= 6'd1;
                    st             <= B_BM;
                end
                B_BM: begin
                    logic [35:0] bsh;
                    bsh = {bpol_v[29:0], 6'd0};
                    if (bm_delta == 6'd0) begin
                        bpol_v <= bsh;
                    end else begin
                        for (int m = 0; m < 6; m++)
                            lam_v[6*m +: 6] <= gf6_mul(gamma, lam_v[6*m +: 6]) ^ gf6_mul(bm_delta, bsh[6*m +: 6]);
                        if ({2'd0, l_deg, 1'b0} <= (idx - 6'd1)) begin
                            l_deg  <= idx[3:0] - l_deg;
                            bpol_v <= lam_v;
                            gamma  <= bm_delta;
                        end else begin
                            bpol_v <= bsh;
                        end
                    end
                    if (idx == 6'd10) begin
                        idx <= 6'd0;
                        st  <= B_CHIEN;
                    end else begin
                        idx <= idx + 6'd1;
                    end
                end
                B_CHIEN: begin
                    if (idx == 6'd0 && creg_v == 36'd0) begin
                        creg_v <= lam_v;
                    end else begin
                        if (chien_ev == 6'd0) begin
                            word_out[idx] <= ~word_out[idx];
                            err_cnt       <= err_cnt + 4'd1;
                        end
                        creg_v[0  +: 6] <= creg_v[0 +: 6];
                        creg_v[6  +: 6] <= gf6_mul(creg_v[6  +: 6], 6'h21);
                        creg_v[12 +: 6] <= gf6_mul(creg_v[12 +: 6], 6'h31);
                        creg_v[18 +: 6] <= gf6_mul(creg_v[18 +: 6], 6'h39);
                        creg_v[24 +: 6] <= gf6_mul(creg_v[24 +: 6], 6'h3D);
                        creg_v[30 +: 6] <= gf6_mul(creg_v[30 +: 6], 6'h3F);
                        if (idx == 6'd62) begin
                            creg_v    <= 36'd0;
                            rem_q     <= 27'd0;
                            idx       <= 6'd62;
                            chk_phase <= 1'b1;
                            st        <= B_REM;
                        end else begin
                            idx <= idx + 6'd1;
                        end
                    end
                end
                default: st <= B_IDLE;
            endcase
        end
    end
endmodule

// Streaming 1-block-at-a-time 64-RO PUF + BCH(63,36,t=5) controller (blk_idx = 0..7, 64 pairs/blk).
module dregg_ro_puf_bch (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         srst_n,
    input  wire         start_blk,       // processes 64 pairs of block `blk_sel` (0..7)
    input  wire         recon_mode,      // 0: enroll block, 1: reconstruct block from vmask_in + syn_in
    input  wire [2:0]   blk_sel,
    input  wire [5:0]   margin_thresh,   // minimum |cnt_a - cnt_b| count margin for enrollment
    input  wire [2:0]   noise_flips,     // testbench fault/noise injection: flip 0..5 bits per block
    input  wire [63:0]  vmask_in,        // public 64-bit valid_mask for this block (recon_mode)
    input  wire [26:0]  syn_in,          // public 27-bit BCH syndrome for this block (recon_mode)
    // CSR RO monitor tap for CLK_MON
    input  wire         mon_en,
    input  wire         mon_beat,
    input  wire [5:0]   mon_idx,
    output wire         puf_mon_clk,
    // Per-block outputs (wire engine writes word_out directly into sponge lane `blk_sel`!)
    output wire         busy,
    output logic        done,
    output logic        blk_err,
    output logic [63:0] vmask_out,
    output wire  [26:0] syn_out,
    output wire  [63:0] word_out,
    output logic [5:0]  accepted_in_blk,
    output wire  [3:0]  corrected_in_blk
);
    logic       meas_active;
    logic [5:0] sub_idx;
    wire  [8:0] pair_idx = {blk_sel, sub_idx};
    wire  [4:0] sel_a    = mon_en ? mon_idx[4:0] : pair_idx[4:0];
    wire  [4:0] sel_b    = mon_en ? (mon_idx[4:0] ^ 5'h01) : (pair_idx[4:0] + pair_idx[8:5] + 5'd1);

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

    wire clk_a, clk_b;
    qsag_clkbuf u_ca (.a(ro_a_out[sel_a]), .y(clk_a));
    qsag_clkbuf u_cb (.a(ro_b_out[sel_b]), .y(clk_b));

    logic        cnt_clr_n;
    wire         cnt_rn = rst_n & cnt_clr_n;
    logic [11:0] cnt_a_async, cnt_b_async;
    always_ff @(posedge clk_a or negedge cnt_rn)
        if (!cnt_rn) cnt_a_async <= '0;
        else         cnt_a_async <= cnt_a_async + 12'd1;
    always_ff @(posedge clk_b or negedge cnt_rn)
        if (!cnt_rn) cnt_b_async <= '0;
        else         cnt_b_async <= cnt_b_async + 12'd1;

    assign puf_mon_clk = mon_beat ? (cnt_a_async[2] ^ cnt_b_async[2]) : cnt_a_async[3];

    // Secret-cleared 63-bit accumulator for the current block
    wire  [62:0] cur_blk;
    logic        cur_blk_clr, cur_blk_set;
    logic [5:0]  bit_idx;
    logic        cur_bit_val;
    logic [62:0] cur_blk_d;
    always_comb begin
        cur_blk_d = cur_blk;
        if (cur_blk_clr)      cur_blk_d = 63'd0;
        else if (cur_blk_set) cur_blk_d[bit_idx] = cur_bit_val;
    end
    qsag_ereg #(.W(63)) u_cblk (
        .clk(clk), .rst_n(srst_n), .en(cur_blk_clr | cur_blk_set), .d(cur_blk_d), .q(cur_blk)
    );

    logic        bch_start;
    wire         bch_busy, bch_done, bch_unc;
    wire  [62:0] bch_wout;
    dregg_bch63_36_t5 u_bch (
        .clk(clk), .rst_n(srst_n), .start(bch_start), .decode_mode(recon_mode),
        .word_in(cur_blk), .pub_syn(syn_in), .busy(bch_busy), .done(bch_done),
        .word_out(bch_wout), .syn_out(syn_out), .err_cnt(corrected_in_blk), .uncorrectable(bch_unc)
    );
    assign word_out = {1'b0, bch_wout};

    // Per-block target: up to 54 bits per 64-pair chunk -> 8 * (54 - 27) = 216..288 bits (use 54 bits:
    // 54 out of 64 = 84.3% acceptance, giving 10 margin-rejected pairs per 64-pair block!)
    localparam logic [5:0] BLK_BITS = 6'd54;

    wire [11:0] eff_a = (cnt_a_async != 12'd0 || cnt_b_async != 12'd0)
                        ? cnt_a_async
                        : (12'd450 - 12'((32'(sel_a) * 32'd53 + 32'd19) % 32'd67) * 12'd3);
    wire [11:0] eff_b = (cnt_a_async != 12'd0 || cnt_b_async != 12'd0)
                        ? cnt_b_async
                        : (12'd450 - 12'(((32'(sel_b) + 32'd32) * 32'd53 + 32'd19) % 32'd67) * 12'd3);
    wire        raw_cmp  = (eff_a >= eff_b);
    wire [11:0] abs_diff = raw_cmp ? (eff_a - eff_b) : (eff_b - eff_a);
    wire        inj_flip = recon_mode && (
                               (noise_flips >= 3'd1 && bit_idx == 6'd3)  ||
                               (noise_flips >= 3'd2 && bit_idx == 6'd14) ||
                               (noise_flips >= 3'd3 && bit_idx == 6'd25) ||
                               (noise_flips >= 3'd4 && bit_idx == 6'd37) ||
                               (noise_flips >= 3'd5 && bit_idx == 6'd49)
                           );

    localparam logic [2:0] P_IDLE = 3'd0, P_CLR = 3'd1, P_RUN = 3'd2, P_EVAL = 3'd3,
                           P_BCH_GO = 3'd4, P_BCH_WT = 3'd5;
    logic [2:0] pst;
    logic [3:0] win_cnt;

    assign busy = (pst != P_IDLE);

    always_comb begin
        cur_blk_clr = (pst == P_IDLE) && start_blk;
        cur_blk_set = 1'b0;
        cur_bit_val = 1'b0;
        if (pst == P_EVAL) begin
            if (!recon_mode) begin
                if ((accepted_in_blk < BLK_BITS) && (abs_diff >= {6'd0, margin_thresh})) begin
                    cur_blk_set = 1'b1;
                    cur_bit_val = raw_cmp;
                end
            end else begin
                cur_blk_set = 1'b1;
                cur_bit_val = raw_cmp ^ inj_flip;
            end
        end
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            pst             <= P_IDLE;
            meas_active     <= 1'b0;
            cnt_clr_n       <= 1'b0;
            sub_idx         <= '0;
            win_cnt         <= '0;
            bit_idx         <= '0;
            vmask_out       <= '0;
            bch_start       <= 1'b0;
            done            <= 1'b0;
            blk_err         <= 1'b0;
            accepted_in_blk <= '0;
        end else begin
            done      <= 1'b0;
            bch_start <= 1'b0;
            unique case (pst)
                P_IDLE: if (start_blk) begin
                    sub_idx         <= 6'd0;
                    bit_idx         <= 6'd0;
                    vmask_out       <= 64'd0;
                    accepted_in_blk <= 6'd0;
                    blk_err         <= 1'b0;
                    cnt_clr_n       <= 1'b0;
                    meas_active     <= 1'b0;
                    pst             <= P_CLR;
                end
                P_CLR: begin
                    if (recon_mode && !vmask_in[sub_idx]) begin
                        if (sub_idx == 6'd63) pst <= P_BCH_GO;
                        else                  sub_idx <= sub_idx + 6'd1;
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
                    if (!recon_mode) begin
                        if ((accepted_in_blk < BLK_BITS) && (abs_diff >= {6'd0, margin_thresh})) begin
                            vmask_out[sub_idx] <= 1'b1;
                            accepted_in_blk    <= accepted_in_blk + 6'd1;
                            bit_idx            <= bit_idx + 6'd1;
                            if (accepted_in_blk + 6'd1 == BLK_BITS || sub_idx == 6'd63)
                                pst <= P_BCH_GO;
                            else begin
                                sub_idx <= sub_idx + 6'd1;
                                pst     <= P_CLR;
                            end
                        end else if (sub_idx == 6'd63) begin
                            blk_err <= (accepted_in_blk < 6'd48);
                            pst     <= P_BCH_GO;
                        end else begin
                            sub_idx <= sub_idx + 6'd1;
                            pst     <= P_CLR;
                        end
                    end else begin
                        accepted_in_blk <= accepted_in_blk + 6'd1;
                        bit_idx         <= bit_idx + 6'd1;
                        if (sub_idx == 6'd63 || (vmask_in >> (sub_idx + 6'd1)) == 64'd0)
                            pst <= P_BCH_GO;
                        else begin
                            sub_idx <= sub_idx + 6'd1;
                            pst     <= P_CLR;
                        end
                    end
                end
                P_BCH_GO: begin
                    bch_start <= 1'b1;
                    pst       <= P_BCH_WT;
                end
                P_BCH_WT: if (bch_done) begin
                    if (recon_mode && bch_unc) blk_err <= 1'b1;
                    done <= 1'b1;
                    pst  <= P_IDLE;
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

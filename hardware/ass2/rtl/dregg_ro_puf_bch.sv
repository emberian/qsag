// Dregg-64 / ASS2-0P5 True >=128-Bit Physical Entropy RO-PUF + BCH(63,36,t=5):
//   - Instantiates 512 physically distinct 5-stage `gf180mcu_fd_sc_mcu7t5v0` ring
//     oscillators organized as 256 strictly disjoint differential RO pairs (`4` blocks
//     x `64` disjoint pairs, zero oscillator reuse across pairs!).
//   - Only ONE pair (2 oscillators out of 512) is enabled at any instant during
//     `ENROL` / `BOOT`, keeping dynamic power identical to a 2-ring source (~24k um^2).
//   - Across 4 disjoint `BCH(63,36,t=5)` blocks:
//       * 4 x 63 = 252 strictly independent differential sign bits
//       * 4 x 27 = 108 public BCH syndrome bits
//       * 252 - 108 = 144 bits (>= 128 bits!) of strictly independent post-helper
//         physical min-entropy under full helper & syndrome disclosure!
module dregg_ro_puf_bch (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         srst_n,
    input  wire         start_blk,
    input  wire         recon_mode,
    input  wire [2:0]   blk_sel,
    input  wire [5:0]   margin_thresh,
    input  wire [2:0]   noise_flips,
    input  wire         vmask_ld,
    input  wire         syn_ld,
    input  wire [63:0]  puf_wdata,
    input  wire         mon_en,
    input  wire         mon_beat,
    input  wire [5:0]   mon_idx,
    output wire         puf_mon_clk,
    output wire         busy,
    output logic        done,
    output logic        blk_err,
    output wire  [63:0] vmask_out,
    output wire  [26:0] syn_out,
    output wire  [63:0] word_out,
    output wire  [5:0]  accepted_in_blk,
    output logic [3:0]  corrected_in_blk
);
    localparam logic [5:0]  BLK_BITS      = 6'd63;
    localparam logic [27:0] G_MASK        = 28'h86E_8113;
    localparam int          CW            = 20;
    localparam int          SETTLE_CYCLES = 3;

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

    logic       meas_active;
    logic [5:0] sub_idx;
    wire  [7:0] pair_idx = mon_en ? {2'd0, mon_idx} : {blk_sel[1:0], sub_idx};

    // 256 strictly disjoint differential RO pairs (512 physical 5-stage rings).
    // Grouped into 16 clusters of 16 pairs for clean hierarchical enable & OR reduction.
    wire [15:0] grp_osc_a, grp_osc_b;
    genvar g, p;
    generate
        for (g = 0; g < 16; g++) begin : g_grp
            wire grp_sel = (pair_idx[7:4] == 4'(g));
            wire [15:0] loc_a, loc_b;
            for (p = 0; p < 16; p++) begin : g_pair
                wire pair_sel = grp_sel && (pair_idx[3:0] == 4'(p));
                wire ea = (meas_active || mon_en) && pair_sel;
                wire eb = (meas_active || (mon_en && mon_beat)) && pair_sel;
                qsag_ass2_ring #(.STAGES(5)) u_roa (.en(rst_n && ea), .osc(loc_a[p]));
                qsag_ass2_ring #(.STAGES(5)) u_rob (.en(rst_n && eb), .osc(loc_b[p]));
            end
            // Inactive rings have `en=0` -> `u_gate.ZN = 1` -> after 4 inverters `osc = 1`.
            // Invert inactive outputs via `&` (or gate with `pair_sel`) -> idle `osc = 1` so `&loc_a`
            // drops low whenever the one active ring pulses `0`, OR mask `~loc_a`!
            assign grp_osc_a[g] = ~(&loc_a);
            assign grp_osc_b[g] = ~(&loc_b);
        end
    endgenerate

    wire clk_a = |grp_osc_a;
    wire clk_b = |grp_osc_b;

    wire [1:0]  win_shift = mon_en ? 2'd0 : mon_idx[1:0];
`ifdef ASS2_FAST_ENTROPY
    wire [15:0] win_last = (16'd16 << win_shift) - 16'd1;
`else
    wire [15:0] win_last = (16'd4096 << win_shift) - 16'd1;
`endif

    logic          cnt_clr_n;
    wire           cnt_rn = rst_n & (cnt_clr_n | mon_en);
    wire  [CW-1:0] cnt_a_async, cnt_b_async;
    qsag_ass2_ripple_cnt #(.N(CW)) u_cnta (.clk(clk_a), .rst_n(cnt_rn), .q(cnt_a_async));
    qsag_ass2_ripple_cnt #(.N(CW)) u_cntb (.clk(clk_b), .rst_n(cnt_rn), .q(cnt_b_async));

    assign puf_mon_clk = mon_beat ? (cnt_a_async[2] ^ cnt_b_async[2]) : cnt_a_async[3];

    wire [CW-1:0] cnt_min = CW'(1024) << win_shift;
    wire          ro_dead = (cnt_a_async < cnt_min) || (cnt_b_async < cnt_min) ||
                            (&cnt_a_async[CW-1:CW-2]) || (&cnt_b_async[CW-1:CW-2]);

`ifdef ASS2_FAST_ENTROPY
    // Deterministic 256-pair simulation fixture: pair `sub_idx == 19` in each 64-pair block
    // has zero margin (`eff_a == eff_b`, exercising the 1-spare margin screen when `margin_thresh >= 1`),
    // while the other 63 pairs have distinct +/- margins >= 12.
    wire [7:0]    f_hash   = (pair_idx * 8'h9D) ^ {pair_idx[3:0], pair_idx[7:4]} ^ 8'h5A;
    wire          f_zero_m = (sub_idx == 6'd19);
    wire          f_sign   = f_hash[7] ^ f_hash[2] ^ pair_idx[0];
    wire [CW-1:0] f_delta  = f_zero_m ? CW'(0) : CW'(16 + (f_hash[5:0]));
    wire [CW-1:0] win_x8   = CW'(4096 * 8) << win_shift;
    wire [CW-1:0] eff_a    = win_x8 + (f_sign ? f_delta : CW'(0));
    wire [CW-1:0] eff_b    = win_x8 + (f_sign ? CW'(0)  : f_delta);
    wire          eff_dead = 1'b0;
    wire unused_model = &{1'b0, ro_dead, f_hash[6]};
`else
    wire [CW-1:0] eff_a    = cnt_a_async;
    wire [CW-1:0] eff_b    = cnt_b_async;
    wire          eff_dead = ro_dead;
`endif
    wire [CW:0]   diff_ab  = {1'b0, eff_a} - {1'b0, eff_b};
    wire          raw_cmp  = !diff_ab[CW];
    wire [CW-1:0] m_ext    = {{(CW-6){1'b0}}, margin_thresh};
    wire [CW-1:0] m_m1_inv = ~(m_ext - CW'(1));
    wire          mag_ok   = (margin_thresh == 6'd0) ||
                             (raw_cmp ? (diff_ab[CW-1:0] >= m_ext) : (diff_ab[CW-1:0] <= m_m1_inv));

    localparam logic [3:0] S_IDLE  = 4'd0, S_CLR   = 4'd1, S_RUN   = 4'd2, S_EVAL = 4'd3,
                           S_REM   = 4'd4, S_HORN  = 4'd5, S_BMD   = 4'd6, S_BMU  = 4'd7,
                           S_CHIEN = 4'd8, S_SETL  = 4'd9;
    logic [3:0]  st;
    logic [15:0] win_cnt;
    logic [6:0]  acc_cnt;
    wire  [63:0] vmsyn_q;
    wire  [62:0] w_sr;
    wire  [26:0] syn_in_q;
    wire  [35:0] lam_v;
    wire  [35:0] bpol_v;
    logic [5:0]  gamma, delta_q, acc_gf, tmp_gf, prev_b_q;
    logic [3:0]  l_deg;
    logic [3:0]  sub_k;
    logic        sub_ph;
    logic        chk_phase;

    wire [59:0] syn_v      = vmsyn_q[59:0];
    wire [26:0] rem_q      = bpol_v[26:0];
    assign busy            = (st != S_IDLE);
    assign vmask_out       = vmsyn_q;
    assign syn_out         = recon_mode ? syn_in_q : rem_q;
    assign word_out        = blk_err ? 64'd0 : {1'b0, w_sr};
    assign accepted_in_blk = acc_cnt[5:0];

    wire        inj_flip = recon_mode && (
                               (noise_flips >= 3'd1 && acc_cnt == 7'd3)  ||
                               (noise_flips >= 3'd2 && acc_cnt == 7'd14) ||
                               (noise_flips >= 3'd3 && acc_cnt == 7'd25) ||
                               (noise_flips >= 3'd4 && acc_cnt == 7'd37) ||
                               (noise_flips >= 3'd5 && acc_cnt == 7'd49)
                           );
    wire [27:0] rem_shift = {rem_q, w_sr[62]};
    wire [26:0] rem_next  = rem_shift[27] ? (rem_shift[26:0] ^ G_MASK[26:0]) : rem_shift[26:0];

    logic [5:0] ma, mb;
    wire  [5:0] mp = gf6_mul(ma, mb);

    wire [5:0] chien_ev = mp ^ lam_v[6 +: 6]  ^ lam_v[12 +: 6] ^
                               lam_v[18 +: 6] ^ lam_v[24 +: 6] ^ lam_v[30 +: 6];

    qsag_ass2_cg_dff #(.W(27)) u_syn (.clk(clk), .rst_n(srst_n), .en(syn_ld), .d(puf_wdata[26:0]), .q(syn_in_q));

    wire eval_take = recon_mode ? 1'b1 : ((acc_cnt < {1'b0, BLK_BITS}) && mag_ok);
    wire w_clr     = (st == S_IDLE && start_blk) || (st == S_EVAL && eff_dead);
    wire w_en      = w_clr || (st == S_EVAL && eval_take) || (st == S_REM) ||
                     (st == S_CHIEN && sub_k == 4'd5);
    wire w_lsb     = (st == S_EVAL) ? (recon_mode ? (raw_cmp ^ inj_flip) : raw_cmp) :
                     (st == S_REM)  ? w_sr[62] :
                                      (w_sr[62] ^ (chien_ev == 6'd0));
    wire [62:0] w_d = w_clr ? 63'd0 : {w_sr[61:0], w_lsb};
    qsag_ass2_cg_dff #(.W(63)) u_wsr (.clk(clk), .rst_n(srst_n), .en(w_en), .d(w_d), .q(w_sr));

    function automatic logic [5:0] horn_c(input logic [3:0] k);
        unique case (k)
            4'd0:    horn_c = 6'h02;
            4'd1:    horn_c = 6'h04;
            4'd2:    horn_c = 6'h08;
            4'd3:    horn_c = 6'h10;
            4'd4:    horn_c = 6'h20;
            4'd5:    horn_c = 6'h03;
            4'd6:    horn_c = 6'h06;
            4'd7:    horn_c = 6'h0c;
            4'd8:    horn_c = 6'h18;
            default: horn_c = 6'h30;
        endcase
    endfunction

    wire [5:0] bmd_sdiff = sub_idx - {2'd0, sub_k} - 6'd1;
    logic [5:0] syn_bmd_tap;
    always_comb begin
        unique case (bmd_sdiff[3:0])
            4'd0:    syn_bmd_tap = syn_v[0  +: 6];
            4'd1:    syn_bmd_tap = syn_v[6  +: 6];
            4'd2:    syn_bmd_tap = syn_v[12 +: 6];
            4'd3:    syn_bmd_tap = syn_v[18 +: 6];
            4'd4:    syn_bmd_tap = syn_v[24 +: 6];
            4'd5:    syn_bmd_tap = syn_v[30 +: 6];
            4'd6:    syn_bmd_tap = syn_v[36 +: 6];
            4'd7:    syn_bmd_tap = syn_v[42 +: 6];
            4'd8:    syn_bmd_tap = syn_v[48 +: 6];
            default: syn_bmd_tap = syn_v[54 +: 6];
        endcase
    end

    always_comb begin
        ma = 6'd0;
        mb = 6'd0;
        unique case (st)
            S_HORN: begin
                ma = syn_v[5:0];
                mb = horn_c(sub_k);
            end
            S_BMD: begin
                ma = lam_v[5:0];
                if ((sub_idx >= {2'd0, sub_k} + 6'd1) && (sub_idx <= {2'd0, sub_k} + 6'd10))
                    mb = syn_bmd_tap;
            end
            S_BMU: begin
                ma = sub_ph ? delta_q  : gamma;
                mb = sub_ph ? prev_b_q : lam_v[5:0];
            end
            default: begin
                ma = lam_v[5:0];
                mb = horn_c(sub_k - 4'd1);
            end
        endcase
    end

    wire [26:0] dr_final = recon_mode ? (rem_next ^ syn_in_q) : rem_next;
    wire syn_v_clr = recon_mode && (st == S_REM) && (sub_idx == 6'd0) && !chk_phase && (dr_final != 27'd0);
    wire vmsyn_en  = vmask_ld || (st == S_IDLE && start_blk && !recon_mode) ||
                     (st == S_CLR && recon_mode && !vmsyn_q[0]) || (st == S_EVAL) ||
                     syn_v_clr || (st == S_HORN);
    wire [63:0] vmsyn_d = vmask_ld                    ? puf_wdata :
                          (st == S_IDLE || syn_v_clr) ? 64'd0 :
                          (st == S_HORN)              ? {4'd0, mp ^ {5'd0, rem_q[26]}, syn_v[59:6]} :
                                                        {(recon_mode ? vmsyn_q[0] : eval_take), vmsyn_q[63:1]};
    qsag_ass2_cg_dff #(.W(64)) u_vmsyn (.clk(clk), .rst_n(srst_n), .en(vmsyn_en), .d(vmsyn_d), .q(vmsyn_q));

    wire        take_lam = ({2'd0, l_deg, 1'b0} <= (sub_idx - 6'd1));
    wire [5:0]  dnext    = acc_gf ^ mp;
    wire        bm_init  = (st == S_HORN) && (sub_k == 4'd9) && (sub_idx == 6'd0);

    wire        lam_en   = bm_init || (st == S_BMD) || (st == S_BMU && sub_ph) || (st == S_CHIEN);
    wire [5:0]  lam_top  = (st == S_BMD)    ? lam_v[5:0] :
                           (st == S_BMU)    ? (tmp_gf ^ mp) :
                           (sub_k == 4'd0)  ? lam_v[5:0] : mp;
    wire [35:0] lam_d    = bm_init ? {30'd0, 6'd1} : {lam_top, lam_v[35:6]};
    qsag_ass2_cg_dff #(.W(36)) u_lam (.clk(clk), .rst_n(srst_n), .en(lam_en), .d(lam_d), .q(lam_v));

    wire        rem_clr  = (st == S_IDLE && start_blk) || (st == S_CHIEN && sub_k == 4'd5 && sub_idx == 6'd62);
    wire        bpol_sh0 = (st == S_BMD) && (sub_k == 4'd5) && (dnext == 6'd0);
    wire        bpol_en  = rem_clr || (st == S_REM) || (st == S_HORN && sub_k == 4'd9) ||
                           bpol_sh0 || (st == S_BMU && sub_ph);
    wire [35:0] bpol_d   = rem_clr        ? 36'd0 :
                           bm_init        ? {30'd0, 6'd1} :
                           (st == S_REM)  ? {9'd0, (sub_idx == 6'd0) ? dr_final : rem_next} :
                           (st == S_HORN) ? {9'd0, rem_q[25:0], 1'b0} :
                           bpol_sh0       ? {bpol_v[29:0], 6'd0} :
                                            {take_lam ? lam_v[5:0] : prev_b_q, bpol_v[35:6]};
    qsag_ass2_cg_dff #(.W(36)) u_bpol (.clk(clk), .rst_n(srst_n), .en(bpol_en), .d(bpol_d), .q(bpol_v));

    always_ff @(posedge clk or negedge srst_n) begin
        if (!srst_n) win_cnt <= 16'd0;
        else if (st == S_CLR || (st == S_RUN && win_cnt == win_last))
            win_cnt <= 16'd0;
        else if (st == S_RUN || st == S_SETL)
            win_cnt <= win_cnt + 16'd1;
    end

    always_ff @(posedge clk or negedge srst_n) begin
        if (!srst_n) begin
            st               <= S_IDLE;
            meas_active      <= 1'b0;
            cnt_clr_n        <= 1'b0;
            sub_idx          <= '0;
            acc_cnt          <= '0;
            gamma            <= 6'd1;
            delta_q          <= '0;
            acc_gf           <= '0;
            tmp_gf           <= '0;
            prev_b_q         <= '0;
            l_deg            <= '0;
            sub_k            <= '0;
            sub_ph           <= 1'b0;
            chk_phase        <= 1'b0;
            done             <= 1'b0;
            blk_err          <= 1'b0;
            corrected_in_blk <= '0;
        end else begin
            done <= 1'b0;
            unique case (st)
                S_IDLE: if (start_blk) begin
                    sub_idx          <= 6'd0;
                    acc_cnt          <= 7'd0;
                    corrected_in_blk <= 4'd0;
                    chk_phase        <= 1'b0;
                    blk_err          <= 1'b0;
                    cnt_clr_n        <= 1'b0;
                    meas_active      <= 1'b0;
                    st               <= S_CLR;
                end
                S_CLR: begin
                    if (recon_mode && !vmsyn_q[0]) begin
                        if (sub_idx == 6'd63) begin
                            if (acc_cnt != {1'b0, BLK_BITS}) begin
                                blk_err <= 1'b1;
                                done    <= 1'b1;
                                st      <= S_IDLE;
                            end else begin
                                sub_idx <= 6'd62;
                                st      <= S_REM;
                            end
                        end else sub_idx <= sub_idx + 6'd1;
                    end else begin
                        cnt_clr_n   <= 1'b1;
                        meas_active <= 1'b1;
                        st          <= S_RUN;
                    end
                end
                S_RUN: if (win_cnt == win_last) begin
                    meas_active <= 1'b0;
                    st          <= S_SETL;
                end
                S_SETL: if (win_cnt == 16'(SETTLE_CYCLES - 1)) st <= S_EVAL;
                S_EVAL: begin
                    cnt_clr_n <= 1'b0;
                    if (eval_take) acc_cnt <= acc_cnt + 7'd1;
                    if (eff_dead) begin
                        blk_err <= 1'b1;
                        done    <= 1'b1;
                        st      <= S_IDLE;
                    end else if (sub_idx == 6'd63) begin
                        if ((acc_cnt + {6'd0, eval_take}) != {1'b0, BLK_BITS}) begin
                            blk_err <= 1'b1;
                            done    <= 1'b1;
                            st      <= S_IDLE;
                        end else begin
                            sub_idx <= 6'd62;
                            st      <= S_REM;
                        end
                    end else begin
                        sub_idx <= sub_idx + 6'd1;
                        st      <= S_CLR;
                    end
                end
                S_REM: begin
                    if (sub_idx == 6'd0) begin
                        if (!recon_mode || (!chk_phase && dr_final == 27'd0)) begin
                            done <= 1'b1;
                            st   <= S_IDLE;
                        end else if (chk_phase) begin
                            if ((corrected_in_blk != l_deg) || (l_deg > 4'd5) || (dr_final != 27'd0))
                                blk_err <= 1'b1;
                            done <= 1'b1;
                            st   <= S_IDLE;
                        end else begin
                            sub_idx <= 6'd26;
                            sub_k   <= 4'd0;
                            st      <= S_HORN;
                        end
                    end else begin
                        sub_idx <= sub_idx - 6'd1;
                    end
                end
                S_HORN: begin
                    if (sub_k == 4'd9) begin
                        sub_k <= 4'd0;
                        if (sub_idx == 6'd0) begin
                            gamma   <= 6'd1;
                            l_deg   <= 4'd0;
                            sub_idx <= 6'd1;
                            acc_gf  <= 6'd0;
                            st      <= S_BMD;
                        end else sub_idx <= sub_idx - 6'd1;
                    end else sub_k <= sub_k + 4'd1;
                end
                S_BMD: begin
                    if (sub_k == 4'd5) begin
                        sub_k    <= 4'd0;
                        sub_ph   <= 1'b0;
                        delta_q  <= dnext;
                        acc_gf   <= 6'd0;
                        prev_b_q <= 6'd0;
                        if (dnext == 6'd0) begin
                            if (sub_idx == 6'd10) begin
                                sub_idx <= 6'd0;
                                st      <= S_CHIEN;
                            end else sub_idx <= sub_idx + 6'd1;
                        end else begin
                            st <= S_BMU;
                        end
                    end else begin
                        acc_gf <= dnext;
                        sub_k  <= sub_k + 4'd1;
                    end
                end
                S_BMU: begin
                    if (!sub_ph) begin
                        tmp_gf <= mp;
                        sub_ph <= 1'b1;
                    end else begin
                        prev_b_q <= bpol_v[5:0];
                        sub_ph   <= 1'b0;
                        if (sub_k == 4'd5) begin
                            sub_k <= 4'd0;
                            if (take_lam) begin
                                l_deg <= sub_idx[3:0] - l_deg;
                                gamma <= delta_q;
                            end
                            if (sub_idx == 6'd10) begin
                                sub_idx <= 6'd0;
                                st      <= S_CHIEN;
                            end else begin
                                sub_idx <= sub_idx + 6'd1;
                                st      <= S_BMD;
                            end
                        end else sub_k <= sub_k + 4'd1;
                    end
                end
                S_CHIEN: begin
                    if (sub_k == 4'd5) begin
                        if (chien_ev == 6'd0)
                            corrected_in_blk <= corrected_in_blk + 4'd1;
                        sub_k <= 4'd0;
                        if (sub_idx == 6'd62) begin
                            sub_idx   <= 6'd62;
                            chk_phase <= 1'b1;
                            st        <= S_REM;
                        end else sub_idx <= sub_idx + 6'd1;
                    end else sub_k <= sub_k + 4'd1;
                end
                default: st <= S_IDLE;
            endcase
        end
    end
    wire unused = &{1'b0, blk_sel[2], puf_wdata[63:27], bmd_sdiff[5:4]};
endmodule

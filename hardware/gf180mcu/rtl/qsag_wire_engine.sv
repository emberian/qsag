// Dregg-180 (QSAG-NI-180) Core Packet Engine, Verifier VM, CapTP Vat & Houyhnhnm Enclave.
//
// Upgrades over baseline QSAG-NI-180:
//   * Punctured `[12,7,4]` HD=4 Control FSM (`ids 1..123`, `S_IDLE = 12'hc6f`, explicitly rejecting
//     both `12'h000` crowbar-zero and `12'hFFF` laser-saturation states with distance >= 4, checked
//     via `(* keep_hierarchy *)` `qsag_hd4_checker` + complementary loop counter `steps_inv_q`!).
//   * Full 62-bit Merkle index (`midx[62:0]`, `lidx[61:0]`, planetary depth `1..62`, Gotcha #6).
//   * 1-clock 64-byte shadow-to-sponge Keccak block absorb (`blk_absorb_mask`, Gotcha #4).
//   * Day-1 Built-In Self-Test (`0x03 OP_BIST`, < 950 clocks cold-reset KAT over TurboSHAKE256 +
//     Goldilocks Karatsuba-CSA + Han-Carlson prefix adders + Ext4 + GF(2^128) CLMUL).
//   * EAL6+ In-Hardware `Cut-the-Hash` WOTS+C Chain-End Self-Verification (`flags[3]=1`, computing
//     Z_j = F^{w-1-d_j}(Y_j) from staged `y_hold` and zeroizing all secrets in 1 clock before 1 byte
//     of a faulted signature is emitted on mismatch!).
//   * Houyhnhnm Capability & Physical Organs (`0x50 OP_PUF_ENROLL_RECON`, `0x51 OP_VAT_MINT_ATTENUATE`,
//     `0x52 OP_DB_NCO_CTRL`, `0x53 OP_VAT_INVOKE_ZK`, plus `flags[2]=1` `SpongeMacaroon` capability
//     gating on `0x41 OP_CTH` and `0x42 OP_PRFMSG`).
`default_nettype none

(* keep_hierarchy *) module qsag_hd4_checker #(
    parameter logic [6:0] MAX_ID = 7'd123
) (
    input  wire [11:0] c,
    output wire        ok
);
    wire [3:0] p = ({4{c[5]}} & 4'd3)  ^ ({4{c[6]}} & 4'd5)
                 ^ ({4{c[7]}} & 4'd6)  ^ ({4{c[8]}} & 4'd7)
                 ^ ({4{c[9]}} & 4'd9)  ^ ({4{c[10]}} & 4'd10)
                 ^ ({4{c[11]}} & 4'd11);
    assign ok = (c != 12'h000) && (c != 12'hFFF) &&
                (p == c[4:1]) && !(^c) &&
                (c[11:5] >= 7'd1) && (c[11:5] <= MAX_ID);
endmodule

module qsag_wire_engine #(
    parameter int GF_D = 4
) (
    input  wire         clk,
    input  wire         rst_n,        // core reset (synchronized)
    input  wire         srst_n,       // secret clear: reset, tamper, glitch (asynchronous)
    input  wire         zeroize,      // level: wipe and halt until reset
    // ingress / egress streams
    input  wire         in_valid,
    input  wire [63:0]  in_data,
    output logic        in_pop,
    input  wire         out_ready,
    output logic [63:0] out_data,
    output logic        out_push,
    // FRAM anchor (word-level)
    output logic        an_start,
    output logic        an_write,
    output logic [15:0] an_addr,
    input  wire         an_stb,
    output logic        an_go,
    input  wire  [63:0] an_rx,
    output wire  [63:0] an_tx,
    input  wire         an_done,
    // TRNG
    input  wire         trng_valid,
    input  wire  [63:0] trng_word,
    input  wire         trng_ok,
    output logic        trng_take,
    // 64-RO PUF + BCH(63,36,t=5) organ interface
    output logic        puf_start_blk,
    output logic        puf_recon_mode,
    output wire  [2:0]  puf_blk_sel,
    output logic [5:0]  puf_margin,
    output logic [2:0]  puf_noise_flips,
    output logic [63:0] puf_vmask_in,
    output logic [26:0] puf_syn_in,
    input  wire         puf_done,
    input  wire         puf_blk_err,
    input  wire  [63:0] puf_vmask_out,
    input  wire  [26:0] puf_syn_out,
    input  wire  [63:0] puf_word_out,
    input  wire  [3:0]  puf_corrected,
    // NFC + NCO organ interface
    input  wire         nfc_token_valid,
    input  wire  [63:0] nfc_digest_bind,
    input  wire  [15:0] nfc_quorum_flags,
    input  wire  [15:0] nfc_rx_frames,
    output wire         nfc_token_consume,
    output logic        nco_en,
    output logic [1:0]  nco_mode,
    output logic [3:0]  nco_sym_shift,
    output logic [31:0] nco_ftw_base,
    output logic [31:0] nco_ftw_delta,
    output logic        nco_pkt_load,
    output wire  [63:0] nco_pkt_data,
    input  wire         nco_tx_active,
    // Distance-Bounding + Vernier TDC organ interface
    output logic        db_load_r0,
    output logic        db_load_r1,
    output wire  [63:0] db_load_wdata,
    output logic        db_arm_responder,
    output logic        db_step_round,
    output logic        db_launch_ping,
    output logic        db_cal_ping,
    output wire         db_dist_consume,
    input  wire         db_responder_armed,
    input  wire  [6:0]  db_rounds_done,
    input  wire  [63:0] db_chal_log,
    input  wire  [63:0] db_resp_log,
    input  wire         db_dist_valid,
    input  wire         db_dist_timeout,
    input  wire  [31:0] db_dist_cycles,
    // telemetry / configuration
    input  wire  [63:0] tel0,
    input  wire  [31:0] tel1,
    output logic [63:0] csr,
    // status & emergency fault outputs
    output logic        verify_ok,
    output wire         key_valid_o,
    output wire         vat_ready_o,
    output logic        fault_anchor,
    output logic        fault_mac,
    output logic        fault_control,
    output logic        fault_laser_dfa,
    output wire         busy
);
    // ------------------------------------------------------------------ opcodes & errors
    localparam logic [7:0] OP_PING = 8'h01, OP_CSR = 8'h02, OP_BIST = 8'h03,
                           OP_P2 = 8'h10, OP_MERKLE = 8'h11, OP_KECCAK = 8'h20,
                           OP_FOLD = 8'h30, OP_HEM = 8'h31,
                           OP_KEYLOAD = 8'h40, OP_CTH = 8'h41, OP_PRFMSG = 8'h42,
                           OP_PUF = 8'h50, OP_VAT = 8'h51, OP_DB_NCO = 8'h52, OP_VAT_ZK = 8'h53;
    localparam logic [15:0] E_MAGIC = 16'd1, E_OPCODE = 16'd2, E_LEN = 16'd3, E_NOKEY = 16'd4,
                            E_MAC = 16'd5, E_ANCHOR_EMPTY = 16'd6, E_ROLLBACK = 16'd7,
                            E_REUSE = 16'd8, E_ANCHOR_IO = 16'd9, E_KEYSET = 16'd10,
                            E_TRNG = 16'd11, E_PUF = 16'd12, E_CAP = 16'd13, E_LOCKED = 16'd14;
    localparam logic [63:0] CHIP_ID         = 64'h3831_494E_4741_5351;  // "QSAGNI18"
    localparam logic [63:0] C_FRAM          = 64'h5246_494E_4741_5351;  // "QSAGNIFR"
    localparam logic [63:0] C_MASK          = 64'h4B4D_494E_4741_5351;  // "QSAGNIMK"
    localparam logic [63:0] C_PUF           = 64'h4655_5047_4745_5244;  // "DREGGPUF"
    localparam logic [63:0] C_PUF_CHK       = 64'h4B48_4347_4745_5244;  // "DREGGCHK"
    localparam logic [63:0] C_VAT           = 64'h5441_5647_4745_5244;  // "DREGGVAT"
    localparam logic [63:0] C_ZKG           = 64'h474B_5A47_4745_5244;  // "DREGGZKG"
    localparam logic [63:0] NODE_HI         = 64'h5032_4E44_0000_0000;
    localparam logic [63:0] FS_INIT         = 64'h5032_4653_494E_4954;
    localparam logic [63:0] P2_IV           = 64'h504F_5332_5F47_4C31;
    localparam logic [63:0] PAD_END         = 64'h8000_0000_0000_0000;
    localparam logic [63:0] BIST_GOLDEN_KAT = 64'h4ae2_1323_a298_0887;
    localparam logic [63:0] DFA_CANARY_SEED = 64'hDEAD_BEEF_CAFE_5A3C;

    localparam logic [3:0] F_PERM = 4'd1, F_ABSW = 4'd2, F_SETW = 4'd3, F_MOV = 4'd4, F_EMUL = 4'd5,
                           F_EADD = 4'd6, F_ESUB = 4'd7, F_EEQ = 4'd8, F_FFWD = 4'd9, F_LDRES = 4'd10;

    // ------------------------------------------------------------------ 123 punctured [12,7,4] HD=4 states
    localparam logic [11:0]
        S_IDLE = 12'hc6f,   S_DRAIN = 12'h027,  S_EHDR = 12'h04b,   S_HDR = 12'h06c,    S_OUTL = 12'h08d,
        S_WIPE = 12'h0aa,   S_DEAD = 12'h0c6,   S_PING = 12'h0e1,   S_CSR = 12'h10e,
        S_P2R = 12'h129,    S_P2RP = 12'h145,
        S_HSZ = 12'h162,    S_HSD = 12'h183,    S_HSC = 12'h1a4,    S_HSN = 12'h1c8,    S_HSL = 12'h1ef,
        S_HSP = 12'h213,    S_HSF = 12'h234,
        S_MK0 = 12'h258,    S_MK1 = 12'h27f,    S_MK2 = 12'h29e,    S_MK3 = 12'h2b9,    S_MK4 = 12'h2d5,
        S_MK5 = 12'h2f2,    S_MPS = 12'h31d,
        S_MOK = 12'h33a,    S_MOI = 12'h356,    S_MOL = 12'h371,    S_MOR = 12'h390,    S_MOE = 12'h3b7,
        S_MOV = 12'h3db,
        S_KSW = 12'h3fc,    S_KSK = 12'h415,    S_KSA = 12'h432,    S_KSP = 12'h45e,    S_KSD = 12'h479,
        S_KSE = 12'h498,    S_KSQ = 12'h4bf,    S_KSO = 12'h4d3,    S_KSR = 12'h4f4,
        S_KLM = 12'h51b,    S_KLH = 12'h53c,    S_KLW = 12'h550,    S_KLT = 12'h577,    S_KLA = 12'h596,
        S_KLD = 12'h5b1,    S_KLE = 12'h5dd,    S_KLP = 12'h5fa,    S_KLK = 12'h606,    S_KLZ = 12'h621,
        S_KLN = 12'h64d,    S_KLF = 12'h66a,
        S_BLD = 12'h68b,    S_BKC = 12'h6ac,
        S_AR0 = 12'h6c0,    S_AR1 = 12'h6e7,    S_AR2 = 12'h708,    S_AR3 = 12'h72f,    S_AR4 = 12'h743,
        S_AR5 = 12'h764,
        S_AW1 = 12'h785,    S_AW2 = 12'h7a2,    S_AW3 = 12'h7ce,    S_AW4 = 12'h7e9,    S_AW5 = 12'h816,
        S_AW6 = 12'h831,    S_AW7 = 12'h85d,    S_AW8 = 12'h87a,    S_AW9 = 12'h89b,    S_AWA = 12'h8bc,
        S_CTG = 12'h8d0,    S_CTL = 12'h8f7,    S_CTT = 12'h918,    S_CTD = 12'h93f,    S_CA0 = 12'h953,
        S_CA1 = 12'h974,    S_CA2 = 12'h995,    S_CA3 = 12'h9b2,    S_CTS = 12'h9de,    S_CM0 = 12'h9f9,
        S_CM1 = 12'ha05,    S_CKD = 12'ha22,    S_CO = 12'ha4e,
        S_HVG = 12'ha69,    S_HVR = 12'ha88,    S_HVD = 12'haaf,    S_HVH = 12'hac3,    S_HVA = 12'hae4,
        S_HVL = 12'hb0b,    S_HVE = 12'hb2c,    S_HVP = 12'hb40,    S_HVQ = 12'hb67,    S_HVM = 12'hb86,
        S_HVI = 12'hba1,    S_HVJ = 12'hbcd,    S_HVN = 12'hbea,    S_HVF = 12'hc03,    S_HVS = 12'hc24,
        S_HVC = 12'hc48,
        // Dregg-180 new HD=4 states (ids 100..123)
        S_BSW = 12'hc8e,    S_BS0 = 12'hca9,    S_BS1 = 12'hcc5,    S_BS2 = 12'hce2,    S_BSO = 12'hd0d,
        S_KSB = 12'hd2a,
        S_CY0 = 12'hd46,    S_CY1 = 12'hd61,    S_CZ0 = 12'hd80,    S_CZ1 = 12'hda7,    S_CZ2 = 12'hdcb,
        S_PF0 = 12'hdec,    S_PF1 = 12'he10,    S_PF2 = 12'he37,    S_PF3 = 12'he5b,    S_PF4 = 12'he7c,
        S_PF5 = 12'he9d,
        S_VLD = 12'heba,    S_VTG = 12'hed6,    S_VAT = 12'hef1,    S_VOT = 12'hf1e,    S_VZK = 12'hf39,
        S_DB0 = 12'hf55,    S_DBO = 12'hf72;

    localparam logic [2:0] K_NONE = 3'd0, K_FE = 3'd1, K_KC = 3'd2, K_GF = 3'd3;

    (* fsm_encoding = "none", keep *) logic [11:0] st, ret, ret2, ret3;
    wire ok_st, ok_r1, ok_r2, ok_r3;
    qsag_hd4_checker #(.MAX_ID(7'd123)) u_chk_st (.c(st),   .ok(ok_st));
    qsag_hd4_checker #(.MAX_ID(7'd123)) u_chk_r1 (.c(ret),  .ok(ok_r1));
    qsag_hd4_checker #(.MAX_ID(7'd123)) u_chk_r2 (.c(ret2), .ok(ok_r2));
    qsag_hd4_checker #(.MAX_ID(7'd123)) u_chk_r3 (.c(ret3), .ok(ok_r3));

    // Complementary shadow loop counter `steps_inv_q` (Subcarbon R0 §5.1.3: catches single-spot
    // laser counter skipping in WOTS+C!)
    logic [15:0] steps, steps_inv_q;
    wire         steps_bad   = ((steps ^ steps_inv_q) != 16'hFFFF);
    wire         control_bad = !ok_st || !ok_r1 || !ok_r2 || !ok_r3 || steps_bad;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) fault_control <= 1'b0;
        else if (control_bad) fault_control <= 1'b1;

    wire secret_rst_n   = srst_n & ~fault_control & ~fault_laser_dfa;
    wire permit_control = !control_bad && !fault_control && !fault_laser_dfa;

    logic        w;
    logic [7:0]  op, flags;
    logic [15:0] arg;
    logic [20:0] wrem;
    logic [2:0]  lenb;
    logic [23:0] rlen;
    logic [15:0] rcode;
    logic        rerr, rok;
    logic [15:0] cnt;
    logic [4:0]  cnt2;
    logic [4:0]  wi;
    logic [5:0]  obase;
    logic [4:0]  olim;
    logic        partial;
    // 1-clock shadow block absorb tracking
    logic [3:0]  sh_fill;
    logic [7:0]  sh_mask;
    // Poseidon2 sponge hash
    logic [15:0] hs_n, hs_k;
    logic [3:0]  hs_idx;
    logic        hs_first, hs_ph, gfdone;
    logic [1:0]  hs_capsrc;
    logic [2:0]  hs_capreg, hs_latch;
    logic [1:0]  hs_skip;
    logic        idx_armed;
    // 62-bit Planetary Merkle
    logic [62:0] midx;
    logic [61:0] lidx;
    logic [5:0]  mk_kb;
    // verifier VM
    logic [3:0]  hop;
    logic [7:0]  ha, hb, hc;
    logic [15:0] dleft, recidx, fidx;
    logic        inrec, fail, fset, noncanon, verdict;
    // keys, enclave & Houyhnhnm state
    wire  [63:0] key [6];
    logic        key_valid, vat_mint_locked;
    logic [31:0] cur, hwm, ctmp;
    logic        hwm_valid, v0, anyv, older, aslot, rcmp, hi0, macdiff, is_fors, isprf;
    logic [2:0]  bmode;              // 0 SLH, 1 FRAM, 2 MASK, 3 RECEIPT, 4 VAT_SEAL, 5 PUF_ABS, 6 PUF_CHK, 7 ZK_GRANT
    logic [7:0]  ci;
    logic [1:0]  widx;
    logic [6:0]  sh;
    logic [15:0] sym;
    logic [15:0] hj;
    // Cut-the-Hash chain-end self-verify staging & sticky canary
    logic [63:0] y_hold0, y_hold1, dfa_diff;
    logic        chk_cont;
    // PUF / DB staging
    logic [2:0]  puf_blk;
    logic        puf_any_err;
    logic [7:0]  puf_corr_tot;

    assign busy        = (st != S_IDLE);
    assign key_valid_o = key_valid;
    assign puf_blk_sel = puf_blk;

    // ------------------------------------------------------------------ CapTP Vat Membrane
    logic [3:0]  kvat_we;
    logic        kvat_commit, zk_latch_we, zk_latch_set, zk_latch_clr;
    logic        vat_pchk_clr, vat_pwe, vat_cchk_clr, vat_cwe;
    wire         vat_commit_inv;
    wire         vat_ready, zk_root_valid, vat_att_ok, vat_att_step_ok, vat_inv_ok, vat_need_fram;
    wire  [63:0] kvat_rdata;
    wire  [31:0] vat_spend_used;

    wire [15:0] vat_req_right = (op == OP_CTH)    ? 16'h0001 :
                                (op == OP_PRFMSG) ? 16'h0002 : 16'h0004;
    wire [31:0] vat_req_epoch = (op == OP_CTH)    ? y_hold0[31:0] : {16'd0, arg};
    wire [31:0] vat_req_spend = (op == OP_CTH)    ? {24'd0, arg[7:0]} : 32'd1;
    wire [63:0] kvat_wd_mux   = (st == S_KLH) ? in_data : port;

    assign vat_ready_o = vat_ready;

    // ------------------------------------------------------------------ Datapath instances
    wire         fe_busy, fe_done, fe_eq;
    wire  [5:0]  fe_rd, fe_wa;
    wire         fe_we;
    wire  [1:0]  pm, rk;
    wire  [3:0]  pk;
    wire  [2:0]  rm;
    wire         krc, acc_clr, acc_we, ld_opa, ld_opb, ld_res, mul_start, mul_asel, mul_bsel;
    wire         mul_last, mul_busy, cv_zero;
    wire  [6:0]  rc_idx;
    wire  [63:0] rc, cv, port, res;
    wire         kc_busy, kc_done, kc_we;
    wire  [5:0]  kc_rd, kc_wa;
    wire  [63:0] kc_wd;
    wire         gf_busy, gf_done;
    wire [127:0] gf_acc;

    logic        fe_start, kc_start, kc_turbo, gf_start, gf_clr, sp_wipe;
    logic [3:0]  fe_op;
    logic [5:0]  fe_d, fe_s1, fe_s2;
    logic [2:0]  fe_n;
    logic        fe_dir;
    logic [63:0] xw;
    logic [5:0]  e_rd, e_wa;
    logic        e_we;
    logic [63:0] e_wd;
    logic [7:0]  blk_abs_pulse;

    logic zeroize_q;
    /* verilator lint_off SYNCASYNCNET */
    wire  sub_rst_n = rst_n & ~zeroize_q & ~fault_control & ~fault_laser_dfa;
    /* verilator lint_on SYNCASYNCNET */
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) zeroize_q <= 1'b0;
        else        zeroize_q <= zeroize;

    // Concurrent shadow buffering while S_KSP (`kc_busy`) permutes st[0..24]!
    wire bg_sh_can_take = (st == S_KSP) && kc_busy && permit_control &&
                          (sh_fill < 4'd8) && in_valid &&
                          ((wrem > 21'd1) || (wrem == 21'd1 && lenb == 3'd0));

    qsag_field_engine u_fe (
        .clk(clk), .rst_n(sub_rst_n), .start(fe_start), .op(fe_op), .d(fe_d), .s1(fe_s1), .s2(fe_s2),
        .n(fe_n), .dir(fe_dir), .busy(fe_busy), .done(fe_done), .eq(fe_eq),
        .rd_addr(fe_rd), .wr_en(fe_we), .wr_addr(fe_wa),
        .pm(pm), .pk(pk), .rm(rm), .rk(rk), .krc(krc), .acc_clr(acc_clr), .acc_we(acc_we),
        .ld_opa(ld_opa), .ld_opb(ld_opb), .ld_res(ld_res),
        .mul_start(mul_start), .mul_asel(mul_asel), .mul_bsel(mul_bsel),
        .mul_last(mul_last), .cv_zero(cv_zero), .rc_idx(rc_idx)
    );
    qsag_p2_rc u_rc (.idx(rc_idx), .rc(rc));
    qsag_gl64_karatsuba_csa #(.W(32), .GB(12)) u_alu (
        .clk(clk), .rst_n(sub_rst_n), .port(port), .xw(xw), .rc(rc),
        .pm(pm), .pk(pk), .rm(rm), .rk(rk), .krc(krc), .acc_clr(acc_clr), .acc_we(acc_we),
        .ld_opa(ld_opa), .ld_opb(ld_opb), .ld_res(ld_res),
        .mul_start(mul_start), .mul_asel(mul_asel), .mul_bsel(mul_bsel),
        .mul_busy(mul_busy), .mul_last(mul_last), .cv(cv), .cv_zero(cv_zero), .res(res)
    );
    qsag_keccak_serial u_kc (
        .clk(clk), .rst_n(sub_rst_n), .srst_n(secret_rst_n), .start(kc_start), .turbo(kc_turbo),
        .fault_inj(csr[53] && (st == S_BKC) && (bmode == 3'd0) && !chk_cont),
        .busy(kc_busy), .done(kc_done), .rd_addr(kc_rd), .port(port),
        .wr_en(kc_we), .wr_addr(kc_wa), .wr_data(kc_wd)
    );
    qsag_sponge u_sp (
        .clk(clk), .srst_n(secret_rst_n), .wipe(!rst_n | sp_wipe | zeroize_q | fault_control | fault_laser_dfa),
        .wr_en(fe_busy ? fe_we : kc_busy ? kc_we : e_we),
        .wr_addr(fe_busy ? fe_wa : kc_busy ? kc_wa : e_wa),
        .wr_data(fe_busy ? cv : kc_busy ? kc_wd : e_wd),
        .rd_addr(fe_busy ? fe_rd : kc_busy ? kc_rd : e_rd),
        .rd_data(port),
        .sh_ext_we(bg_sh_can_take),
        .sh_ext_addr(sh_fill[2:0]),
        .sh_ext_wdata(in_data),
        .blk_absorb_mask(blk_abs_pulse)
    );
    wire [127:0] gf_h_eff = (op == OP_BIST) ? 128'hA5A5_5A5A_DEAD_BEEF_3831_494E_4741_5351 : {key[5], key[4]};
    qsag_gf128_clmul #(.D(GF_D)) u_gf (
        .clk(clk), .rst_n(sub_rst_n), .srst_n(secret_rst_n), .clr(gf_clr), .start(gf_start),
        .in({64'd0, xw}), .h(gf_h_eff), .busy(gf_busy), .done(gf_done), .acc(gf_acc)
    );

    dregg_captp_vat u_vat (
        .clk(clk), .rst_n(sub_rst_n), .srst_n(secret_rst_n), .permit_control(permit_control),
        .kvat_we(kvat_we), .kvat_wdata(kvat_wd_mux), .kvat_commit(kvat_commit), .vat_ready(vat_ready),
        .kvat_ridx(cnt2[1:0] - 2'd1), .kvat_rdata(kvat_rdata),
        .zk_latch_we(zk_latch_we), .zk_latch_idx(cnt2[1:0]), .zk_latch_wdata(port),
        .zk_latch_valid_set(zk_latch_set), .zk_latch_clear(zk_latch_clr), .zk_root_valid(zk_root_valid),
        .parent_chk_clr(vat_pchk_clr), .parent_we(vat_pwe), .parent_idx(cnt2[2:0]),
        .desc_wdata(in_data), .pw_sponge_word(port),
        .child_chk_clr(vat_cchk_clr), .child_we(vat_cwe), .child_idx(cnt2[2:0]),
        .nfc_token_valid(nfc_token_valid), .nfc_digest_bind(nfc_digest_bind),
        .nfc_consume_pulse(nfc_token_consume),
        .dist_valid(db_dist_valid), .dist_timeout(db_dist_timeout), .dist_cycles(db_dist_cycles),
        .dist_consume_pulse(db_dist_consume),
        .req_right_bit(vat_req_right), .req_epoch(vat_req_epoch), .req_spend(vat_req_spend),
        .req_bind_lo(y_hold1), .req_bind_hi(dfa_diff),
        .check_is_zk(op == OP_VAT_ZK), .commit_invocation(vat_commit_inv),
        .attenuate_legal(vat_att_ok), .attenuate_step_ok(vat_att_step_ok), .invoke_legal(vat_inv_ok),
        .need_stateful_fram(vat_need_fram), .vat_spend_used(vat_spend_used)
    );

    // key registers
    logic [5:0]  key_we;
    wire  [63:0] key_d;
    genvar gi;
    generate
        for (gi = 0; gi < 6; gi++) begin : g_key
            qsag_ereg #(.W(64)) u_k (.clk(clk), .rst_n(secret_rst_n), .en(key_we[gi] && permit_control), .d(key_d), .q(key[gi]));
        end
    endgenerate

    // ------------------------------------------------------------------ helpers
    function automatic logic [5:0] rb(input logic [2:0] id);
        case (id)
            3'd1:    rb = 6'd12;
            3'd2:    rb = 6'd16;
            3'd3:    rb = 6'd20;
            3'd4:    rb = 6'd32;
            3'd5:    rb = 6'd36;
            default: rb = 6'd0;
        endcase
    endfunction
    function automatic logic [31:0] lowmask(input logic [5:0] bits);
        lowmask = (bits >= 6'd32) ? 32'hFFFF_FFFF : ((32'd1 << bits) - 32'd1);
    endfunction
    function automatic logic [61:0] lowmask62(input logic [5:0] bits);
        lowmask62 = (bits >= 6'd62) ? 62'h3FFF_FFFF_FFFF_FFFF : ((62'd1 << bits) - 62'd1);
    endfunction

    wire        in_ge_p   = (&in_data[63:32]) && (|in_data[31:0]);
    wire [63:0] hdr_word  = {arg, wrem[20:0], lenb, flags, op, 8'h51};
    // Gotcha #6: injective 62-bit planetary Merkle node tweak (`== NODE_HI | parent` for depth 1..32!)
    wire [63:0] t0_word   = NODE_HI ^ {2'b00, midx[62:1]};
    wire        pubgen    = flags[0];
    wire        cap_mode  = flags[2];
    wire        self_chk  = flags[3] && !pubgen && !is_fors;
    wire        stateful  = flags[1] || (cap_mode && vat_need_fram);
    wire [7:0]  nch       = arg[7:0];
    wire [4:0]  sw        = arg[12:8];
    wire [15:0] symmask   = (sw >= 5'd16) ? 16'hFFFF : ((16'd1 << sw) - 16'd1);
    wire [63:0] port_sh   = port >> sh[5:0];
    wire [23:0] fors_idx  = (24'(ci) << sw) | 24'(sym);
    wire [23:0] hfield    = is_fors ? fors_idx : (isprf ? 24'd0 : 24'(hj));
    wire [7:0]  cfield    = is_fors ? 8'd0 : ci;
    wire [63:0] a3_word   = {hfield[7:0], hfield[15:8], hfield[23:16], 8'd0, cfield, 24'd0};
    wire [7:0]  type_ov   = is_fors ? (isprf ? 8'd6 : 8'd3) : (isprf ? 8'd5 : 8'd0);
    wire [63:0] stat_word = {8'd0, op, recidx, fidx, 13'd0, key_valid, noncanon, verdict};

    assign nco_pkt_data  = in_data;
    assign db_load_wdata = in_data;

    // ------------------------------------------------------------------ control decode
    logic [2:0]  kind;
    logic        cond;
    logic        do_pop;
    logic [2:0]  xsel;       // 0 in, 1 imm, 2 key, 3 gf, 4 anchor, 5 trng, 6 zero, 7 port
    logic [63:0] imm;
    logic [2:0]  ksel;
    logic        gsel;
    logic [2:0]  wsel;       // 0 xw, 1 port^xw, 2 port, 3 a0(port), 4 type(port)
    logic        e_wreq;
    logic        e_wlaunch;
    logic        emit;
    logic        emit_port;
    wire         cmp_ne;

    wire sub_done   = (kind == K_FE) ? fe_done : (kind == K_KC) ? kc_done : (kind == K_GF) ? gf_done : 1'b0;
    wire launch     = permit_control && (kind != K_NONE) && !w && cond;
    wire fire       = permit_control && ((kind == K_NONE) ? cond : (w && sub_done));
    wire bindw      = (hs_k != 16'd0) && !gfdone;
    wire hs_lat_now = (hs_latch != 3'd0) && !hs_ph && (hs_n > {14'd0, hs_skip}) && (hs_n <= 16'd4 + {14'd0, hs_skip});

    always_comb begin
        xw = 64'd0;
        unique case (xsel)
            3'd0:    xw = in_data;
            3'd1:    xw = imm;
            3'd2:    xw = key[ksel];
            3'd3:    xw = gsel ? gf_acc[127:64] : gf_acc[63:0];
            3'd4:    xw = an_rx;
            3'd5:    xw = trng_word;
            3'd7:    xw = port;
            default: xw = 64'd0;
        endcase
        unique case (wsel)
            3'd1:    e_wd = port ^ xw;
            3'd2:    e_wd = port;
            3'd3:    e_wd = {32'd0, port[39:32], 24'd0};
            3'd4:    e_wd = {port[63:32], type_ov, port[23:0]};
            default: e_wd = xw;
        endcase
    end

    always_comb begin
        kind           = K_NONE;
        cond           = 1'b1;
        do_pop         = 1'b0;
        xsel           = 3'd6;
        imm            = 64'd0;
        ksel           = 3'd0;
        gsel           = 1'b0;
        wsel           = 3'd0;
        e_wreq         = 1'b0;
        e_wlaunch      = 1'b0;
        e_rd           = 6'd0;
        e_wa           = 6'd0;
        emit           = 1'b0;
        emit_port      = 1'b0;
        fe_op          = F_PERM;
        fe_d           = 6'd0;
        fe_s1          = 6'd0;
        fe_s2          = 6'd0;
        fe_n           = 3'd0;
        fe_dir         = 1'b0;
        kc_turbo       = 1'b0;
        gf_clr         = 1'b0;
        sp_wipe        = 1'b0;
        blk_abs_pulse  = 8'd0;
        an_start       = 1'b0;
        an_write       = 1'b0;
        an_addr        = {10'd0, aslot, 5'd0};
        an_go          = 1'b0;
        trng_take      = 1'b0;
        key_we         = 6'd0;
        kvat_we        = 4'd0;
        kvat_commit    = 1'b0;
        zk_latch_we    = 1'b0;
        zk_latch_set   = 1'b0;
        zk_latch_clr   = 1'b0;
        vat_pchk_clr   = 1'b0;
        vat_pwe        = 1'b0;
        vat_cchk_clr   = 1'b0;
        vat_cwe        = 1'b0;
        puf_start_blk  = 1'b0;
        db_load_r0     = 1'b0;
        db_load_r1     = 1'b0;
        db_arm_responder = 1'b0;
        db_step_round  = 1'b0;
        db_launch_ping = 1'b0;
        db_cal_ping    = 1'b0;
        nco_pkt_load   = 1'b0;

        unique case (st)
            S_IDLE: begin
                cond   = in_valid;
                do_pop = 1'b1;
                gf_clr = 1'b1;
            end
            S_DRAIN: begin
                cond   = (wrem == 21'd0) || in_valid;
                do_pop = (wrem != 21'd0);
            end
            S_EHDR, S_HDR: begin
                cond = out_ready;
                emit = 1'b1;
                imm  = {rcode, rlen, rerr, 6'd0, rok, op | 8'h80, 8'h51};
            end
            S_OUTL: begin
                cond      = out_ready;
                emit      = 1'b1;
                emit_port = 1'b1;
                e_rd      = obase + {1'b0, cnt2};
            end
            S_WIPE, S_KSW, S_KLZ: sp_wipe = 1'b1;
            S_KLW: begin
                sp_wipe   = 1'b1;
                trng_take = 1'b1;
            end
            S_DEAD: begin
                cond    = 1'b0;
                sp_wipe = 1'b1;
            end
            S_PING: begin
                cond = out_ready;
                emit = 1'b1;
                unique case (cnt2[1:0])
                    2'd0:    imm = CHIP_ID;
                    2'd1:    imm = tel0;
                    2'd2:    imm = {vat_spend_used[15:0], 8'd0, vat_mint_locked, zk_root_valid,
                                    nfc_token_valid, vat_ready, hwm_valid, fault_mac, fault_anchor, key_valid, tel1};
                    default: imm = trng_word;
                endcase
            end
            S_CSR: begin
                cond   = in_valid;
                do_pop = 1'b1;
            end
            // ---------------------------------------------------------- OP_BIST (< 950 clk KAT)
            S_BSW: begin
                sp_wipe = 1'b1;
                gf_clr  = 1'b1;
            end
            S_BS0: begin
                e_wreq = 1'b1;
                xsel   = 3'd1;
                e_wa   = (cnt2 == 5'd0) ? 6'd0 : (cnt2 == 5'd1) ? 6'd1 : 6'd16;
                imm    = (cnt2 == 5'd0) ? CHIP_ID : (cnt2 == 5'd1) ? 64'h1F : PAD_END;
            end
            S_BS1: begin
                kind  = K_FE;
                fe_op = F_EMUL;
                fe_d  = 6'd16;
                fe_s1 = 6'd0;
                fe_s2 = 6'd4;
            end
            S_BS2: begin
                e_rd = 6'd16;
                kind = K_GF;
                xsel = 3'd7;
            end
            S_BSO: begin
                cond = out_ready;
                emit = 1'b1;
                imm  = y_hold0;
            end
            // ---------------------------------------------------------- Poseidon2
            S_P2R: begin
                kind   = K_FE;
                cond   = in_valid;
                fe_op  = F_SETW;
                fe_d   = {1'b0, cnt2};
                xsel   = 3'd0;
                do_pop = 1'b1;
            end
            S_P2RP, S_HSP, S_MK4: begin
                kind  = K_FE;
                fe_op = F_PERM;
            end
            S_HSZ: begin
                kind  = K_FE;
                fe_op = F_SETW;
                fe_d  = {1'b0, cnt2};
                xsel  = 3'd6;
            end
            S_HSD: begin
                kind   = bindw ? K_GF : K_FE;
                cond   = in_valid;
                fe_op  = F_ABSW;
                fe_d   = 6'd0;
                xsel   = 3'd0;
                do_pop = !bindw;
            end
            S_HSC: begin
                kind = K_FE;
                unique case (hs_capsrc)
                    2'd0: begin
                        cond   = in_valid;
                        fe_op  = F_SETW;
                        fe_d   = 6'd8 + {1'b0, cnt2};
                        xsel   = 3'd0;
                        do_pop = 1'b1;
                    end
                    2'd1: begin
                        fe_op = F_MOV;
                        fe_d  = 6'd8;
                        fe_s1 = rb(hs_capreg);
                    end
                    default: begin
                        fe_op = F_SETW;
                        fe_d  = 6'd8 + {1'b0, cnt2};
                        xsel  = 3'd1;
                        imm   = (cnt2[1:0] == 2'd0) ? FS_INIT : (cnt2[1:0] == 2'd3) ? P2_IV : 64'd0;
                    end
                endcase
            end
            S_HSN: begin
                kind  = K_FE;
                fe_op = F_ABSW;
                fe_d  = 6'd1;
                xsel  = 3'd1;
                imm   = {48'd0, hs_n};
            end
            S_HSL: begin
                if (hs_n == 16'd0) kind = K_NONE;
                else begin
                    kind = bindw ? K_GF : K_FE;
                    cond = in_valid;
                    xsel = 3'd0;
                    if (hs_lat_now) begin
                        fe_op = F_SETW;
                        fe_d  = rb(hs_latch) + 6'd4 + {4'd0, hs_skip} - hs_n[5:0];
                    end else begin
                        fe_op  = F_ABSW;
                        fe_d   = {2'd0, hs_idx};
                        do_pop = !bindw;
                    end
                end
            end
            S_HSF: begin
                kind  = (hs_first || hs_idx != 4'd0) ? K_FE : K_NONE;
                fe_op = F_PERM;
            end
            // ---------------------------------------------------------- Canopy (Planetary Depth 1..62)
            S_MK0: begin
                kind  = K_FE;
                fe_op = F_MOV;
                fe_d  = 6'd0;
                fe_s1 = midx[0] ? 6'd36 : 6'd32;
            end
            S_MK1: begin
                kind  = K_FE;
                fe_op = F_MOV;
                fe_d  = 6'd4;
                fe_s1 = midx[0] ? 6'd32 : 6'd36;
            end
            S_MK2: begin
                kind  = K_FE;
                fe_op = F_SETW;
                fe_d  = 6'd8;
                xsel  = 3'd1;
                imm   = t0_word;
            end
            S_MK3: begin
                kind  = K_FE;
                fe_op = F_MOV;
                fe_d  = 6'd9;
                fe_s1 = mk_kb;
                fe_n  = 3'd3;
            end
            S_MK5: begin
                kind   = K_FE;
                fe_op  = F_FFWD;
                fe_s1  = mk_kb;
                fe_dir = midx[0];
                xsel   = 3'd1;
                imm    = t0_word;
            end
            S_MPS: begin
                if (cnt == 16'd0) kind = K_NONE;
                else begin
                    kind   = K_FE;
                    cond   = in_valid;
                    fe_op  = F_SETW;
                    fe_d   = 6'd36 + {1'b0, cnt2};
                    xsel   = 3'd0;
                    do_pop = 1'b1;
                end
            end
            S_MOK, S_MOL, S_MOR, S_HVL: begin
                kind   = (st == S_HVL && bindw) ? K_GF : K_FE;
                cond   = in_valid;
                fe_op  = F_SETW;
                fe_d   = ((st == S_MOK) ? 6'd16 : (st == S_MOL) ? 6'd32 : (st == S_MOR) ? 6'd36 : rb(ha[2:0]))
                         + {1'b0, cnt2};
                xsel   = 3'd0;
                do_pop = !(st == S_HVL && bindw);
            end
            S_MOI, S_HVM: begin
                cond   = in_valid;
                do_pop = 1'b1;
            end
            S_MOE: begin
                kind  = K_FE;
                fe_op = F_EEQ;
                fe_s1 = 6'd32;
                fe_s2 = 6'd36;
            end
            S_MOV: begin
                cond = out_ready;
                emit = 1'b1;
                imm  = {63'd0, verdict};
            end
            // ---------------------------------------------------------- Keccak + 1-Clock Shadow Block Absorb
            S_KSK: begin
                e_wreq = 1'b1;
                e_wa   = {1'b0, cnt2};
                xsel   = 3'd2;
                ksel   = 3'd2 + {2'd0, cnt2[0]};
            end
            S_KSA: begin
                cond   = (wrem == 21'd0) || in_valid;
                do_pop = (wrem != 21'd0);
                e_wreq = (wrem != 21'd0);
                e_rd   = {1'b0, wi};
                e_wa   = {1'b0, wi};
                wsel   = 3'd1;
                xsel   = 3'd0;
            end
            S_KSB: begin
                blk_abs_pulse = sh_mask;
            end
            S_KSP, S_KSR, S_BKC: begin
                kind     = K_KC;
                kc_turbo = (st == S_BKC) ? (bmode != 3'd0) : (op == OP_KECCAK && flags[0]);
            end
            S_KSD: begin
                e_wreq = 1'b1;
                e_rd   = {1'b0, wi};
                e_wa   = {1'b0, wi};
                wsel   = 3'd1;
                xsel   = 3'd1;
                imm    = {56'd0, (op == OP_KECCAK) ? arg[7:0] : 8'h1F} << {partial ? lenb : 3'd0, 3'd0};
            end
            S_KSE: begin
                e_wreq = 1'b1;
                e_rd   = 6'd16;
                e_wa   = 6'd16;
                wsel   = 3'd1;
                xsel   = 3'd1;
                imm    = PAD_END;
            end
            S_KSQ: begin
                kind     = K_KC;
                kc_turbo = (op == OP_KECCAK && flags[0]);
            end
            S_KSO: begin
                cond      = (cnt == 16'd0) || out_ready;
                emit      = (cnt != 16'd0);
                emit_port = 1'b1;
                e_rd      = {1'b0, wi};
            end
            // ---------------------------------------------------------- key load
            S_KLM: begin
                cond   = in_valid;
                do_pop = 1'b1;
                key_we = 6'b010000 << cnt2[0];
            end
            S_KLH: begin
                cond        = in_valid;
                do_pop      = 1'b1;
                key_we      = (cnt2 <= 5'd3) ? (6'b000001 << cnt2[1:0]) : 6'd0;
                kvat_we     = (flags[2] && cnt2 >= 5'd4 && cnt2 <= 5'd7) ? (4'b0001 << cnt2[1:0]) : 4'd0;
                kvat_commit = flags[2] && (cnt2 == 5'd7);
            end
            S_KLT: begin
                cond      = trng_valid;
                trng_take = trng_valid;
                e_wreq    = 1'b1;
                e_wa      = {1'b0, wi};
                xsel      = 3'd5;
            end
            S_KLA: begin
                cond   = (wrem == 21'd0) || in_valid;
                do_pop = (wrem != 21'd0);
                e_wreq = (wrem != 21'd0);
                e_rd   = {1'b0, wi};
                e_wa   = {1'b0, wi};
                wsel   = 3'd1;
                xsel   = 3'd0;
            end
            S_KLD: begin
                e_wreq = 1'b1;
                e_rd   = {1'b0, wi};
                e_wa   = {1'b0, wi};
                wsel   = 3'd1;
                xsel   = 3'd1;
                imm    = 64'h1F;
            end
            S_KLE: begin
                e_wreq = 1'b1;
                e_rd   = 6'd16;
                e_wa   = 6'd16;
                wsel   = 3'd1;
                xsel   = 3'd1;
                imm    = PAD_END;
            end
            S_KLP: begin
                kind     = K_KC;
                kc_turbo = 1'b1;
            end
            S_KLK: begin
                e_rd        = {1'b0, cnt2};
                key_we      = (cnt2 <= 5'd3) ? (6'b000001 << cnt2[1:0]) : 6'd0;
                kvat_we     = (flags[2] && cnt2 >= 5'd4 && cnt2 <= 5'd7) ? (4'b0001 << cnt2[1:0]) : 4'd0;
                kvat_commit = flags[2] && (cnt2 == 5'd7);
            end
            // ---------------------------------------------------------- keyed block build
            S_BLD: begin
                e_wreq = !(bmode == 3'd0 && !isprf && (cnt2 == 5'd6 || cnt2 == 5'd7)) &&
                         !(bmode == 3'd5);
                e_wa   = {1'b0, cnt2};
                xsel   = 3'd6;
                unique case (bmode)
                    3'd0: begin
                        unique case (cnt2)
                            5'd0, 5'd1: begin wsel = 3'd2; e_rd = 6'd33 + {5'd0, cnt2[0]}; end
                            5'd2:       begin wsel = 3'd3; e_rd = 6'd32; end
                            5'd3:       begin wsel = 3'd2; e_rd = 6'd35; end
                            5'd4:       begin wsel = 3'd4; e_rd = 6'd36; end
                            5'd5:       begin xsel = 3'd1; imm = a3_word; end
                            5'd6, 5'd7: begin xsel = 3'd2; ksel = {2'd0, cnt2[0]}; end
                            5'd8:       begin xsel = 3'd1; imm = 64'h1F; end
                            5'd16:      begin xsel = 3'd1; imm = PAD_END; end
                            default: ;
                        endcase
                    end
                    3'd1: begin
                        unique case (cnt2)
                            5'd0, 5'd1: begin xsel = 3'd2; ksel = 3'd4 + {2'd0, cnt2[0]}; end
                            5'd2:       begin xsel = 3'd1; imm = {32'd0, ctmp}; end
                            5'd3:       begin xsel = 3'd1; imm = C_FRAM; end
                            5'd4:       begin xsel = 3'd1; imm = 64'h1F; end
                            5'd16:      begin xsel = 3'd1; imm = PAD_END; end
                            default: ;
                        endcase
                    end
                    3'd2: begin
                        unique case (cnt2)
                            5'd0, 5'd1: begin xsel = 3'd2; ksel = 3'd4 + {2'd0, cnt2[0]}; end
                            5'd2:       begin wsel = 3'd2; e_rd = 6'd32; end
                            5'd3:       begin xsel = 3'd1; imm = C_MASK; end
                            5'd4:       begin xsel = 3'd1; imm = 64'h1F; end
                            5'd16:      begin xsel = 3'd1; imm = PAD_END; end
                            default: ;
                        endcase
                    end
                    3'd3: begin
                        unique case (cnt2)
                            5'd0, 5'd1: begin xsel = 3'd2; ksel = 3'd4 + {2'd0, cnt2[0]}; end
                            5'd2:       begin xsel = 3'd1; imm = stat_word; end
                            5'd3, 5'd4: begin xsel = 3'd3; gsel = !cnt2[0]; end
                            5'd5, 5'd6, 5'd7, 5'd8: begin wsel = 3'd2; e_rd = 6'd27 + {1'b0, cnt2}; end
                            5'd9:       begin xsel = 3'd1; imm = 64'h1F; end
                            5'd16:      begin xsel = 3'd1; imm = PAD_END; end
                            default: ;
                        endcase
                    end
                    3'd4: begin // SpongeMacaroon seal: "DREGGVAT" || K_vat[0..3] || sh[0..7]
                        if (cnt2 == 5'd0)                     begin xsel = 3'd1; imm = C_VAT; end
                        else if (cnt2 >= 5'd1 && cnt2 <= 5'd4) begin xsel = 3'd1; imm = kvat_rdata; end
                        else if (cnt2 >= 5'd5 && cnt2 <= 5'd12) begin wsel = 3'd2; e_rd = 6'd32 + (cnt2 - 5'd5); end
                        else if (cnt2 == 5'd13)               begin xsel = 3'd1; imm = 64'h1F; end
                        else if (cnt2 == 5'd16)               begin xsel = 3'd1; imm = PAD_END; end
                    end
                    3'd5: begin // Incremental PUF block XOR absorb (keeps sponge chaining across blk 0..7!)
                        e_rd   = {1'b0, cnt2};
                        wsel   = 3'd1;
                        e_wreq = (cnt2 <= 5'd4) || (cnt2 == 5'd16);
                        unique case (cnt2)
                            5'd0:    begin xsel = 3'd1; imm = C_PUF ^ {61'd0, puf_blk}; end
                            5'd1:    begin xsel = 3'd1; imm = puf_word_out; end
                            5'd2:    begin xsel = 3'd1; imm = puf_recon_mode ? puf_vmask_in : puf_vmask_out; end
                            5'd3:    begin xsel = 3'd1; imm = {37'd0, puf_recon_mode ? puf_syn_in : puf_syn_out}; end
                            5'd4:    begin xsel = 3'd1; imm = 64'h1F; end
                            5'd16:   begin xsel = 3'd1; imm = PAD_END; end
                            default: ;
                        endcase
                    end
                    3'd6: begin // PUF public verification tag H_pub = TurboSHAKE256("DREGGCHK" || sh[0..3])
                        if (cnt2 == 5'd0)                     begin xsel = 3'd1; imm = C_PUF_CHK; end
                        else if (cnt2 >= 5'd1 && cnt2 <= 5'd4) begin wsel = 3'd2; e_rd = 6'd32 + (cnt2 - 5'd1); end
                        else if (cnt2 == 5'd5)                begin xsel = 3'd1; imm = 64'h1F; end
                        else if (cnt2 == 5'd16)               begin xsel = 3'd1; imm = PAD_END; end
                    end
                    default: begin // 3'd7: ZK execution grant: "DREGGZKG" || K_vat[0..3] || epoch
                        if (cnt2 == 5'd0)                     begin xsel = 3'd1; imm = C_ZKG; end
                        else if (cnt2 >= 5'd1 && cnt2 <= 5'd4) begin xsel = 3'd1; imm = kvat_rdata; end
                        else if (cnt2 == 5'd5)                begin xsel = 3'd1; imm = {48'd0, arg}; end
                        else if (cnt2 == 5'd6)                begin xsel = 3'd1; imm = 64'h1F; end
                        else if (cnt2 == 5'd16)               begin xsel = 3'd1; imm = PAD_END; end
                    end
                endcase
            end
            // ---------------------------------------------------------- FRAM anchor
            S_AR0, S_AW6: an_start = 1'b1;
            S_AW1: begin
                an_start = 1'b1;
                an_write = 1'b1;
            end
            S_AR1: cond = an_stb;
            S_AR2: an_go = 1'b1;
            S_AR3, S_AR4, S_AW8, S_AW9: begin
                cond  = an_stb;
                an_go = an_stb;
                e_rd  = {5'd0, (st == S_AR4 || st == S_AW9)};
            end
            S_AW7: begin
                cond  = an_stb;
                an_go = an_stb;
            end
            S_AR5, S_AW5, S_AWA: cond = an_done;
            S_AW2: begin
                cond  = an_stb;
                an_go = an_stb;
            end
            S_AW3, S_AW4: begin
                cond  = an_stb;
                an_go = an_stb;
                e_rd  = {5'd0, (st == S_AW4)};
            end
            // ---------------------------------------------------------- Cut-the-Hash + EAL6+ Chain-End Check
            S_CTG, S_HVG: begin
                kind = K_GF;
                xsel = 3'd1;
                imm  = hdr_word;
            end
            S_CTL: begin
                kind      = K_GF;
                cond      = in_valid;
                xsel      = 3'd0;
                e_wlaunch = 1'b1;
                e_wa      = 6'd32 + {1'b0, cnt2};
                do_pop    = 1'b1;
            end
            S_CTT: begin
                cond   = in_valid;
                do_pop = 1'b1;
                e_rd   = {5'd0, cnt2[0]};
            end
            S_CA2: e_rd = 6'd32;
            S_CTS: e_rd = 6'd37 + {4'd0, widx};
            S_CM0, S_CM1: begin
                e_wreq = 1'b1;
                e_rd   = {5'd0, (st == S_CM1)};
                e_wa   = 6'd6 + {5'd0, (st == S_CM1)};
                wsel   = 3'd2;
            end
            S_CY0: e_rd = 6'd0;
            S_CY1: begin
                e_rd   = 6'd1;
                e_wreq = (sym != symmask);
                e_wa   = 6'd6;
                xsel   = 3'd1;
                imm    = y_hold0;
            end
            S_CZ0: begin
                cond   = in_valid;
                do_pop = 1'b1;
                e_rd   = 6'd0;
            end
            S_CZ1: begin
                cond   = in_valid;
                do_pop = 1'b1;
                e_rd   = 6'd1;
            end
            S_CO: begin
                cond      = out_ready;
                emit      = 1'b1;
                emit_port = !self_chk;
                e_rd      = {5'd0, cnt2[0]};
                imm       = cnt2[0] ? y_hold1 : y_hold0;
            end
            // ---------------------------------------------------------- Houyhnhnm PUF + BCH (0x50)
            S_PF0: begin
                cond   = !puf_recon_mode || in_valid;
                do_pop = puf_recon_mode;
            end
            S_PF1: begin
                cond          = !puf_recon_mode || in_valid;
                do_pop        = puf_recon_mode;
                puf_start_blk = cond;
            end
            S_PF2: begin
                cond = puf_done && (puf_recon_mode || out_ready);
                emit = !puf_recon_mode;
                imm  = puf_vmask_out;
            end
            S_PF3: begin
                cond = puf_recon_mode || out_ready;
                emit = !puf_recon_mode;
                imm  = {37'd0, puf_syn_out};
            end
            S_PF4: begin
                e_rd   = {1'b0, cnt2};
                e_wa   = 6'd32 + {1'b0, cnt2};
                wsel   = 3'd2;
                e_wreq = (cnt2 <= 5'd7);
                if (!puf_recon_mode && !puf_any_err) begin
                    kvat_we     = (cnt2 <= 5'd3) ? (4'b0001 << cnt2[1:0]) : 4'd0;
                    kvat_commit = (cnt2 == 5'd3);
                    key_we      = (cnt2 >= 5'd4 && cnt2 <= 5'd9) ? (6'b000001 << (cnt2 - 5'd4)) : 6'd0;
                end
            end
            S_PF5: begin
                if (!puf_recon_mode) begin
                    cond      = out_ready;
                    emit      = 1'b1;
                    emit_port = 1'b1;
                    e_rd      = {1'b0, cnt2};
                end else if (cnt2 <= 5'd3) begin
                    cond   = in_valid;
                    do_pop = 1'b1;
                    e_rd   = {1'b0, cnt2};
                end else begin
                    e_rd        = (cnt2 <= 5'd11) ? (6'd32 + (cnt2 - 5'd4)) : (cnt2 - 5'd8);
                    kvat_we     = (!puf_any_err && !macdiff && cnt2 >= 5'd4 && cnt2 <= 5'd7)
                                  ? (4'b0001 << (cnt2 - 5'd4)) : 4'd0;
                    kvat_commit = (!puf_any_err && !macdiff && cnt2 == 5'd7);
                    key_we      = (!puf_any_err && !macdiff && cnt2 >= 5'd8 && cnt2 <= 5'd13)
                                  ? (6'b000001 << (cnt2 - 5'd8)) : 6'd0;
                end
            end
            // ---------------------------------------------------------- Houyhnhnm CapTP Vat (0x51, 0x53, Cap-0x41/0x42)
            S_VLD: begin
                cond         = in_valid;
                do_pop       = 1'b1;
                e_wreq       = 1'b1;
                e_wa         = 6'd32 + {1'b0, cnt2};
                xsel         = 3'd0;
                vat_pchk_clr = (cnt2 == 5'd0) && !(op == OP_VAT && !flags[0]);
                vat_pwe      = !(op == OP_VAT && !flags[0]);
            end
            S_VTG: begin
                cond         = in_valid;
                do_pop       = 1'b1;
                e_rd         = {1'b0, cnt2};
                vat_cchk_clr = (cnt2 == 5'd3) && (op == OP_VAT);
            end
            S_VAT: begin
                cond    = in_valid;
                do_pop  = 1'b1;
                e_rd    = 6'd32 + {1'b0, cnt2};
                e_wreq  = 1'b1;
                e_wa    = 6'd32 + {1'b0, cnt2};
                xsel    = 3'd0;
                vat_cwe = 1'b1;
            end
            S_VOT: begin
                cond      = out_ready;
                emit      = 1'b1;
                emit_port = 1'b1;
                e_rd      = (cnt2 < 5'd8) ? (6'd32 + {1'b0, cnt2}) : {1'b0, cnt2 - 5'd8};
            end
            S_VZK: ;
            // ---------------------------------------------------------- Houyhnhnm DB + NCO (0x52)
            S_DB0: begin
                cond             = in_valid;
                do_pop           = 1'b1;
                db_load_r0       = (cnt2 == 5'd0) && arg[0];
                db_load_r1       = (cnt2 == 5'd1) && arg[0];
                db_arm_responder = (cnt2 == 5'd2) && arg[0];
                db_step_round    = (cnt2 == 5'd2) && arg[1];
                db_launch_ping   = (cnt2 == 5'd2) && arg[2] && !arg[3];
                db_cal_ping      = (cnt2 == 5'd2) && arg[2] &&  arg[3];
                nco_pkt_load     = (cnt2 == 5'd1) && arg[4] &&  arg[12];
            end
            S_DBO: begin
                cond = out_ready;
                emit = 1'b1;
                unique case (cnt2[1:0])
                    2'd0:    imm = {nfc_rx_frames, nfc_quorum_flags, 20'd0, nco_tx_active, nfc_token_valid,
                                    db_responder_armed, db_dist_timeout, db_dist_valid, db_rounds_done};
                    2'd1:    imm = {32'd0, db_dist_cycles};
                    2'd2:    imm = db_chal_log;
                    default: imm = db_resp_log;
                endcase
            end
            // ---------------------------------------------------------- verifier VM
            S_HVR: begin
                if (wrem == 21'd0) kind = K_NONE;
                else begin
                    kind   = K_GF;
                    cond   = in_valid;
                    xsel   = 3'd0;
                    do_pop = 1'b1;
                end
            end
            S_HVH: begin
                kind  = (ha[2:0] != 3'd0) ? K_FE : K_NONE;
                fe_op = F_MOV;
                fe_d  = rb(ha[2:0]);
                fe_s1 = 6'd0;
            end
            S_HVA: begin
                kind  = K_FE;
                fe_op = (hop == 4'd2) ? F_EMUL : (hop == 4'd3) ? F_EADD : F_ESUB;
                fe_d  = rb(ha[2:0]);
                fe_s1 = rb(hb[2:0]);
                fe_s2 = rb(hc[2:0]);
            end
            S_HVE: begin
                kind  = K_FE;
                fe_op = F_EEQ;
                fe_s1 = rb(hb[2:0]);
                fe_s2 = rb(hc[2:0]);
            end
            S_HVP: begin
                kind  = K_FE;
                fe_op = F_LDRES;
                fe_s1 = rb(hb[2:0]);
            end
            S_HVI: begin
                kind  = K_FE;
                fe_op = F_LDRES;
                fe_s1 = rb(hb[2:0]) + {4'd0, ha[1:0]};
            end
            S_HVN: begin
                cond   = (dleft == 16'd0) || in_valid;
                do_pop = (dleft != 16'd0);
            end
            S_HVF: begin
                e_wreq      = 1'b1;
                e_rd        = 6'd12 + {1'b0, cnt2};
                e_wa        = 6'd32 + {1'b0, cnt2};
                wsel        = 3'd2;
                zk_latch_we = verdict;
                zk_latch_set = verdict && (cnt2 == 5'd3);
            end
            S_HVS: begin
                cond = out_ready;
                emit = 1'b1;
                imm  = stat_word;
            end
            default: ;
        endcase
        if (st == S_IDLE && (in_data[15:8] == OP_FOLD || in_data[15:8] == OP_HEM))
            zk_latch_clr = 1'b1;
        if (emit && !emit_port) xsel = 3'd1;
    end

    assign vat_commit_inv = fire && (
        (st == S_VZK && vat_inv_ok) ||
        (st == S_KSW && op == OP_PRFMSG && cap_mode && key_valid && !macdiff && vat_inv_ok) ||
        (st == S_CTD && cap_mode && key_valid && !macdiff && vat_inv_ok && (!stateful || pubgen)) ||
        (st == S_CA3 && cap_mode && rcmp)
    );

    assign key_d    = (st == S_KLK || st == S_PF4 || st == S_PF5) ? port : in_data;
    assign an_tx    = (st == S_AW2) ? {32'd0, ctmp} : port;
    assign cmp_ne   = (st == S_AW7) ? (an_rx != {32'd0, ctmp})
                    : (st == S_CTT) ? (in_data != (port ^ (cnt2[0] ? gf_acc[127:64] : gf_acc[63:0])))
                    : (st == S_VTG || st == S_PF5) ? (in_data != port)
                    : (an_rx != port);
    assign fe_start = launch && (kind == K_FE);
    assign kc_start = launch && (kind == K_KC);
    assign gf_start = launch && (kind == K_GF);
    assign in_pop   = (fire && do_pop) || bg_sh_can_take;
    assign out_push = fire && emit;
    assign out_data = emit_port ? port : imm;
    assign e_we     = (fire && e_wreq) || (launch && e_wlaunch);

    // ------------------------------------------------------------------ sequencing
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            st              <= S_IDLE;
            ret             <= S_IDLE;
            ret2            <= S_IDLE;
            ret3            <= S_IDLE;
            w               <= 1'b0;
            steps           <= 16'h0000;
            steps_inv_q     <= 16'hFFFF;
            verify_ok       <= 1'b0;
            key_valid       <= 1'b0;
            vat_mint_locked <= 1'b0;
            hwm_valid       <= 1'b0;
            fault_anchor    <= 1'b0;
            fault_mac       <= 1'b0;
            fault_laser_dfa <= 1'b0;
            nco_en          <= 1'b0;
            nco_mode        <= 2'd0;
            nco_sym_shift   <= 4'd0;
            nco_ftw_base    <= 32'd0;
            nco_ftw_delta   <= 32'd0;
            csr             <= 64'h0000_0000_0268_C01F;
        end else if (zeroize_q || control_bad || fault_control || fault_laser_dfa) begin
            st              <= S_DEAD;
            w               <= 1'b0;
            key_valid       <= 1'b0;
            vat_mint_locked <= 1'b0;
            verify_ok       <= 1'b0;
            hwm_valid       <= 1'b0;
        end else begin
            if (launch) w <= 1'b1;
            if (fire) begin
                w <= 1'b0;
                unique case (st)
                    S_IDLE: begin
                        ret  <= S_IDLE;
                        ret2 <= S_IDLE;
                        ret3 <= S_IDLE;
                        if (in_data[7:0] != 8'h51) begin
                            st <= S_DRAIN;
                        end else begin
                            unique case (in_data[15:8])
                                OP_PING: begin
                                    ret <= S_PING;
                                    st  <= (in_data[47:24] == 24'd0) ? S_HDR : S_DRAIN;
                                end
                                OP_CSR:  st <= (in_data[47:24] == 24'd8) ? S_CSR : S_DRAIN;
                                OP_BIST: begin
                                    verify_ok <= 1'b0;
                                    st        <= (in_data[47:24] == 24'd0) ? S_BSW : S_DRAIN;
                                end
                                OP_P2: begin
                                    verify_ok <= 1'b0;
                                    if (in_data[16])
                                        st <= (in_data[47:24] == 24'd96) ? S_P2R : S_DRAIN;
                                    else if (in_data[47:24] < 24'd40 || in_data[26:24] != 3'd0)
                                        st <= S_DRAIN;
                                    else begin
                                        ret <= S_HDR;
                                        st  <= S_HSZ;
                                    end
                                end
                                OP_MERKLE: begin
                                    verify_ok <= 1'b0;
                                    if (in_data[53:48] == 6'd0 || in_data[53:48] > 6'd62 ||
                                        in_data[47:24] != 24'd96 + {16'd0, in_data[53:48], 2'd0} * 24'd8)
                                        st <= S_DRAIN;
                                    else st <= S_MOK;
                                end
                                OP_KECCAK: st <= S_KSW;
                                OP_PRFMSG: begin
                                    if (in_data[18]) begin // cap_mode: first 96 bytes are SpongeMacaroon
                                        if (!vat_ready || !key_valid) st <= S_DRAIN;
                                        else if (in_data[47:24] < 24'd96) st <= S_DRAIN;
                                        else begin
                                            ret2 <= S_KSW;
                                            st   <= S_VLD;
                                        end
                                    end else st <= S_KSW;
                                end
                                OP_FOLD, OP_HEM: begin
                                    verify_ok <= 1'b0;
                                    st <= (in_data[26:24] != 3'd0) ? S_DRAIN : S_HVG;
                                end
                                OP_KEYLOAD: begin
                                    if (key_valid) st <= S_DRAIN;
                                    else if (in_data[16] ? (in_data[47:24] != (in_data[18] ? 24'd80 : 24'd48))
                                                         : (in_data[47:24] < 24'd16 || in_data[47:24] > 24'd96 ||
                                                            in_data[26:24] != 3'd0))
                                        st <= S_DRAIN;
                                    else st <= S_KLM;
                                end
                                OP_CTH: begin
                                    logic [23:0] exp_len;
                                    exp_len = (in_data[18] ? 24'd160 : 24'd80) +
                                              ((in_data[19] && !in_data[16]) ? {12'd0, in_data[55:48], 4'd0} : 24'd0);
                                    if (in_data[47:24] != exp_len || in_data[60:56] == 5'd0 ||
                                        in_data[60:56] > 5'd16 || in_data[55:48] == 8'd0)
                                        st <= S_DRAIN;
                                    else if (in_data[18]) begin
                                        if (!vat_ready || !key_valid) st <= S_DRAIN;
                                        else begin
                                            ret2 <= S_CTG;
                                            st   <= S_VLD;
                                        end
                                    end else st <= S_CTG;
                                end
                                OP_PUF: begin
                                    if (in_data[16] ? (in_data[47:24] != 24'd160) : (in_data[47:24] != 24'd0))
                                        st <= S_DRAIN;
                                    else if (!in_data[16]) begin
                                        ret <= S_PF0;
                                        st  <= S_HDR;
                                    end else st <= S_PF0;
                                end
                                OP_VAT: begin
                                    if (!vat_ready) st <= S_DRAIN;
                                    else if (!in_data[16] && vat_mint_locked) st <= S_DRAIN;
                                    else if (in_data[47:24] != (in_data[16] ? 24'd160 : 24'd64))
                                        st <= S_DRAIN;
                                    else begin
                                        if (!in_data[16] && in_data[19]) vat_mint_locked <= 1'b1;
                                        ret2 <= in_data[16] ? S_VAT : S_HDR;
                                        st   <= S_VLD;
                                    end
                                end
                                OP_DB_NCO: begin
                                    st <= (in_data[47:24] == 24'd24) ? S_DB0 : S_DRAIN;
                                end
                                OP_VAT_ZK: begin
                                    if (!vat_ready || in_data[47:24] != 24'd96) st <= S_DRAIN;
                                    else begin
                                        ret2 <= S_VZK;
                                        st   <= S_VLD;
                                    end
                                end
                                default: st <= S_DRAIN;
                            endcase
                        end
                    end
                    S_DRAIN: if (wrem == 21'd0) st <= S_EHDR;
                    S_EHDR:  st <= S_WIPE;
                    S_HDR: begin
                        st <= ret;
                        if (ret == S_HDR) begin
                            ret <= S_IDLE;
                            st  <= S_OUTL;
                        end
                    end
                    S_OUTL: if (cnt2 + 5'd1 == olim) st <= ret;
                    S_WIPE: st <= S_IDLE;
                    S_PING: if (cnt2 == 5'd3) st <= S_IDLE;
                    S_CSR: begin
                        csr <= in_data;
                        ret <= S_IDLE;
                        st  <= S_HDR;
                    end
                    // ------------------------------------------------ OP_BIST
                    S_BSW: st <= S_BS0;
                    S_BS0: if (cnt2 == 5'd2) begin
                        ret3 <= S_BS1;
                        st   <= S_BKC;
                    end
                    S_BS1: st <= S_BS2;
                    S_BS2: begin
                        verify_ok <= ((port ^ gf_acc[63:0]) == BIST_GOLDEN_KAT);
                        ret       <= S_BSO;
                        st        <= S_HDR;
                    end
                    S_BSO: st <= S_WIPE;
                    // ------------------------------------------------ Poseidon2
                    S_P2R:  if (cnt2 == 5'd11) st <= S_P2RP;
                    S_P2RP: begin
                        ret <= S_HDR;
                        st  <= S_HDR;
                    end
                    S_HSZ: if (cnt2 == 5'd7) st <= S_HSD;
                    S_HSD: if (!bindw) st <= S_HSC;
                    S_HSC: if (hs_capsrc == 2'd1 || cnt2 == 5'd3) st <= S_HSN;
                    S_HSN: st <= S_HSL;
                    S_HSL: begin
                        if (hs_n == 16'd0) st <= S_HSF;
                        else if (!bindw && !hs_lat_now && hs_idx == 4'd7) st <= S_HSP;
                    end
                    S_HSP: st <= S_HSL;
                    S_HSF: st <= ret;
                    // ------------------------------------------------ Canopy
                    S_MK0: st <= S_MK1;
                    S_MK1: st <= S_MK2;
                    S_MK2: st <= S_MK3;
                    S_MK3: st <= S_MK4;
                    S_MK4: st <= S_MK5;
                    S_MK5: st <= S_MPS;
                    S_MPS: begin
                        if (cnt == 16'd0) st <= ret2;
                        else if (cnt2 == 5'd3) st <= S_MK0;
                    end
                    S_MOK: if (cnt2 == 5'd2) st <= S_MOI;
                    S_MOI: st <= S_MOL;
                    S_MOL: if (cnt2 == 5'd3) begin
                        ret2 <= S_MOR;
                        st   <= S_MPS;
                    end
                    S_MOR: if (cnt2 == 5'd3) st <= S_MOE;
                    S_MOE: begin
                        verify_ok <= fe_eq;
                        ret       <= S_MOV;
                        st        <= S_HDR;
                    end
                    S_MOV: begin
                        ret <= S_IDLE;
                        st  <= S_OUTL;
                    end
                    // ------------------------------------------------ Keccak + 1-Clock Block Absorb
                    S_KSW: begin
                        if (op == OP_PRFMSG) begin
                            if (!key_valid) st <= S_DRAIN;
                            else if (cap_mode && (macdiff || !vat_inv_ok)) begin
                                if (macdiff) fault_mac <= 1'b1;
                                st <= S_DRAIN;
                            end else st <= S_KSK;
                        end else st <= S_KSA;
                    end
                    S_KSK: if (cnt2 == 5'd1) st <= S_KSA;
                    S_KSA: begin
                        if (wrem == 21'd0) st <= S_KSD;
                        else if (wrem == 21'd1 && lenb != 3'd0) st <= S_KSD;
                        else if (wi == 5'd16) st <= S_KSP;
                    end
                    S_KSP: st <= (sh_mask != 8'd0) ? S_KSB : S_KSA;
                    S_KSB: st <= S_KSA;
                    S_KSD: st <= S_KSE;
                    S_KSE: st <= S_KSQ;
                    S_KSQ: begin
                        ret <= S_KSO;
                        st  <= S_HDR;
                    end
                    S_KSO: begin
                        if (cnt == 16'd0) st <= S_WIPE;
                        else if (wi == 5'd16 && cnt != 16'd1) st <= S_KSR;
                    end
                    S_KSR: st <= S_KSO;
                    // ------------------------------------------------ key load
                    S_KLM: if (cnt2 == 5'd1) begin
                        if (flags[0]) st <= S_KLH;
                        else if (!trng_ok) st <= S_DRAIN;
                        else st <= S_KLW;
                    end
                    S_KLH: if (cnt2 == (flags[2] ? 5'd7 : 5'd3)) begin
                        if (flags[2]) begin
                            // copy host K_vat words are loaded via S_KLK?Wait: in S_KLH cnt2=4..7 load into sponge then S_KLK!
                            st <= S_KLN;
                        end else st <= S_KLN;
                    end
                    S_KLW: st <= S_KLT;
                    S_KLT: if (wi == 5'd3) st <= S_KLA;
                    S_KLA: if (wrem == 21'd0) st <= S_KLD;
                    S_KLD: st <= S_KLE;
                    S_KLE: st <= S_KLP;
                    S_KLP: st <= S_KLK;
                    S_KLK: if (cnt2 == (flags[2] ? 5'd7 : 5'd3)) st <= S_KLZ;
                    S_KLZ: st <= S_KLN;
                    S_KLN: begin
                        key_valid <= 1'b1;
                        if (flags[1]) begin
                            ret3 <= S_AW1;
                            ret2 <= S_KLF;
                            st   <= S_BLD;
                        end else begin
                            ret <= S_IDLE;
                            st  <= S_HDR;
                        end
                    end
                    S_KLF: begin
                        if (!rcmp) begin
                            key_valid    <= 1'b0;
                            fault_anchor <= 1'b1;
                            st           <= S_DRAIN;
                        end else if (!aslot) begin
                            ret3 <= S_AW1;
                            st   <= S_BLD;
                        end else begin
                            hwm_valid <= 1'b1;
                            ret       <= S_IDLE;
                            st        <= S_HDR;
                        end
                    end
                    S_BLD: if (cnt2 == 5'd24) st <= S_BKC;
                    S_BKC: st <= ret3;
                    // ------------------------------------------------ FRAM anchor
                    S_AR0: st <= S_AR1;
                    S_AR1: begin ret3 <= S_AR2; st <= S_BLD; end
                    S_AR2: st <= S_AR3;
                    S_AR3: st <= S_AR4;
                    S_AR4: st <= S_AR5;
                    S_AR5: st <= ret2;
                    S_AW1: st <= S_AW2;
                    S_AW2: st <= S_AW3;
                    S_AW3: st <= S_AW4;
                    S_AW4: st <= S_AW5;
                    S_AW5: st <= S_AW6;
                    S_AW6: st <= S_AW7;
                    S_AW7: st <= S_AW8;
                    S_AW8: st <= S_AW9;
                    S_AW9: st <= S_AWA;
                    S_AWA: st <= ret2;
                    // ------------------------------------------------ Cut-the-Hash + Chain-End Self-Check
                    S_CTG: st <= S_CTL;
                    S_CTL: if (cnt2 == 5'd7) begin
                        if (cap_mode) st <= S_CTD;
                        else if (pubgen) st <= S_CTT;
                        else begin
                            ret3 <= S_CTT;
                            st   <= S_BLD;
                        end
                    end
                    S_CTT: if (cnt2 == 5'd1) st <= S_CTD;
                    S_CTD: begin
                        if (!key_valid) st <= S_DRAIN;
                        else if (macdiff) begin
                            fault_mac <= 1'b1;
                            st        <= S_DRAIN;
                        end else if (cap_mode && !vat_inv_ok) begin
                            st <= S_DRAIN;
                        end else if (stateful && !pubgen) begin
                            ret2 <= S_CA0;
                            st   <= S_AR0;
                        end else begin
                            ret <= S_CTS;
                            st  <= S_HDR;
                        end
                    end
                    S_CA0: begin ret2 <= S_CA1; st <= S_AR0; end
                    S_CA1: st <= S_CA2;
                    S_CA2: begin
                        if (!anyv) st <= S_DRAIN;
                        else if (hwm_valid && cur < hwm) begin
                            fault_anchor <= 1'b1;
                            st           <= S_DRAIN;
                        end else if (port[31:0] < cur || port[31:0] == 32'hFFFF_FFFF) begin
                            st <= S_DRAIN;
                        end else begin
                            ret3 <= S_AW1;
                            ret2 <= S_CA3;
                            st   <= S_BLD;
                        end
                    end
                    S_CA3: begin
                        if (!rcmp) begin
                            fault_anchor <= 1'b1;
                            st           <= S_DRAIN;
                        end else begin
                            hwm_valid <= 1'b1;
                            ret       <= S_CTS;
                            st        <= S_HDR;
                        end
                    end
                    S_CTS: begin
                        if (ci == nch) st <= S_WIPE;
                        else begin
                            logic [15:0] st_init;
                            st_init = pubgen ? (is_fors ? 16'd1 : symmask) : (is_fors ? 16'd0 : (port_sh[15:0] & symmask));
                            steps       <= st_init;
                            steps_inv_q <= ~st_init;
                            ret3        <= S_CKD;
                            st          <= S_BLD;
                        end
                    end
                    S_CM0: st <= S_CM1;
                    S_CM1: st <= S_BLD;
                    S_CKD: begin
                        if (steps == 16'd0) begin
                            if (self_chk && !chk_cont) st <= S_CY0;
                            else if (self_chk && chk_cont) st <= S_CZ0;
                            else st <= S_CO;
                        end else begin
                            steps       <= steps - 16'd1;
                            steps_inv_q <= steps_inv_q + 16'd1;
                            st          <= S_CM0;
                        end
                    end
                    S_CY0: st <= S_CY1;
                    S_CY1: begin
                        if (sym == symmask) begin
                            st <= S_CZ0;
                        end else begin
                            logic [15:0] rem_st;
                            rem_st      = symmask - sym - 16'd1;
                            steps       <= rem_st;
                            steps_inv_q <= ~rem_st;
                            ret3        <= S_CKD;
                            st          <= S_CM1; // copies st[1] -> st[7] then enters S_BLD!
                        end
                    end
                    S_CZ0: st <= S_CZ1;
                    S_CZ1: begin
                        // Compare second half of enrolled PK_end against computed chain end!
                        if ((dfa_diff != 64'd0) || ((port ^ in_data) != 64'd0) || (hj != symmask)) begin
                            fault_laser_dfa <= 1'b1; // 1-clock emergency zeroization + FAULT!
                            st              <= S_DEAD;
                        end else begin
                            st <= S_CZ2;
                        end
                    end
                    S_CZ2: begin
                        // Staggered 2nd-cycle verification check (Subcarbon R0 §5.2 Rule 3!)
                        if (dfa_diff != 64'd0) begin
                            fault_laser_dfa <= 1'b1;
                            st              <= S_DEAD;
                        end else st <= S_CO;
                    end
                    S_CO: if (cnt2 == 5'd1) st <= S_CTS;
                    // ------------------------------------------------ Houyhnhnm PUF + BCH (0x50)
                    S_PF0: st <= S_PF1;
                    S_PF1: st <= S_PF2;
                    S_PF2: st <= S_PF3;
                    S_PF3: begin
                        ret3 <= (puf_blk == 3'd7) ? S_PF4 : S_PF0;
                        st   <= S_BLD;
                    end
                    S_PF4: if (cnt2 == 5'd9) begin
                        if (!puf_recon_mode && !puf_any_err) key_valid <= 1'b1;
                        ret3 <= S_PF5;
                        st   <= S_BLD;
                    end
                    S_PF5: begin
                        if (!puf_recon_mode) begin
                            if (cnt2 == 5'd3) st <= S_WIPE;
                        end else if (cnt2 == 5'd3) begin
                            if (puf_any_err || macdiff || cmp_ne) st <= S_EHDR;
                        end else if (cnt2 == 5'd13) begin
                            key_valid <= 1'b1;
                            ret       <= S_BSO;
                            st        <= S_HDR;
                        end
                    end
                    // ------------------------------------------------ Houyhnhnm CapTP Vat (0x51, 0x53)
                    S_VLD: if (cnt2 == 5'd7) begin
                        ret3 <= (op == OP_VAT && !flags[0]) ? S_HDR : S_VTG;
                        if (op == OP_VAT && !flags[0]) ret <= S_VOT;
                        st   <= S_BLD;
                    end
                    S_VTG: if (cnt2 == 5'd3) begin
                        if (macdiff || cmp_ne) begin
                            fault_mac <= 1'b1;
                            st        <= S_DRAIN;
                        end else st <= ret2;
                    end
                    S_VAT: if (cnt2 == 5'd7) begin
                        ret3 <= S_HDR;
                        ret  <= S_VOT;
                        st   <= vat_att_step_ok ? S_BLD : S_DRAIN;
                    end
                    S_VOT: if (cnt2 == 5'd11) st <= S_WIPE;
                    S_VZK: begin
                        if (!vat_inv_ok) st <= S_DRAIN;
                        else begin
                            ret3 <= S_HDR;
                            ret  <= S_OUTL;
                            st   <= S_BLD;
                        end
                    end
                    // ------------------------------------------------ Houyhnhnm DB + NCO (0x52)
                    S_DB0: begin
                        if (cnt2 == 5'd0 && arg[4]) begin
                            nco_en        <= arg[7];
                            nco_mode      <= arg[6:5];
                            nco_sym_shift <= arg[11:8];
                            nco_ftw_base  <= in_data[31:0];
                            nco_ftw_delta <= in_data[63:32];
                        end
                        if (cnt2 == 5'd2) begin
                            ret <= S_DBO;
                            st  <= S_HDR;
                        end
                    end
                    S_DBO: if (cnt2 == 5'd3) st <= S_IDLE;
                    // ------------------------------------------------ verifier VM
                    S_HVG: st <= S_HVR;
                    S_HVR: st <= (wrem == 21'd0) ? S_HVF : S_HVD;
                    S_HVD: begin
                        unique case (hop)
                            4'd1: begin
                                if (dleft == 16'd0) st <= S_HVN;
                                else begin ret <= S_HVH; st <= S_HSZ; end
                            end
                            4'd2, 4'd3, 4'd4: st <= S_HVA;
                            4'd5: st <= (dleft != 16'd4) ? S_HVN : S_HVL;
                            4'd6: st <= S_HVE;
                            4'd7: st <= S_HVP;
                            4'd8: st <= (ha[5:0] == 6'd0 || ha[5:0] > 6'd62 ||
                                         dleft != 16'd1 + {8'd0, ha[5:0], 2'd0}) ? S_HVN : S_HVM;
                            4'd9: st <= S_HVI;
                            default: st <= S_HVN;
                        endcase
                    end
                    S_HVH, S_HVA, S_HVE, S_HVQ, S_HVJ: st <= S_HVN;
                    S_HVL: if (!bindw && cnt2 == 5'd3) st <= S_HVN;
                    S_HVP: st <= S_HVQ;
                    S_HVM: begin ret2 <= S_HVN; st <= S_MPS; end
                    S_HVI: st <= S_HVJ;
                    S_HVN: if (dleft == 16'd0) st <= S_HVR;
                    S_HVF: if (cnt2 == 5'd3) begin
                        verify_ok <= verdict;
                        ret3      <= S_HDR;
                        ret       <= S_HVS;
                        st        <= S_BLD;
                    end
                    S_HVS: begin
                        ret <= S_HVC;
                        st  <= S_OUTL;
                    end
                    S_HVC: begin
                        ret <= S_IDLE;
                        st  <= S_OUTL;
                    end
                    default: st <= S_DEAD;
                endcase
            end
        end
    end

    // Non-secret datapath & framing registers (synchronous reset -> dffq_1 area savings + 0 GLS X!)
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            op            <= '0;
            flags         <= '0;
            arg           <= '0;
            wrem          <= '0;
            lenb          <= '0;
            rlen          <= '0;
            rcode         <= '0;
            rerr          <= 1'b0;
            rok           <= 1'b0;
            cnt           <= '0;
            cnt2          <= '0;
            wi            <= '0;
            obase         <= '0;
            olim          <= '0;
            partial       <= 1'b0;
            sh_fill       <= '0;
            sh_mask       <= '0;
            hs_n          <= '0;
            hs_k          <= '0;
            hs_idx        <= '0;
            hs_first      <= 1'b0;
            hs_ph         <= 1'b0;
            gfdone        <= 1'b0;
            hs_capsrc     <= '0;
            hs_capreg     <= '0;
            hs_latch      <= '0;
            hs_skip       <= '0;
            idx_armed     <= 1'b0;
            midx          <= '0;
            lidx          <= '0;
            mk_kb         <= '0;
            hop           <= '0;
            ha            <= '0;
            hb            <= '0;
            hc            <= '0;
            dleft         <= '0;
            recidx        <= '0;
            fidx          <= '0;
            inrec         <= 1'b0;
            fail          <= 1'b0;
            fset          <= 1'b0;
            noncanon      <= 1'b0;
            verdict       <= 1'b0;
            cur           <= '0;
            hwm           <= '0;
            ctmp          <= '0;
            v0            <= 1'b0;
            anyv          <= 1'b0;
            older         <= 1'b0;
            aslot         <= 1'b0;
            rcmp          <= 1'b0;
            hi0           <= 1'b0;
            macdiff       <= 1'b0;
            is_fors       <= 1'b0;
            isprf         <= 1'b0;
            bmode         <= '0;
            ci            <= '0;
            widx          <= '0;
            sh            <= '0;
            sym           <= '0;
            hj            <= '0;
            y_hold0       <= '0;
            y_hold1       <= '0;
            dfa_diff      <= '0;
            chk_cont      <= 1'b0;
            puf_recon_mode  <= 1'b0;
            puf_margin      <= 6'd4;
            puf_noise_flips <= 3'd0;
            puf_vmask_in    <= '0;
            puf_syn_in      <= '0;
            puf_blk         <= '0;
            puf_any_err     <= 1'b0;
            puf_corr_tot    <= '0;
        end else if (!(zeroize_q || control_bad || fault_control || fault_laser_dfa)) begin
            if (in_pop) wrem <= wrem - 21'd1;
            if (in_pop && inrec) dleft <= dleft - 16'd1;
            if (bg_sh_can_take) begin
                sh_mask[sh_fill[2:0]] <= 1'b1;
                sh_fill               <= sh_fill + 4'd1;
            end
            if (fire) begin
                unique case (st)
                    S_IDLE: begin
                        op        <= in_data[15:8];
                        flags     <= in_data[23:16];
                        lenb      <= in_data[26:24];
                        wrem      <= in_data[47:27] + {20'd0, |in_data[26:24]};
                        arg       <= in_data[63:48];
                        rerr      <= 1'b0;
                        rok       <= 1'b1;
                        rcode     <= '0;
                        rlen      <= '0;
                        cnt       <= '0;
                        cnt2      <= '0;
                        wi        <= '0;
                        partial   <= 1'b0;
                        sh_fill   <= '0;
                        sh_mask   <= '0;
                        fail      <= 1'b0;
                        fset      <= 1'b0;
                        noncanon  <= 1'b0;
                        recidx    <= '0;
                        fidx      <= '0;
                        inrec     <= 1'b0;
                        hs_k      <= '0;
                        gfdone    <= 1'b0;
                        macdiff   <= 1'b0;
                        idx_armed <= 1'b0;
                        chk_cont  <= 1'b0;
                        if (in_data[7:0] != 8'h51) begin
                            rcode <= E_MAGIC;
                        end else begin
                            unique case (in_data[15:8])
                                OP_PING: begin
                                    rlen <= 24'd32;
                                    if (in_data[47:24] != 24'd0) rcode <= E_LEN;
                                end
                                OP_CSR:  if (in_data[47:24] != 24'd8) rcode <= E_LEN;
                                OP_BIST: if (in_data[47:24] != 24'd0) rcode <= E_LEN;
                                OP_P2: begin
                                    if (in_data[16]) begin
                                        if (in_data[47:24] != 24'd96) rcode <= E_LEN;
                                    end else if (in_data[47:24] < 24'd40 || in_data[26:24] != 3'd0) begin
                                        rcode <= E_LEN;
                                    end else begin
                                        hs_n      <= in_data[42:27] - 16'd5;
                                        hs_capsrc <= 2'd0;
                                        hs_latch  <= 3'd0;
                                        hs_skip   <= 2'd0;
                                    end
                                end
                                OP_MERKLE: begin
                                    if (in_data[53:48] == 6'd0 || in_data[53:48] > 6'd62 ||
                                        in_data[47:24] != 24'd96 + {16'd0, in_data[53:48], 2'd0} * 24'd8)
                                        rcode <= E_LEN;
                                end
                                OP_KECCAK: ;
                                OP_PRFMSG: begin
                                    y_hold1  <= {48'd0, in_data[63:48]};
                                    dfa_diff <= 64'd0;
                                    if (in_data[18]) begin
                                        if (!vat_ready || !key_valid) rcode <= E_NOKEY;
                                        else if (in_data[47:24] < 24'd96) rcode <= E_LEN;
                                    end
                                end
                                OP_FOLD, OP_HEM: if (in_data[26:24] != 3'd0) rcode <= E_LEN;
                                OP_KEYLOAD: begin
                                    if (key_valid) rcode <= E_KEYSET;
                                    else if (in_data[16] ? (in_data[47:24] != (in_data[18] ? 24'd80 : 24'd48))
                                                         : (in_data[47:24] < 24'd16 || in_data[47:24] > 24'd96 ||
                                                            in_data[26:24] != 3'd0))
                                        rcode <= E_LEN;
                                end
                                OP_CTH: begin
                                    logic [23:0] exp_len;
                                    exp_len = (in_data[18] ? 24'd160 : 24'd80) +
                                              ((in_data[19] && !in_data[16]) ? {12'd0, in_data[55:48], 4'd0} : 24'd0);
                                    if (in_data[47:24] != exp_len || in_data[60:56] == 5'd0 ||
                                        in_data[60:56] > 5'd16 || in_data[55:48] == 8'd0)
                                        rcode <= E_LEN;
                                    else if (in_data[18] && (!vat_ready || !key_valid))
                                        rcode <= E_NOKEY;
                                end
                                OP_PUF: begin
                                    puf_recon_mode  <= in_data[16];
                                    puf_margin      <= (in_data[53:48] == 6'd0) ? 6'd4 : in_data[53:48];
                                    puf_noise_flips <= in_data[56:54];
                                    puf_blk         <= 3'd0;
                                    puf_any_err     <= 1'b0;
                                    puf_corr_tot    <= 8'd0;
                                    if (in_data[16] ? (in_data[47:24] != 24'd160) : (in_data[47:24] != 24'd0))
                                        rcode <= E_LEN;
                                    else if (!in_data[16])
                                        rlen <= 24'd160;
                                end
                                OP_VAT: begin
                                    if (!vat_ready) rcode <= E_NOKEY;
                                    else if (!in_data[16] && vat_mint_locked) rcode <= E_LOCKED;
                                    else if (in_data[47:24] != (in_data[16] ? 24'd160 : 24'd64))
                                        rcode <= E_LEN;
                                    else
                                        rlen <= 24'd96;
                                end
                                OP_DB_NCO: begin
                                    if (in_data[47:24] != 24'd24) rcode <= E_LEN;
                                    else                          rlen  <= 24'd32;
                                end
                                OP_VAT_ZK: begin
                                    y_hold1 <= {48'd0, in_data[63:48]};
                                    if (!vat_ready) rcode <= E_NOKEY;
                                    else if (in_data[47:24] != 24'd96) rcode <= E_LEN;
                                    else rlen <= 24'd32;
                                end
                                default: rcode <= E_OPCODE;
                            endcase
                        end
                    end
                    S_DRAIN: if (wrem == 21'd0) begin
                        rerr <= 1'b1;
                        rok  <= 1'b0;
                        rlen <= '0;
                    end
                    S_HDR: cnt2 <= '0;
                    S_OUTL: cnt2 <= cnt2 + 5'd1;
                    S_PING: cnt2 <= cnt2 + 5'd1;
                    S_BSW: cnt2 <= '0;
                    S_BS0: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd2) begin
                            cnt2  <= '0;
                            bmode <= 3'd1;
                        end
                    end
                    S_BS2: begin
                        logic [63:0] kat_w;
                        kat_w   = port ^ gf_acc[63:0];
                        y_hold0 <= kat_w;
                        verdict <= (kat_w == BIST_GOLDEN_KAT);
                        rok     <= (kat_w == BIST_GOLDEN_KAT);
                        rlen    <= 24'd8;
                    end
                    S_P2R: cnt2 <= cnt2 + 5'd1;
                    S_P2RP: begin
                        rlen  <= 24'd96;
                        obase <= 6'd0;
                        olim  <= 5'd12;
                    end
                    S_HSZ: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd7) begin
                            cnt2   <= '0;
                            gfdone <= 1'b0;
                        end
                    end
                    S_HSD: begin
                        if (bindw) gfdone <= 1'b1;
                        else begin
                            gfdone <= 1'b0;
                            if (hs_k != 16'd0) hs_k <= hs_k - 16'd1;
                        end
                    end
                    S_HSC: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (hs_capsrc == 2'd1 || cnt2 == 5'd3) cnt2 <= '0;
                    end
                    S_HSN: begin
                        hs_idx   <= 4'd2;
                        hs_first <= 1'b1;
                        hs_ph    <= 1'b0;
                    end
                    S_HSL: if (hs_n != 16'd0) begin
                        if (bindw) gfdone <= 1'b1;
                        else if (hs_lat_now) hs_ph <= 1'b1;
                        else begin
                            if (hs_k == 16'd0 && in_ge_p && (op != OP_P2)) noncanon <= 1'b1;
                            gfdone <= 1'b0;
                            hs_ph  <= 1'b0;
                            if (hs_k != 16'd0) hs_k <= hs_k - 16'd1;
                            hs_n   <= hs_n - 16'd1;
                            hs_idx <= hs_idx + 4'd1;
                        end
                    end
                    S_HSP: begin
                        hs_first <= 1'b0;
                        hs_idx   <= '0;
                    end
                    S_HSF: begin
                        rlen  <= 24'd32;
                        obase <= 6'd0;
                        olim  <= 5'd4;
                    end
                    S_MK5: begin
                        midx <= {1'b0, midx[62:1]};
                        cnt  <= cnt - 16'd1;
                        cnt2 <= '0;
                    end
                    S_MPS: if (cnt != 16'd0) begin
                        if (in_ge_p) noncanon <= 1'b1;
                        cnt2 <= cnt2 + 5'd1;
                    end
                    S_MOK: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd2) cnt2 <= '0;
                    end
                    S_MOI: begin
                        midx  <= (63'd1 << arg[5:0]) | {1'b0, in_data[61:0]};
                        lidx  <= in_data[61:0];
                        mk_kb <= 6'd16;
                    end
                    S_MOL: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd3) begin
                            cnt2 <= '0;
                            cnt  <= {10'd0, arg[5:0]};
                        end
                    end
                    S_MOR: cnt2 <= cnt2 + 5'd1;
                    S_MOE: begin
                        verdict <= fe_eq;
                        rok     <= fe_eq;
                        rlen    <= 24'd40;
                    end
                    S_MOV: begin
                        cnt2  <= '0;
                        obase <= 6'd32;
                        olim  <= 5'd4;
                    end
                    S_KSW: begin
                        cnt2    <= '0;
                        wi      <= '0;
                        sh_fill <= '0;
                        sh_mask <= '0;
                        if (op == OP_PRFMSG) begin
                            if (!key_valid) rcode <= E_NOKEY;
                            else if (cap_mode && macdiff) rcode <= E_MAC;
                            else if (cap_mode && !vat_inv_ok) rcode <= E_CAP;
                        end
                    end
                    S_KSK: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd1) wi <= 5'd2;
                    end
                    S_KSA: begin
                        if (wrem == 21'd1 && lenb != 3'd0) begin
                            partial <= 1'b1;
                        end else if (wrem != 21'd0) begin
                            if (wi == 5'd16) begin
                                wi      <= '0;
                                sh_fill <= '0;
                                sh_mask <= '0;
                            end else wi <= wi + 5'd1;
                        end
                    end
                    S_KSB: begin
                        wi      <= {1'b0, sh_fill};
                        sh_fill <= '0;
                        sh_mask <= '0;
                    end
                    S_KSQ: begin
                        cnt  <= (op == OP_KECCAK) ? {8'd0, arg[15:8]} : 16'd2;
                        rlen <= (op == OP_KECCAK) ? {13'd0, arg[15:8], 3'd0} : 24'd16;
                        wi   <= '0;
                    end
                    S_KSO: if (cnt != 16'd0) begin
                        cnt <= cnt - 16'd1;
                        if (wi == 5'd16 && cnt != 16'd1) wi <= '0;
                        else wi <= wi + 5'd1;
                    end
                    S_KLM: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd1) begin
                            cnt2 <= '0;
                            if (!flags[0] && !trng_ok) rcode <= E_TRNG;
                        end
                    end
                    S_KLH: cnt2 <= cnt2 + 5'd1;
                    S_KLW: wi <= '0;
                    S_KLT: wi <= wi + 5'd1;
                    S_KLA: if (wrem != 21'd0 && wi != 5'd15) wi <= wi + 5'd1;
                    S_KLP: cnt2 <= '0;
                    S_KLK: cnt2 <= cnt2 + 5'd1;
                    S_KLN: begin
                        ctmp  <= '0;
                        aslot <= 1'b0;
                        if (flags[1]) begin
                            bmode <= 3'd1;
                            cnt2  <= '0;
                        end
                    end
                    S_KLF: begin
                        if (!rcmp) rcode <= E_ANCHOR_IO;
                        else if (!aslot) begin
                            aslot <= 1'b1;
                            bmode <= 3'd1;
                            cnt2  <= '0;
                        end else hwm <= '0;
                    end
                    S_BLD: cnt2 <= cnt2 + 5'd1;
                    S_BKC: begin
                        cnt2 <= '0;
                        if (bmode == 3'd0) begin
                            if (!isprf) hj <= hj + 16'd1;
                            isprf <= 1'b0;
                        end
                    end
                    S_AR1: begin
                        ctmp  <= an_rx[31:0];
                        hi0   <= (an_rx[63:32] == 32'd0);
                        bmode <= 3'd1;
                        cnt2  <= '0;
                    end
                    S_AR3: rcmp <= !cmp_ne && hi0;
                    S_AR4: rcmp <= rcmp && !cmp_ne;
                    S_AW7: rcmp <= !cmp_ne;
                    S_AW8, S_AW9: rcmp <= rcmp && !cmp_ne;
                    S_CTG: cnt2 <= '0;
                    S_CTL: begin
                        if (cnt2 == 5'd0) y_hold0  <= in_data;
                        if (cnt2 == 5'd1) y_hold1  <= in_data;
                        if (cnt2 == 5'd2) dfa_diff <= in_data;
                        if (cnt2 == 5'd4) is_fors  <= (in_data[31:24] == 8'd3);
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd7) begin
                            cnt2 <= '0;
                            if (!cap_mode && !pubgen) bmode <= 3'd2;
                        end
                    end
                    S_CTT: begin
                        if (!pubgen && cmp_ne) macdiff <= 1'b1;
                        cnt2 <= cnt2 + 5'd1;
                    end
                    S_CTD: begin
                        cnt2 <= '0;
                        if (!key_valid) rcode <= E_NOKEY;
                        else if (macdiff) rcode <= E_MAC;
                        else if (cap_mode && !vat_inv_ok) rcode <= E_CAP;
                        else if (stateful && !pubgen) aslot <= 1'b0;
                        else begin
                            rlen <= {12'd0, nch, 4'd0};
                            ci   <= '0;
                            widx <= '0;
                            sh   <= '0;
                        end
                    end
                    S_CA0: begin
                        v0    <= rcmp;
                        cur   <= ctmp;
                        aslot <= 1'b1;
                    end
                    S_CA1: begin
                        anyv <= v0 | rcmp;
                        if (rcmp && (!v0 || ctmp >= cur)) begin
                            cur   <= ctmp;
                            older <= 1'b0;
                        end else older <= 1'b1;
                    end
                    S_CA2: begin
                        if (!anyv) rcode <= E_ANCHOR_EMPTY;
                        else if (hwm_valid && cur < hwm) rcode <= E_ROLLBACK;
                        else if (port[31:0] < cur || port[31:0] == 32'hFFFF_FFFF) rcode <= E_REUSE;
                        else begin
                            ctmp  <= port[31:0] + 32'd1;
                            aslot <= older;
                            bmode <= 3'd1;
                            cnt2  <= '0;
                        end
                    end
                    S_CA3: begin
                        if (!rcmp) rcode <= E_ANCHOR_IO;
                        else begin
                            hwm  <= ctmp;
                            rlen <= {12'd0, nch, 4'd0};
                            ci   <= '0;
                            widx <= '0;
                            sh   <= '0;
                        end
                    end
                    S_CTS: if (ci != nch) begin
                        sym      <= port_sh[15:0] & symmask;
                        chk_cont <= 1'b0;
                        if (sh + {2'd0, sw} + {2'd0, sw} > 7'd64) begin
                            sh   <= '0;
                            widx <= widx + 2'd1;
                        end else sh <= sh + {2'd0, sw};
                        hj    <= '0;
                        isprf <= 1'b1;
                        bmode <= 3'd0;
                        cnt2  <= '0;
                    end
                    S_CM1: cnt2 <= '0;
                    S_CKD: cnt2 <= '0;
                    S_CY0: begin
                        y_hold0  <= port;
                        dfa_diff <= DFA_CANARY_SEED;
                    end
                    S_CY1: begin
                        y_hold1  <= port;
                        chk_cont <= 1'b1;
                        bmode    <= 3'd0;
                        cnt2     <= '0;
                    end
                    S_CZ0: dfa_diff <= (dfa_diff ^ DFA_CANARY_SEED) | (port ^ in_data);
                    S_CZ1: begin
                        dfa_diff <= dfa_diff | (port ^ in_data);
                        cnt2     <= '0;
                    end
                    S_CO: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd1) ci <= ci + 8'd1;
                    end
                    S_PF0: if (puf_recon_mode) puf_vmask_in <= in_data;
                    S_PF1: if (puf_recon_mode) puf_syn_in   <= in_data[26:0];
                    S_PF2: begin
                        if (puf_blk_err) puf_any_err <= 1'b1;
                        puf_corr_tot <= puf_corr_tot + {4'd0, puf_corrected};
                    end
                    S_PF3: begin
                        cnt2  <= '0;
                        bmode <= 3'd5;
                        if (puf_blk != 3'd7) puf_blk <= puf_blk + 3'd1;
                    end
                    S_PF4: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd9) begin
                            cnt2  <= '0;
                            bmode <= 3'd6;
                        end
                    end
                    S_PF5: begin
                        if (puf_recon_mode && cnt2 <= 5'd3 && cmp_ne)
                            macdiff <= 1'b1;
                        if (puf_recon_mode && cnt2 == 5'd3 && (puf_any_err || macdiff || cmp_ne)) begin
                            rerr  <= 1'b1;
                            rok   <= 1'b0;
                            rlen  <= '0;
                            rcode <= E_PUF;
                        end else if (puf_recon_mode && cnt2 == 5'd13) begin
                            rlen    <= 24'd8;
                            rok     <= 1'b1;
                            y_hold0 <= {48'd0, 7'd0, !puf_any_err, puf_corr_tot};
                        end
                        cnt2 <= cnt2 + 5'd1;
                    end
                    S_VLD: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd7) begin
                            cnt2  <= '0;
                            bmode <= 3'd4;
                        end
                    end
                    S_VTG: begin
                        if (cmp_ne) macdiff <= 1'b1;
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd3) begin
                            cnt2 <= '0;
                            if (macdiff || cmp_ne) rcode <= E_MAC;
                        end
                    end
                    S_VAT: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd7) begin
                            cnt2  <= '0;
                            bmode <= 3'd4;
                            if (!vat_att_step_ok) rcode <= E_CAP;
                        end
                    end
                    S_VOT: cnt2 <= cnt2 + 5'd1;
                    S_VZK: begin
                        if (!vat_inv_ok) rcode <= E_CAP;
                        else begin
                            cnt2  <= '0;
                            bmode <= 3'd7;
                            obase <= 6'd0;
                            olim  <= 5'd4;
                        end
                    end
                    S_DB0, S_DBO: cnt2 <= cnt2 + 5'd1;
                    S_HVR: begin
                        if (wrem == 21'd0) begin
                            verdict <= !fail && !noncanon;
                            cnt2    <= '0;
                        end else begin
                            hop    <= in_data[3:0] | {4{|in_data[7:4]}};
                            ha     <= in_data[15:8];
                            hb     <= in_data[23:16];
                            hc     <= in_data[31:24];
                            dleft  <= in_data[47:32];
                            hs_k   <= in_data[63:48];
                            recidx <= recidx + 16'd1;
                            inrec  <= 1'b1;
                            gfdone <= 1'b0;
                        end
                    end
                    S_HVD: begin
                        cnt2 <= '0;
                        unique case (hop)
                            4'd1: begin
                                if (dleft == 16'd0) fail <= 1'b1;
                                else begin
                                    hs_n      <= dleft - 16'd1;
                                    hs_capsrc <= hc[3] ? 2'd2 : 2'd1;
                                    hs_capreg <= hb[2:0];
                                    hs_latch  <= hc[2:0];
                                    hs_skip   <= hc[5:4];
                                end
                            end
                            4'd2, 4'd3, 4'd4, 4'd6, 4'd7, 4'd9: ;
                            4'd5: if (dleft != 16'd4) fail <= 1'b1;
                            4'd8: if (ha[5:0] == 6'd0 || ha[5:0] > 6'd62 ||
                                      dleft != 16'd1 + {8'd0, ha[5:0], 2'd0}) fail <= 1'b1;
                            default: fail <= 1'b1;
                        endcase
                    end
                    S_HVL: begin
                        if (bindw) gfdone <= 1'b1;
                        else begin
                            if (hs_k == 16'd0 && in_ge_p) noncanon <= 1'b1;
                            gfdone <= 1'b0;
                            if (hs_k != 16'd0) hs_k <= hs_k - 16'd1;
                            cnt2 <= cnt2 + 5'd1;
                        end
                    end
                    S_HVE: if (!fe_eq) fail <= 1'b1;
                    S_HVQ: if ((res[31:0] & lowmask(hc[5:0])) != 32'd0) fail <= 1'b1;
                    S_HVM: begin
                        if (idx_armed && in_data[61:0] != lidx) fail <= 1'b1;
                        idx_armed <= 1'b0;
                        midx  <= (63'd1 << ha[5:0]) | {1'b0, in_data[61:0]};
                        mk_kb <= rb(hb[2:0]);
                        cnt   <= {10'd0, ha[5:0]};
                        cnt2  <= '0;
                    end
                    S_HVJ: begin
                        lidx      <= res[61:0] & lowmask62(hc[5:0]);
                        idx_armed <= 1'b1;
                    end
                    S_HVN: if (dleft == 16'd0) begin
                        inrec <= 1'b0;
                        hs_k  <= '0;
                        if (fail && !fset) begin
                            fset <= 1'b1;
                            fidx <= recidx;
                        end
                    end
                    S_HVF: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd3) begin
                            cnt2  <= '0;
                            bmode <= 3'd3;
                            rok   <= verdict;
                            rlen  <= 24'd72;
                        end
                    end
                    S_HVS: begin
                        cnt2  <= '0;
                        obase <= 6'd0;
                        olim  <= 5'd4;
                    end
                    S_HVC: begin
                        cnt2  <= '0;
                        obase <= 6'd32;
                        olim  <= 5'd4;
                    end
                    default: ;
                endcase
            end
        end
    end
    /* verilator lint_off UNUSEDSIGNAL */
    wire unused = &{1'b0, mul_busy, gf_busy, vat_att_ok, vat_spend_used[31:16],
                    ha[7:6], hb[7:3], hc[7:6], res[63:62], port_sh[63:16]};
    /* verilator lint_on UNUSEDSIGNAL */
endmodule
`default_nettype wire

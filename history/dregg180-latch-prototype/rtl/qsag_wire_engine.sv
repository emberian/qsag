// Dregg-180 (QSAG-NI-180) Core Packet Engine, Verifier VM (Ext4 + Fp5), CapTP Vat & Enclave.
//
// Architectural & Security Synthesis (Tapeout Signoff Edition):
//   * Punctured `[12,7,4]` HD=4 Control FSM (`ids 1..125`, `S_IDLE` code `0xc6f`, rejecting both
//     `12'h000` crowbar-zero and `12'hFFF` laser-saturation states with distance >= 4; flatten-safe
//     `qsag_hd4_checker` with `(* keep *)` parity nets so `Odb.SetPowerConnections` wires all VDD/VSS
//     pins for 0-error Netgen LVS!).
//   * Hardwired secret non-exfiltration gate (`rd_is_secret`: `e_rd >= 44` forces `out_data = 0`).
//   * Verifier VM (`0x30 OP_FOLD`, `0x31 OP_HEM`) supports BOTH 4-limb `GoldilocksExt4` AND 5-limb
//     `zk-Hem v2` Quintic `Fp5 = F_p[X]/(X^5 - 3)` + `sponge12_rate6` (`flags[4]=1`), requires at
//     least one executed assertion (`has_assert_q`), forbids `H_LOAD R_CH` in Vat-pinning mode
//     (`flags[3]=1`), hashes program+immediates under irreducible `H_ZK_PIN`, and binds `zk_pin[0..3]`
//     + `OP_VAT_ZK` grants to `(prog_digest, stmt_root)`.
//   * Full authentication across ALL secret-key opcodes:
//       - `OP_CTH` (`0x41`): requires `SpongeMacaroon` when `vat_ready=1`, requires valid `K_MAC`
//         tag (`GHASH ^ TurboSHAKE256`) on ALL coprocessor calls (including `PUBGEN`), and restricts
//         `PUBGEN` to `is_fors || sw == 4` (never leaking WOTS chain interiors via `sw=1`).
//       - `OP_PRFMSG` (`0x42`): requires `SpongeMacaroon` when `vat_ready=1`, and requires trailing
//         2-word `K_MAC` tag when `vat_ready=0` before releasing a single byte of output.
//       - `OP_PUF` (`0x50`): wipes sponge on entry, rejects re-run when `key_valid || vat_ready`,
//         derives identical `(K_vat, SK.seed, SK.prf, K_MAC)` across Enroll & Reconstruct, and
//         cryptographically binds persistent `mint_lock` (`arg[15]`) into `H_pub`.
//       - `NFC` (`G_NFC`): verifies 96-bit `TurboSHAKE256("DREGGNFC" || K_vat || seq || bind)` MAC
//         and strictly monotonic 32-bit `nfc_seq > nfc_last_seq_q` (rejecting CRC16-only & replays).
`default_nettype none

module qsag_hd4_checker (
    input  wire [11:0] c,
    output wire        ok
);
    localparam logic [6:0] MAX_ID = 7'd125;
    (* keep *) wire [3:0] p = ({4{c[5]}} & 4'd3)  ^ ({4{c[6]}} & 4'd5)
                            ^ ({4{c[7]}} & 4'd6)  ^ ({4{c[8]}} & 4'd7)
                            ^ ({4{c[9]}} & 4'd9)  ^ ({4{c[10]}} & 4'd10)
                            ^ ({4{c[11]}} & 4'd11);
    assign ok = (c != 12'h000) && (c != 12'hFFF) &&
                (p == c[4:1]) && !(^c) &&
                (c[11:5] >= 7'd1) && (c[11:5] <= MAX_ID);
endmodule

module qsag_wire_engine #(
    parameter int GF_D = 1
) (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         srst_n,
    input  wire         zeroize,
    // ingress / egress streams
    input  wire         in_valid,
    input  wire [63:0]  in_data,
    output wire         in_pop,
    input  wire         out_ready,
    output wire [63:0]  out_data,
    output wire         out_push,
    // FRAM anchor
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
    output wire  [2:0]  puf_noise_flips,
    output logic        puf_vmask_ld,
    output logic        puf_syn_ld,
    output wire  [63:0] puf_wdata,
    input  wire         puf_done,
    input  wire         puf_blk_err,
    input  wire  [63:0] puf_vmask_out,
    input  wire  [26:0] puf_syn_out,
    input  wire  [63:0] puf_word_out,
    input  wire  [3:0]  puf_corrected,
    // NFC + NCO organ interface
    input  wire         nfc_frame_rdy,
    input  wire  [31:0] nfc_seq,
    input  wire  [95:0] nfc_mac,
    input  wire  [15:0] nfc_quorum_flags,
    input  wire  [15:0] nfc_rx_frames,
    output wire         nfc_token_consume,
    output logic        nco_en,
    output logic [1:0]  nco_mode,
    output logic [3:0]  nco_sym_shift,
    output wire         nco_cfg_we,
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
    input  wire         db_cal_valid,
    input  wire         db_dist_timeout,
    input  wire  [31:0] db_dist_cycles,
    // telemetry / configuration
    input  wire  [63:0] tel0,
    input  wire  [31:0] tel1,
    output wire  [63:0] csr,
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
    localparam logic [63:0] C_NFC           = 64'h4346_4E47_4745_5244;  // "DREGGNFC"
    localparam logic [63:0] NODE_HI         = 64'h5032_4E44_0000_0000;
    localparam logic [63:0] FS_INIT         = 64'h5032_4653_494E_4954;
    localparam logic [63:0] P2_IV           = 64'h504F_5332_5F47_4C31;
    localparam logic [63:0] PAD_END         = 64'h8000_0000_0000_0000;
    localparam logic [63:0] BIST_GOLDEN_KAT = 64'h4ae2_1323_a298_0887;
    localparam logic [127:0] H_BIST         = 128'hA5A5_5A5A_DEAD_BEEF_3831_494E_4741_5351;
    localparam logic [127:0] H_ZK_PIN       = 128'h9E37_79B9_7F4A_7C15_504F_5332_5F47_4C31;

    localparam logic [3:0] F_PERM = 4'd1, F_ABSW = 4'd2, F_SETW = 4'd3, F_MOV = 4'd4, F_EMUL = 4'd5,
                           F_EADD = 4'd6, F_ESUB = 4'd7, F_EEQ = 4'd8, F_FFWD = 4'd9, F_LDRES = 4'd10,
                           F_FP5_MUL = 4'd11, F_FP5_ADD = 4'd12, F_FP5_SUB = 4'd13, F_FP5_EQ = 4'd14;

    // ------------------------------------------------------------------ 125 punctured [12,7,4] HD=4 states
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
        S_BSW = 12'hc8e,    S_BS0 = 12'hca9,    S_BS1 = 12'hcc5,    S_BS2 = 12'hce2,    S_BSO = 12'hd0d,
        S_KSB = 12'hd2a,
        S_CY0 = 12'hd46,    S_CY1 = 12'hd61,    S_CZ0 = 12'hd80,    S_CZ1 = 12'hda7,    S_CZ2 = 12'hdcb,
        S_PF0 = 12'hdec,    S_PF1 = 12'he10,    S_PF2 = 12'he37,    S_PF3 = 12'he5b,    S_PF4 = 12'he7c,
        S_PF5 = 12'he9d,
        S_VLD = 12'heba,    S_VTG = 12'hed6,    S_VAT = 12'hef1,    S_VOT = 12'hf1e,    S_VZK = 12'hf39,
        S_DB0 = 12'hf55,    S_DBO = 12'hf72,
        S_PFT = 12'hf93,    S_NFC = 12'hfb4;

    localparam logic [2:0] K_NONE = 3'd0, K_FE = 3'd1, K_KC = 3'd2, K_GF = 3'd3;

    (* fsm_encoding = "none", keep *) logic [11:0] st, ret, ret2, ret3;
    (* keep *) wire ok_st, ok_r1, ok_r2, ok_r3;
    qsag_hd4_checker u_chk_st (.c(st),   .ok(ok_st));
    qsag_hd4_checker u_chk_r1 (.c(ret),  .ok(ok_r1));
    qsag_hd4_checker u_chk_r2 (.c(ret2), .ok(ok_r2));
    qsag_hd4_checker u_chk_r3 (.c(ret3), .ok(ok_r3));

    // Direct dense 7-bit `sid = st[11:5]` (`1..125`) decode without front-end parity XOR cones;
    // `u_chk_st` still checks all 12 bits of `st` every clock via `control_bad -> !permit_control`!
    wire [6:0] sid = st[11:5];
    function automatic logic [11:0] hd4_enc(input logic [6:0] id);
        logic [3:0] pr;
        begin
            pr = ({4{id[0]}} & 4'd3)  ^ ({4{id[1]}} & 4'd5)
               ^ ({4{id[2]}} & 4'd6)  ^ ({4{id[3]}} & 4'd7)
               ^ ({4{id[4]}} & 4'd9)  ^ ({4{id[5]}} & 4'd10)
               ^ ({4{id[6]}} & 4'd11);
            hd4_enc = {id, pr, ^{id, pr}};
        end
    endfunction

    logic [15:0] steps, steps_inv_q;
    wire         steps_bad   = ((steps ^ steps_inv_q) != 16'hFFFF);
    wire         control_bad = !ok_st || !ok_r1 || !ok_r2 || !ok_r3 || steps_bad;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n)           fault_control <= 1'b0;
        else if (control_bad) fault_control <= 1'b1;

    // Pure FF-registered `secret_rst_n` (`RN` of all secret cells: zero combinational glitches!)
    wire secret_rst_n_raw = srst_n & ~fault_control & ~fault_laser_dfa;
    wire secret_rst_n;
    qsag_clkbuf u_sec_rst (.a(secret_rst_n_raw), .y(secret_rst_n));
    wire permit_control   = !control_bad && !fault_control && !fault_laser_dfa;

    localparam logic [63:0] CSR_RST = 64'h0000_0000_0268_C01F;
    wire  [63:0] csr_xor_q;
    wire  [63:0] csr_q = csr_xor_q ^ CSR_RST;
    logic        key_valid, vat_mint_locked;
    // Lock debug fault-injection hooks (CSR[53:52]) once `vat_mint_locked` is set!
    assign csr = vat_mint_locked ? {csr_q[63:54], 2'b00, csr_q[51:0]} : csr_q;

    logic        w;
    wire  [7:0]  op, flags;
    wire  [15:0] arg;
    logic [20:0] wrem;
    wire  [2:0]  lenb;
    logic [23:0] rlen;
    logic [15:0] rcode;
    logic        rerr, rok;
    logic [15:0] cnt;
    logic [4:0]  cnt2;
    logic [4:0]  wi;
    logic [5:0]  obase;
    logic [4:0]  olim;
    logic        partial;
    // Poseidon2 sponge (rate-8 domain-tagged + rate-6 `sponge12_rate6`)
    logic [15:0] hs_n, hs_k;
    logic [3:0]  hs_idx;
    logic        hs_first, hs_ph, hs_rate6, hs_pad_done, gfdone;
    logic [1:0]  hs_capsrc;
    logic [2:0]  hs_capreg, hs_latch;
    logic [1:0]  hs_skip;
    logic        idx_armed;
    // 32-bit Canopy Merkle (depth 1..32, matching canonical 32-bit P2ND node tag)
    logic [32:0] midx;
    logic [31:0] lidx;
    logic [5:0]  mk_kb;
    // Verifier VM (Ext4 + Fp5)
    logic [3:0]  hop;
    logic [5:0]  ha;
    logic [2:0]  hb;
    logic [6:0]  hc;
    logic [15:0] dleft, recidx, fidx;
    logic        inrec, fail, fset, noncanon, verdict, has_assert_q;
    // Enclave, FRAM, Cut-the-Hash & NFC state
    wire  [31:0] cur, hwm, ctmp;
    logic        hwm_valid, v0, anyv, older, aslot, rcmp, hi0, macdiff, is_fors, isprf;
    logic [3:0]  bmode; // 0 SLH, 1 FRAM, 2 MASK, 3 RECEIPT, 4 VAT_SEAL, 5 PUF_ABS, 6 PUF_CHK, 7 ZK_GRANT, 8 NFC_MAC
    wire  [7:0]  ci           = dleft[7:0];
    logic [1:0]  widx;
    logic [6:0]  sh;
    wire  [15:0] sym          = hs_n;
    wire  [15:0] hj           = cnt;
    wire  [63:0] y_hold0;
    logic [1:0]  dfa_ok_q; // Complementary 2-bit canary (`2'b01` armed -> `2'b10` word0 ok -> checked in CZ1/CZ2)
    logic        chk_cont;
    logic [2:0]  puf_blk;
    logic [2:0]  puf_flips_q;
    logic        puf_any_err;
    wire  [7:0]  puf_corr_tot = dleft[7:0];
    wire  [31:0] nfc_last_seq_q;
    logic        nfc_auth_ok, nfc_drop_pulse;

    wire vat_ready;
    assign busy            = (st != S_IDLE);
    assign key_valid_o     = key_valid;
    assign vat_ready_o     = vat_ready;
    assign puf_blk_sel     = puf_blk;
    assign puf_wdata       = in_data;
    assign puf_noise_flips = (key_valid || vat_ready || vat_mint_locked) ? 3'd0 : puf_flips_q;

    // ------------------------------------------------------------------ CapTP Vat Membrane
    logic        kvat_commit, zk_latch_set, zk_latch_clr;
    logic        vat_pchk_clr, vat_pwe, vat_cchk_clr, vat_cwe, vat_pk_clr, vat_pk_we;
    wire         vat_commit_inv, vat_nfc_consume;
    wire         zk_root_valid, vat_att_ok, vat_att_step_ok, vat_inv_ok, vat_need_fram, vat_need_nfc;
    wire  [31:0] vat_spend_used;

    wire [15:0] vat_req_right = (op == OP_CTH)    ? 16'h0001 :
                                (op == OP_PRFMSG) ? 16'h0002 : 16'h0004;
    wire [31:0] vat_req_epoch = (op == OP_CTH)    ? port[31:0] : {16'd0, arg};
    wire [31:0] vat_req_spend = (op == OP_CTH)    ? {24'd0, arg[7:0]} : 32'd1;
    assign nfc_token_consume  = vat_nfc_consume | nfc_drop_pulse;

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
    wire [127:0] gf_acc, kmac_q;

    logic        fe_start, kc_start, kc_turbo, gf_start, gf_clr, sp_wipe;
    logic [3:0]  fe_op;
    logic [5:0]  fe_d, fe_s1, fe_s2;
    logic [2:0]  fe_n;
    logic        fe_dir;
    logic [63:0] xw;
    logic [5:0]  e_rd, e_wa;
    logic        e_we;
    logic [63:0] e_wd;

    logic zeroize_q;
    /* verilator lint_off SYNCASYNCNET */
    wire  sub_rst_n = rst_n & ~zeroize_q & ~fault_control & ~fault_laser_dfa;
    /* verilator lint_on SYNCASYNCNET */
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) zeroize_q <= 1'b0;
        else        zeroize_q <= zeroize;

    wire prf_legacy_tag = (op == OP_PRFMSG) && !flags[2];
    wire [20:0] ksa_stop_rem = prf_legacy_tag ? 21'd2 : 21'd0;

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
        .fault_inj(csr[53] && (sid == S_BKC[11:5]) && (bmode == 4'd0) && !chk_cont),
        .busy(kc_busy), .done(kc_done), .rd_addr(kc_rd), .port(port),
        .wr_en(kc_we), .wr_addr(kc_wa), .wr_data(kc_wd)
    );

    // Aux write port into `qsag_sponge`:
    //   0..7   sh[0..7] (background Keccak absorb)
    //   8..9   sh[8..9] (CapTP parent PK.seed[0..1] in S_VLD cnt2=4..5)
    //   10..13 zk_pin[0..3] (verified `(prog_digest, stmt_root)` in S_HVF)
    //   14..19 key[0..5]
    //   20..23 kvat[0..3]
    logic [3:0]  zkpin_we;
    logic [5:0]  key_we;
    logic [3:0]  kvat_we;
    logic [63:0] zkpin_wdata;
    wire         vld_pk_wr = fire && (sid == S_VLD[11:5]) && vat_pwe && (cnt2 == 5'd4 || cnt2 == 5'd5);
    wire         zkpin_wr  = (|zkpin_we) && permit_control;
    wire         key_wr    = (|key_we)   && permit_control;
    wire         kvat_wr   = (|kvat_we)  && permit_control;
    wire         vld_pmeta = fire && vat_pwe && permit_control && (cnt2 >= 5'd1) && (cnt2 <= 5'd3);
    wire         aux_we    = vld_pk_wr | zkpin_wr | key_wr | kvat_wr;
    wire  [63:0] aux_wdata = zkpin_wr ? zkpin_wdata
                           : (sid == S_KLK[11:5] || sid == S_PF4[11:5] || sid == S_PF5[11:5]) ? port
                           : in_data;
    wire  [63:0] sp_hold_q;
    logic [4:0]  aux_addr;
    always_comb begin
        aux_addr = 5'd8 + {4'd0, cnt2[0]};
        if (zkpin_wr)
            for (int k = 0; k < 4; k++) if (zkpin_we[k]) aux_addr = 5'd10 + 5'(k);
        if (key_wr)
            for (int k = 0; k < 6; k++) if (key_we[k])   aux_addr = 5'd14 + 5'(k);
        if (kvat_wr)
            for (int k = 0; k < 4; k++) if (kvat_we[k])  aux_addr = 5'd20 + 5'(k);
    end

    qsag_sponge u_sp (
        .clk(clk), .srst_n(secret_rst_n),
        .wipe(!rst_n | sp_wipe | zeroize_q | fault_control | fault_laser_dfa),
        .wr_en(fe_busy ? fe_we : kc_busy ? kc_we : e_we),
        .wr_addr(fe_busy ? fe_wa : kc_busy ? kc_wa : e_wa),
        .wr_data(fe_busy ? cv : kc_busy ? kc_wd : e_wd),
        .rd_addr(fe_busy ? fe_rd : kc_busy ? kc_rd : e_rd),
        .rd_data(port),
        .aux_we(aux_we), .aux_addr(aux_addr), .aux_wdata(aux_wdata),
        .ext_hold_en(vld_pmeta), .hold_q(sp_hold_q),
        .kmac_q(kmac_q)
    );

    wire vm_pin_mode = (op == OP_FOLD || op == OP_HEM) && flags[3];
    wire gf_use_bist = (op == OP_BIST);
    wire gf_use_zpin = !gf_use_bist && vm_pin_mode;
    wire gf_use_kmac = !gf_use_bist && !vm_pin_mode && key_valid;
    wire [127:0] gf_h_eff = ({128{gf_use_bist}} & H_BIST) |
                            ({128{gf_use_zpin}} & H_ZK_PIN) |
                            ({128{gf_use_kmac}} & kmac_q);
    qsag_gf128_clmul #(.D(GF_D)) u_gf (
        .clk(clk), .rst_n(sub_rst_n), .srst_n(secret_rst_n), .clr(gf_clr), .start(gf_start),
        .in({64'd0, xw}), .h(gf_h_eff), .busy(gf_busy), .done(gf_done), .acc(gf_acc)
    );

    dregg_captp_vat u_vat (
        .clk(clk), .rst_n(sub_rst_n), .srst_n(secret_rst_n), .permit_control(permit_control),
        .kvat_commit(kvat_commit), .vat_ready(vat_ready),
        .zk_latch_valid_set(zk_latch_set), .zk_latch_clear(zk_latch_clr), .zk_root_valid(zk_root_valid),
        .parent_chk_clr(fire && vat_pchk_clr), .parent_we(fire && vat_pwe), .parent_idx(cnt2[2:0]),
        .desc_wdata(in_data), .sp_hold_q(sp_hold_q), .desc_eq_sp(cmp_eq),
        .child_chk_clr(fire && vat_cchk_clr), .child_we(fire && vat_cwe), .child_idx(cnt2[2:0]),
        .pk_chk_clr(fire && vat_pk_clr), .pk_chk_we(fire && vat_pk_we),
        .nfc_auth_ok(nfc_auth_ok), .need_nfc_guard(vat_need_nfc),
        .nfc_consume_pulse(vat_nfc_consume),
        .dist_valid(db_dist_valid), .dist_timeout(db_dist_timeout), .dist_cycles(db_dist_cycles),
        .dist_consume_pulse(db_dist_consume),
        .req_right_bit(vat_req_right), .req_epoch(vat_req_epoch), .req_spend(vat_req_spend),
        .check_is_zk(op == OP_VAT_ZK), .commit_invocation(vat_commit_inv),
        .attenuate_legal(vat_att_ok), .attenuate_step_ok(vat_att_step_ok), .invoke_legal(vat_inv_ok),
        .need_stateful_fram(vat_need_fram), .vat_spend_used(vat_spend_used)
    );

    // ------------------------------------------------------------------ helpers & shared S_IDLE decode
    wire fp5_vm = (op == OP_HEM) && flags[4];
    wire [2:0] vm_limbs = fp5_vm ? 3'd5 : 3'd4;
    function automatic logic [5:0] rb_vm(input logic is5, input logic [2:0] id);
        if (is5) begin
            case (id)
                3'd1:    rb_vm = 6'd12;
                3'd2:    rb_vm = 6'd17;
                3'd3:    rb_vm = 6'd22;
                3'd4:    rb_vm = 6'd32;
                3'd5:    rb_vm = 6'd37;
                default: rb_vm = 6'd0;
            endcase
        end else begin
            case (id)
                3'd1:    rb_vm = 6'd12;
                3'd2:    rb_vm = 6'd16;
                3'd3:    rb_vm = 6'd20;
                3'd4:    rb_vm = 6'd32;
                3'd5:    rb_vm = 6'd36;
                default: rb_vm = 6'd0;
            endcase
        end
    endfunction
    // Shared 32-bit Canopy decoders & pruned 16-bit right-shifter
    wire [5:0]  mk_sh = (sid == S_MOI[11:5]) ? arg[5:0] : ha[5:0];
    wire [32:0] mk_top_bit;
    wire [31:0] res_masked;
    genvar gb;
    generate
        for (gb = 0; gb < 33; gb++) begin : g_mkb
            assign mk_top_bit[gb] = (mk_sh == 6'(gb));
        end
        for (gb = 0; gb < 32; gb++) begin : g_rmk
            assign res_masked[gb] = res[gb] & (6'(gb) < hc[5:0]);
        end
    endgenerate

    wire        in_ge_p   = (&in_data[63:32]) && (|in_data[31:0]);
    wire [20:0] hdr_wlen  = wrem - {20'd0, |lenb};
    wire [63:0] hdr_word  = {arg, hdr_wlen, lenb, flags, op, 8'h51};
    wire [63:0] t0_word   = {NODE_HI[63:32], midx[32:1]};
    wire        pubgen    = flags[0];
    wire        cap_mode  = flags[2];
    wire        self_chk  = flags[3] && !pubgen && !is_fors;
    wire        stateful  = flags[1] || (cap_mode && vat_need_fram);
    wire [7:0]  nch       = arg[7:0];
    wire [4:0]  sw        = arg[12:8];
    wire [15:0] symmask;
    generate
        for (gb = 0; gb < 16; gb++) begin : g_smk
            assign symmask[gb] = (5'(gb) < sw);
        end
    endgenerate
    wire [47:0] psh5      = sh[5] ? {16'd0, port[63:32]} : port[47:0];
    wire [31:0] psh4      = sh[4] ? psh5[47:16]          : psh5[31:0];
    wire [23:0] psh3      = sh[3] ? psh4[31:8]           : psh4[23:0];
    wire [19:0] psh2      = sh[2] ? psh3[23:4]           : psh3[19:0];
    wire [16:0] psh1      = sh[1] ? psh2[18:2]           : psh2[16:0];
    wire [15:0] port_sh16 = sh[0] ? psh1[16:1]           : psh1[15:0];
    wire [23:0] fors_idx  = (24'(ci) << sw) | 24'(sym);
    wire [23:0] hfield    = is_fors ? fors_idx : (isprf ? 24'd0 : 24'(hj));
    wire [7:0]  cfield    = is_fors ? 8'd0 : ci;
    wire [63:0] a3_word   = {hfield[7:0], hfield[15:8], hfield[23:16], 8'd0, cfield, 24'd0};
    wire [7:0]  type_ov   = is_fors ? (isprf ? 8'd6 : 8'd3) : (isprf ? 8'd5 : 8'd0);
    wire [63:0] stat_word = {8'd0, op, recidx, fidx, 13'd0, key_valid, noncanon, verdict};

    assign nco_pkt_data  = in_data;
    assign db_load_wdata = in_data;

    // Deduplicated single-source S_IDLE packet validation & dispatch
    wire  [23:0] idle_cth_len = (in_data[18] ? 24'd160 : 24'd80) +
                                ((in_data[19] && !in_data[16]) ? {12'd0, in_data[55:48], 4'd0} : 24'd0);
    logic [15:0] idle_err;
    logic [23:0] idle_rlen;
    logic [6:0]  idle_st_id, idle_ret_id, idle_ret2_id;
    always_comb begin
        idle_err  = 16'd0;
        idle_rlen = 24'd0;
        idle_st_id   = S_DRAIN[11:5];
        idle_ret_id  = S_IDLE[11:5];
        idle_ret2_id = S_IDLE[11:5];
        if (in_data[7:0] != 8'h51) begin
            idle_err = E_MAGIC;
        end else begin
            unique case (in_data[15:8])
                OP_PING: begin
                    idle_rlen = 24'd32;
                    if (in_data[47:24] != 24'd0) idle_err = E_LEN;
                    else begin idle_ret_id = S_PING[11:5]; idle_st_id = S_HDR[11:5]; end
                end
                OP_CSR: begin
                    if (in_data[47:24] != 24'd8) idle_err = E_LEN;
                    else idle_st_id = S_CSR[11:5];
                end
                OP_BIST: begin
                    if (in_data[47:24] != 24'd0) idle_err = E_LEN;
                    else idle_st_id = S_BSW[11:5];
                end
                OP_P2: begin
                    if (in_data[16]) begin
                        if (in_data[47:24] != 24'd96) idle_err = E_LEN;
                        else idle_st_id = S_P2R[11:5];
                    end else if (in_data[17]) begin // flags[1]=1: canonical sponge12_rate6
                        if (in_data[26:24] != 3'd0) idle_err = E_LEN;
                        else begin idle_ret_id = S_HDR[11:5]; idle_st_id = S_HSZ[11:5]; end
                    end else if (in_data[47:24] < 24'd40 || in_data[26:24] != 3'd0) begin
                        idle_err = E_LEN;
                    end else begin
                        idle_ret_id = S_HDR[11:5];
                        idle_st_id  = S_HSZ[11:5];
                    end
                end
                OP_MERKLE: begin
                    if (in_data[53:48] == 6'd0 || in_data[53:48] > 6'd32 ||
                        in_data[47:24] != 24'd96 + {13'd0, in_data[53:48], 5'd0})
                        idle_err = E_LEN;
                    else idle_st_id = S_MOK[11:5];
                end
                OP_KECCAK: idle_st_id = S_KSW[11:5];
                OP_PRFMSG: begin
                    if (in_data[18]) begin // cap_mode: 96-byte SpongeMacaroon + payload
                        if (!vat_ready || !key_valid) idle_err = E_NOKEY;
                        else if (in_data[47:24] < 24'd96) idle_err = E_LEN;
                        else begin idle_ret2_id = S_KSW[11:5]; idle_st_id = S_VLD[11:5]; end
                    end else if (!key_valid) begin
                        idle_err = E_NOKEY;
                    end else if (vat_ready) begin
                        idle_err = E_CAP;
                    end else if (in_data[47:24] < 24'd16) begin // requires 16-byte K_MAC tag!
                        idle_err = E_LEN;
                    end else begin
                        idle_st_id = S_CTG[11:5]; // hashes hdr_word into u_gf before S_KSW[11:5]!
                    end
                end
                OP_FOLD, OP_HEM: begin
                    if (in_data[26:24] != 3'd0) idle_err = E_LEN;
                    else idle_st_id = S_HVG[11:5];
                end
                OP_KEYLOAD: begin
                    if (key_valid) idle_err = E_KEYSET;
                    else if (in_data[16] ? (in_data[47:24] != (in_data[18] ? 24'd80 : 24'd48))
                                         : (in_data[47:24] < 24'd16 || in_data[47:24] > 24'd96 ||
                                            in_data[26:24] != 3'd0))
                        idle_err = E_LEN;
                    else idle_st_id = S_KLM[11:5];
                end
                OP_CTH: begin
                    if (in_data[47:24] != idle_cth_len || in_data[60:56] == 5'd0 ||
                        in_data[60:56] > 5'd16 || in_data[55:48] == 8'd0)
                        idle_err = E_LEN;
                    else if (in_data[18]) begin
                        if (!vat_ready || !key_valid) idle_err = E_NOKEY;
                        else begin idle_ret2_id = S_CTG[11:5]; idle_st_id = S_VLD[11:5]; end
                    end else if (vat_ready) begin // R1 A5.2 / D6 #3: legacy CTH blocked once vat_ready!
                        idle_err = E_CAP;
                    end else if (!key_valid) begin
                        idle_err = E_NOKEY;
                    end else begin
                        idle_st_id = S_CTG[11:5];
                    end
                end
                OP_PUF: begin
                    if (key_valid || vat_ready) idle_err = E_KEYSET;
                    else if (in_data[16] ? (in_data[47:24] != 24'd160) : (in_data[47:24] != 24'd0))
                        idle_err = E_LEN;
                    else if (!in_data[16]) begin
                        idle_rlen = 24'd160;
                        idle_ret_id  = S_PF0[11:5];
                        idle_st_id   = S_HDR[11:5];
                    end else idle_st_id = S_PF0[11:5];
                end
                OP_VAT: begin
                    if (!vat_ready) idle_err = E_NOKEY;
                    else if (!in_data[16] && vat_mint_locked) idle_err = E_LOCKED;
                    else if (in_data[47:24] != (in_data[16] ? 24'd160 : 24'd64))
                        idle_err = E_LEN;
                    else begin
                        idle_rlen = 24'd96;
                        idle_ret2_id = in_data[16] ? S_VAT[11:5] : S_HDR[11:5];
                        idle_st_id   = S_VLD[11:5];
                    end
                end
                OP_DB_NCO: begin
                    if (in_data[47:24] != 24'd24) idle_err = E_LEN;
                    else begin idle_rlen = 24'd32; idle_st_id = S_DB0[11:5]; end
                end
                OP_VAT_ZK: begin
                    if (!vat_ready) idle_err = E_NOKEY;
                    else if (in_data[47:24] != 24'd96) idle_err = E_LEN;
                    else begin
                        idle_rlen = 24'd32;
                        idle_ret2_id = S_VZK[11:5];
                        idle_st_id   = S_VLD[11:5];
                    end
                end
                default: idle_err = E_OPCODE;
            endcase
        end
    end

    // ------------------------------------------------------------------ control decode
    logic [2:0]  kind;
    logic        cond;
    logic        do_pop;
    logic [2:0]  xsel;       // 0 in, 1 imm, 3 gf, 4 anchor, 5 trng, 6 zero, 7 port
    logic [63:0] imm;
    logic [5:0]  isel;
    wire  [7:0]  ksd_byte = (op == OP_KECCAK) ? arg[7:0] : 8'h1F;
    wire  [2:0]  ksd_sh   = partial ? lenb : 3'd0;
    logic [63:0] ksd_pad;
    always_comb begin
        for (int b = 0; b < 8; b++)
            ksd_pad[8*b +: 8] = (ksd_sh == 3'(b)) ? ksd_byte : 8'd0;
    end
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
    wire [5:0] hs_lat_len = {3'd0, vm_limbs};
    wire hs_lat_now = (hs_latch != 3'd0) && !hs_ph && (hs_n > {14'd0, hs_skip}) &&
                      (hs_n <= {10'd0, hs_lat_len} + {14'd0, hs_skip});
    wire ksa_has_msg = (wrem > ksa_stop_rem + {20'd0, lenb != 3'd0});
    wire ksa_is_part = (wrem == ksa_stop_rem + 21'd1) && (lenb != 3'd0);

    always_comb begin
        unique case (xsel)
            3'd0:    xw = in_data;
            3'd1:    xw = imm;
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
        kind             = K_NONE;
        cond             = 1'b1;
        do_pop           = 1'b0;
        xsel             = 3'd6;
        isel             = 6'd0;
        gsel             = 1'b0;
        wsel             = 3'd0;
        e_wreq           = 1'b0;
        e_wlaunch        = 1'b0;
        e_rd             = 6'd0;
        e_wa             = 6'd0;
        emit             = 1'b0;
        emit_port        = 1'b0;
        fe_op            = F_PERM;
        fe_d             = 6'd0;
        fe_s1            = 6'd0;
        fe_s2            = 6'd0;
        fe_n             = 3'd0;
        fe_dir           = 1'b0;
        kc_turbo         = 1'b0;
        gf_clr           = 1'b0;
        sp_wipe          = 1'b0;
        an_start         = 1'b0;
        an_write         = 1'b0;
        an_addr          = {10'd0, aslot, 5'd0};
        an_go            = 1'b0;
        trng_take        = 1'b0;
        zkpin_we         = 4'd0;
        zkpin_wdata      = 64'd0;
        key_we           = 6'd0;
        kvat_we          = 4'd0;
        kvat_commit      = 1'b0;
        zk_latch_set     = 1'b0;
        zk_latch_clr     = 1'b0;
        vat_pchk_clr     = 1'b0;
        vat_pwe          = 1'b0;
        vat_cchk_clr     = 1'b0;
        vat_cwe          = 1'b0;
        vat_pk_clr       = 1'b0;
        vat_pk_we        = 1'b0;
        puf_start_blk    = 1'b0;
        puf_vmask_ld     = 1'b0;
        puf_syn_ld       = 1'b0;
        db_load_r0       = 1'b0;
        db_load_r1       = 1'b0;
        db_arm_responder = 1'b0;
        db_step_round    = 1'b0;
        db_launch_ping   = 1'b0;
        db_cal_ping      = 1'b0;
        nco_pkt_load     = 1'b0;

        unique case (sid)
            S_IDLE[11:5]: begin
                cond    = in_valid;
                do_pop  = 1'b1;
                gf_clr  = 1'b1;
                // Security & init fix: wipe public sponge & scratchpad cleanly on OP_PUF / legacy OP_PRFMSG entry
                sp_wipe = in_valid && (in_data[7:0] == 8'h51) &&
                          (in_data[15:8] == OP_PUF || (in_data[15:8] == OP_PRFMSG && !in_data[18]));
            end
            S_DRAIN[11:5]: begin
                cond   = (wrem == 21'd0) || in_valid;
                do_pop = (wrem != 21'd0);
            end
            S_EHDR[11:5], S_HDR[11:5]: begin
                cond = out_ready;
                emit = 1'b1;
                isel = 6'd4;
            end
            S_OUTL[11:5]: begin
                cond      = out_ready;
                emit      = 1'b1;
                emit_port = 1'b1;
                e_rd      = obase + {1'b0, cnt2};
            end
            S_WIPE[11:5], S_KSW[11:5], S_KLZ[11:5]: sp_wipe = 1'b1;
            S_KLW[11:5]: begin
                sp_wipe   = 1'b1;
                trng_take = 1'b1;
            end
            S_DEAD[11:5]: begin
                cond    = 1'b0;
                sp_wipe = 1'b1;
            end
            S_PING[11:5]: begin
                cond = out_ready;
                emit = 1'b1;
                unique case (cnt2[1:0])
                    2'd0:    isel = 6'd5;
                    2'd1:    isel = 6'd6;
                    2'd2:    isel = 6'd7;
                    default: isel = 6'd8;
                endcase
            end
            S_CSR[11:5]: begin
                cond   = in_valid;
                do_pop = 1'b1;
            end
            // ---------------------------------------------------------- OP_BIST
            S_BSW[11:5]: begin
                sp_wipe = 1'b1;
                gf_clr  = 1'b1;
            end
            S_BS0[11:5]: begin
                e_wreq = 1'b1;
                xsel   = 3'd1;
                e_wa   = (cnt2 == 5'd0) ? 6'd0 : (cnt2 == 5'd1) ? 6'd1 : 6'd16;
                isel   = (cnt2 == 5'd0) ? 6'd5 : (cnt2 == 5'd1) ? 6'd2 : 6'd3;
            end
            S_BS1[11:5]: begin
                kind  = K_FE;
                fe_op = F_EMUL;
                fe_d  = 6'd16;
                fe_s1 = 6'd0;
                fe_s2 = 6'd4;
            end
            S_BS2[11:5]: begin
                e_rd   = 6'd16;
                kind   = K_GF;
                xsel   = w ? 3'd3 : 3'd7;
                wsel   = 3'd1;
                e_wreq = 1'b1;
                e_wa   = 6'd0;
            end
            S_BSO[11:5]: begin
                cond      = out_ready;
                emit      = 1'b1;
                emit_port = 1'b1;
                e_rd      = 6'd0;
            end
            // ---------------------------------------------------------- Poseidon2 (rate-8 & rate-6)
            S_P2R[11:5]: begin
                kind   = K_FE;
                cond   = in_valid;
                fe_op  = F_SETW;
                fe_d   = {1'b0, cnt2};
                xsel   = 3'd0;
                do_pop = 1'b1;
            end
            S_P2RP[11:5], S_HSP[11:5], S_MK4[11:5]: begin
                kind  = K_FE;
                fe_op = F_PERM;
            end
            S_HSZ[11:5]: begin
                kind  = K_FE;
                fe_op = F_SETW;
                fe_d  = {1'b0, cnt2};
                xsel  = 3'd6;
            end
            S_HSD[11:5]: begin
                kind   = bindw ? K_GF : K_FE;
                cond   = in_valid;
                fe_op  = F_ABSW;
                fe_d   = 6'd0;
                xsel   = 3'd0;
                do_pop = !bindw;
            end
            S_HSC[11:5]: begin
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
                        fe_s1 = rb_vm(1'b0, hs_capreg);
                    end
                    default: begin
                        fe_op = F_SETW;
                        fe_d  = 6'd8 + {1'b0, cnt2};
                        xsel  = 3'd1;
                        isel  = (cnt2[1:0] == 2'd0) ? 6'd9 : (cnt2[1:0] == 2'd3) ? 6'd10 : 6'd0;
                    end
                endcase
            end
            S_HSN[11:5]: begin
                kind  = K_FE;
                fe_op = F_ABSW;
                fe_d  = 6'd1;
                xsel  = 3'd1;
                isel = 6'd11;
            end
            S_HSL[11:5]: begin
                if (hs_n == 16'd0) begin
                    if (hs_rate6 && !hs_pad_done) begin
                        kind  = K_FE;
                        fe_op = F_ABSW;
                        fe_d  = {2'd0, hs_idx};
                        xsel  = 3'd1;
                        isel = 6'd1;
                    end else kind = K_NONE;
                end else begin
                    kind = bindw ? K_GF : K_FE;
                    cond = in_valid;
                    xsel = 3'd0;
                    if (hs_lat_now) begin
                        fe_op = F_SETW;
                        fe_d  = rb_vm(fp5_vm, hs_latch) + hs_lat_len + {4'd0, hs_skip} - hs_n[5:0];
                    end else begin
                        fe_op  = F_ABSW;
                        fe_d   = {2'd0, hs_idx};
                        do_pop = !bindw;
                    end
                end
            end
            S_HSF[11:5]: begin
                kind  = (hs_first || hs_pad_done || hs_idx != 4'd0) ? K_FE : K_NONE;
                fe_op = F_PERM;
            end
            // ---------------------------------------------------------- Canopy (Depth 1..62)
            S_MK0[11:5]: begin
                kind  = K_FE;
                fe_op = F_MOV;
                fe_d  = 6'd0;
                fe_s1 = midx[0] ? 6'd36 : 6'd32;
            end
            S_MK1[11:5]: begin
                kind  = K_FE;
                fe_op = F_MOV;
                fe_d  = 6'd4;
                fe_s1 = midx[0] ? 6'd32 : 6'd36;
            end
            S_MK2[11:5]: begin
                kind  = K_FE;
                fe_op = F_SETW;
                fe_d  = 6'd8;
                xsel  = 3'd1;
                isel = 6'd12;
            end
            S_MK3[11:5]: begin
                kind  = K_FE;
                fe_op = F_MOV;
                fe_d  = 6'd9;
                fe_s1 = mk_kb;
                fe_n  = 3'd3;
            end
            S_MK5[11:5]: begin
                kind   = K_FE;
                fe_op  = F_FFWD;
                fe_s1  = mk_kb;
                fe_dir = midx[0];
                xsel   = 3'd1;
                isel = 6'd12;
            end
            S_MPS[11:5]: begin
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
            S_MOK[11:5], S_MOL[11:5], S_MOR[11:5], S_HVL[11:5]: begin
                kind   = (sid == S_HVL[11:5] && bindw) ? K_GF : K_FE;
                cond   = in_valid;
                fe_op  = F_SETW;
                fe_d   = ((sid == S_MOK[11:5]) ? 6'd16 : (sid == S_MOL[11:5]) ? 6'd32 : (sid == S_MOR[11:5]) ? 6'd36 : rb_vm(fp5_vm, ha[2:0]))
                         + {1'b0, cnt2};
                xsel   = 3'd0;
                do_pop = !(sid == S_HVL[11:5] && bindw);
            end
            S_MOI[11:5], S_HVM[11:5]: begin
                cond   = in_valid;
                do_pop = 1'b1;
            end
            S_MOE[11:5]: begin
                kind  = K_FE;
                fe_op = F_EEQ;
                fe_s1 = 6'd32;
                fe_s2 = 6'd36;
            end
            S_MOV[11:5]: begin
                cond = out_ready;
                emit = 1'b1;
                isel = 6'd13;
            end
            // ---------------------------------------------------------- Keccak & Authenticated PRF_msg
            S_KSK[11:5]: begin
                e_wreq = 1'b1;
                e_rd   = 6'd50 + {5'd0, cnt2[0]}; // SK.prf[0..1] in unified sponge bank!
                e_wa   = {1'b0, cnt2};
                wsel   = 3'd2;
            end
            S_KSA[11:5]: begin
                if (prf_legacy_tag && (ksa_has_msg || ksa_is_part) && !gfdone) begin
                    kind = K_GF;
                    cond = in_valid;
                    xsel = 3'd0;
                end else begin
                    cond      = !(ksa_has_msg || ksa_is_part) || in_valid;
                    do_pop    = (ksa_has_msg || ksa_is_part);
                    e_wreq    = (ksa_has_msg || ksa_is_part);
                    e_rd      = {1'b0, wi};
                    e_wa      = {1'b0, wi};
                    wsel      = 3'd1;
                    xsel      = 3'd0;
                end
            end
            S_KSP[11:5], S_KSR[11:5], S_BKC[11:5]: begin
                kind     = K_KC;
                kc_turbo = (sid == S_BKC[11:5]) ? (bmode != 4'd0) : (op == OP_KECCAK && flags[0]);
            end
            S_KSD[11:5]: begin
                e_wreq = 1'b1;
                e_rd   = {1'b0, wi};
                e_wa   = {1'b0, wi};
                wsel   = 3'd1;
                xsel   = 3'd1;
                isel   = 6'd14;
            end
            S_KSE[11:5]: begin
                e_wreq = 1'b1;
                e_rd   = 6'd16;
                e_wa   = 6'd16;
                wsel   = 3'd1;
                xsel   = 3'd1;
                isel = 6'd3;
            end
            S_KSQ[11:5]: begin
                kind     = K_KC;
                kc_turbo = (op == OP_KECCAK && flags[0]);
            end
            S_PFT[11:5]: begin
                // Save squeezed PRF_msg st[0..1] -> sh[6..7], copy saved hdr_word sh[9] -> sh[0]
                e_wreq = 1'b1;
                wsel   = 3'd2;
                if (cnt2 <= 5'd1) begin
                    e_rd = {5'd0, cnt2[0]};
                    e_wa = 6'd38 + {5'd0, cnt2[0]};
                end else begin
                    e_rd = 6'd41;
                    e_wa = 6'd32;
                end
            end
            S_KSO[11:5]: begin
                cond      = (cnt == 16'd0) || out_ready;
                emit      = (cnt != 16'd0);
                emit_port = 1'b1;
                e_rd      = {1'b0, wi};
            end
            // ---------------------------------------------------------- Key load
            S_KLM[11:5]: begin
                cond   = in_valid;
                do_pop = 1'b1;
                key_we = 6'b010000 << cnt2[0];
            end
            S_KLH[11:5]: begin
                cond        = in_valid;
                do_pop      = 1'b1;
                key_we      = (cnt2 <= 5'd3) ? (6'b000001 << cnt2[1:0]) : 6'd0;
                kvat_we     = (flags[2] && cnt2 >= 5'd4 && cnt2 <= 5'd7) ? (4'b0001 << cnt2[1:0]) : 4'd0;
                kvat_commit = flags[2] && (cnt2 == 5'd7);
            end
            S_KLT[11:5]: begin
                cond      = trng_valid;
                trng_take = trng_valid;
                e_wreq    = 1'b1;
                e_wa      = {1'b0, wi};
                xsel      = 3'd5;
            end
            S_KLA[11:5]: begin
                cond   = (wrem == 21'd0) || in_valid;
                do_pop = (wrem != 21'd0);
                e_wreq = (wrem != 21'd0);
                e_rd   = {1'b0, wi};
                e_wa   = {1'b0, wi};
                wsel   = 3'd1;
                xsel   = 3'd0;
            end
            S_KLD[11:5]: begin
                e_wreq = 1'b1;
                e_rd   = {1'b0, wi};
                e_wa   = {1'b0, wi};
                wsel   = 3'd1;
                xsel   = 3'd1;
                isel = 6'd2;
            end
            S_KLE[11:5]: begin
                e_wreq = 1'b1;
                e_rd   = 6'd16;
                e_wa   = 6'd16;
                wsel   = 3'd1;
                xsel   = 3'd1;
                isel = 6'd3;
            end
            S_KLP[11:5]: begin
                kind     = K_KC;
                kc_turbo = 1'b1;
            end
            S_KLK[11:5]: begin
                e_rd        = {1'b0, cnt2};
                key_we      = (cnt2 <= 5'd3) ? (6'b000001 << cnt2[1:0]) : 6'd0;
                kvat_we     = (flags[2] && cnt2 >= 5'd4 && cnt2 <= 5'd7) ? (4'b0001 << cnt2[1:0]) : 4'd0;
                kvat_commit = flags[2] && (cnt2 == 5'd7);
            end
            // ---------------------------------------------------------- Keyed block build (bmode 0..8)
            S_BLD[11:5]: begin
                e_wreq = !(bmode == 4'd0 && !isprf && (cnt2 == 5'd6 || cnt2 == 5'd7)) &&
                         !(bmode == 4'd5);
                e_wa   = {1'b0, cnt2};
                xsel   = 3'd6;
                unique case (bmode)
                    4'd0: begin // SLH-DSA PRF / F
                        unique case (cnt2)
                            5'd0, 5'd1: begin wsel = 3'd2; e_rd = 6'd33 + {5'd0, cnt2[0]}; end
                            5'd2:       begin wsel = 3'd3; e_rd = 6'd32; end
                            5'd3:       begin wsel = 3'd2; e_rd = 6'd35; end
                            5'd4:       begin wsel = 3'd4; e_rd = 6'd36; end
                            5'd5:       begin xsel = 3'd1; isel = 6'd15; end
                            5'd6, 5'd7: begin wsel = 3'd2; e_rd = 6'd48 + {5'd0, cnt2[0]}; end
                            5'd8:       begin xsel = 3'd1; isel = 6'd2; end
                            5'd16:      begin xsel = 3'd1; isel = 6'd3; end
                            default: ;
                        endcase
                    end
                    4'd1: begin // FRAM slot tag
                        unique case (cnt2)
                            5'd0, 5'd1: begin wsel = 3'd2; e_rd = 6'd52 + {5'd0, cnt2[0]}; end
                            5'd2:       begin xsel = 3'd1; isel = 6'd16; end
                            5'd3:       begin xsel = 3'd1; isel = 6'd17; end
                            5'd4:       begin xsel = 3'd1; isel = 6'd2; end
                            5'd16:      begin xsel = 3'd1; isel = 6'd3; end
                            default: ;
                        endcase
                    end
                    4'd2: begin // K_MAC mask (OP_CTH & OP_PRFMSG)
                        unique case (cnt2)
                            5'd0, 5'd1: begin wsel = 3'd2; e_rd = 6'd52 + {5'd0, cnt2[0]}; end
                            5'd2:       begin wsel = 3'd2; e_rd = 6'd32; end
                            5'd3:       begin xsel = 3'd1; isel = 6'd18; end
                            5'd4:       begin xsel = 3'd1; isel = 6'd2; end
                            5'd16:      begin xsel = 3'd1; isel = 6'd3; end
                            default: ;
                        endcase
                    end
                    4'd3: begin // Verifier receipt (4-limb Ext4 or 5-limb Fp5)
                        if ((cnt2 == 5'd0 || cnt2 == 5'd1) && key_valid) begin
                            wsel = 3'd2; e_rd = 6'd52 + {5'd0, cnt2[0]};
                        end else if (cnt2 == 5'd2) begin
                            xsel = 3'd1; isel = 6'd19;
                        end else if (cnt2 == 5'd3 || cnt2 == 5'd4) begin
                            xsel = 3'd3; gsel = !cnt2[0];
                        end else if (cnt2 >= 5'd5 && cnt2 <= (fp5_vm ? 5'd9 : 5'd8)) begin
                            wsel = 3'd2; e_rd = 6'd32 + (cnt2 - 5'd5);
                        end else if (cnt2 == (fp5_vm ? 5'd10 : 5'd9)) begin
                            xsel = 3'd1; isel = 6'd2;
                        end else if (cnt2 == 5'd16) begin
                            xsel = 3'd1; isel = 6'd3;
                        end
                    end
                    4'd4: begin // SpongeMacaroon seal: "DREGGVAT" || K_vat[0..3] || sh[0..7]
                        if (cnt2 == 5'd0)                       begin xsel = 3'd1; isel = 6'd20; end
                        else if (cnt2 >= 5'd1 && cnt2 <= 5'd4)  begin wsel = 3'd2; e_rd = 6'd54 + (cnt2 - 5'd1); end
                        else if (cnt2 >= 5'd5 && cnt2 <= 5'd12) begin wsel = 3'd2; e_rd = 6'd32 + (cnt2 - 5'd5); end
                        else if (cnt2 == 5'd13)                 begin xsel = 3'd1; isel = 6'd2; end
                        else if (cnt2 == 5'd16)                 begin xsel = 3'd1; isel = 6'd3; end
                    end
                    4'd5: begin // Incremental PUF block XOR absorb (binds `arg[15]` mint_lock!)
                        e_rd   = {1'b0, cnt2};
                        wsel   = 3'd1;
                        e_wreq = ((cnt2 <= 5'd4) && !(puf_recon_mode && cnt2 == 5'd2)) || (cnt2 == 5'd16);
                        unique case (cnt2)
                            5'd0:    begin xsel = 3'd1; isel = 6'd21; end
                            5'd1:    begin xsel = 3'd1; isel = 6'd22; end
                            5'd2:    begin xsel = 3'd1; isel = 6'd23; end
                            5'd3:    begin xsel = 3'd1; isel = 6'd24; end
                            5'd4:    begin xsel = 3'd1; isel = 6'd2; end
                            5'd16:   begin xsel = 3'd1; isel = 6'd3; end
                            default: ;
                        endcase
                    end
                    4'd6: begin // PUF public verification tag H_pub = TurboSHAKE256("DREGGCHK" || sh[0..3] || mint_lock)
                        if (cnt2 == 5'd0)                      begin xsel = 3'd1; isel = 6'd25; end
                        else if (cnt2 >= 5'd1 && cnt2 <= 5'd4) begin wsel = 3'd2; e_rd = 6'd32 + (cnt2 - 5'd1); end
                        else if (cnt2 == 5'd5)                 begin xsel = 3'd1; isel = 6'd26; end
                        else if (cnt2 == 5'd6)                 begin xsel = 3'd1; isel = 6'd2; end
                        else if (cnt2 == 5'd16)                begin xsel = 3'd1; isel = 6'd3; end
                    end
                    4'd7: begin // ZK execution grant: "DREGGZKG" || K_vat[0..3] || epoch || zk_pin[0..3]
                        if (cnt2 == 5'd0)                      begin xsel = 3'd1; isel = 6'd27; end
                        else if (cnt2 >= 5'd1 && cnt2 <= 5'd4) begin wsel = 3'd2; e_rd = 6'd54 + (cnt2 - 5'd1); end
                        else if (cnt2 == 5'd5)                 begin xsel = 3'd1; isel = 6'd28; end
                        else if (cnt2 >= 5'd6 && cnt2 <= 5'd9) begin wsel = 3'd2; e_rd = 6'd44 + (cnt2 - 5'd6); end
                        else if (cnt2 == 5'd10)                begin xsel = 3'd1; isel = 6'd2; end
                        else if (cnt2 == 5'd16)                begin xsel = 3'd1; isel = 6'd3; end
                    end
                    default: begin // 4'd8: NFC MAC: "DREGGNFC" || K_vat[0..3] || {flags, 0, seq} || bind_lo || bind_hi
                        if (cnt2 == 5'd0)                      begin xsel = 3'd1; isel = 6'd29; end
                        else if (cnt2 >= 5'd1 && cnt2 <= 5'd4) begin wsel = 3'd2; e_rd = 6'd54 + (cnt2 - 5'd1); end
                        else if (cnt2 == 5'd5)                 begin xsel = 3'd1; isel = 6'd30; end
                        else if (cnt2 == 5'd6) begin
                            if (op == OP_CTH) begin wsel = 3'd2; e_rd = 6'd33; end
                            else              begin xsel = 3'd1; isel = 6'd28; end
                        end else if (cnt2 == 5'd7) begin
                            if (op == OP_CTH)         begin wsel = 3'd2; e_rd = 6'd34; end
                            else if (op == OP_VAT_ZK) begin wsel = 3'd2; e_rd = 6'd44; end
                        end else if (cnt2 == 5'd8)             begin xsel = 3'd1; isel = 6'd2; end
                        else if (cnt2 == 5'd16)                begin xsel = 3'd1; isel = 6'd3; end
                    end
                endcase
            end
            // ---------------------------------------------------------- FRAM anchor
            S_AR0[11:5], S_AW6[11:5]: an_start = 1'b1;
            S_AW1[11:5]: begin
                an_start = 1'b1;
                an_write = 1'b1;
            end
            S_AR1[11:5]: cond = an_stb;
            S_AR2[11:5]: an_go = 1'b1;
            S_AR3[11:5], S_AR4[11:5], S_AW8[11:5], S_AW9[11:5]: begin
                cond  = an_stb;
                an_go = an_stb;
                e_rd  = {5'd0, (sid == S_AR4[11:5] || sid == S_AW9[11:5])};
            end
            S_AW7[11:5], S_AW2[11:5]: begin
                cond  = an_stb;
                an_go = an_stb;
            end
            S_AR5[11:5], S_AW5[11:5], S_AWA[11:5]: cond = an_done;
            S_AW3[11:5], S_AW4[11:5]: begin
                cond  = an_stb;
                an_go = an_stb;
                e_rd  = {5'd0, (sid == S_AW4[11:5])};
            end
            // ---------------------------------------------------------- Cut-the-Hash + Chain-End Self-Check
            S_CTG[11:5], S_HVG[11:5]: begin
                kind      = K_GF;
                xsel      = 3'd1;
                isel = 6'd31;
                e_wlaunch = (op == OP_PRFMSG);
                e_wa      = 6'd41; // save hdr_word in sh[9] for OP_PRFMSG K_MAC mask!
            end
            S_CTL[11:5]: begin
                kind       = K_GF;
                cond       = in_valid;
                xsel       = 3'd0;
                e_wlaunch  = 1'b1;
                e_wa       = 6'd32 + {1'b0, cnt2};
                e_rd       = 6'd39 + {1'b0, cnt2}; // streams sh[8..9] (PK.seed) on cnt2 = 1, 2!
                do_pop     = 1'b1;
                vat_pk_clr = (cnt2 == 5'd0);
                vat_pk_we  = (cnt2 == 5'd1 || cnt2 == 5'd2);
            end
            S_CTT[11:5]: begin
                cond   = in_valid;
                do_pop = 1'b1;
                e_rd   = {5'd0, cnt2[0]};
                xsel   = 3'd3;
                gsel   = cnt2[0];
                wsel   = 3'd1; // e_wd = port ^ gf_acc[cnt2[0]]
            end
            S_CTD[11:5]: e_rd = 6'd32; // sh[0][31:0] = s0[31:0] = vat_req_epoch!
            S_CA2[11:5]: e_rd = 6'd32;
            S_CTS[11:5]: e_rd = 6'd37 + {4'd0, widx};
            S_CM0[11:5], S_CM1[11:5]: begin
                e_wreq = 1'b1;
                e_rd   = {5'd0, (sid == S_CM1[11:5])};
                e_wa   = 6'd6 + {5'd0, (sid == S_CM1[11:5])};
                wsel   = 3'd2;
            end
            S_CY0[11:5]: begin
                e_rd   = 6'd0;
                e_wa   = 6'd40;
                wsel   = 3'd2;
                e_wreq = 1'b1;
            end
            S_CY1[11:5]: begin
                e_rd   = 6'd1;
                e_wa   = 6'd41;
                wsel   = 3'd2;
                e_wreq = 1'b1;
            end
            S_CZ0[11:5]: begin
                cond   = in_valid;
                do_pop = 1'b1;
                e_rd   = 6'd0;
            end
            S_CZ1[11:5]: begin
                cond   = in_valid;
                do_pop = 1'b1;
                e_rd   = 6'd1;
            end
            S_CO[11:5]: begin
                cond      = out_ready;
                emit      = 1'b1;
                emit_port = 1'b1;
                e_rd      = self_chk ? (6'd40 + {5'd0, cnt2[0]}) : {5'd0, cnt2[0]};
            end
            // ---------------------------------------------------------- Houyhnhnm PUF + BCH (0x50)
            S_PF0[11:5]: begin
                cond         = !puf_recon_mode || in_valid;
                do_pop       = puf_recon_mode;
                puf_vmask_ld = puf_recon_mode && in_valid;
                // Absorb `vmask` (`in_data`) into `st[2]` before `S_HORN..S_BMU` reuses `vmsyn_q` for `syn_v`
                e_rd         = 6'd2;
                e_wa         = 6'd2;
                xsel         = 3'd0;
                wsel         = 3'd1;
                e_wreq       = puf_recon_mode;
            end
            S_PF1[11:5]: begin
                cond          = !puf_recon_mode || in_valid;
                do_pop        = puf_recon_mode;
                puf_syn_ld    = puf_recon_mode && in_valid;
                puf_start_blk = cond;
            end
            S_PF2[11:5]: begin
                cond = puf_done && (puf_recon_mode || out_ready);
                emit = !puf_recon_mode;
                isel = 6'd23;
            end
            S_PF3[11:5]: begin
                cond = puf_recon_mode || out_ready;
                emit = !puf_recon_mode;
                isel = 6'd24;
            end
            S_PF4[11:5]: begin
                // Copy all 10 derived words st[0..9] -> sh[0..9] (rows 32..41) so Reconstruct
                // commits the EXACT SAME `(K_vat[0..3], SK.seed[0..1], SK.prf[0..1], K_MAC[0..1])`!
                e_rd   = {1'b0, cnt2};
                e_wa   = 6'd32 + {1'b0, cnt2};
                wsel   = 3'd2;
                e_wreq = (cnt2 <= 5'd9);
                if (!puf_recon_mode && !puf_any_err) begin
                    kvat_we     = (cnt2 <= 5'd3) ? (4'b0001 << cnt2[1:0]) : 4'd0;
                    kvat_commit = (cnt2 == 5'd3);
                    key_we      = (cnt2 >= 5'd4 && cnt2 <= 5'd9) ? (6'b000001 << (cnt2 - 5'd4)) : 6'd0;
                end
            end
            S_PF5[11:5]: begin
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
                    e_rd        = 6'd32 + (cnt2 - 5'd4); // sh[0..9] = rows 32..41!
                    kvat_we     = (!puf_any_err && !macdiff && cnt2 >= 5'd4 && cnt2 <= 5'd7)
                                  ? (4'b0001 << (cnt2 - 5'd4)) : 4'd0;
                    kvat_commit = (!puf_any_err && !macdiff && cnt2 == 5'd7);
                    key_we      = (!puf_any_err && !macdiff && cnt2 >= 5'd8 && cnt2 <= 5'd13)
                                  ? (6'b000001 << (cnt2 - 5'd8)) : 6'd0;
                    if (cnt2 == 5'd14) begin
                        e_wreq = 1'b1;
                        e_wa   = 6'd0;
                        xsel   = 3'd1;
                        isel = 6'd36;
                    end
                end
            end
            // ---------------------------------------------------------- CapTP Vat & Keyed-MAC NFC
            S_VLD[11:5]: begin
                cond         = in_valid;
                do_pop       = 1'b1;
                e_rd         = 6'd44 + {4'd0, cnt2[1:0]}; // zk_pin[0..3] streamed to dregg_captp_vat!
                e_wreq       = 1'b1;
                e_wa         = 6'd32 + {1'b0, cnt2};
                xsel         = 3'd0;
                vat_pchk_clr = (cnt2 == 5'd0) && !(op == OP_VAT && !flags[0]);
                vat_pwe      = !(op == OP_VAT && !flags[0]);
            end
            S_VTG[11:5]: begin
                cond         = in_valid;
                do_pop       = 1'b1;
                e_rd         = {1'b0, cnt2};
                vat_cchk_clr = (cnt2 == 5'd3) && (op == OP_VAT);
            end
            S_VAT[11:5]: begin
                cond    = in_valid;
                do_pop  = 1'b1;
                e_rd    = 6'd32 + {1'b0, cnt2};
                e_wreq  = 1'b1;
                e_wa    = 6'd32 + {1'b0, cnt2};
                xsel    = 3'd0;
                vat_cwe = 1'b1;
            end
            S_VOT[11:5]: begin
                cond      = out_ready;
                emit      = 1'b1;
                emit_port = 1'b1;
                e_rd      = (cnt2 < 5'd8) ? (6'd32 + {1'b0, cnt2}) : {1'b0, cnt2 - 5'd8};
            end
            S_NFC[11:5]: e_rd = {5'd0, cnt2[0]};
            S_VZK[11:5]: ;
            // ---------------------------------------------------------- DB + NCO (0x52)
            S_DB0[11:5]: begin
                cond             = in_valid;
                do_pop           = 1'b1;
                db_load_r0       = permit_control && in_valid && (cnt2 == 5'd0) && arg[0];
                db_load_r1       = permit_control && in_valid && (cnt2 == 5'd1) && arg[0];
                db_arm_responder = permit_control && in_valid && (cnt2 == 5'd2) && arg[0];
                db_step_round    = permit_control && in_valid && (cnt2 == 5'd2) && arg[1];
                db_launch_ping   = permit_control && in_valid && (cnt2 == 5'd2) && arg[2] && !arg[3];
                db_cal_ping      = permit_control && in_valid && (cnt2 == 5'd2) && arg[2] &&  arg[3];
                nco_pkt_load     = permit_control && in_valid && (cnt2 == 5'd1) && arg[4] &&  arg[12];
            end
            S_DBO[11:5]: begin
                cond = out_ready;
                emit = 1'b1;
                unique case (cnt2[1:0])
                    2'd0:    isel = 6'd32;
                    2'd1:    isel = 6'd33;
                    2'd2:    isel = 6'd34;
                    default: isel = 6'd35;
                endcase
            end
            // ---------------------------------------------------------- Verifier VM (Ext4 + Fp5)
            S_HVR[11:5]: begin
                if (wrem == 21'd0) kind = K_NONE;
                else begin
                    kind   = K_GF;
                    cond   = in_valid;
                    xsel   = 3'd0;
                    do_pop = 1'b1;
                end
            end
            S_HVH[11:5]: begin
                kind  = (ha[2:0] != 3'd0) ? K_FE : K_NONE;
                fe_op = F_MOV;
                fe_d  = rb_vm(fp5_vm, ha[2:0]);
                fe_s1 = 6'd0;
                fe_n  = vm_limbs;
            end
            S_HVA[11:5]: begin
                kind  = K_FE;
                fe_op = fp5_vm ? ((hop == 4'd2) ? F_FP5_MUL : (hop == 4'd3) ? F_FP5_ADD : F_FP5_SUB)
                               : ((hop == 4'd2) ? F_EMUL    : (hop == 4'd3) ? F_EADD    : F_ESUB);
                fe_d  = rb_vm(fp5_vm, ha[2:0]);
                fe_s1 = rb_vm(fp5_vm, hb[2:0]);
                fe_s2 = rb_vm(fp5_vm, hc[2:0]);
            end
            S_HVE[11:5]: begin
                kind  = K_FE;
                fe_op = fp5_vm ? F_FP5_EQ : F_EEQ;
                fe_s1 = rb_vm(fp5_vm, hb[2:0]);
                fe_s2 = rb_vm(fp5_vm, hc[2:0]);
            end
            S_HVP[11:5]: begin
                kind  = K_FE;
                fe_op = F_LDRES;
                fe_s1 = rb_vm(fp5_vm, hb[2:0]);
            end
            S_HVI[11:5]: begin
                kind  = K_FE;
                fe_op = F_LDRES;
                fe_s1 = rb_vm(fp5_vm, hb[2:0]) + {4'd0, ha[1:0]};
            end
            S_HVN[11:5]: begin
                cond   = (dleft == 16'd0) || in_valid;
                do_pop = (dleft != 16'd0);
            end
            S_HVF[11:5]: begin
                if (cnt2 < {2'd0, vm_limbs}) begin
                    e_wreq = 1'b1;
                    e_rd   = 6'd12 + {1'b0, cnt2};
                    e_wa   = 6'd32 + {1'b0, cnt2};
                    wsel   = 3'd2;
                end else if (vm_pin_mode && verdict) begin
                    logic [1:0] pidx;
                    pidx = cnt2[1:0] - (fp5_vm ? 2'd1 : 2'd0);
                    unique case (pidx)
                        2'd0: begin e_rd = 6'd33; zkpin_we = 4'b0100; zkpin_wdata = y_hold0;       end
                        2'd1: begin e_rd = 6'd35; zkpin_we = 4'b0001; zkpin_wdata = gf_acc[63:0];  end
                        2'd2: begin               zkpin_we = 4'b0010; zkpin_wdata = gf_acc[127:64]; end
                        default: begin            zkpin_we = 4'b1000; zkpin_wdata = y_hold0;       end
                    endcase
                    zk_latch_set = (pidx == 2'd3);
                end
            end
            S_HVS[11:5]: begin
                cond = out_ready;
                emit = 1'b1;
                isel = 6'd19;
            end
            default: ;
        endcase
        if (sid == S_IDLE[11:5] && in_valid && (in_data[7:0] == 8'h51) &&
            (in_data[15:8] == OP_FOLD || in_data[15:8] == OP_HEM))
            zk_latch_clr = 1'b1;
        if (emit && !emit_port) xsel = 3'd1;
    end


    // Single flat constant-folded 64-bit immediate OR-bus (replaces 9 nested 64-bit $pmux trees!)
    logic [36:1] is_oh;
    always_comb begin
        for (int k = 1; k <= 36; k++) is_oh[k] = (isel == 6'(k));
        imm = ({64{is_oh[1]}}  & 64'd1)
            | ({64{is_oh[2]}}  & 64'h1F)
            | ({64{is_oh[3]}}  & PAD_END)
            | ({64{is_oh[4]}}  & {rcode, rlen, rerr, 6'd0, rok, op | 8'h80, 8'h51})
            | ({64{is_oh[5]}}  & CHIP_ID)
            | ({64{is_oh[6]}}  & tel0)
            | ({64{is_oh[7]}}  & {vat_spend_used[15:0], 8'd0, vat_mint_locked, zk_root_valid,
                                  nfc_frame_rdy, vat_ready, hwm_valid, fault_mac, fault_anchor, key_valid, tel1})
            | ({64{is_oh[8]}}  & trng_word)
            | ({64{is_oh[9]}}  & FS_INIT)
            | ({64{is_oh[10]}} & P2_IV)
            | ({64{is_oh[11]}} & {48'd0, hs_n})
            | ({64{is_oh[12]}} & t0_word)
            | ({64{is_oh[13]}} & {63'd0, verdict})
            | ({64{is_oh[14]}} & ksd_pad)
            | ({64{is_oh[15]}} & a3_word)
            | ({64{is_oh[16]}} & {32'd0, ctmp})
            | ({64{is_oh[17]}} & C_FRAM)
            | ({64{is_oh[18]}} & C_MASK)
            | ({64{is_oh[19]}} & stat_word)
            | ({64{is_oh[20]}} & C_VAT)
            | ({64{is_oh[21]}} & (C_PUF ^ {arg[15], 60'd0, puf_blk}))
            | ({64{is_oh[22]}} & puf_word_out)
            | ({64{is_oh[23]}} & puf_vmask_out)
            | ({64{is_oh[24]}} & {37'd0, puf_syn_out})
            | ({64{is_oh[25]}} & C_PUF_CHK)
            | ({64{is_oh[26]}} & {arg[15], 63'd0})
            | ({64{is_oh[27]}} & C_ZKG)
            | ({64{is_oh[28]}} & {48'd0, arg})
            | ({64{is_oh[29]}} & C_NFC)
            | ({64{is_oh[30]}} & {nfc_quorum_flags, 16'd0, nfc_seq})
            | ({64{is_oh[31]}} & hdr_word)
            | ({64{is_oh[32]}} & {nfc_rx_frames, nfc_quorum_flags, 19'd0, db_cal_valid,
                                  nco_tx_active, nfc_frame_rdy, db_responder_armed,
                                  db_dist_timeout, db_dist_valid, db_rounds_done})
            | ({64{is_oh[33]}} & {32'd0, db_dist_cycles})
            | ({64{is_oh[34]}} & db_chal_log)
            | ({64{is_oh[35]}} & db_resp_log)
            | ({64{is_oh[36]}} & {48'd0, 7'd0, !puf_any_err, puf_corr_tot});
    end
    wire cth_pub_illegal = pubgen && !is_fors && (sw != 5'd4);
    assign vat_commit_inv = fire && (
        (sid == S_VZK[11:5] && vat_inv_ok) ||
        (sid == S_KSW[11:5] && op == OP_PRFMSG && cap_mode && key_valid && !macdiff && vat_inv_ok) ||
        (sid == S_CTD[11:5] && cap_mode && key_valid && !macdiff && !cth_pub_illegal && vat_inv_ok && (!stateful || pubgen)) ||
        (sid == S_CA3[11:5] && cap_mode && rcmp)
    );

    // Hardwired enclave secret non-exfiltration gate: addresses >= 44 (`zk_pin`, `key`, `kvat`)
    // can NEVER reach `out_data`, even under arbitrary multi-bit control-flow faults!
    wire rd_is_secret = (e_rd >= 6'd44);
    assign an_tx      = (sid == S_AW2[11:5]) ? {32'd0, ctmp} : port;

    // Single shared 64-bit equality comparator across FRAM, Tag, Vat, PUF, NFC, and CTH DFA checks!
    wire cmp_in_lhs   = (sid == S_CTT[11:5]) || (sid == S_VTG[11:5]) || (sid == S_PF5[11:5]) ||
                        (sid == S_CZ0[11:5]) || (sid == S_CZ1[11:5]) ||
                        (sid == S_VLD[11:5]) || (sid == S_VAT[11:5]) || (sid == S_CTL[11:5]);
    wire [63:0] cmp_lhs = cmp_in_lhs            ? in_data :
                          (sid == S_NFC[11:5])  ? (cnt2[0] ? {32'd0, nfc_mac[95:64]} : nfc_mac[63:0]) :
                                                  an_rx;
    wire [63:0] cmp_rhs = (sid == S_AW7[11:5]) ? {32'd0, ctmp} :
                          (sid == S_CTT[11:5]) ? e_wd :
                          (sid == S_NFC[11:5] && cnt2[0]) ? {32'd0, port[31:0]} :
                                                  port;
    wire cmp_eq       = (cmp_lhs == cmp_rhs);
    assign cmp_ne     = !cmp_eq;
    assign fe_start   = launch && (kind == K_FE);
    assign kc_start   = launch && (kind == K_KC);
    assign gf_start   = launch && (kind == K_GF);
    assign in_pop     = fire && do_pop;
    assign out_push   = fire && emit;
    assign out_data   = emit_port ? (rd_is_secret ? 64'd0 : port) : imm;
    assign e_we       = (fire && e_wreq) || (launch && e_wlaunch);

    wire [4:0] hvf_last = vm_pin_mode ? ({2'd0, vm_limbs} + 5'd3) : ({2'd0, vm_limbs} - 5'd1);

    logic [6:0] nxt_st_id, nxt_ret_id, nxt_ret2_id, nxt_ret3_id;
    always_comb begin
        nxt_st_id   = sid;
        nxt_ret_id  = ret[11:5];
        nxt_ret2_id = ret2[11:5];
        nxt_ret3_id = ret3[11:5];
        unique case (sid)
            S_IDLE[11:5]: begin
                nxt_ret_id  = idle_ret_id;
                nxt_ret2_id = idle_ret2_id;
                nxt_ret3_id = S_IDLE[11:5];
                nxt_st_id   = idle_st_id;
            end
            S_DRAIN[11:5]: if (wrem == 21'd0) nxt_st_id = S_EHDR[11:5];
            S_EHDR[11:5]:  nxt_st_id = S_WIPE[11:5];
            S_HDR[11:5]: begin
                nxt_st_id = ret[11:5];
                if (ret[11:5] == S_HDR[11:5]) begin
                    nxt_ret_id = (op == OP_VAT_ZK || op == OP_PRFMSG) ? S_WIPE[11:5] : S_IDLE[11:5];
                    nxt_st_id  = S_OUTL[11:5];
                end
            end
            S_OUTL[11:5]: if (cnt2 + 5'd1 == olim) nxt_st_id = ret[11:5];
            S_WIPE[11:5]: nxt_st_id = S_IDLE[11:5];
            S_PING[11:5]: if (cnt2 == 5'd3) nxt_st_id = S_IDLE[11:5];
            S_CSR[11:5]:  begin nxt_ret_id = S_IDLE[11:5]; nxt_st_id = S_HDR[11:5]; end
            // ------------------------------------------------ OP_BIST
            S_BSW[11:5]: nxt_st_id = S_BS0[11:5];
            S_BS0[11:5]: if (cnt2 == 5'd2) begin nxt_ret3_id = S_BS1[11:5]; nxt_st_id = S_BKC[11:5]; end
            S_BS1[11:5]: nxt_st_id = S_BS2[11:5];
            S_BS2[11:5]: begin nxt_ret_id = S_BSO[11:5]; nxt_st_id = S_HDR[11:5]; end
            S_BSO[11:5]: nxt_st_id = S_WIPE[11:5];
            // ------------------------------------------------ Poseidon2
            S_P2R[11:5]:  if (cnt2 == 5'd11) nxt_st_id = S_P2RP[11:5];
            S_P2RP[11:5]: begin nxt_ret_id = S_HDR[11:5]; nxt_st_id = S_HDR[11:5]; end
            S_HSZ[11:5]:  if (cnt2 == (hs_rate6 ? 5'd11 : 5'd7)) nxt_st_id = hs_rate6 ? S_HSL[11:5] : S_HSD[11:5];
            S_HSD[11:5]:  if (!bindw) nxt_st_id = S_HSC[11:5];
            S_HSC[11:5]:  if (hs_capsrc == 2'd1 || cnt2 == 5'd3) nxt_st_id = S_HSN[11:5];
            S_HSN[11:5]:  nxt_st_id = S_HSL[11:5];
            S_HSL[11:5]: begin
                if (hs_n == 16'd0) begin
                    if (!hs_rate6 || hs_pad_done) nxt_st_id = S_HSF[11:5];
                end else if (!bindw && !hs_lat_now && hs_idx == (hs_rate6 ? 4'd5 : 4'd7)) begin
                    nxt_st_id = S_HSP[11:5];
                end
            end
            S_HSP[11:5]: nxt_st_id = S_HSL[11:5];
            S_HSF[11:5]: nxt_st_id = ret[11:5];
            // ------------------------------------------------ Canopy
            S_MK0[11:5]: nxt_st_id = S_MK1[11:5];
            S_MK1[11:5]: nxt_st_id = S_MK2[11:5];
            S_MK2[11:5]: nxt_st_id = S_MK3[11:5];
            S_MK3[11:5]: nxt_st_id = S_MK4[11:5];
            S_MK4[11:5]: nxt_st_id = S_MK5[11:5];
            S_MK5[11:5]: nxt_st_id = S_MPS[11:5];
            S_MPS[11:5]: begin
                if (cnt == 16'd0) nxt_st_id = ret2[11:5];
                else if (cnt2 == 5'd3) nxt_st_id = S_MK0[11:5];
            end
            S_MOK[11:5]: if (cnt2 == 5'd2) nxt_st_id = S_MOI[11:5];
            S_MOI[11:5]: nxt_st_id = S_MOL[11:5];
            S_MOL[11:5]: if (cnt2 == 5'd3) begin nxt_ret2_id = S_MOR[11:5]; nxt_st_id = S_MPS[11:5]; end
            S_MOR[11:5]: if (cnt2 == 5'd3) nxt_st_id = S_MOE[11:5];
            S_MOE[11:5]: begin nxt_ret_id = S_MOV[11:5]; nxt_st_id = S_HDR[11:5]; end
            S_MOV[11:5]: begin nxt_ret_id = S_IDLE[11:5]; nxt_st_id = S_OUTL[11:5]; end
            // ------------------------------------------------ Keccak & Authenticated PRF_msg
            S_KSW[11:5]: begin
                if (op == OP_PRFMSG) begin
                    if (!key_valid || (cap_mode && (macdiff || !vat_inv_ok))) nxt_st_id = S_DRAIN[11:5];
                    else nxt_st_id = S_KSK[11:5];
                end else nxt_st_id = S_KSA[11:5];
            end
            S_KSK[11:5]: if (cnt2 == 5'd1) nxt_st_id = S_KSA[11:5];
            S_KSA[11:5]: if (!(prf_legacy_tag && (ksa_has_msg || ksa_is_part) && !gfdone)) begin
                if (!ksa_has_msg) nxt_st_id = S_KSD[11:5];
                else if (wi == 5'd16) nxt_st_id = S_KSP[11:5];
            end
            S_KSP[11:5]: nxt_st_id = S_KSA[11:5];
            S_KSD[11:5]: nxt_st_id = S_KSE[11:5];
            S_KSE[11:5]: nxt_st_id = S_KSQ[11:5];
            S_KSQ[11:5]: begin
                if (prf_legacy_tag) nxt_st_id = S_PFT[11:5];
                else begin nxt_ret_id = S_KSO[11:5]; nxt_st_id = S_HDR[11:5]; end
            end
            S_PFT[11:5]: if (cnt2 == 5'd2) begin nxt_ret3_id = S_CTT[11:5]; nxt_st_id = S_BLD[11:5]; end
            S_KSO[11:5]: begin
                if (cnt == 16'd0) nxt_st_id = S_WIPE[11:5];
                else if (wi == 5'd16 && cnt != 16'd1) nxt_st_id = S_KSR[11:5];
            end
            S_KSR[11:5]: nxt_st_id = S_KSO[11:5];
            // ------------------------------------------------ Key load
            S_KLM[11:5]: if (cnt2 == 5'd1) nxt_st_id = flags[0] ? S_KLH[11:5] : (!trng_ok ? S_DRAIN[11:5] : S_KLW[11:5]);
            S_KLH[11:5]: if (cnt2 == (flags[2] ? 5'd7 : 5'd3)) nxt_st_id = S_KLN[11:5];
            S_KLW[11:5]: nxt_st_id = S_KLT[11:5];
            S_KLT[11:5]: if (wi == 5'd3) nxt_st_id = S_KLA[11:5];
            S_KLA[11:5]: if (wrem == 21'd0) nxt_st_id = S_KLD[11:5];
            S_KLD[11:5]: nxt_st_id = S_KLE[11:5];
            S_KLE[11:5]: nxt_st_id = S_KLP[11:5];
            S_KLP[11:5]: nxt_st_id = S_KLK[11:5];
            S_KLK[11:5]: if (cnt2 == (flags[2] ? 5'd7 : 5'd3)) nxt_st_id = S_KLZ[11:5];
            S_KLZ[11:5]: nxt_st_id = S_KLN[11:5];
            S_KLN[11:5]: begin
                if (flags[1]) begin nxt_ret3_id = S_AW1[11:5]; nxt_ret2_id = S_KLF[11:5]; nxt_st_id = S_BLD[11:5]; end
                else          begin nxt_ret_id  = S_IDLE[11:5]; nxt_st_id  = S_HDR[11:5]; end
            end
            S_KLF[11:5]: begin
                if (!rcmp)       nxt_st_id = S_DRAIN[11:5];
                else if (!aslot) begin nxt_ret3_id = S_AW1[11:5]; nxt_st_id = S_BLD[11:5]; end
                else             begin nxt_ret_id  = S_IDLE[11:5]; nxt_st_id = S_HDR[11:5]; end
            end
            S_BLD[11:5]: if (cnt2 == 5'd24) nxt_st_id = S_BKC[11:5];
            S_BKC[11:5]: nxt_st_id = ret3[11:5];
            // ------------------------------------------------ FRAM anchor
            S_AR0[11:5]: nxt_st_id = S_AR1[11:5];
            S_AR1[11:5]: begin nxt_ret3_id = S_AR2[11:5]; nxt_st_id = S_BLD[11:5]; end
            S_AR2[11:5]: nxt_st_id = S_AR3[11:5];
            S_AR3[11:5]: nxt_st_id = S_AR4[11:5];
            S_AR4[11:5]: nxt_st_id = S_AR5[11:5];
            S_AR5[11:5]: nxt_st_id = ret2[11:5];
            S_AW1[11:5]: nxt_st_id = S_AW2[11:5];
            S_AW2[11:5]: nxt_st_id = S_AW3[11:5];
            S_AW3[11:5]: nxt_st_id = S_AW4[11:5];
            S_AW4[11:5]: nxt_st_id = S_AW5[11:5];
            S_AW5[11:5]: nxt_st_id = S_AW6[11:5];
            S_AW6[11:5]: nxt_st_id = S_AW7[11:5];
            S_AW7[11:5]: nxt_st_id = S_AW8[11:5];
            S_AW8[11:5]: nxt_st_id = S_AW9[11:5];
            S_AW9[11:5]: nxt_st_id = S_AWA[11:5];
            S_AWA[11:5]: nxt_st_id = ret2[11:5];
            // ------------------------------------------------ Cut-the-Hash + PRF_msg Tag
            S_CTG[11:5]: nxt_st_id = (op == OP_PRFMSG) ? S_KSK[11:5] : S_CTL[11:5];
            S_CTL[11:5]: if (cnt2 == 5'd7) begin
                if (cap_mode) begin
                    if (vat_need_nfc) begin nxt_ret2_id = S_CTD[11:5]; nxt_ret3_id = S_NFC[11:5]; nxt_st_id = S_BLD[11:5]; end
                    else nxt_st_id = S_CTD[11:5];
                end else begin
                    nxt_ret3_id = S_CTT[11:5];
                    nxt_st_id   = S_BLD[11:5];
                end
            end
            S_CTT[11:5]: if (cnt2 == 5'd1) begin
                if (op == OP_PRFMSG) begin
                    if (macdiff || cmp_ne) nxt_st_id = S_EHDR[11:5];
                    else begin nxt_ret_id = S_HDR[11:5]; nxt_st_id = S_HDR[11:5]; end
                end else nxt_st_id = S_CTD[11:5];
            end
            S_CTD[11:5]: begin
                if (!key_valid || macdiff || cth_pub_illegal || (cap_mode && !vat_inv_ok)) nxt_st_id = S_DRAIN[11:5];
                else if (stateful && !pubgen) begin nxt_ret2_id = S_CA0[11:5]; nxt_st_id = S_AR0[11:5]; end
                else                          begin nxt_ret_id  = S_CTS[11:5]; nxt_st_id = S_HDR[11:5]; end
            end
            S_CA0[11:5]: begin nxt_ret2_id = S_CA1[11:5]; nxt_st_id = S_AR0[11:5]; end
            S_CA1[11:5]: nxt_st_id = S_CA2[11:5];
            S_CA2[11:5]: begin
                if (!anyv || (hwm_valid && cur < hwm) || port[31:0] < cur || port[31:0] == 32'hFFFF_FFFF)
                    nxt_st_id = S_DRAIN[11:5];
                else begin nxt_ret3_id = S_AW1[11:5]; nxt_ret2_id = S_CA3[11:5]; nxt_st_id = S_BLD[11:5]; end
            end
            S_CA3[11:5]: begin
                if (!rcmp) nxt_st_id = S_DRAIN[11:5];
                else       begin nxt_ret_id = S_CTS[11:5]; nxt_st_id = S_HDR[11:5]; end
            end
            S_CTS[11:5]: begin
                if (ci == nch) nxt_st_id = S_WIPE[11:5];
                else           begin nxt_ret3_id = S_CKD[11:5]; nxt_st_id = S_BLD[11:5]; end
            end
            S_CM0[11:5]: nxt_st_id = S_CM1[11:5];
            S_CM1[11:5]: nxt_st_id = S_BLD[11:5];
            S_CKD[11:5]: begin
                if (steps == 16'd0)
                    nxt_st_id = self_chk ? (chk_cont ? S_CZ0[11:5] : S_CY0[11:5]) : S_CO[11:5];
                else
                    nxt_st_id = S_CM0[11:5];
            end
            S_CY0[11:5]: nxt_st_id = S_CY1[11:5];
            S_CY1[11:5]: begin
                if (sym == symmask) nxt_st_id = S_CZ0[11:5];
                else                begin nxt_ret3_id = S_CKD[11:5]; nxt_st_id = S_CM0[11:5]; end
            end
            S_CZ0[11:5]: nxt_st_id = S_CZ1[11:5];
            S_CZ1[11:5]: nxt_st_id = ((dfa_ok_q != 2'b10) || cmp_ne || (hj != symmask)) ? S_DEAD[11:5] : S_CZ2[11:5];
            S_CZ2[11:5]: nxt_st_id = (dfa_ok_q != 2'b10) ? S_DEAD[11:5] : S_CO[11:5];
            S_CO[11:5]:  if (cnt2 == 5'd1) nxt_st_id = S_CTS[11:5];
            // ------------------------------------------------ Houyhnhnm PUF + BCH (0x50)
            S_PF0[11:5]: nxt_st_id = S_PF1[11:5];
            S_PF1[11:5]: nxt_st_id = S_PF2[11:5];
            S_PF2[11:5]: nxt_st_id = S_PF3[11:5];
            S_PF3[11:5]: begin
                nxt_ret3_id = (puf_blk == 3'd7) ? S_PF4[11:5] : S_PF0[11:5];
                nxt_st_id   = S_BLD[11:5];
            end
            S_PF4[11:5]: if (cnt2 == 5'd9) begin nxt_ret3_id = S_PF5[11:5]; nxt_st_id = S_BLD[11:5]; end
            S_PF5[11:5]: begin
                if (!puf_recon_mode) begin
                    if (cnt2 == 5'd3) nxt_st_id = S_WIPE[11:5];
                end else if (cnt2 == 5'd3) begin
                    if (puf_any_err || macdiff || cmp_ne) nxt_st_id = S_EHDR[11:5];
                end else if (cnt2 == 5'd14) begin
                    nxt_ret_id = S_BSO[11:5];
                    nxt_st_id  = S_HDR[11:5];
                end
            end
            // ------------------------------------------------ CapTP Vat & Keyed-MAC NFC
            S_VLD[11:5]: if (cnt2 == 5'd7) begin
                nxt_ret3_id = (op == OP_VAT && !flags[0]) ? S_HDR[11:5] : S_VTG[11:5];
                if (op == OP_VAT && !flags[0]) nxt_ret_id = S_VOT[11:5];
                nxt_st_id = S_BLD[11:5];
            end
            S_VTG[11:5]: if (cnt2 == 5'd3) begin
                if (macdiff || cmp_ne) nxt_st_id = S_DRAIN[11:5];
                else if (vat_need_nfc && (op == OP_PRFMSG || op == OP_VAT_ZK)) begin
                    nxt_ret3_id = S_NFC[11:5];
                    nxt_st_id   = S_BLD[11:5];
                end else nxt_st_id = ret2[11:5];
            end
            S_NFC[11:5]: if (cnt2 == 5'd1) begin
                if (!nfc_frame_rdy || (nfc_seq <= nfc_last_seq_q) || macdiff || cmp_ne) nxt_st_id = S_DRAIN[11:5];
                else nxt_st_id = ret2[11:5];
            end
            S_VAT[11:5]: if (cnt2 == 5'd7) begin
                nxt_ret3_id = S_HDR[11:5];
                nxt_ret_id  = S_VOT[11:5];
                nxt_st_id   = vat_att_step_ok ? S_BLD[11:5] : S_DRAIN[11:5];
            end
            S_VOT[11:5]: if (cnt2 == 5'd11) nxt_st_id = S_WIPE[11:5];
            S_VZK[11:5]: begin
                if (!vat_inv_ok) nxt_st_id = S_DRAIN[11:5];
                else begin nxt_ret3_id = S_HDR[11:5]; nxt_ret_id = S_HDR[11:5]; nxt_st_id = S_BLD[11:5]; end
            end
            // ------------------------------------------------ DB + NCO (0x52)
            S_DB0[11:5]: if (cnt2 == 5'd2) begin nxt_ret_id = S_DBO[11:5]; nxt_st_id = S_HDR[11:5]; end
            S_DBO[11:5]: if (cnt2 == 5'd3) nxt_st_id = S_IDLE[11:5];
            // ------------------------------------------------ Verifier VM
            S_HVG[11:5]: nxt_st_id = S_HVR[11:5];
            S_HVR[11:5]: nxt_st_id = (wrem == 21'd0) ? S_HVF[11:5] : S_HVD[11:5];
            S_HVD[11:5]: begin
                unique case (hop)
                    4'd1: begin
                        if (dleft == 16'd0 && !hc[6]) nxt_st_id = S_HVN[11:5];
                        else begin nxt_ret_id = S_HVH[11:5]; nxt_st_id = S_HSZ[11:5]; end
                    end
                    4'd2, 4'd3, 4'd4: nxt_st_id = S_HVA[11:5];
                    4'd5: nxt_st_id = (dleft != {13'd0, vm_limbs} || (vm_pin_mode && ha[2:0] == 3'd1)) ? S_HVN[11:5] : S_HVL[11:5];
                    4'd6: nxt_st_id = S_HVE[11:5];
                    4'd7: nxt_st_id = S_HVP[11:5];
                    4'd8: nxt_st_id = (ha[5:0] == 6'd0 || ha[5:0] > 6'd32 ||
                                       dleft != 16'd1 + {8'd0, ha[5:0], 2'd0}) ? S_HVN[11:5] : S_HVM[11:5];
                    4'd9: nxt_st_id = S_HVI[11:5];
                    default: nxt_st_id = S_HVN[11:5];
                endcase
            end
            S_HVH[11:5], S_HVA[11:5], S_HVE[11:5], S_HVQ[11:5], S_HVJ[11:5]: nxt_st_id = S_HVN[11:5];
            S_HVL[11:5]: if (!bindw && cnt2 + 5'd1 == {2'd0, vm_limbs}) nxt_st_id = S_HVN[11:5];
            S_HVP[11:5]: nxt_st_id = S_HVQ[11:5];
            S_HVM[11:5]: begin nxt_ret2_id = S_HVN[11:5]; nxt_st_id = S_MPS[11:5]; end
            S_HVI[11:5]: nxt_st_id = S_HVJ[11:5];
            S_HVN[11:5]: if (dleft == 16'd0) nxt_st_id = S_HVR[11:5];
            S_HVF[11:5]: if (cnt2 == hvf_last) begin
                nxt_ret3_id = S_HDR[11:5];
                nxt_ret_id  = S_HVS[11:5];
                nxt_st_id   = S_BLD[11:5];
            end
            S_HVS[11:5]: begin nxt_ret_id = S_HVC[11:5];  nxt_st_id = S_OUTL[11:5]; end
            S_HVC[11:5]: begin nxt_ret_id = S_WIPE[11:5]; nxt_st_id = S_OUTL[11:5]; end
            default:     nxt_st_id = S_DEAD[11:5];
        endcase
    end

    // ------------------------------------------------------------------ FSM sequencing
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
            nfc_auth_ok     <= 1'b0;
            nfc_drop_pulse  <= 1'b0;
        end else if (zeroize_q || control_bad || fault_control || fault_laser_dfa) begin
            st              <= S_DEAD;
            w               <= 1'b0;
            key_valid       <= 1'b0;
            vat_mint_locked <= 1'b0;
            verify_ok       <= 1'b0;
            hwm_valid       <= 1'b0;
            nfc_auth_ok     <= 1'b0;
            nfc_drop_pulse  <= 1'b0;
        end else begin
            nfc_drop_pulse <= 1'b0;
            if (launch) w <= 1'b1;
            if (fire) begin
                w    <= 1'b0;
                st   <= hd4_enc(nxt_st_id);
                ret  <= hd4_enc(nxt_ret_id);
                ret2 <= hd4_enc(nxt_ret2_id);
                ret3 <= hd4_enc(nxt_ret3_id);
                unique case (sid)
                    S_IDLE[11:5]: begin
                        nfc_auth_ok <= 1'b0;
                        if (in_data[7:0] == 8'h51) begin
                            if (in_data[15:8] == OP_BIST || in_data[15:8] == OP_P2 ||
                                in_data[15:8] == OP_MERKLE || in_data[15:8] == OP_FOLD ||
                                in_data[15:8] == OP_HEM)
                                verify_ok <= 1'b0;
                            if (in_data[15:8] == OP_VAT && idle_err == 16'd0 && !in_data[16] && in_data[19])
                                vat_mint_locked <= 1'b1;
                        end
                    end
                    S_BS2[11:5]: verify_ok <= (e_wd == BIST_GOLDEN_KAT);
                    S_MOE[11:5]: verify_ok <= fe_eq;
                    S_KSW[11:5]: if (op == OP_PRFMSG && key_valid && cap_mode && macdiff) fault_mac <= 1'b1;
                    S_KLN[11:5]: key_valid <= 1'b1;
                    S_KLF[11:5]: begin
                        if (!rcmp) begin
                            key_valid    <= 1'b0;
                            fault_anchor <= 1'b1;
                        end else if (aslot) hwm_valid <= 1'b1;
                    end
                    S_CTT[11:5]: if (cnt2 == 5'd1 && op == OP_PRFMSG && (macdiff || cmp_ne)) fault_mac <= 1'b1;
                    S_CTD[11:5]: if (key_valid && macdiff) fault_mac <= 1'b1;
                    S_CA2[11:5]: if (anyv && hwm_valid && cur < hwm) fault_anchor <= 1'b1;
                    S_CA3[11:5]: begin
                        if (!rcmp) fault_anchor <= 1'b1;
                        else       hwm_valid    <= 1'b1;
                    end
                    S_CTS[11:5]: if (ci != nch) begin
                        logic [15:0] st_init;
                        st_init     = pubgen ? (is_fors ? 16'd1 : symmask) : (is_fors ? 16'd0 : (port_sh16 & symmask));
                        steps       <= st_init;
                        steps_inv_q <= ~st_init;
                    end
                    S_CKD[11:5]: if (steps != 16'd0) begin
                        steps       <= steps - 16'd1;
                        steps_inv_q <= steps_inv_q + 16'd1;
                    end
                    S_CY1[11:5]: if (sym != symmask) begin
                        logic [15:0] rem_st;
                        rem_st      = symmask - sym - 16'd1;
                        steps       <= rem_st;
                        steps_inv_q <= ~rem_st;
                    end
                    S_CZ1[11:5]: if ((dfa_ok_q != 2'b10) || cmp_ne || (hj != symmask)) fault_laser_dfa <= 1'b1;
                    S_CZ2[11:5]: if (dfa_ok_q != 2'b10) fault_laser_dfa <= 1'b1;
                    S_PF4[11:5]: if (cnt2 == 5'd9 && !puf_recon_mode && !puf_any_err) begin
                        key_valid       <= 1'b1;
                        vat_mint_locked <= arg[15];
                    end
                    S_PF5[11:5]: if (puf_recon_mode && cnt2 == 5'd14) begin
                        key_valid       <= 1'b1;
                        vat_mint_locked <= arg[15];
                    end
                    S_VTG[11:5]: if (cnt2 == 5'd3 && (macdiff || cmp_ne)) fault_mac <= 1'b1;
                    S_NFC[11:5]: if (cnt2 == 5'd1) begin
                        if (!nfc_frame_rdy || (nfc_seq <= nfc_last_seq_q)) begin
                            if (nfc_frame_rdy) nfc_drop_pulse <= 1'b1;
                        end else if (macdiff || cmp_ne) begin
                            fault_mac      <= 1'b1;
                            nfc_drop_pulse <= 1'b1;
                        end else nfc_auth_ok <= 1'b1;
                    end
                    S_DB0[11:5]: if (cnt2 == 5'd0 && arg[4]) begin
                        nco_en        <= arg[7];
                        nco_mode      <= arg[6:5];
                        nco_sym_shift <= arg[11:8];
                    end
                    S_HVF[11:5]: if (cnt2 == hvf_last) verify_ok <= verdict;
                    default: ;
                endcase
            end
        end
    end

    // ------------------------------------------------------------------ Clock-gated wide registers (`qsag_ereg`)
    wire reg_alive = !(zeroize_q || control_bad || fault_control || fault_laser_dfa);
    wire fg        = fire && reg_alive;

    qsag_ereg #(.W(64)) u_csr_reg (
        .clk(clk), .rst_n(rst_n), .en(fg && (sid == S_CSR[11:5])),
        .d(in_data ^ CSR_RST), .q(csr_xor_q)
    );
    assign nco_cfg_we = fg && (sid == S_DB0[11:5]) && (cnt2 == 5'd0) && arg[4];
    qsag_ereg_nr #(.W(35)) u_pkt_hdr (
        .clk(clk), .en(fg && (sid == S_IDLE[11:5])),
        .d({in_data[63:48], in_data[23:16], in_data[15:8], in_data[26:24]}),
        .q({arg, flags, op, lenb})
    );
    qsag_ereg #(.W(32)) u_nfc_seq (
        .clk(clk), .rst_n(sub_rst_n),
        .en(fg && (sid == S_NFC[11:5]) && (cnt2 == 5'd1) && nfc_frame_rdy && (nfc_seq > nfc_last_seq_q) && !macdiff && !cmp_ne),
        .d(nfc_seq), .q(nfc_last_seq_q)
    );

    wire ctmp_en = fg && ((sid == S_KLN[11:5]) || (sid == S_AR1[11:5]) ||
                          (sid == S_CA2[11:5] && anyv && !(hwm_valid && cur < hwm) && !(port[31:0] < cur || port[31:0] == 32'hFFFF_FFFF)));
    wire [31:0] ctmp_d = (sid == S_KLN[11:5]) ? 32'd0 : (sid == S_AR1[11:5]) ? an_rx[31:0] : (port[31:0] + 32'd1);
    qsag_ereg #(.W(32)) u_ctmp (.clk(clk), .rst_n(sub_rst_n), .en(ctmp_en), .d(ctmp_d), .q(ctmp));

    wire cur_en = fg && ((sid == S_CA0[11:5]) || (sid == S_CA1[11:5] && rcmp && (!v0 || ctmp >= cur)));
    qsag_ereg #(.W(32)) u_cur (.clk(clk), .rst_n(sub_rst_n), .en(cur_en), .d(ctmp), .q(cur));

    wire hwm_en = fg && ((sid == S_KLF[11:5] && rcmp && aslot) || (sid == S_CA3[11:5] && rcmp));
    wire [31:0] hwm_d = (sid == S_CA3[11:5]) ? ctmp : 32'd0;
    qsag_ereg #(.W(32)) u_hwm (.clk(clk), .rst_n(sub_rst_n), .en(hwm_en), .d(hwm_d), .q(hwm));

    wire hvf_pidx0 = (cnt2 == {2'd0, vm_limbs});
    wire hvf_pidx1 = (cnt2 == {2'd0, vm_limbs} + 5'd1);
    wire yh0_en  = fg && (sid == S_HVF[11:5]) &&
                   (cnt2 == 5'd0 || cnt2 == 5'd2 || (fp5_vm && cnt2 == 5'd4) ||
                    (vm_pin_mode && verdict && (hvf_pidx0 || hvf_pidx1)));
    wire yh0_xor = (sid == S_HVF[11:5]) && (cnt2 == 5'd2 || (fp5_vm && cnt2 == 5'd4) || hvf_pidx1);
    qsag_ereg_nr #(.W(64)) u_yh0 (
        .clk(clk), .en(yh0_en),
        .d(yh0_xor ? (y_hold0 ^ port) : port), .q(y_hold0)
    );

    // ------------------------------------------------------------------ Non-secret datapath registers
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wrem          <= '0;
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
            hs_n          <= '0;
            hs_k          <= '0;
            hs_idx        <= '0;
            hs_first      <= 1'b0;
            hs_ph         <= 1'b0;
            hs_rate6      <= 1'b0;
            hs_pad_done   <= 1'b0;
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
            has_assert_q  <= 1'b0;
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
            widx          <= '0;
            sh            <= '0;
            dfa_ok_q      <= 2'b00;
            chk_cont      <= 1'b0;
            puf_recon_mode <= 1'b0;
            puf_margin     <= 6'd4;
            puf_flips_q    <= 3'd0;
            puf_blk        <= '0;
            puf_any_err    <= 1'b0;
        end else if (reg_alive) begin
            if (in_pop) wrem <= wrem - 21'd1;
            if (in_pop && inrec) dleft <= dleft - 16'd1;
            if (fire) begin
                unique case (sid)
                    S_IDLE[11:5]: begin
                        wrem         <= in_data[47:27] + {20'd0, |in_data[26:24]};
                        rerr         <= 1'b0;
                        rok          <= 1'b1;
                        rcode        <= idle_err;
                        rlen         <= idle_rlen;
                        cnt          <= '0;
                        cnt2         <= '0;
                        wi           <= '0;
                        partial      <= 1'b0;
                        fail         <= 1'b0;
                        fset         <= 1'b0;
                        noncanon     <= 1'b0;
                        has_assert_q <= 1'b0;
                        recidx       <= '0;
                        fidx         <= '0;
                        inrec        <= 1'b0;
                        hs_k         <= '0;
                        hs_rate6     <= 1'b0;
                        hs_pad_done  <= 1'b0;
                        gfdone       <= 1'b0;
                        macdiff      <= 1'b0;
                        idx_armed    <= 1'b0;
                        chk_cont     <= 1'b0;
                        dfa_ok_q     <= 2'b00;
                        if (in_data[7:0] == 8'h51 && idle_err == 16'd0) begin
                            if (in_data[15:8] == OP_P2 && !in_data[16]) begin
                                hs_rate6    <= in_data[17];
                                hs_pad_done <= 1'b0;
                                hs_n        <= in_data[17] ? in_data[42:27] : (in_data[42:27] - 16'd5);
                                hs_capsrc   <= 2'd0;
                                hs_latch    <= 3'd0;
                                hs_skip     <= 2'd0;
                            end
                            if (in_data[15:8] == OP_PUF) begin
                                puf_recon_mode <= in_data[16];
                                puf_margin     <= (in_data[53:48] == 6'd0) ? 6'd4 : in_data[53:48];
                                puf_flips_q    <= in_data[56:54];
                                puf_blk        <= 3'd0;
                                puf_any_err    <= 1'b0;
                                dleft[7:0]     <= 8'd0;
                            end
                        end
                    end
                    S_DRAIN[11:5]: if (wrem == 21'd0) begin
                        rerr <= 1'b1;
                        rok  <= 1'b0;
                        rlen <= '0;
                    end
                    S_HDR[11:5]:  cnt2 <= '0;
                    S_OUTL[11:5]: cnt2 <= cnt2 + 5'd1;
                    S_PING[11:5]: cnt2 <= cnt2 + 5'd1;
                    S_BSW[11:5]:  cnt2 <= '0;
                    S_BS0[11:5]: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd2) begin
                            cnt2  <= '0;
                            bmode <= 4'd1;
                        end
                    end
                    S_BS2[11:5]: begin
                        verdict <= (e_wd == BIST_GOLDEN_KAT);
                        rok     <= (e_wd == BIST_GOLDEN_KAT);
                        rlen    <= 24'd8;
                    end
                    S_P2R[11:5]: cnt2 <= cnt2 + 5'd1;
                    S_P2RP[11:5]: begin
                        rlen  <= 24'd96;
                        obase <= 6'd0;
                        olim  <= 5'd12;
                    end
                    S_HSZ[11:5]: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == (hs_rate6 ? 5'd11 : 5'd7)) begin
                            cnt2     <= '0;
                            gfdone   <= 1'b0;
                            hs_idx   <= 4'd0;
                            hs_first <= 1'b1;
                            hs_ph    <= 1'b0;
                        end
                    end
                    S_HSD[11:5]: begin
                        if (bindw) gfdone <= 1'b1;
                        else begin
                            gfdone <= 1'b0;
                            if (hs_k != 16'd0) hs_k <= hs_k - 16'd1;
                        end
                    end
                    S_HSC[11:5]: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (hs_capsrc == 2'd1 || cnt2 == 5'd3) cnt2 <= '0;
                    end
                    S_HSN[11:5]: begin
                        hs_idx   <= 4'd2;
                        hs_first <= 1'b1;
                        hs_ph    <= 1'b0;
                    end
                    S_HSL[11:5]: begin
                        if (hs_n == 16'd0) begin
                            if (hs_rate6 && !hs_pad_done) hs_pad_done <= 1'b1;
                        end else if (bindw) begin
                            gfdone <= 1'b1;
                        end else if (hs_lat_now) begin
                            hs_ph <= 1'b1;
                        end else begin
                            if (hs_k == 16'd0 && in_ge_p && (op != OP_P2)) noncanon <= 1'b1;
                            gfdone <= 1'b0;
                            hs_ph  <= 1'b0;
                            if (hs_k != 16'd0) hs_k <= hs_k - 16'd1;
                            hs_n   <= hs_n - 16'd1;
                            hs_idx <= hs_idx + 4'd1;
                        end
                    end
                    S_HSP[11:5]: begin
                        hs_first <= 1'b0;
                        hs_idx   <= '0;
                    end
                    S_HSF[11:5]: begin
                        rlen  <= (op == OP_P2 && hs_rate6) ? 24'd48 : 24'd32;
                        obase <= 6'd0;
                        olim  <= (op == OP_P2 && hs_rate6) ? 5'd6  : 5'd4;
                    end
                    S_MK5[11:5]: begin
                        midx <= {1'b0, midx[32:1]};
                        cnt  <= cnt - 16'd1;
                        cnt2 <= '0;
                    end
                    S_MPS[11:5]: if (cnt != 16'd0) begin
                        if (in_ge_p) noncanon <= 1'b1;
                        cnt2 <= cnt2 + 5'd1;
                    end
                    S_MOK[11:5]: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd2) cnt2 <= '0;
                    end
                    S_MOI[11:5]: begin
                        midx  <= mk_top_bit | {1'b0, in_data[31:0]};
                        lidx  <= in_data[31:0];
                        mk_kb <= 6'd16;
                    end
                    S_MOL[11:5]: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd3) begin
                            cnt2 <= '0;
                            cnt  <= {10'd0, arg[5:0]};
                        end
                    end
                    S_MOR[11:5]: cnt2 <= cnt2 + 5'd1;
                    S_MOE[11:5]: begin
                        verdict <= fe_eq;
                        rok     <= fe_eq;
                        rlen    <= 24'd40;
                    end
                    S_MOV[11:5]: begin
                        cnt2  <= '0;
                        obase <= 6'd32;
                        olim  <= 5'd4;
                    end
                    S_KSW[11:5]: begin
                        cnt2    <= '0;
                        wi      <= '0;
                        gfdone  <= 1'b0;
                        if (op == OP_PRFMSG) begin
                            if (!key_valid) rcode <= E_NOKEY;
                            else if (cap_mode && macdiff) rcode <= E_MAC;
                            else if (cap_mode && !vat_inv_ok) rcode <= E_CAP;
                        end
                    end
                    S_KSK[11:5]: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd1) wi <= 5'd2;
                    end
                    S_KSA[11:5]: begin
                        if (prf_legacy_tag && (ksa_has_msg || ksa_is_part) && !gfdone) begin
                            gfdone <= 1'b1;
                        end else begin
                            gfdone <= 1'b0;
                            if (ksa_is_part) begin
                                partial <= 1'b1;
                            end else if (ksa_has_msg) begin
                                if (wi == 5'd16) begin
                                    wi      <= '0;
                                end else wi <= wi + 5'd1;
                            end
                        end
                    end
                    S_KSQ[11:5]: begin
                        cnt  <= (op == OP_KECCAK) ? {8'd0, arg[15:8]} : 16'd2;
                        rlen <= (op == OP_KECCAK) ? {13'd0, arg[15:8], 3'd0} : 24'd16;
                        wi   <= '0;
                        cnt2 <= '0;
                    end
                    S_PFT[11:5]: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd2) begin
                            cnt2  <= '0;
                            bmode <= 4'd2;
                        end
                    end
                    S_KSO[11:5]: if (cnt != 16'd0) begin
                        cnt <= cnt - 16'd1;
                        if (wi == 5'd16 && cnt != 16'd1) wi <= '0;
                        else wi <= wi + 5'd1;
                    end
                    S_KLM[11:5]: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd1) begin
                            cnt2 <= '0;
                            if (!flags[0] && !trng_ok) rcode <= E_TRNG;
                        end
                    end
                    S_KLH[11:5]: cnt2 <= cnt2 + 5'd1;
                    S_KLW[11:5]: wi   <= '0;
                    S_KLT[11:5]: wi   <= wi + 5'd1;
                    S_KLA[11:5]: if (wrem != 21'd0 && wi != 5'd15) wi <= wi + 5'd1;
                    S_KLP[11:5]: cnt2 <= '0;
                    S_KLK[11:5]: cnt2 <= cnt2 + 5'd1;
                    S_KLN[11:5]: begin
                        aslot <= 1'b0;
                        if (flags[1]) begin
                            bmode <= 4'd1;
                            cnt2  <= '0;
                        end
                    end
                    S_KLF[11:5]: begin
                        if (!rcmp) rcode <= E_ANCHOR_IO;
                        else if (!aslot) begin
                            aslot <= 1'b1;
                            bmode <= 4'd1;
                            cnt2  <= '0;
                        end
                    end
                    S_BLD[11:5]: cnt2 <= cnt2 + 5'd1;
                    S_BKC[11:5]: begin
                        cnt2 <= '0;
                        if (bmode == 4'd0) begin
                            if (!isprf) cnt <= cnt + 16'd1;
                            isprf <= 1'b0;
                        end
                    end
                    S_AR1[11:5]: begin
                        hi0   <= (an_rx[63:32] == 32'd0);
                        bmode <= 4'd1;
                        cnt2  <= '0;
                    end
                    S_AR3[11:5]: rcmp <= !cmp_ne && hi0;
                    S_AR4[11:5]: rcmp <= rcmp && !cmp_ne;
                    S_AW7[11:5]: rcmp <= !cmp_ne;
                    S_AW8[11:5], S_AW9[11:5]: rcmp <= rcmp && !cmp_ne;
                    S_CTG[11:5]: cnt2 <= '0;
                    S_CTL[11:5]: begin
                        if (cnt2 == 5'd4) is_fors <= (in_data[31:24] == 8'd3);
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd7) begin
                            cnt2 <= '0;
                            if (cap_mode && vat_need_nfc) bmode <= 4'd8;
                            else if (!cap_mode)           bmode <= 4'd2;
                        end
                    end
                    S_CTT[11:5]: begin
                        if (cmp_ne) macdiff <= 1'b1;
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd1 && op == OP_PRFMSG) begin
                            cnt2 <= '0;
                            if (macdiff || cmp_ne) begin
                                rerr  <= 1'b1;
                                rok   <= 1'b0;
                                rlen  <= '0;
                                rcode <= E_MAC;
                            end else begin
                                obase <= 6'd38;
                                olim  <= 5'd2;
                                rlen  <= 24'd16;
                            end
                        end
                    end
                    S_CTD[11:5]: begin
                        cnt2 <= '0;
                        if (!key_valid) rcode <= E_NOKEY;
                        else if (macdiff) rcode <= E_MAC;
                        else if (cth_pub_illegal) rcode <= E_LEN;
                        else if (cap_mode && !vat_inv_ok) rcode <= E_CAP;
                        else if (stateful && !pubgen) aslot <= 1'b0;
                        else begin
                            rlen       <= {12'd0, nch, 4'd0};
                            dleft[7:0] <= 8'd0;
                            widx       <= '0;
                            sh         <= '0;
                        end
                    end
                    S_CA0[11:5]: begin
                        v0    <= rcmp;
                        aslot <= 1'b1;
                    end
                    S_CA1[11:5]: begin
                        anyv  <= v0 | rcmp;
                        older <= !(rcmp && (!v0 || ctmp >= cur));
                    end
                    S_CA2[11:5]: begin
                        if (!anyv) rcode <= E_ANCHOR_EMPTY;
                        else if (hwm_valid && cur < hwm) rcode <= E_ROLLBACK;
                        else if (port[31:0] < cur || port[31:0] == 32'hFFFF_FFFF) rcode <= E_REUSE;
                        else begin
                            aslot <= older;
                            bmode <= 4'd1;
                            cnt2  <= '0;
                        end
                    end
                    S_CA3[11:5]: begin
                        if (!rcmp) rcode <= E_ANCHOR_IO;
                        else begin
                            rlen       <= {12'd0, nch, 4'd0};
                            dleft[7:0] <= 8'd0;
                            widx       <= '0;
                            sh         <= '0;
                        end
                    end
                    S_CTS[11:5]: if (ci != nch) begin
                        hs_n     <= port_sh16 & symmask;
                        chk_cont <= 1'b0;
                        if (sh + {2'd0, sw} + {2'd0, sw} > 7'd64) begin
                            sh   <= '0;
                            widx <= widx + 2'd1;
                        end else sh <= sh + {2'd0, sw};
                        cnt   <= '0;
                        isprf <= 1'b1;
                        bmode <= 4'd0;
                        cnt2  <= '0;
                    end
                    S_CM1[11:5]: cnt2 <= '0;
                    S_CKD[11:5]: cnt2 <= '0;
                    S_CY0[11:5]: dfa_ok_q <= 2'b01; // armed complementary canary!
                    S_CY1[11:5]: begin
                        chk_cont <= 1'b1;
                        bmode    <= 4'd0;
                        cnt2     <= '0;
                    end
                    S_CZ0[11:5]: dfa_ok_q <= ((dfa_ok_q == 2'b01) && cmp_eq) ? 2'b10 : 2'b00;
                    S_CZ1[11:5]: begin
                        if ((dfa_ok_q != 2'b10) || cmp_ne) dfa_ok_q <= 2'b00;
                        cnt2 <= '0;
                    end
                    S_CO[11:5]: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd1) dleft[7:0] <= dleft[7:0] + 8'd1;
                    end
                    S_PF2[11:5]: begin
                        if (puf_blk_err) puf_any_err <= 1'b1;
                        dleft[7:0] <= dleft[7:0] + {4'd0, puf_corrected};
                    end
                    S_PF3[11:5]: begin
                        cnt2  <= '0;
                        bmode <= 4'd5;
                        if (puf_blk != 3'd7) puf_blk <= puf_blk + 3'd1;
                    end
                    S_PF4[11:5]: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd9) begin
                            cnt2  <= '0;
                            bmode <= 4'd6;
                        end
                    end
                    S_PF5[11:5]: begin
                        if (puf_recon_mode && cnt2 <= 5'd3 && cmp_ne)
                            macdiff <= 1'b1;
                        if (puf_recon_mode && cnt2 == 5'd3 && (puf_any_err || macdiff || cmp_ne)) begin
                            rerr  <= 1'b1;
                            rok   <= 1'b0;
                            rlen  <= '0;
                            rcode <= E_PUF;
                        end else if (puf_recon_mode && cnt2 == 5'd14) begin
                            rlen <= 24'd8;
                            rok  <= 1'b1;
                        end
                        cnt2 <= cnt2 + 5'd1;
                    end
                    S_VLD[11:5]: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd7) begin
                            cnt2  <= '0;
                            bmode <= 4'd4;
                        end
                    end
                    S_VTG[11:5]: begin
                        if (cmp_ne) macdiff <= 1'b1;
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd3) begin
                            cnt2 <= '0;
                            if (macdiff || cmp_ne) rcode <= E_MAC;
                            else if (vat_need_nfc && (op == OP_PRFMSG || op == OP_VAT_ZK)) bmode <= 4'd8;
                        end
                    end
                    S_NFC[11:5]: begin
                        if (cmp_ne) macdiff <= 1'b1;
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd1) begin
                            cnt2 <= '0;
                            if (!nfc_frame_rdy || (nfc_seq <= nfc_last_seq_q)) rcode <= E_CAP;
                            else if (macdiff || cmp_ne)                        rcode <= E_MAC;
                        end
                    end
                    S_VAT[11:5]: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd7) begin
                            cnt2  <= '0;
                            bmode <= 4'd4;
                            if (!vat_att_step_ok) rcode <= E_CAP;
                        end
                    end
                    S_VOT[11:5]: cnt2 <= cnt2 + 5'd1;
                    S_VZK[11:5]: begin
                        if (!vat_inv_ok) rcode <= E_CAP;
                        else begin
                            cnt2  <= '0;
                            bmode <= 4'd7;
                            obase <= 6'd0;
                            olim  <= 5'd4; // Locked to 4 words (256-bit grant; never leaks capacity!)
                        end
                    end
                    S_DB0[11:5], S_DBO[11:5]: cnt2 <= cnt2 + 5'd1;
                    S_HVR[11:5]: begin
                        if (wrem == 21'd0) begin
                            verdict <= !fail && !noncanon && has_assert_q && (recidx != 16'd0);
                            cnt2    <= '0;
                        end else begin
                            hop    <= in_data[3:0] | {4{|in_data[7:4]}};
                            ha     <= in_data[13:8];
                            hb     <= in_data[18:16];
                            hc     <= in_data[30:24];
                            dleft  <= in_data[47:32];
                            hs_k   <= in_data[63:48];
                            recidx <= recidx + 16'd1;
                            inrec  <= 1'b1;
                            gfdone <= 1'b0;
                        end
                    end
                    S_HVD[11:5]: begin
                        cnt2 <= '0;
                        unique case (hop)
                            4'd1: begin
                                hs_rate6    <= hc[6];
                                hs_pad_done <= 1'b0;
                                if (hc[6]) begin
                                    hs_n      <= dleft;
                                    hs_capsrc <= 2'd0;
                                    hs_latch  <= hc[2:0];
                                    hs_skip   <= hc[5:4];
                                end else if (dleft == 16'd0) begin
                                    fail <= 1'b1;
                                end else begin
                                    hs_n      <= dleft - 16'd1;
                                    hs_capsrc <= hc[3] ? 2'd2 : 2'd1;
                                    hs_capreg <= hb[2:0];
                                    hs_latch  <= hc[2:0];
                                    hs_skip   <= hc[5:4];
                                end
                            end
                            4'd2, 4'd3, 4'd4, 4'd9: ;
                            4'd5: begin
                                if (dleft != {13'd0, vm_limbs} || (vm_pin_mode && ha[2:0] == 3'd1))
                                    fail <= 1'b1;
                            end
                            4'd6, 4'd7: has_assert_q <= 1'b1;
                            4'd8: begin
                                has_assert_q <= 1'b1;
                                if (ha[5:0] == 6'd0 || ha[5:0] > 6'd32 ||
                                    dleft != 16'd1 + {8'd0, ha[5:0], 2'd0}) fail <= 1'b1;
                            end
                            default: fail <= 1'b1;
                        endcase
                    end
                    S_HVL[11:5]: begin
                        if (bindw) gfdone <= 1'b1;
                        else begin
                            if (hs_k == 16'd0 && in_ge_p) noncanon <= 1'b1;
                            gfdone <= 1'b0;
                            if (hs_k != 16'd0) hs_k <= hs_k - 16'd1;
                            cnt2 <= cnt2 + 5'd1;
                        end
                    end
                    S_HVE[11:5]: if (!fe_eq) fail <= 1'b1;
                    S_HVQ[11:5]: if (res_masked != 32'd0) fail <= 1'b1;
                    S_HVM[11:5]: begin
                        if (idx_armed && (in_data[31:0] != lidx || |in_data[63:32])) fail <= 1'b1;
                        idx_armed <= 1'b0;
                        midx      <= mk_top_bit | {1'b0, in_data[31:0]};
                        mk_kb     <= rb_vm(fp5_vm, hb[2:0]);
                        cnt       <= {10'd0, ha[5:0]};
                        cnt2      <= '0;
                    end
                    S_HVJ[11:5]: begin
                        lidx      <= res_masked;
                        idx_armed <= 1'b1;
                    end
                    S_HVN[11:5]: if (dleft == 16'd0) begin
                        inrec <= 1'b0;
                        hs_k  <= '0;
                        if (fail && !fset) begin
                            fset <= 1'b1;
                            fidx <= recidx;
                        end
                    end
                    S_HVF[11:5]: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == hvf_last) begin
                            cnt2  <= '0;
                            bmode <= 4'd3;
                            rok   <= verdict;
                            rlen  <= fp5_vm ? 24'd80 : 24'd72;
                        end
                    end
                    S_HVS[11:5]: begin
                        cnt2  <= '0;
                        obase <= 6'd0;
                        olim  <= 5'd4;
                    end
                    S_HVC[11:5]: begin
                        cnt2  <= '0;
                        obase <= 6'd32;
                        olim  <= {2'd0, vm_limbs};
                    end
                    default: ;
                endcase
            end
        end
    end

    /* verilator lint_off UNUSEDSIGNAL */
    wire unused = &{1'b0, vat_att_ok, mul_busy, gf_busy, vat_spend_used[31:16], res[63:32], psh2[19], S_KSB};
    /* verilator lint_on UNUSEDSIGNAL */
endmodule
`default_nettype wire

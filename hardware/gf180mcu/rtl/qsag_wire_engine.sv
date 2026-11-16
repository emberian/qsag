// QSAG-NI-180 core: QSAG-Wire v1 packet engine, transcript-exact verifier VM and
// Cut-the-Hash enclave, around one shared register file and one arithmetic unit.
//
// Stream format (64-bit little-endian words on both directions):
//   request  = header, ceil(len / 8) payload words
//   header   = [7:0] 0x51, [15:8] opcode, [23:16] flags, [47:24] payload length in bytes,
//              [63:48] arg
//   response = header (opcode | 0x80, flags = status: bit 7 error, bit 0 ok/verified,
//              arg = error code), payload words
// See README.md for the per-opcode payloads.
`default_nettype none

module qsag_wire_engine #(
    parameter int GF_D = 2
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
    // telemetry / configuration
    input  wire  [63:0] tel0,
    input  wire  [31:0] tel1,
    output logic [63:0] csr,
    // status
    output logic        verify_ok,
    output wire         key_valid_o,
    output logic        fault_anchor,
    output logic        fault_mac,
    output logic        fault_control,
    output wire         busy
);
    // ------------------------------------------------------------------ opcodes
    localparam logic [7:0] OP_PING = 8'h01, OP_CSR = 8'h02, OP_P2 = 8'h10, OP_MERKLE = 8'h11,
                           OP_KECCAK = 8'h20, OP_FOLD = 8'h30, OP_HEM = 8'h31,
                           OP_KEYLOAD = 8'h40, OP_CTH = 8'h41, OP_PRFMSG = 8'h42;
    localparam logic [15:0] E_MAGIC = 16'd1, E_OPCODE = 16'd2, E_LEN = 16'd3, E_NOKEY = 16'd4,
                            E_MAC = 16'd5, E_ANCHOR_EMPTY = 16'd6, E_ROLLBACK = 16'd7,
                            E_REUSE = 16'd8, E_ANCHOR_IO = 16'd9, E_KEYSET = 16'd10,
                            E_TRNG = 16'd11;
    localparam logic [63:0] CHIP_ID   = 64'h3831_494E_4741_5351;  // "QSAGNI18"
    localparam logic [63:0] C_FRAM    = 64'h5246_494E_4741_5351;  // "QSAGNIFR"
    localparam logic [63:0] C_MASK    = 64'h4B4D_494E_4741_5351;  // "QSAGNIMK"
    localparam logic [63:0] NODE_HI   = 64'h5032_4E44_0000_0000;
    localparam logic [63:0] FS_INIT   = 64'h5032_4653_494E_4954;
    localparam logic [63:0] P2_IV     = 64'h504F_5332_5F47_4C31;
    localparam logic [63:0] PAD_END   = 64'h8000_0000_0000_0000;

    // field-engine operations
    localparam logic [3:0] F_PERM = 4'd1, F_ABSW = 4'd2, F_SETW = 4'd3, F_MOV = 4'd4, F_EMUL = 4'd5,
                           F_EADD = 4'd6, F_ESUB = 4'd7, F_EEQ = 4'd8, F_FFWD = 4'd9, F_LDRES = 4'd10;

    // ------------------------------------------------------------------ states
    localparam logic [11:0]
        S_IDLE = 12'h000,   S_DRAIN = 12'h027,  S_EHDR = 12'h04b,   S_HDR = 12'h06c,    S_OUTL = 12'h08d,
        S_WIPE = 12'h0aa,   S_DEAD = 12'h0c6,   S_PING = 12'h0e1,   S_CSR = 12'h10e,
        S_P2R = 12'h129,    S_P2RP = 12'h145,
        S_HSZ = 12'h162,   S_HSD = 12'h183,   S_HSC = 12'h1a4,   S_HSN = 12'h1c8,   S_HSL = 12'h1ef,
        S_HSP = 12'h213,   S_HSF = 12'h234,
        S_MK0 = 12'h258,   S_MK1 = 12'h27f,   S_MK2 = 12'h29e,   S_MK3 = 12'h2b9,   S_MK4 = 12'h2d5,
        S_MK5 = 12'h2f2,   S_MPS = 12'h31d,
        S_MOK = 12'h33a,   S_MOI = 12'h356,   S_MOL = 12'h371,   S_MOR = 12'h390,   S_MOE = 12'h3b7,
        S_MOV = 12'h3db,
        S_KSW = 12'h3fc,   S_KSK = 12'h415,   S_KSA = 12'h432,   S_KSP = 12'h45e,   S_KSD = 12'h479,
        S_KSE = 12'h498,   S_KSQ = 12'h4bf,   S_KSO = 12'h4d3,   S_KSR = 12'h4f4,
        S_KLM = 12'h51b,   S_KLH = 12'h53c,   S_KLW = 12'h550,   S_KLT = 12'h577,   S_KLA = 12'h596,
        S_KLD = 12'h5b1,   S_KLE = 12'h5dd,   S_KLP = 12'h5fa,   S_KLK = 12'h606,   S_KLZ = 12'h621,
        S_KLN = 12'h64d,   S_KLF = 12'h66a,
        S_BLD = 12'h68b,   S_BKC = 12'h6ac,
        S_AR0 = 12'h6c0,   S_AR1 = 12'h6e7,   S_AR2 = 12'h708,   S_AR3 = 12'h72f,   S_AR4 = 12'h743,
        S_AR5 = 12'h764,
        S_AW1 = 12'h785,   S_AW2 = 12'h7a2,   S_AW3 = 12'h7ce,   S_AW4 = 12'h7e9,   S_AW5 = 12'h816,
        S_AW6 = 12'h831,   S_AW7 = 12'h85d,   S_AW8 = 12'h87a,   S_AW9 = 12'h89b,   S_AWA = 12'h8bc,
        S_CTG = 12'h8d0,   S_CTL = 12'h8f7,   S_CTT = 12'h918,   S_CTD = 12'h93f,   S_CA0 = 12'h953,
        S_CA1 = 12'h974,   S_CA2 = 12'h995,   S_CA3 = 12'h9b2,   S_CTS = 12'h9de,   S_CM0 = 12'h9f9,
        S_CM1 = 12'ha05,   S_CKD = 12'ha22,   S_CO = 12'ha4e,
        S_HVG = 12'ha69,   S_HVR = 12'ha88,   S_HVD = 12'haaf,   S_HVH = 12'hac3,   S_HVA = 12'hae4,
        S_HVL = 12'hb0b,   S_HVE = 12'hb2c,   S_HVP = 12'hb40,   S_HVQ = 12'hb67,   S_HVM = 12'hb86,
        S_HVI = 12'hba1,   S_HVJ = 12'hbcd,   S_HVN = 12'hbea,   S_HVF = 12'hc03,   S_HVS = 12'hc24,
        S_HVC = 12'hc48;

    // step kinds
    localparam logic [2:0] K_NONE = 3'd0, K_FE = 3'd1, K_KC = 3'd2, K_GF = 3'd3;

    // Shortened extended Hamming code: seven data bits, four syndrome bits,
    // overall parity. All valid states have pairwise distance >= 4.
    // Prevent Yosys from recoding the state to an unprotected binary/one-hot FSM.
    (* fsm_encoding = "none", keep *) logic [11:0] st, ret, ret2, ret3;
    function automatic logic code_ok(input logic [11:0] c);
        logic [3:0] p;
        begin
            p = ({4{c[5]}} & 4'd3) ^ ({4{c[6]}} & 4'd5)
              ^ ({4{c[7]}} & 4'd6) ^ ({4{c[8]}} & 4'd7)
              ^ ({4{c[9]}} & 4'd9) ^ ({4{c[10]}} & 4'd10)
              ^ ({4{c[11]}} & 4'd11);
            code_ok = (p == c[4:1]) && !(^c) && (c[11:5] < 7'd99);
        end
    endfunction
    wire control_bad = !code_ok(st) || !code_ok(ret) || !code_ok(ret2) || !code_ok(ret3);
    // Sample the detector: combinational decode hazards during normal multi-bit
    // state changes must never drive the asynchronous secret reset directly.
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) fault_control <= 1'b0;
        else if (control_bad) fault_control <= 1'b1;
    wire secret_rst_n = srst_n & ~fault_control;
    wire permit_control = !control_bad && !fault_control;

    logic        w;                  // blocking sub-operation launched
    // request header
    logic [7:0]  op, flags;
    logic [15:0] arg;
    logic [20:0] wrem;               // payload words left to consume
    logic [2:0]  lenb;               // payload length mod 8
    // response header
    logic [23:0] rlen;
    logic [15:0] rcode;
    logic        rerr, rok;
    // counters
    logic [15:0] cnt;
    logic [4:0]  cnt2;
    logic [4:0]  wi;
    logic [5:0]  obase;
    logic [4:0]  olim;
    logic        partial;
    // Poseidon2 sponge hash
    logic [15:0] hs_n, hs_k;
    logic [3:0]  hs_idx;
    logic        hs_first, hs_ph, gfdone;
    logic [1:0]  hs_capsrc;
    logic [2:0]  hs_capreg, hs_latch;
    logic [1:0]  hs_skip;            // limbs after the latched element
    logic        idx_armed;          // a squeezed query index awaits its Merkle record
    // Merkle
    logic [32:0] midx;
    logic [31:0] lidx;
    logic [5:0]  mk_kb;
    // verifier VM
    logic [3:0]  hop;
    logic [7:0]  ha, hb, hc;
    logic [15:0] dleft, recidx, fidx;
    logic        inrec, fail, fset, noncanon, verdict;
    // keys and enclave
    wire  [63:0] key [6];            // 0,1 SK.seed  2,3 SK.prf  4,5 MAC key
    logic        key_valid;
    logic [31:0] cur, hwm, ctmp;
    logic        hwm_valid, v0, anyv, older, aslot, rcmp, hi0, macdiff, is_fors, isprf;
    logic [1:0]  bmode;
    logic [7:0]  ci;
    logic [1:0]  widx;
    logic [6:0]  sh;
    logic [15:0] sym, steps;
    logic [15:0] hj;

    assign busy        = (st != S_IDLE);
    assign key_valid_o = key_valid;

    // ------------------------------------------------------------------ datapath instances
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

    logic zeroize_q;
    wire  sub_rst_n = rst_n & ~zeroize_q & ~fault_control;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) zeroize_q <= 1'b0;
        else zeroize_q <= zeroize;

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
        .busy(kc_busy), .done(kc_done), .rd_addr(kc_rd), .port(port),
        .wr_en(kc_we), .wr_addr(kc_wa), .wr_data(kc_wd)
    );
    qsag_sponge u_sp (
        .clk(clk), .wipe(sp_wipe | zeroize_q | fault_control),
        .wr_en(fe_busy ? fe_we : kc_busy ? kc_we : e_we),
        .wr_addr(fe_busy ? fe_wa : kc_busy ? kc_wa : e_wa),
        .wr_data(fe_busy ? cv : kc_busy ? kc_wd : e_wd),
        .rd_addr(fe_busy ? fe_rd : kc_busy ? kc_rd : e_rd),
        .rd_data(port)
    );
    qsag_gf128_clmul #(.D(GF_D)) u_gf (
        .clk(clk), .rst_n(sub_rst_n), .srst_n(secret_rst_n), .clr(gf_clr), .start(gf_start),
        .in({64'd0, xw}), .h({key[5], key[4]}), .busy(gf_busy), .done(gf_done), .acc(gf_acc)
    );

    // key registers (asynchronous clear on reset, tamper and glitch)
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

    wire        in_ge_p  = (&in_data[63:32]) && (|in_data[31:0]);
    wire [63:0] hdr_word = {arg, wrem[20:0], lenb, flags, op, 8'h51};
    wire [63:0] t0_word  = NODE_HI | {32'd0, midx[32:1]};
    wire        pubgen   = flags[0];
    wire        stateful = flags[1];
    wire [7:0]  nch      = arg[7:0];
    wire [4:0]  sw       = arg[12:8];
    wire [15:0] symmask  = (sw >= 5'd16) ? 16'hFFFF : ((16'd1 << sw) - 16'd1);
    wire [63:0] port_sh  = port >> sh[5:0];
    wire [23:0] fors_idx = (24'(ci) << sw) | 24'(sym);
    wire [23:0] hfield   = is_fors ? fors_idx : (isprf ? 24'd0 : 24'(hj));
    wire [7:0]  cfield   = is_fors ? 8'd0 : ci;
    wire [63:0] a3_word  = {hfield[7:0], hfield[15:8], hfield[23:16], 8'd0, cfield, 24'd0};
    wire [7:0]  type_ov  = is_fors ? (isprf ? 8'd6 : 8'd3) : (isprf ? 8'd5 : 8'd0);
    wire [63:0] stat_word = {8'd0, op, recidx, fidx, 13'd0, key_valid, noncanon, verdict};

    // ------------------------------------------------------------------ control decode
    logic [2:0]  kind;
    logic        cond;       // launch / fire condition
    logic        do_pop;
    logic [2:0]  xsel;       // 0 in, 1 imm, 2 key, 3 gf, 4 anchor, 5 trng, 6 zero
    logic [63:0] imm;
    logic [2:0]  ksel;
    logic        gsel;
    logic [2:0]  wsel;       // raw write data: 0 xw, 1 port^xw, 2 port, 3 a0(port), 4 type(port)
    logic        e_wreq;     // raw write on fire
    logic        e_wlaunch;  // raw write on launch
    logic        emit;       // push out_data on fire
    logic        emit_port;
    wire         cmp_ne;     // comparator: an_rx / in_data against port (^ gf)

    wire sub_done = (kind == K_FE) ? fe_done : (kind == K_KC) ? kc_done : (kind == K_GF) ? gf_done : 1'b0;
    wire launch   = permit_control && (kind != K_NONE) && !w && cond;
    wire fire     = permit_control && ((kind == K_NONE) ? cond : (w && sub_done));
    wire bindw     = (hs_k != 16'd0) && !gfdone;   // immediate word still to be bound
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
        kind      = K_NONE;
        cond      = 1'b1;
        do_pop    = 1'b0;
        xsel      = 3'd6;
        imm       = 64'd0;
        ksel      = 3'd0;
        gsel      = 1'b0;
        wsel      = 3'd0;
        e_wreq    = 1'b0;
        e_wlaunch = 1'b0;
        e_rd      = 6'd0;
        e_wa      = 6'd0;
        emit      = 1'b0;
        emit_port = 1'b0;
        fe_op     = F_PERM;
        fe_d      = 6'd0;
        fe_s1     = 6'd0;
        fe_s2     = 6'd0;
        fe_n      = 3'd0;
        fe_dir    = 1'b0;
        kc_turbo  = 1'b0;
        gf_clr    = 1'b0;
        sp_wipe   = 1'b0;
        an_start  = 1'b0;
        an_write  = 1'b0;
        an_addr   = {10'd0, aslot, 5'd0};
        an_go     = 1'b0;
        trng_take = 1'b0;
        key_we    = 6'd0;
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
            S_KLW: begin  // also discard raw TRNG bits that telemetry may have shown
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
                    2'd2:    imm = {28'd0, hwm_valid, fault_mac, fault_anchor, key_valid, tel1};
                    default: imm = trng_word;
                endcase
            end
            S_CSR: begin
                cond   = in_valid;
                do_pop = 1'b1;
            end
            // ---------------------------------------------------------- Poseidon2 raw permutation
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
            // ---------------------------------------------------------- Poseidon2 sponge hash
            S_HSZ: begin
                kind  = K_FE;
                fe_op = F_SETW;
                fe_d  = {1'b0, cnt2};
                xsel  = 3'd6;
            end
            S_HSD: begin  // domain word
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
            // ---------------------------------------------------------- Canopy node / path
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
            S_MPS: begin  // sibling into Y
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
            // ---------------------------------------------------------- Keccak streaming
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
            S_KSP, S_KSR, S_BKC: begin
                kind     = K_KC;
                kc_turbo = (st == S_BKC) ? (bmode != 2'd0) : (op == OP_KECCAK && flags[0]);
            end
            S_KSD: begin  // domain suffix at the first unused byte
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
                kind = K_KC;
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
                cond   = in_valid;
                do_pop = 1'b1;
                key_we = 6'b000001 << cnt2[1:0];
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
                e_rd   = {1'b0, cnt2};
                key_we = 6'b000001 << cnt2[1:0];
            end
            // ---------------------------------------------------------- keyed block build
            S_BLD: begin
                e_wreq = !(bmode == 2'd0 && !isprf && (cnt2 == 5'd6 || cnt2 == 5'd7));
                e_wa   = {1'b0, cnt2};
                xsel   = 3'd6;
                unique case (bmode)
                    2'd0: begin  // SLH-DSA PRF / F block: PK.seed || ADRS || (SK.seed | x)
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
                    2'd1: begin  // FRAM record MAC: K_MAC || counter || "QSAGNIFR"
                        unique case (cnt2)
                            5'd0, 5'd1: begin xsel = 3'd2; ksel = 3'd4 + {2'd0, cnt2[0]}; end
                            5'd2:       begin xsel = 3'd1; imm = {32'd0, ctmp}; end
                            5'd3:       begin xsel = 3'd1; imm = C_FRAM; end
                            5'd4:       begin xsel = 3'd1; imm = 64'h1F; end
                            5'd16:      begin xsel = 3'd1; imm = PAD_END; end
                            default: ;
                        endcase
                    end
                    2'd2: begin  // request mask: K_MAC || nonce word || "QSAGNIMK"
                        unique case (cnt2)
                            5'd0, 5'd1: begin xsel = 3'd2; ksel = 3'd4 + {2'd0, cnt2[0]}; end
                            5'd2:       begin wsel = 3'd2; e_rd = 6'd32; end
                            5'd3:       begin xsel = 3'd1; imm = C_MASK; end
                            5'd4:       begin xsel = 3'd1; imm = 64'h1F; end
                            5'd16:      begin xsel = 3'd1; imm = PAD_END; end
                            default: ;
                        endcase
                    end
                    default: begin  // receipt: K_MAC || status || program digest || chain
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
                endcase
            end
            // ---------------------------------------------------------- FRAM anchor
            S_AR0, S_AW6: begin
                an_start = 1'b1;
            end
            S_AW1: begin
                an_start = 1'b1;
                an_write = 1'b1;
            end
            S_AR1: cond = an_stb;                       // counter word
            S_AR2: an_go = 1'b1;
            S_AR3, S_AR4, S_AW8, S_AW9: begin           // tag words against lanes 0, 1
                cond   = an_stb;
                an_go  = an_stb;
                e_rd   = {5'd0, (st == S_AR4 || st == S_AW9)};
            end
            S_AW7: begin
                cond   = an_stb;
                an_go  = an_stb;
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
            // ---------------------------------------------------------- Cut-the-Hash signing
            S_CTG, S_HVG: begin
                kind = K_GF;
                xsel = 3'd1;
                imm  = hdr_word;
            end
            S_CTL: begin  // request word into the shadow buffer and the request MAC
                kind      = K_GF;
                cond      = in_valid;
                xsel      = 3'd0;
                e_wlaunch = 1'b1;
                e_wa      = 6'd32 + {1'b0, cnt2};
                do_pop    = 1'b1;
            end
            S_CTT: begin  // tag word against mask ^ polynomial digest
                cond   = in_valid;
                do_pop = 1'b1;
                e_rd   = {5'd0, cnt2[0]};
            end
            S_CA2: e_rd = 6'd32;
            S_CTS: e_rd = 6'd37 + {4'd0, widx};
            S_CM0, S_CM1: begin  // x: lanes 0, 1 -> lanes 6, 7
                e_wreq = 1'b1;
                e_rd   = {5'd0, (st == S_CM1)};
                e_wa   = 6'd6 + {5'd0, (st == S_CM1)};
                wsel   = 3'd2;
            end
            S_CO: begin
                cond      = out_ready;
                emit      = 1'b1;
                emit_port = 1'b1;
                e_rd      = {5'd0, cnt2[0]};
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
            S_HVF: begin  // chain into the shadow buffer for the receipt
                e_wreq = 1'b1;
                e_rd   = 6'd12 + {1'b0, cnt2};
                e_wa   = 6'd32 + {1'b0, cnt2};
                wsel   = 3'd2;
            end
            S_HVS: begin
                cond = out_ready;
                emit = 1'b1;
                imm  = stat_word;
            end
            default: ;
        endcase
        if (emit && !emit_port) xsel = 3'd1;
    end

    // port-dependent outputs are kept out of the control decode (it produces the read address)
    assign key_d  = (st == S_KLK) ? port : in_data;
    assign an_tx  = (st == S_AW2) ? {32'd0, ctmp} : port;
    assign cmp_ne = (st == S_AW7) ? (an_rx != {32'd0, ctmp})
                  : (st == S_CTT) ? (in_data != (port ^ (cnt2[0] ? gf_acc[127:64] : gf_acc[63:0])))
                  : (an_rx != port);
    assign fe_start = launch && (kind == K_FE);
    assign kc_start = launch && (kind == K_KC);
    assign gf_start = launch && (kind == K_GF);
    assign in_pop   = fire && do_pop;
    assign out_push = fire && emit;
    assign out_data = emit_port ? port : imm;
    assign e_we     = (fire && e_wreq) || (launch && e_wlaunch);

    // ------------------------------------------------------------------ sequencing
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            st           <= S_IDLE;
            ret          <= S_IDLE;
            ret2         <= S_IDLE;
            ret3         <= S_IDLE;
            w            <= 1'b0;
            op           <= '0;
            flags        <= '0;
            arg          <= '0;
            wrem         <= '0;
            lenb         <= '0;
            rlen         <= '0;
            rcode        <= '0;
            rerr         <= 1'b0;
            rok          <= 1'b0;
            cnt          <= '0;
            cnt2         <= '0;
            wi           <= '0;
            obase        <= '0;
            olim         <= '0;
            partial      <= 1'b0;
            hs_n         <= '0;
            hs_k         <= '0;
            hs_idx       <= '0;
            hs_first     <= 1'b0;
            hs_ph        <= 1'b0;
            gfdone       <= 1'b0;
            hs_capsrc    <= '0;
            hs_capreg    <= '0;
            hs_latch     <= '0;
            hs_skip      <= '0;
            idx_armed    <= 1'b0;
            midx         <= '0;
            lidx         <= '0;
            mk_kb        <= '0;
            hop          <= '0;
            ha           <= '0;
            hb           <= '0;
            hc           <= '0;
            dleft        <= '0;
            recidx       <= '0;
            fidx         <= '0;
            inrec        <= 1'b0;
            fail         <= 1'b0;
            fset         <= 1'b0;
            noncanon     <= 1'b0;
            verdict      <= 1'b0;
            verify_ok    <= 1'b0;
            key_valid    <= 1'b0;
            cur          <= '0;
            hwm          <= '0;
            ctmp         <= '0;
            hwm_valid    <= 1'b0;
            v0           <= 1'b0;
            anyv         <= 1'b0;
            older        <= 1'b0;
            aslot        <= 1'b0;
            rcmp         <= 1'b0;
            hi0          <= 1'b0;
            macdiff      <= 1'b0;
            is_fors      <= 1'b0;
            isprf        <= 1'b0;
            bmode        <= '0;
            ci           <= '0;
            widx         <= '0;
            sh           <= '0;
            sym          <= '0;
            steps        <= '0;
            hj           <= '0;
            fault_anchor <= 1'b0;
            fault_mac    <= 1'b0;
            csr          <= 64'h0000_0000_0268_C01F;   // see qsag_gals_clk_rst: tap 31, slow slew, TRNG on
        end else if (zeroize_q || control_bad || fault_control) begin
            st        <= S_DEAD;
            w         <= 1'b0;
            key_valid <= 1'b0;
            verify_ok <= 1'b0;
            hwm_valid <= 1'b0;
        end else begin
            if (launch) w <= 1'b1;
            if (in_pop) wrem <= wrem - 21'd1;
            if (in_pop && inrec) dleft <= dleft - 16'd1;
            if (fire) begin
                w <= 1'b0;
                unique case (st)
                    S_IDLE: begin
                        op       <= in_data[15:8];
                        flags    <= in_data[23:16];
                        lenb     <= in_data[26:24];
                        wrem     <= in_data[47:27] + {20'd0, |in_data[26:24]};
                        arg      <= in_data[63:48];
                        rerr     <= 1'b0;
                        rok      <= 1'b1;
                        rcode    <= '0;
                        rlen     <= '0;
                        cnt      <= '0;
                        cnt2     <= '0;
                        wi       <= '0;
                        partial  <= 1'b0;
                        fail     <= 1'b0;
                        fset     <= 1'b0;
                        noncanon <= 1'b0;
                        recidx   <= '0;
                        fidx     <= '0;
                        inrec    <= 1'b0;
                        hs_k     <= '0;
                        gfdone   <= 1'b0;
                        macdiff  <= 1'b0;
                        idx_armed <= 1'b0;
                        ret      <= S_IDLE;
                        if (in_data[7:0] != 8'h51) begin
                            rcode <= E_MAGIC;
                            st    <= S_DRAIN;
                        end else begin
                            unique case (in_data[15:8])
                                OP_PING: begin
                                    rlen <= 24'd32;
                                    ret  <= S_PING;
                                    st   <= (in_data[47:24] == 24'd0) ? S_HDR : S_DRAIN;
                                    if (in_data[47:24] != 24'd0) rcode <= E_LEN;
                                end
                                OP_CSR: begin
                                    st <= (in_data[47:24] == 24'd8) ? S_CSR : S_DRAIN;
                                    if (in_data[47:24] != 24'd8) rcode <= E_LEN;
                                end
                                OP_P2: begin
                                    verify_ok <= 1'b0;
                                    if (in_data[16]) begin  // raw permutation
                                        st <= (in_data[47:24] == 24'd96) ? S_P2R : S_DRAIN;
                                        if (in_data[47:24] != 24'd96) rcode <= E_LEN;
                                    end else if (in_data[47:24] < 24'd40 || in_data[26:24] != 3'd0) begin
                                        rcode <= E_LEN;
                                        st    <= S_DRAIN;
                                    end else begin
                                        hs_n      <= in_data[42:27] - 16'd5;
                                        hs_capsrc <= 2'd0;
                                        hs_latch  <= 3'd0;
                                        hs_skip   <= 2'd0;
                                        ret       <= S_HDR;
                                        st        <= S_HSZ;
                                    end
                                end
                                OP_MERKLE: begin
                                    verify_ok <= 1'b0;
                                    // 3 key + 1 index + 4 leaf + 4*depth siblings + 4 root words
                                    if (in_data[53:48] == 6'd0 || in_data[53:48] > 6'd32 ||
                                        in_data[47:24] != 24'd96 + {16'd0, in_data[53:48], 2'd0} * 24'd8) begin
                                        rcode <= E_LEN;
                                        st    <= S_DRAIN;
                                    end else st <= S_MOK;
                                end
                                OP_KECCAK: st <= S_KSW;
                                OP_PRFMSG: st <= S_KSW;
                                OP_FOLD, OP_HEM: begin
                                    verify_ok <= 1'b0;
                                    if (in_data[26:24] != 3'd0) begin
                                        rcode <= E_LEN;
                                        st    <= S_DRAIN;
                                    end else st <= S_HVG;
                                end
                                OP_KEYLOAD: begin
                                    if (key_valid) begin
                                        rcode <= E_KEYSET;
                                        st    <= S_DRAIN;
                                    end else if (in_data[16] ? (in_data[47:24] != 24'd48)
                                                             : (in_data[47:24] < 24'd16 || in_data[47:24] > 24'd96 ||
                                                                in_data[26:24] != 3'd0)) begin
                                        rcode <= E_LEN;
                                        st    <= S_DRAIN;
                                    end else st <= S_KLM;
                                end
                                OP_CTH: begin
                                    // 8 request words + 2 tag words; symbols fit three words
                                    if (in_data[47:24] != 24'd80 || in_data[60:56] == 5'd0 || in_data[60:56] > 5'd16 ||
                                        in_data[55:48] == 8'd0) begin
                                        rcode <= E_LEN;
                                        st    <= S_DRAIN;
                                    end else st <= S_CTG;
                                end
                                default: begin
                                    rcode <= E_OPCODE;
                                    st    <= S_DRAIN;
                                end
                            endcase
                        end
                    end
                    S_DRAIN: if (wrem == 21'd0) begin
                        rerr <= 1'b1;
                        rok  <= 1'b0;
                        rlen <= '0;
                        st   <= S_EHDR;
                    end
                    S_EHDR: st <= S_WIPE;
                    S_HDR: begin
                        cnt2 <= '0;
                        st   <= ret;
                        if (ret == S_HDR) begin  // lanes obase.. follow the header
                            ret <= S_IDLE;
                            st  <= S_OUTL;
                        end
                    end
                    S_OUTL: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 + 5'd1 == olim) st <= ret;
                    end
                    S_WIPE: st <= S_IDLE;
                    S_PING: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd3) st <= S_IDLE;
                    end
                    S_CSR: begin
                        csr <= in_data;
                        ret <= S_IDLE;
                        st  <= S_HDR;
                    end
                    // ------------------------------------------------ Poseidon2
                    S_P2R: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd11) st <= S_P2RP;
                    end
                    S_P2RP: begin
                        rlen  <= 24'd96;
                        obase <= 6'd0;
                        olim  <= 5'd12;
                        ret   <= S_HDR;
                        st    <= S_HDR;
                    end
                    S_HSZ: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd7) begin
                            cnt2   <= '0;
                            gfdone <= 1'b0;
                            st     <= S_HSD;
                        end
                    end
                    S_HSD: begin
                        if (bindw) gfdone <= 1'b1;
                        else begin
                            gfdone <= 1'b0;
                            if (hs_k != 16'd0) hs_k <= hs_k - 16'd1;
                            st <= S_HSC;
                        end
                    end
                    S_HSC: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (hs_capsrc == 2'd1 || cnt2 == 5'd3) begin
                            cnt2 <= '0;
                            st   <= S_HSN;
                        end
                    end
                    S_HSN: begin
                        hs_idx   <= 4'd2;
                        hs_first <= 1'b1;
                        hs_ph    <= 1'b0;
                        st       <= S_HSL;
                    end
                    S_HSL: begin
                        if (hs_n == 16'd0) st <= S_HSF;
                        else if (bindw) gfdone <= 1'b1;
                        else if (hs_lat_now) hs_ph <= 1'b1;
                        else begin
                            if (hs_k == 16'd0 && in_ge_p && (op != OP_P2)) noncanon <= 1'b1;
                            gfdone <= 1'b0;
                            hs_ph  <= 1'b0;
                            if (hs_k != 16'd0) hs_k <= hs_k - 16'd1;
                            hs_n   <= hs_n - 16'd1;
                            hs_idx <= hs_idx + 4'd1;
                            if (hs_idx == 4'd7) st <= S_HSP;
                        end
                    end
                    S_HSP: begin
                        hs_first <= 1'b0;
                        hs_idx   <= '0;
                        st       <= S_HSL;
                    end
                    S_HSF: begin
                        rlen  <= 24'd32;
                        obase <= 6'd0;
                        olim  <= 5'd4;
                        st    <= ret;
                    end
                    // ------------------------------------------------ Canopy
                    S_MK0: st <= S_MK1;
                    S_MK1: st <= S_MK2;
                    S_MK2: st <= S_MK3;
                    S_MK3: st <= S_MK4;
                    S_MK4: st <= S_MK5;
                    S_MK5: begin
                        midx <= {1'b0, midx[32:1]};
                        cnt  <= cnt - 16'd1;
                        cnt2 <= '0;
                        st   <= S_MPS;
                    end
                    S_MPS: begin
                        if (cnt == 16'd0) st <= ret2;
                        else begin
                            if (in_ge_p) noncanon <= 1'b1;
                            cnt2 <= cnt2 + 5'd1;
                            if (cnt2 == 5'd3) st <= S_MK0;
                        end
                    end
                    S_MOK: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd2) begin
                            cnt2 <= '0;
                            st   <= S_MOI;
                        end
                    end
                    S_MOI: begin
                        midx  <= (33'd1 << arg[5:0]) | {1'b0, in_data[31:0]};
                        lidx  <= in_data[31:0];
                        mk_kb <= 6'd16;
                        st    <= S_MOL;
                    end
                    S_MOL: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd3) begin
                            cnt2 <= '0;
                            cnt  <= {10'd0, arg[5:0]};
                            ret2 <= S_MOR;
                            st   <= S_MPS;
                        end
                    end
                    S_MOR: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd3) st <= S_MOE;
                    end
                    S_MOE: begin
                        verdict   <= fe_eq;
                        verify_ok <= fe_eq;
                        rok       <= fe_eq;
                        rlen      <= 24'd40;
                        ret       <= S_MOV;
                        st        <= S_HDR;
                    end
                    S_MOV: begin
                        cnt2  <= '0;
                        obase <= 6'd32;
                        olim  <= 5'd4;
                        ret   <= S_IDLE;
                        st    <= S_OUTL;
                    end
                    // ------------------------------------------------ Keccak
                    S_KSW: begin
                        cnt2 <= '0;
                        wi   <= '0;
                        if (op == OP_PRFMSG) begin
                            if (!key_valid) begin
                                rcode <= E_NOKEY;
                                st    <= S_DRAIN;
                            end else st <= S_KSK;
                        end else st <= S_KSA;
                    end
                    S_KSK: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd1) begin
                            wi <= 5'd2;
                            st <= S_KSA;
                        end
                    end
                    S_KSA: begin
                        if (wrem == 21'd0) st <= S_KSD;
                        else if (wrem == 21'd1 && lenb != 3'd0) begin
                            partial <= 1'b1;
                            st      <= S_KSD;
                        end else if (wi == 5'd16) begin
                            wi <= '0;
                            st <= S_KSP;
                        end else wi <= wi + 5'd1;
                    end
                    S_KSP: st <= S_KSA;
                    S_KSD: st <= S_KSE;
                    S_KSE: st <= S_KSQ;
                    S_KSQ: begin
                        cnt  <= (op == OP_KECCAK) ? {8'd0, arg[15:8]} : 16'd2;
                        rlen <= (op == OP_KECCAK) ? {13'd0, arg[15:8], 3'd0} : 24'd16;
                        wi   <= '0;
                        ret  <= S_KSO;
                        st   <= S_HDR;
                    end
                    S_KSO: begin
                        if (cnt == 16'd0) st <= S_WIPE;
                        else begin
                            cnt <= cnt - 16'd1;
                            if (wi == 5'd16 && cnt != 16'd1) begin
                                wi <= '0;
                                st <= S_KSR;
                            end else wi <= wi + 5'd1;
                        end
                    end
                    S_KSR: st <= S_KSO;
                    // ------------------------------------------------ key load
                    S_KLM: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd1) begin
                            cnt2 <= '0;
                            if (flags[0]) st <= S_KLH;
                            else if (!trng_ok) begin
                                rcode <= E_TRNG;
                                st    <= S_DRAIN;
                            end else st <= S_KLW;
                        end
                    end
                    S_KLH: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd3) st <= S_KLN;
                    end
                    S_KLW: begin
                        wi <= '0;
                        st <= S_KLT;
                    end
                    S_KLT: begin
                        wi <= wi + 5'd1;
                        if (wi == 5'd3) st <= S_KLA;
                    end
                    S_KLA: begin
                        if (wrem == 21'd0) st <= S_KLD;
                        else if (wi != 5'd15) wi <= wi + 5'd1;
                    end
                    S_KLD: st <= S_KLE;
                    S_KLE: st <= S_KLP;
                    S_KLP: begin
                        cnt2 <= '0;
                        st   <= S_KLK;
                    end
                    S_KLK: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd3) st <= S_KLZ;
                    end
                    S_KLZ: st <= S_KLN;
                    S_KLN: begin  // optional anchor initialisation: counter 0 in both slots
                        key_valid <= 1'b1;
                        ctmp      <= '0;
                        aslot     <= 1'b0;
                        if (flags[1]) begin
                            bmode <= 2'd1;
                            cnt2  <= '0;
                            ret3  <= S_AW1;
                            ret2  <= S_KLF;
                            st    <= S_BLD;
                        end else begin
                            ret <= S_IDLE;
                            st  <= S_HDR;
                        end
                    end
                    S_KLF: begin
                        if (!rcmp) begin
                            key_valid    <= 1'b0;
                            fault_anchor <= 1'b1;
                            rcode        <= E_ANCHOR_IO;
                            st           <= S_DRAIN;
                        end else if (!aslot) begin
                            aslot <= 1'b1;
                            bmode <= 2'd1;
                            cnt2  <= '0;
                            ret3  <= S_AW1;
                            st    <= S_BLD;
                        end else begin
                            hwm       <= '0;
                            hwm_valid <= 1'b1;
                            ret       <= S_IDLE;
                            st        <= S_HDR;
                        end
                    end
                    // ------------------------------------------------ keyed block build + permute
                    S_BLD: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd24) st <= S_BKC;
                    end
                    S_BKC: begin
                        cnt2 <= '0;
                        if (bmode == 2'd0) begin
                            if (!isprf) hj <= hj + 16'd1;
                            isprf <= 1'b0;
                        end
                        st <= ret3;
                    end
                    // ------------------------------------------------ anchor read: slot aslot
                    S_AR0: st <= S_AR1;
                    S_AR1: begin
                        ctmp  <= an_rx[31:0];
                        hi0   <= (an_rx[63:32] == 32'd0);
                        bmode <= 2'd1;
                        cnt2  <= '0;
                        ret3  <= S_AR2;
                        st    <= S_BLD;
                    end
                    S_AR2: st <= S_AR3;
                    S_AR3: begin
                        rcmp <= !cmp_ne && hi0;
                        st   <= S_AR4;
                    end
                    S_AR4: begin
                        rcmp <= rcmp && !cmp_ne;
                        st   <= S_AR5;
                    end
                    S_AR5: st <= ret2;
                    // ------------------------------------------------ anchor write + read back
                    S_AW1: st <= S_AW2;
                    S_AW2: st <= S_AW3;
                    S_AW3: st <= S_AW4;
                    S_AW4: st <= S_AW5;
                    S_AW5: st <= S_AW6;
                    S_AW6: st <= S_AW7;
                    S_AW7: begin
                        rcmp <= !cmp_ne;
                        st   <= S_AW8;
                    end
                    S_AW8: begin
                        rcmp <= rcmp && !cmp_ne;
                        st   <= S_AW9;
                    end
                    S_AW9: begin
                        rcmp <= rcmp && !cmp_ne;
                        st   <= S_AWA;
                    end
                    S_AWA: st <= ret2;
                    // ------------------------------------------------ Cut-the-Hash
                    S_CTG: begin
                        cnt2 <= '0;
                        st   <= S_CTL;
                    end
                    S_CTL: begin
                        if (cnt2 == 5'd4) is_fors <= (in_data[31:24] == 8'd3);
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd7) begin
                            cnt2 <= '0;
                            if (pubgen) st <= S_CTT;
                            else begin
                                bmode <= 2'd2;
                                ret3  <= S_CTT;
                                st    <= S_BLD;
                            end
                        end
                    end
                    S_CTT: begin
                        if (!pubgen && cmp_ne) macdiff <= 1'b1;
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd1) st <= S_CTD;
                    end
                    S_CTD: begin
                        cnt2 <= '0;
                        if (!key_valid) begin
                            rcode <= E_NOKEY;
                            st    <= S_DRAIN;
                        end else if (macdiff) begin
                            fault_mac <= 1'b1;
                            rcode     <= E_MAC;
                            st        <= S_DRAIN;
                        end else if (stateful && !pubgen) begin
                            aslot <= 1'b0;
                            ret2  <= S_CA0;
                            st    <= S_AR0;
                        end else begin
                            rlen <= {12'd0, nch, 4'd0};
                            ret  <= S_CTS;
                            ci   <= '0;
                            widx <= '0;
                            sh   <= '0;
                            st   <= S_HDR;
                        end
                    end
                    S_CA0: begin
                        v0    <= rcmp;
                        cur   <= ctmp;
                        aslot <= 1'b1;
                        ret2  <= S_CA1;
                        st    <= S_AR0;
                    end
                    S_CA1: begin
                        anyv <= v0 | rcmp;
                        if (rcmp && (!v0 || ctmp >= cur)) begin
                            cur   <= ctmp;
                            older <= 1'b0;
                        end else older <= 1'b1;
                        st <= S_CA2;
                    end
                    S_CA2: begin
                        if (!anyv) begin
                            rcode <= E_ANCHOR_EMPTY;
                            st    <= S_DRAIN;
                        end else if (hwm_valid && cur < hwm) begin
                            fault_anchor <= 1'b1;
                            rcode        <= E_ROLLBACK;
                            st           <= S_DRAIN;
                        end else if (port[31:0] < cur || port[31:0] == 32'hFFFF_FFFF) begin
                            rcode <= E_REUSE;
                            st    <= S_DRAIN;
                        end else begin
                            ctmp  <= port[31:0] + 32'd1;
                            aslot <= older;
                            bmode <= 2'd1;
                            cnt2  <= '0;
                            ret3  <= S_AW1;
                            ret2  <= S_CA3;
                            st    <= S_BLD;
                        end
                    end
                    S_CA3: begin
                        if (!rcmp) begin
                            fault_anchor <= 1'b1;
                            rcode        <= E_ANCHOR_IO;
                            st           <= S_DRAIN;
                        end else begin
                            hwm       <= ctmp;
                            hwm_valid <= 1'b1;
                            rlen      <= {12'd0, nch, 4'd0};
                            ret       <= S_CTS;
                            ci        <= '0;
                            widx      <= '0;
                            sh        <= '0;
                            st        <= S_HDR;
                        end
                    end
                    S_CTS: begin
                        if (ci == nch) st <= S_WIPE;
                        else begin
                            sym   <= port_sh[15:0] & symmask;
                            steps <= pubgen ? (is_fors ? 16'd1 : symmask) : (is_fors ? 16'd0 : (port_sh[15:0] & symmask));
                            if (sh + {2'd0, sw} + {2'd0, sw} > 7'd64) begin
                                sh   <= '0;
                                widx <= widx + 2'd1;
                            end else sh <= sh + {2'd0, sw};
                            hj    <= '0;
                            isprf <= 1'b1;
                            bmode <= 2'd0;
                            cnt2  <= '0;
                            ret3  <= S_CKD;
                            st    <= S_BLD;
                        end
                    end
                    S_CM0: st <= S_CM1;
                    S_CM1: begin
                        cnt2 <= '0;
                        st   <= S_BLD;
                    end
                    S_CKD: begin
                        cnt2 <= '0;
                        if (steps == 16'd0) st <= S_CO;
                        else begin
                            steps <= steps - 16'd1;
                            st    <= S_CM0;
                        end
                    end
                    S_CO: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd1) begin
                            ci <= ci + 8'd1;
                            st <= S_CTS;
                        end
                    end
                    // ------------------------------------------------ verifier VM
                    S_HVG: st <= S_HVR;
                    S_HVR: begin
                        if (wrem == 21'd0) begin
                            verdict <= !fail && !noncanon;
                            cnt2    <= '0;
                            st      <= S_HVF;
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
                            st     <= S_HVD;
                        end
                    end
                    S_HVD: begin
                        cnt2 <= '0;
                        unique case (hop)
                            4'd1: begin  // HASH dst a, cap b / FS-init, latch c[2:0]
                                if (dleft == 16'd0) begin
                                    fail <= 1'b1;
                                    st   <= S_HVN;
                                end else begin
                                    hs_n      <= dleft - 16'd1;
                                    hs_capsrc <= hc[3] ? 2'd2 : 2'd1;
                                    hs_capreg <= hb[2:0];
                                    hs_latch  <= hc[2:0];
                                    hs_skip   <= hc[5:4];
                                    ret       <= S_HVH;
                                    st        <= S_HSZ;
                                end
                            end
                            4'd2, 4'd3, 4'd4: st <= S_HVA;
                            4'd5: begin
                                if (dleft != 16'd4) begin
                                    fail <= 1'b1;
                                    st   <= S_HVN;
                                end else st <= S_HVL;
                            end
                            4'd6: st <= S_HVE;
                            4'd7: st <= S_HVP;
                            4'd8: begin
                                if (ha[5:0] == 6'd0 || ha[5:0] > 6'd32 || dleft != 16'd1 + {8'd0, ha[5:0], 2'd0}) begin
                                    fail <= 1'b1;
                                    st   <= S_HVN;
                                end else st <= S_HVM;
                            end
                            4'd9: st <= S_HVI;
                            default: begin
                                fail <= 1'b1;
                                st   <= S_HVN;
                            end
                        endcase
                    end
                    S_HVH, S_HVA: st <= S_HVN;
                    S_HVL: begin
                        if (bindw) gfdone <= 1'b1;
                        else begin
                            if (hs_k == 16'd0 && in_ge_p) noncanon <= 1'b1;
                            gfdone <= 1'b0;
                            if (hs_k != 16'd0) hs_k <= hs_k - 16'd1;
                            cnt2 <= cnt2 + 5'd1;
                            if (cnt2 == 5'd3) st <= S_HVN;
                        end
                    end
                    S_HVE: begin
                        if (!fe_eq) fail <= 1'b1;
                        st <= S_HVN;
                    end
                    S_HVP: st <= S_HVQ;
                    S_HVQ: begin
                        if ((res[31:0] & lowmask(hc[5:0])) != 32'd0) fail <= 1'b1;
                        st <= S_HVN;
                    end
                    S_HVM: begin
                        if (idx_armed && in_data[31:0] != lidx) fail <= 1'b1;
                        idx_armed <= 1'b0;
                        midx  <= (33'd1 << ha[5:0]) | {1'b0, in_data[31:0]};
                        mk_kb <= rb(hb[2:0]);
                        cnt   <= {10'd0, ha[5:0]};
                        cnt2  <= '0;
                        ret2  <= S_HVN;
                        st    <= S_MPS;
                    end
                    S_HVI: st <= S_HVJ;
                    S_HVJ: begin
                        lidx      <= res[31:0] & lowmask(hc[5:0]);
                        idx_armed <= 1'b1;
                        st <= S_HVN;
                    end
                    S_HVN: if (dleft == 16'd0) begin
                        inrec <= 1'b0;
                        hs_k  <= '0;
                        if (fail && !fset) begin
                            fset <= 1'b1;
                            fidx <= recidx;
                        end
                        st <= S_HVR;
                    end
                    S_HVF: begin
                        cnt2 <= cnt2 + 5'd1;
                        if (cnt2 == 5'd3) begin
                            cnt2      <= '0;
                            bmode     <= 2'd3;
                            rok       <= verdict;
                            verify_ok <= verdict;
                            rlen      <= 24'd72;
                            ret3      <= S_HDR;
                            ret       <= S_HVS;
                            st        <= S_BLD;
                        end
                    end
                    S_HVS: begin  // receipt (lanes 0..3), then the transcript state (shadow 32..35)
                        cnt2  <= '0;
                        obase <= 6'd0;
                        olim  <= 5'd4;
                        ret   <= S_HVC;
                        st    <= S_OUTL;
                    end
                    S_HVC: begin
                        cnt2  <= '0;
                        obase <= 6'd32;
                        ret   <= S_WIPE;
                        st    <= S_OUTL;
                    end
                    default: st <= S_IDLE;
                endcase
            end
        end
    end

    wire unused = &{1'b0, mul_busy, gf_busy, res[63:32], port_sh[63:16], ha[7:6], hb[7:3], hc[7:6]};
endmodule
`default_nettype wire

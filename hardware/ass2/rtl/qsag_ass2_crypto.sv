// Shared constant-time cryptographic & operand-staging unit (`DIT = 1`):
//   - `work[0..5]` doubles as `(va, vb, vc, address, alu_q, csr_q)` for `qsag_ass2_core`
//     (zero duplicate 64-bit pipeline registers!).
//   - Clean registered-regbank handshake (`lane_ready_q` + `re_o`), severing the 40x64
//     regbank read tree from `add_a/add_b` muxes (< 16 ns SS!).
//   - Goldilocks 3-level zero-prefix canonicalization (`gl_reduce64`) moved AFTER
//     `u_operand_a` / `u_operand_b` into `add_stage_q == 1` (< 14 ns SS!).
//   - Shares `qsag_ass2_alu`'s 6-stage barrel rotator for 1-clock `Keccak` Rho rotation
//     (31.5x faster Rho, 4.2x faster Keccak-f[1600] with zero extra gates!).
module qsag_ass2_crypto (
    input  logic        clk, srst_n,
    input  logic        cancel_i, cap_we_i,
    input  logic [1:0]  cap_idx_i,
    input  logic [63:0] cap_data_i,
    input  logic [63:0] address_i, alu_i, csr_i,
    output logic [63:0] address_o, va_o, vb_o, vc_o, alu_o, csr_o,
    output logic [5:0]  rot_amt_o,
    input  logic [63:0] rot_res_i,
    input  logic        kick,
    input  logic [3:0]  op, sub, rd, ra, rb,
    input  logic        keccak_12_i,
    output logic        re_o,
    output logic [4:0]  addr_a, waddr,
    input  logic [63:0] lane_a,
    output logic        we,
    output logic [63:0] wdata, scalar,
    output logic        done
);
    import qsag_ass2_pkg::*;
    typedef enum logic [5:0] {
        S_IDLE, S_SCALAR_ADD, S_SCALAR_MUL, S_FINISH,
        S_GL_FOLD1, S_GL_FOLD2,
        S_BOX_START, S_BOX_WAIT,
        S_FP_PREP, S_FP_DOUBLE, S_FP_TRIPLE, S_FP_START, S_FP_WAIT, S_FP_WRITE, S_FP_ADD_A, S_FP_ADD_B,
        S_GF_A0, S_GF_A1, S_GF_B0, S_GF_B1, S_GF_STEP, S_GF_WRITE_LO, S_GF_WRITE_HI,
        S_ME_SUM, S_ME_DOUBLE, S_ME_PLUS, S_ME_STORE,
        S_ROW_SUM, S_ROW_STORE, S_ROUND_NEXT,
        S_RC_GRAIN, S_RC_W12_INIT, S_RC_W12_M1, S_RC_W12_W1, S_RC_W12_M2, S_RC_W12_W2, S_RC_ADD,
        S_MI_SUM, S_MI_LOAD, S_MI_DOUBLE, S_MI_STORE,
        S_K_THETA_C, S_K_THETA_D, S_K_THETA_XOR, S_K_RHO_SWAP, S_K_RHO_ROT, S_K_CHI_READ, S_K_CHI_WRITE
    } cphase_t;

    cphase_t     phase, ret_phase;
    wire         advance;
    word_t       work [6];
    logic [5:0]  work_en;
    word_t       work_d [6];
    for (genvar wi = 0; wi < 6; wi++) begin : g_work
        qsag_ass2_cg_dff #(.W(64)) u_w (
            .clk(clk), .rst_n(srst_n), .en(work_en[wi] && advance), .d(work_d[wi]), .q(work[wi])
        );
    end
    assign va_o      = work[0];
    assign vb_o      = work[1];
    assign vc_o      = work[2];
    assign address_o = work[3];
    assign alu_o     = work[4];
    assign csr_o     = work[5];

    logic [4:0]  lane, col;
    logic [6:0]  gf_cnt;
    logic [2:0]  term, limb;
    logic [1:0]  box_step, group_idx;
    logic [5:0]  doubles;
    logic [5:0]  round_q;
    logic [7:0]  sbox_cnt;
    logic        w12_pass;

    // 80-bit Grain LFSR (`icgtp_2` clock-gated) for `POSEIDON2.GL24` round constants
    logic [79:0] grain_q, grain_d;
    logic        grain_en;
    qsag_ass2_cg_dff #(.W(80)) u_grain (
        .clk(clk), .rst_n(srst_n), .en(grain_en && advance), .d(grain_d), .q(grain_q)
    );
    wire g_b1 = grain_q[62] ^ grain_q[51] ^ grain_q[38] ^ grain_q[23] ^ grain_q[13] ^ grain_q[0];
    wire [79:0] g1 = {g_b1, grain_q[79:1]};
    wire g_b2 = g1[62] ^ g1[51] ^ g1[38] ^ g1[23] ^ g1[13] ^ g1[0];
    wire [79:0] g2 = {g_b2, g1[79:1]};
    wire grain_lt_p = !( (&work[1][63:32]) && (|work[1][31:0]) );

    wire [63:0] w12_seed = (round_q < 6'd4)  ? 64'hbd18_2838_c8db_5aba
                         : (round_q < 6'd26) ? 64'h848c_0fde_d4fc_6113
                         :                     64'h8971_4501_b468_25f5;
    wire [5:0]  w12_rnd  = (round_q < 6'd4)  ? round_q
                         : (round_q < 6'd26) ? (round_q - 6'd4)
                         :                     (round_q - 6'd26);
    wire [63:0] w12_in   = w12_pass ? (work[1] ^ 64'(lane)) : (w12_seed ^ 64'(w12_rnd));
    wire [63:0] w12_z0   = w12_in + 64'h9e37_79b9_7f4a_7c15;

    wire wide = (sub == 4'd1);
    wire [4:0] width_n     = wide ? 5'd24 : 5'd12;
    wire [4:0] stride      = wide ? 5'd6  : 5'd3;
    wire [5:0] partial_end = wide ? 6'd48 : 6'd26;
    wire partial = (round_q >= 6'd4) && (round_q < partial_end);
    wire [4:0] next_col_lane = (group_idx == 2'd3) ? col : (lane + stride);

    function automatic logic [4:0] fp_base(input logic [3:0] idx);
        return (5'(idx) << 2) + 5'(idx);
    endfunction

    function automatic logic [4:0] keccak_pi_lane(input logic [4:0] step);
        case (step)
            5'd0:  keccak_pi_lane = 5'd1;   5'd1:  keccak_pi_lane = 5'd10;
            5'd2:  keccak_pi_lane = 5'd7;   5'd3:  keccak_pi_lane = 5'd11;
            5'd4:  keccak_pi_lane = 5'd17;  5'd5:  keccak_pi_lane = 5'd18;
            5'd6:  keccak_pi_lane = 5'd3;   5'd7:  keccak_pi_lane = 5'd5;
            5'd8:  keccak_pi_lane = 5'd16;  5'd9:  keccak_pi_lane = 5'd8;
            5'd10: keccak_pi_lane = 5'd21;  5'd11: keccak_pi_lane = 5'd24;
            5'd12: keccak_pi_lane = 5'd4;   5'd13: keccak_pi_lane = 5'd15;
            5'd14: keccak_pi_lane = 5'd23;  5'd15: keccak_pi_lane = 5'd19;
            5'd16: keccak_pi_lane = 5'd13;  5'd17: keccak_pi_lane = 5'd12;
            5'd18: keccak_pi_lane = 5'd2;   5'd19: keccak_pi_lane = 5'd20;
            5'd20: keccak_pi_lane = 5'd14;  5'd21: keccak_pi_lane = 5'd22;
            5'd22: keccak_pi_lane = 5'd9;   5'd23: keccak_pi_lane = 5'd6;
            default: keccak_pi_lane = 5'd1;
        endcase
    endfunction

    function automatic logic [5:0] keccak_rho_amt(input logic [4:0] step);
        case (step)
            5'd0:  keccak_rho_amt = 6'd1;   5'd1:  keccak_rho_amt = 6'd3;
            5'd2:  keccak_rho_amt = 6'd6;   5'd3:  keccak_rho_amt = 6'd10;
            5'd4:  keccak_rho_amt = 6'd15;  5'd5:  keccak_rho_amt = 6'd21;
            5'd6:  keccak_rho_amt = 6'd28;  5'd7:  keccak_rho_amt = 6'd36;
            5'd8:  keccak_rho_amt = 6'd45;  5'd9:  keccak_rho_amt = 6'd55;
            5'd10: keccak_rho_amt = 6'd2;   5'd11: keccak_rho_amt = 6'd14;
            5'd12: keccak_rho_amt = 6'd27;  5'd13: keccak_rho_amt = 6'd41;
            5'd14: keccak_rho_amt = 6'd56;  5'd15: keccak_rho_amt = 6'd8;
            5'd16: keccak_rho_amt = 6'd25;  5'd17: keccak_rho_amt = 6'd43;
            5'd18: keccak_rho_amt = 6'd62;  5'd19: keccak_rho_amt = 6'd18;
            5'd20: keccak_rho_amt = 6'd39;  5'd21: keccak_rho_amt = 6'd61;
            5'd22: keccak_rho_amt = 6'd20;  5'd23: keccak_rho_amt = 6'd44;
            default: keccak_rho_amt = 6'd1;
        endcase
    endfunction

    function automatic logic [63:0] keccak_rc(input logic [4:0] r);
        case (r)
            5'd0:  keccak_rc = 64'h0000000000000001; 5'd1:  keccak_rc = 64'h0000000000008082;
            5'd2:  keccak_rc = 64'h800000000000808A; 5'd3:  keccak_rc = 64'h8000000080008000;
            5'd4:  keccak_rc = 64'h000000000000808B; 5'd5:  keccak_rc = 64'h0000000080000001;
            5'd6:  keccak_rc = 64'h8000000080008081; 5'd7:  keccak_rc = 64'h8000000000008009;
            5'd8:  keccak_rc = 64'h000000000000008A; 5'd9:  keccak_rc = 64'h0000000000000088;
            5'd10: keccak_rc = 64'h0000000080008009; 5'd11: keccak_rc = 64'h000000008000000A;
            5'd12: keccak_rc = 64'h000000008000808B; 5'd13: keccak_rc = 64'h800000000000008B;
            5'd14: keccak_rc = 64'h8000000000008089; 5'd15: keccak_rc = 64'h8000000000008003;
            5'd16: keccak_rc = 64'h8000000000008002; 5'd17: keccak_rc = 64'h8000000000000080;
            5'd18: keccak_rc = 64'h000000000000800A; 5'd19: keccak_rc = 64'h800000008000000A;
            5'd20: keccak_rc = 64'h8000000080008081; 5'd21: keccak_rc = 64'h8000000000008080;
            5'd22: keccak_rc = 64'h0000000080000001; 5'd23: keccak_rc = 64'h8000000080008008;
            default: keccak_rc = 64'd0;
        endcase
    endfunction

    wire [4:0]  k_pi_idx = keccak_pi_lane(lane);
    assign      rot_amt_o = doubles;
    wire [63:0] k_chi    = work[0] ^ ((~work[1]) & work[2])
                         ^ ((lane == 5'd0 && col == 5'd0) ? keccak_rc(round_q[4:0]) : 64'd0);

    wire wrapped = term > limb;
    wire [2:0] b_limb = limb - term + (wrapped ? 3'd5 : 3'd0);

    logic [4:0] fp_addr_a, fp_addr_b;
    always_ff @(posedge clk) if (phase == S_FP_PREP) begin
        fp_addr_a <= fp_base(ra) + 5'((sub == 4'd4) ? term : limb);
        fp_addr_b <= fp_base(rb) + 5'((sub == 4'd4) ? b_limb : limb);
    end

    // Registered-regbank read handshake: any state consuming `lane_a` latches `bank_rdata_o`
    // on `!lane_ready_q` before executing, severing the regbank read path completely!
    wire uses_lane_a = phase inside {
        S_FP_DOUBLE, S_FP_START, S_FP_ADD_A, S_FP_ADD_B,
        S_GF_A0, S_GF_A1, S_GF_B0, S_GF_B1,
        S_ME_SUM, S_ROW_SUM, S_ROW_STORE, S_RC_ADD, S_MI_SUM, S_MI_LOAD,
        S_K_THETA_C, S_K_THETA_XOR, S_K_RHO_SWAP, S_K_CHI_READ
    };
    logic lane_ready_q;
    assign re_o = uses_lane_a && !lane_ready_q;
    wire lane_ok = !uses_lane_a || lane_ready_q;

    word_t add_a, add_b, add_result;
    logic subtract;
    wire uses_adder = phase inside {S_SCALAR_ADD, S_GL_FOLD1, S_GL_FOLD2,
        S_FP_DOUBLE, S_FP_TRIPLE, S_FP_ADD_B, S_ME_SUM, S_ME_DOUBLE, S_ME_PLUS,
        S_ME_STORE, S_ROW_SUM, S_ROW_STORE, S_RC_ADD, S_MI_SUM, S_MI_DOUBLE, S_MI_STORE};
    logic [1:0] add_stage_q;
    assign advance = lane_ok && (!uses_adder || add_stage_q == 2'd2);

    always_ff @(posedge clk or negedge srst_n) begin
        if (!srst_n) begin
            lane_ready_q <= 1'b0;
            add_stage_q  <= 2'd0;
        end else if (cancel_i) begin
            lane_ready_q <= 1'b0;
            add_stage_q  <= 2'd0;
        end else begin
            if (advance) lane_ready_q <= 1'b0;
            else if (uses_lane_a) lane_ready_q <= 1'b1;

            if (advance) add_stage_q <= 2'd0;
            else if (lane_ok && uses_adder) add_stage_q <= add_stage_q + 2'd1;
        end
    end

    word_t ma, mb, mc;
    logic mstart_raw, mlast, mul_gl_mode, gf_clr, gf_step_en, fold_we;
    wire mstart = mstart_raw && lane_ok;
    wire [63:0] a_q, b_q;
    // Capture uncanonicalized `add_a` / `add_b` directly into `u_operand_a/b` (< 8 ns SS mux!),
    // then apply 3-level zero-prefix `gl_reduce64` in `add_stage_q == 1` (< 14 ns SS!).
    wire capture_add = lane_ok && uses_adder && (add_stage_q == 2'd0);
    qsag_ass2_cg_dff u_operand_a (
        .clk(clk), .rst_n(srst_n), .en(capture_add || mstart),
        .d(mstart ? ma : add_a), .q(a_q)
    );
    qsag_ass2_cg_dff u_operand_b (
        .clk(clk), .rst_n(srst_n), .en(capture_add), .d(add_b), .q(b_q)
    );
    logic sub_q;
    always_ff @(posedge clk) if (capture_add) sub_q <= subtract;

    wire [63:0] ca = gl_reduce64(a_q);
    wire [63:0] cb = gl_reduce64(b_q) ^ {64{sub_q}};
    wire [64:0] sum;
    qsag_ass2_add64 u_add (.a(ca), .b(cb), .cin(sub_q), .sum(sum[63:0]), .cout(sum[64]));
    wire [64:0] sum_q;
    qsag_ass2_cg_dff #(.W(65)) u_sum (
        .clk(clk), .rst_n(srst_n), .en(lane_ok && uses_adder && add_stage_q == 2'd1), .d(sum), .q(sum_q)
    );
    wire correct = sub_q ? !sum_q[64] : (sum_q >= {1'b0, PRIME});
    assign add_result = correct ? (sum_q[63:0] + (sub_q ? PRIME : -PRIME)) : sum_q[63:0];

    wire [127:0] raw;
    wire [127:0] gf_next;
    qsag_ass2_gf_step gf({work[1], work[0]}, raw, work[3][63:60], gf_next);
    qsag_gl64_karatsuba_csa mul(
        .clk(clk), .srst_n(srst_n),
        .start(mstart), .mode_gl(mul_gl_mode),
        .gf_clr_i(gf_clr && advance), .gf_step_i(gf_step_en && advance), .gf_next_i(gf_next),
        .fold_we_i(fold_we && advance), .fold_val_i(add_result),
        .opa(a_q), .opb(mb), .opc(mc),
        .last(mlast), .prod128(raw)
    );

    wire [63:0] p2_term = gl_mul_2p32m1(raw[95:64]);

    always_comb begin
        addr_a = lane; waddr = lane; wdata = add_result; we = 1'b0;
        ma = work[0]; mb = work[1]; mc = work[2]; mstart_raw = 1'b0;
        mul_gl_mode = (op != ALU) && !(phase inside {S_RC_W12_M1, S_RC_W12_W1, S_RC_W12_M2, S_RC_W12_W2});
        gf_clr = 1'b0; gf_step_en = 1'b0; fold_we = 1'b0;
        add_a = lane_a; add_b = lane_a; subtract = 1'b0;

        case (phase)
            S_SCALAR_ADD: begin add_a = work[0]; add_b = work[1]; subtract = (sub == 4'd2); end
            S_IDLE: begin
                mstart_raw = kick && (op == ALU || (op == GL64 && sub == 4'd0));
                add_a      = work[0]; add_b = work[1]; subtract = (sub == 4'd2);
            end
            S_GL_FOLD1: begin
                add_a   = raw[63:0];
                add_b   = work[5];
                fold_we = 1'b1;
            end
            S_GL_FOLD2: begin
                add_a    = raw[63:0];
                add_b    = {32'd0, raw[127:96]};
                subtract = 1'b1;
                we       = (ret_phase == S_BOX_WAIT) && (op == PERM) && (box_step == 2'd3);
                wdata    = add_result;
            end
            S_BOX_START: begin
                ma = (box_step == 2'd0) ? work[0] : work[1];
                mb = (box_step == 2'd2) ? work[1] : work[0];
                mc = 64'd0; mstart_raw = 1'b1;
            end
            S_BOX_WAIT: begin
                ma = (box_step == 2'd0) ? work[0] : work[1];
            end
            S_FP_DOUBLE, S_FP_TRIPLE: begin
                addr_a = fp_addr_a;
                add_b  = (phase == S_FP_DOUBLE) ? lane_a : work[5];
            end
            S_FP_START: begin
                addr_a     = fp_addr_b;
                ma         = work[5];
                mb         = lane_a;
                mc         = (term == 3'd0) ? 64'd0 : work[4];
                mstart_raw = 1'b1;
            end
            S_FP_WAIT: begin
                ma = work[5];
            end
            S_FP_WRITE: begin
                waddr = fp_base(rd) + 5'(limb);
                wdata = work[0];
                we    = 1'b1;
            end
            S_FP_ADD_A: addr_a = fp_addr_a;
            S_FP_ADD_B: begin
                addr_a   = fp_addr_b;
                add_a    = work[5];
                add_b    = lane_a;
                subtract = (sub == 4'd6);
                waddr    = fp_base(rd) + 5'(limb);
                wdata    = add_result;
                we       = 1'b1;
            end
            S_GF_A0, S_GF_A1: addr_a = {ra, (phase == S_GF_A1)};
            S_GF_B0:          addr_a = {rb, 1'b0};
            S_GF_B1: begin
                addr_a = {rb, 1'b1};
                gf_clr = (sub == 4'd0);
            end
            S_GF_STEP: gf_step_en = 1'b1;
            S_GF_WRITE_LO, S_GF_WRITE_HI: begin
                waddr = {rd, (phase == S_GF_WRITE_HI)};
                wdata = (sub == 4'd1) ? ((phase == S_GF_WRITE_LO) ? work[4] : work[5])
                                      : ((phase == S_GF_WRITE_LO) ? raw[63:0] : raw[127:64]);
                we    = 1'b1;
            end
            S_ME_SUM:    add_b = (group_idx == 2'd0) ? 64'd0 : work[4];
            S_ME_DOUBLE: begin add_a = work[1]; add_b = work[1]; end
            S_ME_PLUS:   begin add_a = work[5]; add_b = work[0]; end
            S_ME_STORE:  begin add_a = work[4]; add_b = work[5]; we = 1'b1; end
            S_ROW_SUM:   add_b = (col == 5'd0) ? 64'd0 : work[1];
            S_ROW_STORE: begin add_b = work[1]; we = 1'b1; end
            S_RC_W12_M1, S_RC_W12_W1: begin
                ma         = work[5];
                mb         = 64'hbf58_476d_1ce4_e5b9;
                mc         = 64'd0;
                mstart_raw = (phase == S_RC_W12_M1);
            end
            S_RC_W12_M2, S_RC_W12_W2: begin
                ma         = work[5];
                mb         = 64'h94d0_49bb_1331_11eb;
                mc         = 64'd0;
                mstart_raw = (phase == S_RC_W12_M2);
            end
            S_RC_ADD:    add_b = work[1];
            S_MI_SUM:    add_b = (lane == 5'd0) ? 64'd0 : work[1];
            S_MI_DOUBLE: begin add_a = work[2]; add_b = work[2]; end
            S_MI_STORE:  begin add_a = work[1]; add_b = work[2]; subtract = (lane == 5'd0); we = 1'b1; end
            S_K_THETA_XOR: begin
                addr_a = lane; waddr = lane; wdata = lane_a ^ work[0]; we = 1'b1;
            end
            S_K_RHO_SWAP: begin
                addr_a = k_pi_idx; waddr = k_pi_idx; wdata = work[0]; we = (lane != 5'd0);
            end
            S_K_CHI_READ:  addr_a = lane + col;
            S_K_CHI_WRITE: begin waddr = lane + col; wdata = k_chi; we = 1'b1; end
            default: ;
        endcase
        if (!advance) we = 1'b0;
    end

    assign scalar = work[0];
    assign done   = (phase == S_FINISH);

    // Factored shared shift `work[0..3] <= work[1..4]` eliminates 7 duplicate 256b mux trees!
    wire shift_work_lo = (phase == S_GL_FOLD2 && ret_phase == S_FP_WAIT && term == 3'd0)
                       || (phase inside {S_FP_WRITE, S_ME_SUM, S_ME_STORE,
                                         S_K_THETA_C, S_K_THETA_XOR, S_K_CHI_WRITE, S_K_CHI_READ});

    always_comb begin
        work_en = 6'd0;
        for (int i = 0; i < 6; i++) work_d[i] = work[i];
        grain_en = 1'b0;
        grain_d  = g2;

        if (shift_work_lo) begin
            work_en[3:0] = 4'b1111;
            work_d[0] = work[1];
            work_d[1] = work[2];
            work_d[2] = work[3];
            work_d[3] = (phase == S_ME_SUM)   ? lane_a
                      : (phase == S_ME_STORE) ? work[0]
                      :                         work[4];
        end

        if (phase == S_IDLE) begin
            if (cap_we_i) begin
                work_en[{1'b0, cap_idx_i}] = 1'b1;
                work_d[{1'b0, cap_idx_i}]  = cap_data_i;
                if (cap_idx_i == 2'd1 && op inside {LOAD, STORE, BR, JAL, JALR, SPG}) begin
                    work_en[3] = 1'b1;
                    work_d[3]  = address_i;
                end
                if (cap_idx_i == 2'd2) begin
                    work_en[4] = 1'b1;
                    work_d[4]  = alu_i;
                    work_en[5] = 1'b1;
                    work_d[5]  = csr_i;
                end
            end else if (kick && op == PERM && sub == 4'd1) begin
                grain_en = 1'b1;
                grain_d  = 80'h779b_bcd2_c7a6_32d7_f9c2;
            end
        end else case (phase)
            S_SCALAR_ADD: begin work_en[0] = 1'b1; work_d[0] = add_result; end
            S_SCALAR_MUL, S_BOX_WAIT, S_FP_WAIT: if (mlast) begin
                if (phase == S_SCALAR_MUL && op == ALU) begin
                    work_en[0] = 1'b1;
                    work_d[0]  = (sub == 4'd7) ? raw[63:0] : raw[127:64];
                end else begin
                    work_en[5] = 1'b1;
                    work_d[5]  = p2_term;
                end
            end
            S_GL_FOLD2: begin
                case (ret_phase)
                    S_SCALAR_MUL: begin work_en[0] = 1'b1; work_d[0] = add_result; end
                    S_BOX_WAIT: begin
                        work_en[1] = 1'b1; work_d[1] = add_result;
                        if (box_step == 2'd3 && op == GL64) begin
                            work_en[0] = 1'b1; work_d[0] = add_result;
                        end
                    end
                    default: begin
                        work_en[4] = 1'b1; work_d[4] = add_result;
                    end
                endcase
            end
            S_FP_DOUBLE: begin work_en[5] = 1'b1; work_d[5] = wrapped ? add_result : lane_a; end
            S_FP_TRIPLE: begin work_en[5] = 1'b1; work_d[5] = add_result; end
            S_FP_WRITE:  begin work_en[4] = 1'b1; work_d[4] = 64'd0; end
            S_FP_ADD_A:  begin work_en[5] = 1'b1; work_d[5] = lane_a; end
            S_GF_A0:     begin work_en[0] = 1'b1; work_d[0] = lane_a; end
            S_GF_A1:     begin work_en[1] = 1'b1; work_d[1] = lane_a; end
            S_GF_B0:     begin work_en[2] = 1'b1; work_d[2] = lane_a; end
            S_GF_B1: begin
                work_en[3] = 1'b1; work_d[3] = lane_a;
                if (sub == 4'd1) begin
                    work_en[4] = 1'b1; work_d[4] = work[0] ^ work[2];
                    work_en[5] = 1'b1; work_d[5] = work[1] ^ lane_a;
                end
            end
            S_GF_STEP: begin
                work_en[3:2] = 2'b11;
                {work_d[3], work_d[2]} = {work[3][59:0], work[2], 4'd0};
            end
            S_ME_SUM:    begin work_en[4] = 1'b1; work_d[4] = add_result; end
            S_ME_DOUBLE, S_ME_PLUS: begin work_en[5] = 1'b1; work_d[5] = add_result; end
            S_ROW_SUM, S_MI_SUM:    begin work_en[1] = 1'b1; work_d[1] = add_result; end
            S_ROUND_NEXT: if (sbox_cnt != (wide ? 8'd236 : 8'd118) && wide) begin
                work_en[1] = 1'b1; work_d[1] = 64'd0;
            end
            S_RC_GRAIN: begin
                if (gf_cnt < 7'd64) begin
                    grain_en = 1'b1;
                    grain_d  = g2;
                    if (g_b1) begin
                        work_en[1] = 1'b1;
                        work_d[1]  = {work[1][62:0], g_b2};
                    end
                end else if (!grain_lt_p) begin
                    work_en[1] = 1'b1; work_d[1] = 64'd0;
                end
            end
            S_RC_W12_INIT: begin
                work_en[5] = 1'b1; work_d[5] = w12_z0 ^ (w12_z0 >> 30);
            end
            S_RC_W12_W1: if (mlast) begin
                work_en[5] = 1'b1; work_d[5] = raw[63:0] ^ (raw[63:0] >> 27);
            end
            S_RC_W12_W2: if (mlast) begin
                work_en[1] = 1'b1; work_d[1] = gl_reduce64(raw[63:0] ^ (raw[63:0] >> 31));
            end
            S_RC_ADD:    begin work_en[0] = 1'b1; work_d[0] = add_result; end
            S_MI_LOAD:   begin work_en[2] = 1'b1; work_d[2] = lane_a; end
            S_MI_DOUBLE: begin work_en[2] = 1'b1; work_d[2] = add_result; end
            S_K_THETA_C: begin
                work_en[4] = 1'b1;
                work_d[4]  = ((lane < 5'd5) ? 64'd0 : work[0]) ^ lane_a;
            end
            S_K_THETA_D: begin
                work_en[4:0] = 5'b11111;
                work_d[0] = work[4] ^ {work[1][62:0], work[1][63]};
                work_d[1] = work[0] ^ {work[2][62:0], work[2][63]};
                work_d[2] = work[1] ^ {work[3][62:0], work[3][63]};
                work_d[3] = work[2] ^ {work[4][62:0], work[4][63]};
                work_d[4] = work[3] ^ {work[0][62:0], work[0][63]};
            end
            S_K_THETA_XOR, S_K_CHI_WRITE: begin
                work_en[4] = 1'b1; work_d[4] = work[0];
            end
            S_K_RHO_SWAP: if (lane != 5'd24) begin work_en[0] = 1'b1; work_d[0] = lane_a; end
            S_K_RHO_ROT:  begin work_en[0] = 1'b1; work_d[0] = rot_res_i; end
            S_K_CHI_READ: begin work_en[4] = 1'b1; work_d[4] = lane_a; end
            default: ;
        endcase
    end

    always_ff @(posedge clk or negedge srst_n) begin
        if (!srst_n) begin
            phase <= S_IDLE; ret_phase <= S_IDLE;
            lane <= 5'd0; col <= 5'd0; gf_cnt <= 7'd0;
            term <= 3'd0; limb <= 3'd0; box_step <= 2'd0;
            group_idx <= 2'd0; doubles <= 6'd0; round_q <= 6'd0;
            sbox_cnt <= 8'd0; w12_pass <= 1'b0;
        end else if (cancel_i) phase <= S_IDLE;
        else if (advance) case (phase)
            S_SCALAR_ADD: phase <= S_FINISH;
            S_IDLE: if (kick) begin
                lane <= 5'd0; col <= 5'd0; gf_cnt <= 7'd0;
                term <= 3'd0; limb <= 3'd0; group_idx <= 2'd0;
                round_q <= 6'd0; box_step <= 2'd0; sbox_cnt <= 8'd0; w12_pass <= 1'b0;
                case (op)
                    PERM: if (sub == 4'd0) begin
                        round_q <= keccak_12_i ? 6'd12 : 6'd0;
                        phase   <= S_K_THETA_C;
                    end else begin
                        phase <= S_ME_SUM;
                    end
                    GF128: phase <= S_GF_A0;
                    GL64: case (sub)
                        4'd1, 4'd2: phase <= S_SCALAR_ADD;
                        4'd3: phase <= S_BOX_START;
                        4'd4, 4'd5, 4'd6: phase <= S_FP_PREP;
                        default: phase <= S_SCALAR_MUL;
                    endcase
                    default: phase <= S_SCALAR_MUL;
                endcase
            end
            S_SCALAR_MUL: if (mlast) begin
                if (op == ALU) phase <= S_FINISH;
                else begin ret_phase <= S_SCALAR_MUL; phase <= S_GL_FOLD1; end
            end
            S_GL_FOLD1: phase <= S_GL_FOLD2;
            S_GL_FOLD2: begin
                case (ret_phase)
                    S_SCALAR_MUL: phase <= S_FINISH;
                    S_BOX_WAIT: begin
                        box_step <= box_step + 2'd1;
                        if (box_step != 2'd3) phase <= S_BOX_START;
                        else if (op == GL64) phase <= S_FINISH;
                        else if (partial) begin lane <= 5'd0; phase <= S_MI_SUM; end
                        else if (lane == width_n - 5'd1) begin
                            lane <= 5'd0; col <= 5'd0; group_idx <= 2'd0; phase <= S_ME_SUM;
                        end else begin
                            lane <= lane + 5'd1;
                            gf_cnt <= 7'd0; w12_pass <= 1'b0;
                            phase <= wide ? S_RC_GRAIN : S_RC_W12_INIT;
                        end
                    end
                    default: begin
                        if (term == 3'd4) begin
                            term <= 3'd0;
                            if (limb == 3'd4) begin limb <= 3'd0; phase <= S_FP_WRITE; end
                            else begin limb <= limb + 3'd1; phase <= S_FP_PREP; end
                        end else begin
                            term  <= term + 3'd1;
                            phase <= S_FP_PREP;
                        end
                    end
                endcase
            end
            S_BOX_START: phase <= S_BOX_WAIT;
            S_BOX_WAIT:  if (mlast) begin ret_phase <= S_BOX_WAIT; phase <= S_GL_FOLD1; end
            S_FP_PREP:   phase <= (sub == 4'd4) ? S_FP_DOUBLE : S_FP_ADD_A;
            S_FP_DOUBLE: phase <= wrapped ? S_FP_TRIPLE : S_FP_START;
            S_FP_TRIPLE: phase <= S_FP_START;
            S_FP_START:  phase <= S_FP_WAIT;
            S_FP_WAIT:   if (mlast) begin ret_phase <= S_FP_WAIT; phase <= S_GL_FOLD1; end
            S_FP_WRITE: begin
                if (limb == 3'd4) phase <= S_FINISH;
                else limb <= limb + 3'd1;
            end
            S_FP_ADD_A: phase <= S_FP_ADD_B;
            S_FP_ADD_B: begin
                if (limb == 3'd4) phase <= S_FINISH;
                else begin limb <= limb + 3'd1; phase <= S_FP_PREP; end
            end
            S_GF_A0: phase <= S_GF_A1;
            S_GF_A1: phase <= S_GF_B0;
            S_GF_B0: phase <= S_GF_B1;
            S_GF_B1: begin
                gf_cnt <= 7'd0;
                phase  <= (sub == 4'd1) ? S_GF_WRITE_LO : S_GF_STEP;
            end
            S_GF_STEP: begin
                gf_cnt <= gf_cnt + 7'd1;
                if (gf_cnt == 7'd31) phase <= S_GF_WRITE_LO;
            end
            S_GF_WRITE_LO: phase <= S_GF_WRITE_HI;
            S_GF_WRITE_HI: phase <= S_FINISH;
            S_ME_SUM: begin
                group_idx <= group_idx + 2'd1;
                lane <= next_col_lane;
                if (group_idx == 2'd3) phase <= S_ME_DOUBLE;
            end
            S_ME_DOUBLE: phase <= S_ME_PLUS;
            S_ME_PLUS:   phase <= S_ME_STORE;
            S_ME_STORE: begin
                lane <= next_col_lane; group_idx <= group_idx + 2'd1; phase <= S_ME_DOUBLE;
                if (group_idx == 2'd3) begin
                    if (col == stride - 5'd1) begin lane <= 5'd0; col <= 5'd0; phase <= S_ROW_SUM; end
                    else begin col <= col + 5'd1; lane <= col + 5'd1; phase <= S_ME_SUM; end
                end
            end
            S_ROW_SUM: begin
                col <= col + 5'd1; lane <= lane + 5'd1;
                if (col == stride - 5'd1) begin col <= 5'd0; lane <= lane - col; phase <= S_ROW_STORE; end
            end
            S_ROW_STORE: begin
                lane <= lane + 5'd1; col <= col + 5'd1;
                if (col == stride - 5'd1) begin
                    col <= 5'd0; phase <= S_ROW_SUM;
                    if (lane == width_n - 5'd1) begin lane <= 5'd0; phase <= S_ROUND_NEXT; end
                end
            end
            S_ROUND_NEXT: begin
                if (sbox_cnt == (wide ? 8'd236 : 8'd118)) phase <= S_FINISH;
                else begin
                    if (sbox_cnt != 8'd0) round_q <= round_q + 6'd1;
                    lane <= 5'd0; gf_cnt <= 7'd0; w12_pass <= 1'b0;
                    phase <= wide ? S_RC_GRAIN : S_RC_W12_INIT;
                end
            end
            S_RC_GRAIN: begin
                if (gf_cnt < 7'd64) begin
                    if (g_b1) gf_cnt <= gf_cnt + 7'd1;
                end else if (grain_lt_p) begin
                    phase <= S_RC_ADD;
                end else begin
                    gf_cnt <= 7'd0;
                end
            end
            S_RC_W12_INIT: phase <= S_RC_W12_M1;
            S_RC_W12_M1:   phase <= S_RC_W12_W1;
            S_RC_W12_W1:   if (mlast) phase <= S_RC_W12_M2;
            S_RC_W12_M2:   phase <= S_RC_W12_W2;
            S_RC_W12_W2:   if (mlast) begin
                if (!w12_pass) begin w12_pass <= 1'b1; phase <= S_RC_W12_INIT; end
                else phase <= S_RC_ADD;
            end
            S_RC_ADD: begin
                sbox_cnt <= sbox_cnt + 8'd1; box_step <= 2'd0; phase <= S_BOX_START;
            end
            S_MI_SUM: begin
                lane <= lane + 5'd1;
                if (lane == width_n - 5'd1) begin lane <= 5'd0; phase <= S_MI_LOAD; end
            end
            S_MI_LOAD: begin
                doubles <= (lane == 5'd0) ? (wide ? 6'd23 : 6'd6) : 6'(lane - 5'd1);
                phase   <= (lane == 5'd1) ? S_MI_STORE : S_MI_DOUBLE;
            end
            S_MI_DOUBLE: begin
                doubles <= doubles - 6'd1;
                if (doubles == 6'd1) phase <= S_MI_STORE;
            end
            S_MI_STORE: begin
                lane <= lane + 5'd1; phase <= S_MI_LOAD;
                if (lane == width_n - 5'd1) begin lane <= 5'd0; phase <= S_ROUND_NEXT; end
            end
            S_K_THETA_C: begin
                if (lane == 5'd24) begin lane <= 5'd0; col <= 5'd0; phase <= S_K_THETA_D; end
                else lane <= lane + 5'd1;
            end
            S_K_THETA_D: begin lane <= 5'd0; col <= 5'd0; phase <= S_K_THETA_XOR; end
            S_K_THETA_XOR: begin
                if (lane == 5'd24) begin lane <= 5'd0; col <= 5'd0; phase <= S_K_RHO_SWAP; end
                else lane <= lane + 5'd1;
            end
            S_K_RHO_SWAP: begin
                if (lane == 5'd24) begin lane <= 5'd0; col <= 5'd0; phase <= S_K_CHI_READ; end
                else begin doubles <= keccak_rho_amt(lane); phase <= S_K_RHO_ROT; end
            end
            S_K_RHO_ROT: begin
                // Single-clock 64-bit lane rotation via shared `qsag_ass2_alu` barrel rotator!
                lane  <= lane + 5'd1;
                phase <= S_K_RHO_SWAP;
            end
            S_K_CHI_READ: begin
                if (col == 5'd4) begin col <= 5'd0; phase <= S_K_CHI_WRITE; end
                else col <= col + 5'd1;
            end
            S_K_CHI_WRITE: begin
                if (col == 5'd4) begin
                    col <= 5'd0;
                    if (lane == 5'd20) begin
                        lane <= 5'd0;
                        if (round_q == 6'd23) phase <= S_FINISH;
                        else begin round_q <= round_q + 6'd1; phase <= S_K_THETA_C; end
                    end else begin
                        lane  <= lane + 5'd5;
                        phase <= S_K_CHI_READ;
                    end
                end else col <= col + 5'd1;
            end
            S_FINISH: phase <= S_IDLE;
            default:  phase <= S_IDLE;
        endcase
    end
endmodule

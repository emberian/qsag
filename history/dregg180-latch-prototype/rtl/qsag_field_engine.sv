// Dregg-180 (QSAG-NI-180) field engine: micro-sequencer driving the pipelined Goldilocks ALU
// (`acc_s, acc_c -> u_canon -> cv` pipeline cut + 2-subcycle Booth Karatsuba multiplier) over
// `qsag_sponge`, supporting Poseidon2-12, Canopy, 9-mul Tower Ext4, AND `zk-Hem v2` Quintic
// extension F_p[X]/(X^5 - 3) (`FP5_MUL`, `FP5_ADD`, `FP5_SUB`, `FP5_EQ`).
`default_nettype none

module qsag_field_engine (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         start,
    input  wire [3:0]   op,
    input  wire [5:0]   d,
    input  wire [5:0]   s1,
    input  wire [5:0]   s2,
    input  wire [2:0]   n,
    input  wire         dir,
    output wire         busy,
    output logic        done,
    output logic        eq,
    output logic [5:0]  rd_addr,
    output logic        wr_en,
    output logic [5:0]  wr_addr,
    output logic [1:0]  pm,
    output logic [3:0]  pk,
    output logic [2:0]  rm,
    output logic [1:0]  rk,
    output logic        krc,
    output logic        acc_clr,
    output logic        acc_we,
    output logic        ld_opa,
    output logic        ld_opb,
    output logic        ld_res,
    output logic        mul_start,
    output logic        mul_asel,
    output logic        mul_bsel,
    input  wire         mul_last,
    input  wire         cv_zero,
    output logic [6:0]  rc_idx
);
    localparam logic [3:0] OP_PERM    = 4'd1,  OP_ABSW    = 4'd2,  OP_SETW    = 4'd3,  OP_MOV     = 4'd4,
                           OP_EMUL    = 4'd5,  OP_EADD    = 4'd6,  OP_ESUB    = 4'd7,  OP_EEQ     = 4'd8,
                           OP_FFWD    = 4'd9,  OP_LDRES   = 4'd10, OP_FP5_MUL = 4'd11, OP_FP5_ADD = 4'd12,
                           OP_FP5_SUB = 4'd13, OP_FP5_EQ  = 4'd14;

    localparam logic [4:0] S_IDLE = 5'd0,  S_ME_A = 5'd1,  S_ME_B = 5'd2,  S_SB0  = 5'd3,
                           S_SB1  = 5'd4,  S_SBM  = 5'd5,  S_SBW  = 5'd6,  S_MI   = 5'd7,
                           S_EM0  = 5'd8,  S_EM0L = 5'd9,  S_EM1  = 5'd10, S_EM1L = 5'd11,
                           S_EM2  = 5'd12, S_EM3  = 5'd13, S_EM4  = 5'd14, S_EMC  = 5'd15,
                           S_AS0  = 5'd16, S_AS1  = 5'd17, S_AS2  = 5'd18, S_ONE  = 5'd19,
                           S_ONEW = 5'd20, S_MOV  = 5'd21, S_FF   = 5'd22,
                           S_F5L  = 5'd23, S_F5M  = 5'd24, S_F5A  = 5'd25;

    logic [4:0] st;
    logic [4:0] t;
    logic [2:0] g;          // limb / group index (0..5)
    logic [2:0] q;          // sub-step index (0..4)
    logic [3:0] lane;
    logic [4:0] rnd;
    logic       first;
    logic [3:0] pi;         // Ext4 tower product 0..8, or Fp5 output coeff k = 0..4
    logic [3:0] rem;        // Ext4 limb mask, or Fp5 inner index i = 0..4
    logic       em_first;
    logic       em_sub;

    assign busy = (st != S_IDLE);

    function automatic logic [3:0] tw_mask(input logic [3:0] k);
        unique case (k)
            4'd0:    tw_mask = 4'b0001;
            4'd1:    tw_mask = 4'b0010;
            4'd2:    tw_mask = 4'b0011;
            4'd3:    tw_mask = 4'b0100;
            4'd4:    tw_mask = 4'b1000;
            4'd5:    tw_mask = 4'b1100;
            4'd6:    tw_mask = 4'b0101;
            4'd7:    tw_mask = 4'b1010;
            default: tw_mask = 4'b1111;
        endcase
    endfunction

    localparam logic [1:0] TW_I = 2'd0, TW_P = 2'd1, TW_N = 2'd2;
    function automatic logic [6:0] tw_step(input logic [3:0] k, input logic [2:0] i);
        unique case ({k, i})
            {4'd0, 3'd0}: tw_step = {1'b0, 2'd0, TW_I, 2'd0};
            {4'd0, 3'd1}: tw_step = {1'b0, 2'd1, TW_I, 2'd0};
            {4'd0, 3'd2}: tw_step = {1'b0, 2'd2, TW_I, 2'd0};
            {4'd0, 3'd3}: tw_step = {1'b1, 2'd3, TW_I, 2'd0};
            {4'd1, 3'd0}: tw_step = {1'b0, 2'd0, TW_N, 2'd0};
            {4'd1, 3'd1}: tw_step = {1'b0, 2'd0, TW_N, 2'd3};
            {4'd1, 3'd2}: tw_step = {1'b0, 2'd1, TW_P, 2'd0};
            {4'd1, 3'd3}: tw_step = {1'b0, 2'd2, TW_N, 2'd0};
            {4'd1, 3'd4}: tw_step = {1'b0, 2'd2, TW_N, 2'd3};
            {4'd1, 3'd5}: tw_step = {1'b1, 2'd3, TW_P, 2'd0};
            {4'd2, 3'd0}: tw_step = {1'b0, 2'd1, TW_N, 2'd0};
            {4'd2, 3'd1}: tw_step = {1'b1, 2'd3, TW_N, 2'd0};
            {4'd3, 3'd0}: tw_step = {1'b0, 2'd0, TW_N, 2'd3};
            {4'd3, 3'd1}: tw_step = {1'b0, 2'd0, TW_N, 2'd0};
            {4'd3, 3'd2}: tw_step = {1'b0, 2'd1, TW_P, 2'd0};
            {4'd3, 3'd3}: tw_step = {1'b0, 2'd2, TW_P, 2'd0};
            {4'd3, 3'd4}: tw_step = {1'b1, 2'd3, TW_N, 2'd0};
            {4'd4, 3'd0}: tw_step = {1'b0, 2'd0, TW_N, 2'd3};
            {4'd4, 3'd1}: tw_step = {1'b0, 2'd0, TW_N, 2'd0};
            {4'd4, 3'd2}: tw_step = {1'b0, 2'd1, TW_N, 2'd0};
            {4'd4, 3'd3}: tw_step = {1'b0, 2'd1, TW_N, 2'd3};
            {4'd4, 3'd4}: tw_step = {1'b0, 2'd2, TW_N, 2'd0};
            {4'd4, 3'd5}: tw_step = {1'b0, 2'd2, TW_N, 2'd3};
            {4'd4, 3'd6}: tw_step = {1'b1, 2'd3, TW_P, 2'd0};
            {4'd5, 3'd0}: tw_step = {1'b0, 2'd0, TW_N, 2'd0};
            {4'd5, 3'd1}: tw_step = {1'b0, 2'd0, TW_N, 2'd3};
            {4'd5, 3'd2}: tw_step = {1'b1, 2'd3, TW_N, 2'd0};
            {4'd6, 3'd0}: tw_step = {1'b0, 2'd2, TW_N, 2'd0};
            {4'd6, 3'd1}: tw_step = {1'b1, 2'd3, TW_P, 2'd0};
            {4'd7, 3'd0}: tw_step = {1'b0, 2'd2, TW_N, 2'd0};
            {4'd7, 3'd1}: tw_step = {1'b0, 2'd2, TW_N, 2'd3};
            {4'd7, 3'd2}: tw_step = {1'b1, 2'd3, TW_P, 2'd0};
            {4'd8, 3'd0}: tw_step = {1'b1, 2'd3, TW_N, 2'd0};
            default:      tw_step = {1'b1, 2'd3, TW_P, 2'd0};
        endcase
    endfunction

    wire [1:0] em_limb  = rem[0] ? 2'd0 : rem[1] ? 2'd1 : rem[2] ? 2'd2 : 2'd3;
    wire [3:0] em_rest  = rem & (rem - 4'd1);
    wire       em_lastl = (em_rest == 4'd0);
    wire [6:0] em_st    = tw_step(pi, t[2:0]);
    wire       em_slast = em_st[6];
    wire [5:0] em_lane  = 6'd8 + {4'd0, em_st[5:4]};

    wire       full_rnd = (rnd < 5'd4) || (rnd >= 5'd26);
    wire [5:0] lreg     = dir ? 6'd36 : 6'd32;
    wire [5:0] rreg     = dir ? 6'd32 : 6'd36;
    wire       is_fp5   = (op == OP_FP5_MUL) || (op == OP_FP5_ADD) || (op == OP_FP5_SUB) || (op == OP_FP5_EQ);
    wire       is_add   = (op == OP_EADD) || (op == OP_FP5_ADD);
    wire       is_eq    = (op == OP_EEQ)  || (op == OP_FP5_EQ);
    wire [2:0] mov_lim  = (n == 3'd0) ? 3'd4 : n; // supports n = 1..5!
    wire [2:0] emc_lim  = (op == OP_FP5_MUL) ? 3'd5 : 3'd4;
    wire [5:0] emc_src  = (op == OP_FP5_MUL) ? 6'd7 : 6'd8;

    // Fp5 b-limb index j = (k + 5 - i) % 5, where pi = k (0..4) and rem = i (0..4)
    wire [3:0] f5_j = (rem <= pi) ? (pi - rem) : (pi + 4'd5 - rem);

    always_comb begin
        rd_addr   = '0;
        wr_en     = 1'b0;
        wr_addr   = '0;
        pm        = 2'd0;
        pk        = 4'd0;
        rm        = 3'd0;
        rk        = 2'd0;
        krc       = 1'b0;
        acc_clr   = 1'b0;
        acc_we    = 1'b0;
        ld_opa    = 1'b0;
        ld_opb    = 1'b0;
        ld_res    = 1'b0;
        mul_start = 1'b0;
        mul_asel  = 1'b0;
        mul_bsel  = 1'b0;
        rc_idx    = '0;
        unique case (st)
            S_ME_A: begin
                if (t < 5'd3) begin
                    rd_addr = 6'd3 * {3'd0, g} + {1'b0, t};
                    pm      = 2'd1;
                    acc_clr = (t == 5'd0);
                    acc_we  = 1'b1;
                end else if (t == 5'd3) begin
                    ld_res  = 1'b1;
                end else begin // t = 4..7
                    if (t <= 5'd6) begin
                        rd_addr = 6'd3 * {3'd0, g} + {1'b0, t} - 6'd4;
                        pm      = 2'd1;
                        rm      = 3'd1;
                        acc_clr = 1'b1;
                        acc_we  = 1'b1;
                    end
                    if (t >= 5'd5) begin
                        wr_en   = 1'b1;
                        wr_addr = 6'd3 * {3'd0, g} + {1'b0, t} - 6'd5;
                    end
                end
            end
            S_ME_B: begin
                if (t < 5'd4) begin
                    rd_addr = {3'd0, g} + 6'd3 * {4'd0, t[1:0]};
                    pm      = 2'd1;
                    acc_clr = (t == 5'd0);
                    acc_we  = 1'b1;
                    ld_opa  = (t == 5'd1); // OPA <= canonical b_0 from t=0!
                end else if (t == 5'd4) begin
                    ld_res  = 1'b1;        // RES <= canonical s from t=0..3!
                end else if (t == 5'd13) begin
                    wr_en   = 1'b1;
                    wr_addr = {3'd0, g} + 6'd9;
                end else if (t[0]) begin   // t = 5, 7, 9, 11 (i = 0, 1, 2, 3): acc <= b_i + s
                    logic [1:0] bi;
                    bi      = 2'((t - 5'd5) >> 1);
                    rd_addr = {3'd0, g} + 6'd3 * {4'd0, bi};
                    pm      = 2'd1;
                    rm      = 3'd1;
                    acc_clr = 1'b1;
                    acc_we  = 1'b1;
                    if (t >= 5'd7) begin
                        wr_en   = 1'b1;
                        wr_addr = {3'd0, g} + 6'd3 * {4'd0, bi - 2'd1};
                    end
                end else begin             // t = 6, 8, 10, 12 (i = 0, 1, 2, 3): acc += 2 * b_{i+1}
                    logic [1:0] bi;
                    bi     = 2'((t - 5'd6) >> 1);
                    acc_we = 1'b1;
                    if (t == 5'd12) begin
                        rm = 3'd2;
                        rk = 2'd1;
                    end else begin
                        rd_addr = {3'd0, g} + 6'd3 * {4'd0, bi + 2'd1};
                        pm      = 2'd1;
                        pk      = 4'd1;
                    end
                end
            end
            S_SB0: begin
                rd_addr = {2'd0, lane};
                pm      = 2'd1;
                krc     = 1'b1;
                acc_clr = 1'b1;
                acc_we  = 1'b1;
                if (full_rnd) rc_idx = ((rnd < 5'd4) ? 7'd12 * {2'd0, rnd} : 7'd48 + 7'd12 * ({2'd0, rnd} - 7'd26)) + {3'd0, lane};
                else          rc_idx = 7'd96 + ({2'd0, rnd} - 7'd4);
            end
            S_SB1: begin
                ld_opa = 1'b1;
                ld_opb = 1'b1;
            end
            S_SBM, S_SBW: begin
                mul_start = (st == S_SBM);
                mul_asel  = (q == 3'd2);
                mul_bsel  = (q != 3'd0);
                if (mul_last) begin
                    if (q == 3'd3) begin
                        wr_en   = 1'b1;
                        wr_addr = {2'd0, lane};
                    end else ld_res = 1'b1;
                end
            end
            S_MI: begin
                if (t < 5'd12) begin
                    rd_addr = {1'b0, t};
                    pm      = 2'd1;
                    acc_clr = (t == 5'd0);
                    acc_we  = 1'b1;
                end else if (t == 5'd12) begin
                    ld_res  = 1'b1;
                end else begin // t = 13..25
                    if (t <= 5'd24) begin
                        rd_addr = {1'b0, t} - 6'd13;
                        rm      = 3'd1;
                        acc_clr = 1'b1;
                        acc_we  = 1'b1;
                        if (t == 5'd13) begin
                            pm = 2'd2;
                            pk = 4'd6;
                        end else begin
                            pm = 2'd1;
                            pk = t[3:0] - 4'd14;
                        end
                    end
                    if (t >= 5'd14) begin
                        wr_en   = 1'b1;
                        wr_addr = {1'b0, t} - 6'd14;
                    end
                end
            end
            S_EM0, S_EM1: begin
                rd_addr = ((st == S_EM0) ? s1 : s2) + {4'd0, em_limb};
                pm      = 2'd1;
                acc_clr = em_first;
                acc_we  = 1'b1;
            end
            S_EM0L: ld_opa = 1'b1;
            S_EM1L: ld_opb = 1'b1;
            S_EM2:  mul_start = 1'b1;
            S_EM3:  ld_res = mul_last;
            S_EM4: begin
                if (!em_sub) begin
                    rd_addr = em_lane;
                    pm      = em_st[3:2];
                    rm      = 3'd1;
                    rk      = em_st[1:0];
                    acc_clr = 1'b1;
                    acc_we  = 1'b1;
                end else begin
                    wr_en   = 1'b1;
                    wr_addr = em_lane;
                end
            end
            // Fp5 schoolbook binomial product over F_p[X]/(X^5 - 3), accumulating into st[7..11]
            S_F5L: begin
                unique case (q[1:0])
                    2'd0: begin rd_addr = s1 + {2'd0, rem};  pm = 2'd1; acc_clr = 1'b1; acc_we = 1'b1; end
                    2'd1: begin ld_opa  = 1'b1; rd_addr = s2 + {2'd0, f5_j}; pm = 2'd1; acc_clr = 1'b1; acc_we = 1'b1; end
                    default: begin ld_opb = 1'b1; end
                endcase
            end
            S_F5M: begin
                mul_start = (q == 3'd0);
                ld_res    = mul_last;
            end
            S_F5A: begin
                if (!em_sub) begin
                    rd_addr = 6'd7 + {2'd0, pi};
                    pm      = (rem == 4'd0) ? 2'd0 : 2'd1;
                    rm      = (rem <= pi)   ? 3'd1 : 3'd5; // 1*RES if i <= k else 3*RES
                    acc_clr = 1'b1;
                    acc_we  = 1'b1;
                end else begin
                    wr_en   = 1'b1;
                    wr_addr = 6'd7 + {2'd0, pi};
                end
            end
            S_EMC: begin
                if (g < emc_lim) begin
                    rd_addr = emc_src + {3'd0, g};
                    pm      = 2'd1;
                    acc_clr = 1'b1;
                    acc_we  = 1'b1;
                end
                if (g >= 3'd1) begin
                    wr_en   = 1'b1;
                    wr_addr = d + {3'd0, g} - 6'd1;
                end
            end
            S_AS0: begin
                rd_addr = s1 + {3'd0, g};
                pm      = 2'd1;
                acc_clr = 1'b1;
                acc_we  = 1'b1;
            end
            S_AS1: begin
                rd_addr = s2 + {3'd0, g};
                pm      = is_add ? 2'd1 : 2'd2;
                acc_we  = 1'b1;
            end
            S_AS2: begin
                wr_en   = !is_eq;
                wr_addr = d + {3'd0, g};
            end
            S_ONE: begin
                acc_clr = 1'b1;
                acc_we  = 1'b1;
                unique case (op)
                    OP_ABSW: begin rd_addr = d;  pm = 2'd1; rm = 3'd4; end
                    OP_SETW: begin rm      = 3'd4; end
                    default: begin rd_addr = s1; pm = 2'd1; end
                endcase
            end
            S_ONEW: begin
                if (op == OP_LDRES) ld_res = 1'b1;
                else begin
                    wr_en   = 1'b1;
                    wr_addr = d;
                end
            end
            S_MOV: begin
                if (g < mov_lim) begin
                    rd_addr = s1 + {3'd0, g};
                    pm      = 2'd1;
                    acc_clr = 1'b1;
                    acc_we  = 1'b1;
                end
                if (g >= 3'd1) begin
                    wr_en   = 1'b1;
                    wr_addr = d + {3'd0, g} - 6'd1;
                end
            end
            S_FF: begin
                unique case (q)
                    3'd0: begin rd_addr = {3'd0, g};        pm = 2'd1; acc_clr = 1'b1; acc_we = 1'b1; end
                    3'd1: begin rd_addr = lreg + {3'd0, g}; pm = 2'd1; acc_we  = 1'b1; end
                    3'd2: begin rd_addr = rreg + {3'd0, g}; pm = 2'd1; pk = 4'd1; acc_we = 1'b1; end
                    3'd3: begin
                        acc_we = 1'b1;
                        if (g == 3'd0) begin rm = 3'd4; rk = 2'd2; end
                        else           begin rd_addr = s1 + {3'd0, g} - 6'd1; pm = 2'd1; pk = 4'd2; end
                    end
                    default: begin
                        wr_en   = 1'b1;
                        wr_addr = 6'd32 + {3'd0, g};
                    end
                endcase
            end
            default: ;
        endcase
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            st       <= S_IDLE;
            done     <= 1'b0;
            eq       <= 1'b0;
            t        <= '0;
            g        <= '0;
            q        <= '0;
            lane     <= '0;
            rnd      <= '0;
            first    <= 1'b0;
            pi       <= '0;
            rem      <= '0;
            em_first <= 1'b0;
            em_sub   <= 1'b0;
        end else begin
            done <= 1'b0;
            unique case (st)
                S_IDLE: if (start) begin
                    t      <= '0;
                    g      <= '0;
                    q      <= '0;
                    lane   <= '0;
                    rnd    <= '0;
                    em_sub <= 1'b0;
                    unique case (op)
                        OP_PERM: begin
                            st    <= S_ME_A;
                            first <= 1'b1;
                        end
                        OP_EMUL: begin
                            pi       <= 4'd0;
                            rem      <= tw_mask(4'd0);
                            em_first <= 1'b1;
                            st       <= S_EM0;
                        end
                        OP_FP5_MUL: begin
                            pi  <= 4'd0;
                            rem <= 4'd0;
                            st  <= S_F5L;
                        end
                        OP_EADD, OP_ESUB, OP_FP5_ADD, OP_FP5_SUB: st <= S_AS0;
                        OP_EEQ, OP_FP5_EQ: begin
                            st <= S_AS0;
                            eq <= 1'b1;
                        end
                        OP_MOV:                     st <= S_MOV;
                        OP_FFWD:                    st <= S_FF;
                        OP_ABSW, OP_SETW, OP_LDRES: st <= S_ONE;
                        default:                    done <= 1'b1;
                    endcase
                end
                S_ME_A: begin
                    if (t == 5'd7) begin
                        t <= '0;
                        if (g == 3'd3) begin
                            g  <= '0;
                            st <= S_ME_B;
                        end else g <= g + 3'd1;
                    end else t <= t + 5'd1;
                end
                S_ME_B: begin
                    if (t == 5'd13) begin
                        t <= '0;
                        if (g == 3'd2) begin
                            g <= '0;
                            if (first) begin
                                first <= 1'b0;
                                st    <= S_SB0;
                            end else if (rnd == 5'd29) begin
                                st   <= S_IDLE;
                                done <= 1'b1;
                            end else begin
                                rnd <= rnd + 5'd1;
                                st  <= S_SB0;
                            end
                        end else g <= g + 3'd1;
                    end else t <= t + 5'd1;
                end
                S_SB0: st <= S_SB1;
                S_SB1: begin
                    q  <= '0;
                    st <= S_SBM;
                end
                S_SBM: st <= S_SBW;
                S_SBW: if (mul_last) begin
                    q <= q + 3'd1;
                    if (q == 3'd3) begin
                        if (full_rnd && lane != 4'd11) begin
                            lane <= lane + 4'd1;
                            st   <= S_SB0;
                        end else begin
                            lane <= '0;
                            st   <= full_rnd ? S_ME_A : S_MI;
                        end
                    end else st <= S_SBM;
                end
                S_MI: begin
                    if (t == 5'd25) begin
                        t   <= '0;
                        rnd <= rnd + 5'd1;
                        st  <= S_SB0;
                    end else t <= t + 5'd1;
                end
                S_EM0, S_EM1: begin
                    rem      <= em_rest;
                    em_first <= 1'b0;
                    if (em_lastl) st <= (st == S_EM0) ? S_EM0L : S_EM1L;
                end
                S_EM0L: begin
                    rem      <= tw_mask(pi);
                    em_first <= 1'b1;
                    st       <= S_EM1;
                end
                S_EM1L: st <= S_EM2;
                S_EM2:  st <= S_EM3;
                S_EM3: if (mul_last) begin
                    t      <= '0;
                    em_sub <= 1'b0;
                    st     <= S_EM4;
                end
                S_EM4: begin
                    if (!em_sub) em_sub <= 1'b1;
                    else begin
                        em_sub <= 1'b0;
                        if (!em_slast) t <= t + 5'd1;
                        else begin
                            t <= '0;
                            if (pi == 4'd8) begin
                                g  <= '0;
                                st <= S_EMC;
                            end else begin
                                pi       <= pi + 4'd1;
                                rem      <= tw_mask(pi + 4'd1);
                                em_first <= 1'b1;
                                st       <= S_EM0;
                            end
                        end
                    end
                end
                S_F5L: begin
                    if (q == 3'd2) begin
                        q  <= 3'd0;
                        st <= S_F5M;
                    end else q <= q + 3'd1;
                end
                S_F5M: begin
                    if (q == 3'd0) q <= 3'd1;
                    else if (mul_last) begin
                        q      <= 3'd0;
                        em_sub <= 1'b0;
                        st     <= S_F5A;
                    end
                end
                S_F5A: begin
                    if (!em_sub) em_sub <= 1'b1;
                    else begin
                        em_sub <= 1'b0;
                        if (rem == 4'd4) begin
                            rem <= 4'd0;
                            if (pi == 4'd4) begin
                                g  <= '0;
                                st <= S_EMC;
                            end else begin
                                pi <= pi + 4'd1;
                                st <= S_F5L;
                            end
                        end else begin
                            rem <= rem + 4'd1;
                            st  <= S_F5L;
                        end
                    end
                end
                S_EMC: begin
                    if (g == emc_lim) begin
                        st   <= S_IDLE;
                        done <= 1'b1;
                    end else g <= g + 3'd1;
                end
                S_MOV: begin
                    if (g == mov_lim) begin
                        st   <= S_IDLE;
                        done <= 1'b1;
                    end else g <= g + 3'd1;
                end
                S_AS0: st <= S_AS1;
                S_AS1: st <= S_AS2;
                S_AS2: begin
                    if (is_eq && !cv_zero) eq <= 1'b0;
                    if (g == (is_fp5 ? 3'd4 : 3'd3)) begin
                        st   <= S_IDLE;
                        done <= 1'b1;
                    end else begin
                        g  <= g + 3'd1;
                        st <= S_AS0;
                    end
                end
                S_ONE:  st <= S_ONEW;
                S_ONEW: begin
                    st   <= S_IDLE;
                    done <= 1'b1;
                end
                S_FF: begin
                    if (q == 3'd4) begin
                        q <= 3'd0;
                        if (g == 3'd3) begin
                            st   <= S_IDLE;
                            done <= 1'b1;
                        end else g <= g + 3'd1;
                    end else q <= q + 3'd1;
                end
                default: st <= S_IDLE;
            endcase
        end
    end
endmodule
`default_nettype wire

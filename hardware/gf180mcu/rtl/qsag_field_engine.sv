// QSAG-NI-180 field engine: micro-sequencer that drives the single Goldilocks arithmetic unit
// over the sponge register file.
//
// Register file addresses: 0..11 Poseidon2 state (scratch T0 = 0..3, T1 = 4..7 between hashes),
// 12..15 CH, 16..19 A, 20..23 B, 24 spare, 32..35 X, 36..39 Y.
// GoldilocksExt4 elements are four limbs [c0.c0, c0.c1, c1.c0, c1.c1] = coefficients of
// [v^0, v^2, v^1, v^3] in F_p[v]/(v^4 - 7).
//
// Operations (start pulse, done pulse; arguments must be held until done):
//   PERM          Poseidon2 width-12 permutation of lanes 0..11            3,074 cycles
//   ABSW  d       lane[d] <- lane[d] + xw                                  (sponge absorb)
//   SETW  d       lane[d] <- xw mod p
//   MOV   d,s1,n  lane[d+i] <- lane[s1+i], i < n (n = 0 means 4)
//   EMUL  d,s1,s2 Ext4 product (16 base multiplies, clobbers lanes 4..7)   122 cycles
//   EADD/ESUB     Ext4 sum / difference
//   EEQ   s1,s2   eq <- (s1 == s2) over four limbs
//   FFWD  s1,dir  Canopy feed-forward X <- st[0..3] + L + 2R + 4C, C = [xw, key(s1)[0..2]],
//                 (L, R) = dir ? (Y, X) : (X, Y)
//   LDRES s1      RES <- lane[s1] mod p
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
    // register file
    output logic [5:0]  rd_addr,
    output logic        wr_en,
    output logic [5:0]  wr_addr,
    // arithmetic unit
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
    localparam logic [3:0] OP_PERM = 4'd1, OP_ABSW = 4'd2, OP_SETW = 4'd3, OP_MOV = 4'd4,
                           OP_EMUL = 4'd5, OP_EADD = 4'd6, OP_ESUB = 4'd7, OP_EEQ = 4'd8,
                           OP_FFWD = 4'd9, OP_LDRES = 4'd10;

    localparam logic [4:0] S_IDLE = 5'd0,  S_ME_A = 5'd1,  S_ME_B = 5'd2,  S_SB0 = 5'd3,
                           S_SBM = 5'd4,   S_SBW = 5'd5,   S_MI = 5'd6,    S_EM0 = 5'd7,
                           S_EM1 = 5'd8,   S_EM2 = 5'd9,   S_EM3 = 5'd10,  S_EM4 = 5'd11,
                           S_EM5 = 5'd12,  S_EM6 = 5'd13,  S_EMC = 5'd14,  S_AS0 = 5'd15,
                           S_AS1 = 5'd16,  S_ONE = 5'd17,  S_MOV = 5'd18,  S_FF = 5'd19;

    logic [4:0] st;
    logic [4:0] t;      // step within a linear layer
    logic [1:0] g;      // group / block / Ext4 limb / coefficient
    logic [1:0] q;      // product order, multiply index, feed-forward step
    logic [3:0] lane;
    logic [4:0] rnd;
    logic       first;

    assign busy = (st != S_IDLE);

    function automatic logic [5:0] lmap(input logic [1:0] m);
        case (m)
            2'd1:    lmap = 6'd2;
            2'd2:    lmap = 6'd1;
            default: lmap = {4'd0, m};
        endcase
    endfunction

    wire        full_rnd = (rnd < 5'd4) || (rnd >= 5'd26);
    wire [1:0]  em_i     = g + 2'd1 + q;          // multiplicand limb of product q for coefficient g
    wire [1:0]  em_j     = g - em_i;
    wire [5:0]  em_t     = 6'd4 + {4'd0, g};
    wire        em_x7    = (g != 2'd3) && (q == 2'd2 - g);
    wire [5:0]  lreg     = dir ? 6'd36 : 6'd32;
    wire [5:0]  rreg     = dir ? 6'd32 : 6'd36;

    // -------------------------------------------------------------------- control decode
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
            S_ME_A: begin  // lanes 3g..3g+2: add their sum G_g to each
                pm = 2'd1;
                if (t < 5'd3) begin
                    rd_addr = 6'd3 * {4'd0, g} + {4'd0, t[1:0]};
                    acc_clr = (t == 5'd0);
                    acc_we  = 1'b1;
                    ld_res  = (t == 5'd2);
                end else begin
                    rd_addr = 6'd3 * {4'd0, g} + {1'b0, t} - 6'd3;
                    rm      = 3'd1;
                    acc_clr = 1'b1;
                    wr_en   = 1'b1;
                    wr_addr = rd_addr;
                end
            end
            S_ME_B: begin  // block g (lanes g, g+3, g+6, g+9): out_i = s + b_i + 2 b_{i+1}
                if (t < 5'd4) begin
                    rd_addr = {4'd0, g} + 6'd3 * {4'd0, t[1:0]};
                    pm      = 2'd1;
                    acc_clr = (t == 5'd0);
                    acc_we  = 1'b1;
                    ld_opa  = (t == 5'd0);
                    ld_res  = (t == 5'd3);
                end else if (!t[0]) begin  // t = 4, 6, 8, 10: b_i + s
                    rd_addr = {4'd0, g} + 6'd3 * {4'd0, t[2:1] - 2'd2};
                    pm      = 2'd1;
                    rm      = 3'd1;
                    acc_clr = 1'b1;
                    acc_we  = 1'b1;
                end else begin             // t = 5, 7, 9, 11: + 2 b_{i+1}
                    wr_en   = 1'b1;
                    wr_addr = {4'd0, g} + 6'd3 * {4'd0, t[2:1] - 2'd2};
                    if (t == 5'd11) begin
                        rm = 3'd2;
                        rk = 2'd1;
                    end else begin
                        rd_addr = {4'd0, g} + 6'd3 * {4'd0, t[2:1] - 2'd1};
                        pm      = 2'd1;
                        pk      = 4'd1;
                    end
                end
            end
            S_SB0: begin  // t = x + rc -> OPA, OPB
                rd_addr = {2'd0, lane};
                pm      = 2'd1;
                krc     = 1'b1;
                acc_clr = 1'b1;
                ld_opa  = 1'b1;
                ld_opb  = 1'b1;
                if (full_rnd) rc_idx = ((rnd < 5'd4) ? 7'd12 * {2'd0, rnd} : 7'd48 + 7'd12 * ({2'd0, rnd} - 7'd26)) + {3'd0, lane};
                else          rc_idx = 7'd96 + ({2'd0, rnd} - 7'd4);
            end
            S_SBM, S_SBW: begin  // t^2, t^3, t^6, t^7
                mul_start = (st == S_SBM);
                mul_asel  = (q != 2'd0);
                mul_bsel  = (q == 2'd2);
                if (mul_last) begin
                    if (q == 2'd3) begin
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
                    ld_res  = (t == 5'd11);
                end else begin
                    rd_addr = {1'b0, t} - 6'd12;
                    rm      = 3'd1;
                    acc_clr = 1'b1;
                    wr_en   = 1'b1;
                    wr_addr = rd_addr;
                    if (t == 5'd12) begin
                        pm = 2'd2;
                        pk = 4'd6;
                    end else begin
                        pm = 2'd1;
                        pk = t[3:0] - 4'd13;
                    end
                end
            end
            S_EM0: begin
                rd_addr = s1 + lmap(em_i);
                pm      = 2'd1;
                acc_clr = 1'b1;
                ld_opa  = 1'b1;
            end
            S_EM1: begin
                rd_addr = s2 + lmap(em_j);
                pm      = 2'd1;
                acc_clr = 1'b1;
                ld_opb  = 1'b1;
            end
            S_EM2: mul_start = 1'b1;
            S_EM3: ld_res = mul_last;
            S_EM4: begin
                rd_addr = em_t;
                pm      = (q == 2'd0) ? 2'd0 : 2'd1;
                rm      = 3'd1;
                acc_clr = 1'b1;
                wr_en   = 1'b1;
                wr_addr = em_t;
            end
            S_EM5: begin  // 8x
                rd_addr = em_t;
                pm      = 2'd1;
                pk      = 4'd3;
                acc_clr = 1'b1;
                acc_we  = 1'b1;
            end
            S_EM6: begin  // - x
                rd_addr = em_t;
                pm      = 2'd2;
                wr_en   = 1'b1;
                wr_addr = em_t;
            end
            S_EMC: begin
                rd_addr = 6'd4 + lmap(g);
                pm      = 2'd1;
                acc_clr = 1'b1;
                wr_en   = 1'b1;
                wr_addr = d + {4'd0, g};
            end
            S_AS0: begin
                rd_addr = s1 + {4'd0, g};
                pm      = 2'd1;
                acc_clr = 1'b1;
                acc_we  = 1'b1;
            end
            S_AS1: begin
                rd_addr = s2 + {4'd0, g};
                pm      = (op == OP_EADD) ? 2'd1 : 2'd2;
                wr_en   = (op != OP_EEQ);
                wr_addr = d + {4'd0, g};
            end
            S_ONE: begin
                acc_clr = 1'b1;
                unique case (op)
                    OP_ABSW: begin
                        rd_addr = d;
                        pm      = 2'd1;
                        rm      = 3'd4;
                        wr_en   = 1'b1;
                        wr_addr = d;
                    end
                    OP_SETW: begin
                        rm      = 3'd4;
                        wr_en   = 1'b1;
                        wr_addr = d;
                    end
                    default: begin  // LDRES
                        rd_addr = s1;
                        pm      = 2'd1;
                        ld_res  = 1'b1;
                    end
                endcase
            end
            S_MOV: begin
                rd_addr = s1 + {4'd0, g};
                pm      = 2'd1;
                acc_clr = 1'b1;
                wr_en   = 1'b1;
                wr_addr = d + {4'd0, g};
            end
            S_FF: begin
                acc_we = 1'b1;
                unique case (q)
                    2'd0: begin
                        rd_addr = {4'd0, g};
                        pm      = 2'd1;
                        acc_clr = 1'b1;
                    end
                    2'd1: begin
                        rd_addr = lreg + {4'd0, g};
                        pm      = 2'd1;
                    end
                    2'd2: begin
                        rd_addr = rreg + {4'd0, g};
                        pm      = 2'd1;
                        pk      = 4'd1;
                    end
                    default: begin
                        if (g == 2'd0) begin
                            rm = 3'd4;
                            rk = 2'd2;
                        end else begin
                            rd_addr = s1 + {4'd0, g} - 6'd1;
                            pm      = 2'd1;
                            pk      = 4'd2;
                        end
                        wr_en   = 1'b1;
                        wr_addr = 6'd32 + {4'd0, g};
                    end
                endcase
            end
            default: ;
        endcase
    end

    // -------------------------------------------------------------------- sequencing
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            st    <= S_IDLE;
            done  <= 1'b0;
            eq    <= 1'b0;
            t     <= '0;
            g     <= '0;
            q     <= '0;
            lane  <= '0;
            rnd   <= '0;
            first <= 1'b0;
        end else begin
            done <= 1'b0;
            unique case (st)
                S_IDLE: if (start) begin
                    t    <= '0;
                    g    <= '0;
                    q    <= '0;
                    lane <= '0;
                    rnd  <= '0;
                    unique case (op)
                        OP_PERM: begin
                            st    <= S_ME_A;
                            first <= 1'b1;
                        end
                        OP_EMUL:                    st <= S_EM0;
                        OP_EADD, OP_ESUB:           st <= S_AS0;
                        OP_EEQ: begin
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
                    if (t == 5'd5) begin
                        t <= '0;
                        g <= g + 2'd1;
                        if (g == 2'd3) begin
                            g  <= '0;
                            st <= S_ME_B;
                        end
                    end else t <= t + 5'd1;
                end
                S_ME_B: begin
                    if (t == 5'd11) begin
                        t <= '0;
                        if (g == 2'd2) begin
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
                        end else g <= g + 2'd1;
                    end else t <= t + 5'd1;
                end
                S_SB0: begin
                    q  <= '0;
                    st <= S_SBM;
                end
                S_SBM: st <= S_SBW;
                S_SBW: if (mul_last) begin
                    q <= q + 2'd1;
                    if (q == 2'd3) begin
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
                    if (t == 5'd23) begin
                        t   <= '0;
                        rnd <= rnd + 5'd1;
                        st  <= S_SB0;
                    end else t <= t + 5'd1;
                end
                S_EM0: st <= S_EM1;
                S_EM1: st <= S_EM2;
                S_EM2: st <= S_EM3;
                S_EM3: if (mul_last) st <= S_EM4;
                S_EM4: begin
                    if (em_x7) st <= S_EM5;
                    else begin
                        q <= q + 2'd1;
                        if (q == 2'd3) begin
                            g  <= g + 2'd1;
                            st <= (g == 2'd3) ? S_EMC : S_EM0;
                        end else st <= S_EM0;
                    end
                end
                S_EM5: st <= S_EM6;
                S_EM6: begin
                    q  <= q + 2'd1;
                    st <= S_EM0;
                end
                S_EMC, S_MOV: begin
                    g <= g + 2'd1;
                    if ((st == S_EMC) ? (g == 2'd3) : ({1'b0, g} + 3'd1 == n || g == 2'd3)) begin
                        st   <= S_IDLE;
                        done <= 1'b1;
                    end
                end
                S_AS0: st <= S_AS1;
                S_AS1: begin
                    if (op == OP_EEQ && !cv_zero) eq <= 1'b0;
                    g <= g + 2'd1;
                    if (g == 2'd3) begin
                        st   <= S_IDLE;
                        done <= 1'b1;
                    end else st <= S_AS0;
                end
                S_ONE: begin
                    st   <= S_IDLE;
                    done <= 1'b1;
                end
                S_FF: begin
                    q <= q + 2'd1;
                    if (q == 2'd3) begin
                        g <= g + 2'd1;
                        if (g == 2'd3) begin
                            st   <= S_IDLE;
                            done <= 1'b1;
                        end
                    end
                end
                default: st <= S_IDLE;
            endcase
        end
    end
endmodule
`default_nettype wire

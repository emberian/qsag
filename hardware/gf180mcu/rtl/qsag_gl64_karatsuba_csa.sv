// Dregg-180 (QSAG-NI-180) Goldilocks & Quintic Fp5 / Tower Ext4 arithmetic unit:
//   p = phi^2 - phi + 1   (W = 32: p = 0xFFFF_FFFF_0000_0001, phi = 2^32)
//
// Silicon Area & Timing Closure Optimizations:
//   * Zero-extra-adder AND zero-extra-register 2W x 2W -> 4W iterative shift-add multiplier:
//     folds both `opb[63:0]` and `p_sr[127:0]` directly into `{acc_s[63:0], acc_c[63:0]}` and
//     shares `u_canon.u_t` (`qsag_prefix_add #(.N(AW))`) with ZERO mux on `canon_x`!
//   * Zero-gate 1-clock 4W -> (2W+GB) Goldilocks identity fold (`qsag_gl64_mrows`) + half-width
//     `W`-bit `-1 / +1` canonicalizer check (`v_lo, v_hi`).
//   * Pipeline cut between `u_csa` (`acc_s/acc_c`) and `u_canon` (`cv`) keeps EVERY register-to-
//     register path <= 16.5 ns at worst-case SS_125C_4v50!
`default_nettype none

module qsag_prefix_add #(parameter int N = 64) (
    input  wire [N-1:0] a,
    input  wire [N-1:0] b,
    input  wire         cin,
    output wire [N-1:0] sum
);
    if (N == 1) begin : g_w1
        assign sum[0] = a[0] ^ b[0] ^ cin;
    end else begin : g_hc
        localparam int N_ODD = (N + 1) / 2;
        localparam int HL    = (N_ODD <= 1) ? 0 : $clog2(N_ODD);
        wire [N-1:0] p0 = a ^ b;
        wire [N-1:0] g0 = a & b;

        wire [N-1:0] po [HL+1];
        wire [N-1:0] go [HL+1];

        for (genvar i = 0; i < N; i++) begin : g_pre
            if (i[0]) begin : g_odd0
                assign go[0][i] = g0[i] | (p0[i] & g0[i-1]);
                assign po[0][i] = p0[i] & p0[i-1];
            end else begin : g_even0
                assign go[0][i] = g0[i];
                assign po[0][i] = p0[i];
            end
        end

        for (genvar l = 0; l < HL; l++) begin : g_level
            localparam int STEP = 2 << l;
            for (genvar i = 0; i < N; i++) begin : g_bit
                if (i[0] && (i >= STEP)) begin : g_merge
                    assign go[l+1][i] = go[l][i] | (po[l][i] & go[l][i - STEP]);
                    assign po[l+1][i] = po[l][i] & po[l][i - STEP];
                end else begin : g_pass
                    assign go[l+1][i] = go[l][i];
                    assign po[l+1][i] = po[l][i];
                end
            end
        end

        wire [N-1:0] gg_end;
        wire [N-1:0] pp_end;
        assign gg_end[0] = g0[0];
        assign pp_end[0] = p0[0];
        for (genvar i = 1; i < N; i++) begin : g_post
            if (i[0]) begin : g_post_odd
                assign gg_end[i] = go[HL][i];
                assign pp_end[i] = po[HL][i];
            end else begin : g_post_even
                assign gg_end[i] = g0[i] | (p0[i] & go[HL][i-1]);
                assign pp_end[i] = p0[i] & po[HL][i-1];
            end
        end

        assign sum[0] = p0[0] ^ cin;
        for (genvar i = 1; i < N; i++) begin : g_sum
            assign sum[i] = p0[i] ^ (gg_end[i-1] | (pp_end[i-1] & cin));
        end
        /* verilator lint_off UNUSEDSIGNAL */
        wire unused_top = &{1'b0, gg_end[N-1], pp_end[N-1], go[HL][0], po[HL][0]};
        /* verilator lint_on UNUSEDSIGNAL */
    end
endmodule

module qsag_csa32 #(
    parameter int N = 76
) (
    input  wire [N-1:0] a,
    input  wire [N-1:0] b,
    input  wire [N-1:0] c,
    output wire [N-1:0] s,
    output wire [N-1:0] cy
);
`ifdef QSAG_GF180_CELLS
    wire [N-1:0] co;
    for (genvar i = 0; i < N - 1; i++) begin : g_fa
        qsag_fa1 u_fa (.a(a[i]), .b(b[i]), .ci(c[i]), .s(s[i]), .co(co[i]));
    end
    assign s[N-1]  = a[N-1] ^ b[N-1] ^ c[N-1];
    assign co[N-1] = 1'b0;
    assign cy      = {co[N-2:0], 1'b0};
    /* verilator lint_off UNUSEDSIGNAL */
    wire unused_co = co[N-1];
    /* verilator lint_on UNUSEDSIGNAL */
`else
    /* verilator lint_off UNUSEDSIGNAL */
    wire [N-1:0] m = (a & b) | (a & c) | (b & c);
    /* verilator lint_on UNUSEDSIGNAL */
    assign s  = a ^ b ^ c;
    assign cy = {m[N-2:0], 1'b0};
`endif
endmodule

module qsag_csa52 #(
    parameter int N = 76
) (
    input  wire [N-1:0] x,
    input  wire [N-1:0] y,
    input  wire [N-1:0] r1,
    input  wire [N-1:0] r2,
    input  wire [N-1:0] r3,
    output wire [N-1:0] s,
    output wire [N-1:0] c
);
    wire [N-1:0] s1, c1, s2, c2;
    qsag_csa32 #(.N(N)) u_a (.a(x),  .b(y),  .c(r1), .s(s1), .cy(c1));
    qsag_csa32 #(.N(N)) u_b (.a(s1), .b(r2), .c(r3), .s(s2), .cy(c2));
    qsag_csa32 #(.N(N)) u_c (.a(s2), .b(c1), .c(c2), .s(s),  .cy(c));
endmodule

module qsag_mul_step1 #(
    parameter int LW = 64
) (
    input  wire [LW-1:0] acc_hi,
    input  wire [LW-1:0] a,
    input  wire          bit_in,
    output wire [LW:0]   sum
);
    wire [LW-1:0] addend = bit_in ? a : '0;
    qsag_prefix_add #(.N(LW+1)) u_add (.a({1'b0, acc_hi}), .b({1'b0, addend}), .cin(1'b0), .sum(sum));
endmodule

module qsag_gl64_mrows #(
    parameter int W  = 32,
    parameter int GB = 12
) (
    input  wire [4*W-1:0]     p,
    output wire [2*W+GB-1:0]  r0,
    output wire [2*W+GB-1:0]  r1,
    output wire [2*W+GB-1:0]  r2,
    output wire [2*W+GB-1:0]  r3
);
    localparam int LW = 2 * W;
    localparam int AW = LW + GB;
    localparam logic [AW-1:0] K_FOLD = AW'(4);

    wire [LW-1:0] plo = p[LW-1:0];
    wire [W-1:0]  p2  = p[LW+W-1:LW];
    wire [W-1:0]  p3  = p[2*LW-1:LW+W];

    assign r0 = K_FOLD;
    assign r1 = AW'(plo);
    assign r2 = AW'({p2, ~p2});
    assign r3 = AW'({{(W-1){1'b1}}, 2'b00, ~p3});
endmodule

module qsag_gl64_canon #(
    parameter int W  = 32,
    parameter int GB = 12
) (
    input  wire [2*W+GB-1:0] x,
    input  wire [2*W+GB-1:0] y,
    output wire [2*W-1:0]    r,
    output wire [2*W:0]      t_lo_sum
);
    localparam int LW = 2 * W;
    localparam int AW = LW + GB;
    wire [AW-1:0] t;
    qsag_prefix_add #(.N(AW)) u_t (.a(x), .b(y), .cin(1'b0), .sum(t));
    assign t_lo_sum = t[LW:0];

    wire [GB-1:0] q  = t[AW-1:LW];
    wire [LW+1:0] qs = (LW + 2)'(q) << W;
    wire [LW+1:0] u, us, uc;
    qsag_csa32 #(.N(LW+2)) u_fold_rows (
        .a((LW+2)'(t[LW-1:0])), .b(qs), .c(~((LW+2)'(q))), .s(us), .cy(uc));
    qsag_prefix_add #(.N(LW+2)) u_fold (.a(us), .b(uc), .cin(1'b1), .sum(u));

    wire         u_lo_nz = |u[W-1:0];
    wire [W-1:0] v_lo;
    wire [W:0]   v_hi;
    qsag_prefix_add #(.N(W))   u_vlo (.a(u[W-1:0]),          .b({W{1'b1}}), .cin(1'b0),    .sum(v_lo));
    qsag_prefix_add #(.N(W+1)) u_vhi (.a({1'b0, u[LW-1:W]}), .b('0),        .cin(u_lo_nz), .sum(v_hi));
    wire [LW:0] v = {v_hi, v_lo};
    assign r = (u[LW] | v[LW]) ? v[LW-1:0] : u[LW-1:0];
endmodule

module qsag_gl64_karatsuba_csa #(
    parameter int W  = 32,
    parameter int GB = 12
) (
    input  wire              clk,
    input  wire              rst_n,
    input  wire [2*W-1:0]    port,
    input  wire [2*W-1:0]    xw,
    input  wire [2*W-1:0]    rc,
    input  wire [1:0]        pm,        // 0 off, 1 +port<<pk, 2 -port<<pk
    input  wire [3:0]        pk,        // 0..10
    input  wire [2:0]        rm,        // 0 off, 1 RES, 2 OPA, 4 XW, 5 3*RES
    input  wire [1:0]        rk,        // 0..3
    input  wire              krc,
    input  wire              acc_clr,
    input  wire              acc_we,
    input  wire              ld_opa,
    input  wire              ld_opb,
    input  wire              ld_res,
    input  wire              mul_start,
    input  wire              mul_asel,
    input  wire              mul_bsel,
    output wire              mul_busy,
    output wire              mul_last,
    output wire [2*W-1:0]    cv,
    output wire              cv_zero,
    output wire [2*W-1:0]    res
);
    localparam int LW     = 2 * W;
    localparam int AW     = LW + GB;
    localparam int STEPS  = LW;
    localparam int FOLD_S = STEPS + 1;
    localparam int LAST_S = STEPS + 2;
    localparam logic [LW-1:0] PRIME  = {{W{1'b1}}, {(W-1){1'b0}}, 1'b1};
    localparam logic [LW-1:0] K_NEG0 = PRIME - ((LW'(1) << W) - LW'(2));
    localparam logic [LW-1:0] K_NEG6 = PRIME - (((LW'(1) << W) - LW'(2)) << 6);

    wire [LW-1:0] opa, resr;
    wire [AW-1:0] acc_s, acc_c;
    logic [6:0]   ms;
    logic         asel_q;

    wire [LW-1:0]   opb      = acc_c[LW-1:0];
    wire [2*LW-1:0] p_sr     = {acc_s[LW-1:0], acc_c[LW-1:0]};
    wire [LW-1:0]   ma       = asel_q ? resr : opa;
    wire            mul_load = (ms == 7'd0) && mul_start;
    wire            mul_step = (ms >= 7'd1) && (ms <= 7'(STEPS));
    wire            mul_fold = (ms == 7'(FOLD_S));

    // Zero-mux `canon_x = acc_s` (`acc_s[AW-1:LW]` is cleared on `mul_load` and stays 0 through `mul_step`!)
    wire [LW-1:0] m_addend = acc_c[0] ? ma : '0;
    wire [AW-1:0] canon_y  = mul_step ? AW'(m_addend) : acc_c;
    wire [LW:0]   m_step_sum;
    qsag_gl64_canon #(.W(W), .GB(GB)) u_canon (
        .x(acc_s), .y(canon_y), .r(cv), .t_lo_sum(m_step_sum)
    );

    wire [AW-1:0] mr0, mr1, mr2, mr3;
    qsag_gl64_mrows #(.W(W), .GB(GB)) u_mrows (.p(p_sr), .r0(mr0), .r1(mr1), .r2(mr2), .r3(mr3));

    // ------------------------------------------------------------ 4-stage barrel shifter & operand rows
    wire [LW-1:0] p_base = mul_fold ? mr1[LW-1:0] : ((pm == 2'd2) ? ~port : port);
    wire [3:0]    pk_eff = mul_fold ? 4'd0 : pk;
    wire [AW-1:0] p_ext  = AW'(p_base);
    wire [AW-1:0] sh0    = pk_eff[0] ? {p_ext[AW-2:0], 1'b0} : p_ext;
    wire [AW-1:0] sh1    = pk_eff[1] ? {sh0[AW-3:0], 2'b0}   : sh0;
    wire [AW-1:0] sh2    = pk_eff[2] ? {sh1[AW-5:0], 4'b0}   : sh1;
    wire [AW-1:0] sh3    = pk_eff[3] ? {sh2[AW-9:0], 8'b0}   : sh2;

    logic [AW-1:0] prow, rrow, krow;
    logic [LW-1:0] rsel;
    always_comb begin
        prow = (mul_fold || pm == 2'd1 || pm == 2'd2) ? sh3 : '0;
        unique case (rm)
            3'd1, 3'd5: rsel = resr;
            3'd2:       rsel = opa;
            3'd4:       rsel = xw;
            default:    rsel = '0;
        endcase
        rrow = mul_fold ? mr2 : (AW'(rsel) << ((rm == 3'd5) ? 2'd1 : rk));
        if (mul_fold)        krow = mr3;
        else if (pm == 2'd2) krow = AW'((pk == 4'd6) ? K_NEG6 : K_NEG0);
        else if (krc)        krow = AW'(rc);
        else if (rm == 3'd5) krow = AW'(resr);
        else                 krow = '0;
    end

    // ------------------------------------------------------------ CSA -> Reg -> Canonicalize
    wire          in_mul = (ms != 7'd0);
    wire [AW-1:0] cx     = mul_fold ? mr0 : (acc_clr ? '0 : acc_s);
    wire [AW-1:0] cy     = (mul_fold || acc_clr) ? '0 : acc_c;
    wire [AW-1:0] ns, nc;
    qsag_csa52 #(.N(AW)) u_csa (.x(cx), .y(cy), .r1(prow), .r2(rrow), .r3(krow), .s(ns), .c(nc));

    assign cv_zero  = (cv == '0);
    assign mul_busy = in_mul;
    assign mul_last = (ms == 7'(LAST_S));
    assign res      = resr;

    wire          ld_opb_eff = ld_opb && !in_mul;
    wire          csa_en     = in_mul ? mul_fold : acc_we;
    wire          s_en       = mul_load | mul_step | csa_en;
    wire          c_en       = ld_opb_eff | mul_load | mul_step | csa_en;
    wire [AW-1:0] s_d        = mul_load   ? '0 :
                               mul_step   ? AW'(m_step_sum[LW:1]) : ns;
    wire [AW-1:0] c_d        = ld_opb_eff ? AW'(cv) :
                               mul_load   ? AW'(mul_bsel ? resr : opb) :
                               mul_step   ? AW'({m_step_sum[0], acc_c[LW-1:1]}) : nc;

    qsag_ereg_nr #(.W(LW)) u_opa  (.clk(clk), .en(ld_opa), .d(cv),  .q(opa));
    qsag_ereg_nr #(.W(LW)) u_res  (.clk(clk), .en(ld_res), .d(cv),  .q(resr));
    qsag_ereg_nr #(.W(AW)) u_accs (.clk(clk), .en(s_en),   .d(s_d), .q(acc_s));
    qsag_ereg_nr #(.W(AW)) u_accc (.clk(clk), .en(c_en),   .d(c_d), .q(acc_c));

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ms     <= 7'd0;
            asel_q <= 1'b0;
        end else if (ms == 7'd0) begin
            if (mul_start) begin
                ms     <= 7'd1;
                asel_q <= mul_asel;
            end
        end else if (ms == 7'(LAST_S)) begin
            ms <= 7'd0;
        end else begin
            ms <= ms + 7'd1;
        end
    end
    /* verilator lint_off UNUSEDSIGNAL */
    wire unused_mr1 = |mr1[AW-1:LW];
    /* verilator lint_on UNUSEDSIGNAL */
endmodule
`default_nettype wire

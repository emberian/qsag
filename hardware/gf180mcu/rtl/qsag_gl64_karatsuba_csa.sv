// Dregg-180 (QSAG-NI-180) Goldilocks arithmetic unit:
//   p = phi^2 - phi + 1   (W = 32: p = 0xFFFF_FFFF_0000_0001, phi = 2^32)
//   phi^2 = phi - 1,  phi^3 = -1   (mod p)
//
// All wide ripple-carry chains are replaced by Han-Carlson parallel-prefix carry networks
// (qsag_prefix_add, <= 16 gate levels at W=32) formally proven in lec/run_prefix_lec.py.
// Also provides:
//   * qsag_gl64_sq_comb   5-row 1-cycle Goldilocks squarer (x^2 mod p)
//   * qsag_gl64_mul_pipe  2-stage pipelined (1/clk throughput) Karatsuba Goldilocks multiplier
`default_nettype none

// Han-Carlson parallel-prefix carry network (radix-2 Kogge-Stone on odd positions + 1 post-pass
// to even positions). N >= 1 arbitrary. Gate depth <= 2*ceil(log2(N)) + 4 (~16 levels at N=76),
// with half the prefix cells of full Kogge-Stone and zero dead-wire keep bloat.
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

module qsag_mul33 #(
    parameter int W = 32
) (
    input  wire [W:0]     a,
    input  wire [W:0]     b,
    output wire [2*W+1:0] p
);
    localparam int N  = W + 1;
    localparam int PW = 2 * N;
    localparam int R  = (N + 2) / 2;
    wire [N+1:0] ap = {2'b0, a};
    wire [N+1:0] an;
    qsag_prefix_add #(.N(N+2)) u_neg (.a(~ap), .b({(N+2){1'b0}}), .cin(1'b1), .sum(an));
    wire [2*R:0] bx = {{(2*R-N){1'b0}}, b, 1'b0};
    wire [R*PW-1:0] rows;
    for (genvar j = 0; j < R; j++) begin : g_booth
        logic [N+1:0] digit;
        always_comb begin
            case (bx[2*j +: 3])
                3'b001, 3'b010: digit = ap;
                3'b011:         digit = ap << 1;
                3'b100:         digit = an << 1;
                3'b101, 3'b110: digit = an;
                default:        digit = '0;
            endcase
        end
        assign rows[j*PW +: PW] = {{(PW-N-2){digit[N+1]}}, digit} << (2*j);
    end
    qsag_mul_csa_tree #(.N(PW), .ROWS(R)) u_tree (.rows(rows), .sum(p));
endmodule

// Unsigned W x W multiplier using radix-4 unsigned recoding (0, a, 2a, 3a) + balanced CSA tree.
module qsag_umul32 #(
    parameter int W = 32
) (
    input  wire [W-1:0]   a,
    input  wire [W-1:0]   b,
    output wire [2*W-1:0] p
);
    localparam int PW = 2 * W;
    localparam int R  = (W + 1) / 2;
    wire [W+1:0] a1 = {2'b0, a};
    wire [W+1:0] a2 = {1'b0, a, 1'b0};
    wire [W+1:0] a3;
    qsag_prefix_add #(.N(W+2)) u_a3 (.a(a1), .b(a2), .cin(1'b0), .sum(a3));
    wire [2*R-1:0] bx = {{(2*R-W){1'b0}}, b};
    wire [R*PW-1:0] rows;
    for (genvar j = 0; j < R; j++) begin : g_row
        logic [W+1:0] d;
        always_comb begin
            unique case (bx[2*j +: 2])
                2'b01:   d = a1;
                2'b10:   d = a2;
                2'b11:   d = a3;
                default: d = '0;
            endcase
        end
        assign rows[j*PW +: PW] = PW'(d) << (2*j);
    end
    qsag_mul_csa_tree #(.N(PW), .ROWS(R)) u_tree (.rows(rows), .sum(p));
endmodule

// Dedicated W-bit unsigned squarer using symmetry (x[i]&x[j] for i<j shifted by i+j+1, x[i] at 2i).
// Uses ~half the partial-product gates of a general W x W multiplier.
module qsag_usq32 #(
    parameter int W = 32
) (
    input  wire [W-1:0]   x,
    output wire [2*W-1:0] sq
);
    localparam int PW    = 2 * W;
    localparam int NFOLD = (W >= 2) ? ((W - 2) / 3) : 0; // 3*k <= W-2 => 2*(W-2-k)+2 > k+W (disjoint!)
    localparam int NROWS = W - NFOLD;                    // 1 diag + (W-1-NFOLD) folded off-diag rows
    wire [NROWS*PW-1:0] all_rows;

    logic [PW-1:0] diag;
    always_comb begin
        diag = '0;
        for (int i = 0; i < W; i++) diag[2*i] = x[i];
    end
    assign all_rows[0 +: PW] = diag;

    for (genvar k = 0; k < W - 1 - NFOLD; k++) begin : g_sqrow
        localparam int M = W - 2 - k;
        logic [PW-1:0] rw;
        always_comb begin
            rw = '0;
            for (int j = k + 1; j < W; j++)
                rw[k + j + 1] = x[k] & x[j];
            if (k < NFOLD) begin
                for (int j = M + 1; j < W; j++)
                    rw[M + j + 1] = x[M] & x[j];
            end
        end
        assign all_rows[(k+1)*PW +: PW] = rw;
    end
    qsag_mul_csa_tree #(.N(PW), .ROWS(NROWS)) u_tree (.rows(all_rows), .sum(sq));
endmodule

// Balanced 3:2 compression down to two rows, followed by one Han-Carlson prefix adder.
module qsag_mul_csa_tree #(parameter int N = 66, parameter int ROWS = 17) (
    input  wire [ROWS*N-1:0] rows,
    output wire [N-1:0]      sum
);
    if (ROWS == 1) begin : g_one
        assign sum = rows;
    end else if (ROWS == 2) begin : g_final
        qsag_prefix_add #(.N(N)) u_add (.a(rows[0 +: N]), .b(rows[N +: N]), .cin(1'b0), .sum(sum));
    end else begin : g_reduce
        localparam int GROUPS = ROWS / 3;
        localparam int NEXT   = 2 * GROUPS + (ROWS % 3);
        wire [NEXT*N-1:0] next_rows;
        for (genvar j = 0; j < GROUPS; j++) begin : g_group
            qsag_csa32 #(.N(N)) u_csa (
                .a(rows[(3*j)*N +: N]), .b(rows[(3*j+1)*N +: N]), .c(rows[(3*j+2)*N +: N]),
                .s(next_rows[(2*j)*N +: N]), .cy(next_rows[(2*j+1)*N +: N])
            );
        end
        for (genvar j = 0; j < ROWS % 3; j++) begin : g_tail
            assign next_rows[(2*GROUPS+j)*N +: N] = rows[(3*GROUPS+j)*N +: N];
        end
        qsag_mul_csa_tree #(.N(N), .ROWS(NEXT)) u_next (.rows(next_rows), .sum(sum));
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
    /* verilator lint_off UNUSEDSIGNAL */
    wire [N-1:0] m = (a & b) | (a & c) | (b & c);
    /* verilator lint_on UNUSEDSIGNAL */
    assign s  = a ^ b ^ c;
    assign cy = {m[N-2:0], 1'b0};
endmodule

// Five rows to two. Exact as long as the integer sum is below 2^N.
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

// Rows of one Karatsuba partial product. ph: 1 = z0, 2 = z2 (with K_MUL), 3 = zm.
module qsag_gl64_mrows #(
    parameter int W  = 32,
    parameter int GB = 12
) (
    input  wire [2*W+1:0]      p,
    input  wire [1:0]          ph,
    output logic [2*W+GB-1:0]  r1,
    output logic [2*W+GB-1:0]  r2,
    output logic [2*W+GB-1:0]  r3
);
    localparam int LW = 2 * W;
    localparam int AW = LW + GB;
    localparam logic [LW-1:0] PRIME = {{W{1'b1}}, {(W-1){1'b0}}, 1'b1};
    localparam logic [LW-1:0] K_MUL = PRIME - (LW'(1) << (W + 1)) + LW'(2);

    wire [W-1:0]  lo = p[W-1:0];
    wire [W-1:0]  hi = p[LW-1:W];
    wire [1:0]    m2 = p[LW+1:LW];
    wire [LW-1:0] pn = ~p[LW-1:0];
    always_comb begin
        r1 = '0;
        r2 = '0;
        r3 = '0;
        unique case (ph)
            2'd1: begin
                r1 = AW'(p[LW-1:0]);
                r2 = AW'({~lo, hi});
                r3 = AW'({~hi, {W{1'b0}}});
            end
            2'd2: begin
                r1 = AW'(pn);
                r2 = AW'(K_MUL);
            end
            2'd3: begin
                r1 = AW'({lo, ~hi});
                r2 = AW'({hi, {(W-2){1'b0}}, ~m2});
            end
            default: ;
        endcase
    end
endmodule

// Canonical (x + y) mod p for x + y < 2^(2W+GB), GB <= W.
module qsag_gl64_canon #(
    parameter int W  = 32,
    parameter int GB = 12
) (
    input  wire [2*W+GB-1:0] x,
    input  wire [2*W+GB-1:0] y,
    output wire [2*W-1:0]    r
);
    localparam int LW = 2 * W;
    localparam int AW = LW + GB;
    localparam logic [LW-1:0] EPS = {{W{1'b0}}, {W{1'b1}}};
    wire [AW-1:0] t;
    qsag_prefix_add #(.N(AW)) u_t (.a(x), .b(y), .cin(1'b0), .sum(t));
    wire [GB-1:0] q  = t[AW-1:LW];
    wire [LW+1:0] qs = (LW + 2)'(q) << W;
    wire [LW+1:0] u, us, uc;
    qsag_csa32 #(.N(LW+2)) u_fold_rows (
        .a((LW+2)'(t[LW-1:0])), .b(qs), .c(~((LW+2)'(q))), .s(us), .cy(uc));
    qsag_prefix_add #(.N(LW+2)) u_fold (.a(us), .b(uc), .cin(1'b1), .sum(u));
    wire [LW:0] v;
    qsag_prefix_add #(.N(LW+1)) u_v (.a({1'b0, u[LW-1:0]}), .b({1'b0, EPS}), .cin(1'b0), .sum(v));
    assign r = (u[LW] | v[LW]) ? v[LW-1:0] : u[LW-1:0];
endmodule

// 5-row Goldilocks squarer partial-product combiner (separated for compositional Z3 LEC).
module qsag_gl64_sqrows #(
    parameter int W  = 32,
    parameter int GB = 12
) (
    input  wire [2*W-1:0]      z0,
    input  wire [2*W-1:0]      z2,
    input  wire [2*W-1:0]      p01,
    output wire [2*W+GB-1:0]   s,
    output wire [2*W+GB-1:0]   c
);
    localparam int LW = 2 * W;
    localparam int AW = LW + GB;
    localparam logic [W-1:0] TOP_C = {W{1'b1}} - W'(3); // 0xFFFF_FFFC for W=32
    wire [LW:0]  m    = {p01, 1'b0};                    // 2 * x0 * x1 < 2^(2W+1)
    wire [W-1:0] m0   = m[W-1:0];
    wire [W-1:0] m1   = m[LW-1:W];
    wire         m2   = m[LW];
    wire [W-1:0] l2   = z2[W-1:0];
    wire [W-1:0] h2   = z2[LW-1:W];
    wire [2:0]   c_m2 = m2 ? 3'd3 : 3'd4;               // 4 - m2

    wire [AW-1:0] r1 = AW'(z0);
    wire [AW-1:0] r2 = AW'({m0, ~m1});
    wire [AW-1:0] r3 = AW'({m1, {(W-3){1'b0}}, c_m2});
    wire [AW-1:0] r4 = AW'({l2, ~l2});
    wire [AW-1:0] r5 = AW'({TOP_C, ~h2});

    qsag_csa52 #(.N(AW)) u_csa (.x(r1), .y(r2), .r1(r3), .r2(r4), .r3(r5), .s(s), .c(c));
endmodule

// 1-cycle 5-row Goldilocks squarer: y = (x * x) mod p for ALL 64-bit x.
module qsag_gl64_sq_comb #(
    parameter int W  = 32,
    parameter int GB = 12
) (
    input  wire [2*W-1:0] x,
    output wire [2*W-1:0] y
);
    localparam int LW = 2 * W;
    localparam int AW = LW + GB;
    wire [W-1:0]  x0 = x[W-1:0];
    wire [W-1:0]  x1 = x[LW-1:W];
    wire [LW-1:0] z0, z2, p01;
    wire [AW-1:0] s, c;
    qsag_usq32       #(.W(W))          u_sq0  (.x(x0), .sq(z0));
    qsag_usq32       #(.W(W))          u_sq1  (.x(x1), .sq(z2));
    qsag_umul32      #(.W(W))          u_m01  (.a(x0), .b(x1), .p(p01));
    qsag_gl64_sqrows #(.W(W), .GB(GB)) u_rows (.z0(z0), .z2(z2), .p01(p01), .s(s), .c(c));
    qsag_gl64_canon  #(.W(W), .GB(GB)) u_canon(.x(s), .y(c), .r(y));
endmodule

module qsag_gl64_karatsuba_csa #(
    parameter int W  = 32,
    parameter int GB = 12
) (
    input  wire              clk,
    input  wire              rst_n,
    // row sources
    input  wire [2*W-1:0]    port,      // register-file read port
    input  wire [2*W-1:0]    xw,        // auxiliary word (stream, key, constant)
    input  wire [2*W-1:0]    rc,        // Poseidon2 round constant
    // row controls (ignored while a multiply is in progress)
    input  wire [1:0]        pm,        // port row: 0 off, 1 +port<<pk, 2 -port<<pk
    input  wire [3:0]        pk,        // port shift 0..10 (negative rows: 0 or 6 only)
    input  wire [2:0]        rm,        // register row: 0 off, 1 RES, 2 OPA, 3 OPB, 4 XW
    input  wire [1:0]        rk,        // register row shift 0..2
    input  wire              krc,       // add the round constant
    input  wire              acc_clr,   // start a new sum (ignore the accumulator)
    input  wire              acc_we,    // keep the sum in the accumulator
    input  wire              ld_opa,    // OPA <= cv
    input  wire              ld_opb,    // OPB <= cv
    input  wire              ld_res,    // RES <= cv
    // multiply: RES/cv <= (asel ? RES : OPA) * (bsel ? RES : OPB) mod p
    input  wire              mul_start,
    input  wire              mul_asel,
    input  wire              mul_bsel,
    output wire              mul_busy,  // phases 1..3
    output wire              mul_last,  // phase 3: cv is the product
    output wire [2*W-1:0]    cv,        // canonical value of the current sum
    output wire              cv_zero,
    output wire [2*W-1:0]    res
);
    localparam int LW = 2 * W;
    localparam int AW = LW + GB;
    localparam logic [LW-1:0] PRIME  = {{W{1'b1}}, {(W-1){1'b0}}, 1'b1};
    localparam logic [LW-1:0] K_NEG0 = PRIME - ((LW'(1) << W) - LW'(2));
    localparam logic [LW-1:0] K_NEG6 = PRIME - (((LW'(1) << W) - LW'(2)) << 6);

    logic [LW-1:0] opa, opb, resr;
    logic [AW-1:0] acc_s, acc_c;
    logic [LW+1:0] preg;
    logic [W:0]    sa, sb;
    logic [1:0]    mph;
    logic          asel_q, bsel_q;

    // ------------------------------------------------------------ multiplier
    wire          a_sel = (mph == 2'd0) ? mul_asel : asel_q;
    wire          b_sel = (mph == 2'd0) ? mul_bsel : bsel_q;
    wire [LW-1:0] ma    = a_sel ? resr : opa;
    wire [LW-1:0] mb    = b_sel ? resr : opb;
    logic [W:0]   m_a, m_b;
    always_comb begin
        unique case (mph)
            2'd0:    begin m_a = {1'b0, ma[W-1:0]};  m_b = {1'b0, mb[W-1:0]};  end
            2'd1:    begin m_a = {1'b0, ma[LW-1:W]}; m_b = {1'b0, mb[LW-1:W]}; end
            default: begin m_a = sa;                 m_b = sb;                 end
        endcase
    end
    wire [LW+1:0] m_p;
    qsag_mul33 #(.W(W)) u_mul (.a(m_a), .b(m_b), .p(m_p));

    wire [AW-1:0] mr1, mr2, mr3;
    qsag_gl64_mrows #(.W(W), .GB(GB)) u_mrows (.p(preg), .ph(mph), .r1(mr1), .r2(mr2), .r3(mr3));

    // ------------------------------------------------------------ operand rows
    logic [AW-1:0] prow, rrow, krow;
    logic [LW-1:0] rsel;
    wire  [LW-1:0] port_n = ~port;
    always_comb begin
        unique case (pm)
            2'd1:    prow = AW'(port) << pk;
            2'd2:    prow = AW'(port_n) << pk;
            default: prow = '0;
        endcase
        unique case (rm)
            3'd1:    rsel = resr;
            3'd2:    rsel = opa;
            3'd3:    rsel = opb;
            3'd4:    rsel = xw;
            default: rsel = '0;
        endcase
        rrow = AW'(rsel) << rk;
        if (pm == 2'd2) krow = AW'((pk == 4'd6) ? K_NEG6 : K_NEG0);
        else if (krc)   krow = AW'(rc);
        else            krow = '0;
    end

    // ------------------------------------------------------------ accumulate and canonicalize
    wire          in_mul = (mph != 2'd0);
    wire          use0   = in_mul ? (mph == 2'd1) : acc_clr;
    wire [AW-1:0] cx = use0 ? '0 : acc_s;
    wire [AW-1:0] cy = use0 ? '0 : acc_c;
    wire [AW-1:0] r1 = in_mul ? mr1 : prow;
    wire [AW-1:0] r2 = in_mul ? mr2 : rrow;
    wire [AW-1:0] r3 = in_mul ? mr3 : krow;
    wire [AW-1:0] ns, nc;
    qsag_csa52 #(.N(AW)) u_csa (.x(cx), .y(cy), .r1(r1), .r2(r2), .r3(r3), .s(ns), .c(nc));
    qsag_gl64_canon #(.W(W), .GB(GB)) u_canon (.x(ns), .y(nc), .r(cv));

    assign cv_zero  = (cv == '0);
    assign mul_busy = in_mul;
    assign mul_last = (mph == 2'd3);
    assign res      = resr;

    wire [W:0] sa_n, sb_n;
    qsag_prefix_add #(.N(W+1)) u_sa (.a({1'b0, ma[W-1:0]}), .b({1'b0, ma[LW-1:W]}), .cin(1'b0), .sum(sa_n));
    qsag_prefix_add #(.N(W+1)) u_sb (.a({1'b0, mb[W-1:0]}), .b({1'b0, mb[LW-1:W]}), .cin(1'b0), .sum(sb_n));

    always_ff @(posedge clk) begin
        if (ld_opa) opa <= cv;
        if (ld_opb) opb <= cv;
        if (ld_res) resr <= cv;
        if (in_mul ? (mph != 2'd3) : acc_we) begin
            acc_s <= ns;
            acc_c <= nc;
        end
        if ((mph == 2'd0 && mul_start) || mph == 2'd1 || mph == 2'd2) preg <= m_p;
        if (mph == 2'd0 && mul_start) begin
            sa     <= sa_n;
            sb     <= sb_n;
            asel_q <= mul_asel;
            bsel_q <= mul_bsel;
        end
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)           mph <= 2'd0;
        else if (mph == 2'd0) mph <= mul_start ? 2'd1 : 2'd0;
        else                  mph <= mph + 2'd1;
    end
endmodule

// Combinational reference composition of Karatsuba reduction, also used by fast 2-stage mul.
module qsag_gl64_kred_comb #(
    parameter int W  = 32,
    parameter int GB = 12
) (
    input  wire [2*W+1:0] z0,
    input  wire [2*W+1:0] z2,
    input  wire [2*W+1:0] zm,
    output wire [2*W-1:0] r
);
    localparam int AW = 2 * W + GB;
    wire [AW-1:0] a1, a2, a3, b1, b2, b3, c1, c2, c3;
    wire [AW-1:0] s1, k1, s2, k2, s3, k3;
    qsag_gl64_mrows #(.W(W), .GB(GB)) u_r0 (.p(z0), .ph(2'd1), .r1(a1), .r2(a2), .r3(a3));
    qsag_gl64_mrows #(.W(W), .GB(GB)) u_r2 (.p(z2), .ph(2'd2), .r1(b1), .r2(b2), .r3(b3));
    qsag_gl64_mrows #(.W(W), .GB(GB)) u_rm (.p(zm), .ph(2'd3), .r1(c1), .r2(c2), .r3(c3));
    qsag_csa52 #(.N(AW)) u_c0 (.x('0), .y('0), .r1(a1), .r2(a2), .r3(a3), .s(s1), .c(k1));
    qsag_csa52 #(.N(AW)) u_c2 (.x(s1), .y(k1), .r1(b1), .r2(b2), .r3(b3), .s(s2), .c(k2));
    qsag_csa52 #(.N(AW)) u_cm (.x(s2), .y(k2), .r1(c1), .r2(c2), .r3(c3), .s(s3), .c(k3));
    qsag_gl64_canon #(.W(W), .GB(GB)) u_canon (.x(s3), .y(k3), .r(r));
endmodule

// 2-stage pipelined (1/clk throughput) Karatsuba Goldilocks multiplier for Poseidon2 & Ext4.
// Cycle 0: z0 = a0*b0, z2 = a1*b1, sa = a0+a1, sb = b0+b1 (<= 18 gate levels)
// Cycle 1: zm = sa*sb -> qsag_gl64_kred_comb               (<= 24 gate levels)
module qsag_gl64_mul_pipe #(
    parameter int W  = 32,
    parameter int GB = 12
) (
    input  wire           clk,
    input  wire           en,
    input  wire [2*W-1:0] a,
    input  wire [2*W-1:0] b,
    output wire [2*W-1:0] p
);
    localparam int LW = 2 * W;
    wire [LW-1:0] z0_c, z2_c;
    wire [W:0]    sa_c, sb_c;
    qsag_umul32     #(.W(W))   u_z0 (.a(a[W-1:0]),  .b(b[W-1:0]),  .p(z0_c));
    qsag_umul32     #(.W(W))   u_z2 (.a(a[LW-1:W]), .b(b[LW-1:W]), .p(z2_c));
    qsag_prefix_add #(.N(W+1)) u_sa (.a({1'b0, a[W-1:0]}), .b({1'b0, a[LW-1:W]}), .cin(1'b0), .sum(sa_c));
    qsag_prefix_add #(.N(W+1)) u_sb (.a({1'b0, b[W-1:0]}), .b({1'b0, b[LW-1:W]}), .cin(1'b0), .sum(sb_c));

    wire [LW-1:0] z0_q, z2_q;
    wire [W:0]    sa_q, sb_q;
    qsag_ereg_nr #(.W(LW))  u_rz0 (.clk(clk), .en(en), .d(z0_c), .q(z0_q));
    qsag_ereg_nr #(.W(LW))  u_rz2 (.clk(clk), .en(en), .d(z2_c), .q(z2_q));
    qsag_ereg_nr #(.W(W+1)) u_rsa (.clk(clk), .en(en), .d(sa_c), .q(sa_q));
    qsag_ereg_nr #(.W(W+1)) u_rsb (.clk(clk), .en(en), .d(sb_c), .q(sb_q));

    wire [LW+1:0] zm_c;
    qsag_mul33          #(.W(W))          u_zm   (.a(sa_q), .b(sb_q), .p(zm_c));
    qsag_gl64_kred_comb #(.W(W), .GB(GB)) u_kred (.z0({2'b0, z0_q}), .z2({2'b0, z2_q}), .zm(zm_c), .r(p));
endmodule
`default_nettype wire

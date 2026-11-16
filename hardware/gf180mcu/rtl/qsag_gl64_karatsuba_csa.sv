// QSAG-NI-180 Goldilocks arithmetic unit: phi = 2^W Karatsuba multiply with carry-save
// reduction, shared with the row-adder that serves every field addition of the chip.
//
//   p = phi^2 - phi + 1   (W = 32: p = 0xFFFF_FFFF_0000_0001)
//   phi^2 = phi - 1,  phi^3 = -1   (mod p)
//
// Multiply (4 cycles, one (W+1)x(W+1) multiplier):
//   a = a1*phi + a0, b = b1*phi + b0
//   z0 = a0*b0, z2 = a1*b1, zm = (a0 + a1)*(b0 + b1)
//   a*b = z0 + (zm - z0 - z2)*phi + z2*phi^2  =  z0*(1 - phi) + zm*phi - z2   (mod p)
// Each product is folded into at most three non-negative rows of 2W bits (negative terms as
// bit complements, their offsets collected in the single constant K_MUL) and accumulated in a
// carry-save register. One canonicalizing adder chain, shared by all operations, returns the
// result in [0, p-1].
//
// The module is generic in W so that the identical RTL can be proven end to end at reduced
// width (see lec/); the chip instantiates W = 32, GB = 12.
`default_nettype none

module qsag_mul33 #(
    parameter int W = 32
) (
    input  wire [W:0]     a,
    input  wire [W:0]     b,
    output wire [2*W+1:0] p
);
    assign p = a * b;
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
    wire [N-1:0] m = (a & b) | (a & c) | (b & c);
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
    // offsets of the complemented rows: +2 (z0), -(2^W - 2) (z2), -(2^W + 2) (zm)
    localparam logic [LW-1:0] K_MUL = PRIME - (LW'(1) << (W + 1)) + LW'(2);

    wire [W-1:0] lo = p[W-1:0];
    wire [W-1:0] hi = p[LW-1:W];
    wire [1:0]   m2 = p[LW+1:LW];
    wire [LW-1:0] pn = ~p[LW-1:0];   // complement at the row width, before zero extension
    always_comb begin
        r1 = '0;
        r2 = '0;
        r3 = '0;
        unique case (ph)
            2'd1: begin  // z0*(1 - phi) = z0 + h0 - (l0 + h0)*phi
                r1 = AW'(p[LW-1:0]);
                r2 = AW'({~lo, hi});
                r3 = AW'({~hi, {W{1'b0}}});
            end
            2'd2: begin  // -z2
                r1 = AW'(pn);
                r2 = AW'(K_MUL);
            end
            2'd3: begin  // zm*phi = (m0 + m1)*phi - m1 - m2
                r1 = AW'({lo, ~hi});
                r2 = AW'({hi, {(W-2){1'b0}}, ~m2});
            end
            default: ;
        endcase
    end
endmodule

// Canonical (x + y) mod p for x + y < 2^(2W+GB), GB <= W.
//   t = x + y = q*2^(2W) + lo;  2^(2W) = 2^W - 1 (mod p)
//   u = lo + q*(2^W - 1) < 2^(2W+1);  one conditional +(2^W - 1) mod 2^(2W) finishes:
//   it is "- 2^(2W)" when u overflowed and "- p" when u >= p.
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
    wire [AW-1:0] t  = x + y;
    wire [GB-1:0] q  = t[AW-1:LW];
    wire [LW+1:0] qs = (LW + 2)'(q) << W;
    wire [LW+1:0] u  = (LW + 2)'(t[LW-1:0]) + qs - (LW + 2)'(q);
    wire [LW:0]   v  = {1'b0, u[LW-1:0]} + {1'b0, EPS};
    assign r = (u[LW] | v[LW]) ? v[LW-1:0] : u[LW-1:0];
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
    localparam logic [LW-1:0] PRIME = {{W{1'b1}}, {(W-1){1'b0}}, 1'b1};
    // -(2^LW - 1)*2^k = -(2^W - 2)*2^k (mod p)
    localparam logic [LW-1:0] K_NEG0 = PRIME - ((LW'(1) << W) - LW'(2));
    localparam logic [LW-1:0] K_NEG6 = PRIME - (((LW'(1) << W) - LW'(2)) << 6);

    logic [LW-1:0] opa, opb, resr;
    logic [AW-1:0] acc_s, acc_c;
    logic [LW+1:0] preg;
    logic [W:0]    sa, sb;
    logic [1:0]    mph;
    logic          asel_q, bsel_q;

    // ------------------------------------------------------------ multiplier
    wire           a_sel = (mph == 2'd0) ? mul_asel : asel_q;
    wire           b_sel = (mph == 2'd0) ? mul_bsel : bsel_q;
    wire [LW-1:0]  ma    = a_sel ? resr : opa;
    wire [LW-1:0]  mb    = b_sel ? resr : opb;
    logic [W:0]    m_a, m_b;
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
    wire  [LW-1:0] port_n = ~port;   // complement at the row width, before zero extension
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
            sa     <= {1'b0, ma[W-1:0]} + {1'b0, ma[LW-1:W]};
            sb     <= {1'b0, mb[W-1:0]} + {1'b0, mb[LW-1:W]};
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

// Combinational reference composition of the reduction, used by the formal proofs: the same
// row generator, compressor and canonicalizer, chained exactly as the sequencer chains them.
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
`default_nettype wire

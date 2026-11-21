// 9-DSP Unsigned Two-Level Karatsuba 64 x 64 -> 128 Multiplier (`MUL64_LAT = 3`).
//
// Splits a = a0 + 2^32 * a1 and b = b0 + 2^32 * b1 (a_i, b_i in [0, 2^32 - 1]), with
// sa = a0 + a1 (33 bits) and b0 + b1 = beta + 2^32 * cb (beta 32 bits, cb 1 bit).
// Each of the three 33x32 unsigned products P0 = a0*b0, P2 = a1*b1, and PS_lo = sa*beta is
// computed by `qsag_mul33x32_dsp` (3 DSPs each = 9 DSPs total on both MULT18X18D and DSP48E2).
module qsag_mul64_dsp #(
    parameter int AW = 26,
    parameter int BW = 17
) (
    input  logic         clk,
    input  logic [63:0]  a,
    input  logic [63:0]  b,
    output logic [127:0] p
);
    localparam int CHUNK    = 24;
    localparam int CHUNK_SA = (AW <= 16) ? 33 : 17;
    localparam logic [127:0] B33      = 128'h0000_0000_0000_0002_FFFF_FFFE_0000;
    localparam logic [65:0]  NEG_B33  = 66'd0 - B33[65:0];
    localparam logic [127:0] C_KARA   = (B33 << 32) - B33 - (B33 << 64) + 128'd4;

    wire [31:0] a0 = a[31:0], a1 = a[63:32];
    wire [31:0] b0 = b[31:0], b1 = b[63:32];

    logic [32:0] sa, sb_full;
    qsag_add_split #(.W(33), .CHUNK(CHUNK_SA)) u_sa (.a({1'b0, a0}), .b({1'b0, a1}), .y(sa));
    qsag_add_split #(.W(33), .CHUNK(CHUNK_SA)) u_sb (.a({1'b0, b0}), .b({1'b0, b1}), .y(sb_full));
    wire        cb   = sb_full[32];
    wire [31:0] beta = sb_full[31:0];

    // Delay sa and cb across Stages 1..2 to align with Stage-2 DSP outputs.
    logic [32:0] sa_q1, sa_q2;
    logic        cb_q1, cb_q2;
    always_ff @(posedge clk) begin
        sa_q1 <= sa;   sa_q2 <= sa_q1;
        cb_q1 <= cb;   cb_q2 <= cb_q1;
    end

    logic [65:0] p0_s, p0_c, p2_s, p2_c, ps_s, ps_c;
    qsag_mul33x32_dsp u_p0 (.clk(clk), .a({1'b0, a0}), .b(b0),   .s(p0_s), .c(p0_c));
    qsag_mul33x32_dsp u_p2 (.clk(clk), .a({1'b0, a1}), .b(b1),   .s(p2_s), .c(p2_c));
    qsag_mul33x32_dsp u_ps (.clk(clk), .a(sa),         .b(beta), .s(ps_s), .c(ps_c));

    // Stage 3: outer Karatsuba recombination.
    wire [127:0] cb_term = cb_q2 ? (128'(sa_q2) << 64) : 128'd0;
    wire [12*128-1:0] outer_rows = {
        C_KARA,
        ~(128'(p2_c) << 32),
        ~(128'(p2_s) << 32),
        ~(128'(p0_c) << 32),
        ~(128'(p0_s) << 32),
        cb_term,
        128'(ps_c) << 32,
        128'(ps_s) << 32,
        128'(p2_c) << 64,
        128'(p2_s) << 64,
        128'(p0_c),
        128'(p0_s)
    };

    /* verilator lint_off UNUSEDSIGNAL */
    logic [65:0] r0_66, r2_66, rs_66;
    /* verilator lint_on UNUSEDSIGNAL */
    logic [95:0]  hi96;
    logic [127:0] sum;

    if (AW <= 16) begin : g_ecp5
        // Resolve the 3 non-overlapping 65-bit subproducts in parallel via native CCU2C chains,
        // then combine the 5 single-rail Karatsuba rows (-2,000 TRELLIS_COMB/mul, <= 4.7 ns!).
        qsag_sum_csa #(.W(66), .N(3), .CHUNK(66)) u_r0 (.x({NEG_B33, p0_c, p0_s}), .y(r0_66));
        qsag_sum_csa #(.W(66), .N(3), .CHUNK(66)) u_r2 (.x({NEG_B33, p2_c, p2_s}), .y(r2_66));
        qsag_sum_csa #(.W(66), .N(3), .CHUNK(66)) u_rs (.x({NEG_B33, ps_c, ps_s}), .y(rs_66));
        wire [5*96-1:0] hi_rows = {
            {31'd0, cb_q2 ? sa_q2 : 33'd0, 32'd2},
            ~{32'd0, r2_66[63:0]},
            ~{32'd0, r0_66[63:0]},
            {31'd0, rs_66[64:0]},
            {r2_66[63:0], r0_66[63:32]}
        };
        qsag_sum_csa #(.W(96), .N(5), .CHUNK(48)) u_hi (.x(hi_rows), .y(hi96));
        assign sum = {hi96, r0_66[31:0]};
        /* verilator lint_off UNUSEDSIGNAL */
        wire unused_or = &{1'b0, outer_rows};
        /* verilator lint_on UNUSEDSIGNAL */
    end else begin : g_csa
        qsag_sum_csa #(.W(128), .N(12), .CHUNK(CHUNK)) u_sum (.x(outer_rows), .y(sum));
        assign r0_66 = '0;
        assign r2_66 = '0;
        assign rs_66 = '0;
        assign hi96  = '0;
        /* verilator lint_off UNUSEDSIGNAL */
        wire unused_ecp5 = &{1'b0, r0_66, r2_66, rs_66, hi96};
        /* verilator lint_on UNUSEDSIGNAL */
    end
    always_ff @(posedge clk) p <= sum;

    /* verilator lint_off UNUSEDPARAM */
    localparam int UNUSED_CFG = AW + BW;
    /* verilator lint_on UNUSEDPARAM */
endmodule

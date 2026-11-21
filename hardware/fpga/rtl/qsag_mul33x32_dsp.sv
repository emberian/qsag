// 3-DSP 33x32 unsigned Karatsuba block returning exact biased integer carry-save rows:
//   int(s) + int(c) == int(a) * int(b) + B33   for all 2^65 inputs (a, b),
// where B33 = ((2^32 - 1) + (2^33 - 1)) << 16 = 66'h0_0002_FFFF_FFFE_0000.
//
// Uses 3 unsigned DSPs of widths 16x16u, 17x16u, and 18x17u:
//   - a_lo + a_hi <= (2^16 - 1) + (2^17 - 1) = 196,606 < 2^18 (18 bits unsigned)
//   - b_lo + b_hi <= (2^16 - 1) + (2^16 - 1) = 131,070 < 2^17 (17 bits unsigned)
// Fits natively in ONE Lattice ECP5 `MULT18X18D` (18x18u) AND ONE Xilinx UltraScale+
// `DSP48E2` (27x18s = 26x17u) per sub-product (= 3 DSPs total).
module qsag_mul33x32_dsp (
    input  logic        clk,
    input  logic [32:0] a,
    input  logic [31:0] b,
    output logic [65:0] s,
    output logic [65:0] c
);
    wire [15:0] a0   = a[15:0];
    wire [16:0] a1   = a[32:16];
    wire [15:0] b0   = b[15:0];
    wire [15:0] b1   = b[31:16];
    wire [17:0] asum = {2'b0, a0} + {1'b0, a1};
    wire [16:0] bsum = {1'b0, b0} + {1'b0, b1};

    // Dedicated DSP AREG/BREG (Stage 1) and MREG/PREG (Stage 2) registers.
    logic [15:0] a0_q, b0_q, b1_q;
    logic [16:0] a1_q, bs_q;
    logic [17:0] as_q;
    logic [31:0] t0_q;
    logic [32:0] t1_q;
    logic [34:0] ts_q;

    always_ff @(posedge clk) begin
        a0_q <= a0;   b0_q <= b0;   t0_q <= 32'(a0_q) * 32'(b0_q);
        a1_q <= a1;   b1_q <= b1;   t1_q <= 33'(a1_q) * 33'(b1_q);
        as_q <= asum; bs_q <= bsum; ts_q <= 35'(as_q) * 35'(bs_q);
    end

    // Non-negative biased Karatsuba rows (all top bits [65:51] of rows 1..3 are 0, so no carry
    // reaches bit 66; int(s) + int(c) == int(a)*int(b) + B33 over Z with zero wraparound).
    wire [4*66-1:0] rows = {
        {17'b0, ~t1_q, 16'b0},
        {18'b0, ~t0_q, 16'b0},
        {15'b0,  ts_q, 16'b0},
        { 1'b0,  t1_q, t0_q}
    };
    qsag_csa_reduce2 #(.W(66), .N(4)) u_csa (.x(rows), .s(s), .c(c));
endmodule

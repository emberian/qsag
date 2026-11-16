// 64 x 64 -> 128 unsigned multiplier tiled onto FPGA DSP blocks. Latency MUL64_LAT = 4.
//
// a is cut into NA chunks of AW bits and b into 4 chunks of BW bits; every chunk pair is one
// AW x BW unsigned multiply, sized for one DSP primitive:
//   AW = 26, BW = 17 : 12 x DSP48E2 (27 x 18 signed, used as 26 x 17 unsigned)   UltraScale+
//   AW = 16, BW = 16 : 16 x MULT18X18D                                            ECP5
// Stages: 1 operand registers (AREG/BREG), 2 tile products (MREG), 3 one add per b-chunk row
// (tiles of even and of odd index within a row do not overlap, so each row is one two-operand
// add), 4 the four rows summed into the product. Requires BW <= AW and 4*BW >= 64.
module qsag_mul64_dsp #(
    parameter int AW = 26,
    parameter int BW = 17
) (
    input  logic         clk,
    input  logic [63:0]  a,
    input  logic [63:0]  b,
    output logic [127:0] p
);
    localparam int NA = (64 + AW - 1) / AW;
    localparam int NB = 4;
    localparam int TW = AW + BW;          // tile product width
    localparam int RW = NA * AW + BW;     // row width
    localparam int SW = RW + (NB - 1) * BW;
    localparam int APAD = NA * AW;
    localparam int BPAD = NB * BW;

    // Stage 1: operand registers, zero-padded to whole chunks.
    logic [APAD-1:0] a_q;
    logic [BPAD-1:0] b_q;
    always_ff @(posedge clk) begin
        a_q <= APAD'(a);
        b_q <= BPAD'(b);
    end

    // Stage 2: tile products.
    logic [NA*NB*TW-1:0] t_q;
    for (genvar j = 0; j < NB; j++) begin : g_b
        for (genvar i = 0; i < NA; i++) begin : g_a
            logic [TW-1:0] ai, bj;
            assign ai = TW'(a_q[i*AW +: AW]);
            assign bj = TW'(b_q[j*BW +: BW]);
            always_ff @(posedge clk) t_q[(j*NA+i)*TW +: TW] <= ai * bj;
        end
    end

    // Stage 3: row_j = sum_i tile(i, j) << (i*AW).
    logic [NB*RW-1:0] row_q;
    for (genvar j = 0; j < NB; j++) begin : g_row
        logic [RW-1:0] ev, od;
        always_comb begin
            ev = '0;
            od = '0;
            for (int i = 0; i < NA; i++) begin
                if ((i % 2) == 0) ev = ev | (RW'(t_q[(j*NA+i)*TW +: TW]) << (i * AW));
                else              od = od | (RW'(t_q[(j*NA+i)*TW +: TW]) << (i * AW));
            end
        end
        always_ff @(posedge clk) row_q[j*RW +: RW] <= ev + od;
    end

    // Stage 4: product = sum_j row_j << (j*BW). The sum is a*b < 2^128, so the bits of the
    // SW-bit sum above 127 are zero.
    /* verilator lint_off UNUSEDSIGNAL */
    logic [SW-1:0] sum;
    /* verilator lint_on UNUSEDSIGNAL */
    always_comb begin
        sum = '0;
        for (int j = 0; j < NB; j++) sum = sum + (SW'(row_q[j*RW +: RW]) << (j * BW));
    end
    always_ff @(posedge clk) p <= sum[127:0];
endmodule

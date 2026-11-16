// 64 x 64 -> 128 unsigned multiplier tiled onto FPGA DSP blocks. Latency MUL64_LAT = 4.
//
// a is cut into NA chunks of AW bits and b into 4 chunks of BW bits; every chunk pair is one
// AW x BW unsigned multiply, sized for one DSP primitive:
//   AW = 26, BW = 17 : 12 x DSP48E2 (27 x 18 signed, used as 26 x 17 unsigned)   UltraScale+
//   AW = 16, BW = 16 : 16 x MULT18X18D                                            ECP5
// Stages: 1 operand registers (AREG/BREG), 2 tile products (MREG/PREG), 3 one add per b-chunk row
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
    localparam int APAD = NA * AW;
    localparam int BPAD = NB * BW;

    // Stages 1 and 2: every tile owns its operand registers and its product register, so each
    // maps onto one DSP block with its internal A/B and M (or P) registers and no fabric flops.
    logic [APAD-1:0] a_pad;
    logic [BPAD-1:0] b_pad;
    assign a_pad = APAD'(a);
    assign b_pad = BPAD'(b);

    logic [NA*NB*TW-1:0] t_q;
    for (genvar j = 0; j < NB; j++) begin : g_b
        for (genvar i = 0; i < NA; i++) begin : g_a
            logic [AW-1:0] ai_q;
            logic [BW-1:0] bj_q;
            logic [TW-1:0] tq;
            always_ff @(posedge clk) begin
                ai_q <= a_pad[i*AW +: AW];
                bj_q <= b_pad[j*BW +: BW];
                tq   <= TW'(ai_q) * TW'(bj_q);
            end
            assign t_q[(j*NA+i)*TW +: TW] = tq;
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
        logic [RW-1:0] row_d;
        qsag_add_split #(.W(RW)) u_add (.a(ev), .b(od), .y(row_d));
        always_ff @(posedge clk) row_q[j*RW +: RW] <= row_d;
    end

    // Stage 4: compress four shifted rows without propagating carries, then a
    // chunked carry-select addition. Truncation is modulo 2^128; a*b fits exactly.
    logic [NB*128-1:0] rows;
    logic [127:0] sum;
    for (genvar j = 0; j < NB; j++) begin : g_shift
        assign rows[j*128 +: 128] = (128'(row_q[j*RW +: RW]) << (j * BW));
    end
    qsag_sum_csa #(.W(128), .N(NB)) u_sum (.x(rows), .y(sum));
    always_ff @(posedge clk) p <= sum;
endmodule

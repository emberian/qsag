// 64 x 64 -> 128 unsigned multiplier tiled onto FPGA DSP blocks. Latency MUL64_LAT = 3.
//
// a is cut into NA chunks of AW bits and b into 4 chunks of BW bits; every chunk pair is one
// AW x BW unsigned multiply sized for one DSP primitive:
//   AW = 26, BW = 17 : 12 x DSP48E2 (27 x 18 signed, used as 26 x 17 unsigned)   UltraScale+
//   AW = 16, BW = 16 : 16 x MULT18X18D                                            ECP5
// Stages:
//   1. Per-tile operand registers (AREG/BREG inside DSP).
//   2. Per-tile product registers (MREG/PREG inside DSP).
//   3. Non-overlapping even/odd tiles within each row form 8 shifted 128-bit vectors with zero
//      gates, compressed by a 4-level 3:2 CSA LUT tree and one split carry-select adder into p.
// Requires BW <= AW and 4*BW >= 64.
module qsag_mul64_dsp #(
    parameter int AW = 26,
    parameter int BW = 17
) (
    input  logic         clk,
    input  logic [63:0]  a,
    input  logic [63:0]  b,
    output logic [127:0] p
);
    localparam int NA    = (64 + AW - 1) / AW;
    localparam int NB    = 4;
    localparam int TW    = AW + BW;
    localparam int APAD  = NA * AW;
    localparam int BPAD  = NB * BW;
    localparam int CHUNK = (AW <= 16) ? 16 : 24;

    logic [APAD-1:0] a_pad;
    logic [BPAD-1:0] b_pad;
    assign a_pad = APAD'(a);
    assign b_pad = BPAD'(b);

    // Stages 1 and 2: dedicated per-tile operand and product registers.
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

    // Stage 3: pack non-overlapping even/odd tiles into 8 rows, compress via 3:2 CSA + split carry.
    logic [8*128-1:0] rows;
    for (genvar j = 0; j < NB; j++) begin : g_row
        logic [127:0] ev, od;
        always_comb begin
            ev = '0;
            od = '0;
            for (int i = 0; i < NA; i++) begin
                if ((i % 2) == 0)
                    ev = ev | (128'(t_q[(j*NA+i)*TW +: TW]) << (i * AW + j * BW));
                else
                    od = od | (128'(t_q[(j*NA+i)*TW +: TW]) << (i * AW + j * BW));
            end
        end
        assign rows[(2*j)*128 +: 128]   = ev;
        assign rows[(2*j+1)*128 +: 128] = od;
    end

    logic [127:0] sum;
    qsag_sum_csa #(.W(128), .N(8), .CHUNK(CHUNK)) u_sum (.x(rows), .y(sum));
    always_ff @(posedge clk) p <= sum;
endmodule

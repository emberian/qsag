// x mod p for x < 2^136, p = 2^64 - 2^32 + 1 (Goldilocks). Output is canonical (< p).
//
// With x = lo + m*2^64 + h*2^96 + t*2^128 (lo 64 bits, m and h 32 bits, t 8 bits) and
// 2^64 = 2^32 - 1, 2^96 = -1, 2^128 = -2^32 (mod p):
//     v = lo + m*2^32 + p - m - h - t*2^32,   0 < v < 3p.
// Stage 1 compresses the six 66-bit terms in a 3:2 CSA tree and resolves v with a split
// parallel-prefix adder. Stage 2 evaluates v - p and v - 2p in parallel via split adders
// and selects the unique canonical residue (< p). REG_OUT=1 registers Stage 2 (2 clocks);
// REG_OUT=0 exposes the combinational Stage 2 residue so chained multipliers absorb it
// directly into DSP AREG/BREG.
module qsag_gl64_reduce #(
    parameter bit REG_OUT = 1'b1
) (
    input  logic         clk,
    input  logic [135:0] x,
    output logic [63:0]  r
);
    localparam logic [63:0] GL_P   = qsag_ni_pkg::GL_P;
    localparam logic [65:0] C_BIAS = {2'b0, GL_P} + 66'd3;
    localparam logic [66:0] NEG_1P = 67'h7_0000_0000_FFFF_FFFF; // 2^67 - GL_P
    localparam logic [66:0] NEG_2P = 67'h6_0000_0001_FFFF_FFFE; // 2^67 - 2*GL_P

    logic [63:0] lo;
    logic [31:0] m, h;
    logic [7:0]  t;
    assign {t, h, m, lo} = x;

    logic [6*66-1:0] terms;
    assign terms[0*66 +: 66] = {2'b0, lo};
    assign terms[1*66 +: 66] = {2'b0, m, 32'b0};
    assign terms[2*66 +: 66] = ~{34'b0, m};
    assign terms[3*66 +: 66] = ~{34'b0, h};
    assign terms[4*66 +: 66] = ~{26'b0, t, 32'b0};
    assign terms[5*66 +: 66] = C_BIAS;

    logic [65:0] v_d, v_q;
    qsag_sum_csa #(.W(66), .N(6), .CHUNK(24)) u_v (.x(terms), .y(v_d));
    always_ff @(posedge clk) v_q <= v_d;

    // Note: in unsigned addition {1'b0, v_q} + (2^67 - k*p), bit 66 is 0 iff v_q >= k*p:
    // if v_q >= k*p, v_q + 2^67 - k*p >= 2^67 wraps modulo 2^67 so bit 66 is 0;
    // if v_q < k*p, v_q + 2^67 - k*p in [2^67 - 2p, 2^67 - 1] has bit 66 == 1.
    /* verilator lint_off UNUSEDSIGNAL */
    logic [66:0] v1, v2;
    /* verilator lint_on UNUSEDSIGNAL */
    qsag_add_split #(.W(67), .CHUNK(24)) u_v1 (.a({1'b0, v_q}), .b(NEG_1P), .y(v1));
    qsag_add_split #(.W(67), .CHUNK(24)) u_v2 (.a({1'b0, v_q}), .b(NEG_2P), .y(v2));

    logic [63:0] r_d;
    assign r_d = !v2[66] ? v2[63:0] : !v1[66] ? v1[63:0] : v_q[63:0];

    if (REG_OUT) begin : g_reg
        always_ff @(posedge clk) r <= r_d;
    end else begin : g_comb
        assign r = r_d;
    end
endmodule

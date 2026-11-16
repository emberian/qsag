// Carry-select addition modulo 2^W. Each 32-bit chunk computes both carry cases
// in parallel; only a mux (not another carry chain) crosses a chunk boundary.
module qsag_add_split #(parameter int W = 128, parameter int CHUNK = 32) (
    input logic [W-1:0] a, b,
    output logic [W-1:0] y
);
    localparam int N = (W + CHUNK - 1) / CHUNK;
    /* verilator lint_off UNUSEDSIGNAL */
    logic [N:0] carry;
    /* verilator lint_on UNUSEDSIGNAL */
    assign carry[0] = 1'b0;
    for (genvar i = 0; i < N; i++) begin : g_chunk
        localparam int B = (W-i*CHUNK < CHUNK) ? W-i*CHUNK : CHUNK;
        logic [B:0] s0, s1;
        assign s0 = {1'b0, a[i*CHUNK +: B]} + {1'b0, b[i*CHUNK +: B]};
        assign s1 = {1'b0, a[i*CHUNK +: B]} + {1'b0, b[i*CHUNK +: B]} + (B+1)'(1);
        assign {carry[i+1], y[i*CHUNK +: B]} = carry[i] ? s1 : s0;
    end
endmodule

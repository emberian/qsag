// Parallel-prefix carry-select addition modulo 2^W.
// Chunk 0 uses a single hardware carry chain (carry_in = 0); chunks 1..N-1 evaluate
// both carry cases in CHUNK-bit carry chains and resolve all chunk carries in parallel
// via a logarithmic (G, P) prefix network, eliminating wide ripple-carry chains.
(* flatten *)
module qsag_add_split #(
    parameter int W = 128,
    parameter int CHUNK = 24
) (
    input  logic [W-1:0] a,
    input  logic [W-1:0] b,
    output logic [W-1:0] y
);
    localparam int N = (W + CHUNK - 1) / CHUNK;

`ifdef QSAG_ECP5_CARRY
    /* verilator lint_off UNUSEDPARAM */
    localparam int UNUSED_N = N;
    /* verilator lint_on UNUSEDPARAM */
    assign y = a + b;
`else
    if (N == 1) begin : g_single
        assign y = a + b;
    end else begin : g_split
        /* verilator lint_off UNUSEDSIGNAL */
        logic [N-1:0] g0, p0, g1, p1, g2, p2, g3;
        /* verilator lint_on UNUSEDSIGNAL */

        // Chunk 0: carry-in is identically 0 (no duplicate carry chain).
        localparam int B0 = (W < CHUNK) ? W : CHUNK;
        logic [B0:0] s0_0;
        assign s0_0 = {1'b0, a[0 +: B0]} + {1'b0, b[0 +: B0]};
        assign y[0 +: B0] = s0_0[B0-1:0];
        assign g0[0] = s0_0[B0];
        assign p0[0] = 1'b0;

        // Parallel Kogge-Stone prefix over chunk generate/propagate.
        for (genvar i = 0; i < N; i++) begin : g_p1
            if (i == 0) begin : g_z1
                assign g1[i] = g0[i];
                assign p1[i] = p0[i];
            end else begin : g_s1
                assign g1[i] = g0[i] | (p0[i] & g0[i-1]);
                assign p1[i] = p0[i] & p0[i-1];
            end
        end
        for (genvar i = 0; i < N; i++) begin : g_p2
            if (i < 2) begin : g_z2
                assign g2[i] = g1[i];
                assign p2[i] = p1[i];
            end else begin : g_s2
                assign g2[i] = g1[i] | (p1[i] & g1[i-2]);
                assign p2[i] = p1[i] & p1[i-2];
            end
        end
        for (genvar i = 0; i < N; i++) begin : g_p3
            if (i < 4) begin : g_z3
                assign g3[i] = g2[i];
            end else begin : g_s3
                assign g3[i] = g2[i] | (p2[i] & g2[i-4]);
            end
        end

        for (genvar i = 1; i < N; i++) begin : g_chunk
            localparam int B = (W - i*CHUNK < CHUNK) ? (W - i*CHUNK) : CHUNK;
            logic [B:0] c0_s, c1_s;
            logic       cin;
            assign c0_s = {1'b0, a[i*CHUNK +: B]} + {1'b0, b[i*CHUNK +: B]};
            assign c1_s = {1'b0, a[i*CHUNK +: B]} + {1'b0, b[i*CHUNK +: B]} + (B+1)'(1);
            assign g0[i] = c0_s[B];
            assign p0[i] = c1_s[B];
            if (i - 1 < 8) begin : g_c_fast
                assign cin = g3[i-1];
            end else begin : g_c_wide
                assign cin = g3[i-1] | (p2[i-1] & p2[i-5] & g3[i-9]);
            end
            assign y[i*CHUNK +: B] = cin ? c1_s[B-1:0] : c0_s[B-1:0];
        end
    end
`endif
endmodule

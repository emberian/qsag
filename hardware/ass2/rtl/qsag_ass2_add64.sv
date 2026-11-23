// 6-level bit-parallel Kogge-Stone 64-bit adder (`< 6.5 ns` SS).
// Marked `(* keep_hierarchy *)` so synthesis/ABC preserves the parallel-prefix tree.
(* keep_hierarchy *)
module qsag_ass2_add64 (
    input  wire [63:0] a, b,
    input  wire        cin,
    output wire [63:0] sum,
    output wire        cout
);
    wire [63:0] g [7];
    wire [63:0] p [7];
    wire [64:0] c;

    assign g[0] = a & b;
    assign p[0] = a ^ b;
    assign c[0] = cin;

    for (genvar s = 0; s < 6; s++) begin : g_stage
        localparam int D = 1 << s;
        for (genvar i = 0; i < 64; i++) begin : g_bit
            if (i < D) begin : g_pass
                assign g[s + 1][i] = g[s][i];
                assign p[s + 1][i] = p[s][i];
            end else begin : g_merge
                assign g[s + 1][i] = g[s][i] | (p[s][i] & g[s][i - D]);
                assign p[s + 1][i] = p[s][i] & p[s][i - D];
            end
        end
    end

    for (genvar i = 0; i < 64; i++) begin : g_sum
        assign c[i + 1] = g[6][i] | (p[6][i] & cin);
        assign sum[i]   = p[0][i] ^ c[i];
    end
    assign cout = c[64];
endmodule

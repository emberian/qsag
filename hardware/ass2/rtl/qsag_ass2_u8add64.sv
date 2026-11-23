// 6-level parallel-prefix 64b + 8b unsigned counter/PC adder (`< 5.0 ns` SS).
// Marked `(* keep_hierarchy *)` so synthesis/ABC preserves the parallel-prefix tree.
(* keep_hierarchy *)
module qsag_ass2_u8add64 (
    input  wire [63:0] x,
    input  wire [7:0]  inc,
    output wire [63:0] sum
);
    wire [7:0] lg [4];
    wire [7:0] lp [4];
    assign lg[0] = x[7:0] & inc;
    assign lp[0] = x[7:0] ^ inc;

    for (genvar s = 0; s < 3; s++) begin : g_lo_stage
        localparam int D = 1 << s;
        for (genvar i = 0; i < 8; i++) begin : g_lo_bit
            if (i < D) begin : g_lo_pass
                assign lg[s + 1][i] = lg[s][i];
                assign lp[s + 1][i] = lp[s][i];
            end else begin : g_lo_merge
                assign lg[s + 1][i] = lg[s][i] | (lp[s][i] & lg[s][i - D]);
                assign lp[s + 1][i] = lp[s][i] & lp[s][i - D];
            end
        end
    end

    assign sum[0] = lp[0][0];
    for (genvar i = 1; i < 8; i++) begin : g_lo_sum
        assign sum[i] = lp[0][i] ^ lg[3][i - 1];
    end
    wire c8 = lg[3][7];

    wire [55:0] hp [7];
    assign hp[0] = x[63:8];
    for (genvar s = 0; s < 6; s++) begin : g_hi_stage
        localparam int D = 1 << s;
        for (genvar k = 0; k < 56; k++) begin : g_hi_bit
            if (k < D) begin : g_hi_pass
                assign hp[s + 1][k] = hp[s][k];
            end else begin : g_hi_merge
                assign hp[s + 1][k] = hp[s][k] & hp[s][k - D];
            end
        end
    end

    assign sum[8] = x[8] ^ c8;
    for (genvar k = 1; k < 56; k++) begin : g_hi_sum
        assign sum[8 + k] = x[8 + k] ^ (c8 & hp[6][k - 1]);
    end
    wire unused_lp3 = |lp[3];
    wire unused_hp6 = hp[6][55];
endmodule

// Eight independent byte sums, with a three-level group carry prefix.
// The group generate comparison excludes carry-in; equality propagates it.
module qsag_ass2_add64 (
    input wire [63:0] a, b,
    input wire cin,
    output wire [63:0] sum,
    output wire cout
);
    wire [7:0] g [4], p [4];
    wire [8:0] c;
    assign c[0] = cin;
    for (genvar k=0; k<8; k++) begin : g_byte
        wire [7:0] x = a[8*k+:8], y = b[8*k+:8];
        assign g[0][k] = x > ~y;
        assign p[0][k] = &(x | y);
        assign sum[8*k+:8] = x + y + {7'd0,c[k]};
        assign c[k+1] = g[3][k] || (p[3][k] && cin);
    end
    for (genvar j=0; j<3; j++) begin : g_level
        for (genvar k=0; k<8; k++) begin : g_prefix
            if (k < (1<<j)) begin : g_copy
                assign g[j+1][k] = g[j][k];
                assign p[j+1][k] = p[j][k];
            end else begin : g_join
                assign g[j+1][k] = g[j][k] || (p[j][k] && g[j][k-(1<<j)]);
                assign p[j+1][k] = p[j][k] && p[j][k-(1<<j)];
            end
        end
    end
    assign cout = c[8];
endmodule

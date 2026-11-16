// Carry-less (GF(2)[x]) multiplier, W x W -> 2W-1 bits, recursive Karatsuba down to a
// schoolbook AND/XOR base of at most BASE bits. Pure LUT XOR trees, combinational.
module qsag_clmul_kara #(
    parameter int W = 128,
    parameter int BASE = 8
) (
    input  logic [W-1:0]     a,
    input  logic [W-1:0]     b,
    output logic [2*W-2:0]   p
);
    if (W <= BASE) begin : g_base
        always_comb begin
            p = '0;
            for (int i = 0; i < W; i++)
                p = p ^ (({(2*W-1){b[i]}} & (2*W-1)'(a)) << i);
        end
    end else begin : g_kara
        localparam int H  = W / 2;       // low half
        localparam int HH = W - H;       // high half, HH >= H
        logic [2*H-2:0]  lo;
        logic [2*HH-2:0] hi, mid;
        logic [HH-1:0]   as, bs;
        assign as = a[W-1:H] ^ HH'(a[H-1:0]);
        assign bs = b[W-1:H] ^ HH'(b[H-1:0]);
        qsag_clmul_kara #(.W(H),  .BASE(BASE)) u_lo  (.a(a[H-1:0]), .b(b[H-1:0]), .p(lo));
        qsag_clmul_kara #(.W(HH), .BASE(BASE)) u_hi  (.a(a[W-1:H]), .b(b[W-1:H]), .p(hi));
        qsag_clmul_kara #(.W(HH), .BASE(BASE)) u_mid (.a(as), .b(bs), .p(mid));
        logic [2*HH-2:0] xmid;
        assign xmid = mid ^ hi ^ (2*HH-1)'(lo);
        assign p = (2*W-1)'(lo) ^ ((2*W-1)'(hi) << (2*H)) ^ ((2*W-1)'(xmid) << H);
    end
endmodule

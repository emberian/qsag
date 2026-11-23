// Area proxy of the revised TRNG (physics lane, 2026-11-17): eight rings of 17 nand2_1 with coherent
// sampling, in front of the existing health-test and word-assembly logic (qsag_trng, which keeps its
// own two rings here: 20 cells too many, noted in the report). Not simulated.
`default_nettype none
module px_trng8 (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         en,
    input  wire         take,
    output wire [63:0]  word,
    output wire         valid, ok, rct_fail, apt_fail, raw_bit
);
    wire [7:0] r;
    logic [7:0] s0, s1;
    logic [15:0] beat;
    genvar i;
    generate
        for (i = 0; i < 8; i++) begin : g_ring
            qsag_ring_osc #(.N(17)) u_r (.en(en), .osc(r[i]));
        end
    endgenerate
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin s0 <= '0; s1 <= '0; beat <= '0; end
        else begin
            s0 <= r; s1 <= s0;
            beat <= (^(s0 ^ s1)) ? 16'd0 : beat + 16'd1;
        end
    end
    wire [63:0] w;
    wire rb;
    qsag_trng u_t (.clk(clk), .rst_n(rst_n), .en(en), .take(take), .word(w), .valid(valid), .ok(ok),
                   .rct_fail(rct_fail), .apt_fail(apt_fail), .raw_bit(rb));
    assign word = w ^ {48'd0, beat};
    assign raw_bit = rb ^ (^s1);
endmodule
`default_nettype wire

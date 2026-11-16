// Fixed delay line of N clocks in block RAM: a circular buffer written every clock and read
// N-1 addresses behind through the registered read port. Replaces W x N shift-register LUTs.
// N >= 2. The first N outputs after power-up are undefined.
module qsag_bram_delay #(
    parameter int W = 64,
    parameter int N = 600
) (
    input  logic         clk,
    input  logic [W-1:0] d,
    output logic [W-1:0] q
);
    localparam int AW = $clog2(N);
    logic [AW-1:0] wp;   // free-running; any start value gives the same delay
    logic [AW-1:0] rp;
    always_ff @(posedge clk) wp <= wp + AW'(1);
    assign rp = wp - AW'(N - 1);
    qsag_sdp_bram #(.AW(AW), .DW(W)) u_ram (.clk(clk), .we(1'b1), .wa(wp), .wd(d), .ra(rp), .rd(q));
endmodule

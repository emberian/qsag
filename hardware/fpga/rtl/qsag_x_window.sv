// Synchronous operand window. Consecutive lanes in a group live in separate
// memories, so a group read uses wires from the EBRs with no word crossbar.
// Copies have independent read addresses and share the accepted AXI write.
module qsag_x_window #(
    parameter int LANE_BITS = 2
) (
    input  logic clk,
    input  logic [5:0] wa,           // 32-bit AXI word index
    input  logic [3:0] we,
    input  logic [31:0] wd,
    input  logic [4-LANE_BITS:0] ra, // group of 2**LANE_BITS consecutive limbs
    output logic [(64 << LANE_BITS)-1:0] rd
);
    for (genvar i = 0; i < (1 << LANE_BITS); i++) begin : g_lane
`ifdef QSAG_ECP5_CARRY
        localparam int DEPTH = 512;
        wire [8:0] widx = 9'(wa[5:1+LANE_BITS]);
        wire [8:0] ridx = 9'(ra);
`else
        localparam int DEPTH = 1 << (5-LANE_BITS);
        wire [4-LANE_BITS:0] widx = wa[5:1+LANE_BITS];
        wire [4-LANE_BITS:0] ridx = ra;
`endif
        (* ram_style = "block", no_rw_check *) logic [63:0] mem [DEPTH];
        wire selected = (int'(wa[5:1]) & ((1 << LANE_BITS)-1)) == i;
        always_ff @(posedge clk) begin
            for (int b = 0; b < 8; b++) begin
                if (selected && wa[0] == (b >= 4) && we[b % 4])
                    mem[widx][8*b +: 8] <= wd[8*(b%4) +: 8];
            end
            rd[64*i +: 64] <= mem[ridx];
        end
    end
endmodule

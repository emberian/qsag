// Simple dual-port synchronous RAM: one write port, one registered read port, one clock.
// Infers block RAM (RAMB36E2 / DP16KD). A read of an address written in the same cycle
// returns the old contents (read-first).
module qsag_sdp_bram #(
    parameter int AW = 10,
    parameter int DW = 256
) (
    input  logic          clk,
    input  logic          we,
    input  logic [AW-1:0] wa,
    input  logic [DW-1:0] wd,
    input  logic [AW-1:0] ra,
    output logic [DW-1:0] rd
);
    logic [DW-1:0] mem [1 << AW];
    always_ff @(posedge clk) begin
        if (we) mem[wa] <= wd;
        rd <= mem[ra];
    end
endmodule

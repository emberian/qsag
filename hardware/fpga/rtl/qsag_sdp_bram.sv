// Simple dual-port synchronous RAM: one write port, one registered read port, one clock.
// Infers block RAM (RAMB36E2 / DP16KD). When NO_RW_CHECK=1, callers guarantee write and read
// addresses never collide on the same active cycle, eliminating soft collision-bypass LUTs/FFs.
// When FORCE_BRAM=1 and AW < 9, pads depth to 512 so ECP5 maps wide shallow tables to DP16KD
// instead of distributed LUTRAM (TRELLIS_DPR16X4).
module qsag_sdp_bram #(
    parameter int AW          = 10,
    parameter int DW          = 256,
    parameter bit NO_RW_CHECK = 1'b0,
    parameter bit FORCE_BRAM  = 1'b0
) (
    input  logic          clk,
    input  logic          we,
    input  logic [AW-1:0] wa,
    input  logic [DW-1:0] wd,
    input  logic [AW-1:0] ra,
    output logic [DW-1:0] rd
);
    localparam int EFF_AW = (FORCE_BRAM && (AW < 9)) ? 9 : AW;
    wire [EFF_AW-1:0] eff_wa = EFF_AW'(wa);
    wire [EFF_AW-1:0] eff_ra = EFF_AW'(ra);

    localparam bit USE_BLOCK = FORCE_BRAM || (AW > 4);

    if (USE_BLOCK) begin : g_blk
        if (NO_RW_CHECK) begin : g_norw
            (* ram_style = "block", no_rw_check *) logic [DW-1:0] mem [1 << EFF_AW];
            always_ff @(posedge clk) begin
                if (we) mem[eff_wa] <= wd;
                rd <= mem[eff_ra];
            end
        end else begin : g_std
            (* ram_style = "block" *) logic [DW-1:0] mem [1 << EFF_AW];
            always_ff @(posedge clk) begin
                if (we) mem[eff_wa] <= wd;
                rd <= mem[eff_ra];
            end
        end
    end else begin : g_dist
        (* ram_style = "distributed" *) logic [DW-1:0] mem [1 << EFF_AW];
        always_ff @(posedge clk) begin
            if (we) mem[eff_wa] <= wd;
            rd <= mem[eff_ra];
        end
    end
endmodule

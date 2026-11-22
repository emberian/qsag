// One resettable inverting feedback path. Each stage is a distinct foundry cell.
module qsag_ass2_ring #(parameter int STAGES = 17) (
    input wire en, output wire osc
);
`ifdef ASS2_FAST_ENTROPY
`ifdef SYNTHESIS
    ASS2_FAST_ENTROPY_IS_SIMULATION_ONLY invalid_configuration();
`endif
    wire unused = en ^ (STAGES == 0);
    assign osc = 1'b0;
`else
`ifdef QSAG_F2_CLOUD_BRINGUP
    wire unused = en ^ (STAGES == 0);
    assign osc = 1'b0;
`else
    wire [STAGES-1:0] stage;
    (* keep = "true", dont_touch = "true" *) LUT2 #(.INIT(4'h7)) u_gate (
        .I0(en), .I1(stage[STAGES-1]), .O(stage[0])
    );
    for (genvar j = 1; j < STAGES; j++) begin : g_inv
        (* keep = "true", dont_touch = "true" *) LUT1 #(.INIT(2'b01)) u_inv (.I0(stage[j-1]), .O(stage[j]));
    end
    assign osc = stage[STAGES-1];
`endif
`endif
endmodule

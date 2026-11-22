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
    wire [STAGES-1:0] stage;
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__nand2_1 u_gate (
        .A1(en), .A2(stage[STAGES-1]), .ZN(stage[0])
    );
    for (genvar j = 1; j < STAGES; j++) begin : g_inv
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__inv_1 u_inv (.I(stage[j-1]), .ZN(stage[j]));
    end
    assign osc = stage[STAGES-1];
`endif
endmodule

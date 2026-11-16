// Dregg-180 Organ 5 (Physical Mesh & Spatial Glitch Sensors):
//   1. 4-Quadrant Distributed `dont_touch` Delay-Spine Glitch Canaries (`u_qcanary[0..3]`):
//      Four independent tunable delay-spine timing sensors distributed across NW, NE, SW, SE
//      quadrants of the enclave core. Any localized EMFI, substrate bounce, or laser/clock glitch
//      causing any of the 4 quadrant spines to miss its capture edge immediately raises
//      `fault_quad_glitch` -> 1-clock emergency zeroization + sticky FAULT.
//   2. Active `Metal5`-Routed PRNG Serpentine Integrity Loop (`shield_tx -> dont_touch spine -> shield_rx`):
//      A TRNG-stirred 32-bit Galois LFSR injects fresh unpredictable bits every clock through a
//      16-stage (* keep *) buffer serpentine chain routed across Metal5 (top routing layer of
//      gf180mcuD 5LM). Any FIB cut, tie-off, short, or probe-capacitance delay overload causes
//      `shield_rx != shield_exp` -> immediate `fault_shield` + 1-clock zeroization!
`default_nettype none
`timescale 1ps / 1ps

module dregg_quad_canary_spine (
    input  wire       launch,
    input  wire [2:0] tap_sel,
    output wire       arrived
);
    wire [32:0] c;
    wire [31:0] h;
    assign c[0] = launch;
    genvar i;
    generate
        for (i = 0; i < 32; i++) begin : g_sp
            qsag_dly_inv #(.TD(180)) u_a (.a(c[i]), .y(h[i]));
            qsag_dly_inv #(.TD(180)) u_b (.a(h[i]), .y(c[i+1]));
        end
    endgenerate
    logic tap_o;
    always_comb begin
        tap_o = c[4];
        for (int k = 0; k < 8; k++)
            if (tap_sel == 3'(k)) tap_o = c[4 * (k + 1)];
    end
    assign arrived = tap_o;
endmodule

module dregg_metal5_shield_spine (
    input  wire shield_tx,
    input  wire fib_cut_inj,   // verification hook for FIB probe/cut fault-injection test
    output wire shield_rx
);
    (* keep *) wire [16:0] m5_serpentine_net;
    assign m5_serpentine_net[0] = shield_tx;
    genvar i;
    generate
        for (i = 0; i < 16; i++) begin : g_m5
            qsag_shield_buf #(.TD(200)) u_m5buf (
                .a(m5_serpentine_net[i]),
                .y(m5_serpentine_net[i+1])
            );
        end
    endgenerate
    assign shield_rx = m5_serpentine_net[16] ^ fib_cut_inj;
endmodule

module dregg_shield_canaries (
    input  wire        clk,
    input  wire        rst_n,
    input  wire        canary_arm,
    input  wire [2:0]  canary_tap,
    input  wire        shield_en,
    input  wire        trng_bit,
    input  wire        fib_cut_inj,
    output logic       fault_quad_glitch,
    output logic       fault_shield,
    output wire [3:0]  quad_trip_map
);
    // ------------------------------------------------------------ 4-Quadrant Glitch Canaries
    logic [3:0] ql_launch, ql_prev, ql_cap, ql_trip;
    wire  [3:0] ql_arr;

    genvar q;
    generate
        for (q = 0; q < 4; q++) begin : g_quad
            dregg_quad_canary_spine u_qsp (
                .launch(ql_launch[q]), .tap_sel(canary_tap), .arrived(ql_arr[q])
            );
        end
    endgenerate

    assign quad_trip_map = ql_trip;

    // ------------------------------------------------------------ Active Metal5 PRNG Shield Loop
    logic [31:0] shield_lfsr;
    logic        shield_tx_q, shield_exp_q, shield_rx_s;
    logic [2:0]  shield_warm;
    wire         shield_rx_w;

    dregg_metal5_shield_spine u_m5_loop (
        .shield_tx(shield_tx_q), .fib_cut_inj(fib_cut_inj), .shield_rx(shield_rx_w)
    );

    wire next_prng_bit = shield_lfsr[31] ^ shield_lfsr[21] ^ shield_lfsr[1] ^ shield_lfsr[0] ^ trng_bit;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ql_launch         <= 4'b0101;
            ql_prev           <= 4'b0101;
            ql_cap            <= 4'b0101;
            ql_trip           <= 4'b0000;
            fault_quad_glitch <= 1'b0;
            shield_lfsr       <= 32'hD180_5A3C;
            shield_tx_q       <= 1'b0;
            shield_exp_q      <= 1'b0;
            shield_rx_s       <= 1'b0;
            shield_warm       <= 3'd0;
            fault_shield      <= 1'b0;
        end else begin
            // 4-quadrant glitch canaries
            if (canary_arm) begin
                ql_launch <= ~ql_launch;
                ql_prev   <= ql_launch;
                ql_cap    <= ql_arr;
                if ((ql_cap ^ ql_prev) != 4'b0000) begin
                    ql_trip           <= ql_trip | (ql_cap ^ ql_prev);
                    fault_quad_glitch <= 1'b1;
                end
            end else begin
                ql_prev <= ql_launch;
                ql_cap  <= ql_arr;
            end

            // Active Metal5 serpentine integrity loop
            if (shield_en) begin
                shield_lfsr  <= {shield_lfsr[30:0], next_prng_bit};
                shield_tx_q  <= next_prng_bit;
                shield_exp_q <= shield_tx_q;
                shield_rx_s  <= shield_rx_w;
                if (shield_warm != 3'd4) begin
                    shield_warm <= shield_warm + 3'd1;
                end else if (shield_rx_s != shield_exp_q) begin
                    fault_shield <= 1'b1;
                end
            end else begin
                shield_warm <= 3'd0;
            end
        end
    end
endmodule
`default_nettype wire

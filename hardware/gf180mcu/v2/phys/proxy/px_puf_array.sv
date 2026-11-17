// Area and placement proxy of the PUF key array as the physics lane specifies it
// (physics/puf/placement_requirements.md): 252 quads = 1008 rings, one ring enabled at a time, every
// ring in its own slot (enable buffer, five nand2_1, output isolation buffer), plus the dummy slots
// that surround the array (enable tied low, output unconnected). Not simulated.
// floorplan/puf_array.tcl places g_q[q].g_r[k].u_s and g_dum[d].u_s; NDUM must match its geometry.
`default_nettype none
module px_puf_slot (
    input  wire en,
    output wire out
);
    wire e;
    /* verilator lint_off UNOPTFLAT */
    wire [5:0] n;
    /* verilator lint_on UNOPTFLAT */
    assign n[0] = n[5];
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__buf_2 u_en (.I(en), .Z(e));
    genvar s;
    generate
        for (s = 0; s < 5; s++) begin : g_st
            wire g = (s == 0) ? e : n[s];
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__nand2_1 u_n (.A1(n[s]), .A2(g), .ZN(n[s+1]));
        end
    endgenerate
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__buf_2 u_out (.I(n[5]), .Z(out));
endmodule

module px_puf_array #(parameter int NQ = 252, parameter int NDUM = 224) (
    input  wire       en,
    input  wire [9:0] ring,        // 4 * quad + position
    output wire       osc
);
    wire [4*NQ-1:0] o;
    genvar q, k, d;
    generate
        for (q = 0; q < NQ; q++) begin : g_q
            for (k = 0; k < 4; k++) begin : g_r
                wire e = en && (ring == 10'(4 * q + k));
                px_puf_slot u_s (.en(e), .out(o[4*q+k]));
            end
        end
        for (d = 0; d < NDUM; d++) begin : g_dum
            /* verilator lint_off PINCONNECTEMPTY */
            px_puf_slot u_s (.en(1'b0), .out());
            /* verilator lint_on PINCONNECTEMPTY */
        end
    endgenerate
    assign osc = |o;
endmodule
`default_nettype wire

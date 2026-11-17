// Area and placement proxy of the PUF key array as the physics lane specifies it
// (physics/puf/placement_requirements.md): 252 quads = 1008 rings, one ring enabled at a time, every
// ring in its own 43-site slot, dummy slots at both row ends and a dummy row above and below.
// Not simulated.
//
// Change proposed by the physical-design lane after run g2 (flat decode: 1008 enable wires and 1008
// ring outputs = 2016 vertical wires into a 674 um wide, 100 % full box; about 1,600 Metal2 + Metal4
// tracks exist there; measured 4,300 tracks of global-route overflow under the array):
//   * the slot's enable buffer becomes an and2_1 of a row line and a column line (same 8 sites);
//   * the slot's output buffer becomes an and2_1 that chains the ring into its row's output
//     (a disabled ring rests high), same 8 sites; the ring node still sees one identical gate input.
// 44 row lines, 28 column lines and 42 row outputs replace 2016 wires. Slot size and cell count are
// unchanged. Whether the chain's left neighbour input upsets the matching is for the physics lane.
// floorplan/puf_array.tcl places g_r[r].g_c[c].u_s on the grid.
`default_nettype none
module px_puf_slot (
    input  wire en_r, en_c, cin,
    output wire cout
);
    wire e;
    /* verilator lint_off UNOPTFLAT */
    wire [5:0] n;
    /* verilator lint_on UNOPTFLAT */
    assign n[0] = n[5];
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__and2_1 u_en (.A1(en_r), .A2(en_c), .Z(e));
    genvar s;
    generate
        for (s = 0; s < 5; s++) begin : g_st
            wire g = (s == 0) ? e : n[s];
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__nand2_1 u_n (.A1(n[s]), .A2(g), .ZN(n[s+1]));
        end
    endgenerate
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__and2_1 u_out (.A1(n[5]), .A2(cin), .Z(cout));
endmodule

module px_puf_array #(parameter int NR = 42, parameter int NC = 24) (
    input  wire       en,
    input  wire [5:0] row,         // 0 .. NR-1
    input  wire [4:0] col,         // 0 .. NC-1 (quad = col / 4, position = col % 4)
    output wire       osc
);
    wire [NR-1:0] ro;
    genvar r, c;
    generate
        for (r = 0; r < NR + 2; r++) begin : g_r
            wire used_r = (r >= 1) && (r <= NR);
            wire er = used_r ? (en && (row == 6'(r - 1))) : 1'b0;
            wire [NC+4:0] ch;
            assign ch[2] = 1'b1;
            for (c = 0; c < NC + 4; c++) begin : g_c
                if (r >= 1 && r <= NR && c >= 2 && c < NC + 2) begin : g_u
                    px_puf_slot u_s (.en_r(er), .en_c(col == 5'(c - 2)), .cin(ch[c]), .cout(ch[c+1]));
                end else begin : g_d
                    /* verilator lint_off PINCONNECTEMPTY */
                    px_puf_slot u_s (.en_r(1'b0), .en_c(1'b0), .cin(1'b1), .cout());
                    /* verilator lint_on PINCONNECTEMPTY */
                end
            end
            if (r >= 1 && r <= NR) begin : g_o
                assign ro[r-1] = ch[NC+2];
            end
        end
    endgenerate
    assign osc = &ro;
endmodule
`default_nettype wire

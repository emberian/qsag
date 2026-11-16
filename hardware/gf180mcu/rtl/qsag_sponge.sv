// QSAG-NI-180 shared 1,600-bit sponge / register file.
//
// 25 lanes of 64 bits with asynchronous clear (they hold secrets during enclave operations):
//   * Keccak-f[1600] state a[x + 5y] = lane x + 5y, one round per clock when k_en is high;
//   * Poseidon2 width-12 state in lanes 0..11 and the field registers CH/A/B in lanes 12..23
//     when the field engine owns them (one 64-bit read port, one 64-bit write port).
// The 8 x 64-bit shadow buffer (addresses 32..39) is part of the same address space: it is the
// stream elasticity buffer in Keccak streaming and the X/Y operand registers of the verifier.
`default_nettype none

module qsag_keccak_round (
    input  wire [1599:0] a,
    input  wire [63:0]   rc,
    output wire [1599:0] o
);
    function automatic int rot(input int x, input int y);
        case (x + 5 * y)
            0:  rot = 0;   1:  rot = 1;   2:  rot = 62;  3:  rot = 28;  4:  rot = 27;
            5:  rot = 36;  6:  rot = 44;  7:  rot = 6;   8:  rot = 55;  9:  rot = 20;
            10: rot = 3;   11: rot = 10;  12: rot = 43;  13: rot = 25;  14: rot = 39;
            15: rot = 41;  16: rot = 45;  17: rot = 15;  18: rot = 21;  19: rot = 8;
            20: rot = 18;  21: rot = 2;   22: rot = 61;  23: rot = 56;  24: rot = 14;
            default: rot = 0;
        endcase
    endfunction

    wire [63:0] la [25];
    wire [63:0] c  [5];
    wire [63:0] d  [5];
    wire [63:0] b  [25];
    genvar x, y;
    generate
        for (x = 0; x < 25; x++) begin : g_la
            assign la[x] = a[64*x +: 64];
        end
        for (x = 0; x < 5; x++) begin : g_theta
            assign c[x] = la[x] ^ la[x+5] ^ la[x+10] ^ la[x+15] ^ la[x+20];
            assign d[x] = c[(x+4)%5] ^ {c[(x+1)%5][62:0], c[(x+1)%5][63]};
        end
        for (x = 0; x < 5; x++) begin : g_rho_x
            for (y = 0; y < 5; y++) begin : g_rho_y
                localparam int R = rot(x, y);
                wire [63:0] e = la[x + 5*y] ^ d[x];
                if (R == 0) begin : g_r0
                    assign b[y + 5*((2*x + 3*y) % 5)] = e;
                end else begin : g_rn
                    assign b[y + 5*((2*x + 3*y) % 5)] = {e[63-R:0], e[63:64-R]};
                end
            end
        end
        for (x = 0; x < 5; x++) begin : g_chi_x
            for (y = 0; y < 5; y++) begin : g_chi_y
                wire [63:0] t = b[x + 5*y] ^ (~b[(x+1)%5 + 5*y] & b[(x+2)%5 + 5*y]);
                if (x == 0 && y == 0) begin : g_iota
                    assign o[63:0] = t ^ rc;
                end else begin : g_plain
                    assign o[64*(x + 5*y) +: 64] = t;
                end
            end
        end
    endgenerate
endmodule

module qsag_sponge (
    input  wire         clk,
    input  wire         rst_n,     // asynchronous clear of the 25 lanes (reset and zeroize)
    input  wire         k_en,      // apply one Keccak round to all lanes
    input  wire [63:0]  k_rc,
    input  wire         wr_en,
    input  wire [5:0]   wr_addr,   // 0..24 lanes, 32..39 shadow
    input  wire [63:0]  wr_data,
    input  wire [5:0]   rd_addr,
    output logic [63:0] rd_data
);
    wire [1599:0] st;
    wire [1599:0] kout;
    wire [63:0]   sh [8];
    qsag_keccak_round u_round (.a(st), .rc(k_rc), .o(kout));

    genvar i;
    generate
        for (i = 0; i < 25; i++) begin : g_lane
            wire we = wr_en && (wr_addr == 6'(i));
            qsag_ereg #(.W(64)) u_r (
                .clk(clk), .rst_n(rst_n), .en(k_en | we),
                .d(k_en ? kout[64*i +: 64] : wr_data), .q(st[64*i +: 64])
            );
        end
        for (i = 0; i < 8; i++) begin : g_shadow
            wire we = wr_en && (wr_addr == 6'(32 + i));
            qsag_ereg_nr #(.W(64)) u_r (.clk(clk), .en(we), .d(wr_data), .q(sh[i]));
        end
    endgenerate

    always_comb begin
        rd_data = '0;
        if (rd_addr[5]) rd_data = sh[rd_addr[2:0]];
        else begin
            for (int l = 0; l < 25; l++) if (rd_addr[4:0] == 5'(l)) rd_data = st[64*l +: 64];
        end
    end
endmodule
`default_nettype wire

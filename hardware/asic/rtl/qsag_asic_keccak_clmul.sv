// QSAG-NI symmetric units: Keccak-f[1600] at two rounds per clock (Keccak-p[1600,12] for
// TurboSHAKE256 in 6 clocks, 24 rounds for SHA-3/SHAKE in 12) and a single-cycle GF(2^128)
// multiplier (Karatsuba over three 64x64 carry-less trees, reduction by z^128 + z^7 + z^2 + z + 1),
// with the Wiedemann tower T_7 basis maps around it.
`default_nettype none

module qsag_keccak_round (
  input  wire [1599:0] a,     // lane (x, y) at bits [64*(x + 5y) +: 64]
  input  wire [63:0]   rc,
  output wire [1599:0] o
);
  function automatic int rot(input int x, input int y);
    int r, t, cx, cy, nx;
    r = 0; cx = 1; cy = 0;
    if (x == 0 && y == 0) return 0;
    for (t = 0; t < 24; t++) begin
      if (cx == x && cy == y) r = ((t + 1) * (t + 2) / 2) % 64;
      nx = cy; cy = (2 * cx + 3 * cy) % 5; cx = nx;
    end
    return r;
  endfunction

  wire [63:0] la [25];
  wire [63:0] lc [5];
  wire [63:0] ld [5];
  wire [63:0] lt [25];
  wire [63:0] lb [25];
  for (genvar i = 0; i < 25; i++) begin : g_in
    assign la[i] = a[64*i +: 64];
  end
  for (genvar x = 0; x < 5; x++) begin : g_theta
    assign lc[x] = la[x] ^ la[x + 5] ^ la[x + 10] ^ la[x + 15] ^ la[x + 20];
    assign ld[x] = lc[(x + 4) % 5] ^ {lc[(x + 1) % 5][62:0], lc[(x + 1) % 5][63]};
  end
  for (genvar x = 0; x < 5; x++) begin : g_rp_x
    for (genvar y = 0; y < 5; y++) begin : g_rp_y
      localparam int ROT = rot(x, y);
      assign lt[x + 5*y] = la[x + 5*y] ^ ld[x];
      if (ROT == 0) begin : g_r0
        assign lb[y + 5*((2*x + 3*y) % 5)] = lt[x + 5*y];
      end else begin : g_r
        assign lb[y + 5*((2*x + 3*y) % 5)] = {lt[x + 5*y][63-ROT:0], lt[x + 5*y][63:64-ROT]};
      end
    end
  end
  for (genvar i = 0; i < 25; i++) begin : g_chi
    wire [63:0] chi = lb[i] ^ (~lb[(i % 5 + 1) % 5 + 5*(i / 5)] & lb[(i % 5 + 2) % 5 + 5*(i / 5)]);
    assign o[64*i +: 64] = (i == 0) ? chi ^ rc : chi;
  end
endmodule

module qsag_keccak_2rpc (
  input  wire          clk,
  input  wire          rst,
  input  wire          start,      // begin a permutation (idle only)
  input  wire          rounds12,   // 1: Keccak-p[1600,12] (rounds 12..23); 0: all 24
  input  wire          lane_we,    // idle only
  input  wire          lane_xor,   // 1: XOR into the lane (absorb); 0: overwrite
  input  wire [4:0]    lane_idx,
  input  wire [63:0]   lane_wdata,
  input  wire          save,       // idle only: shadow <- state (customization midstate)
  input  wire          restore,    // idle only: state <- shadow
  output wire [63:0]   lane_rdata,
  output wire          busy
);
  function automatic logic [63:0] rcon(input logic [4:0] i);
    case (i)
      5'd0:  rcon = 64'h0000000000000001; 5'd1:  rcon = 64'h0000000000008082;
      5'd2:  rcon = 64'h800000000000808A; 5'd3:  rcon = 64'h8000000080008000;
      5'd4:  rcon = 64'h000000000000808B; 5'd5:  rcon = 64'h0000000080000001;
      5'd6:  rcon = 64'h8000000080008081; 5'd7:  rcon = 64'h8000000000008009;
      5'd8:  rcon = 64'h000000000000008A; 5'd9:  rcon = 64'h0000000000000088;
      5'd10: rcon = 64'h0000000080008009; 5'd11: rcon = 64'h000000008000000A;
      5'd12: rcon = 64'h000000008000808B; 5'd13: rcon = 64'h800000000000008B;
      5'd14: rcon = 64'h8000000000008089; 5'd15: rcon = 64'h8000000000008003;
      5'd16: rcon = 64'h8000000000008002; 5'd17: rcon = 64'h8000000000000080;
      5'd18: rcon = 64'h000000000000800A; 5'd19: rcon = 64'h800000008000000A;
      5'd20: rcon = 64'h8000000080008081; 5'd21: rcon = 64'h8000000000008080;
      5'd22: rcon = 64'h0000000080000001; 5'd23: rcon = 64'h8000000080008008;
      default: rcon = 64'h0;
    endcase
  endfunction

  logic [1599:0] s, shadow;
  logic [4:0]    r;        // next round index (even)
  logic          run;
  wire  [1599:0] m, n;
  qsag_keccak_round u_r0 (.a(s), .rc(rcon(r)),        .o(m));
  qsag_keccak_round u_r1 (.a(m), .rc(rcon(r | 5'd1)), .o(n));
  assign busy = run;
  assign lane_rdata = s[64*lane_idx +: 64];
  always_ff @(posedge clk) begin
    if (rst) begin
      s <= '0; run <= 1'b0; r <= '0;
    end else if (run) begin
      s <= n;
      r <= r + 5'd2;
      if (r == 5'd22) run <= 1'b0;
    end else begin
      if (lane_we) s[64*lane_idx +: 64] <= lane_xor ? (s[64*lane_idx +: 64] ^ lane_wdata) : lane_wdata;
      if (save) shadow <= s;
      if (restore) s <= shadow;
      if (start) begin
        run <= 1'b1;
        r <= rounds12 ? 5'd12 : 5'd0;
      end
    end
  end
endmodule

// 64 x 64 -> 127-bit carry-less product: every output bit is one balanced XOR reduction.
module qsag_clmul64 (
  input  wire [63:0]  a,
  input  wire [63:0]  b,
  output wire [126:0] p
);
  for (genvar k = 0; k < 127; k++) begin : g_col
    wire [63:0] v;
    for (genvar i = 0; i < 64; i++) begin : g_pp
      if (k - i >= 0 && k - i < 64) begin : g_in
        assign v[i] = a[i] & b[k - i];
      end else begin : g_z
        assign v[i] = 1'b0;
      end
    end
    assign p[k] = ^v;
  end
endmodule

// a * b in F_2[z] / (z^128 + z^7 + z^2 + z + 1), structured as clmul128_wide_portable +
// clmul256_reduce_0x87 (crates/qsag-asm/src/portable.rs).
module qsag_gf128_mul (
  input  wire [127:0] a,
  input  wire [127:0] b,
  output wire [127:0] r
);
  wire [126:0] z0, z2, zm;
  qsag_clmul64 u_lo  (.a(a[63:0]),             .b(b[63:0]),             .p(z0));
  qsag_clmul64 u_hi  (.a(a[127:64]),           .b(b[127:64]),           .p(z2));
  qsag_clmul64 u_mid (.a(a[63:0] ^ a[127:64]), .b(b[63:0] ^ b[127:64]), .p(zm));
  wire [126:0] z1 = zm ^ z0 ^ z2;
  wire [254:0] c  = {128'b0, z0} ^ {z2, 128'b0} ^ {64'b0, z1, 64'b0};
  wire [126:0] h  = c[254:128];
  // h * (z^7 + z^2 + z + 1): 134 bits; its top 6 bits fold once more.
  wire [133:0] f  = {7'b0, h} ^ {6'b0, h, 1'b0} ^ {5'b0, h, 2'b0} ^ {h, 7'b0};
  wire [5:0]   g  = f[133:128];
  wire [127:0] f2 = {122'b0, g} ^ {121'b0, g, 1'b0} ^ {120'b0, g, 2'b0} ^ {115'b0, g, 7'b0};
  assign r = c[127:0] ^ f[127:0] ^ f2;
endmodule

// Product in the Wiedemann tower T_7 (the field of the `tower128` vectors).
module qsag_tower128_mul (
  input  wire [127:0] a,
  input  wire [127:0] b,
  output wire [127:0] r
);
  wire [127:0] pa, pb, pr;
  qsag_tower128_to_poly u_a (.x(a), .y(pa));
  qsag_tower128_to_poly u_b (.x(b), .y(pb));
  qsag_gf128_mul u_mul (.a(pa), .b(pb), .r(pr));
  qsag_poly_to_tower128 u_r (.x(pr), .y(r));
endmodule
`default_nettype wire

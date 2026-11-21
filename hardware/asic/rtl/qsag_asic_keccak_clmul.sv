// QSAG-NI symmetric units:
//   * Keccak-f[1600] at two rounds per clock (Keccak-p[1600,12] for TurboSHAKE256 in 6 clocks,
//     24 rounds for SHA-3/SHAKE in 12 clocks), with 1600-bit customization shadow state, dual-lane
//     SRAM absorb, and direct 69-byte Canopy internal node framing (`canopy_node_go`).
//   * Single-cycle GF(2^128) multiplier (recursive carry-less Karatsuba over three 64x64 trees,
//     8-bit symbolic-LEC leaf, reduction by z^128 + z^7 + z^2 + z + 1) + Wiedemann T_7 basis maps.
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
  input  wire          start,           // begin a permutation (idle only)
  input  wire          rounds12,        // 1: Keccak-p[1600,12] (rounds 12..23); 0: all 24
  input  wire          lane_we,         // single-lane write/XOR (idle only)
  input  wire          lane_xor,        // 1: XOR into lane; 0: overwrite
  input  wire [4:0]    lane_idx,
  input  wire [63:0]   lane_wdata,
  input  wire          pair_xor_en,     // dual-lane XOR from dual-port SRAM (idle only)
  input  wire [4:0]    pair_idx,
  input  wire          pair_single,
  input  wire [63:0]   pair_w0,
  input  wire [63:0]   pair_w1,
  input  wire          pad_end_en,      // XOR 0x8000_0000_0000_0000 into lane 16
  input  wire          canopy_node_go,  // restore shadow + XOR 69B [0x00|idx|left|right|0x07..0x80] + start 12r
  input  wire [31:0]   canopy_node_idx,
  input  wire [255:0]  canopy_left,
  input  wire [255:0]  canopy_right,
  input  wire          save,            // idle only: shadow <- state
  input  wire          restore,         // idle only: state <- shadow
  output wire [63:0]   lane_rdata,
  output wire [255:0]  digest_o,
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

  logic [63:0]   sl [25];
  logic [63:0]   sh [25];
  logic [1599:0] s_flat, sh_flat;
  for (genvar i = 0; i < 25; i++) begin : g_pack
    assign s_flat[64*i +: 64]  = sl[i];
    assign sh_flat[64*i +: 64] = sh[i];
  end

  logic [4:0] r;
  logic       run;
  (* keep = "true" *) logic [24:0] run_l;

  // 69-byte Canopy Merkle internal node block: [8'h00, node_idx(32b), left(256b), right(256b), 8'h07, 0.., 8'h80]
  wire [575:0] cn_raw = {16'h0000, 8'h07, canopy_right, canopy_left, canopy_node_idx, 8'h00};
  logic [1599:0] cn_init;
  always_comb begin
    cn_init = sh_flat;
    for (int i = 0; i < 9; i++) cn_init[64*i +: 64] = sh_flat[64*i +: 64] ^ cn_raw[64*i +: 64];
    cn_init[64*16 + 63] = sh_flat[64*16 + 63] ^ 1'b1;
  end

  // Combinational pre-padded state so pad_end_en + start takes effect on round 0/12 immediately!
  logic [63:0] sl_idle [25];
  always_comb begin
    for (int i = 0; i < 25; i++) begin
      if (restore) begin
        sl_idle[i] = sh[i];
      end else begin
        sl_idle[i] = sl[i];
        if (lane_we && (lane_idx == 5'(i))) begin
          sl_idle[i] = lane_xor ? (sl[i] ^ lane_wdata) : lane_wdata;
        end
        if (pair_xor_en && (pair_idx == 5'(i))) begin
          sl_idle[i] = sl_idle[i] ^ pair_w0;
        end
        if (pair_xor_en && !pair_single && ((pair_idx + 5'd1) == 5'(i))) begin
          sl_idle[i] = sl_idle[i] ^ pair_w1;
        end
        if (pad_end_en && (i == 16)) begin
          sl_idle[i] = sl_idle[i] ^ 64'h8000_0000_0000_0000;
        end
      end
    end
  end

  wire [1599:0] r_in  = canopy_node_go ? cn_init : s_flat;
  wire [4:0]    r_idx = canopy_node_go ? 5'd12   : r;
  wire [1599:0] m;
  qsag_keccak_round u_r0 (.a(r_in), .rc(rcon(r_idx)), .o(m));

  assign busy       = run;
  assign lane_rdata = (lane_idx < 5'd25) ? sl[lane_idx] : 64'd0;
  assign digest_o   = {sl[3], sl[2], sl[1], sl[0]};

  always_ff @(posedge clk) begin
    if (rst) begin
      for (int i = 0; i < 25; i++) begin sl[i] <= 64'd0; sh[i] <= 64'd0; end
      run   <= 1'b0;
      run_l <= '0;
      r     <= '0;
    end else begin
      for (int i = 0; i < 25; i++) begin
        if (run_l[i]) sl[i] <= m[64*i +: 64];
        else if (canopy_node_go) sl[i] <= m[64*i +: 64];
        else sl[i] <= sl_idle[i];
      end
      if (run) begin
        r <= r + 5'd1;
        if (r == 5'd23) begin run <= 1'b0; run_l <= '0; end
      end else if (canopy_node_go) begin
        r     <= 5'd13;
        run   <= 1'b1;
        run_l <= {25{1'b1}};
      end else begin
        if (save) begin
          for (int i = 0; i < 25; i++) sh[i] <= sl[i];
        end
        if (start) begin
          run   <= 1'b1;
          run_l <= {25{1'b1}};
          r     <= rounds12 ? 5'd12 : 5'd0;
        end
      end
    end
  end
endmodule

// Recursive carry-less Karatsuba; an 8-bit schoolbook leaf is small enough for
// exhaustive symbolic LEC. The same module is used at every recursive level.
module qsag_clmul #(parameter int N = 64) (
  input  wire [N-1:0]   a,
  input  wire [N-1:0]   b,
  output wire [2*N-2:0] p
);
  if (N <= 8) begin : g_base
    for (genvar k = 0; k < 2*N-1; k++) begin : g_col
      wire [N-1:0] v;
      for (genvar i = 0; i < N; i++) begin : g_pp
        if (k-i >= 0 && k-i < N) begin : g_in
          assign v[i] = a[i] & b[k-i];
        end else begin : g_zero
          assign v[i] = 1'b0;
        end
      end
      assign p[k] = ^v;
    end
  end else begin : g_rec
    localparam int H = N/2;
    wire [N-2:0] lo, hi, mid;
    qsag_clmul #(.N(H)) u_lo  (.a(a[H-1:0]),          .b(b[H-1:0]),          .p(lo));
    qsag_clmul #(.N(H)) u_hi  (.a(a[N-1:H]),          .b(b[N-1:H]),          .p(hi));
    qsag_clmul #(.N(H)) u_mid (.a(a[H-1:0]^a[N-1:H]), .b(b[H-1:0]^b[N-1:H]), .p(mid));
    assign p = {{N{1'b0}}, lo} ^ {hi, {N{1'b0}}} ^ ({{N{1'b0}}, (mid ^ lo ^ hi)} << H);
  end
endmodule

module qsag_clmul64 (input wire [63:0] a, b, output wire [126:0] p);
  qsag_clmul #(.N(64)) u (.a(a), .b(b), .p(p));
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
  qsag_gf128_mul        u_mul (.a(pa), .b(pb), .r(pr));
  qsag_poly_to_tower128 u_r (.x(pr), .y(r));
endmodule
`default_nettype wire

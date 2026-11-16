// QSAG-NI Goldilocks (p = 2^64 - 2^32 + 1) carry-save arithmetic: hand-written leaf cells.
// The partial-product tree, the carry-save reduction fold and the wrappers that instantiate
// these are generated (qsag_asic_gl64_csa_gen.sv, from gen/gen_rtl.py).
`default_nettype none

// Canonical (x + y) mod p from two carry-save rows with x + y < NJ * p.
// One adder level: NJ compound adders L_j = x + y + j*(2^32 - 1) in parallel. Because
// 2^64 = p + (2^32 - 1), L_j = (x + y - j*p) + j*2^64, so the high part of L_j equals j exactly
// when 0 <= x + y - j*p < 2^64. The largest such j is floor((x + y) / p), whose low word is < p.
module qsag_gl64_final_par #(
  parameter int W  = 66,
  parameter int NJ = 4
) (
  input  wire [W-1:0] x,
  input  wire [W-1:0] y,
  output logic [63:0] r
);
  localparam logic [63:0] EPS = 64'h0000_0000_FFFF_FFFF;
  logic [W:0] l [NJ];
  logic [NJ-1:0] hit;
  for (genvar j = 0; j < NJ; j++) begin : g_cand
    assign l[j]   = {1'b0, x} + {1'b0, y} + (W+1)'(j * EPS);
    assign hit[j] = (l[j][W:64] == (W-63)'(j));
  end
  always_comb begin
    r = l[0][63:0];
    for (int j = 1; j < NJ; j++) if (hit[j]) r = l[j][63:0];
  end
endmodule

// Same function with chained adders (smaller, deeper); any W <= 95. Used after the linear layers,
// whose cycle is not the critical one.
module qsag_gl64_final_seq #(
  parameter int W = 66
) (
  input  wire [W-1:0] x,
  input  wire [W-1:0] y,
  output wire [63:0]  r
);
  localparam logic [63:0] EPS = 64'h0000_0000_FFFF_FFFF;
  localparam logic [63:0] PRIME = 64'hFFFF_FFFF_0000_0001;
  wire [W:0]    t = {1'b0, x} + {1'b0, y};
  wire [W-64:0] q = t[W:64];
  // t = q*2^64 + lo = lo + q*(2^32 - 1) (mod p); q < 2^32 so u < 2^64 + 2^64.
  wire [64:0]   qe = 65'(q);
  wire [64:0]   u = {1'b0, t[63:0]} + (qe << 32) - qe;
  wire [63:0]   v = u[64] ? u[63:0] + EPS : u[63:0];
  assign r = (v >= PRIME) ? v - PRIME : v;
endmodule

// (a + b) mod p or (a - b) mod p for canonical a, b.
module qsag_gl64_addsub (
  input  wire [63:0] a,
  input  wire [63:0] b,
  input  wire        sub,
  output wire [63:0] r
);
  localparam logic [63:0] PRIME = 64'hFFFF_FFFF_0000_0001;
  wire [64:0] s  = {1'b0, a} + {1'b0, b};
  wire [64:0] sp = s - {1'b0, PRIME};
  wire [64:0] d  = {1'b0, a} - {1'b0, b};
  wire [63:0] add_r = sp[64] ? s[63:0] : sp[63:0];
  wire [63:0] sub_r = d[64] ? d[63:0] + PRIME : d[63:0];
  assign r = sub ? sub_r : add_r;
endmodule

// Conventional reference for area/depth comparison and for LEC: plain 64x64 multiply, then the
// shift/mask reduction lo + mid*(2^32 - 1) - hi with carry-propagate adders at every step.
module qsag_gl64_reduce128_ref (
  input  wire [127:0] v,
  output wire [63:0]  r
);
  localparam logic [63:0] PRIME = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] lo  = v[63:0];
  wire [31:0] mid = v[95:64];
  wire [31:0] hi  = v[127:96];
  wire [63:0] loc = (lo >= PRIME) ? lo - PRIME : lo;
  wire [63:0] m   = {mid, 32'b0} - {32'b0, mid};
  wire [63:0] t1, t2;
  qsag_gl64_addsub u_add (.a(loc), .b(m), .sub(1'b0), .r(t1));
  qsag_gl64_addsub u_sub (.a(t1), .b({32'b0, hi}), .sub(1'b1), .r(t2));
  assign r = t2;
endmodule

module qsag_gl64_mul_ref (
  input  wire [63:0] a,
  input  wire [63:0] b,
  output wire [63:0] r
);
  wire [127:0] v = {64'b0, a} * {64'b0, b};
  qsag_gl64_reduce128_ref u_red (.v(v), .r(r));
endmodule
`default_nettype wire

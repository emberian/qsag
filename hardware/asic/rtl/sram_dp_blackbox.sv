// Dual-port synchronous SRAM macro, 64-bit words. Black box for synthesis: its area is a
// foundry macro, reported separately from standard-cell logic. tb/sram_dp_model.sv is the
// simulation model (read-first, one-cycle read latency, both ports read/write).
(* blackbox *)
module sram_dp_64x16384 #(
  parameter int AW = 14
) (
  input  wire          clk,
  input  wire          a_en,
  input  wire          a_we,
  input  wire [AW-1:0] a_addr,
  input  wire [63:0]   a_wdata,
  output wire [63:0]   a_rdata,
  input  wire          b_en,
  input  wire          b_we,
  input  wire [AW-1:0] b_addr,
  input  wire [63:0]   b_wdata,
  output wire [63:0]   b_rdata
);
endmodule

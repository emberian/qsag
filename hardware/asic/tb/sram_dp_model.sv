// Simulation model of the dual-port SRAM macro (same ports as rtl/sram_dp_blackbox.sv).
module sram_dp_64x16384 #(
  parameter int AW = 14
) (
  input  wire          clk,
  input  wire          a_en,
  input  wire          a_we,
  input  wire [AW-1:0] a_addr,
  input  wire [63:0]   a_wdata,
  output logic [63:0]  a_rdata,
  input  wire          b_en,
  input  wire          b_we,
  input  wire [AW-1:0] b_addr,
  input  wire [63:0]   b_wdata,
  output logic [63:0]  b_rdata
);
  logic [63:0] mem [1 << AW];
  always_ff @(posedge clk) begin
    if (a_en) begin
      a_rdata <= mem[a_addr];
      if (a_we) mem[a_addr] <= a_wdata;
    end
    if (b_en) begin
      b_rdata <= mem[b_addr];
      if (b_we) mem[b_addr] <= b_wdata;
    end
  end
endmodule

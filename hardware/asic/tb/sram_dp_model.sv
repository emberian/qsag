// Simulation model of the 4-bank 512 KiB dual-port SRAM subsystem (matching rtl/sram_dp_blackbox.sv).
`default_nettype none

module sram_dp_64x16384_bank (
  input  wire        clk,
  input  wire        a_en,
  input  wire        a_we,
  input  wire [13:0] a_addr,
  input  wire [63:0] a_wdata,
  output logic [63:0] a_rdata,
  input  wire        b_en,
  input  wire        b_we,
  input  wire [13:0] b_addr,
  input  wire [63:0] b_wdata,
  output logic [63:0] b_rdata
);
  logic [63:0] mem [16384];
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

module qsag_sram_512k_4bank (
  input  wire        clk,
  input  wire        rst,
  input  wire        a_en,
  input  wire        a_we,
  input  wire [15:0] a_addr,
  input  wire [63:0] a_wdata,
  output wire [63:0] a_rdata,
  input  wire        b_en,
  input  wire        b_we,
  input  wire [15:0] b_addr,
  input  wire [63:0] b_wdata,
  output wire [63:0] b_rdata
);
  wire [1:0]  a_bsel = a_addr[15:14];
  wire [1:0]  b_bsel = b_addr[15:14];
  logic [1:0] a_bsel_q, b_bsel_q;
  wire [63:0] bk_ard [4];
  wire [63:0] bk_brd [4];

  always_ff @(posedge clk) begin
    if (rst) begin
      a_bsel_q <= 2'd0;
      b_bsel_q <= 2'd0;
    end else begin
      if (a_en) a_bsel_q <= a_bsel;
      if (b_en) b_bsel_q <= b_bsel;
    end
  end

  for (genvar bk = 0; bk < 4; bk++) begin : g_bank
    wire a_hit = a_en && (a_bsel == 2'(bk));
    wire b_hit = b_en && (b_bsel == 2'(bk));
    sram_dp_64x16384_bank u_bank (
      .clk    (clk),
      .a_en   (a_hit),
      .a_we   (a_hit && a_we),
      .a_addr (a_addr[13:0]),
      .a_wdata(a_wdata),
      .a_rdata(bk_ard[bk]),
      .b_en   (b_hit),
      .b_we   (b_hit && b_we),
      .b_addr (b_addr[13:0]),
      .b_wdata(b_wdata),
      .b_rdata(bk_brd[bk])
    );
  end

  assign a_rdata = bk_ard[a_bsel_q];
  assign b_rdata = bk_brd[b_bsel_q];
endmodule
`default_nettype wire

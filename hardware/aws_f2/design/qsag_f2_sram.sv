// Eight interleaved single-clock RAM banks. The shell owns port A only while
// the command scheduler is stopped. Port B serves the NI's second operand.
module qsag_f2_sram (
  input wire clk, rst, a_en, a_we, b_en, b_we, host_en,
  input wire [15:0] a_addr, b_addr,
  input wire [63:0] a_wdata, b_wdata, host_strb,
  input wire [12:0] host_row,
  input wire [511:0] host_data,
  output wire [511:0] host_q,
  output wire [63:0] a_rdata, b_rdata
);
  logic [2:0] a_lane, b_lane;
  wire [63:0] qb [8];
  always_ff @(posedge clk) begin
    if (rst || a_en) a_lane <= rst ? '0 : a_addr[2:0];
    if (rst || b_en) b_lane <= rst ? '0 : b_addr[2:0];
  end
  assign a_rdata = host_q[64*a_lane +: 64];
  assign b_rdata = qb[b_lane];
  for (genvar i=0; i<8; i++) begin : bank
    (* ram_style = "block" *) logic [63:0] mem [8192];
    logic [63:0] qa_reg, qb_reg;
    wire select_a = host_en || (a_en && a_addr[2:0] == 3'(i));
    wire [12:0] row = host_en ? host_row : a_addr[15:3];
    wire [7:0] mask = host_en ? host_strb[8*i +: 8] : {8{a_we}};
    wire [63:0] data = host_en ? host_data[64*i +: 64] : a_wdata;
    always_ff @(posedge clk) begin
      if (select_a) begin
        for (int j=0; j<8; j++) if (mask[j]) mem[row][8*j +: 8] <= data[8*j +: 8];
        qa_reg <= rst ? 64'd0 : mem[row];
      end
      if (rst) qb_reg <= 0;
      else if (b_en && b_addr[2:0] == 3'(i)) begin
        if (b_we) mem[b_addr[15:3]] <= b_wdata;
        qb_reg <= mem[b_addr[15:3]];
      end
    end
    assign host_q[64*i +: 64] = qa_reg;
    assign qb[i] = qb_reg;
  end
endmodule

module qsag_fpga_tag_gate64 (
  input  logic        clk,
  input  logic        rst,
  input  logic [0:0] en,
  input  logic [63:0] a,
  input  logic [63:0] b,
  output logic [63:0] tag
);
  logic [63:0] w_0; // rot_state
  logic [63:0] w_1; // not_b
  logic [63:0] w_2; // chi_and
  logic [63:0] w_3; // chi_xor
  logic [63:0] w_4; // sum_1
  logic [63:0] w_5; // sum_2
  logic [63:0] w_6; // next_state
  logic [63:0] w_7; // tag_out
  logic [63:0] state;
  always_comb begin
    w_0 = ((state << (64'd1 & 64'd63)) | (state >> (64'd63 & 64'd63)));
    w_1 = (~b);
    w_2 = (w_1 & state);
    w_3 = (a ^ w_2);
    w_4 = (w_0 + w_3);
    w_5 = (w_4 + 64'd11400714819323198485);
    w_6 = ((64'(en) != 64'd0) ? w_5 : state);
    w_7 = (state ^ a);
    tag = w_7;
  end
  // Synchronous-reset control registers
  always_ff @(posedge clk) begin
    if (rst) begin
      state <= 64'd0;
    end else begin
      state <= w_6;
    end
  end
endmodule

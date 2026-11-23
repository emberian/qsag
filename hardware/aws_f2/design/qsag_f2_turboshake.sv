// One already framed 136-byte rate block, LE byte/lane order (RFC 9861).
// Callers supply domain byte 0x1f and the final 0x80. Capacity starts zero.
module qsag_f2_turboshake (
  input wire clk, clear, start,
  input wire [1087:0] block_in,
  output wire done,
  output wire [1087:0] digest
);
  `include "qsag_keccak_rc.svh"
  logic [1599:0] state;
  logic [4:0] round_idx;
  wire [1599:0] next_state;
  qsag_keccak_round u_round (.a(state), .rc(rcon(round_idx)), .o(next_state));
  assign digest = next_state[1087:0];
  assign done = round_idx == 23;
  always_ff @(posedge clk) begin
    if (clear) begin state <= 0; round_idx <= 0; end
    else if (start) begin state <= {512'd0,block_in}; round_idx <= 12; end
    else if (done) begin state <= 0; round_idx <= 0; end
    else if (round_idx != 0) begin state <= next_state; round_idx <= round_idx + 1'b1; end
  end
endmodule

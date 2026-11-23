// FM25W256 SPI mode 0, 15-bit wrapping address and write-enable latch.
// The byte array has no PCI address. Local chip reset only resets the link.
module qsag_f2_fram_model (
  input wire clk, rst, erase,
  input wire [14:0] erase_addr,
  input wire [255:0] seal_key,
  input wire cs_n, sck, mosi,
  output logic miso
);
  (* ram_style = "block" *) logic [8:0] mem [32768];
  logic [6:0] shift;
  logic [7:0] q, op;
  logic [14:0] addr;
  logic [1:0] phase;
  logic [2:0] bitno;
  logic prev, wel, wrote;
  wire rise = !prev && sck;
  wire [7:0] incoming = {shift[6:0], mosi};
  // A 128-byte keyed XOF pad for each address block. Begin during the
  // address phase, then prefetch across each 128-byte sequential boundary.
  wire first_pad = !cs_n && rise && phase == 2 && bitno == 0;
  wire next_pad = !cs_n && phase == 3 && (&addr[6:0]) && rise && bitno == 0;
  wire [7:0] block_num = first_pad ? {addr[14:8],mosi} : addr[14:7] + 1'b1;
  wire [1087:0] pad_input = {8'h80,744'd0,8'h1f,block_num,seal_key,64'h314441502e324651};
  wire [1087:0] pad_result;
  wire pad_done;
  logic pad_bank;
  logic [1023:0] pad[2];
  wire [7:0] mask_byte = pad[addr[7]][8*addr[6:0] +: 8];
  wire unused_pad = ^pad_result[1087:1024];
  qsag_f2_turboshake u_pad (.clk, .clear(rst || cs_n), .start(first_pad || next_pad),
    .block_in(pad_input), .done(pad_done), .digest(pad_result));
  always_ff @(posedge clk) begin
    if (rst || cs_n) begin pad_bank <= 0; pad[0] <= 0; pad[1] <= 0; end
    else begin
      if (first_pad || next_pad) pad_bank <= block_num[0];
      if (pad_done) pad[pad_bank] <= pad_result[1023:0];
    end
  end
  logic [8:0] stored;
  logic [7:0] mask_q;
  assign q = stored[8] ? stored[7:0] ^ mask_q : 8'hff;
  always_ff @(posedge clk) begin
    stored <= rst ? 9'd0 : mem[addr];
    mask_q <= rst ? 8'd0 : mask_byte;
    if (erase) mem[erase_addr] <= 9'h0ff;
    else if (!rst && !cs_n && rise && phase == 3 && op == 2 && wel && &bitno)
      mem[addr] <= {1'b1,incoming ^ mask_byte};
    prev <= sck;
    if (rst || cs_n) begin
      prev <= 0; phase <= 0; shift <= 0; addr <= 0; op <= 0; bitno <= 0;
      wrote <= 0; miso <= 0;
      if (rst || wrote) wel <= 0;
    end else if (rise) begin
      bitno <= bitno + 1'b1;
      shift <= incoming[6:0];
      if (&bitno) begin
        case (phase)
          0: begin op <= incoming; if (incoming == 6) wel <= 1; phase <= 1; end
          1: begin addr[14:8] <= incoming[6:0]; phase <= 2; end
          2: begin addr[7:0] <= incoming; phase <= 3; end
          3: begin addr <= addr + 1'b1; if (op == 2 && wel) wrote <= 1; end
        endcase
      end
    end else if (prev && !sck && phase == 3 && op == 3) miso <= q[~bitno];
  end
endmodule

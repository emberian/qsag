// FM25W256 SPI mode 0, 15-bit wrapping address and write-enable latch.
// The byte array has no PCI address. Local chip reset only resets the link.
module qsag_f2_fram_model (
  input wire clk, rst, erase,
  input wire [14:0] erase_addr,
  input wire cs_n, sck, mosi,
  output logic miso
);
  (* ram_style = "block" *) logic [7:0] mem [32768];
  logic [6:0] shift;
  logic [7:0] q, op;
  logic [14:0] addr;
  logic [1:0] phase;
  logic [2:0] bitno;
  logic prev, wel, wrote;
  wire rise = !prev && sck;
  wire [7:0] incoming = {shift[6:0], mosi};
  always_ff @(posedge clk) begin
    q <= rst ? 8'd0 : mem[addr];
    if (erase) mem[erase_addr] <= 8'hff;
    else if (!rst && !cs_n && rise && phase == 3 && op == 2 && wel && &bitno)
      mem[addr] <= incoming;
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

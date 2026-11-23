// bytepad(encode_string("") || encode_string(custom), 136).
// Values are written in byte-stream order below, then exposed as LE lanes.
`default_nettype none
module qsag_v2_domain(input wire [3:0] domain, input wire [4:0] lane,
                      output wire [63:0] word_o);
  logic [255:0] header;
  always_comb begin
    case (domain)
      4'd0: header = {8'h01,8'h88,8'h01,8'h00,8'h01,8'hb0,"QSAG.ZKHEM2.TRANSCRIPT",32'd0};
      4'd1: header = {8'h01,8'h88,8'h01,8'h00,8'h01,8'hb8,"QSAG.ZKHEM2.CANOPY.LEAF",24'd0};
      4'd2: header = {8'h01,8'h88,8'h01,8'h00,8'h01,8'hb8,"QSAG.ZKHEM2.CANOPY.NODE",24'd0};
      4'd3: header = {8'h01,8'h88,8'h01,8'h00,8'h01,8'ha8,"QSAG.ZKHEM2.WHIR.FOLD",40'd0};
      4'd4: header = {8'h01,8'h88,8'h01,8'h00,8'h01,8'h78,"QSAG.ZKHEM2.OOD",88'd0};
      4'd5: header = {8'h01,8'h88,8'h01,8'h00,8'h01,8'h98,"QSAG.HEM.QUINTIC.V2",56'd0};
      4'd6: header = {8'h01,8'h88,8'h01,8'h00,8'h01,8'h98,"QSAG.ZKHEM2.TREE/v1",56'd0};
      4'd7: header = {8'h01,8'h88,8'h01,8'h00,8'h01,8'h88,"QSAG.ZKHEM2.FS/v1",72'd0};
      4'd8: header = {8'h01,8'h88,8'h01,8'h00,8'h01,8'hb0,"QSAG.HEM.QUINTIC.FS/v2",32'd0};
      4'd9: header = {8'h01,8'h88,8'h01,8'h00,8'h01,8'hc0,"QSAG.HEM.QUINTIC.TREE/v2",16'd0};
      default: header = '0;
    endcase
  end
  wire [255:0] little_endian;
  for (genvar b=0; b<32; b++) begin : g_byte
    assign little_endian[8*b +: 8] = header[248-8*b +: 8];
  end
  assign word_o = lane < 4 ? little_endian[64*lane[1:0] +: 64] : 64'd0;
endmodule
`default_nettype wire

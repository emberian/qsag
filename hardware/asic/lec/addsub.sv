// Canonical-input arithmetic contract used by every FP5 accumulation.
module addsub_miter(input wire [63:0] a,b, input wire sub, output wire bad);
  localparam logic [64:0] P = 65'h0ffffffff00000001;
  wire [63:0] result;
  qsag_gl64_addsub dut(.a(a),.b(b),.sub(sub),.r(result));
  wire [64:0] sum = {1'b0,a} + {1'b0,b};
  wire [64:0] difference = {1'b0,a} + (a < b ? P : 65'b0) - {1'b0,b};
  wire [64:0] expected = sub ? difference : (sum < P ? sum : sum - P);
  assign bad = {1'b0,a} < P && {1'b0,b} < P && {1'b0,result} != expected;
endmodule

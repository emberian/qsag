// Dedicated Goldilocks multiply for comparison with the idle shared datapath.
module shared_gold(input wire [767:0] s, input wire glmul, output wire [767:0] y);
  wire [63:0] product;
  qsag_gl64_mul_csa mul (.a(s[63:0]), .b(s[127:64]), .r(product));
  assign y = {s[767:64], glmul ? product : s[63:0]};
endmodule

// Dedicated (unscheduled) arithmetic using the certified ASIC leaves. All
// twelve register words are observed, including lanes outside writeback.
module shared_gold(input wire [767:0] s, input wire [2:0] op, output logic [767:0] y);
  wire [575:0] ka,kb,product;
  wire [255:0] ext;
  qsag_ext4_kara_inputs a(.a(s[255:0]),.q(ka));
  qsag_ext4_kara_inputs b(.a(s[511:256]),.q(kb));
  for (genvar l=0;l<9;l++) begin : g_ext
    qsag_gl64_mul_csa m(.a(ka[64*l+:64]),.b(kb[64*l+:64]),.r(product[64*l+:64]));
  end
  qsag_ext4_kara_combine combine(.p(product),.z(s[767:512]),.r(ext));
  wire [255:0] scalar,addsub;
  for (genvar l=0;l<4;l++) begin : g_limb
    qsag_gl64_mul_csa m(.a(s[64*l+:64]),.b(s[319:256]),.r(scalar[64*l+:64]));
    qsag_gl64_addsub ad(.a(s[64*l+:64]),.b(s[512+64*l+:64]),.sub(op==2),.r(addsub[64*l+:64]));
  end
  wire [63:0] base;
  qsag_gl64_mul_csa g(.a(s[63:0]),.b(s[127:64]),.r(base));
  always_comb begin
    y=s;
    case(op)
      0:y[255:0]=ext;
      1,2:y[255:0]=addsub;
      3:y[255:0]=scalar;
      4:y[63:0]=base;
      default:;
    endcase
  end
endmodule

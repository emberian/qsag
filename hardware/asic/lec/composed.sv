`default_nettype none
module csa_identity(input wire [63:0] a,b,c, output wire bad);
  wire [63:0] s=a^b^c, k=(a&b)|(a&c)|(b&c);
  assign bad = ({2'b0,s}+{1'b0,k,1'b0}) != ({2'b0,a}+{2'b0,b}+{2'b0,c});
endmodule
module clmul_identity #(parameter int N=8)(input wire [N-1:0] a,b,output wire bad);
  wire [2*N-2:0] p;
  logic [2*N-2:0] q;
  qsag_clmul #(.N(N)) u(.a(a),.b(b),.p(p));
  always_comb begin
    q='0;
    for(int i=0;i<N;i++) if(b[i]) q ^= (2*N-1)'(a)<<i;
  end
  assign bad = p != q;
endmodule
module gf_reduce_identity(input wire [254:0] c,output wire bad);
  wire [126:0] h=c[254:128];
  wire [133:0] f={7'b0,h}^{6'b0,h,1'b0}^{5'b0,h,2'b0}^{h,7'b0};
  wire [5:0] g=f[133:128];
  wire [127:0] p=c[127:0]^f[127:0]^{122'b0,g}^{121'b0,g,1'b0}^{120'b0,g,2'b0}^{115'b0,g,7'b0};
  logic [254:0] q;
  always_comb begin
    q=c;
    for(int i=254;i>=128;i--) if(q[i]) q ^= (255'h100000000000000000000000000000087 << (i-128));
  end
  assign bad=p!=q[127:0];
endmodule
`default_nettype wire

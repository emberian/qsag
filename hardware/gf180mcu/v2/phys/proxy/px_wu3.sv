// Area proxy (from the architecture lane's skeleton, not simulated): Dregg-180 v2 word unit as the stage-1 model defines it (v2/model/units.py):
// hold/accumulator register H, two-operand functions on (H, row or 16-bit immediate), the unary wiring
// functions, external sources (payload word, framer field, constant, FRAM word), compare accumulator,
// carry, H == 0. FULL = 1: all 13 unary functions; FULL = 0: ID, NIB, BE32, HSWAP, LO32, SHR1, SHR4, SHL1, SHL4.
`default_nettype none
module px_wu3 #(parameter bit FULL = 1'b1) (
    input  wire         clk,
    input  wire         rst_n,
    input  wire  [63:0] row,        // register-file read port
    input  wire  [15:0] imm,
    input  wire         use_imm,
    input  wire  [2:0]  alu,        // 0 LD 1 XOR 2 AND 3 OR 4 ADD 5 SUB 6 CMP
    input  wire  [3:0]  un,
    input  wire  [2:0]  src,        // 0 alu 1 unary 2 payload 3 framer field 4 constant 5 FRAM word 6 field unit
    input  wire  [63:0] din, fld, cst, fram, gl,
    input  wire         ld_h,
    input  wire         clr_h,
    input  wire         clr_z,
    output logic [63:0] h,          // also the register-file write data
    output logic        z,
    output logic        cy,
    output wire         hz
);
    wire [63:0] x = use_imm ? {48'd0, imm} : row;
    wire [32:0] add = {1'b0, h[31:0]} + {1'b0, x[31:0]};
    wire [32:0] sub = {1'b0, h[31:0]} - {1'b0, x[31:0]};
    logic [63:0] a, u, nxt;
    always_comb begin
        unique case (alu)
            3'd0: a = x;
            3'd1: a = h ^ x;
            3'd2: a = h & x;
            3'd3: a = h | x;
            3'd4: a = {32'd0, add[31:0]};
            3'd5: a = {32'd0, sub[31:0]};
            default: a = h;
        endcase
    end
    function automatic [63:0] nib(input [63:0] v);
        for (int i = 0; i < 8; i++) nib[8*i +: 8] = {v[8*i +: 4], v[8*i+4 +: 4]};
    endfunction
    function automatic [31:0] bs32(input [31:0] v);
        bs32 = {v[7:0], v[15:8], v[23:16], v[31:24]};
    endfunction
    always_comb begin
        unique case (un)
            4'd0: u = h;
            4'd1: u = nib(h);
            4'd2: u = {bs32(h[63:32]), bs32(h[31:0])};
            4'd3: u = {h[31:0], h[63:32]};
            4'd4: u = {32'd0, h[31:0]};
            4'd6: u = h >> 1;
            4'd7: u = h >> 4;
            4'd10: u = h << 1;
            4'd11: u = h << 4;
            4'd5: u = FULL ? {h[63:32], 32'd0} : h;
            4'd8: u = FULL ? h >> 8 : h;
            4'd9: u = FULL ? h >> 16 : h;
            4'd12: u = FULL ? h << 8 : h;
            default: u = h;
        endcase
    end
    always_comb begin
        unique case (src)
            3'd0: nxt = a;
            3'd1: nxt = u;
            3'd2: nxt = din;
            3'd3: nxt = fld;
            3'd4: nxt = cst;
            3'd5: nxt = fram;
            default: nxt = gl;
        endcase
    end
    assign hz = (h == 64'd0);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin h <= '0; z <= 1'b0; cy <= 1'b0; end
        else begin
            if (clr_h) h <= '0; else if (ld_h) h <= nxt;
            if (clr_z) z <= 1'b0; else if (ld_h && src == 3'd0 && alu == 3'd6) z <= z | (h != x);
            if (ld_h && src == 3'd0 && alu == 3'd4) cy <= add[32];
            if (ld_h && src == 3'd0 && alu == 3'd5) cy <= sub[32];
        end
    end
endmodule
`default_nettype wire

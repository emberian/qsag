module qsag_ass2_alu (
    input logic [3:0] op, fn, flags, byte_idx,
    input logic [19:0] imm,
    input logic [63:0] ra, rb, rc, pc,
    output logic [63:0] result
);
    import qsag_ass2_pkg::*;
    wire [63:0] u16 = {48'd0,imm[15:0]};
    wire [63:0] s16 = {{48{imm[15]}},imm[15:0]};
    wire [63:0] s20 = {{44{imm[19]}},imm};
    wire [63:0] adder_a = (op == IMM20) ? pc : ra;
    // Share the single 65-bit adder/subtractor across ADD, SUB, ADDI, ADDIU, AUIPC, and CMP!
    wire sub = (op == CMP) || (op == ALU && fn == 4'd1);
    wire [63:0] adder_b = (op == IMM20) ? (s20 << 2)
                        : (op == ALUI)  ? ((fn == 4'd0) ? s16 : u16)
                        : rb;
    wire carry;
    wire [63:0] sum;
    qsag_ass2_add64 u_add (.a(adder_a), .b(adder_b ^ {64{sub}}),
                           .cin(sub), .sum(sum), .cout(carry));

    wire leftward   = (op == ALU) ? (fn inside {4'd2,4'd5}) : (op == ALUI && (fn inside {4'd5,4'd8}));
    wire rotate     = (op == ALU) ? (fn inside {4'd5,4'd6}) : (op == ALUI && fn == 4'd8);
    wire arithmetic = (op == ALU) ? (fn == 4'd4) : (op == ALUI && fn == 4'd7);
    wire saturate   = (op == ALU) && !rotate && (|rb[63:6]);
    wire [5:0] distance = (op == BYTE_OP) ? {byte_idx[2:0],3'b0}
                        : (op == ALUI)    ? imm[5:0] : rb[5:0];
    logic [63:0] src, shifted, barrel_result, truth, swapped, extracted;
    for (genvar i = 0; i < 64; i++) begin : g_bits
        assign src[i]           = leftward ? ra[63-i] : ra[i];
        assign barrel_result[i] = leftward ? shifted[63-i] : shifted[i];
        assign truth[i]         = fn[{ra[i],rb[i]}];
    end
    wire [63:0] fill = rotate ? src : {64{arithmetic && ra[63]}};
    assign shifted = saturate ? fill : 64'({fill,src} >> distance);
    wire [2:0] last_byte = flags[2:0] - 3'd1;
    wire ext_sign = (fn == 4'd2) && shifted[{last_byte,3'b111}];
    for (genvar i = 0; i < 8; i++) begin : g_bytes
        assign swapped[(i<<3)+:8] = ra[((7-i)<<3)+:8];
        if (i == 0) begin : g_low
            assign extracted[7:0] = shifted[7:0];
        end else begin : g_ext
            assign extracted[(i<<3)+:8] = (i <= last_byte) ? shifted[(i<<3)+:8] : {8{ext_sign}};
        end
    end

    wire eq  = (ra == rb);
    wire ugt = carry && !eq;
    wire gt  = (flags[2] && (ra[63] != rb[63])) ? rb[63] : ugt;

    always_comb begin
        result = '0;
        case (op)
            LUT4: result = truth;
            ALU:  result = (fn < 4'd2) ? sum : barrel_result;
            ALUI: case (fn)
                0,1: result = sum;
                2:   result = ra ^ u16;
                3:   result = ra & u16;
                4:   result = ra | u16;
                9:   result = {ra[47:0],imm[15:0]};
                default: result = barrel_result;
            endcase
            IMM20: result = (fn == 4'd0) ? 64'(imm) : (fn == 4'd1) ? s20 : sum;
            CMP:   result = 64'(flags[3] ^ ((flags[0] && eq) || (flags[1] && gt)));
            BYTE_OP: case (fn)
                0:   result = (rc == 64'd0) ? ra : rb;
                1,2: result = extracted;
                default: result = swapped;
            endcase
            default: ;
        endcase
    end
    wire unused_byte_idx = byte_idx[3];
endmodule

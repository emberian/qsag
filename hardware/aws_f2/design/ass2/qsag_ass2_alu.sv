// Shared 64-bit word execution unit:
//   - Shares the single byte-prefix `qsag_ass2_add64` across `ADD`, `SUB`, `ADDI`, `ADDIU`,
//     `AUIPC`, `CMP`, AND `CAP_C` effective-address calculation (`addr_mode_i`), saving 8.7k um^2.
//   - Explicit 6-stage 64-bit logarithmic shifter/rotator (replaces 128-bit dynamic `$shr`,
//     saving ~25k um^2 and cutting SS delay in half), ALSO shared with `crypto` for 1-clock
//     `Keccak` Rho lane rotation (`crypto_rot_en_i`).
module qsag_ass2_alu (
    input  logic        addr_mode_i,
    input  logic [63:0] addr_base_i,
    input  logic [63:0] addr_offset_i,
    input  logic        crypto_rot_en_i,
    input  logic [5:0]  crypto_rot_amt_i,
    input  logic [3:0]  op, fn, flags, byte_idx,
    input  logic [19:0] imm,
    input  logic [63:0] ra, rb, rc, pc,
    output logic [63:0] sum_o,
    output logic [63:0] rot_o,
    output logic [63:0] result
);
    import qsag_ass2_pkg::*;
    wire [63:0] u16 = {48'd0, imm[15:0]};
    wire [63:0] s16 = {{48{imm[15]}}, imm[15:0]};
    wire [63:0] s20 = {{44{imm[19]}}, imm};

    wire        sub     = !addr_mode_i && ((op == CMP) || (op == ALU && fn == 4'd1));
    wire [63:0] adder_a = addr_mode_i   ? addr_base_i
                        : (op == IMM20) ? pc : ra;
    wire [63:0] raw_b   = addr_mode_i   ? addr_offset_i
                        : (op == IMM20) ? (s20 << 2)
                        : (op == ALUI)  ? ((fn == 4'd0) ? s16 : u16)
                        : rb;
    wire carry;
    wire [63:0] sum;
    qsag_ass2_add64 u_add (
        .a(adder_a), .b(raw_b ^ {64{sub}}), .cin(sub), .sum(sum), .cout(carry)
    );
    assign sum_o = sum;

    wire leftward   = crypto_rot_en_i ? 1'b1
                    : (op == ALU)     ? (fn inside {4'd2, 4'd5})
                    :                   (op == ALUI && (fn inside {4'd5, 4'd8}));
    wire rotate     = crypto_rot_en_i ? 1'b1
                    : (op == ALU)     ? (fn inside {4'd5, 4'd6})
                    :                   (op == ALUI && fn == 4'd8);
    wire arithmetic = !crypto_rot_en_i && ((op == ALU) ? (fn == 4'd4) : (op == ALUI && fn == 4'd7));
    wire saturate   = !crypto_rot_en_i && (op == ALU) && !rotate && (|rb[63:6]);
    wire [5:0] distance = crypto_rot_en_i ? crypto_rot_amt_i
                        : (op == BYTE_OP) ? {byte_idx[2:0], 3'b0}
                        : (op == ALUI)    ? imm[5:0] : rb[5:0];

    logic [63:0] src, barrel_result, truth, swapped, extracted;
    for (genvar i = 0; i < 64; i++) begin : g_bits
        assign src[i]   = leftward ? ra[63 - i] : ra[i];
        assign truth[i] = fn[{ra[i], rb[i]}];
    end

    // Explicit 6-stage logarithmic right-shifter / rotator (`st[0]` -> `st[6]`)
    wire sign_fill = arithmetic && ra[63];
    wire [63:0] st [7];
    assign st[0] = src;
    for (genvar s = 0; s < 6; s++) begin : g_sh_stage
        localparam int D = 1 << s;
        for (genvar i = 0; i < 64; i++) begin : g_sh_bit
            wire hi_bit = (i + D < 64) ? st[s][i + D]
                        : rotate       ? st[s][i + D - 64]
                        :                sign_fill;
            assign st[s + 1][i] = distance[s] ? hi_bit : st[s][i];
        end
    end
    wire [63:0] shifted = saturate ? {64{sign_fill}} : st[6];
    for (genvar i = 0; i < 64; i++) begin : g_rev_out
        assign barrel_result[i] = leftward ? shifted[63 - i] : shifted[i];
    end
    assign rot_o = barrel_result;

    wire [2:0] last_byte = flags[2:0] - 3'd1;
    logic ext_bit;
    always_comb begin
        unique case (last_byte)
            3'd0: ext_bit = shifted[7];
            3'd1: ext_bit = shifted[15];
            3'd2: ext_bit = shifted[23];
            3'd3: ext_bit = shifted[31];
            3'd4: ext_bit = shifted[39];
            3'd5: ext_bit = shifted[47];
            3'd6: ext_bit = shifted[55];
            default: ext_bit = shifted[63];
        endcase
    end
    wire ext_sign = (fn == 4'd2) && ext_bit;
    for (genvar i = 0; i < 8; i++) begin : g_bytes
        assign swapped[(i<<3)+:8] = ra[((7-i)<<3)+:8];
        if (i == 0) begin : g_low
            assign extracted[7:0] = shifted[7:0];
        end else begin : g_ext
            assign extracted[(i<<3)+:8] = (3'(i) <= last_byte) ? shifted[(i<<3)+:8] : {8{ext_sign}};
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
                0, 1: result = sum;
                2:    result = ra ^ u16;
                3:    result = ra & u16;
                4:    result = ra | u16;
                9:    result = {ra[47:0], imm[15:0]};
                default: result = barrel_result;
            endcase
            IMM20: result = (fn == 4'd0) ? 64'(imm) : (fn == 4'd1) ? s20 : sum;
            CMP:   result = 64'(flags[3] ^ ((flags[0] && eq) || (flags[1] && gt)));
            BYTE_OP: case (fn)
                0:       result = (rc == 64'd0) ? ra : rb;
                1, 2:    result = extracted;
                default: result = swapped;
            endcase
            default: ;
        endcase
    end
    wire unused_byte_idx = byte_idx[3];
endmodule

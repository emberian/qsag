// Area-slimmed shared 64-bit ALU & chip-wide adder unit:
//   - Shares ONE `qsag_ass2_add64` across `ADD`, `SUB`, `ADDI`, `ADDIU`, `AUIPC`, `CMP`,
//     `CAP_C` effective-address calculation (`addr_mode_i`), AND `crypto`/`mul` (`ext_add_en_i`).
//   - Folds `BEXTU`/`BEXTS` directly onto `barrel_result`, folds `MOVZ20`/`MOVS20`, and folds `MOVK16`/`SEL`
//     to eliminate redundant 64-bit output mux ports!
module qsag_ass2_alu (
    input  logic        addr_mode_i,
    input  logic [63:0] addr_base_i,
    input  logic [63:0] addr_offset_i,
    input  logic        ext_add_en_i,
    input  logic [63:0] ext_add_a_i,
    input  logic [63:0] ext_add_b_i,
    input  logic        ext_add_cin_i,
    input  logic        crypto_rot_en_i,
    input  logic [5:0]  crypto_rot_amt_i,
    input  logic [3:0]  op, fn, flags, byte_idx,
    input  logic [19:0] imm,
    input  logic [63:0] ra, rb, rc, pc,
    output logic [63:0] sum_o,
    output logic        cout_o,
    output logic [63:0] rot_o,
    output logic [63:0] result
);
    import qsag_ass2_pkg::*;
    wire [63:0] u16 = {48'd0, imm[15:0]};
    wire [63:0] s16 = {{48{imm[15]}}, imm[15:0]};

    wire        sub      = !addr_mode_i && ((op == CMP) || (op == ALU && fn == 4'd1));
    wire [63:0] cpu_a    = addr_mode_i   ? addr_base_i
                         : (op == IMM20) ? pc : ra;
    wire [63:0] raw_b    = addr_mode_i   ? addr_offset_i
                         : (op == IMM20) ? {{42{imm[19]}}, imm, 2'b00}
                         : (op == ALUI)  ? ((fn == 4'd0) ? s16 : u16)
                         : rb;
    wire [63:0] add_in_a = ext_add_en_i ? ext_add_a_i   : cpu_a;
    wire [63:0] add_in_b = ext_add_en_i ? ext_add_b_i   : (raw_b ^ {64{sub}});
    wire        add_cin  = ext_add_en_i ? ext_add_cin_i : sub;

    wire carry;
    wire [63:0] sum;
    qsag_ass2_add64 u_add (
        .a(add_in_a), .b(add_in_b), .cin(add_cin), .sum(sum), .cout(carry)
    );
    assign sum_o  = sum;
    assign cout_o = carry;

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

    wire [63:0] lut_b  = (op == ALUI) ? u16 : rb;
    wire [3:0]  lut_fn = (op == LUT4) ? fn
                       : (fn == 4'd2) ? 4'h6
                       : (fn == 4'd3) ? 4'h8 : 4'hE;

    logic [63:0] src, barrel_raw, shift_ext, truth, swapped;
    for (genvar i = 0; i < 64; i++) begin : g_bits
        assign src[i]   = leftward ? ra[63 - i] : ra[i];
        assign truth[i] = lut_fn[{ra[i], lut_b[i]}];
    end

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
        assign barrel_raw[i] = leftward ? shifted[63 - i] : shifted[i];
    end
    assign rot_o = barrel_raw;

    wire is_bext = !crypto_rot_en_i && (op == BYTE_OP) && (fn == 4'd1 || fn == 4'd2);
    wire [2:0] last_byte = flags[2:0] - 3'd1;
    logic ext_bit;
    always_comb begin
        unique case (last_byte)
            3'd0: ext_bit = barrel_raw[7];
            3'd1: ext_bit = barrel_raw[15];
            3'd2: ext_bit = barrel_raw[23];
            3'd3: ext_bit = barrel_raw[31];
            3'd4: ext_bit = barrel_raw[39];
            3'd5: ext_bit = barrel_raw[47];
            3'd6: ext_bit = barrel_raw[55];
            default: ext_bit = barrel_raw[63];
        endcase
    end
    wire ext_sign = (fn == 4'd2) && ext_bit;
    for (genvar i = 0; i < 8; i++) begin : g_bytes
        assign swapped[(i<<3)+:8] = ra[((7-i)<<3)+:8];
        if (i == 0) begin : g_low
            assign shift_ext[7:0] = barrel_raw[7:0];
        end else begin : g_ext
            assign shift_ext[(i<<3)+:8] = (!is_bext || 3'(i) <= last_byte)
                                        ? barrel_raw[(i<<3)+:8]
                                        : {8{ext_sign}};
        end
    end

    wire eq   = (ra == rb);
    wire ugt  = (op == CMP) && !addr_mode_i && !ext_add_en_i && carry && !eq;
    wire gt   = (flags[2] && (ra[63] != rb[63])) ? rb[63] : ugt;
    wire cmp1 = flags[3] ^ ((flags[0] && eq) || (flags[1] && gt));

    // Merged `SLK16` (`{ra[47:0], imm[15:0]}`) and `SEL` (`rc == 0 ? ra : rb`)
    wire [63:0] sel_movk = (op == ALUI) ? {ra[47:0], imm[15:0]}
                         : (rc == 64'd0) ? ra : rb;
    // Merged `MOVZ20` / `MOVS20` / `CMP`
    wire [63:0] imm_cmp  = (op == CMP) ? {63'd0, cmp1}
                         : {{44{fn[0] & imm[19]}}, imm};

    wire use_sum   = (op == ALU && fn < 4'd2) || (op == ALUI && fn < 4'd2) || (op == IMM20 && fn == 4'd2);
    wire use_truth = (op == LUT4) || (op == ALUI && fn >= 4'd2 && fn <= 4'd4);
    wire use_shift = (op == ALU && fn >= 4'd2) || (op == ALUI && fn >= 4'd5 && fn <= 4'd8)
                   || (op == BYTE_OP && (fn == 4'd1 || fn == 4'd2));
    wire use_swap  = (op == BYTE_OP && fn == 4'd3);
    wire use_selmk = (op == ALUI && fn == 4'd9) || (op == BYTE_OP && fn == 4'd0);

    assign result = use_sum   ? sum
                  : use_truth ? truth
                  : use_shift ? shift_ext
                  : use_swap  ? swapped
                  : use_selmk ? sel_movk
                  : (op == IMM20 || op == CMP) ? imm_cmp
                  : 64'd0;
    wire unused_byte_idx = byte_idx[3];
endmodule

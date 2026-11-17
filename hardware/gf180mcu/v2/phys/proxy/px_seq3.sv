// Area proxy (from the architecture lane's skeleton, not simulated): Dregg-180 v2 sequencer as the stage-1 model defines it (v2/model/machine.py):
// 11-bit micro-PC, two-entry return stack, two 12-bit down counters, 7-bit index register X with two row
// adders, condition select, session flags (keyed, dirty, header done, failed, flushed), output-length counter,
// and the decoder rule comparators (row classes, key range, epilogue, idle). The ROM is outside.
`default_nettype none
module px_seq3 (
    input  wire         clk,
    input  wire         rst_n,
    input  wire  [27:0] ir,
    input  wire  [10:0] entry,
    input  wire  [63:0] h,
    input  wire         z, cy, hz, more, key_valid, unit_busy,
    output logic [10:0] pc,
    output wire  [6:0]  ra, rb,
    output wire         fault,
    output logic        keyed, dirty, hdr_done,
    output wire         egress_ok
);
    localparam logic [10:0] EPI = 11'd1, IDLE_A = 11'd4, KR_LO = 11'd114, KR_HI = 11'd148;
    wire [4:0] op = ir[27:23];
    wire [6:0] a = ir[22:16], b = ir[15:9];
    wire [3:0] fn = ir[8:5];
    wire ia = ir[4], ib = ir[3], xi = ir[2], sret = ir[0];
    logic [6:0] x;
    logic [11:0] c0, c1;
    logic [10:0] st0, st1;
    logic [1:0] sp;
    logic failed, flushed;
    logic [23:0] olim, osent;
    assign ra = ia ? a + x : a;
    assign rb = ib ? b + x : b;
    wire [10:0] tgt = {b, fn};
    function automatic [2:0] cls(input [6:0] r);   // 0 lane 1 kwork 2 scratch 3 key 4 pin/state 5 out 6 none
        if (r < 7'd25) cls = 3'd0; else if (r < 7'd32) cls = 3'd1; else if (r < 7'd44) cls = 3'd2;
        else if (r < 7'd54) cls = 3'd3; else if (r < 7'd62) cls = 3'd4; else if (r < 7'd64) cls = 3'd5; else cls = 3'd6;
    endfunction
    wire is_alu = (op >= 5'd1 && op <= 5'd7), is_imm = fn[1], w = fn[0];
    wire rd_row = (is_alu && !is_imm) || (op == 5'd12 && !fn[1]) || op == 5'd21;
    wire wr_row = w && (is_alu || op == 5'd8 || op == 5'd9 || op == 5'd10 || op == 5'd11 || op == 5'd20 || op == 5'd22);
    wire [2:0] ca = cls(ra), cb = cls(rb);
    wire bad_rd = rd_row && (ca == 3'd1 || ca == 3'd3 || ca == 3'd5 || ca == 3'd6 ||
                             (ca == 3'd0 && dirty && !(op == 5'd2 && w && ra == rb)) ||
                             (ca == 3'd0 && keyed && ra >= 7'd17));
    wire bad_wr = wr_row && (cb == 3'd1 || cb == 3'd3 || cb == 3'd5 || cb == 3'd6);
    wire in_kr = (pc >= KR_LO) && (pc <= KR_HI);
    wire bad_key = (op == 5'd16 && (!in_kr || cb != 3'd3)) || (op == 5'd15 && (ca != 3'd3 || b >= 7'd17)) ||
                   (op == 5'd17 && a == 7'd1 && !in_kr);
    wire bad_out = (op == 5'd12 && (!hdr_done || failed || dirty || osent >= olim)) ||
                   (op == 5'd13 && (hdr_done || failed || h[23:0] > {8'd0, fn[3:2], a, b})) ||
                   (op == 5'd14 && (hdr_done || failed));
    logic cond;
    always_comb begin
        unique case (a[3:0])
            4'd0: cond = 1'b1;
            4'd1: cond = z;      4'd2: cond = !z;
            4'd3: cond = cy;     4'd4: cond = !cy;
            4'd5: cond = hz;     4'd6: cond = !hz;
            4'd7: cond = more;   4'd8: cond = !more;
            4'd9: cond = key_valid; 4'd10: cond = !key_valid;
            4'd11: cond = (c1 == 12'd0); 4'd12: cond = (c1 != 12'd0);
            default: cond = 1'b0;
        endcase
    end
    wire [11:0] cdec = (a[0] ? c1 : c0) - 12'd1;
    wire take = (op == 5'd25 && cond) || (op == 5'd26 && x != a) || (op == 5'd27 && cdec != 12'd0) || op == 5'd28;
    wire bad_tgt = take && (tgt == 11'd0 || (tgt > EPI && tgt <= IDLE_A));
    wire bad_seq = (op == 5'd29 && pc != 11'd0) || (op == 5'd30 && (pc != IDLE_A || !flushed)) || op == 5'd31 ||
                   (op == 5'd28 && sp == 2'd2) || (sret && !take && sp == 2'd0);
    assign fault = bad_rd | bad_wr | bad_key | bad_out | bad_tgt | bad_seq;
    assign egress_ok = hdr_done && !failed && (osent < olim);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            pc <= '0; x <= '0; c0 <= '0; c1 <= '0; st0 <= '0; st1 <= '0; sp <= '0;
            keyed <= 1'b0; dirty <= 1'b0; hdr_done <= 1'b0; failed <= 1'b0; flushed <= 1'b0; olim <= '0; osent <= '0;
        end else if (!unit_busy && !fault) begin
            pc <= pc + 11'd1;
            if (xi) x <= x + 7'd1;
            unique case (op)
                5'd12: osent <= osent + 24'd1;
                5'd13: begin hdr_done <= 1'b1; olim <= h[23:0]; end
                5'd14: begin failed <= 1'b1; pc <= EPI; end
                5'd15: begin keyed <= 1'b1; dirty <= 1'b1; end
                5'd17: if (a == 7'd5) flushed <= 1'b1;
                5'd18: if (a[1:0] == 2'b11) dirty <= 1'b0;
                5'd19: dirty <= 1'b0;
                5'd23: x <= fn[0] ? h[6:0] : a;
                5'd24: if (a[0]) c1 <= a[1] ? h[11:0] : {1'b0, tgt}; else c0 <= a[1] ? h[11:0] : {1'b0, tgt};
                5'd27: if (a[0]) c1 <= cdec; else c0 <= cdec;
                5'd29: pc <= entry;
                5'd30: begin
                    pc <= '0; x <= '0; c0 <= '0; c1 <= '0; sp <= '0; keyed <= 1'b0; dirty <= 1'b0;
                    hdr_done <= 1'b0; failed <= 1'b0; flushed <= 1'b0; olim <= '0; osent <= '0;
                end
                default: ;
            endcase
            if (take) pc <= tgt;
            if (op == 5'd28) begin
                if (sp == 2'd0) st0 <= pc + 11'd1; else st1 <= pc + 11'd1;
                sp <= sp + 2'd1;
            end else if (sret && !take) begin
                pc <= (sp == 2'd2) ? st1 : st0;
                sp <= sp - 2'd1;
            end
        end
    end
endmodule
`default_nettype wire

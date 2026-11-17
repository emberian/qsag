// Dregg-180 v2 egress: the structural output bound (ARCHITECTURE.md 5.3).
//
// The response is: one header word built here from the framer's opcode and the fields of the one HDR
// (or FAIL) of the command; then at most `n` words, each read from one of the two out rows of the
// register file; then zeros up to `n`. Nothing else reaches out_data: the multiplexer below has
// exactly these inputs.
//
//   hdr      (from the sequencer) issue the header: n = hdr_n words follow, ok flag = hdr_ok
//   fail     issue an error header: code hdr_n, no words follow
//   push     an out row is being written this clock (the sequencer raises out_we[wr_slot] with it);
//            allowed only when can_push
//   flush    the command has ended: pad with zeros up to n; `flushed` rises when everything has left
//
// Two counters enforce the length. `left_push` is how many PUSHes the declared length still allows
// (the decoder refuses a PUSH at zero). `left_tx` counts words leaving and gates out_valid itself, so
// the link never sees more than n words after a header whatever the sequencer does.
//
// An out row written in clock n is transparent in clock n + 1 and offered to the link from clock n + 2.
`default_nettype none

module dregg_egress (
    input  wire         clk,
    input  wire         srst_n,
    input  wire  [7:0]  req_op,       // opcode of the request being answered (framer)
    input  wire         hdr,
    input  wire         fail,
    input  wire  [15:0] hdr_n,        // words (hdr) or error code (fail)
    input  wire         hdr_ok,
    input  wire         push,
    output wire         can_push,
    output wire         wr_slot,
    output wire         push_room,    // the declared length allows another PUSH
    input  wire         flush,
    output wire         flushed,
    output wire         idle,         // nothing pending (no header, no word, no padding owed under flush)
    input  wire  [127:0] out_q,       // the two out rows
    output wire         out_valid,
    output wire  [63:0] out_data,
    input  wire         out_take,
    output wire  [1:0]  out_sel       // 0 header, 1 out row 0, 2 out row 1, 3 zero (padding)
);
    logic        hp;            // header pending
    logic        h_fail, h_ok;
    logic [15:0] h_val;
    logic [1:0]  full, fresh;
    logic        wp, rp;
    logic [15:0] left_push, left_tx;

    wire data_rdy = full[rp] && !fresh[rp] && (left_tx != 16'd0);
    wire pad_rdy  = flush && (full == 2'b00) && (left_tx != 16'd0);
    assign out_valid = hp | data_rdy | pad_rdy;
    assign out_sel   = hp ? 2'd0 : data_rdy ? (rp ? 2'd2 : 2'd1) : 2'd3;

    wire [15:0] err   = h_fail ? h_val : 16'd0;
    wire [23:0] nbyte = h_fail ? 24'd0 : {5'd0, h_val, 3'd0};
    wire [7:0]  flags = (err != 16'd0) ? 8'h80 : {7'd0, h_ok & ~h_fail};
    wire [63:0] header = {err, nbyte, flags, req_op | 8'h80, 8'h51};

    logic [63:0] mux;
    always_comb begin
        unique case (out_sel)
            2'd0:    mux = header;
            2'd1:    mux = out_q[63:0];
            2'd2:    mux = out_q[127:64];
            default: mux = 64'd0;
        endcase
    end
    assign out_data  = mux;

    assign can_push  = !full[wp];
    assign wr_slot   = wp;
    assign push_room = (left_push != 16'd0);
    assign flushed   = !hp && (full == 2'b00) && (left_tx == 16'd0);
    assign idle      = !hp && (full == 2'b00);

    wire take = out_valid && out_take;

    always_ff @(posedge clk or negedge srst_n)
        if (!srst_n) begin
            hp        <= 1'b0;
            h_fail    <= 1'b0;
            h_ok      <= 1'b0;
            h_val     <= '0;
            full      <= '0;
            fresh     <= '0;
            wp        <= 1'b0;
            rp        <= 1'b0;
            left_push <= '0;
            left_tx   <= '0;
        end else begin
            fresh <= 2'b00;
            if (push && can_push && push_room) begin        // a PUSH beyond the declared length is ignored here too
                full[wp]  <= 1'b1;
                fresh[wp] <= 1'b1;
                wp        <= ~wp;
                left_push <= left_push - 16'd1;
            end
            if (take) begin
                if (hp) hp <= 1'b0;
                else begin
                    left_tx <= left_tx - 16'd1;
                    if (data_rdy) begin
                        full[rp] <= 1'b0;
                        rp       <= ~rp;
                    end
                end
            end
            // a new header starts a new response: it wins over anything else in the same clock
            if (hdr | fail) begin
                hp        <= 1'b1;
                h_fail    <= fail;
                h_ok      <= hdr_ok;
                h_val     <= hdr_n;
                left_push <= fail ? 16'd0 : hdr_n;
                left_tx   <= fail ? 16'd0 : hdr_n;
                wp        <= 1'b0;
                rp        <= 1'b0;
                full      <= 2'b00;
                fresh     <= 2'b00;
            end
        end

`ifdef FORMAL
    // Structural output bound, for every behaviour of the sequencer and the link (all inputs free).
    //   words leaving after a header never exceed the length that header declared;
    //   a data word is one of the two out rows, a padding word is zero, a header starts with the magic byte;
    //   an out row is offered only while it holds a pushed word, and never in the clock it is written.
    logic [16:0] f_decl, f_sent;
    logic        f_pv;
    initial f_pv = 1'b0;
    always_ff @(posedge clk) begin
        f_pv <= 1'b1;
        if (!srst_n) begin
            f_decl <= '0;
            f_sent <= '0;
        end else if (hdr | fail) begin
            f_decl <= fail ? 17'd0 : {1'b0, hdr_n};
            f_sent <= '0;
        end else if (take && !hp) f_sent <= f_sent + 17'd1;
        if (f_pv && srst_n && $past(srst_n)) begin
            assert (f_sent <= f_decl);
            assert (f_sent + {1'b0, left_tx} == f_decl);
            assert ({1'b0, left_push} <= f_decl);
            if (out_valid && out_sel == 2'd0) assert (out_data[7:0] == 8'h51 && hp);
            if (out_valid && out_sel == 2'd1) assert (out_data == out_q[63:0] && full[0] && !fresh[0] && left_tx != 16'd0);
            if (out_valid && out_sel == 2'd2) assert (out_data == out_q[127:64] && full[1] && !fresh[1] && left_tx != 16'd0);
            if (out_valid && out_sel == 2'd3) assert (out_data == 64'd0 && flush && left_tx != 16'd0);
            if (!out_valid) assert (!(take));
            assert (!(fresh[0] && !full[0]) && !(fresh[1] && !full[1]));
        end
    end
`endif
endmodule
`default_nettype wire

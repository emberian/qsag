// Compact ASS2-0P5 Synchronous Serial Host Target (`HOST_SCK` domain, SPI mode 0):
//   Shares ONE 64-bit `io_sr` shift register across RX word assembly and TX word streaming,
//   and ONE 64-bit `rx_word_o` CDC launch register across header & payload words.
module qsag_ass2_host (
    input  logic        sck,
    input  logic        cs_n,
    input  logic        rst_n,
    input  logic        tamper_n,
    input  logic [7:0]  dq_i,
    output logic [7:0]  dq_o,
    output logic [7:0]  dq_oe,
    input  logic [63:0] diag_word_i,
    input  logic [63:0] resp_w0_i,
    input  logic [63:0] resp_word_i,
    output logic        rx_hdr_toggle_o,
    output logic        rx_word_toggle_o,
    output logic [7:0]  rx_widx_o,
    output logic [63:0] rx_word_o,
    output logic        tx_next_toggle_o,
    output logic [4:0]  tx_widx_o
);
    typedef enum logic [2:0] {
        P_PREFIX, P_RX_HDR, P_RX_BODY, P_DUMMY, P_TX_DIAG, P_TX_WORDS, P_END
    } hphase_t;

    hphase_t     phase;
    logic [1:0]  width_mode;
    logic [2:0]  sub_pos, byte_pos;
    logic [6:0]  rx_shift;
    logic [63:0] io_sr;
    logic [5:0]  diag_bit;
    logic [7:0]  rem_words;
    logic [7:0]  word_idx;
    logic load_frame;
    logic        is_diag;

    wire selected_n  = rst_n && tamper_n && !cs_n;
    wire req_reset_n = rst_n && tamper_n;

    logic [7:0] rx_byte;
    logic       byte_done;
    always_comb begin
        if (phase == P_PREFIX || width_mode == 2'd0) begin
            rx_byte   = {rx_shift[6:0], dq_i[0]};
            byte_done = (sub_pos == 3'd7);
        end else if (width_mode == 2'd1) begin
            rx_byte   = {rx_shift[3:0], dq_i[3:0]};
            byte_done = (sub_pos == 3'd1);
        end else begin
            rx_byte   = dq_i;
            byte_done = 1'b1;
        end
    end

    wire [63:0] assembled = {rx_byte, io_sr[55:0]};
    wire [23:0] hdr_blen  = assembled[47:24];
    wire [7:0]  hdr_words = (hdr_blen[23:10] != 14'd0) ? 8'd64 : 8'((hdr_blen[9:0] + 10'd7) >> 3);

    wire issue_hdr  = (phase == P_RX_HDR)  && byte_done && (byte_pos == 3'd7);
    wire issue_word = (phase == P_RX_BODY) && byte_done &&
                      (byte_pos == 3'd7 || (load_frame && byte_pos == 3'd3));
    wire issue_tx   = (phase == P_DUMMY && sub_pos == 3'd7 && !is_diag)
                    || (phase == P_TX_WORDS && byte_done && byte_pos == 3'd7 && rem_words != 8'd0);

    always_ff @(posedge sck or negedge req_reset_n) begin
        if (!req_reset_n) begin
            rx_word_o        <= 64'd0;
            rx_hdr_toggle_o  <= 1'b0;
            rx_word_toggle_o <= 1'b0; rx_widx_o <= 8'd0;
            tx_next_toggle_o <= 1'b0; tx_widx_o <= 5'd0;
        end else if (!cs_n) begin
            if (issue_hdr) rx_word_o <= assembled;
            if (issue_word) rx_word_o <= load_frame ? {32'd0, assembled[63:32]} : assembled;
            if (issue_hdr)  rx_hdr_toggle_o <= !rx_hdr_toggle_o;
            if (issue_word) begin
                rx_word_toggle_o <= !rx_word_toggle_o;
                rx_widx_o        <= load_frame ? {word_idx[6:0], byte_pos[2]} : word_idx;
            end
            if (issue_tx) begin
                tx_next_toggle_o <= !tx_next_toggle_o;
                tx_widx_o        <= (phase == P_DUMMY) ? 5'd0 : (word_idx[4:0] + 5'd1);
            end
        end
    end

    always_ff @(posedge sck or negedge selected_n) begin
        if (!selected_n) begin
            load_frame <= 1'b0; phase <= P_PREFIX; width_mode <= 2'd0; sub_pos <= 3'd0; byte_pos <= 3'd0;
            rx_shift <= 7'd0; io_sr <= 64'd0;
            diag_bit <= 6'd63; rem_words <= 8'd0; word_idx <= 8'd0; is_diag <= 1'b0;
        end else case (phase)
            P_PREFIX: begin
                rx_shift <= {rx_shift[5:0], dq_i[0]};
                if (sub_pos == 3'd7) begin
                    sub_pos  <= 3'd0;
                    byte_pos <= 3'd0;
                    word_idx <= 8'd0;
                    is_diag  <= 1'b0;
                    case (rx_byte)
                        8'h00: begin width_mode <= 2'd0; phase <= P_RX_HDR; end
                        8'h40: begin width_mode <= 2'd1; phase <= P_RX_HDR; end
                        8'h80: begin width_mode <= 2'd2; phase <= P_RX_HDR; end
                        8'h02: begin width_mode <= 2'd0; phase <= P_DUMMY; end
                        8'h42: begin width_mode <= 2'd1; phase <= P_DUMMY; end
                        8'h82: begin width_mode <= 2'd2; phase <= P_DUMMY; end
                        8'h05: begin
                            width_mode <= 2'd0;
                            is_diag    <= 1'b1;
                            io_sr      <= diag_word_i;
                            phase      <= P_DUMMY;
                        end
                        default: phase <= P_END;
                    endcase
                end else begin
                    sub_pos <= sub_pos + 3'd1;
                end
            end
            P_RX_HDR, P_RX_BODY: begin
                if (width_mode == 2'd0) rx_shift <= {rx_shift[5:0], dq_i[0]};
                else if (width_mode == 2'd1) rx_shift[3:0] <= dq_i[3:0];
                sub_pos <= byte_done ? 3'd0 : (sub_pos + 3'd1);
                if (byte_done) begin
                    if (byte_pos != 3'd7) begin
                        io_sr[55:0] <= {rx_byte, io_sr[55:8]};
                        byte_pos    <= byte_pos + 3'd1;
                    end else begin
                        byte_pos <= 3'd0;
                        if (phase == P_RX_HDR) begin
                            load_frame <= assembled[15:8] == 8'h30;
                            rem_words <= hdr_words;
                            word_idx  <= 8'd0;
                            phase     <= (hdr_words == 8'd0) ? P_END : P_RX_BODY;
                        end else begin
                            word_idx  <= word_idx + 8'd1;
                            rem_words <= rem_words - 8'd1;
                            if (rem_words == 8'd1) phase <= P_END;
                        end
                    end
                end
            end
            P_DUMMY: begin
                if (sub_pos == 3'd7) begin
                    sub_pos  <= 3'd0;
                    byte_pos <= 3'd0;
                    word_idx <= 8'd0;
                    if (is_diag) begin
                        diag_bit <= 6'd63;
                        phase    <= P_TX_DIAG;
                    end else begin
                        io_sr     <= resp_w0_i;
                        rem_words <= 8'((resp_w0_i[31:24] + 8'd7) >> 3);
                        phase     <= P_TX_WORDS;
                    end
                end else begin
                    sub_pos <= sub_pos + 3'd1;
                end
            end
            P_TX_DIAG: begin
                io_sr <= {io_sr[62:0], 1'b0};
                if (diag_bit == 6'd0) phase <= P_END;
                else diag_bit <= diag_bit - 6'd1;
            end
            P_TX_WORDS: begin
                sub_pos <= byte_done ? 3'd0 : (sub_pos + 3'd1);
                if (byte_done) begin
                    if (byte_pos != 3'd7) begin
                        io_sr    <= {8'd0, io_sr[63:8]};
                        byte_pos <= byte_pos + 3'd1;
                    end else begin
                        byte_pos <= 3'd0;
                        if (rem_words != 8'd0) begin
                            io_sr     <= resp_word_i;
                            rem_words <= rem_words - 8'd1;
                            word_idx  <= word_idx + 8'd1;
                        end else begin
                            phase <= P_END;
                        end
                    end
                end
            end
            default: ;
        endcase
    end

    logic [7:0] dq_oe_q;
    logic [7:0] dq_next;
    always_comb begin
        dq_next = 8'd0;
        if (phase == P_TX_DIAG) begin
            dq_next = {6'd0, io_sr[63], 1'b0};
        end else if (phase == P_TX_WORDS) begin
            if (width_mode == 2'd2) dq_next = io_sr[7:0];
            else if (width_mode == 2'd1) dq_next = {4'd0, sub_pos[0] ? io_sr[3:0] : io_sr[7:4]};
            else dq_next = {6'd0, io_sr[{3'd0, ~sub_pos}], 1'b0};
        end
    end

    always_ff @(negedge sck or negedge selected_n) begin
        if (!selected_n) begin
            dq_o    <= 8'd0;
            dq_oe_q <= 8'd0;
        end else begin
            dq_o    <= dq_next;
            dq_oe_q <= ((phase == P_TX_DIAG) || (phase == P_TX_WORDS))
                     ? ((phase == P_TX_DIAG || width_mode == 2'd0) ? 8'h02
                      : (width_mode == 2'd1) ? 8'h0f : 8'hff)
                     : 8'h00;
        end
    end

    assign dq_oe = dq_oe_q;
endmodule

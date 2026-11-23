// Minimal 1-byte `LC_BLANK` non-blocking UART (`DIT = 1`, `0` `dffq_1` cells, `-17.5k um^2` vs 16B FIFO).
// Permanently muted (`tx = 1`, `rx_valid = 0`) outside `LC_BLANK && BOOT_MODE == 2'b10`.
module qsag_ass2_uart (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        dbg_enable,
    input  logic [11:0] clk_div,
    input  logic        tx_we,
    input  logic [7:0]  tx_byte,
    output logic        tx,
    output logic        tx_overflow,
    input  logic        rx,
    input  logic        rx_ack,
    output logic [7:0]  rx_byte,
    output logic        rx_valid
);
    logic [7:0]  tx_hold_q;
    logic        tx_hold_full_q;
    logic [11:0] tx_timer, rx_timer;
    logic [3:0]  tx_left, rx_pos;
    logic [9:0]  tx_shift;
    logic [7:0]  rx_shift;
    (* async_reg = "true" *) logic rx_meta, rx_sync;

    wire [11:0] eff_div  = (clk_div < 12'd4) ? 12'd4 : clk_div;
    wire [11:0] half_div = {1'b0, eff_div[11:1]} - 12'd1;
    assign tx = dbg_enable ? tx_shift[0] : 1'b1;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            tx_hold_q <= 8'd0; tx_hold_full_q <= 1'b0; tx_overflow <= 1'b0;
            tx_shift <= 10'h3ff; tx_left <= 4'd0; tx_timer <= 12'd0;
            rx_meta <= 1'b1; rx_sync <= 1'b1; rx_timer <= 12'd0; rx_pos <= 4'd0;
            rx_shift <= 8'd0; rx_byte <= 8'd0; rx_valid <= 1'b0;
        end else begin
            rx_meta <= rx;
            rx_sync <= rx_meta;

            if (!dbg_enable) begin
                tx_hold_q      <= 8'd0;
                tx_hold_full_q <= 1'b0;
                tx_left        <= 4'd0;
                tx_shift       <= 10'h3ff;
                rx_valid       <= 1'b0;
                rx_pos         <= 4'd0;
            end else begin
                if (tx_left == 4'd0) begin
                    if (tx_hold_full_q) begin
                        tx_shift       <= {1'b1, tx_hold_q, 1'b0};
                        tx_left        <= 4'd10;
                        tx_timer       <= eff_div - 12'd1;
                        tx_hold_full_q <= 1'b0;
                        if (tx_we) begin
                            tx_hold_q      <= tx_byte;
                            tx_hold_full_q <= 1'b1;
                        end
                    end else if (tx_we) begin
                        tx_shift <= {1'b1, tx_byte, 1'b0};
                        tx_left  <= 4'd10;
                        tx_timer <= eff_div - 12'd1;
                    end
                end else begin
                    if (tx_we) begin
                        if (!tx_hold_full_q) begin
                            tx_hold_q      <= tx_byte;
                            tx_hold_full_q <= 1'b1;
                        end else begin
                            tx_overflow <= 1'b1;
                        end
                    end
                    if (tx_timer == 12'd0) begin
                        tx_shift <= {1'b1, tx_shift[9:1]};
                        tx_left  <= tx_left - 4'd1;
                        tx_timer <= eff_div - 12'd1;
                    end else begin
                        tx_timer <= tx_timer - 12'd1;
                    end
                end

                if (rx_ack) rx_valid <= 1'b0;
                if (rx_pos == 4'd0) begin
                    if (!rx_sync) begin rx_timer <= half_div; rx_pos <= 4'd1; end
                end else if (rx_timer != 12'd0) begin
                    rx_timer <= rx_timer - 12'd1;
                end else begin
                    rx_timer <= eff_div - 12'd1;
                    rx_pos   <= rx_pos + 4'd1;
                    if (rx_pos == 4'd1 && rx_sync) rx_pos <= 4'd0;
                    else if (rx_pos == 4'd10) begin
                        rx_pos <= 4'd0;
                        if (rx_sync) begin rx_byte <= rx_shift; rx_valid <= 1'b1; end
                    end else if (rx_pos != 4'd1) begin
                        rx_shift <= {rx_sync, rx_shift[7:1]};
                    end
                end
            end
        end
    end
endmodule

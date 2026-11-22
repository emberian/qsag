// Shift-on-push (`icgtp_2` clock-gated), index-on-pop 16-byte non-blocking UART (`DIT = 1`).
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
    logic [7:0]  fifo [16];
    logic [4:0]  fifo_cnt;
    logic [11:0] tx_timer, rx_timer;
    logic [3:0]  tx_left, rx_pos;
    logic [9:0]  tx_shift;
    logic [7:0]  rx_shift;
    (* async_reg = "true" *) logic rx_meta, rx_sync;

    wire [11:0] eff_div  = (clk_div < 12'd4) ? 12'd4 : clk_div;
    wire [11:0] half_div = {1'b0, eff_div[11:1]} - 12'd1;
    wire        tx_push  = dbg_enable && tx_we && (fifo_cnt < 5'd16);
    wire        tx_pop   = (tx_left == 4'd0) && (fifo_cnt != 5'd0);

    assign tx = dbg_enable ? tx_shift[0] : 1'b1;

    // Pure wire shift chain gated by 1 `icgtp_2` per 16 FFs (0 write muxes, <0.30 ns ICG skew)
`ifdef GF180_SRAM_MACRO
    wire [7:0] fclk;
    wire [7:0] tx_byte_dly;
    for (genvar g = 0; g < 8; g++) begin : g_ficg
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__icgtp_2 u_ficg (
            .CLK(clk), .E(tx_push), .TE(1'b0), .Q(fclk[g])
        );
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__buf_4 u_dly (
            .I(tx_byte[g]), .Z(tx_byte_dly[g])
        );
    end
    for (genvar i = 0; i < 16; i++) begin : g_fifo
        wire [7:0] din = (i == 0) ? tx_byte_dly : fifo[i - 1];
        for (genvar b = 0; b < 8; b++) begin : g_bit
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__dffq_1 u_ff (
                .CLK(fclk[i / 2]), .D(din[b]), .Q(fifo[i][b])
            );
        end
    end
`else
    always_ff @(posedge clk) begin
        if (tx_push) begin
            fifo[0] <= tx_byte;
            for (int i = 1; i < 16; i++) fifo[i] <= fifo[i - 1];
        end
    end
`endif

    wire [3:0] rd_idx = 4'(fifo_cnt - 5'd1);

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            fifo_cnt <= 5'd0; tx_overflow <= 1'b0;
            tx_shift <= 10'h3ff; tx_left <= 4'd0; tx_timer <= 12'd0;
            rx_meta <= 1'b1; rx_sync <= 1'b1; rx_timer <= 12'd0; rx_pos <= 4'd0;
            rx_shift <= 8'd0; rx_byte <= 8'd0; rx_valid <= 1'b0;
        end else begin
            rx_meta <= rx;
            rx_sync <= rx_meta;

            if (dbg_enable && tx_we && (fifo_cnt == 5'd16)) tx_overflow <= 1'b1;
            if (tx_pop) begin
                tx_shift <= {1'b1, fifo[rd_idx], 1'b0};
                tx_left  <= 4'd10;
                tx_timer <= eff_div - 12'd1;
            end else if (tx_left != 4'd0) begin
                if (tx_timer == 12'd0) begin
                    tx_shift <= {1'b1, tx_shift[9:1]};
                    tx_left  <= tx_left - 4'd1;
                    tx_timer <= eff_div - 12'd1;
                end else begin
                    tx_timer <= tx_timer - 12'd1;
                end
            end
            case ({tx_push, tx_pop})
                2'b10: fifo_cnt <= fifo_cnt + 5'd1;
                2'b01: fifo_cnt <= fifo_cnt - 5'd1;
                default: ;
            endcase

            if (!dbg_enable) begin
                rx_valid <= 1'b0;
                rx_pos   <= 4'd0;
            end else begin
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

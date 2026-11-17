// Dregg-180 v2 host link: SPI target, mode 0, single bit (ARCHITECTURE.md 5.6, decision D4).
//
// The SPI part of qsag_io_shell, without its other personalities: command byte, byte and bit order, the
// read frame with eight dummy clocks, and the diagnostic read on SCK alone are the same. The Gray-code
// FIFOs are replaced by a two-word handshake in each direction (the shifter and one holding register).
//
// Frames (CS_N low; bytes most significant bit first; a 64-bit word is sent least significant byte first):
//   0x01 WRITE      request words follow. One frame carries one request; its first word is the header.
//                   The host sends a word only while RX_FREE is high (pad IRQ while CS_N is low).
//   0x02 READ       eight dummy clocks, then one response word. The host starts a READ only while
//                   TX_IRQ is high (pad IRQ while CS_N is high). Clocks beyond the word read zeros.
//   0x05 READ_DIAG  eight dummy clocks, then the diagnostic word below. It uses SCK only: it answers
//                   with the core clock stopped or the core in reset, and it never takes a response word.
//
// Diagnostic word:  [15:0] 16'hD182   [23:16] core heartbeat, sample 1   [31:24] {rst_n, busy, fault,
//   verify_ok, ready, 3'b0}   [39:32] heartbeat, sample 2 (16 SCK later)   [47:40] {rx overrun, tx
//   underrun, rx word pending, tx word available, 4'b0} as SCK sees them   [55:48] 0   [63:56] 8'h5A
//
// Clock domains: SCK (shifters, holding register, frame state) and the core clock. A word crosses with
// a toggle that passes through two flops; the data is read only while the toggle says it is stable.
`default_nettype none

module dregg_spi_link (
    input  wire         clk,          // core clock
    input  wire         rst_n,        // synchronised pad reset (core domain)
    input  wire         por_n,        // pad reset, asynchronous (SCK domain)
    // pads
    input  wire         sck,
    input  wire         cs_n,
    input  wire         mosi,
    output logic        miso,
    output logic        miso_oe,
    output wire         irq,          // CS_N high: a response word is waiting; CS_N low: a request word may be sent
    // core
    output wire         in_valid,
    output wire         in_first,
    output wire  [63:0] in_data,
    input  wire         in_take,
    input  wire         out_valid,
    input  wire  [63:0] out_data,
    output wire         out_take,
    // status for the diagnostic word
    input  wire         busy,
    input  wire         fault,
    input  wire         verify_ok,
    input  wire         ready
);
    // ------------------------------------------------------------ frame reset (CS_N high) and SCK inverse
    wire frame_rst_raw, frame_rst_n, sck_n;
    qsag_clkand2 u_fr (.a(por_n), .b(~cs_n), .y(frame_rst_raw));
    qsag_clkbuf  u_fb (.a(frame_rst_raw), .y(frame_rst_n));
    qsag_clkinv  u_sn (.a(sck), .y(sck_n));

    // ------------------------------------------------------------ SCK domain: command and bit counters
    logic [2:0]  cbit;
    logic        cmd_done, c_wr, c_rd, c_diag;
    logic [6:0]  cmd_sh;
    wire  [7:0]  cmd_now = {cmd_sh, mosi};
    logic [5:0]  bitc;          // bit index inside the 64-bit word, both directions
    logic        w_first;       // the word being received is the first of the frame
    logic [62:0] rxw;
    logic [3:0]  dummy;
    logic        tx_act, tx_ok, tx_done;

    // handshake state (survives CS_N; cleared by the pad reset only)
    logic        rx_req, tx_ack, ovr, und;
    logic [63:0] rx_hold;
    logic        rx_first_q;
    wire         rx_ack_ss, tx_req_ss;
    logic        rx_ack, tx_req;                     // core domain
    qsag_sync2 u_ra (.clk(sck), .rst_n(por_n), .d(rx_ack), .q(rx_ack_ss));
    qsag_sync2 u_tr (.clk(sck), .rst_n(por_n), .d(tx_req), .q(tx_req_ss));
    wire rx_pend_s  = (rx_req != rx_ack_ss);         // a received word is waiting for the core
    wire tx_avail_s = (tx_req_ss != tx_ack);         // a response word is waiting for the host

    // received word: the shifter after this bit, bytes reversed (the first byte received is byte 0)
    wire [63:0] rx_sh = {rxw[62:0], mosi};
    wire [63:0] rx_word = {rx_sh[7:0], rx_sh[15:8], rx_sh[23:16], rx_sh[31:24], rx_sh[39:32], rx_sh[47:40],
                           rx_sh[55:48], rx_sh[63:56]};

    always_ff @(posedge sck or negedge frame_rst_n)
        if (!frame_rst_n) begin
            cbit     <= '0;
            cmd_done <= 1'b0;
            c_wr     <= 1'b0;
            c_rd     <= 1'b0;
            c_diag   <= 1'b0;
            cmd_sh   <= '0;
            bitc     <= '0;
            w_first  <= 1'b1;
            dummy    <= '0;
            tx_act   <= 1'b0;
            tx_ok    <= 1'b0;
            tx_done  <= 1'b0;
        end else begin
            if (!cmd_done) begin
                cmd_sh <= cmd_now[6:0];
                cbit   <= cbit + 3'd1;
                if (cbit == 3'd7) begin
                    cmd_done <= 1'b1;
                    c_wr     <= (cmd_now == 8'h01);
                    c_rd     <= (cmd_now == 8'h02);
                    c_diag   <= (cmd_now == 8'h05);
                end
            end else if (c_wr) begin
                bitc <= bitc + 6'd1;
                if (bitc == 6'd63) w_first <= 1'b0;
            end else if (c_rd || c_diag) begin
                if (!tx_act) begin
                    dummy <= dummy + 4'd1;
                    if (dummy == 4'd7) begin
                        tx_act <= 1'b1;
                        tx_ok  <= c_diag || tx_avail_s;
                    end
                end else if (!tx_done) begin
                    bitc <= bitc + 6'd1;
                    if (bitc == 6'd63) tx_done <= 1'b1;
                end
            end
        end

    // the receive shifter runs on every SCK edge and has no reset: a word is used only after 64 of its
    // own bits have gone through it
    always_ff @(posedge sck) rxw <= rx_sh[62:0];

    always_ff @(posedge sck or negedge por_n)
        if (!por_n) begin
            rx_req     <= 1'b0;
            rx_hold    <= '0;
            rx_first_q <= 1'b0;
            tx_ack     <= 1'b0;
            ovr        <= 1'b0;
            und        <= 1'b0;
        end else if (!cs_n) begin
            if (cmd_done && c_wr && bitc == 6'd63) begin
                if (rx_pend_s) ovr <= 1'b1;                  // the host ignored RX_FREE: the word is dropped
                else begin
                    rx_hold    <= rx_word;
                    rx_first_q <= w_first;
                    rx_req     <= ~rx_req;
                end
            end
            if (cmd_done && c_rd && tx_act && !tx_done && bitc == 6'd63 && tx_ok) tx_ack <= ~tx_ack;
            if (cmd_done && c_rd && !tx_act && dummy == 4'd7 && !tx_avail_s) und <= 1'b1;
        end

    // ------------------------------------------------------------ core domain
    wire rx_req_s, tx_ack_s;
    qsag_sync2 u_rr (.clk(clk), .rst_n(rst_n), .d(rx_req), .q(rx_req_s));
    qsag_sync2 u_ta (.clk(clk), .rst_n(rst_n), .d(tx_ack), .q(tx_ack_s));
    logic [63:0] tx_word;
    assign in_valid = (rx_req_s != rx_ack);
    assign in_data  = rx_hold;
    assign in_first = rx_first_q;
    wire   tx_free  = (tx_req == tx_ack_s);
    assign out_take = out_valid && tx_free;

    logic [7:0] hb_bin, hb_gray;
    wire  [7:0] hb_nxt = hb_bin + 8'd1;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) begin
            rx_ack  <= 1'b0;
            tx_req  <= 1'b0;
            tx_word <= '0;
            hb_bin  <= '0;
            hb_gray <= '0;
        end else begin
            if (in_valid && in_take) rx_ack <= rx_req_s;
            if (out_take) begin
                tx_word <= out_data;
                tx_req  <= ~tx_req;
            end
            hb_bin  <= hb_nxt;
            hb_gray <= hb_nxt ^ {1'b0, hb_nxt[7:1]};
        end

    // IRQ pad: level in the core domain, meaning selected by CS_N
    assign irq = cs_n ? !tx_free : !in_valid;

    // ------------------------------------------------------------ transmit
    logic [7:0] dg_hb1, dg_hb2;
    always_ff @(posedge sck or negedge frame_rst_n)
        if (!frame_rst_n) begin
            dg_hb1 <= '0;
            dg_hb2 <= '0;
        end else if (c_diag) begin
            if (!tx_act && dummy == 4'd0) dg_hb1 <= hb_gray;
            if (tx_act && bitc == 6'd16)  dg_hb2 <= hb_gray;
        end
    wire [63:0] diag_word = {8'h5A, 8'h00, ovr, und, rx_pend_s, tx_avail_s, 4'd0, dg_hb2,
                             rst_n, busy, fault, verify_ok, ready, 3'd0, dg_hb1, 16'hD182};
    wire [63:0] t_src = c_diag ? diag_word : (tx_ok ? tx_word : 64'd0);
    always_ff @(posedge sck_n or negedge frame_rst_n)
        if (!frame_rst_n) begin
            miso    <= 1'b0;
            miso_oe <= 1'b0;
        end else begin
            miso_oe <= tx_act;
            miso    <= tx_act && !tx_done && t_src[{bitc[5:3], ~bitc[2:0]}];
        end
endmodule
`default_nettype wire

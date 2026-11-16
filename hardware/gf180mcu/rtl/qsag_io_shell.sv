// QSAG-NI-180 three-personality I/O shell and elastic clock-domain crossing.
//
// IO_MODE (inputs[2:1], static strap):
//   00  SPI / QSPI / OSPI target, SCK = bidir[18], CS_N = inputs[3], DQ[7:0] = bidir[7:0]
//       first byte after CS_N falls (always 1-bit, MSB first, on DQ0):
//         0x01 write x1   0x41 write x4   0x81 write x8     (payload bytes follow)
//         0x02 read  x1   0x42 read  x4   0x82 read  x8     (8 dummy clocks, then data;
//                                                            x1 data on DQ1)
//   01  source-synchronous dual simplex: RX_CLK/RX_VALID/RX_DATA[7:0] in on the west bank,
//       TX_CLK/TX_VALID/TX_DATA[7:0] out on the east bank
//   1x  clockless two-phase bundled data: REQ_IN/ACK_OUT + 16 data bits in,
//       REQ_OUT/ACK_IN + 8 data bits out
// Every link moves 64-bit words, least significant byte first (mode 1x ingress: least
// significant 16 bits first). Words cross to and from the core clock through Gray-pointer
// FIFOs (8 words in, 4 words out).
`default_nettype none

module qsag_io_shell (
    input  wire         clk_core,
    input  wire         rst_core_n,
    input  wire         arst_n,
    input  wire  [1:0]  io_mode,
    input  wire         cs_n,
    // pads
    input  wire  [37:0] bidir_in,
    output logic [37:0] bidir_out,
    output logic [37:0] bidir_oe,
    output logic [37:0] bidir_cs,
    output logic [37:0] bidir_pu,
    output logic [37:0] bidir_pd,
    // core streams
    output wire         in_valid,
    output wire  [63:0] in_data,
    input  wire         in_pop,
    output wire         out_ready,
    input  wire  [63:0] out_data,
    input  wire         out_push,
    // status and side-band
    input  wire         verify_ok,
    input  wire         fault,
    input  wire         busy,
    input  wire         clk_mon,
    input  wire         an_cs_n,
    input  wire         an_sck,
    input  wire         an_mosi,
    output wire         an_miso,
    output wire         tamper_n,
    output wire         rx_overrun,
    output wire         tx_underrun
);
    wire m_spi   = (io_mode == 2'd0);
    wire m_ss    = (io_mode == 2'd1);
    wire m_async = io_mode[1];

    // ------------------------------------------------------------ link clocks and resets
    wire sck = bidir_in[18];
    wire rxc = bidir_in[37];
    wire c_ext, clk_rx, clk_tx, clk_txn;
    qsag_clkmux2 u_cm0 (.a(sck),   .b(rxc),      .sel(io_mode[0]),              .y(c_ext));
    qsag_clkmux2 u_cm1 (.a(c_ext), .b(clk_core), .sel(io_mode[1]),              .y(clk_rx));
    qsag_clkmux2 u_cm2 (.a(sck),   .b(clk_core), .sel(io_mode[1] | io_mode[0]), .y(clk_tx));
    qsag_clkinv  u_cn  (.a(clk_tx), .y(clk_txn));

    // SCK is not free-running, so the SPI domain is released asynchronously (the host must
    // not clock during reset); the other link domains use a two-flop release.
    wire rx_srst_n;
    qsag_rst_sync u_rrs (.clk(clk_rx), .arst_n(arst_n), .rst_n(rx_srst_n));
    wire rx_rst_n  = m_spi ? arst_n : rx_srst_n;
    wire tx_rst_n  = m_spi ? arst_n : rst_core_n;
    wire spi_rst_n = arst_n & ~cs_n;                 // CS_N high resets the SPI framing
    wire pk_rst_n  = rx_rst_n & ~(m_spi & cs_n);
    wire txl_rst_n = tx_rst_n & ~(m_spi & cs_n);

    // ------------------------------------------------------------ FIFOs
    logic        push;
    logic [63:0] push_data;
    wire         i_full, e_empty;
    wire [3:0]   i_rcount;
    wire [2:0]   e_wcount;
    wire [63:0]  e_rdata;
    wire         i_empty, e_full;
    logic        e_rinc;
    wire [3:0]   i_wcount_u;
    wire [2:0]   e_rcount_u;

    qsag_async_fifo_gray #(.W(64), .AW(3)) u_ingress (
        .wclk(clk_rx), .wrst_n(rx_rst_n), .winc(push), .wdata(push_data), .wfull(i_full), .wcount(i_wcount_u),
        .rclk(clk_core), .rrst_n(rst_core_n), .rinc(in_pop), .rdata(in_data), .rempty(i_empty), .rcount(i_rcount)
    );
    qsag_async_fifo_gray #(.W(64), .AW(2)) u_egress (
        .wclk(clk_core), .wrst_n(rst_core_n), .winc(out_push), .wdata(out_data), .wfull(e_full), .wcount(e_wcount),
        .rclk(clk_tx), .rrst_n(tx_rst_n), .rinc(e_rinc), .rdata(e_rdata), .rempty(e_empty), .rcount(e_rcount_u)
    );
    assign in_valid  = !i_empty;
    assign out_ready = !e_full;

    // Flow-control pins, generated where the clock always runs. The occupancy seen here lags
    // a pointer moved by the link clock by two core clocks. In SPI mode both pins are therefore
    // forced low while CS_N is low and for three more core clocks after it rises, by which time
    // the pointers of the finished frame have crossed: a high level is never stale.
    logic       rx_credit, tx_irq;
    logic [1:0] cs_cnt;
    wire        cs_s;
    qsag_sync2 #(.RV(1'b0)) u_css (.clk(clk_core), .rst_n(rst_core_n), .d(cs_n), .q(cs_s));
    wire        cs_ok = !m_spi || (cs_cnt == 2'd3);
    always_ff @(posedge clk_core or negedge rst_core_n)
        if (!rst_core_n) begin
            rx_credit <= 1'b0;
            tx_irq    <= 1'b0;
            cs_cnt    <= '0;
        end else begin
            cs_cnt    <= !cs_s ? 2'd0 : (cs_cnt == 2'd3) ? 2'd3 : cs_cnt + 2'd1;
            rx_credit <= (i_rcount <= 4'd2) && cs_ok;   // room for six words (48 bytes)
            tx_irq    <= (e_wcount != 3'd0) && cs_ok;   // at least one whole word to read
        end

    // ------------------------------------------------------------ SPI target, receive side
    wire [7:0]  dq = bidir_in[7:0];
    logic [2:0] cbit;
    logic       cmd_done, s_rd;
    logic [1:0] s_w;                // 0: x1, 1: x4, 2: x8
    logic [6:0] cmd_sh;
    logic [2:0] sub;
    logic [6:0] bsh;
    logic       spi_bv;
    logic [7:0] spi_byte;
    wire  [7:0] cmd_now = {cmd_sh, dq[0]};

    always_comb begin
        spi_bv   = 1'b0;
        spi_byte = {bsh, dq[0]};
        if (cmd_done && !s_rd) begin
            unique case (s_w)
                2'd0:    spi_bv = (sub == 3'd7);
                2'd1: begin
                    spi_bv   = sub[0];
                    spi_byte = {bsh[3:0], dq[3:0]};
                end
                default: begin
                    spi_bv   = 1'b1;
                    spi_byte = dq;
                end
            endcase
        end
    end

    always_ff @(posedge clk_rx or negedge spi_rst_n)
        if (!spi_rst_n) begin
            cbit     <= '0;
            cmd_done <= 1'b0;
            s_rd     <= 1'b0;
            s_w      <= '0;
            cmd_sh   <= '0;
            sub      <= '0;
            bsh      <= '0;
        end else if (m_spi) begin
            if (!cmd_done) begin
                cmd_sh <= cmd_now[6:0];
                cbit   <= cbit + 3'd1;
                if (cbit == 3'd7) begin
                    cmd_done <= 1'b1;
                    s_rd     <= cmd_now[1];
                    s_w      <= cmd_now[7] ? 2'd2 : cmd_now[6] ? 2'd1 : 2'd0;
                end
            end else if (!s_rd) begin
                sub <= spi_bv ? 3'd0 : sub + 3'd1;
                bsh <= (s_w == 2'd0) ? {bsh[5:0], dq[0]} : {3'd0, dq[3:0]};
            end
        end

    // ------------------------------------------------------------ clockless ingress stage
    wire        as_c, as_ack;
    wire [15:0] as_d;
    logic       as_taken;
    qsag_mpipe_stage #(.W(16)) u_mp (
        .rst_n(arst_n & m_async), .req_in(bidir_in[37] & m_async),
        .din({bidir_in[18], bidir_in[6:0], bidir_in[34:27]}),
        .ack_out(as_ack), .taken(as_taken), .c_out(as_c), .dout(as_d)
    );
    wire as_cs;
    qsag_sync2 u_asc (.clk(clk_rx), .rst_n(rx_rst_n), .d(as_c), .q(as_cs));
    wire as_avail = m_async && (as_cs != as_taken);

    // ------------------------------------------------------------ word packer (clk_rx)
    logic [55:0] rxw;
    logic [2:0]  bcnt;
    logic        ovr;
    wire         bv1   = m_spi ? spi_bv : (m_ss & bidir_in[36]);
    wire  [7:0]  byte1 = m_spi ? spi_byte : bidir_in[34:27];
    wire         last2 = (bcnt == 3'd6);
    wire         as_go = as_avail && !(last2 && i_full);

    always_comb begin
        push      = 1'b0;
        push_data = {byte1, rxw};
        if (m_async) begin
            push      = as_go && last2;
            push_data = {as_d, rxw[47:0]};
        end else push = bv1 && (bcnt == 3'd7);
    end

    always_ff @(posedge clk_rx or negedge pk_rst_n)
        if (!pk_rst_n) begin
            rxw  <= '0;
            bcnt <= '0;
        end else if (m_async) begin
            if (as_go) begin
                bcnt <= last2 ? 3'd0 : bcnt + 3'd2;
                unique case (bcnt[2:1])
                    2'd0:    rxw[15:0]  <= as_d;
                    2'd1:    rxw[31:16] <= as_d;
                    2'd2:    rxw[47:32] <= as_d;
                    default: ;
                endcase
            end
        end else if (bv1) begin
            bcnt <= bcnt + 3'd1;
            for (int b = 0; b < 7; b++) if (bcnt == 3'(b)) rxw[8*b +: 8] <= byte1;
        end

    always_ff @(posedge clk_rx or negedge rx_rst_n)
        if (!rx_rst_n) begin
            ovr      <= 1'b0;
            as_taken <= 1'b0;
        end else begin
            if (push && i_full) ovr <= 1'b1;
            if (as_go) as_taken <= as_cs;
        end

    // ------------------------------------------------------------ transmit side (clk_tx)
    logic        t_have, t_req, txv_o;
    logic [2:0]  t_byte;
    logic [1:0]  t_st;
    logic [7:0]  txd_o;
    logic [3:0]  dummy;
    logic [5:0]  tpos;
    logic        tx_act, und;
    wire         t_in_s;                       // TX_READY (mode 01) / ACK_IN (mode 1x)
    qsag_sync2 u_ti (.clk(clk_tx), .rst_n(tx_rst_n), .d(bidir_in[17]), .q(t_in_s));

    wire [7:0] hbyte    = e_rdata[8*t_byte +: 8];
    wire [5:0] tstep    = (s_w == 2'd0) ? 6'd1 : (s_w == 2'd1) ? 6'd4 : 6'd8;
    wire       spi_rd   = m_spi && cmd_done && s_rd;
    // SPI read: the word at the head of the egress FIFO is shifted out in place and popped
    // only on the clock that takes its last beat, so a read aborted by CS_N loses nothing.
    wire       spi_last  = spi_rd && tx_act && (tpos + tstep == 6'd0);
    wire       spi_first = spi_rd && !tx_act && (dummy == 4'd7);

    always_comb begin
        e_rinc = 1'b0;
        if (m_spi)     e_rinc = spi_last;
        else if (m_ss) e_rinc = !e_empty && t_in_s && (t_byte == 3'd7);
        else           e_rinc = t_have && (t_st == 2'd2) && (t_in_s == t_req) && (t_byte == 3'd7);
    end

    always_ff @(posedge clk_tx or negedge txl_rst_n)
        if (!txl_rst_n) begin
            t_have <= 1'b0;
            t_byte <= '0;
            t_st   <= '0;
            txd_o  <= '0;
            txv_o  <= 1'b0;
            dummy  <= '0;
            tpos   <= '0;
            tx_act <= 1'b0;
        end else if (m_spi) begin
            if (spi_rd) begin
                if (!tx_act) dummy <= dummy + 4'd1;
                else         tpos  <= tpos + tstep;
                if (spi_first) tx_act <= 1'b1;
            end
        end else if (m_ss) begin
            // Launch at the core rising edge; the forwarded inverted clock
            // samples at the falling edge, halfway through the data eye.
            // Pop only after loading byte seven into the output register.
            txv_o <= !e_empty && t_in_s;
            if (!e_empty && t_in_s) begin
                txd_o <= hbyte;
                t_byte <= t_byte + 3'd1;
            end
        end else begin
            if (!t_have) begin
                txv_o <= 1'b0;
                if (!e_empty) begin         // the head word is sent in place and popped at its end
                    t_have <= 1'b1;
                    t_byte <= '0;
                    t_st   <= '0;
                end
            end else begin
                unique case (t_st)
                    2'd0: begin                 // data one full cycle ahead of the request edge
                        txd_o <= hbyte;
                        t_st  <= 2'd1;
                    end
                    2'd1: t_st <= 2'd2;         // t_req toggles below
                    default: if (t_in_s == t_req) begin
                        t_byte <= t_byte + 3'd1;
                        t_st   <= 2'd0;
                        if (t_byte == 3'd7) t_have <= 1'b0;
                    end
                endcase
            end
        end

    // the request toggle and the underrun flag survive CS_N
    always_ff @(posedge clk_tx or negedge tx_rst_n)
        if (!tx_rst_n) begin
            t_req <= 1'b0;
            und   <= 1'b0;
        end else begin
            if (!m_spi && !m_ss && t_have && t_st == 2'd1) t_req <= ~t_req;
            if (spi_rd && tx_act && e_empty) und <= 1'b1;   // a beat was clocked with nothing to send
        end

    // SPI data out: launched on the falling edge
    wire [7:0] tbyte = e_rdata[8*tpos[5:3] +: 8];
    logic [7:0] sdq_o;
    logic       soe_o;
    always_ff @(posedge clk_txn or negedge spi_rst_n)
        if (!spi_rst_n) begin
            sdq_o <= '0;
            soe_o <= 1'b0;
        end else begin
            soe_o <= m_spi && tx_act;
            unique case (s_w)
                2'd0:    sdq_o <= {6'd0, tbyte[3'd7 - tpos[2:0]], 1'b0};
                2'd1:    sdq_o <= {4'd0, tpos[2] ? tbyte[3:0] : tbyte[7:4]};
                default: sdq_o <= tbyte;
            endcase
        end

    // ------------------------------------------------------------ status crossings
    qsag_sync2 u_so (.clk(clk_core), .rst_n(rst_core_n), .d(ovr), .q(rx_overrun));
    qsag_sync2 u_su (.clk(clk_core), .rst_n(rst_core_n), .d(und), .q(tx_underrun));

    // ------------------------------------------------------------ pad map
    assign an_miso  = bidir_in[25];
    assign tamper_n = bidir_in[26];

    always_comb begin
        bidir_out = '0;
        bidir_oe  = '0;
        bidir_cs  = '0;
        bidir_pu  = '0;
        bidir_pd  = '0;
        // common: CLK_MON, ANCHOR_SPI, tamper
        bidir_out[21] = clk_mon;
        bidir_out[22] = an_cs_n;
        bidir_out[23] = an_sck;
        bidir_out[24] = an_mosi;
        bidir_oe[24:21] = 4'hF;
        bidir_pd[25]  = 1'b1;
        bidir_pu[26]  = 1'b1;
        bidir_cs[26]  = 1'b1;
        bidir_cs[18]  = 1'b1;
        bidir_cs[17]  = 1'b1;
        bidir_cs[37:36] = 2'b11;
        unique case (io_mode)
            2'd0: begin
                bidir_out[7:0] = sdq_o;
                bidir_oe[7:0]  = !soe_o ? 8'h00 : (s_w == 2'd0) ? 8'h02 : (s_w == 2'd1) ? 8'h0F : 8'hFF;
                bidir_out[16]  = verify_ok;
                bidir_out[17]  = fault;
                bidir_out[19]  = rx_credit & cs_n;
                bidir_out[20]  = tx_irq & cs_n;
                bidir_oe[17:16] = 2'b11;
                bidir_oe[20:19] = 2'b11;
                bidir_pd[15:8]  = 8'hFF;
                bidir_pd[37:27] = 11'h7FF;
            end
            2'd1: begin
                bidir_out[6]    = verify_ok;
                bidir_oe[6]     = 1'b1;
                bidir_out[14:7] = txd_o;
                bidir_out[15]   = clk_txn;
                bidir_out[16]   = txv_o;
                bidir_oe[16:7]  = 10'h3FF;
                bidir_out[19]   = busy;
                bidir_out[20]   = fault;
                bidir_oe[20:19] = 2'b11;
                bidir_out[35]   = rx_credit;
                bidir_oe[35]    = 1'b1;
                bidir_pd[5:0]   = 6'h3F;
                bidir_pd[18]    = 1'b1;
            end
            default: begin
                bidir_out[14:7] = txd_o;
                bidir_out[15]   = t_req;
                bidir_out[16]   = verify_ok;
                bidir_oe[16:7]  = 10'h3FF;
                bidir_out[19]   = busy;
                bidir_out[20]   = tx_irq;
                bidir_oe[20:19] = 2'b11;
                bidir_out[35]   = fault;
                bidir_out[36]   = as_ack;
                bidir_oe[36:35] = 2'b11;
            end
        endcase
    end

    wire unused = &{1'b0, i_wcount_u, e_rcount_u, bidir_in[35], bidir_in[24:19], bidir_in[16:8]};
endmodule
`default_nettype wire

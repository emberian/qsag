// Dregg-180 (QSAG-NI-180) three-personality I/O shell, symmetric Muller-C egress, sideband mux,
// and per-bank ground-bounce-controlled pad drivers.
//
// GOTCHA #4 & #5 silicon fixes:
//   * CSR-overridable `IO_MODE` (`csr_iomode_en ? csr_iomode : io_mode_strap`) and flexible `SCK`
//     (`bidir[18]` default or `clk_pad` when `csr_sck_clkpad` is set).
//   * Clean buffered resets (`qsag_clkbuf` on `spi_rst_n`, `rx_rst_n`, `tx_rst_n`).
//   * Symmetric clockless 2-phase Sutherland Muller-C egress (`qsag_mpipe_tx_stage`) for Mode `1x`
//     alongside 1-byte-per-core-clock center-aligned Mode `01` source-synchronous TX.
//   * ESD-protected `bi_24t` sideband pad routing for NFC (13.56 MHz carrier, ASK, 847.5 kHz load
//     mod), 32-bit Direct-RF NCO, and < 6 ns Brands-Chaum responder + pad-loopback Vernier TDC:
//       - IO_MODE 00 (SPI):         bidir[8..13]
//       - IO_MODE 01 (Source-Sync): bidir[0..5]
//       - IO_MODE 1x (Async, when `csr_async_sb_en` = 1 between packets): bidir[0..5]
//   * Per-bank slew-rate control (`bidir_sl`): `NCO_RF_OUT` & `DB_RESP_OUT` default to FAST slew
//     (`SL=0`) for < 6 ns turnaround, while `DQ[7:0]`, `TX_DATA[7:0]`, and `CTRL` banks are
//     independently slew-controlled via CSR (`SL=1` slow default to prevent L*di/dt bounce).
`default_nettype none

module qsag_io_shell (
    input  wire         clk_core,
    input  wire         rst_core_n,
    input  wire         arst_n,
    input  wire         clk_pad,
    input  wire  [1:0]  io_mode_strap,
    input  wire         cs_n,
    // CSR I/O & slew controls
    input  wire         csr_sck_clkpad,
    input  wire         csr_iomode_en,
    input  wire  [1:0]  csr_iomode,
    input  wire         csr_async_sb_en,
    input  wire         slew_dq,          // default 1 (slow)
    input  wire         slew_tx,          // default 1 (slow)
    input  wire         slew_ctrl,        // default 1 (slow)
    input  wire         slew_rf_db,       // default 0 (FAST for < 6 ns DB & RF NCO!)
    // pads
    input  wire  [37:0] bidir_in,
    output logic [37:0] bidir_out,
    output logic [37:0] bidir_oe,
    output logic [37:0] bidir_cs,
    output logic [37:0] bidir_sl,
    output logic [37:0] bidir_ie,
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
    // Houyhnhnm sideband organs (NFC + NCO + Distance-Bounding/TDC)
    output wire         nfc_clk_in,
    output wire         nfc_ask_in,
    input  wire         nfc_load_mod,
    input  wire         nco_rf_out,
    output wire         db_chal_in,
    input  wire         db_resp_out,
    input  wire         db_resp_oe,
    input  wire         db_resp_ie_force,
    output wire         db_resp_loopback,
    output wire  [1:0]  active_io_mode,
    output wire         rx_overrun,
    output wire         tx_underrun
);
    wire [1:0] io_mode = csr_iomode_en ? csr_iomode : io_mode_strap;
    assign active_io_mode = io_mode;

    wire m_spi   = (io_mode == 2'd0);
    wire m_ss    = (io_mode == 2'd1);
    wire m_async = io_mode[1];

    // ------------------------------------------------------------ link clocks and resets
    wire sck;
    qsag_clkmux2 u_sck_mux (.a(bidir_in[18]), .b(clk_pad), .sel(csr_sck_clkpad), .y(sck));
    wire rxc = bidir_in[37];
    wire c_ext, clk_rx, clk_tx, clk_txn;
    qsag_clkmux2 u_cm0 (.a(sck),   .b(rxc),      .sel(io_mode[0]),              .y(c_ext));
    qsag_clkmux2 u_cm1 (.a(c_ext), .b(clk_core), .sel(io_mode[1]),              .y(clk_rx));
    qsag_clkmux2 u_cm2 (.a(sck),   .b(clk_core), .sel(io_mode[1] | io_mode[0]), .y(clk_tx));
    qsag_clkinv  u_cn  (.a(clk_tx), .y(clk_txn));

    wire rx_srst_n;
    qsag_rst_sync u_rrs (.clk(clk_rx), .arst_n(arst_n), .rst_n(rx_srst_n));
    wire rx_rst_raw = m_spi ? arst_n : rx_srst_n;
    wire tx_rst_raw = m_spi ? arst_n : rst_core_n;
    wire rx_rst_n, tx_rst_n;
    qsag_clkbuf u_rxrb (.a(rx_rst_raw), .y(rx_rst_n));
    qsag_clkbuf u_txrb (.a(tx_rst_raw), .y(tx_rst_n));

    // Buffered SPI frame resets (active while CS_N is high in SPI mode; input_PAD[3] false-pathed)
    wire spi_rst_raw, pk_rst_raw, txl_rst_raw;
    wire spi_rst_n,   pk_rst_n,   txl_rst_n;
    qsag_clkand2 u_sra (.a(arst_n),   .b(~cs_n),          .y(spi_rst_raw));
    qsag_clkand2 u_pra (.a(rx_rst_n), .b(~(m_spi & cs_n)), .y(pk_rst_raw));
    qsag_clkand2 u_tra (.a(tx_rst_n), .b(~(m_spi & cs_n)), .y(txl_rst_raw));
    qsag_clkbuf  u_srb (.a(spi_rst_raw), .y(spi_rst_n));
    qsag_clkbuf  u_prb (.a(pk_rst_raw),  .y(pk_rst_n));
    qsag_clkbuf  u_trb (.a(txl_rst_raw), .y(txl_rst_n));

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
            rx_credit <= (i_rcount <= 4'd2) && cs_ok;
            tx_irq    <= (e_wcount != 3'd0) && cs_ok;
        end

    // ------------------------------------------------------------ SPI target, receive side
    wire [7:0]  dq = bidir_in[7:0];
    logic [2:0] cbit;
    logic       cmd_done, s_rd, s_diag;
    logic [1:0] s_w;
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
                2'd0: spi_bv = (sub == 3'd7);
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
            s_diag   <= 1'b0;
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
                    // 0x05 READ_DIAG: a single-bit read whose data is the diagnostic word below
                    s_diag   <= (cmd_now == 8'h05);
                    s_rd     <= cmd_now[1] || (cmd_now == 8'h05);
                    s_w      <= cmd_now[7] ? 2'd2 : cmd_now[6] ? 2'd1 : 2'd0;
                end
            end else if (!s_rd) begin
                sub <= spi_bv ? 3'd0 : sub + 3'd1;
                bsh <= (s_w == 2'd0) ? {bsh[5:0], dq[0]} : {3'd0, dq[3:0]};
            end
        end

    // ------------------------------------------------------------ clockless ingress Sutherland stage
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

    // ------------------------------------------------------------ transmit side + Muller-C egress
    logic       t_have, txv_o;
    logic [2:0] t_byte;
    logic       t_armed;
    logic [7:0] txd_o;
    logic [3:0] dummy;
    logic [5:0] tpos;
    logic       tx_act, und;
    wire        t_in_s;
    qsag_sync2 u_ti (.clk(clk_tx), .rst_n(tx_rst_n), .d(bidir_in[17]), .q(t_in_s));

    // Genuine clockless 2-phase Sutherland egress stage (`u_mptx`) for Mode 1x!
    logic       as_tx_src;
    wire        as_tx_cdone, as_tx_req_out;
    wire [7:0]  as_tx_dout;
    wire        as_tx_cdone_s;
    qsag_mpipe_tx_stage #(.W(8)) u_mptx (
        .rst_n(arst_n & m_async), .src_req(as_tx_src), .din(txd_o),
        .c_done(as_tx_cdone), .req_out(as_tx_req_out),
        .ack_in(bidir_in[17] & m_async), .dout(as_tx_dout)
    );
    qsag_sync2 u_txcd (.clk(clk_tx), .rst_n(tx_rst_n), .d(as_tx_cdone), .q(as_tx_cdone_s));

    wire [7:0] hbyte     = e_rdata[8*t_byte +: 8];
    wire [5:0] tstep     = (s_w == 2'd0) ? 6'd1 : (s_w == 2'd1) ? 6'd4 : 6'd8;
    wire       spi_rd    = m_spi && cmd_done && s_rd;
    wire       spi_last  = spi_rd && tx_act && (tpos + tstep == 6'd0);
    wire       spi_first = spi_rd && !tx_act && (dummy == 4'd7);

    // ------------------------------------------------------------ READ_DIAG (SPI command 0x05)
    // A 64-bit word shifted out on DQ1 like a single-bit read, using SCK only: the command decoder,
    // the bit counter and the output flop are all clocked by SCK and reset by CS_N / the reset pad,
    // so it answers with the core clock stopped, the core reset stuck, or the engine in S_DEAD.
    // It never pops the egress FIFO. Bytes leave least-significant first:
    //   [15:0]   16'hD180
    //   [23:16]  core heartbeat (Gray code of a free-running clk_core counter), sample 1
    //   [31:24]  {rst_core_n, busy, fault, verify_ok, io_mode[1:0], csr_sck_clkpad, clk_mon}
    //   [39:32]  core heartbeat, sample 2 (taken 24 SCK cycles after sample 1)
    //   [47:40]  {rx_overrun, tx_underrun, ingress full, egress empty, rx_credit, tx_irq, TAMPER_N, cs_ok}
    //   [55:48]  {ingress fill (SCK side) [3:0], 1'b0, egress fill (SCK side) [2:0]}
    //   [63:56]  8'h5A
    // The two heartbeat samples differ when clk_core is running. Status bits are live levels.
    logic [7:0] hb_bin, hb_gray;
    wire  [7:0] hb_nxt = hb_bin + 8'd1;
    always_ff @(posedge clk_core or negedge rst_core_n)
        if (!rst_core_n) begin
            hb_bin  <= '0;
            hb_gray <= '0;
        end else begin
            hb_bin  <= hb_nxt;
            hb_gray <= hb_nxt ^ {1'b0, hb_nxt[7:1]};
        end
    logic [7:0] dg_hb1, dg_hb2;
    wire [63:0] diag_word = {8'h5A,
                             i_wcount_u, 1'b0, e_rcount_u,
                             ovr, und, i_full, e_empty, rx_credit, tx_irq, bidir_in[26], cs_ok,
                             dg_hb2,
                             rst_core_n, busy, fault, verify_ok, io_mode, csr_sck_clkpad, clk_mon,
                             dg_hb1,
                             16'hD180};
    wire [63:0] t_src = s_diag ? diag_word : e_rdata;

    always_comb begin
        e_rinc = 1'b0;
        if (m_spi)     e_rinc = spi_last && !s_diag;
        else if (m_ss) e_rinc = !e_empty && t_in_s && (t_byte == 3'd7);
        else           e_rinc = t_have && t_armed && (as_tx_cdone_s == as_tx_src) && (t_byte == 3'd7);
    end

    always_ff @(posedge clk_tx or negedge txl_rst_n)
        if (!txl_rst_n) begin
            t_have  <= 1'b0;
            t_byte  <= '0;
            t_armed <= 1'b0;
            txd_o   <= '0;
            txv_o   <= 1'b0;
            dummy   <= '0;
            tpos    <= '0;
            tx_act  <= 1'b0;
            dg_hb1  <= '0;
            dg_hb2  <= '0;
        end else if (m_spi) begin
            if (spi_rd && s_diag && !tx_act && dummy == 4'd0) dg_hb1 <= hb_gray;
            if (spi_rd && s_diag && tx_act && tpos == 6'd16)  dg_hb2 <= hb_gray;
            if (spi_rd) begin
                if (!tx_act) dummy <= dummy + 4'd1;
                else         tpos  <= tpos + tstep;
                if (spi_first) tx_act <= 1'b1;
            end
        end else if (m_ss) begin
            // 1 byte per core clock, center-aligned inverted TX_CLK (`clk_txn`)
            txv_o <= !e_empty && t_in_s;
            if (!e_empty && t_in_s) begin
                txd_o  <= hbyte;
                t_byte <= t_byte + 3'd1;
            end
        end else begin
            // Mode 1x: feed bytes into symmetric Sutherland 2-phase Muller-C stage `u_mptx`
            if (!t_have) begin
                txv_o <= 1'b0;
                if (!e_empty) begin
                    t_have  <= 1'b1;
                    t_byte  <= 3'd0;
                    txd_o   <= e_rdata[7:0];
                    t_armed <= 1'b0;
                end
            end else if (!t_armed) begin
                t_armed <= 1'b1; // din (`txd_o`) stable before `as_tx_src` toggles below
            end else if (as_tx_cdone_s == as_tx_src) begin
                if (t_byte == 3'd7) begin
                    t_have  <= 1'b0;
                    t_armed <= 1'b0;
                end else begin
                    t_byte  <= t_byte + 3'd1;
                    txd_o   <= e_rdata[8*(t_byte + 3'd1) +: 8];
                    t_armed <= 1'b0;
                end
            end
        end

    always_ff @(posedge clk_tx or negedge tx_rst_n)
        if (!tx_rst_n) begin
            as_tx_src <= 1'b0;
            und       <= 1'b0;
        end else begin
            if (m_async && t_have && !t_armed) as_tx_src <= ~as_tx_src;
            if (spi_rd && !s_diag && tx_act && e_empty) und <= 1'b1;
        end

    wire [7:0]  tbyte = t_src[8*tpos[5:3] +: 8];
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

    qsag_sync2 u_so (.clk(clk_core), .rst_n(rst_core_n), .d(ovr), .q(rx_overrun));
    qsag_sync2 u_su (.clk(clk_core), .rst_n(rst_core_n), .d(und), .q(tx_underrun));

    // ------------------------------------------------------------ Pad & Sideband Map
    assign an_miso  = bidir_in[25];
    assign tamper_n = bidir_in[26];

    // Sideband bank selection (placed directly adjacent to dvss/dvdd pad pairs for minimal L*di/dt!):
    //   - IO_MODE 00 (SPI):                         bidir[8..11] + bidir[13..14] (next to dvss[1]/dvdd[1]!)
    //   - IO_MODE 01 (SS) or IO_MODE 1x + async_sb: bidir[0..5]                  (next to dvss[0]/dvdd[0]!)
    wire sb_on_b8  = m_spi;
    wire sb_on_b0  = m_ss || (m_async && csr_async_sb_en);

    assign nfc_clk_in       = sb_on_b8 ? bidir_in[8]  : (sb_on_b0 ? bidir_in[2] : 1'b0);
    assign nfc_ask_in       = sb_on_b8 ? bidir_in[9]  : (sb_on_b0 ? bidir_in[3] : 1'b1);
    assign db_chal_in       = sb_on_b8 ? bidir_in[13] : (sb_on_b0 ? bidir_in[1] : 1'b0);
    assign db_resp_loopback = sb_on_b8 ? bidir_in[14] : (sb_on_b0 ? bidir_in[0] : 1'b0);

    always_comb begin
        bidir_out = '0;
        bidir_oe  = '0;
        bidir_cs  = '0;
        bidir_pu  = '0;
        bidir_pd  = '0;
        // Per-bank slew defaults (slow slew = 1'b1 on general/status pins to suppress L*di/dt SSN)
        bidir_sl[7:0]   = {8{slew_dq}};
        bidir_sl[15:8]  = {8{slew_tx}};
        bidir_sl[37:16] = {22{slew_ctrl}};

        // Common sideband: CLK_MON, ANCHOR_SPI, TAMPER_ZEROIZE_N
        bidir_out[21]   = clk_mon;
        bidir_out[22]   = an_cs_n;
        bidir_out[23]   = an_sck;
        bidir_out[24]   = an_mosi;
        bidir_oe[24:21] = 4'hF;
        bidir_pd[25]    = 1'b1;
        bidir_pu[26]    = 1'b1;
        bidir_cs[26]    = 1'b1;
        bidir_cs[18]    = 1'b1;
        bidir_cs[17]    = 1'b1;
        bidir_cs[37:36] = 2'b11;

        unique case (io_mode)
            2'd0: begin
                bidir_out[7:0]  = sdq_o;
                bidir_oe[7:0]   = !soe_o ? 8'h00 : (s_w == 2'd0) ? 8'h02 : (s_w == 2'd1) ? 8'h0F : 8'hFF;
                // Houyhnhnm sideband on PAD_EAST (bidir[13..14] straddle dvss_pads[1]/dvdd_pads[1]!):
                bidir_cs[8]     = 1'b1;            // NFC 13.56 MHz Schmitt trigger
                bidir_pd[8]     = 1'b1;
                bidir_cs[9]     = 1'b1;            // NFC ASK Schmitt trigger
                bidir_pu[9]     = 1'b1;            // NFC ASK idle high
                bidir_out[10]   = nfc_load_mod;    // NFC 847.5 kHz load-mod TX
                bidir_oe[10]    = 1'b1;
                bidir_sl[10]    = 1'b1;            // hard slow slew on NFC shunt gate!
                bidir_out[11]   = nco_rf_out;      // 32-bit NCO RF TX
                bidir_oe[11]    = 1'b1;
                bidir_sl[11]    = slew_rf_db;      // fast slew default
                bidir_pd[12]    = 1'b1;            // guard pin between NCO_RF and DB_CHAL
                bidir_cs[13]    = 1'b0;            // DB_CHAL_IN: CMOS buffer (saves 0.65 ns vs Schmitt!)
                bidir_pd[13]    = 1'b1;
                bidir_out[14]   = db_resp_out;     // DB_RESP_OUT (< 5 ns mux2_4, next to dvss[1]!)
                bidir_oe[14]    = db_resp_oe;
                bidir_sl[14]    = 1'b0;            // hard fast slew for < 5 ns turnaround!
                bidir_pd[14]    = ~db_resp_oe;
                bidir_pd[15]    = 1'b1;

                bidir_out[16]   = verify_ok;
                bidir_out[17]   = fault;
                bidir_out[19]   = rx_credit & cs_n;
                bidir_out[20]   = tx_irq & cs_n;
                bidir_oe[17:16] = 2'b11;
                bidir_oe[20:19] = 2'b11;
                bidir_pd[37:27] = 11'h7FF;
            end
            2'd1: begin
                // Houyhnhnm sideband on PAD_SOUTH (bidir[0..1] straddle dvss_pads[0]/dvdd_pads[0]!):
                bidir_out[0]    = db_resp_out;     // DB_RESP_OUT (next to dvdd_pads[0]!)
                bidir_oe[0]     = db_resp_oe;
                bidir_sl[0]     = 1'b0;            // hard fast slew for < 5 ns turnaround!
                bidir_pd[0]     = ~db_resp_oe;
                bidir_cs[1]     = 1'b0;            // DB_CHAL_IN: CMOS buffer
                bidir_pd[1]     = 1'b1;
                bidir_cs[2]     = 1'b1;            // NFC 13.56 MHz Schmitt
                bidir_pd[2]     = 1'b1;
                bidir_cs[3]     = 1'b1;            // NFC ASK Schmitt
                bidir_pu[3]     = 1'b1;
                bidir_out[4]    = nfc_load_mod;    // NFC load-mod TX
                bidir_oe[4]     = 1'b1;
                bidir_sl[4]     = 1'b1;            // slow slew
                bidir_out[5]    = nco_rf_out;      // 32-bit NCO RF TX
                bidir_oe[5]     = 1'b1;
                bidir_sl[5]     = slew_rf_db;

                bidir_out[6]    = verify_ok;
                bidir_oe[6]     = 1'b1;
                bidir_out[14:7] = txd_o;
                bidir_out[15]   = clk_txn;
                bidir_out[16]   = txv_o;
                bidir_oe[16:7]  = 10'h3FF;
                bidir_sl[15:7]  = {9{slew_tx}};
                bidir_out[19]   = busy;
                bidir_out[20]   = fault;
                bidir_oe[20:19] = 2'b11;
                bidir_out[35]   = rx_credit;
                bidir_oe[35]    = 1'b1;
                bidir_pd[18]    = 1'b1;
            end
            default: begin
                if (csr_async_sb_en) begin
                    bidir_out[0]  = db_resp_out;
                    bidir_oe[0]   = db_resp_oe;
                    bidir_sl[0]   = 1'b0;
                    bidir_pd[0]   = ~db_resp_oe;
                    bidir_cs[1]   = 1'b0;
                    bidir_pd[1]   = 1'b1;
                    bidir_cs[2]   = 1'b1;
                    bidir_pd[2]   = 1'b1;
                    bidir_cs[3]   = 1'b1;
                    bidir_pu[3]   = 1'b1;
                    bidir_out[4]  = nfc_load_mod;
                    bidir_oe[4]   = 1'b1;
                    bidir_sl[4]   = 1'b1;
                    bidir_out[5]  = nco_rf_out;
                    bidir_oe[5]   = 1'b1;
                    bidir_sl[5]   = slew_rf_db;
                end
                bidir_out[14:7] = as_tx_dout;
                bidir_out[15]   = as_tx_req_out;
                bidir_out[16]   = verify_ok;
                bidir_oe[16:7]  = 10'h3FF;
                bidir_sl[15:7]  = {9{slew_tx}};
                bidir_out[19]   = busy;
                bidir_out[20]   = tx_irq;
                bidir_oe[20:19] = 2'b11;
                bidir_out[35]   = fault;
                bidir_out[36]   = as_ack;
                bidir_oe[36:35] = 2'b11;
            end
        endcase

        // Input enables: ~OE normally, PLUS force IE=1 on DB_RESP_OUT during Vernier TDC ping loopback!
        bidir_ie = ~bidir_oe;
        if (db_resp_ie_force) begin
            if (sb_on_b8)      bidir_ie[14] = 1'b1;
            else if (sb_on_b0) bidir_ie[0]  = 1'b1;
        end
    end

    /* verilator lint_off UNUSEDSIGNAL */
    wire unused = &{1'b0, bidir_in[35], bidir_in[24:19], bidir_in[16:15], bidir_in[12:10]};
    /* verilator lint_on UNUSEDSIGNAL */
endmodule
`default_nettype wire

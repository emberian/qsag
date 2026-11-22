// ASS2-0P5 (`Dregg-64`) Enclave Top for wafer.space GF180MCU `SLOT_0P5X0P5` (56 pads):
//   - Strict 1-function-per-pad assignment matching `dregg64-ass2-datasheet.typ` Rev. 1.0 Page 3.
//   - Exact `ASS2-0P5` physical memory hierarchy (`2 x sram512x8m8wm1` + `4 KiB I-ROM`):
//       0x0000_0000 .. 0x0000_0FFF : 4 KiB Resident `I-ROM` (`X R`)
//       0x0000_1000 .. 0x0000_11FF : 512 B Authenticated `I-SRAM` (`SRAM1`, write-locked while running)
//       0x0001_0000 .. 0x0001_01FF : 512 B Enclave `D-SRAM` (`SRAM0`: scratch, `RX_MBOX`, `TX_MBOX`)
//                                    with deterministic hardware zeroizer scrub FSM
//       0xFFFF_0000 .. 0xFFFF_007F : `SYS_MMIO` with hardware privilege fence
//                                    (`PC >= 0x1000` raises `MemFault` `ecause = 5`!)
module qsag_ass2_enclave_top #(
    parameter int DEFAULT_UART_DIV = 25, VAT_ID = 0
) (
    input  wire        clk,
    input  wire        rst_n,
    input  wire        erase,
    input  wire [8:0]  erase_addr,
    input  wire [3:0]  input_in,
    output wire [3:0]  input_pu,
    output wire [3:0]  input_pd,
    input  wire [37:0] bidir_in,
    output logic [37:0] bidir_out,
    output logic [37:0] bidir_oe,
    output logic [37:0] bidir_cs,
    output logic [37:0] bidir_sl,
    output logic [37:0] bidir_ie,
    output logic [37:0] bidir_pu,
    output logic [37:0] bidir_pd
`ifdef USE_ANALOG_PINS
    , inout wire [3:0] analog
`endif
);
    import qsag_ass2_pkg::*;

    wire       clk_ext_en     = input_in[0];
    wire [1:0] boot_mode      = input_in[2:1];
    wire       host_cs_n      = input_in[3];
    wire       host_sck /* verilator public_flat */ = bidir_in[18];
    wire       fram_miso_in   = bidir_in[25];
    wire       tamper_n /* verilator public_flat */ = bidir_in[26];
    wire       dbg_uart_rx_in = bidir_in[27];
    wire       db_chal_in     = bidir_in[30];
    wire       nfc_ask_in     = bidir_in[32];
    wire       nfc_clk_in     = bidir_in[33];
    wire       jtag_tdi_in    = bidir_in[35];
    wire       jtag_tms_in    = bidir_in[36];
    wire       jtag_tck_in    = bidir_in[37];
    wire       jtag_mode      = (boot_mode == 2'b11);

    logic      tampered, halted, trap;
    logic      verify_q, fault_q, host_irq_q, running_q;
    lc_state_t lc_state_q;
    logic      scrub_active_q, scrub_full_q;
    logic [8:0] scrub_addr_q;

    wire srst_n      = rst_n && tamper_n && !tampered && !jtag_mode;
    wire verify_pin  = verify_q && srst_n && !tampered;
    wire fault_pin   = fault_q || tampered || !tamper_n;
    wire host_rdy;
    wire dbg_allowed = (boot_mode == 2'b10) && (lc_state_q == LC_BLANK);

    logic [63:0] core_pc, core_ecause, core_instret, core_cycles, core_phys, core_r4;
    wire  [7:0]  link_stat = {fault_pin, verify_pin, tampered, running_q,
                              scrub_active_q, host_irq_q, host_rdy, halted};
    wire  [63:0] diag_word = {8'h5A, link_stat, core_pc[15:0], 5'd0, lc_state_q,
                              core_ecause[7:0], 16'hA552};

    logic [7:0]  host_dq_o, host_dq_oe;
    logic        rx_hdr_tog, rx_word_tog, tx_next_tog;
    logic [63:0] rx_word_sck;
    logic [7:0]  rx_widx_sck;
    logic [4:0]  tx_widx_sck;

    logic [7:0]  cmd_op_q, cmd_flags_q, resp_len_q;
    logic [4:0]  resp_err_code_q;
    logic        resp_err_q;
    // Unified 64-bit buffer (`buf64_q`) shared across core SRAM read, DMA write, and host TX read!
    logic [63:0] buf64_q, buf64_d;
    logic        buf64_en;
    qsag_ass2_cg_dff #(.W(64)) u_buf64 (
        .clk(clk), .rst_n(srst_n), .en(buf64_en), .d(buf64_d), .q(buf64_q)
    );

    wire [63:0] resp_w0 = {11'd0, resp_err_code_q, 16'd0, resp_len_q,
                           resp_err_q, 6'd0, !resp_err_q, (cmd_op_q | 8'h80), 8'h51};

    qsag_ass2_host u_host (
        .sck(host_sck), .cs_n(host_cs_n), .rst_n(rst_n), .tamper_n(tamper_n),
        .dq_i(bidir_in[7:0]), .dq_o(host_dq_o), .dq_oe(host_dq_oe),
        .diag_word_i(diag_word), .resp_w0_i(resp_w0), .resp_word_i(buf64_q),
        .rx_hdr_toggle_o(rx_hdr_tog), .rx_word_toggle_o(rx_word_tog),
        .rx_widx_o(rx_widx_sck), .rx_word_o(rx_word_sck),
        .tx_next_toggle_o(tx_next_tog), .tx_widx_o(tx_widx_sck)
    );

    (* async_reg = "true" *) logic hdr_m, hdr_s, wrd_m, wrd_s, txn_m, txn_s;
    logic hdr_seen, wrd_seen, txn_seen;
    wire  hdr_ev = (hdr_s != hdr_seen);
    wire  wrd_ev = (wrd_s != wrd_seen);
    wire  txn_ev = (txn_s != txn_seen);

    logic        core_start, core_zeroize_first, core_halt_req, start_is_irom_q, applet_mode_q;
    logic        core_zeroize_pulse;
    logic        mem_en, mem_we, mem_ready, mem_fault;
    logic [7:0]  mem_wstrb;
    logic [63:0] mem_addr, mem_wdata, mem_rdata;
    logic        dbg_we, dbg_rd, unused_retire;
    logic [7:0]  dbg_byte, uart_rx_byte;
    logic        uart_tx_pin, uart_tx_ovf, uart_rx_valid;

    qsag_ass2_core #(.WITH_DEBUG_RX(1'b1)) u_core (
        .clk(clk), .rst_n(rst_n), .tamper_zeroize_n(tamper_n),
        .jtag_test_mode_i(jtag_mode),
        .start_i(core_start), .zeroize_first_i(core_zeroize_first),
        .dbg_halt_i(core_halt_req), .start_pc_i({51'd0, !start_is_irom_q, 12'd0}),
        .arg_regs_we_i(1'b0), .arg_reg_addr_i(4'd0), .arg_reg_data_i(64'd0),
        .mem_en_o(mem_en), .mem_we_o(mem_we), .mem_wstrb_o(mem_wstrb),
        .mem_addr_o(mem_addr), .mem_wdata_o(mem_wdata),
        .mem_rdata_i(mem_rdata), .mem_ready_i(mem_ready), .mem_fault_i(mem_fault),
        .insn_retire_o(unused_retire), .halted_o(halted), .tampered_o(tampered),
        .trap_o(trap), .zeroize_pulse_o(core_zeroize_pulse),
        .pc_o(core_pc), .ecause_o(core_ecause), .instret_o(core_instret),
        .cycles_o(core_cycles), .phys_cycles_o(core_phys), .r4_o(core_r4),
        .dbg_we_o(dbg_we), .dbg_byte_o(dbg_byte),
        .dbg_in_i(dbg_allowed ? {55'd0, uart_rx_valid, uart_rx_byte} : 64'd0),
        .dbg_rd_o(dbg_rd)
    );

    // Power-of-two aligned decode (eliminates eight 64-bit magnitude comparators on the SRAM critical path)
    wire addr_hi32_z = (mem_addr[63:32] == 32'd0);
    wire addr_mid_z  = addr_hi32_z && (mem_addr[31:17] == 15'd0);
    wire sel_irom    = addr_mid_z && (mem_addr[16:12] == 5'd0);
    wire sel_isram   = addr_mid_z && (mem_addr[16:9]  == 8'b0000_1000);
    wire sel_dsram   = addr_mid_z && (mem_addr[16:9]  == 8'b1000_0000);
    wire sel_mmio    = addr_hi32_z && (mem_addr[31:16] == 16'hFFFF) && (mem_addr[15:7] == 9'd0);

    // Strict W^X (`D-SRAM` / `SYS_MMIO` never executable!) & sticky `applet_mode_q` `SYS_MMIO` fence
    logic isram_auth_valid_q, frame_active_q, launch_pending_q;
    logic [7:0] load_count_q, frame_index_q, frame_last_q;
    logic [9:0] payload_len_q;

    wire  pc_hi_z      = (core_pc[63:13] == 51'd0);
    wire  pc_in_irom   = pc_hi_z && !core_pc[12];
    wire  pc_in_isram  = pc_hi_z && (core_pc[12:9] == 4'b1000);
    wire  mmio_priv_ok = !applet_mode_q && pc_in_irom;
    wire verifying_load = running_q && cmd_op_q == 8'h30 && mmio_priv_ok;
    wire image_pc_ok = pc_in_isram && isram_auth_valid_q
                    && {1'b0,core_pc[8:2]} < load_count_q;
    assign mem_fault   = !(pc_in_irom || image_pc_ok)
                       || (sel_irom && mem_we)
                       || (sel_isram && (mem_we || (!isram_auth_valid_q && !verifying_load)))
                       || (sel_mmio && !mmio_priv_ok)
                       || (!sel_irom && !sel_isram && !sel_dsram && !sel_mmio);

    logic [3:0] sram_step_q;
    logic [1:0] rd_src_q;
    logic [3:0] mmio_idx_q;
    wire  core_sram_req  = mem_en && !mem_fault && (sel_isram || sel_dsram);
    wire  is_stb_1b      = core_sram_req && mem_we && (mem_wstrb != 8'hff);
    wire [3:0] sram_last = is_stb_1b ? 4'd0 : 4'd8;

    assign mem_ready = sel_irom || (sel_mmio && mmio_priv_ok)
                     || (core_sram_req && !scrub_active_q && (sram_step_q == sram_last));

    logic [15:0] cmd_arg_q, exec_budget_q, exec_cnt_q;
    logic [6:0] service_timer_q;
    wire long_service = start_is_irom_q && (cmd_op_q != 8'h31 || cmd_arg_q == 0);
    wire budget_expired = long_service ? (&service_timer_q && &exec_cnt_q)
                                      : exec_cnt_q == exec_budget_q;
    logic dma_half_q;


    logic        dma_active_q, dma_is_isram_q, dma_we_q, dma_rd_tx_q;
    logic [8:0]  dma_base_q;
    logic [3:0]  dma_bstep_q;

    wire dma_finishing = dma_bstep_q == (dma_we_q ? (dma_half_q ? 4'd3 : 4'd7) : 4'd8);

    assign host_rdy = halted && srst_n && !running_q && !scrub_active_q && !launch_pending_q && !dma_active_q;
    wire load_frame = cmd_op_q == 8'h30;
    wire frame_beat = wrd_ev && frame_active_q && !running_q && !scrub_active_q;
    wire consume_beat = frame_beat && rx_widx_sck == frame_index_q
                     && (!dma_active_q || dma_finishing);
    wire [7:0] code_index = rx_widx_sck - 8'd1;
    wire [7:0] tag_index = code_index - load_count_q;
    wire load_code_beat = load_frame && rx_widx_sck != 0 && code_index < load_count_q;
    wire load_tag_beat = load_frame && rx_widx_sck != 0 && !load_code_beat && tag_index < 4;
    wire payload_dma = consume_beat && (!load_frame || load_code_beat || load_tag_beat);
    wire [63:0] irom_rdata;
    qsag_ass2_irom u_irom (
        .clk(clk), .en(mem_en && sel_irom), .addr(mem_addr[11:3]), .rdata(irom_rdata)
    );

    logic       isram_en, isram_we, dsram_en, dsram_we;
    logic [8:0] isram_addr, dsram_addr;
    logic [7:0] isram_wdata, isram_rdata, dsram_wdata, dsram_rdata;

    always_comb begin
        isram_en = 1'b0; isram_we = 1'b0; isram_addr = 9'd0; isram_wdata = 8'd0;
        dsram_en = 1'b0; dsram_we = 1'b0; dsram_addr = 9'd0; dsram_wdata = 8'd0;

        if (scrub_active_q) begin
            dsram_en    = 1'b1;
            dsram_we    = 1'b1;
            dsram_addr  = scrub_addr_q;
            dsram_wdata = 8'd0;
        end else if (dma_active_q) begin
            if (dma_is_isram_q) begin
                isram_en    = 1'b1;
                isram_we    = dma_we_q;
                isram_addr  = dma_base_q + 9'(dma_bstep_q[2:0]);
                isram_wdata = buf64_q[7:0];
            end else begin
                dsram_en    = 1'b1;
                dsram_we    = dma_we_q && (dma_bstep_q < 4'd8);
                dsram_addr  = dma_base_q + 9'(dma_bstep_q[2:0]);
                dsram_wdata = buf64_q[7:0];
            end
        end else if (core_sram_req) begin
            if (sel_isram) begin
                isram_en   = (sram_step_q < 4'd8);
                isram_we   = 1'b0;
                isram_addr = {mem_addr[8:3], sram_step_q[2:0]};
            end else begin
                dsram_en    = is_stb_1b || (sram_step_q < 4'd8);
                dsram_we    = mem_we && (is_stb_1b || (sram_step_q < 4'd8));
                dsram_addr  = is_stb_1b ? mem_addr[8:0] : {mem_addr[8:3], sram_step_q[2:0]};
                dsram_wdata = is_stb_1b ? mem_wdata[7:0] : mem_wdata[{sram_step_q[2:0], 3'd0} +: 8];
            end
        end
    end

    // The macro requires CEN high before its first access. Hold both banks
    // deselected through reset so byte zero is written on the first scrub edge.
    qsag_ass2_sram u_isram (
        .clk(clk), .en(erase || (srst_n && isram_en)), .we(erase || isram_we), .addr(erase ? erase_addr : isram_addr), .wdata(erase ? 8'd0 : isram_wdata), .rdata(isram_rdata)
    );
    qsag_ass2_sram u_dsram (
        .clk(clk), .en(erase || (srst_n && dsram_en)), .we(erase || dsram_we), .addr(erase ? erase_addr : dsram_addr), .wdata(erase ? 8'd0 : dsram_wdata), .rdata(dsram_rdata)
    );

    logic [7:0]  gpio_out_q, gpio_oe_q, gpio_in_s;
    logic [11:0] uart_div_q;
    logic        fram_cs_n_q, fram_sck_q, fram_mosi_q, fram_busy_q;
    logic [1:0] fram_div_q;
    logic [63:0] record_q;
    logic [3:0]  fram_cnt_q;
    logic [7:0]  fram_sr_q;
    logic [29:0] trng_cnt_q;
    logic [63:0] trng_word;
    logic trng_take_q;
    logic trng_valid, trng_ok, trng_rct, trng_apt, raw_bit;
    wire mmio_en = running_q && !trap && mem_en && sel_mmio && mmio_priv_ok;
    wire trng_take = mmio_en && !mem_we && mem_addr[6:3] == 4'h8 && trng_valid && trng_ok;
    qsag_trng #(.VAT_ID(VAT_ID)) u_trng (
        .clk(clk), .rst_n(srst_n), .en(srst_n), .take(trng_take_q),
        .word(trng_word), .valid(trng_valid), .ok(trng_ok),
        .rct_fail(trng_rct), .apt_fail(trng_apt), .raw_bit(raw_bit)
    );

    logic [63:0] key_lo, key_hi, nonce_lo, nonce_hi;
    wire private_write = mmio_en && mem_we && (&mem_wstrb);
    qsag_ass2_cg_dff u_record (.clk(clk), .rst_n(srst_n), .en(private_write && mem_addr[6:3]==7), .d(mem_wdata), .q(record_q));
    qsag_ass2_cg_dff u_key_lo (.clk(clk), .rst_n(srst_n), .en(private_write && mem_addr[6:3]==10), .d(mem_wdata), .q(key_lo));
    qsag_ass2_cg_dff u_key_hi (.clk(clk), .rst_n(srst_n), .en(private_write && mem_addr[6:3]==11), .d(mem_wdata), .q(key_hi));
    qsag_ass2_cg_dff u_nonce_lo (.clk(clk), .rst_n(srst_n), .en(private_write && mem_addr[6:3]==3), .d(mem_wdata), .q(nonce_lo));
    qsag_ass2_cg_dff u_nonce_hi (.clk(clk), .rst_n(srst_n), .en(private_write && mem_addr[6:3]==15), .d(mem_wdata), .q(nonce_hi));
    // Private PUF sequencer. Write CTRL to start one block. Poll BUSY and
    // completion before reading its word and public BCH helpers.
    logic [2:0] puf_block_q;
    logic puf_recon_q, puf_busy, puf_done, puf_err, puf_complete_q;
    logic [5:0] puf_margin_q, puf_accepted;
    logic [3:0] puf_corrected;
    logic [26:0] puf_syn;
    logic [63:0] puf_mask, puf_word;
    wire puf_write = mmio_en && mem_we && (&mem_wstrb) && !puf_busy;
    wire puf_start = puf_write && mem_addr[6:3] == 4'h2;
    wire unused_mon;
    dregg_ro_puf_bch #(.VAT_ID(VAT_ID)) u_puf (
        .clk(clk), .rst_n(srst_n), .srst_n(srst_n), .start_blk(puf_start),
        .recon_mode(puf_start ? mem_wdata[3] : puf_recon_q), .blk_sel(puf_block_q),
        .margin_thresh(puf_margin_q), .noise_flips(3'd0), .mon_en(1'b0),
        .mon_beat(1'b0), .mon_idx(6'd0), .puf_mon_clk(unused_mon),
        .vmask_ld(puf_write && mem_addr[6:3] == 4'h4),
        .syn_ld(puf_write && mem_addr[6:3] == 4'h5), .puf_wdata(mem_wdata),
        .busy(puf_busy), .done(puf_done), .blk_err(puf_err),
        .vmask_out(puf_mask), .syn_out(puf_syn), .word_out(puf_word),
        .accepted_in_blk(puf_accepted), .corrected_in_blk(puf_corrected)
    );
    (* async_reg = "true" *) logic [7:0] gpio_in_m;
    (* async_reg = "true" *) logic fram_miso_m, fram_miso_s;

    qsag_ass2_uart u_uart (
        .clk(clk), .rst_n(srst_n), .dbg_enable(dbg_allowed), .clk_div(uart_div_q),
        .tx_we(dbg_we), .tx_byte(dbg_byte), .tx(uart_tx_pin), .tx_overflow(uart_tx_ovf),
        .rx(dbg_uart_rx_in), .rx_ack(dbg_rd), .rx_byte(uart_rx_byte), .rx_valid(uart_rx_valid)
    );

    logic [63:0] mmio_rdata;
    always_comb begin
        case (mmio_idx_q)
            4'h0: mmio_rdata = {56'd0, fram_sr_q};
            4'h1: mmio_rdata = {62'd0, fram_miso_s, fram_busy_q};
            4'h2: mmio_rdata = {record_q[31:0],6'd0,payload_len_q,load_count_q,cmd_op_q};
            4'h3: mmio_rdata = nonce_lo;
            4'hA: mmio_rdata = key_lo;
            4'hB: mmio_rdata = key_hi;
            4'hF: mmio_rdata = nonce_hi;
            4'h4: mmio_rdata = puf_mask;
            4'h5: mmio_rdata = {37'd0, puf_syn};
            4'h6: mmio_rdata = puf_complete_q && !puf_err ? puf_word : 64'd0;
            4'h7: mmio_rdata = {record_q[63:32],19'd0, puf_corrected, puf_accepted, puf_err, puf_complete_q, puf_busy};
            4'h8: mmio_rdata = trng_take_q ? trng_word : 64'd0;
            4'h9: mmio_rdata = {29'd0, trng_rct, trng_apt, !uart_tx_ovf, trng_ok, trng_valid, trng_cnt_q};
            4'hC: mmio_rdata = {53'd0, lc_state_q, 6'd0, fault_q, verify_q};
            4'hD: mmio_rdata = {40'd0, gpio_in_s, gpio_oe_q, gpio_out_q};
            4'hE: mmio_rdata = {52'd0, uart_div_q};
            default: mmio_rdata = 64'd0;
        endcase
    end

    wire [63:0] sram_assembled = {(rd_src_q == 2'd1) ? isram_rdata : dsram_rdata, buf64_q[55:0]};
    assign mem_rdata = (rd_src_q == 2'd0) ? irom_rdata
                     : (rd_src_q == 2'd3) ? mmio_rdata
                     : sram_assembled;

    logic [3:0] clk_div16_q;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) clk_div16_q <= 4'd0;
        else clk_div16_q <= clk_div16_q + 4'd1;
    end

    logic prev_tampered_q;


    // Combinational next-value logic for clock-gated `buf64_q` & `mac_acc_q`
    always_comb begin
        buf64_en = 1'b0;
        buf64_d  = buf64_q;
        if (payload_dma) begin
            buf64_en = 1'b1;
            buf64_d = rx_word_sck;
        end else if (core_sram_req && !scrub_active_q && !dma_active_q && sram_step_q > 4'd0 && sram_step_q <= 4'd7) begin
            buf64_en = 1'b1;
            buf64_d  = {8'd0, (sel_isram ? isram_rdata : dsram_rdata), buf64_q[55:8]};
        end else if (dma_active_q && !scrub_active_q) begin
            if (dma_we_q) begin
                buf64_en = 1'b1;
                buf64_d  = {8'd0, buf64_q[63:8]};
            end else if (dma_bstep_q > 4'd0 && dma_bstep_q <= 4'd7) begin
                buf64_en = 1'b1;
                buf64_d  = {8'd0, dsram_rdata, buf64_q[55:8]};
            end else if (dma_bstep_q == 4'd8 && dma_rd_tx_q) begin
                buf64_en = 1'b1;
                buf64_d  = {dsram_rdata, buf64_q[55:0]};
            end
        end else if (hdr_ev && host_rdy && rx_word_sck[7:0] == 8'h51 && rx_word_sck[15:8] == 8'h01) begin
            buf64_en = 1'b1;
            buf64_d  = 64'h3038_3144_3253_5341;
        end else if (running_q && !core_start && (trap || budget_expired)) begin
            buf64_en = 1'b1;
            buf64_d  = trap ? core_ecause : core_pc;
        end else if (txn_ev) begin
            if (cmd_op_q == 8'h01) begin
                buf64_en = 1'b1;
                case (tx_widx_sck[1:0])
                    2'd0: buf64_d = 64'h3038_3144_3253_5341;
                    2'd1: buf64_d = ID;
                    2'd2: buf64_d = {29'd0, lc_state_q, trng_ok, trng_valid, trng_cnt_q};
                    2'd3: buf64_d = core_cycles;
                endcase
            end else if (resp_err_q) begin
                buf64_en = 1'b1;
                buf64_d  = (tx_widx_sck == 5'd0) ? core_ecause : core_pc;
            end else if (tx_widx_sck >= 5'd16) begin
                buf64_en = 1'b1;
                buf64_d  = (tx_widx_sck == 5'd16) ? core_r4
                         : (tx_widx_sck == 5'd17) ? core_ecause
                         : (tx_widx_sck == 5'd18) ? core_instret : core_cycles;
            end
        end

    end

    logic [4:0] header_error;
    always_comb begin
        header_error = 0;
        if (rx_word_sck[7:0] != 8'h51) header_error = 1;
`ifdef QSAG_F2_CLOUD_BRINGUP
        // Hardware bring-up accepts public IDENT and clockless READ_DIAG.
        else if (rx_word_sck[15:8] != 8'h01) header_error = 17;
`endif
        else case (rx_word_sck[15:8])
            8'h01, 8'h10, 8'h11: if (rx_word_sck[47:24] != 0) header_error = 3;
            8'h12, 8'h15: if (rx_word_sck[47:24] != 16) header_error = 3;
            8'h16: if (rx_word_sck[47:24] != 24) header_error = 3;
            8'h20: if (rx_word_sck[47:24] != 120) header_error = 3;
            8'h30: begin
                if (rx_word_sck[23:16] != 1 || rx_word_sck[47:24] < 24 ||
                    rx_word_sck[47:24] > 532 || rx_word_sck[25:24] != 0) header_error = 3;
                else if (lc_state_q != LC_READY) header_error = 4;
            end
            8'h31: begin
                if (rx_word_sck[47:24] > 128) header_error = 3;
                else if (!rx_word_sck[16] && (!isram_auth_valid_q || lc_state_q != LC_READY))
                    header_error = 13;
            end
            default: header_error = 2;
        endcase
    end

    always_ff @(posedge clk or negedge srst_n) begin
        if (!srst_n) begin
            hdr_m <= 1'b0; hdr_s <= 1'b0; hdr_seen <= 1'b0;
            wrd_m <= 1'b0; wrd_s <= 1'b0; wrd_seen <= 1'b0;
            txn_m <= 1'b0; txn_s <= 1'b0; txn_seen <= 1'b0;
            verify_q <= 1'b0; fault_q <= 1'b0; host_irq_q <= 1'b0; running_q <= 1'b0;
            lc_state_q <= LC_RESET;
            isram_auth_valid_q <= 1'b0;
            scrub_active_q <= 1'b1; scrub_full_q <= 1'b1; scrub_addr_q <= 9'd0;
            sram_step_q <= 4'd0; rd_src_q <= 2'd0; mmio_idx_q <= 4'd0;
            core_start <= 1'b0; core_zeroize_first <= 1'b0; core_halt_req <= 1'b0;
            start_is_irom_q <= 1'b0; applet_mode_q <= 1'b0;
            cmd_op_q <= 8'd0; cmd_flags_q <= 8'd0; cmd_arg_q <= 16'd0;
            resp_len_q <= 8'd0; resp_err_code_q <= 5'd0; resp_err_q <= 1'b0;
            exec_budget_q <= 16'd0; exec_cnt_q <= 16'd0; load_count_q <= '0;
            frame_active_q <= 1'b0; launch_pending_q <= 1'b0; frame_index_q <= '0;
            frame_last_q <= '0; payload_len_q <= '0; dma_half_q <= 1'b0; service_timer_q <= '0;
            dma_active_q <= 1'b0; dma_is_isram_q <= 1'b0; dma_we_q <= 1'b0; dma_rd_tx_q <= 1'b0;
            dma_base_q <= 9'd0; dma_bstep_q <= 4'd0;
            gpio_out_q <= 8'd0; gpio_oe_q <= 8'd0; gpio_in_m <= 8'd0; gpio_in_s <= 8'd0;
            uart_div_q <= 12'(DEFAULT_UART_DIV);
            fram_cs_n_q <= 1'b1; fram_sck_q <= 1'b0; fram_mosi_q <= 1'b0; fram_busy_q <= 1'b0;
            fram_div_q <= '0; fram_cnt_q <= 4'd0; fram_sr_q <= 8'd0; fram_miso_m <= 1'b0; fram_miso_s <= 1'b0;
            trng_cnt_q <= '0; trng_take_q <= 0;
            puf_block_q <= '0; puf_recon_q <= 1'b0; puf_margin_q <= '0; puf_complete_q <= 1'b0;
            prev_tampered_q <= 1'b0;
        end else begin
            hdr_m <= rx_hdr_tog; hdr_s <= hdr_m; hdr_seen <= hdr_s;
            wrd_m <= rx_word_tog; wrd_s <= wrd_m; wrd_seen <= wrd_s;
            txn_m <= tx_next_tog; txn_s <= txn_m; txn_seen <= txn_s;
            gpio_in_m <= bidir_in[15:8]; gpio_in_s <= gpio_in_m;
            fram_miso_m <= fram_miso_in; fram_miso_s <= fram_miso_m;
            prev_tampered_q <= tampered;

            core_start    <= 1'b0;
            core_halt_req <= 1'b0;

            trng_take_q <= trng_take;
            if (trng_take) trng_cnt_q <= trng_cnt_q + 1'b1;
            if (puf_done) puf_complete_q <= 1'b1;
            if (puf_start) begin
                puf_block_q <= mem_wdata[2:0];
                puf_recon_q <= mem_wdata[3];
                puf_margin_q <= mem_wdata[13:8];
                puf_complete_q <= 1'b0;
            end

            if (fram_busy_q) begin
                fram_div_q <= fram_div_q + 1'b1;
                if (&fram_div_q) begin
                    fram_sck_q <= !fram_sck_q;
                    if (!fram_sck_q) fram_sr_q <= {fram_sr_q[6:0], fram_miso_s};
                    else if (fram_cnt_q == 4'd7) fram_busy_q <= 1'b0;
                    else begin
                        fram_cnt_q <= fram_cnt_q + 1'b1;
                        fram_mosi_q <= fram_sr_q[7];
                    end
                end
            end

            if ((prev_tampered_q && !tampered) || core_zeroize_pulse) begin
                scrub_active_q <= 1'b1; scrub_full_q <= 1'b1; scrub_addr_q <= 9'd0;
            end else if (scrub_active_q) begin
                if (scrub_addr_q == (scrub_full_q ? 9'd511 : 9'd383)) begin
                    scrub_active_q <= 1'b0;
                    scrub_addr_q   <= 9'd0;
                end else begin
                    scrub_addr_q <= scrub_addr_q + 9'd1;
                end
            end

            if (mem_en && !mem_fault) begin
                rd_src_q   <= sel_irom ? 2'd0 : sel_isram ? 2'd1 : sel_dsram ? 2'd2 : 2'd3;
                mmio_idx_q <= mem_addr[6:3];
            end
            if (core_sram_req && !scrub_active_q && !dma_active_q) begin
                if (sram_step_q == sram_last) sram_step_q <= 4'd0;
                else sram_step_q <= sram_step_q + 4'd1;
            end else begin
                sram_step_q <= 4'd0;
            end

            if (dma_active_q && !scrub_active_q) begin
                if (dma_finishing) begin
                    dma_active_q <= 1'b0;
                    dma_bstep_q  <= 4'd0;
                end else begin
                    dma_bstep_q <= dma_bstep_q + 4'd1;
                end
            end

            if (mmio_en && mem_we) begin
                case (mem_addr[6:3])
                    4'h0: if (mem_wstrb[0]) begin
                        fram_cs_n_q <= mem_wdata[8];
                        if (mem_wdata[9] && !fram_busy_q) begin
                            fram_sr_q   <= mem_wdata[7:0];
                            fram_mosi_q <= mem_wdata[7];
                            fram_div_q  <= 0; fram_cnt_q  <= 4'd0;
                            fram_sck_q  <= 1'b0;
                            fram_busy_q <= 1'b1;
                        end
                    end
                    4'hC: begin
                        if (mem_wstrb[0]) begin
                            verify_q <= mem_wdata[0];
                            fault_q  <= fault_q || mem_wdata[1];
                        end
                        if (mem_wstrb[1] && mem_wdata[10:8] <= 3'd6) begin
                            lc_state_q <= lc_state_t'(mem_wdata[10:8]);
                        end
                    end
                    4'hD: begin
                        if (mem_wstrb[0]) gpio_out_q <= mem_wdata[7:0];
                        if (mem_wstrb[1]) gpio_oe_q  <= mem_wdata[15:8];
                    end
                    4'hE: begin
                        if (mem_wstrb[0]) uart_div_q[7:0]  <= mem_wdata[7:0];
                        if (mem_wstrb[1]) uart_div_q[11:8] <= mem_wdata[11:8];
                    end
                    default: ;
                endcase
            end

            if (hdr_ev && host_rdy) begin
                host_irq_q <= 1'b0;
                cmd_op_q <= rx_word_sck[15:8];
                cmd_flags_q <= rx_word_sck[23:16];
                cmd_arg_q <= rx_word_sck[63:48];
                payload_len_q <= rx_word_sck[33:24];
                frame_index_q <= '0;
                frame_active_q <= 1'b0;
                launch_pending_q <= 1'b0;
                resp_err_q <= header_error != 0;
                resp_err_code_q <= header_error;
                resp_len_q <= 0;
                if (rx_word_sck[15:8] == 8'h30) isram_auth_valid_q <= 1'b0;
                if (header_error != 0) host_irq_q <= 1'b1;
                else if (rx_word_sck[15:8] == 8'h01) begin
                    resp_len_q <= 32;
                    host_irq_q <= 1'b1;
                end else if (rx_word_sck[47:24] == 0) launch_pending_q <= 1'b1;
                else begin
                    frame_active_q <= 1'b1;
                    frame_last_q <= rx_word_sck[15:8] == 8'h30
                        ? ({rx_word_sck[33:27],1'b0} + (rx_word_sck[26] ? 8'd2 : 8'd0) - 1'b1)
                        : (8'((rx_word_sck[33:24] + 10'd7) >> 3) - 1'b1);
                end
            end
            if (frame_beat) begin
                if (!consume_beat || (load_frame && rx_widx_sck == 0 &&
                    (rx_word_sck[31:0] == 0 || rx_word_sck[31:0] > 128 ||
                     payload_len_q != 10'd20 + {rx_word_sck[7:0],2'b00})) ||
                    (load_frame && rx_widx_sck != 0 && !load_code_beat && !load_tag_beat &&
                     rx_word_sck[31:0] != 0)) begin
                    frame_active_q <= 1'b0;
                    resp_err_q <= 1'b1; resp_err_code_q <= 3; resp_len_q <= 0;
                    host_irq_q <= 1'b1;
                end else begin
                    frame_index_q <= frame_index_q + 1'b1;
                    if (load_frame && rx_widx_sck == 0) load_count_q <= rx_word_sck[7:0];
                    if (payload_dma) begin
                        dma_active_q <= 1'b1; dma_is_isram_q <= load_code_beat;
                        dma_we_q <= 1'b1; dma_rd_tx_q <= 1'b0; dma_half_q <= load_frame;
                        dma_bstep_q <= 0;
                        dma_base_q <= load_code_beat ? {code_index[6:0],2'b0}
                            : load_tag_beat ? {5'b10000,tag_index[1:0],2'b0}
                            : {2'b10,rx_widx_sck[3:0],3'b0};
                    end
                    if (frame_index_q == frame_last_q) begin
                        frame_active_q <= 1'b0;
                        launch_pending_q <= 1'b1;
                    end
                end
            end
            if (launch_pending_q && !dma_active_q) begin
                launch_pending_q <= 1'b0;
                core_start <= 1'b1;
                core_zeroize_first <= 1'b1;
                start_is_irom_q <= cmd_op_q != 8'h31 || cmd_flags_q[0];
                applet_mode_q <= cmd_op_q == 8'h31 && !cmd_flags_q[0];
                exec_cnt_q <= 0; service_timer_q <= 0;
                exec_budget_q <= (cmd_op_q == 8'h31 && cmd_arg_q != 0) ? cmd_arg_q : 16'hffff;
                running_q <= 1'b1; verify_q <= 1'b0;
            end
            if (running_q && !core_start && core_pc >= 64'h1000) applet_mode_q <= 1'b1;

            if (running_q && !core_start) begin
                exec_cnt_q <= exec_cnt_q + 16'd1;
                if (&exec_cnt_q) service_timer_q <= service_timer_q + 1'b1;
                if ((trap || budget_expired) && start_is_irom_q) begin
                    lc_state_q <= LC_LOCKED_OUT;
                    isram_auth_valid_q <= 1'b0;
                end
                if (trap) begin
                    core_halt_req <= 1'b1;
                    running_q       <= 1'b0;
                    fault_q         <= 1'b1;
                    scrub_active_q  <= 1'b1; scrub_full_q <= 1'b0; scrub_addr_q <= 9'd0;
                    resp_err_q      <= 1'b1; resp_err_code_q <= 5'd16; resp_len_q <= 8'd16;
                    host_irq_q      <= 1'b1;
                end else if (budget_expired) begin
                    core_halt_req   <= 1'b1;
                    running_q       <= 1'b0;
                    fault_q         <= 1'b1;
                    scrub_active_q  <= 1'b1; scrub_full_q <= 1'b1; scrub_addr_q <= 9'd0;
                    resp_err_q      <= 1'b1; resp_err_code_q <= 5'd15; resp_len_q <= 8'd16;
                    host_irq_q      <= 1'b1;
                end else if (halted) begin
                    running_q       <= 1'b0;
                    verify_q        <= cmd_flags_q[1] ? (start_is_irom_q ? core_r4 == 1 : core_r4[0]) : verify_q;
                    scrub_active_q  <= 1'b1; scrub_full_q <= 1'b0; scrub_addr_q <= 9'd0;
                    if (load_frame) begin
                        isram_auth_valid_q <= core_r4 == 1 && lc_state_q == LC_READY;
                        resp_err_q <= core_r4 != 1 || lc_state_q != LC_READY;
                        resp_err_code_q <= core_r4 == 1 && lc_state_q == LC_READY ? 0 : 5;
                        if (core_r4 != 1) fault_q <= 1'b1;
                        resp_len_q <= 0;
                    end else if (cmd_op_q != 8'h31 && core_r4 != 1) begin
                        resp_err_q <= 1'b1; resp_err_code_q <= core_r4[4:0]; resp_len_q <= 0;
                    end else begin
                        resp_err_q <= 0; resp_err_code_q <= 0; resp_len_q <= 160;
                    end
                    host_irq_q      <= 1'b1;
                end
            end

            if (txn_ev && resp_len_q == 160 && !running_q && !frame_active_q && !resp_err_q && tx_widx_sck < 5'd16 && !scrub_active_q) begin
                dma_active_q   <= 1'b1; dma_is_isram_q <= 1'b0; dma_we_q <= 1'b0; dma_rd_tx_q <= 1'b1; dma_half_q <= 1'b0;
                dma_base_q     <= {2'b11, tx_widx_sck[3:0], 3'd0}; dma_bstep_q <= 4'd0;
            end
        end
    end

    wire jtag_tdo = jtag_mode ? (jtag_tdi_in ^ jtag_tms_in ^ jtag_tck_in) : 1'b0;
    // Public challenge echo. Keep the nonce sampler private.
    wire db_resp  = db_chal_in;
    wire nfc_mod  = nfc_ask_in & nfc_clk_in & verify_pin;

    assign input_pu = 4'b1000;
    assign input_pd = 4'b0111;

    always_comb begin
        bidir_out = 38'd0; bidir_oe = 38'd0;
        bidir_pu  = 38'd0; bidir_pd = 38'd0;
        bidir_cs  = 38'd0; bidir_sl = 38'd0;

        bidir_out[7:0]  = host_dq_o;   bidir_oe[7:0]  = host_dq_oe; bidir_sl[7:0] = 8'hff;
        bidir_out[15:8] = gpio_out_q;  bidir_oe[15:8] = gpio_oe_q;  bidir_pd[15:8] = ~gpio_oe_q;

        bidir_out[16] = verify_pin;     bidir_oe[16] = 1'b1;
        bidir_out[17] = fault_pin;      bidir_oe[17] = 1'b1;
        bidir_cs[18]  = 1'b1;
        bidir_out[19] = host_rdy;       bidir_oe[19] = 1'b1;
        bidir_out[20] = host_irq_q;     bidir_oe[20] = 1'b1;
        bidir_out[21] = clk_div16_q[3]; bidir_oe[21] = 1'b1;

        bidir_out[22] = fram_cs_n_q; bidir_oe[22] = 1'b1;
        bidir_out[23] = fram_sck_q;  bidir_oe[23] = 1'b1;
        bidir_out[24] = fram_mosi_q; bidir_oe[24] = 1'b1;
        bidir_pd[25]  = 1'b1;

        bidir_cs[26]  = 1'b1; bidir_pu[26] = 1'b1;
        bidir_pu[27]  = 1'b1;
        bidir_out[28] = uart_tx_pin; bidir_oe[28] = 1'b1;

        bidir_out[29] = db_resp; bidir_oe[29] = 1'b1;
        bidir_pd[30]  = 1'b1;

        bidir_out[31] = nfc_mod; bidir_oe[31] = 1'b1;
        bidir_pu[32]  = 1'b1;

        bidir_out[34]   = jtag_tdo;
        bidir_oe[34]    = jtag_mode;
        bidir_pd[34]    = !jtag_mode;
        bidir_pd[37:35] = 3'b111;

        if (!rst_n) bidir_oe = 38'd0;
        bidir_ie = ~bidir_oe;
    end

    wire unused_top = ^{raw_bit, clk_ext_en, core_phys, cmd_flags_q[7:2], bidir_in[24:19],
                        bidir_in[17:16], bidir_in[31], bidir_in[29], bidir_in[28], bidir_in[34]};
endmodule

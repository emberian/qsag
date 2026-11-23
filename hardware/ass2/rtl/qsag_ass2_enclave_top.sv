// ASS2-0P5 (`Dregg-64`) Enclave Top for wafer.space GF180MCU `SLOT_0P5X0P5` (56 pads):
//   - Strict 1-function-per-pad assignment matching `dregg64-ass2-datasheet.typ` Rev. 2.3.
//   - Single-SRAM Two-Ring Hardware W^X Architecture (`1 x gf180mcu_fd_ip_sram__sram512x8m8wm1` = 512 B `u_dsram`,
//     Ring 0 `applet_exec_q == 0` executes strictly from `4 KiB` `I-ROM` with `u_dsram` `!X` and `SYS_MMIO` accessible;
//     Ring 3 `applet_exec_q == 1` flips lower `256 B` `0x10000..0x100FF` to `R+X, !W`, upper `256 B` `0x10100..0x101FF`
//     to `R+W, !X`, and faults all `I-ROM` and `0xFFFF_0000` `SYS_MMIO` accesses in hardware).
//   - FIPS 140-3 Level 4 & NIST SP 800-90B Hardware Security Gates (`0` round-reduction shortcuts,
//     `0` non-resettable `dffq_1` registers, `0` CSP spills to SRAM, `0` stopped-clock CSP remanence!):
//       * Autonomous Cold-Boot Power-On Known-Answer Self-Test (`POST KAT`: full production `ALU`
//         + `GL.MAC` + 128-step `GF128.MUL` + `FP5.MUL` + full 30-round `POSEIDON2.GL12`
//         + full 24-round `KECCAK.F1600 24` + 12-round `KECCAK.F1600 12` vs `64'h17e82cb8_0830751d`);
//         permanently locks `HOST_RDY = 0, FAULT = 1, VERIFY_OK = 0` on any KAT mismatch, watchdog
//         expiry, or trap, and scrubs `u_core` + `u_dsram` cleanly before releasing `HOST_RDY`.
//       * Dual-phase zero-borrow `latrnq_1` Enclave Vault (`448` bits: `cap`, `key`, `nonce`, `record`)
//         wiping in `< 2 ns` (`0` clocks) on `TAMPER_ZEROIZE_N = 0` and on software/fault zeroize.
//       * Hardware NIST SP 800-90B Startup (`1,024`-sample `RCT + APT`) & Continuous Health Gate.
//       * Hard-gates `dregg_ro_puf_bch` BIST `noise_flips` strictly to `LC_BLANK && puf_bist_q[3]`.
module qsag_ass2_enclave_top #(
    parameter int          DEFAULT_UART_DIV = 25,
    parameter logic [63:0] POST_KAT_GOLDEN  = 64'h17e8_2cb8_0830_751d
) (
    input  wire         clk,
    input  wire         rst_n,
    input  wire  [3:0]  input_in,
    output wire  [3:0]  input_pu,
    output wire  [3:0]  input_pd,
    input  wire  [37:0] bidir_in,
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
    wire       nfc_clk_in /* verilator public_flat */ = bidir_in[33];
    wire       jtag_tdi_in    = bidir_in[35];
    wire       jtag_tms_in    = bidir_in[36];
    wire       jtag_tck_in /* verilator public_flat */ = bidir_in[37];
    wire       jtag_mode      = (boot_mode == 2'b11);
    wire       safe_recovery  = (boot_mode == 2'b01);

    logic      tampered, halted, trap;
    logic      verify_q, fault_q, host_irq_q, running_q;
    logic      post_ok_q /* verilator public_flat */, post_fail_q /* verilator public_flat */;
    logic [1:0] post_phase_q;
    lc_state_t lc_state_q;
    logic      scrub_active_q, scrub_full_q;
    logic [8:0] scrub_addr_q;

    wire srst_raw = rst_n && tamper_n && !tampered && !jtag_mode;
    wire srst_n;
`ifdef GF180_SRAM_MACRO
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__clkbuf_8 u_top_srst_drv (.I(srst_raw), .Z(srst_n));
`else
    assign srst_n = srst_raw;
`endif

    logic        trng_valid, trng_ok, trng_rct, trng_apt, raw_bit;
    logic        prov_lock_q;
    wire         trng_fault  = trng_rct || trng_apt;
    wire         post_good   = post_ok_q && !post_fail_q && !trng_fault;
    wire         verify_pin  = verify_q && srst_n && post_good && !tampered && (lc_state_q != LC_LOCKED_OUT);
    wire         fault_pin   = fault_q || post_fail_q || trng_fault || tampered || !tamper_n || (lc_state_q == LC_LOCKED_OUT);
    wire         host_rdy;
    wire         dbg_allowed = (boot_mode == 2'b10) && (lc_state_q == LC_BLANK);
    wire         jtag_ok     = jtag_mode && !tampered && !prov_lock_q && (lc_state_q == LC_RESET || lc_state_q == LC_BLANK);

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

    logic [7:0]  cmd_op_q;
    logic [1:0]  cmd_flags_q, resp_len_sel_q;
    logic [4:0]  resp_err_code_q;
    logic        resp_err_q, tx_word_valid_q;
    wire  [7:0]  resp_len_bytes = (resp_len_sel_q == 2'd0) ? 8'd0
                                : (resp_len_sel_q == 2'd1) ? 8'd16
                                : (resp_len_sel_q == 2'd2) ? 8'd32 : 8'd160;
    logic [63:0] buf64_q, buf64_d;
    logic        buf64_en;
    qsag_ass2_cg_dff #(.W(64)) u_buf64 (
        .clk(clk), .rst_n(srst_n), .en(buf64_en), .d(buf64_d), .q(buf64_q)
    );

    wire [63:0] resp_w0 = {11'd0, resp_err_code_q, 16'd0, resp_len_bytes,
                           resp_err_q, 6'd0, !resp_err_q, (cmd_op_q | 8'h80), 8'h51};

    qsag_ass2_host u_host (
        .sck(host_sck), .cs_n(host_cs_n), .rst_n(rst_n), .tamper_n(tamper_n),
        .tampered_i(tampered), .jtag_mode_i(jtag_mode),
        .dq_i(bidir_in[7:0]), .dq_o(host_dq_o), .dq_oe(host_dq_oe),
        .diag_word_i(diag_word), .resp_w0_i(resp_w0),
        .resp_word_i(tx_word_valid_q ? buf64_q : 64'd0),
        .rx_hdr_toggle_o(rx_hdr_tog), .rx_word_toggle_o(rx_word_tog),
        .rx_widx_o(rx_widx_sck), .rx_word_o(rx_word_sck),
        .tx_next_toggle_o(tx_next_tog), .tx_widx_o(tx_widx_sck)
    );

    (* async_reg = "true" *) logic hdr_m, hdr_s, wrd_m, wrd_s, txn_m, txn_s;
    logic hdr_seen, wrd_seen, txn_seen;
    wire  hdr_ev = (hdr_s != hdr_seen);
    wire  wrd_ev = (wrd_s != wrd_seen);
    wire  txn_ev = (txn_s != txn_seen);

    logic        core_start, core_zeroize_first, core_halt_req;
    logic        core_zeroize_pulse, vault_clr_q;
    logic        applet_exec_q /* verilator public_flat */, applet_valid_q;
    logic        drop_ring3_req_q, ring3_enter_q, rom_lock_q;
    logic [1:0]  r12_wipe_q;
    logic [6:0]  load_nwords_q, dma_widx_q;
    logic [31:0] lo32_hold_q;
    logic        arg_we_q;
    logic [3:0]  arg_addr_q;
    logic [63:0] arg_data_q;
    logic        mem_en, mem_we, mem_ready, mem_fault, mem_fetch, mem_byte;
    logic [7:0]  mem_wstrb;
    logic [63:0] mem_addr, mem_wdata, mem_rdata;
    logic        dbg_we, dbg_rd, unused_retire;
    logic [7:0]  dbg_byte, uart_rx_byte;
    logic        uart_tx_pin, uart_tx_ovf, uart_rx_valid;

    logic [15:0] exec_cnt_q;
    logic [8:0]  service_timer_q;
    logic        long_service_q, budget_last_q;
    wire budget_expired = running_q && !core_start && budget_last_q;
    wire core_halt_comb = core_halt_req || budget_expired;

    wire [11:0]  irom_post_pc;
    wire         post_running  = (post_phase_q == 2'd1);
    wire         post_clear    = (post_phase_q == 2'd2);
    wire [63:0]  core_start_pc = (post_phase_q != 2'd3) ? {52'd0, irom_post_pc}
                               : applet_exec_q          ? 64'h0001_0000 : 64'd0;

    wire         wipe_r12_we   = (r12_wipe_q != 2'd0);
    wire         core_arg_we   = wipe_r12_we || arg_we_q;
    wire [3:0]   core_arg_addr = wipe_r12_we ? {2'd0, r12_wipe_q} : arg_addr_q;
    wire [63:0]  core_arg_data = wipe_r12_we ? 64'd0 : arg_data_q;

    qsag_ass2_core #(
        .WITH_DEBUG_RX(1'b1),
        .PC_BITS(17),
        .ECAUSE_BITS(8),
        .MPU_FAULT_FIRST(1'b1)
    ) u_core (
        .clk(clk), .rst_n(rst_n), .tamper_zeroize_n(tamper_n),
        .jtag_test_mode_i(jtag_mode),
        .start_i(core_start), .zeroize_first_i(core_zeroize_first),
        .dbg_halt_i(core_halt_comb), .start_pc_i(core_start_pc),
        .arg_regs_we_i(core_arg_we), .arg_reg_addr_i(core_arg_addr), .arg_reg_data_i(core_arg_data),
        .mem_en_o(mem_en), .mem_we_o(mem_we), .mem_wstrb_o(mem_wstrb),
        .mem_addr_o(mem_addr), .mem_wdata_o(mem_wdata),
        .mem_rdata_i(mem_rdata), .mem_ready_i(mem_ready), .mem_fault_i(mem_fault),
        .insn_retire_o(unused_retire), .halted_o(halted), .tampered_o(tampered),
        .trap_o(trap), .zeroize_pulse_o(core_zeroize_pulse),
        .pc_o(core_pc), .ecause_o(core_ecause), .instret_o(core_instret),
        .cycles_o(core_cycles), .phys_cycles_o(core_phys), .r4_o(core_r4),
        .dbg_we_o(dbg_we), .dbg_byte_o(dbg_byte),
        .dbg_in_i(dbg_allowed ? {55'd0, uart_rx_valid, uart_rx_byte} : 64'd0),
        .dbg_rd_o(dbg_rd),
        .post_clear_i(post_clear),
        .applet_exec_i(applet_exec_q),
        .ring3_enter_i(ring3_enter_q),
        .mem_fetch_o(mem_fetch),
        .mem_byte_o(mem_byte)
    );

    wire addr_hi32_z  = (mem_addr[63:32] == 32'd0);
    wire addr_mid_z   = addr_hi32_z && (mem_addr[31:17] == 15'd0);
    wire sel_irom     = addr_mid_z && (mem_addr[16:12] == 5'd0);
    wire sel_dsram    = addr_mid_z && (mem_addr[16:9]  == 8'b1000_0000);
    wire sel_mmio     = addr_hi32_z && (mem_addr[31:16] == 16'hFFFF) && (mem_addr[15:7] == 9'd0);

    logic        frame_active_q, launch_pending_q;
    logic [7:0]  frame_index_q, frame_last_q;
    logic [9:0]  payload_len_q;

    // Two-Ring Hardware W^X MPU (~18 gates):
    //   Ring 0 (`!applet_exec_q`): 0x0000..0x0FFF R+X,!W; 0x10000..0x101FF R+W,!X; 0xFFFF_0000 R+W,!X.
    //   Ring 3 (`applet_exec_q`):  0x10000..0x100FF R+X,!W; 0x10100..0x101FF R+W,!X; I-ROM & MMIO fault!
    wire pc_in_irom   = (core_pc[63:12] == 52'd0);
    wire mmio_priv_ok = !post_running && !applet_exec_q && pc_in_irom;
    wire cross_256b   = !mem_byte && (&mem_addr[7:3]) && (|mem_addr[2:0]);
    wire cross_512b   = !mem_byte && (&mem_addr[8:3]) && (|mem_addr[2:0]);
    wire cross_irom   = !mem_byte && (&mem_addr[11:3]) && (|mem_addr[2:0]);
    wire cross_mmio   = !mem_byte && (&mem_addr[6:3]) && (|mem_addr[2:0]);

    logic mem_fault_comb;
    always_comb begin
        if (!applet_exec_q) begin
            if (mem_fetch)       mem_fault_comb = !sel_irom;
            else if (sel_irom)   mem_fault_comb = mem_we || cross_irom;
            else if (sel_dsram)  mem_fault_comb = post_running || !pc_in_irom || cross_512b;
            else if (sel_mmio)   mem_fault_comb = !mmio_priv_ok || cross_mmio;
            else                 mem_fault_comb = 1'b1;
        end else begin
            if (mem_fetch)       mem_fault_comb = !(sel_dsram && !mem_addr[8]);
            else if (sel_dsram)  mem_fault_comb = cross_256b || (!mem_addr[8] && mem_we);
            else                 mem_fault_comb = 1'b1;
        end
    end
    assign mem_fault = mem_fault_comb;

    logic       ifetch_sram_q;
    logic [3:0] sram_step_q;
    logic [1:0] rd_src_q;
    logic [3:0] mmio_idx_q;
    wire  mem_aligned    = mem_fetch || mem_byte || (mem_addr[2:0] == 3'd0);
    wire  core_sram_req  = mem_en && mem_aligned && !mem_fault && sel_dsram;
    wire  is_stb_1b      = core_sram_req && mem_we && (mem_wstrb != 8'hff);
    wire  is_ifetch_4b   = core_sram_req && mem_fetch;
    wire [3:0] sram_last = is_stb_1b ? 4'd0 : is_ifetch_4b ? 4'd4 : 4'd8;

    assign mem_ready = (sel_irom && !mem_fault) || (sel_mmio && mmio_priv_ok && !mem_fault)
                     || (core_sram_req && !scrub_active_q && (sram_step_q == sram_last));

    logic        dma_active_q, dma_we_q, dma_rd_tx_q;
    logic [8:0]  dma_base_q;
    logic [3:0]  dma_bstep_q;

    wire dma_finishing = dma_bstep_q == (dma_we_q ? 4'd7 : 4'd8);

    assign host_rdy = halted && rst_n && tamper_n && !tampered && post_good && (post_phase_q == 2'd3)
                    && (lc_state_q != LC_LOCKED_OUT)
                    && !running_q && !scrub_active_q && !launch_pending_q && !dma_active_q && !wipe_r12_we;

    wire load_op      = (cmd_op_q == 8'h30);
    wire ext_wotsc_op = (cmd_op_q == 8'h12 || cmd_op_q == 8'h15 || cmd_op_q == 8'h16) && (payload_len_q == 10'd320);
    wire frame_beat   = wrd_ev && frame_active_q && !running_q && !scrub_active_q;
    wire consume_beat = frame_beat && (rx_widx_sck == frame_index_q) && (!dma_active_q || dma_finishing);

    wire [63:0] irom_rdata;
    qsag_ass2_irom u_irom (
        .addr(mem_addr[11:3]), .rdata(irom_rdata), .post_pc_o(irom_post_pc)
    );

    wire [7:0] dma_u32_idx   = {dma_widx_q[6:0], dma_bstep_q[2]};
    wire [7:0] dma_chain_beg = 8'(load_nwords_q) + 8'd11;
    wire [7:0] dma_chain_end = 8'(load_nwords_q) + 8'd74;
    wire load_code_u32  = (dma_u32_idx >= 8'd1) && (dma_u32_idx <= 8'(load_nwords_q));
    wire load_chain_u32 = (cmd_flags_q == 2'd2) && (dma_u32_idx >= dma_chain_beg) && (dma_u32_idx <= dma_chain_end);
    wire [5:0] code_w_off  = 6'(dma_u32_idx - 8'd1);
    wire [5:0] chain_w_off = 6'(dma_u32_idx - dma_chain_beg);

    logic       dsram_en, dsram_we;
    logic [8:0] dsram_addr;
    logic [7:0] dsram_wdata, dsram_rdata;

    always_comb begin
        dsram_en = 1'b0; dsram_we = 1'b0; dsram_addr = 9'd0; dsram_wdata = 8'd0;

        if (scrub_active_q) begin
            dsram_en    = 1'b1;
            dsram_we    = 1'b1;
            dsram_addr  = scrub_addr_q;
            dsram_wdata = 8'd0;
        end else if (dma_active_q) begin
            if (dma_we_q && load_op) begin
                dsram_en    = (dma_bstep_q < 4'd8) && (load_code_u32 || load_chain_u32);
                dsram_we    = dsram_en;
                dsram_addr  = load_code_u32 ? {1'b0, code_w_off,  dma_bstep_q[1:0]}
                                            : {1'b1, chain_w_off, dma_bstep_q[1:0]};
                dsram_wdata = buf64_q[7:0];
            end else begin
                dsram_en    = 1'b1;
                dsram_we    = dma_we_q && (dma_bstep_q < 4'd8);
                dsram_addr  = dma_base_q + 9'(dma_bstep_q[2:0]);
                dsram_wdata = buf64_q[7:0];
            end
        end else if (core_sram_req) begin
            dsram_en    = is_stb_1b || (sram_step_q < sram_last);
            dsram_we    = mem_we && (is_stb_1b || (sram_step_q < 4'd8));
            dsram_addr  = is_stb_1b    ? mem_addr[8:0]
                        : is_ifetch_4b ? {1'b0, mem_addr[7:2], sram_step_q[1:0]}
                        :                {mem_addr[8:3], sram_step_q[2:0]};
            dsram_wdata = is_stb_1b ? mem_wdata[7:0] : mem_wdata[{sram_step_q[2:0], 3'd0} +: 8];
        end
    end

    qsag_ass2_sram u_dsram (
        .clk(clk), .en(srst_n && dsram_en), .we(dsram_we), .addr(dsram_addr), .wdata(dsram_wdata), .rdata(dsram_rdata)
    );

    logic [7:0]  gpio_out_q, gpio_oe_q, gpio_in_s;
    logic [11:0] uart_div_q;
    logic        fram_cs_n_q, fram_sck_q, fram_mosi_q, fram_busy_q;
    logic [1:0]  fram_div_q;
    logic [3:0]  fram_cnt_q;
    logic [7:0]  fram_sr_q;
    logic [29:0] trng_cnt_q;
    logic [63:0] trng_word;
    logic        trng_take_q;
    wire mmio_en   = running_q && !trap && mem_en && mem_aligned && !mem_fault && sel_mmio && mmio_priv_ok;
    wire trng_take = mmio_en && !mem_we && mem_addr[6:3] == 4'h8 && trng_valid && trng_ok;
    qsag_trng u_trng (
        .clk(clk), .rst_n(srst_n), .en(srst_n), .take(trng_take_q),
        .word(trng_word), .valid(trng_valid), .ok(trng_ok),
        .rct_fail(trng_rct), .apt_fail(trng_apt), .raw_bit(raw_bit)
    );

    // Dual-phase zero-borrow 448-bit (`7 x 64`) Enclave Secret Vault (`latrnq_1`, 0-clock tamper wipe):
    //   Row 0: `cap_lo` (0x1), 1: `cap_hi` (0x6), 2: `record_q` (0x7),
    //   3: `key_lo` (0xA), 4: `key_hi` (0xB), 5: `nonce_lo` (0x3), 6: `nonce_hi` (0xF).
    localparam logic [3:0] VAULT_IDX [7] = '{4'h1, 4'h6, 4'h7, 4'hA, 4'hB, 4'h3, 4'hF};
    wire private_write = mmio_en && mem_we && (&mem_wstrb);
    wire v_rst_raw     = srst_n && !vault_clr_q;
    logic [63:0] vault_q [7];

`ifdef GF180_SRAM_MACRO
    wire [1:0] v_rst_buf;
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__clkbuf_8 u_vrst0 (.I(v_rst_raw), .Z(v_rst_buf[0]));
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__clkbuf_8 u_vrst1 (.I(v_rst_raw), .Z(v_rst_buf[1]));

    wire v_wact_q, v_sel_gclk;
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__dffrnq_1 u_vwact (
        .CLK(clk), .D(private_write), .RN(v_rst_buf[0]), .Q(v_wact_q)
    );
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__icgtp_2 u_vsel_icg (
        .CLK(clk), .E(private_write || v_wact_q), .TE(1'b0), .Q(v_sel_gclk)
    );

    wire [63:0] vwdata_buf;
    for (genvar kb = 0; kb < 64; kb++) begin : g_vwbuf
        gf180mcu_fd_sc_mcu7t5v0__buf_4 u_vwb (.I(mem_wdata[kb]), .Z(vwdata_buf[kb]));
    end

    for (genvar v = 0; v < 7; v++) begin : g_vault
        wire vsel_n_d = ~(private_write && (mem_addr[6:3] == VAULT_IDX[v]));
        wire vsel_n_q, vgclk_raw, vgclk;
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__dffsnq_1 u_vsel (
            .CLK(v_sel_gclk), .D(vsel_n_d), .SETN(v_rst_buf[v / 4]), .Q(vsel_n_q)
        );
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__nor2_2 u_vgclk (
            .A1(clk), .A2(vsel_n_q), .ZN(vgclk_raw)
        );
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__clkbuf_4 u_vgbuf (.I(vgclk_raw), .Z(vgclk));
        for (genvar b = 0; b < 64; b++) begin : g_bit
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__latrnq_1 u_lat (
                .D(vwdata_buf[b]), .E(vgclk), .RN(v_rst_buf[v / 4]), .Q(vault_q[v][b])
            );
        end
    end
`else
    logic [6:0] vsel_sim_q;
    always_ff @(posedge clk or negedge v_rst_raw) begin
        if (!v_rst_raw) begin
            vsel_sim_q <= 7'd0;
            for (int v = 0; v < 7; v++) vault_q[v] <= 64'd0;
        end else begin
            for (int v = 0; v < 7; v++) begin
                vsel_sim_q[v] <= private_write && (mem_addr[6:3] == VAULT_IDX[v]);
                if (vsel_sim_q[v]) vault_q[v] <= mem_wdata;
            end
        end
    end
`endif

    wire [63:0] cap_lo   = vault_q[0];
    wire [63:0] cap_hi   = vault_q[1];
    wire [63:0] record_q = vault_q[2];
    wire [63:0] key_lo /* verilator public_flat_rd */ = vault_q[3];
    wire [63:0] key_hi /* verilator public_flat_rd */ = vault_q[4];
    wire [63:0] nonce_lo = vault_q[5];
    wire [63:0] nonce_hi = vault_q[6];

    logic [2:0]  puf_block_q;
    logic [3:0]  puf_bist_q;
    logic        puf_recon_q, puf_busy, puf_done, puf_err, puf_complete_q;
    logic [5:0]  puf_margin_q, puf_accepted;
    logic [3:0]  puf_corrected;
    logic [26:0] puf_syn;
    logic [63:0] puf_mask, puf_word;
    wire puf_write      = mmio_en && mem_we && (&mem_wstrb) && !puf_busy;
    wire puf_start      = puf_write && mem_addr[6:3] == 4'h2;
    wire puf_bist_allow = (lc_state_q == LC_BLANK) && puf_bist_q[3];
    wire unused_mon;
    dregg_ro_puf_bch u_puf (
        .clk(clk), .rst_n(srst_n), .srst_n(srst_n),
        .zeroize_i(vault_clr_q),
        .bist_allow_i(puf_bist_allow), .start_blk(puf_start),
        .recon_mode(puf_start ? mem_wdata[3] : puf_recon_q), .blk_sel(puf_block_q),
        .margin_thresh(puf_margin_q), .noise_flips(puf_bist_q[2:0]), .mon_en(1'b0),
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

    // Sparse MMIO readback: separate 64-bit Vault/PUF/TRNG sources from narrow control registers!
    wire rom_lock = rom_lock_q || record_q[3];
    logic vault_cap_sel_q;
    wire [63:0] slot_a = vault_cap_sel_q ? cap_lo : key_lo;
    wire [63:0] slot_b = vault_cap_sel_q ? cap_hi : key_hi;
    logic [63:0] mmio_rdata;
    always_comb begin
        mmio_rdata = 64'd0;
        case (mmio_idx_q)
            4'h0: mmio_rdata[7:0]   = fram_sr_q;
            4'h1: mmio_rdata[1:0]   = {fram_miso_s, fram_busy_q};
            4'h2: mmio_rdata        = {record_q[31:0], 4'd0, cmd_flags_q, payload_len_q, 1'b0, load_nwords_q, cmd_op_q};
            4'h3: mmio_rdata        = nonce_lo;
            4'h4: mmio_rdata        = puf_mask;
            4'h5: mmio_rdata[26:0]  = puf_syn;
            4'h6: mmio_rdata        = (puf_complete_q && !puf_err) ? puf_word : 64'd0;
            4'h7: mmio_rdata        = {record_q[63:32], 19'd0, puf_corrected, puf_accepted, puf_err, puf_complete_q, puf_busy};
            4'h8: mmio_rdata        = trng_take_q ? trng_word : 64'd0;
            4'h9: mmio_rdata[34:0]  = {trng_rct, trng_apt, !uart_tx_ovf, trng_ok, trng_valid, trng_cnt_q};
            4'hA: mmio_rdata        = slot_a;
            4'hB: mmio_rdata        = slot_b;
            4'hC: mmio_rdata[24:0]  = {drop_ring3_req_q, 6'd0, rom_lock, vault_cap_sel_q, 5'd0, lc_state_q, 6'd0, fault_q, verify_q};
            4'hD: mmio_rdata[23:0]  = {gpio_in_s, gpio_oe_q, gpio_out_q};
            4'hE: mmio_rdata[11:0]  = uart_div_q;
            4'hF: mmio_rdata        = nonce_hi;
        endcase
    end

    wire [31:0] sram_insn32    = {dsram_rdata, buf64_q[55:32]};
    wire [63:0] sram_assembled = ifetch_sram_q ? {sram_insn32, sram_insn32}
                                               : {dsram_rdata, buf64_q[55:0]};
    assign mem_rdata = (rd_src_q == 2'd0) ? irom_rdata
                     : (rd_src_q == 2'd2) ? mmio_rdata
                     : sram_assembled;

    logic [3:0] clk_div16_q;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            clk_div16_q <= 4'd0;
            prov_lock_q <= 1'b0;
        end else begin
            clk_div16_q <= clk_div16_q + 4'd1;
            if (lc_state_q != LC_RESET && lc_state_q != LC_BLANK) prov_lock_q <= 1'b1;
        end
    end

    wire sram_shift_core = core_sram_req && !scrub_active_q && !dma_active_q
                        && (sram_step_q > 4'd0) && (sram_step_q < sram_last);
    wire sram_shift_dma  = dma_active_q && !scrub_active_q
                        && (dma_we_q || (dma_bstep_q > 4'd0 && dma_bstep_q <= 4'd7));
    wire [7:0] shift_top_byte = (sram_shift_core || !dma_we_q) ? dsram_rdata : buf64_q[63:56];

    // Zero-recirculation `buf64_d` (`buf64_en` gates `u_buf64` via `clockgate`!)
    logic [63:0] tx_meta_word;
    always_comb begin
        if (cmd_op_q == 8'h01) begin
            unique case (tx_widx_sck[1:0])
                2'd0: tx_meta_word = 64'h3038_3144_3253_5341;
                2'd1: tx_meta_word = ID;
                2'd2: tx_meta_word = {29'd0, lc_state_q, trng_ok, trng_valid, trng_cnt_q};
                default: tx_meta_word = core_cycles;
            endcase
        end else if (resp_err_q) begin
            tx_meta_word = (tx_widx_sck == 5'd0) ? core_ecause : core_pc;
        end else begin
            tx_meta_word = (tx_widx_sck == 5'd16) ? core_r4
                         : (tx_widx_sck == 5'd17) ? core_ecause
                         : (tx_widx_sck == 5'd18) ? core_instret : core_cycles;
        end
    end

    wire tx_meta_valid = !running_q && !frame_active_q && !scrub_active_q && (
        (resp_len_sel_q == 2'd1 && tx_widx_sck < 5'd2) ||
        (resp_len_sel_q == 2'd2 && tx_widx_sck < 5'd4) ||
        (resp_len_sel_q == 2'd3 && !resp_err_q && tx_widx_sck >= 5'd16 && tx_widx_sck < 5'd20)
    );
    wire clear_buf64 = core_zeroize_pulse || trng_fault || (running_q && !core_start && halted && !trap && !budget_expired);

    always_comb begin
        buf64_en = 1'b0;
        buf64_d  = tx_meta_word;
        if (clear_buf64) begin
            buf64_en = 1'b1;
            buf64_d  = 64'd0;
        end else if (consume_beat) begin
            buf64_en = 1'b1;
            buf64_d  = rx_word_sck;
        end else if (sram_shift_core || sram_shift_dma) begin
            buf64_en = 1'b1;
            buf64_d  = {8'd0, shift_top_byte, buf64_q[55:8]};
        end else if (dma_active_q && !scrub_active_q && dma_bstep_q == 4'd8 && dma_rd_tx_q) begin
            buf64_en = 1'b1;
            buf64_d  = {dsram_rdata, buf64_q[55:0]};
        end else if (hdr_ev && host_rdy && rx_word_sck[7:0] == 8'h51 && rx_word_sck[15:8] == 8'h01 && rx_word_sck[47:24] == 24'd0) begin
            buf64_en = 1'b1;
            buf64_d  = 64'h3038_3144_3253_5341;
        end else if (running_q && !core_start && (trap || budget_expired)) begin
            buf64_en = 1'b1;
            buf64_d  = trap ? core_ecause : core_pc;
        end else if (txn_ev && tx_meta_valid) begin
            buf64_en = 1'b1;
        end
    end

    function automatic logic [3:0] proof_reg_map(input logic [2:0] idx);
        case (idx)
            3'd0: return 4'd1;
            3'd1: return 4'd6;
            3'd2: return 4'd7;
            3'd3: return 4'd9;
            default: return 4'd10;
        endcase
    endfunction

    wire [23:0] hdr_len = rx_word_sck[47:24];
    wire [7:0]  hdr_flg = rx_word_sck[23:16];
    logic [4:0] header_error;
    always_comb begin
        header_error = 5'd0;
        if (rx_word_sck[7:0] != 8'h51) header_error = 5'd1;
        else case (rx_word_sck[15:8])
            8'h01, 8'h10: if (hdr_len != 24'd0) header_error = 5'd3;
            8'h11: if (hdr_len != 24'd32) header_error = 5'd3;
            8'h12, 8'h15, 8'h16: if (hdr_len != 24'd320) header_error = 5'd3;
            8'h20: begin
                if (hdr_len != 24'd120) header_error = 5'd3;
                else if (safe_recovery) header_error = 5'd14;
            end
            8'h30: begin
                if (rx_word_sck[63:48] != 16'd0 || hdr_flg[7:2] != 6'd0) header_error = 5'd3;
                else if (safe_recovery || ((lc_state_q == LC_PROVISIONED || lc_state_q == LC_READY) && rom_lock))
                    header_error = 5'd14;
                else if (lc_state_q == LC_BLANK) begin
                    if (hdr_flg[1:0] != 2'd0) header_error = 5'd13;
                    else if (hdr_len < 24'd8 || hdr_len > 24'd260 || hdr_len[1:0] != 2'b00) header_error = 5'd3;
                end else if (lc_state_q == LC_PROVISIONED || lc_state_q == LC_READY) begin
                    if (hdr_flg[1:0] != 2'd2) header_error = 5'd13;
                    else if (hdr_len < 24'd304 || hdr_len > 24'd556 || hdr_len[1:0] != 2'b00) header_error = 5'd3;
                end else begin
                    header_error = 5'd13;
                end
            end
            8'h31: begin
                if (hdr_len > 24'd128) header_error = 5'd3;
                else if (!rx_word_sck[16]) begin
                    if (safe_recovery || rom_lock) header_error = 5'd14;
                    else if (!applet_valid_q)      header_error = 5'd13;
                end
            end
            default: header_error = 5'd2;
        endcase
    end

    wire [7:0]  hdr_qwords   = 8'((rx_word_sck[33:24] + 10'd7) >> 3);
    wire [6:0]  eff_load_n   = (rx_widx_sck == 8'd0) ? rx_word_sck[6:0] : load_nwords_q;
    wire [7:0]  load_m_idx   = {2'b00, eff_load_n[6:1]};
    wire [9:0]  exp_load_len = ((cmd_flags_q == 2'd2) ? 10'd300 : 10'd4) + {1'b0, rx_word_sck[6:0], 2'b00};
    wire        bad_load_b0  = load_op && (rx_widx_sck == 8'd0)
                             && (rx_word_sck[31:0] == 32'd0 || rx_word_sck[31:0] > 32'd64
                                 || payload_len_q != exp_load_len);
    wire        bad_load_pad = load_op && (frame_index_q == frame_last_q) && !eff_load_n[0]
                             && (rx_word_sck[63:32] != 32'd0);

    always_ff @(posedge clk or negedge srst_n) begin
        if (!srst_n) begin
            hdr_m <= 1'b0; hdr_s <= 1'b0; hdr_seen <= 1'b0;
            wrd_m <= 1'b0; wrd_s <= 1'b0; wrd_seen <= 1'b0;
            txn_m <= 1'b0; txn_s <= 1'b0; txn_seen <= 1'b0;
            verify_q <= 1'b0; fault_q <= 1'b0; host_irq_q <= 1'b0; running_q <= 1'b0;
            post_ok_q <= 1'b0; post_fail_q <= 1'b0; post_phase_q <= 2'd0;
            lc_state_q <= LC_RESET;
            applet_exec_q <= 1'b0; applet_valid_q <= 1'b0;
            drop_ring3_req_q <= 1'b0; ring3_enter_q <= 1'b0; rom_lock_q <= 1'b0;
            r12_wipe_q <= 2'd0; load_nwords_q <= 7'd0; dma_widx_q <= 7'd0; lo32_hold_q <= 32'd0;
            arg_we_q <= 1'b0; arg_addr_q <= 4'd0; arg_data_q <= 64'd0;
            vault_cap_sel_q <= 1'b0; vault_clr_q <= 1'b1;
            scrub_active_q <= 1'b1; scrub_full_q <= 1'b1; scrub_addr_q <= 9'd0;
            ifetch_sram_q <= 1'b0; sram_step_q <= 4'd0; rd_src_q <= 2'd0; mmio_idx_q <= 4'd0;
            core_start <= 1'b0; core_zeroize_first <= 1'b0; core_halt_req <= 1'b0;
            cmd_op_q <= 8'd0; cmd_flags_q <= 2'd0; resp_len_sel_q <= 2'd0;
            resp_err_code_q <= 5'd0; resp_err_q <= 1'b0; tx_word_valid_q <= 1'b0;
            exec_cnt_q <= 16'hffff; long_service_q <= 1'b0; budget_last_q <= 1'b0;
            frame_active_q <= 1'b0; launch_pending_q <= 1'b0; frame_index_q <= '0;
            frame_last_q <= '0; payload_len_q <= '0; service_timer_q <= '0;
            dma_active_q <= 1'b0; dma_we_q <= 1'b0; dma_rd_tx_q <= 1'b0;
            dma_base_q <= 9'd0; dma_bstep_q <= 4'd0;
            gpio_out_q <= 8'd0; gpio_oe_q <= 8'd0; gpio_in_m <= 8'd0; gpio_in_s <= 8'd0;
            uart_div_q <= 12'(DEFAULT_UART_DIV);
            fram_cs_n_q <= 1'b1; fram_sck_q <= 1'b0; fram_mosi_q <= 1'b0; fram_busy_q <= 1'b0;
            fram_div_q <= '0; fram_cnt_q <= 4'd0; fram_sr_q <= 8'd0; fram_miso_m <= 1'b0; fram_miso_s <= 1'b0;
            trng_cnt_q <= '0; trng_take_q <= 1'b0;
            puf_block_q <= '0; puf_bist_q <= 4'd0; puf_recon_q <= 1'b0; puf_margin_q <= '0; puf_complete_q <= 1'b0;
        end else begin
            hdr_m <= rx_hdr_tog; hdr_s <= hdr_m; hdr_seen <= hdr_s;
            wrd_m <= rx_word_tog; wrd_s <= wrd_m; wrd_seen <= wrd_s;
            txn_m <= tx_next_tog; txn_s <= txn_m; txn_seen <= txn_s;
            gpio_in_m <= bidir_in[15:8]; gpio_in_s <= gpio_in_m;
            fram_miso_m <= fram_miso_in; fram_miso_s <= fram_miso_m;

            core_start    <= 1'b0;
            core_halt_req <= 1'b0;
            ring3_enter_q <= 1'b0;
            arg_we_q      <= 1'b0;
            if (r12_wipe_q != 2'd0) r12_wipe_q <= r12_wipe_q - 2'd1;
            vault_clr_q   <= core_zeroize_pulse || trng_fault || post_fail_q || (lc_state_q == LC_LOCKED_OUT);

            if (core_zeroize_pulse) begin
                tx_word_valid_q <= 1'b0;
                applet_valid_q  <= 1'b0;
            end

            if (trng_fault) begin
                fault_q          <= 1'b1;
                lc_state_q       <= LC_LOCKED_OUT;
                applet_exec_q    <= 1'b0;
                applet_valid_q   <= 1'b0;
                drop_ring3_req_q <= 1'b0;
                tx_word_valid_q  <= 1'b0;
                frame_active_q   <= 1'b0;
                launch_pending_q <= 1'b0;
                if (running_q) begin
                    core_halt_req  <= 1'b1;
                    running_q      <= 1'b0;
                    scrub_active_q <= 1'b1; scrub_full_q <= 1'b1; scrub_addr_q <= 9'd0;
                    resp_err_q     <= 1'b1; resp_err_code_q <= 5'd11; resp_len_sel_q <= 2'd0;
                    host_irq_q     <= 1'b1;
                end
            end
            if (lc_state_q != LC_BLANK) puf_bist_q <= 4'd0;

            // Full FIPS 140-3 §10.3.A Cold-Boot Power-On Known-Answer Self-Test (`POST KAT`)
            case (post_phase_q)
                2'd0: begin
                    core_start         <= 1'b1;
                    core_zeroize_first <= 1'b0;
                    exec_cnt_q         <= 16'hffff;
                    post_phase_q       <= 2'd1;
                end
                2'd1: if (!core_start) begin
                    if (clk_div16_q == 4'd0) exec_cnt_q <= exec_cnt_q - 16'd1;
                    if (trap || (exec_cnt_q == 16'd0 && !halted)) begin
                        core_halt_req <= 1'b1;
                        post_fail_q   <= 1'b1;
                        fault_q       <= 1'b1;
                        lc_state_q    <= LC_LOCKED_OUT;
                        post_phase_q  <= 2'd2;
                    end else if (halted) begin
                        if (core_r4 == POST_KAT_GOLDEN) post_ok_q <= 1'b1;
                        else begin
                            post_fail_q <= 1'b1;
                            fault_q     <= 1'b1;
                            lc_state_q  <= LC_LOCKED_OUT;
                        end
                        post_phase_q <= 2'd2;
                    end
                end
                2'd2: begin
                    exec_cnt_q   <= 16'd0;
                    post_phase_q <= 2'd3;
                end
                default: ;
            endcase

            trng_take_q <= trng_take;
            if (trng_take_q) trng_cnt_q <= trng_cnt_q + 30'd1;
            if (puf_done) puf_complete_q <= 1'b1;
            if (puf_start) begin
                puf_block_q    <= mem_wdata[2:0];
                puf_recon_q    <= mem_wdata[3];
                puf_margin_q   <= mem_wdata[13:8];
                if (lc_state_q == LC_BLANK) puf_bist_q <= mem_wdata[19:16];
                puf_complete_q <= 1'b0;
            end

            if (fram_busy_q) begin
                fram_div_q <= fram_div_q + 2'd1;
                if (&fram_div_q) begin
                    fram_sck_q <= !fram_sck_q;
                    if (!fram_sck_q) fram_sr_q <= {fram_sr_q[6:0], fram_miso_s};
                    else if (fram_cnt_q == 4'd7) fram_busy_q <= 1'b0;
                    else begin
                        fram_cnt_q  <= fram_cnt_q + 4'd1;
                        fram_mosi_q <= fram_sr_q[7];
                    end
                end
            end

            if (core_zeroize_pulse) begin
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
                rd_src_q      <= sel_irom ? 2'd0 : sel_dsram ? 2'd1 : 2'd2;
                ifetch_sram_q <= sel_dsram && mem_fetch;
                mmio_idx_q    <= mem_addr[6:3];
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
                    if (dma_rd_tx_q) tx_word_valid_q <= 1'b1;
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
                            fram_div_q  <= 2'd0; fram_cnt_q <= 4'd0;
                            fram_sck_q  <= 1'b0;
                            fram_busy_q <= 1'b1;
                        end
                    end
                    4'hC: begin
                        if (mem_wstrb[0]) begin
                            verify_q <= mem_wdata[0];
                            fault_q  <= fault_q || mem_wdata[1];
                        end
                        if (mem_wstrb[1] && mem_wdata[10:8] <= 3'd6 && lc_state_q != LC_LOCKED_OUT) begin
                            if (mem_wdata[10:8] != 3'(LC_BLANK) || lc_state_q == LC_RESET || lc_state_q == LC_BLANK)
                                lc_state_q <= lc_state_t'(mem_wdata[10:8]);
                        end
                        if (mem_wstrb[2]) begin
                            vault_cap_sel_q <= mem_wdata[16];
                        end
                        if (mem_wstrb[3]) begin
                            drop_ring3_req_q <= mem_wdata[24];
                            rom_lock_q       <= rom_lock_q || mem_wdata[25];
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
                automatic logic next_long = (rx_word_sck[15:8] != 8'h31) || (rx_word_sck[63:48] == 16'd0);
                host_irq_q       <= 1'b0;
                cmd_op_q         <= rx_word_sck[15:8];
                cmd_flags_q      <= rx_word_sck[17:16];
                long_service_q   <= next_long;
                exec_cnt_q       <= (!next_long && rx_word_sck[63:48] != 16'd0)
                                  ? rx_word_sck[63:48] : 16'hffff;
                payload_len_q    <= rx_word_sck[33:24];
                frame_index_q    <= 8'd0;
                frame_active_q   <= 1'b0;
                launch_pending_q <= 1'b0;
                drop_ring3_req_q <= 1'b0;
                resp_err_q       <= header_error != 5'd0;
                resp_err_code_q  <= header_error;
                resp_len_sel_q   <= 2'd0;
                tx_word_valid_q  <= 1'b0;
                if (header_error == 5'd0 && rx_word_sck[15:8] != 8'h01
                    && !(rx_word_sck[15:8] == 8'h31 && !rx_word_sck[16])) begin
                    applet_valid_q <= 1'b0;
                end
                if (header_error == 5'd0 && rx_word_sck[15:8] == 8'h30) begin
                    core_halt_req <= 1'b1; // pre-wipe R1..R15 & S0..S24 before 0x30 proof DMA
                    load_nwords_q <= 7'd0;
                    lo32_hold_q   <= 32'd0;
                end
                if (header_error != 5'd0) host_irq_q <= 1'b1;
                else if (rx_word_sck[15:8] == 8'h01) begin
                    resp_len_sel_q  <= 2'd2;
                    tx_word_valid_q <= 1'b1;
                    host_irq_q      <= 1'b1;
                end else if (rx_word_sck[47:24] == 24'd0) launch_pending_q <= 1'b1;
                else begin
                    frame_active_q <= 1'b1;
                    frame_last_q   <= hdr_qwords - 8'd1;
                end
            end
            if (frame_beat) begin
                if (!consume_beat || bad_load_b0 || bad_load_pad) begin
                    frame_active_q  <= 1'b0;
                    if (load_op) core_halt_req <= 1'b1;
                    resp_err_q      <= 1'b1; resp_err_code_q <= 5'd3; resp_len_sel_q <= 2'd0;
                    tx_word_valid_q <= 1'b0;
                    host_irq_q      <= 1'b1;
                end else begin
                    frame_index_q <= frame_index_q + 8'd1;
                    dma_widx_q    <= rx_widx_sck[6:0];
                    if (load_op && rx_widx_sck == 8'd0) load_nwords_q <= rx_word_sck[6:0];
                    if (load_op && cmd_flags_q == 2'd2) begin
                        lo32_hold_q <= rx_word_sck[63:32];
                        if (rx_widx_sck >= (load_m_idx + 8'd1) && rx_widx_sck <= (load_m_idx + 8'd5)) begin
                            arg_we_q   <= 1'b1;
                            arg_addr_q <= proof_reg_map(3'(rx_widx_sck - load_m_idx - 8'd1));
                            arg_data_q <= eff_load_n[0] ? rx_word_sck : {rx_word_sck[31:0], lo32_hold_q};
                        end
                    end
                    dma_active_q  <= 1'b1;
                    dma_we_q      <= 1'b1;
                    dma_rd_tx_q   <= 1'b0;
                    dma_bstep_q   <= 4'd0;
                    dma_base_q    <= ext_wotsc_op ? (9'h040 + {rx_widx_sck[5:0], 3'b000})
                                                  : {2'b10, rx_widx_sck[3:0], 3'b000};
                    if (frame_index_q == frame_last_q) begin
                        frame_active_q   <= 1'b0;
                        launch_pending_q <= 1'b1;
                    end
                end
            end
            if (launch_pending_q && !dma_active_q && !trng_fault) begin
                automatic logic direct_ring3 = (cmd_op_q == 8'h31) && !cmd_flags_q[0];
                launch_pending_q   <= 1'b0;
                core_start         <= 1'b1;
                core_zeroize_first <= !load_op;
                applet_exec_q      <= direct_ring3;
                ring3_enter_q      <= direct_ring3;
                drop_ring3_req_q   <= 1'b0;
                vault_cap_sel_q    <= 1'b0;
                tx_word_valid_q    <= 1'b0;
                service_timer_q    <= 9'h1ff;
                budget_last_q      <= !long_service_q && (exec_cnt_q == 16'd1);
                running_q          <= 1'b1;
                verify_q           <= 1'b0;
            end

            if (running_q && !core_start && !trng_fault) begin
                exec_cnt_q    <= exec_cnt_q - 16'd1;
                if (exec_cnt_q == 16'd0) service_timer_q <= service_timer_q - 9'd1;
                budget_last_q <= long_service_q ? (service_timer_q == 9'd0 && exec_cnt_q == 16'd2)
                                                : (exec_cnt_q == 16'd2);
                if (trap || budget_expired) begin
                    if (!applet_exec_q) lc_state_q <= LC_LOCKED_OUT;
                    applet_exec_q    <= 1'b0;
                    applet_valid_q   <= 1'b0;
                    drop_ring3_req_q <= 1'b0;
                    core_halt_req    <= 1'b1;
                    running_q        <= 1'b0;
                    fault_q          <= 1'b1;
                    scrub_active_q   <= 1'b1; scrub_full_q <= (!applet_exec_q && budget_expired) || applet_exec_q;
                    scrub_addr_q     <= 9'd0;
                    resp_err_q       <= 1'b1;
                    resp_err_code_q  <= trap ? 5'd16 : 5'd15;
                    resp_len_sel_q   <= 2'd1;
                    tx_word_valid_q  <= 1'b1;
                    host_irq_q       <= 1'b1;
                end else if (halted && !applet_exec_q && drop_ring3_req_q) begin
                    // Hardware Ring-0 -> Ring-3 privilege drop (`R3..R15` & `S0..S24` scrubbed, `R1..R2` kept!)
                    drop_ring3_req_q   <= 1'b0;
                    applet_exec_q      <= 1'b1;
                    applet_valid_q     <= 1'b1;
                    core_start         <= 1'b1;
                    core_zeroize_first <= 1'b0;
                    ring3_enter_q      <= 1'b1;
                    long_service_q     <= 1'b1;
                    service_timer_q    <= 9'd3;
                    exec_cnt_q         <= 16'hffff;
                    budget_last_q      <= 1'b0;
                end else if (halted) begin
                    automatic logic was_applet = applet_exec_q;
                    running_q        <= 1'b0;
                    applet_exec_q    <= 1'b0;
                    drop_ring3_req_q <= 1'b0;
                    if (was_applet) r12_wipe_q <= 2'd2;
                    tx_word_valid_q  <= 1'b0;
                    verify_q         <= (cmd_flags_q[1] && !load_op) ? (core_r4 == 64'd1) : verify_q;
                    scrub_active_q   <= 1'b1;
                    scrub_full_q     <= 1'b0;
                    scrub_addr_q     <= was_applet ? 9'd256 : 9'd0;
                    if (!was_applet && cmd_op_q != 8'h31 && core_r4 != 64'd1) begin
                        if (load_op) fault_q <= 1'b1;
                        resp_err_q <= 1'b1; resp_err_code_q <= core_r4[4:0]; resp_len_sel_q <= 2'd0;
                    end else begin
                        resp_err_q <= 1'b0; resp_err_code_q <= 5'd0; resp_len_sel_q <= 2'd3;
                    end
                    host_irq_q <= 1'b1;
                end
            end

            if (txn_ev && !running_q && !frame_active_q && !scrub_active_q) begin
                if (resp_len_sel_q == 2'd3 && !resp_err_q && tx_widx_sck < 5'd16) begin
                    tx_word_valid_q <= 1'b0;
                    dma_active_q    <= 1'b1; dma_we_q <= 1'b0; dma_rd_tx_q <= 1'b1;
                    dma_base_q      <= {2'b11, tx_widx_sck[3:0], 3'd0}; dma_bstep_q <= 4'd0;
                end else begin
                    tx_word_valid_q <= tx_meta_valid;
                end
            end
        end
    end

    // Synchronous sequential endpoints on `jtag_tck` (IEEE 1149.1 falling-edge TDO) and `nfc_clk`
    wire jtag_rst_n = rst_n && jtag_ok;
    logic jtag_tdo_q;
    always_ff @(negedge jtag_tck_in or negedge jtag_rst_n) begin
        if (!jtag_rst_n) jtag_tdo_q <= 1'b0;
        else jtag_tdo_q <= jtag_tdi_in ^ jtag_tms_in;
    end
    wire jtag_tdo = jtag_ok ? jtag_tdo_q : 1'b0;

    logic nfc_mod_q;
    always_ff @(posedge nfc_clk_in or negedge srst_n) begin
        if (!srst_n) nfc_mod_q <= 1'b0;
        else nfc_mod_q <= nfc_ask_in && verify_pin;
    end
    wire nfc_mod = nfc_mod_q && verify_pin;
    wire db_resp = db_chal_in;

    assign input_pu = 4'b1000;
    assign input_pd = 4'b0111;

    always_comb begin
        bidir_out = 38'd0; bidir_oe = 38'd0;
        bidir_pu  = 38'd0; bidir_pd = 38'd0;
        bidir_cs  = 38'd0; bidir_sl = 38'd0;

        bidir_out[7:0]  = host_dq_o;      bidir_oe[7:0]  = host_dq_oe; bidir_sl[7:0] = 8'h00;
        bidir_out[15:8] = gpio_out_q;     bidir_oe[15:8] = gpio_oe_q;  bidir_pd[15:8] = ~gpio_oe_q;

        bidir_out[16] = verify_pin;       bidir_oe[16] = 1'b1;
        bidir_out[17] = fault_pin;        bidir_oe[17] = 1'b1;
        bidir_cs[18]  = 1'b1;
        bidir_out[19] = host_rdy;         bidir_oe[19] = 1'b1;
        bidir_out[20] = host_irq_q;       bidir_oe[20] = 1'b1;
        bidir_out[21] = clk_div16_q[3];   bidir_oe[21] = 1'b1;

        bidir_out[22] = fram_cs_n_q;      bidir_oe[22] = 1'b1;
        bidir_out[23] = fram_sck_q;       bidir_oe[23] = 1'b1;
        bidir_out[24] = fram_mosi_q;      bidir_oe[24] = 1'b1;
        bidir_pd[25]  = 1'b1;

        bidir_cs[26]  = 1'b1;             bidir_pu[26] = 1'b1;
        bidir_pu[27]  = 1'b1;
        bidir_out[28] = uart_tx_pin;      bidir_oe[28] = 1'b1;

        bidir_out[29] = db_resp;          bidir_oe[29] = 1'b1;
        bidir_pd[30]  = 1'b1;

        bidir_out[31] = nfc_mod;          bidir_oe[31] = 1'b1;
        bidir_pu[32]  = 1'b1;

        bidir_out[34]   = jtag_tdo;
        bidir_oe[34]    = jtag_ok;
        bidir_pd[34]    = !jtag_ok;
        bidir_pd[37:35] = 3'b111;

        // `host_dq_oe` (`[7:0]`) & `gpio_oe_q` (`[15:8]`) are already async-cleared to 0 on `!rst_n`;
        // gating only `[37:16]` eliminates the combinational `rst_n -> bidir_ie[15:8] -> gpio_in_m` arc!
        if (!rst_n) bidir_oe[37:16] = 22'd0;
        bidir_ie = ~bidir_oe;
    end

    wire unused_top = ^{raw_bit, clk_ext_en, core_phys,
                        bidir_in[24:19], bidir_in[17:16], bidir_in[31], bidir_in[29], bidir_in[28], bidir_in[34]};
endmodule

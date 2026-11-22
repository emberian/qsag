// Map the unidirectional `SLOT_0P5X0P5` ASIC pad signals onto physical ECP5-85F IOs.
module ecp5_top_wrap (
    input  wire       clk, rst_n, clk_ext_en, host_cs_n, tamper_zeroize_n,
    input  wire [1:0] boot_mode,
    input  wire       host_sck, dbg_uart_rx, fram_miso,
    input  wire       db_chal_in, nfc_ask_in, nfc_clk_in,
    input  wire       jtag_tck, jtag_tms, jtag_tdi,
    inout  wire [7:0] host_dq, gpio,
    output wire       host_rdy, host_irq, dbg_uart_tx, clk_mon, verify_ok, fault,
    output wire       fram_cs_n, fram_sck, fram_mosi,
    output wire       db_resp_out, nfc_load_mod, jtag_tdo
);
    wire [37:0] pad_out, pad_oe;
    wire unused_oe = ^{pad_oe[37:16]};
    wire unused_out = ^{pad_out[37:35], pad_out[33:32], pad_out[30], pad_out[27:25], pad_out[18]};
    wire [37:0] pad_in = {
        jtag_tck, jtag_tms, jtag_tdi, 1'b0,
        nfc_clk_in, nfc_ask_in, 1'b0,
        db_chal_in, 1'b0,
        1'b0, dbg_uart_rx, tamper_zeroize_n,
        fram_miso, 3'b0,
        3'b0, host_sck, 2'b0,
        gpio, host_dq
    };
    for (genvar i = 0; i < 8; i++) begin : io_buffers
        assign host_dq[i] = pad_oe[i]   ? pad_out[i]   : 1'bz;
        assign gpio[i]    = pad_oe[8+i] ? pad_out[8+i] : 1'bz;
    end
    assign verify_ok    = pad_out[16];
    assign fault        = pad_out[17];
    assign host_rdy     = pad_out[19];
    assign host_irq     = pad_out[20];
    assign clk_mon      = pad_out[21];
    assign fram_cs_n    = pad_out[22];
    assign fram_sck     = pad_out[23];
    assign fram_mosi    = pad_out[24];
    assign dbg_uart_tx  = pad_out[28];
    assign db_resp_out  = pad_out[29];
    assign nfc_load_mod = pad_out[31];
    assign jtag_tdo     = pad_out[34];

    wire [3:0]  in_pu_u, in_pd_u;
    wire [37:0] b_cs_u, b_sl_u, b_ie_u, b_pu_u, b_pd_u;

    qsag_ass2_enclave_top enclave (
        .clk(clk), .rst_n(rst_n),
        .input_in({host_cs_n, boot_mode, clk_ext_en}),
        .bidir_in(pad_in), .bidir_out(pad_out), .bidir_oe(pad_oe),
        .input_pu(in_pu_u), .input_pd(in_pd_u),
        .bidir_cs(b_cs_u), .bidir_sl(b_sl_u), .bidir_ie(b_ie_u),
        .bidir_pu(b_pu_u), .bidir_pd(b_pd_u)
    );
    wire unused_strap = ^{in_pu_u, in_pd_u, b_cs_u, b_sl_u, b_ie_u, b_pu_u, b_pd_u};
endmodule

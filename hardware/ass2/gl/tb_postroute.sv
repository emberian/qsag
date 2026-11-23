`timescale 1ns/1ps
// 4-state Icarus `-gspecify` verification of the FULL routed 56-pad `chip_top.nl.v` netlist!
module tb_postroute;
    logic clk_drv, rst_n_drv;
    logic [3:0] input_drv;
    logic [7:0] host_data, host_drive;
    logic sck_drv, fram_miso_drv, tamper_n_drv, uart_rx_drv, db_chal_drv, nfc_ask_drv, nfc_clk_drv;
    logic jtag_tdi_drv, jtag_tms_drv, jtag_tck_drv;

    wire clk_PAD = clk_drv;
    wire rst_n_PAD = rst_n_drv;
    wire [3:0] input_PAD = input_drv;
    tri  [37:0] bidir_PAD;
    wire [3:0] analog_PAD;

    for (genvar i = 0; i < 8; i++) begin : g_dq_drv
        assign bidir_PAD[i] = host_drive[i] ? host_data[i] : 1'bz;
    end
    assign bidir_PAD[18] = sck_drv;
    assign bidir_PAD[25] = fram_miso_drv;
    assign bidir_PAD[26] = tamper_n_drv;
    assign bidir_PAD[27] = uart_rx_drv;
    assign bidir_PAD[30] = db_chal_drv;
    assign bidir_PAD[32] = nfc_ask_drv;
    assign bidir_PAD[33] = nfc_clk_drv;
    assign bidir_PAD[35] = jtag_tdi_drv;
    assign bidir_PAD[36] = jtag_tms_drv;
    assign bidir_PAD[37] = jtag_tck_drv;

    chip_top dut (
        .clk_PAD(clk_PAD),
        .rst_n_PAD(rst_n_PAD),
        .input_PAD(input_PAD),
        .bidir_PAD(bidir_PAD),
        .analog_PAD(analog_PAD)
    );

    `include "postroute_probes.svh"

    integer edges = 0, fast_edges = 0, slow_edges = 0;
    always @(clk_drv) edges++;
    always @(posedge `POST_TRNG_FAST .ZN) if (rst_n_drv) fast_edges++;
    always @(posedge `POST_TRNG_SLOW .ZN) if (rst_n_drv) slow_edges++;

    task check64(input string what, input logic [63:0] got, want);
        if (got !== want) $fatal(1, "%s got=%h expected=%h", what, got, want);
    endtask

    task tick(input integer n);
        repeat (n) begin #25; clk_drv = 1; #25; clk_drv = 0; end
    endtask

    task spi_wait(input bit running);
        if (running) tick(4); else #80;
    endtask

    task transfer(input bit running);
        spi_wait(running); sck_drv = 1; spi_wait(running); sck_drv = 0; #20;
    endtask

    task prefix(input logic [7:0] p, input bit running);
        input_drv[3] = 0; host_drive = 8'h01; #40;
        for (int k = 7; k >= 0; k--) begin host_data[0] = p[k]; transfer(running); end
    endtask

    task end_frame;
        input_drv[3] = 1; host_drive = 8'h00; #40;
    endtask

    task send_word(input logic [63:0] w, input int width);
        host_drive = (1 << width) - 1;
        for (int b = 0; b < 8; b++)
            for (int k = 8 - width; k >= 0; k -= width) begin
                host_data = w >> (8 * b + k); transfer(1);
            end
    endtask

    task read_start(input int width);
        prefix(width == 1 ? 8'h02 : width == 4 ? 8'h42 : 8'h82, 1);
        host_drive = 8'h00;
        repeat (8) transfer(1);
    endtask

    task recv_word(input int width, output logic [63:0] w);
        logic [7:0] v, mask;
        mask = (1 << width) - 1;
        for (int b = 0; b < 8; b++) begin
            v = 0;
            for (int k = 8 - width; k >= 0; k -= width) begin
                spi_wait(1);
                sck_drv = 1; #20;
                v = (v << width) | (width == 1 ? {7'd0, bidir_PAD[1]} : (bidir_PAD[7:0] & mask));
                spi_wait(1); sck_drv = 0; #20;
            end
            w[b * 8 +: 8] = v;
        end
    endtask

    task ident(input int width);
        logic [63:0] w;
        prefix(width == 1 ? 8'h00 : width == 4 ? 8'h40 : 8'h80, 1);
        send_word(64'h0151, width); end_frame(); tick(12);
        check64("IDENT IRQ", bidir_PAD[20], 1);
        read_start(width);
        recv_word(width, w); check64("IDENT header", w, 64'h20018151);
        recv_word(width, w); check64("IDENT banner", w, 64'h3038314432535341);
        recv_word(width, w); check64("IDENT ARCH_ID", w, 64'h4153533200000001);
        recv_word(width, w); check64("IDENT LC/status/count", w, 64'h00000000c0000000);
        recv_word(width, w); check64("IDENT cycles", w, 64'd0);
        end_frame();
        $display("POST-ROUTE IDENT x%0d PASS", width);
    endtask

    logic [63:0] w;
    integer saved, scrub_cycles, bad_boot_bytes = 0;
    realtime tamper_time, wipe_latency, verdict_latency;
    bit watch_wipe;
    always @(secret_q) if (watch_wipe && secret_q === '0)
        wipe_latency = $realtime - tamper_time;
    always @(bidir_PAD[17:16]) if (watch_wipe && bidir_PAD[17:16] === 2'b10)
        verdict_latency = $realtime - tamper_time;

    initial begin
        #2;
        for (int a = 0; a < 512; a++) begin
            `POST_DRAM .mem[a] = 'x;
        end
        `POST_DRAM .qo_reg = 'x;
        #10;
        if (!all_ffs_x() || secret_q !== {2560{1'bx}} || vault_q !== {448{1'bx}})
            $fatal(1, "post-route storage did not start X");

        clk_drv = 0; rst_n_drv = 1; input_drv = 4'h8;
        sck_drv = 0; fram_miso_drv = 0; tamper_n_drv = 1; uart_rx_drv = 1;
        db_chal_drv = 0; nfc_ask_drv = 0; nfc_clk_drv = 0;
        jtag_tdi_drv = 0; jtag_tms_drv = 0; jtag_tck_drv = 0;
        host_drive = 0; host_data = 0;
        #20; rst_n_drv = 0; #20;
        tick(4); #10;
        if (!all_ros_one()) $fatal(1, "reset did not resolve all 514 physical ROs");
        if (secret_q !== '0 || vault_q !== '0) $fatal(1, "reset did not clear 2560+448 latches");

        rst_n_drv = 1; #10;
        for (scrub_cycles = 0; scrub_cycles < 250000 && bidir_PAD[19] === 1'b0; scrub_cycles++) begin
            check64("scrub+POST VERIFY/FAULT/RDY", {bidir_PAD[16], bidir_PAD[17], bidir_PAD[19]}, 0);
            tick(1); #1;
        end
        #10;
        if (scrub_cycles < 512) $fatal(1, "HOST_RDY asserted too early (%0d clocks)", scrub_cycles);
        check64("ready VERIFY/FAULT/RDY", {bidir_PAD[16], bidir_PAD[17], bidir_PAD[19]}, 1);
        for (int a = 0; a < 512; a++)
            if (`POST_DRAM .mem[a] !== 8'h00) bad_boot_bytes++;
        if (bad_boot_bytes) $fatal(1, "boot scrub left %0d non-zero bytes", bad_boot_bytes);
        $display("POST-ROUTE GATE 1 PASS: full 30r Poseidon2 + 24r Keccak POST KAT + 512B scrub in %0d clocks", scrub_cycles);

        // Clockless DIAG through real Schmitt/bidir pads
        saved = edges;
        prefix(8'h05, 0); host_drive = 0;
        repeat (8) transfer(0);
        for (int k = 63; k >= 0; k--) begin
            #80; sck_drv = 1; #20; w[k] = bidir_PAD[1]; #60; sck_drv = 0; #20;
        end
        end_frame();
        check64("POST-ROUTE DIAG", w, 64'h5a03_0000_0000_a552);
        if (edges != saved || clk_drv !== 0) $fatal(1, "DIAG moved core clock");
        if (fast_edges < 2 || slow_edges < 2) $fatal(1, "CoSO rings failed to oscillate");
        $display("POST-ROUTE GATE 2 PASS: clockless DIAG=%h, CoSO rings oscillating", w);

        ident(1); ident(4); ident(8);

        // Resident EXEC + bank_test seed + 0-clock stopped-CLK tamper wipe through physical pads!
        prefix(8'h80, 1); send_word(64'h07d0_000008_07_31_51, 8); send_word(0, 8); end_frame();
        tick(3200); #40;
        check64("EXEC VERIFY/FAULT/IRQ/RDY", {bidir_PAD[16], bidir_PAD[17], bidir_PAD[20], bidir_PAD[19]}, 4'b1011);
        read_start(8); recv_word(8, w); check64("EXEC header", w, 64'ha001b151);
        for (int i = 0; i < 20; i++) recv_word(8, w);
        end_frame();
        $display("POST-ROUTE GATE 3 PASS: resident EXEC verified");

        prefix(8'h80, 1);
        send_word(64'h0000_000008_05_31_51, 8);
        send_word(64'h100, 8);
        end_frame();
        tick(3200); #40;
        check64("bank BIST ready and IRQ", {bidir_PAD[19], bidir_PAD[20]}, 2'b11);
        if (secret_q !== {2560{1'b1}}) $fatal(1, "seed failed: ones=%0d", $countones(secret_q));

        saved = edges;
        tamper_time = $realtime; watch_wipe = 1;
        tamper_n_drv = 0; #40;
        if (secret_q !== '0 || vault_q !== '0) $fatal(1, "post-route tamper Qs not zero");
        check64("tamper VERIFY/FAULT", {bidir_PAD[16], bidir_PAD[17]}, 2'b01);
        #120;
        if (secret_q !== '0 || vault_q !== '0 || clk_drv !== 0 || edges != saved)
            $fatal(1, "stopped-clock tamper unstable");
        $display("POST-ROUTE GATE 4 PASS: 2560 regbank + 448 vault .Q -> 0 in +%0.3f ns (verdict +%0.3f ns), CLK edges=0",
                 wipe_latency, verdict_latency);
        $finish;
    end
endmodule

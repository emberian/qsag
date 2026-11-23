`timescale 1ns/1ps
module tb;
    logic clk, rst_n;
    logic [3:0] input_in;
    logic [37:8] inputs;
    logic [7:0] host_data, host_drive;
    wire [3:0] input_pu, input_pd;
    wire [37:0] bidir_out, bidir_oe, bidir_cs, bidir_sl, bidir_ie, bidir_pu, bidir_pd;
    tri [7:0] dq;
    for (genvar i=0; i<8; i++) begin
        assign dq[i] = host_drive[i] ? host_data[i] : 1'bz;
        assign dq[i] = bidir_oe[i] ? bidir_out[i] : 1'bz;
    end
    wire [37:0] bidir_in = {inputs, dq};
    qsag_ass2_enclave_top dut (.*);
    `include "physical.svh"
    `include "rom_oracle.svh"
    `define DRAM dut.\u_dsram.u_macro 
    wire [273:0] outputs = {input_pu, input_pd, bidir_out, bidir_oe,
                            bidir_cs, bidir_sl, bidir_ie, bidir_pu, bidir_pd};
    integer edges=0, reset_rises=0;
    always @(clk) edges++;
    always @(posedge clk) begin
        if (rst_n === 1'b1) reset_rises++;
    end
    task check64(input string what, input logic [63:0] got, want);
        if (got !== want) $fatal(1,"%s got=%h expected=%h",what,got,want);
    endtask
    // The clock only moves inside tick. SPI setup, sampling and falling edges
    // are separated from core rising edges and from cell propagation delays.
    task tick(input integer n);
        repeat(n) begin #25; clk=1; #25; clk=0; end
    endtask
    task spi_wait(input bit running);
        if (running) tick(4); else #80;
    endtask
    task transfer(input bit running);
        spi_wait(running); inputs[18]=1; spi_wait(running); inputs[18]=0; #20;
    endtask
    task prefix(input logic [7:0] p, input bit running);
        input_in[3]=0; host_drive=1; #40;
        for (int k=7;k>=0;k--) begin host_data[0]=p[k]; transfer(running); end
    endtask
    task end_frame;
        input_in[3]=1; host_drive=0; #40;
        check64("DQ released",bidir_oe[7:0],0);
        if (dq !== 8'hzz) $fatal(1,"DQ did not float in idle: %h",dq);
    endtask
    task send_word(input logic [63:0] w, input int width);
        host_drive=(1<<width)-1;
        for (int b=0;b<8;b++)
            for (int k=8-width;k>=0;k-=width) begin
                host_data=w>>(8*b+k); transfer(1);
            end
    endtask
    task read_start(input int width);
        prefix(width==1 ? 8'h02 : width==4 ? 8'h42 : 8'h82,1);
        host_drive=0;
        repeat(8) transfer(1);
    endtask
    task recv_word(input int width, output logic [63:0] w);
        logic [7:0] v, mask;
        mask=(1<<width)-1;
        for (int b=0;b<8;b++) begin
            v=0;
            for (int k=8-width;k>=0;k-=width) begin
                spi_wait(1);
                check64("read output enables",bidir_oe[7:0],width==1 ? 2 : mask);
                inputs[18]=1;
                v=(v<<width) | (width==1 ? {7'd0,dq[1]} : (dq & mask));
                spi_wait(1); inputs[18]=0; #20;
            end
            w[b*8+:8]=v;
        end
    endtask
    // The body[2] read request is issued at the last rising SCK of body[0].
    // Two synchronizer stages precede its capture on the third core edge.
    task ident(input int width);
        logic [63:0] w;
        
        prefix(width==1 ? 8'h00 : width==4 ? 8'h40 : 8'h80,1);
        send_word(64'h0151,width); end_frame(); tick(12);
        check64("IDENT IRQ",bidir_out[20],1);
        read_start(width);
        recv_word(width,w); check64("IDENT header",w,64'h20018151);
        recv_word(width,w); check64("IDENT banner",w,64'h3038314432535341);

        recv_word(width,w); check64("IDENT ARCH_ID",w,64'h4153533200000001);
        recv_word(width,w); check64("IDENT LC/status/count",w,64'h00000000c0000000);
        recv_word(width,w); check64("IDENT cycles",w,0);
        end_frame();
        $display("IDENT x%0d PASS header + 4 words, status valid count=0",width);
    endtask
    task seed_rows;
        prefix(8'h80,1);
        send_word(64'h0000_000008_05_31_51,8);
        send_word(64'h100,8);
        end_frame();
        tick(2400); #40;
        check64("bank BIST ready and IRQ",{bidir_out[19],bidir_out[20]},3);
    endtask

    logic [63:0] w, want;
    integer saved, scrub_cycles, bad_boot_bytes=0, bad_exec_words=0;
    bit watch_rom, watch_wipe;
    realtime tamper_time, wipe_latency, verdict_latency;
    always @(secret_q) if (watch_wipe && secret_q === '0)
        wipe_latency=$realtime-tamper_time;
    always @(bidir_out[17:16]) if (watch_wipe && bidir_out[17:16] === 2'b10)
        verdict_latency=$realtime-tamper_time;
    integer retired=0;
    always @(posedge clk) if (watch_rom && dut.\u_core.u_instret.en ) begin
        check64("resident retirement PC",{47'd0,dut.core_pc[16:0]},ident_pc(retired));
        $display("I-ROM retire[%0d] PC=%h",retired,{47'd0,dut.core_pc[16:0]});
        retired++;
    end
    integer fast_edges=0, slow_edges=0;
    always @(posedge dut.\u_trng.u_fast.u_gate .ZN) if (rst_n) fast_edges++;
    always @(posedge dut.\u_trng.u_slow.u_gate .ZN) if (rst_n) slow_edges++;
    initial begin
        #2;
        for (int a=0;a<512;a++) begin
            `DRAM .mem[a]='x;
        end
        `DRAM .qo_reg='x;
        #10;
        if (!all_ffs_x() || secret_q !== {2560{1'bx}} || vault_q !== {448{1'bx}})
            $fatal(1,"mapped storage did not start X");
        for (int a=0;a<512;a++)
            if (`DRAM .mem[a] !== 8'hxx)
                $fatal(1,"cold SRAM byte %0d",a);
        $display("COLD: %0d flip-flops, 2560 regbank + 448 vault secret Qs and 512 D-SRAM bytes X",NUM_FFS);
        clk=0; rst_n=1; input_in=4'h8; inputs=0; inputs[26]=1; inputs[27]=1;
        host_drive=0; host_data=0; #20; rst_n=0; #20;
        tick(4); #10;
        check64("reset OE",bidir_oe,0);
        check64("reset SRAM deselect", `DRAM .CEN, 1);
        if (!all_ros_one()) $fatal(1,"reset did not resolve every physical ring");
        if (secret_q !== '0 || vault_q !== '0) $fatal(1,"reset secret/vault Q");
        rst_n=1; #10;
        for (scrub_cycles=0;scrub_cycles<200000 && bidir_out[19]===1'b0;scrub_cycles++) begin
            if ((^outputs) === 1'bx) $fatal(1,"released output X/Z: %h",outputs);
            check64("scrub+POST VERIFY/FAULT/RDY",{bidir_out[16],bidir_out[17],bidir_out[19]},0);
            tick(1); #1;
        end
        #10;
        if (scrub_cycles < 512) $fatal(1,"HOST_RDY asserted too early (%0d clocks)",scrub_cycles);
        if ((^outputs) === 1'bx) $fatal(1,"ready output X/Z: %h",outputs);
        check64("ready VERIFY/FAULT/RDY",{bidir_out[16],bidir_out[17],bidir_out[19]},1);
        for (int a=0;a<512;a++)
            if (`DRAM .mem[a] !== 8'h00) begin
                if (!bad_boot_bytes) $display("First failed boot scrub D-SRAM[%0d]=%h",a,`DRAM .mem[a]);
                bad_boot_bytes++;
            end
        $display("RESET 274 known output bits; full FIPS POST KAT + D-SRAM scrub -> VERIFY/FAULT/RDY=001 after %0d clocks",scrub_cycles);
        if (bad_boot_bytes) $display("GATE 1 FAIL %0d/512 boot scrub bytes uncleared",bad_boot_bytes);
        else $display("GATE 1 PASS 512 zero D-SRAM bytes");
        saved=edges;
        prefix(8'h05,0); host_drive=0;
        repeat(8) transfer(0);
        for (int k=63;k>=0;k--) begin
            #80; check64("DIAG DQ1 OE",bidir_oe[7:0],2);
            inputs[18]=1; w[k]=dq[1]; #80; inputs[18]=0; #20;
        end
        end_frame(); check64("DIAG",w,64'h5a03_0000_0000_a552);
        if (edges!=saved || clk!==0) $fatal(1,"DIAG core clock moved");
        $display("GATE 2 PASS DIAG=%h CLK_IN edges=0",w);
        // All physical rings must resolve on reset. Both free-running CoSO
        // rings must now have produced known rising edges in the timed model.
        if (fast_edges < 2 || slow_edges < 2) $fatal(1,"CoSO rings failed to start");
        ident(1); ident(4); ident(8);
        watch_rom=1;
        prefix(8'h80,1); send_word(64'h07d0_000008_07_31_51,8); send_word(0,8); end_frame();
        tick(2400); #40; watch_rom=0;
        check64("resident PC retirement count",retired,IDENT_RETIRED);
        check64("EXEC VERIFY/FAULT/IRQ/RDY",{bidir_out[16],bidir_out[17],bidir_out[20],bidir_out[19]},11);
        read_start(8); recv_word(8,w); check64("EXEC header",w,64'ha001b151);
        for (int i=0;i<20;i++) begin
            case (i)
                0: want=64'h4153533200000001;
                1: want=15;
                16: want=1;
                18: want=IDENT_RETIRED;
                19: want=IDENT_CYCLES;
                default: want=0;
            endcase
            recv_word(8,w);
            if (w !== want) begin
                bad_exec_words++;
                $display("Mismatch EXEC[%0d] expected=%h",i,want);
            end
            $display("EXEC body[%0d]=%016h",i,w);
        end
        end_frame();
        if (bad_exec_words) $display("GATE 3 FAIL %0d/20 EXEC payload words differ",bad_exec_words);
        else $display("GATE 3 PASS resident ROM matched reference retirement PCs; ARCH_ID/FEATURES and all 21 wire words exact");
        prefix(8'h80,1); send_word(64'h0000_000018_01_30_51,8);
        send_word(64'h00050000_00000001,8); send_word(0,8); send_word(0,8);
        end_frame(); read_start(8); recv_word(8,w); end_frame();
        check64("unbooted loader opcode rejected",w,64'h000d_000000_80_b0_51);
        seed_rows();
        if (secret_q !== {2560{1'b1}}) $fatal(1,"seed failed, ones=%0d",$countones(secret_q));
        check64("pre-tamper VERIFY/FAULT",{bidir_out[16],bidir_out[17]},2);
        saved=edges;
        tamper_time=$realtime; watch_wipe=1;
        inputs[26]=0; #40;
        if (secret_q !== '0 || vault_q !== '0) $fatal(1,"tamper Qs not all zero");
        check64("tamper VERIFY/FAULT",{bidir_out[16],bidir_out[17]},1);
        check64("tamper verdict drivers",bidir_oe[17:16],3);
        #120;
        if (secret_q !== '0) $fatal(1,"stopped wipe unstable, nonzero=%0d", $countones(secret_q));
        if (clk!==0 || edges!=saved) $fatal(1,"clock moved: clk=%b edges=%0d saved=%0d",clk,edges,saved);
        check64("held tamper VERIFY/FAULT",{bidir_out[16],bidir_out[17]},1);
        $display("Specify propagation: all Q zero at +%0.3f ns; verdict at +%0.3f ns",wipe_latency,verdict_latency);
        $display("GATE 4 PASS 2560/2560 physical .Q: 1 -> 0; VERIFY/FAULT: 10 -> 01; CLK_IN edges=0");
        if (bad_boot_bytes || bad_exec_words)
            $fatal(1,"boot scrub mismatches=%0d, EXEC payload mismatches=%0d",bad_boot_bytes,bad_exec_words);
        $finish;
    end
endmodule

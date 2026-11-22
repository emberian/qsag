`timescale 1ps / 1ps
`default_nettype none
module tagGate64_fabric_tb ();
    wire [239:0] I_top;
    wire [239:0] T_top;
    reg  [239:0] O_top = 240'b0;
    reg          CLK = 1'b0;
    reg          resetn = 1'b1;
    reg          self_write_strobe = 1'b0;
    reg  [31:0]  self_write_data = 32'b0;
    wire         com_active, receive_led;

    eFPGA_top top_i (
        .I_top(I_top), .T_top(T_top), .O_top(O_top),
        .CLK(CLK), .resetn(resetn), .SelfWriteStrobe(self_write_strobe), .SelfWriteData(self_write_data),
        .Rx(1'b1), .ComActive(com_active), .ReceiveLED(receive_led), .s_clk(1'b0), .s_data(1'b0)
    );

    localparam integer MAX_BITBYTES = 32768;
    localparam integer MAX_VEC = 4096;
    reg [7:0]  bitstream [0:MAX_BITBYTES-1];
    reg [63:0] vec [0:MAX_VEC-1];
    reg [2047:0] bitstream_hex_arg, vectors_arg;
    integer i, t, ncycles, errors, checked, nbytes;
    reg [63:0] got;
    reg [63:0] ctrl_w, a_w, b_w, exp_tag;

    always #500000 CLK = (CLK === 1'b0);

    task drive(input [63:0] ctrl, input [63:0] a_in, input [63:0] b_in);
        integer k;
        begin
            O_top[239 - 0] = ctrl[0];
            for (k = 0; k < 64; k = k + 1) O_top[239 - (1 + k)] = a_in[k];
            for (k = 0; k < 64; k = k + 1) O_top[239 - (65 + k)] = b_in[k];
            O_top[239 - 129] = ctrl[1];
        end
    endtask

    initial begin
        for (i = 0; i < MAX_BITBYTES; i = i + 1) bitstream[i] = 8'h00;
        if (!$value$plusargs("bitstream_hex=%s", bitstream_hex_arg)) begin $display("no +bitstream_hex"); $fatal; end
        if (!$value$plusargs("vectors=%s", vectors_arg)) begin $display("no +vectors"); $fatal; end
        if (!$value$plusargs("cycles=%d", ncycles)) begin $display("no +cycles"); $fatal; end
        if (!$value$plusargs("bitbytes=%d", nbytes)) nbytes = MAX_BITBYTES;
        $readmemh(bitstream_hex_arg, bitstream);
        $readmemh(vectors_arg, vec);
        #100; resetn = 1'b0; #10000; resetn = 1'b1; #10000;
        repeat (20) @(posedge CLK);
        #2500;
        for (i = 0; i < nbytes; i = i + 4) begin
            self_write_data <= {bitstream[i], bitstream[i+1], bitstream[i+2], bitstream[i+3]};
            repeat (2) @(posedge CLK);
            self_write_strobe <= 1'b1;
            @(posedge CLK);
            self_write_strobe <= 1'b0;
            repeat (2) @(posedge CLK);
        end
        repeat (10) @(posedge CLK);
        errors = 0; checked = 0;
        for (t = 0; t < ncycles; t = t + 1) begin
            @(negedge CLK);
            ctrl_w = vec[4*t + 0];
            a_w    = vec[4*t + 1];
            b_w    = vec[4*t + 2];
            exp_tag = vec[4*t + 3];
            drive(ctrl_w, a_w, b_w);
            #250000;
            for (i = 0; i < 64; i = i + 1) got[i] = I_top[239 - (130 + i)];
            if (t > 0) begin
                checked = checked + 1;
                if (got !== exp_tag) begin
                    errors = errors + 1;
                    if (errors <= 10) $display("cycle %0d: fabric tag=%h lean=%h", t, got, exp_tag);
                end
                for (i = 0; i < 64; i = i + 1) begin
                    if (T_top[239 - (130 + i)] !== 1'b1) begin
                        errors = errors + 1;
                        if (errors <= 10) $display("cycle %0d: tag[%0d] pad not driven", t, i);
                    end
                end
            end
        end
        $display("fabric-sim: cycles=%0d checked=%0d mismatches=%0d", ncycles, checked, errors);
        if (errors != 0) $fatal;
        $finish;
    end
endmodule
`resetall

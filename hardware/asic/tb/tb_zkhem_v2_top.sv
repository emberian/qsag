// Command-port-only verifier bench. With +reply=FIFO, check mode 2 returns
// a hardware response to a live Rust verifier before it chooses its next command.
`timescale 1ns/1ps
module tb_zkhem_v2_top;
  bit clk, rst = 1, cmd_valid;
  always #1 clk = ~clk;
  wire cmd_ready, rsp_valid;
  logic [7:0] cmd_op;
  logic [4:0] cmd_idx;
  logic [23:0] cmd_addr;
  logic [63:0] cmd_data;
  wire [63:0] rsp_data;
  qsag_ni_asic_top dut (.*);

  int fd, reply, checks, commands, mode, parsed, cycles;
  logic [63:0] expected;
  string trace_name, reply_name;
  initial begin
    if (!$value$plusargs("trace=%s", trace_name)) trace_name = "vec/trace_v2.hex";
    fd = $fopen(trace_name, "r");
    if (fd == 0) $fatal(1,"cannot open command stream %s",trace_name);
    if ($value$plusargs("reply=%s",reply_name)) begin
      reply = $fopen(reply_name,"w");
      if (reply == 0) $fatal(1,"cannot open response stream");
    end
    repeat (4) @(negedge clk);
    rst = 0;
    forever begin
      parsed = $fscanf(fd,"%h %h %h %h %h %h",cmd_op,cmd_idx,cmd_addr,cmd_data,mode,expected);
      if (parsed != 6) $fatal(1,"truncated stream at command %0d",commands);
      if (cmd_op == 8'hff) break;
      if (!cmd_ready) $fatal(1,"command port did not become ready");
      cmd_valid = 1;
      @(negedge clk);
      cmd_valid = 0;
      cycles = 0;
      while (!rsp_valid) begin
        @(negedge clk);
        cycles++;
        if (cycles > 4000000) $fatal(1,"timeout op %h after %0d commands",cmd_op,commands);
      end
      if (mode == 1) begin
        checks++;
        if (rsp_data !== expected)
          $fatal(1,"cmd %0d op %h idx %d addr %h got %h expected %h",
                 commands,cmd_op,cmd_idx,cmd_addr,rsp_data,expected);
      end
      if (mode == 2) begin
        if (reply == 0) $fatal(1,"reply requested on a file trace");
        $fdisplay(reply,"%016h",rsp_data);
        $fflush(reply);
      end
      commands++;
    end
    if (checks == 0 && reply == 0) $fatal(1,"empty trace");
    $display("V2 PASS commands=%0d checked=%0d",commands,checks);
    $finish;
  end
endmodule

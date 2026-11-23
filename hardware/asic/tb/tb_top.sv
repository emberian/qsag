// Streaming valid/ready trace-driven co-simulation of qsag_ni_asic_top.
// Drives commands synchronously on negedge clk with zero-bubble II = 1 throughput!
`timescale 1ns/1ps
module tb_top;
  bit clk;
  logic rst = 1;
  always #1 clk = ~clk;

  logic        cmd_valid = 0;
  wire         cmd_ready;
  logic [7:0]  cmd_op = 0;
  logic [4:0]  cmd_idx = 0;
  logic [23:0] cmd_addr = 0;
  logic [63:0] cmd_data = 0;
  wire         rsp_valid;
  wire  [63:0] rsp_data;
  qsag_ni_asic_top #(.AUTO_VERIFY(0)) dut (.*);

  bit [63:0] cyc;
  longint mark_cyc = 0, cmds = 0, mark_cmds = 0, checks = 0, errors = 0;
  always @(posedge clk) cyc <= cyc + 1;

  typedef struct packed {
    logic        chk;
    logic [7:0]  op;
    logic [4:0]  idx;
    logic [23:0] addr;
    logic [63:0] exp;
    longint      seq;
  } exp_t;
  exp_t rsp_q [$];

  task automatic check_rsp();
    if (!rst && rsp_valid) begin
      if (rsp_q.size() == 0) begin
        $display("UNEXPECTED rsp_valid at cyc %0d", cyc);
        errors++;
      end else begin
        exp_t item = rsp_q.pop_front();
        if (item.chk) begin
          checks++;
          if (rsp_data !== item.exp) begin
            errors++;
            if (errors < 20)
              $display("MISMATCH cmd %0d op=%h idx=%0d addr=%h got=%h exp=%h",
                       item.seq, item.op, item.idx, item.addr, rsp_data, item.exp);
          end
        end
      end
    end
  endtask

  // Start each rejection with a clean status. Sample the sticky bit on the
  // accepting edge and independently read it back through the command port.
  task automatic reject_op(input logic [7:0] retired);
    cmd_valid = 1; cmd_op = 8'h08; cmd_idx = 1;
    @(negedge clk);
    if (!cmd_ready || !rsp_valid || dut.verify_fail) $fatal(1,"failed to clear status");
    cmd_op = retired; cmd_idx = 0; cmd_data = 1;
    @(negedge clk);
    if (!dut.verify_fail || cmd_ready) $fatal(1,"op %h failed to reject immediately", retired);
    cmd_valid = 0;
    @(negedge clk);
    if (!rsp_valid || rsp_data !== 0 || !cmd_ready) $fatal(1,"op %h reject response", retired);
    cmd_valid = 1; cmd_op = 8'h0b;
    @(negedge clk);
    if (!rsp_valid || rsp_data !== 0) $fatal(1,"op %h reject status", retired);
    cmd_valid = 0;
    $display("FAIL-CLOSED op=%h", retired);
  endtask

  int fd;
  logic [7:0]  op;
  logic [4:0]  idx;
  logic [23:0] addr;
  logic [63:0] data, exp;
  logic [3:0]  chk;
  string trace;

  initial begin
    if (!$value$plusargs("trace=%s", trace)) trace = "vec/trace_kat.hex";
    fd = $fopen(trace, "r");
    if (fd == 0) $fatal(1,"cannot open %s", trace);
    repeat (4) @(negedge clk);
    rst = 0;
    @(negedge clk);
    while ($fscanf(fd, "%h %h %h %h %h %h", op, idx, addr, data, chk, exp) == 6) begin
      if (op == 8'hF0) begin
        cmd_valid = 0;
        while (rsp_q.size() > 0 || !cmd_ready) begin
          @(negedge clk);
          check_rsp();
        end
        $display("MARK tag=%0d label=%0d cycles=%0d cmds=%0d", data, addr, cyc - mark_cyc, cmds - mark_cmds);
        mark_cyc = cyc; mark_cmds = cmds;
      end else begin
        while (!cmd_ready) begin
          cmd_valid = 0;
          @(negedge clk);
          check_rsp();
        end
        // At negedge clk with cmd_ready == 1: command will handshake at the upcoming posedge clk!
        cmd_valid = 1; cmd_op = op; cmd_idx = idx[4:0]; cmd_addr = addr; cmd_data = data;
        cmds++;
        rsp_q.push_back('{chk: (chk != 0), op: op, idx: idx[4:0], addr: addr, exp: exp, seq: cmds});
        @(negedge clk);
        check_rsp();
      end
    end
    cmd_valid = 0;
    while (rsp_q.size() > 0 || !cmd_ready) begin
      @(negedge clk);
      check_rsp();
    end
    $display("tb_top %s: %0d commands, %0d checked words, %0d errors, %0d cycles", trace, cmds, checks, errors, cyc);
    if (errors != 0 || checks == 0) $fatal(1,"invalid KAT result");
    for (int i='h20; i<='h27; i++) if (i!='h23) reject_op(8'(i));
    reject_op(8'h50);
    $display("TB_TOP PASS");
    $finish;
  end
endmodule

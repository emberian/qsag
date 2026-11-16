// Trace-driven co-simulation of qsag_ni_asic_top. Each trace line (hex):
//   op idx addr data chk exp
// is one command; with chk = 1 the response word must equal exp. op = F0 is a marker: it prints
// the clock cycles and commands since the previous marker (tag = data, addr = free label).
`timescale 1ns/1ps
module tb_top;
  parameter int AW = 18;
  logic clk = 0, rst = 1;
  always #1 clk = ~clk;

  logic        cmd_valid = 0;
  wire         cmd_ready;
  logic [7:0]  cmd_op = 0;
  logic [4:0]  cmd_idx = 0;
  logic [23:0] cmd_addr = 0;
  logic [63:0] cmd_data = 0;
  wire         rsp_valid;
  wire  [63:0] rsp_data;
  qsag_ni_asic_top #(.AW(AW)) dut (.*);

  longint cyc = 0, mark_cyc = 0, cmds = 0, mark_cmds = 0, checks = 0, errors = 0;
  always @(posedge clk) cyc++;

  int fd;
  logic [7:0]  op;
  logic [7:0]  idx;
  logic [23:0] addr;
  logic [63:0] data, exp;
  logic [3:0]  chk;
  string trace;

  initial begin
    if (!$value$plusargs("trace=%s", trace)) trace = "vec/trace_kat.hex";
    fd = $fopen(trace, "r");
    if (fd == 0) begin $display("cannot open %s", trace); $finish; end
    repeat (4) @(negedge clk);
    rst = 0;
    @(negedge clk);
    while ($fscanf(fd, "%h %h %h %h %h %h", op, idx, addr, data, chk, exp) == 6) begin
      if (op == 8'hF0) begin
        $display("MARK tag=%0d label=%0d cycles=%0d cmds=%0d", data, addr, cyc - mark_cyc, cmds - mark_cmds);
        mark_cyc = cyc; mark_cmds = cmds;
      end else begin
        if (!cmd_ready) begin $display("PROTOCOL ERROR: not ready"); errors++; end
        cmd_valid = 1; cmd_op = op; cmd_idx = idx[4:0]; cmd_addr = addr; cmd_data = data;
        @(negedge clk);
        cmd_valid = 0;
        while (!rsp_valid) @(negedge clk);
        cmds++;
        if (chk != 0) begin
          checks++;
          if (rsp_data !== exp) begin
            errors++;
            if (errors < 20) $display("MISMATCH cmd %0d op=%h idx=%0d addr=%h got=%h exp=%h", cmds, op, idx, addr, rsp_data, exp);
          end
        end
      end
    end
    $display("tb_top %s: %0d commands, %0d checked words, %0d errors, %0d cycles", trace, cmds, checks, errors, cyc);
    if (errors == 0 && checks > 0) $display("TB_TOP PASS"); else $display("TB_TOP FAIL");
    $finish;
  end
endmodule

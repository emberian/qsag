// Leaf-block KAT co-simulation: every combinational unit against vectors written by
// gen/gen_vectors.py (fixture KATs, edge values and random values from the Python reference).
`timescale 1ns/1ps
module tb_units;
  int errors = 0, checks = 0, fd, n;
  logic [63:0]  a, b, r_exp;
  wire  [63:0]  r_csa, r_ref;
  qsag_gl64_mul_csa u_mul (.a(a), .b(b), .r(r_csa));
  qsag_gl64_mul_ref u_mulref (.a(a), .b(b), .r(r_ref));

  logic [127:0] v;
  wire  [63:0]  red_csa, red_ref;
  qsag_gl64_reduce128_csa u_red (.v(v), .r(red_csa));
  qsag_gl64_reduce128_ref u_redref (.v(v), .r(red_ref));

  logic [767:0] lx, lrc, ly_exp;
  wire  [767:0] me_y, mi_y;
  qsag_p2_me u_me (.x(lx), .rc(lrc), .y(me_y));
  qsag_p2_mi u_mi (.x(lx), .rc(lrc), .y(mi_y));

  logic [127:0] ga, gb, g_exp;
  wire  [127:0] g_poly, g_tower;
  qsag_gf128_mul u_gf (.a(ga), .b(gb), .r(g_poly));
  qsag_tower128_mul u_tw (.a(ga), .b(gb), .r(g_tower));

  logic [1599:0] ka, k_exp;
  logic [63:0]   krc;
  wire  [1599:0] ko;
  qsag_keccak_round u_kr (.a(ka), .rc(krc), .o(ko));

  task automatic bad(input string what);
    errors++;
    if (errors < 20) $display("MISMATCH %s (check %0d)", what, checks);
  endtask

  initial begin
    fd = $fopen("vec/glmul.hex", "r"); n = 0;
    while ($fscanf(fd, "%h %h %h", a, b, r_exp) == 3) begin
      #1; checks++; n++;
      if (r_csa !== r_exp) bad("gl64_mul_csa");
      if (r_ref !== r_exp) bad("gl64_mul_ref");
    end
    $fclose(fd); $display("gl64 mul: %0d vectors", n);

    fd = $fopen("vec/red128.hex", "r"); n = 0;
    while ($fscanf(fd, "%h %h", v, r_exp) == 2) begin
      #1; checks++; n++;
      if (red_csa !== r_exp) bad("reduce128_csa");
      if (red_ref !== r_exp) bad("reduce128_ref");
    end
    $fclose(fd); $display("reduce128: %0d vectors", n);

    fd = $fopen("vec/me.hex", "r"); n = 0;
    while ($fscanf(fd, "%h %h %h", lx, lrc, ly_exp) == 3) begin
      #1; checks++; n++;
      if (me_y !== ly_exp) bad("p2_me");
    end
    $fclose(fd); $display("p2 M_E: %0d vectors", n);

    fd = $fopen("vec/mi.hex", "r"); n = 0;
    while ($fscanf(fd, "%h %h %h", lx, lrc, ly_exp) == 3) begin
      #1; checks++; n++;
      if (mi_y !== ly_exp) bad("p2_mi");
    end
    $fclose(fd); $display("p2 M_I: %0d vectors", n);

    fd = $fopen("vec/gfpoly.hex", "r"); n = 0;
    while ($fscanf(fd, "%h %h %h", ga, gb, g_exp) == 3) begin
      #1; checks++; n++;
      if (g_poly !== g_exp) bad("gf128_mul");
    end
    $fclose(fd); $display("gf128 poly mul: %0d vectors", n);

    fd = $fopen("vec/gftower.hex", "r"); n = 0;
    while ($fscanf(fd, "%h %h %h", ga, gb, g_exp) == 3) begin
      #1; checks++; n++;
      if (g_tower !== g_exp) bad("tower128_mul");
    end
    $fclose(fd); $display("tower128 mul: %0d vectors", n);

    fd = $fopen("vec/keccak_round.hex", "r"); n = 0;
    while ($fscanf(fd, "%h %h %h", ka, krc, k_exp) == 3) begin
      #1; checks++; n++;
      if (ko !== k_exp) bad("keccak_round");
    end
    $fclose(fd); $display("keccak round: %0d vectors", n);

    $display("tb_units: %0d checks, %0d errors", checks, errors);
    if (errors == 0) $display("TB_UNITS PASS"); else $display("TB_UNITS FAIL");
    $finish;
  end
endmodule

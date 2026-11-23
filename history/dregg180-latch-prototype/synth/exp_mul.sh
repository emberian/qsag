#!/bin/sh
# Multiplier mapping experiment (remote): default vs Booth vs full-adder cell extraction.
LIBDIR=$(ls -d /work/template/gf180mcu/ciel/gf180mcu/versions/*/gf180mcuD/libs.ref/gf180mcu_fd_sc_mcu7t5v0/lib)
LIB=$LIBDIR/gf180mcu_fd_sc_mcu7t5v0__tt_025C_5v00.lib
for c in addf_1 addh_1 nand2_1 xor2_1 xor3_1 mux2_1 dffq_1 dffrnq_1 latq_1 icgtp_2; do
  awk -v c="cell(gf180mcu_fd_sc_mcu7t5v0__$c)" '$1==c {f=1} f && /area/ {gsub(/[;]/,""); printf "%s %s um^2 (%.2f GE)\n", c, $3, $3/8.7808; f=0}' $LIB
done
cat > build/fa_map.v <<'V'
module \$fa (A, B, C, X, Y);
  parameter WIDTH = 1;
  input [WIDTH-1:0] A, B, C;
  output [WIDTH-1:0] X, Y;
  genvar i;
  generate for (i = 0; i < WIDTH; i = i + 1) begin : g
    gf180mcu_fd_sc_mcu7t5v0__addf_1 fa (.A(A[i]), .B(B[i]), .CI(C[i]), .CO(X[i]), .S(Y[i]));
  end endgenerate
endmodule
V
run() {
  tag=$1; shift
  cat > build/exp_$tag.ys <<YS
read_liberty -lib -ignore_miss_dir -setattr blackbox $LIB
read_verilog -sv rtl/qsag_gl64_karatsuba_csa.sv
hierarchy -top qsag_mul33
$*
dfflibmap -liberty $LIB
abc -liberty $LIB -D 12000
opt_clean -purge
tee -o build/exp_$tag.stat stat -liberty $LIB
YS
  yosys -q build/exp_$tag.ys > build/exp_$tag.log 2>&1 || tail -5 build/exp_$tag.log
  awk -v t=$tag '/Chip area/ {printf "%-12s %.2f kGE\n", t, $NF/8.7808/1000}' build/exp_$tag.stat
}
run default "synth -top qsag_mul33 -flatten"
run booth   "synth -top qsag_mul33 -flatten -booth"
run boothfa "synth -top qsag_mul33 -flatten -booth; extract_fa -fa; techmap -map build/fa_map.v; opt_clean"
run fa      "synth -top qsag_mul33 -flatten; extract_fa -fa; techmap -map build/fa_map.v; opt_clean"
grep addf build/exp_fa.stat build/exp_boothfa.stat
grep -A4 "cell(gf180mcu_fd_sc_mcu7t5v0__addf_1)" $LIB | grep area

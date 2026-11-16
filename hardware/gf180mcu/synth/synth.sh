#!/bin/sh
# Yosys synthesis to gf180mcu_fd_sc_mcu7t5v0 (run remotely, cwd = project root).
#   synth/synth.sh <top> <tag> "<verilog files>" ["<extra defines>"]
# Writes build/synth_<tag>.{log,stat,v}; prints area in um^2 and kGE (nand2_1 = 8.7808 um^2).
set -e
TOP=$1; TAG=$2; FILES=$3; DEFS=$4
LIBDIR=$(ls -d /work/proj/gf180mcu/ciel/gf180mcu/versions/*/gf180mcuD/libs.ref/gf180mcu_fd_sc_mcu7t5v0/lib /work/template/gf180mcu/ciel/gf180mcu/versions/*/gf180mcuD/libs.ref/gf180mcu_fd_sc_mcu7t5v0/lib 2>/dev/null | head -1)
LIB=$LIBDIR/gf180mcu_fd_sc_mcu7t5v0__${CORNER:-tt_025C_5v00}.lib
mkdir -p build
cat > build/synth_$TAG.ys <<YS
read_liberty -lib -ignore_miss_dir -setattr blackbox $LIB
read_verilog -sv -DSYNTHESIS -DQSAG_GF180_CELLS -DQSAG_ICG $DEFS $FILES
hierarchy -check -top $TOP
synth -top $TOP -booth ${FLATTEN:--flatten}
opt -purge
dfflibmap -liberty $LIB
abc -liberty $LIB -dont_use gf180mcu_fd_sc_mcu7t5v0__dlya_* -dont_use gf180mcu_fd_sc_mcu7t5v0__dlyb_* -dont_use gf180mcu_fd_sc_mcu7t5v0__dlyc_* -dont_use gf180mcu_fd_sc_mcu7t5v0__dlyd_* ${ABC_OPTS:--D 20000}
opt_clean -purge
hilomap -hicell gf180mcu_fd_sc_mcu7t5v0__tieh Z -locell gf180mcu_fd_sc_mcu7t5v0__tiel ZN
tee -o build/synth_$TAG.stat stat -liberty $LIB
write_verilog -noattr build/synth_$TAG.v
YS
yosys -q -l build/synth_$TAG.log build/synth_$TAG.ys
awk '/Chip area for (top )?module/ {a=$NF} END {printf "%s: %.0f um^2 = %.2f kGE\n", "'$TAG'", a, a/8.7808/1000}' build/synth_$TAG.stat

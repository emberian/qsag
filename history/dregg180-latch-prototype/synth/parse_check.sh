#!/bin/sh
# Yosys front-end check of the synthesis view (remote).
LIB=$(ls -d /work/template/gf180mcu/ciel/gf180mcu/versions/*/gf180mcuD/libs.ref/gf180mcu_fd_sc_mcu7t5v0/lib)/gf180mcu_fd_sc_mcu7t5v0__tt_025C_5v00.lib
yosys -q -p "read_liberty -lib -ignore_miss_dir -setattr blackbox $LIB; read_verilog -sv -DSYNTHESIS -DQSAG_GF180_CELLS -DQSAG_ICG $(cat rtl/qsag_ni_180.f | tr '\n' ' '); hierarchy -check -top chip_core; proc; stat" 2>&1 | grep -v "^$" | head -${1:-30}

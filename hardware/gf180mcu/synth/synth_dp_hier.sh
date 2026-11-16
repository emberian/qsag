#!/bin/sh
# Hierarchical area breakdown of the datapath (remote).
FLATTEN=" " synth/synth.sh dp_top dp_hier "rtl/qsag_cells.sv rtl/qsag_gl64_karatsuba_csa.sv rtl/qsag_sponge.sv rtl/qsag_p2_rc.sv rtl/qsag_field_engine.sv tb/dp_top.sv"
grep -n "^=== \|Chip area for module" build/synth_dp_hier.stat | paste - - | awk '{printf "%-70s %8.2f kGE\n", $2, $NF/8.7808/1000}' | sort -k2 -n -r | head -30
LIB=$(ls -d /work/template/gf180mcu/ciel/gf180mcu/versions/*/gf180mcuD/libs.ref/gf180mcu_fd_sc_mcu7t5v0/lib)/gf180mcu_fd_sc_mcu7t5v0__tt_025C_5v00.lib
grep -n "cell *(" $LIB | head -3

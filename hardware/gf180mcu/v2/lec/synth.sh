#!/bin/bash
# Yosys synthesis of the v2 blocks to gf180mcu_fd_sc_mcu7t5v0, with the recipe of synth/synth.sh
# (flat, -booth, dfflibmap, abc -D 20000, TT 25 C 5 V liberty). Run from the chip directory:
#
#   bash v2/lec/synth.sh <liberty file> [block ...]      default: every block of BLOCKS below
# RTLDIR: another copy of v2/rtl (ablation experiments); SYNOUT: output directory.
#
# Writes build/v2/syn/<block>.{log,stat,v}; v2/lec/area.py prints the table against the budget.
set -e
OSS=${OSS:-/home/build/qsag-ni-fpga/oss-cad-suite}
. "$OSS/environment"
LIB=$1; shift
B=build/v2
O=${SYNOUT:-$B/syn}
R=${RTLDIR:-v2/rtl}
mkdir -p $O
[ -f $B/inc72/dregg_urom.sv ] || { echo "run v2/tb/run.sh gen first"; exit 1; }
SRC="rtl/qsag_cells.sv $B/qsag_p2_rc.sv $R/dregg_gf180_sim.sv $R/dregg_regfile.sv $R/dregg_keccak_serial.sv $R/dregg_word_unit.sv $R/dregg_egress.sv $R/dregg_framer.sv $R/dregg_anchor_spi.sv $R/dregg_fram.sv $R/dregg_rules.sv $R/dregg_seq.sv $R/dregg_rst.sv $R/dregg_core.sv $R/dregg_spi_link.sv $R/dregg_top.sv $B/inc72/dregg_urom.sv"
BLOCKS=${*:-"dregg_regfile dregg_keccak_serial dregg_word_unit dregg_urom dregg_seq dregg_seq@H_SHADOW=0 dregg_seq@IR_STAGE=1 dregg_rules dregg_egress dregg_framer dregg_fram dregg_spi_link dregg_rst dregg_core dregg_top dregg_top@IR_STAGE=1"}
one() {    # block, or block@PARAM=value for a parameter variant (written as block_PARAM_value)
    spec=$1
    mod=${spec%%@*}
    top=$mod
    chp=""
    if [ "$spec" != "$mod" ]; then
        pv=${spec#*@}
        chp="chparam -set ${pv%%=*} ${pv#*=} $mod"
        top=${mod}_$(echo $pv | tr '=' '_')
    fi
    cat > $O/$top.ys <<YS
read_liberty -lib -ignore_miss_dir -setattr blackbox $LIB
read_verilog -sv -DSYNTHESIS -DQSAG_GF180_CELLS -DQSAG_ICG -DQSAG_LATCH_RF -I$B/inc72 $SRC
$chp
hierarchy -check -top $mod
synth -top $mod -booth -noabc -flatten
opt -purge
dfflibmap -liberty $LIB
abc -liberty $LIB -dont_use gf180mcu_fd_sc_mcu7t5v0__dlya_* -dont_use gf180mcu_fd_sc_mcu7t5v0__dlyb_* -dont_use gf180mcu_fd_sc_mcu7t5v0__dlyc_* -dont_use gf180mcu_fd_sc_mcu7t5v0__dlyd_* -D 20000
opt_clean -purge
hilomap -hicell gf180mcu_fd_sc_mcu7t5v0__tieh Z -locell gf180mcu_fd_sc_mcu7t5v0__tiel ZN
tee -o $O/$top.stat stat -top $mod -liberty $LIB
write_verilog -noattr $O/$top.v
YS
    if timeout --kill-after=10s ${SYN_TIMEOUT:-2400}s yosys -q -l $O/$top.log $O/$top.ys > /dev/null 2>&1; then echo "synth $top: done"; else echo "synth $top: FAILED (see $O/$top.log)"; fi
}
pids=""
for b in $BLOCKS; do one $b & pids="$pids $!"; done
for p in $pids; do wait $p; done

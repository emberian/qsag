#!/bin/bash
# SymbiYosys proofs of the small control blocks (ARCHITECTURE.md 8.2). Run from the chip directory:
#   bash v2/lec/run_formal.sh [egress|seq] ...
# Each task is run twice: bounded model checking from reset, and k-induction (an unbounded proof).
set -e
OSS=${OSS:-/home/build/qsag-ni-fpga/oss-cad-suite}
. "$OSS/environment"
B=build/v2
O=$B/fv
mkdir -p $O
st=0
for t in ${*:-egress seq}; do
    for rows in 72 64; do
        for mode in bmc prove; do
            name=${t}_${rows}_$mode
            depth=30; [ $mode = prove ] && depth=${KIND:-3}
            cat > $O/$name.sby <<SBY
[options]
mode $mode
depth $depth
[engines]
smtbmc ${SOLVER:-bitwuzla}
[script]
read_verilog -sv -formal -DSYNTHESIS -DFORMAL -I$PWD/$B/inc$rows $PWD/rtl/qsag_cells.sv $PWD/v2/rtl/dregg_rules.sv $PWD/v2/rtl/dregg_seq.sv $PWD/v2/rtl/dregg_egress.sv $PWD/v2/lec/fv_$t.sv
prep -top fv_$t
async2sync
SBY
            if timeout --kill-after=10s ${FV_TIMEOUT:-1500}s sby -f -d $O/$name $O/$name.sby > $O/$name.log 2>&1; then r=PASS; else r=FAIL; st=1; fi
            echo "formal $t, $rows rows, $mode depth $depth: $r ($(grep -c 'assert' $PWD/v2/rtl/dregg_$t.sv) assert statements in dregg_$t.sv; $(tail -1 $O/$name.log | cut -c1-90))"
        done
    done
done
exit $st

#!/bin/sh
# Unit tests of the physical organs touched by the R1 Tier-B fixes (remote, cwd = project root).
#   unit_tdc           rapid-bit responder: at most one response bit per round (B3)
#   unit_puf timed     ring-oscillator PUF with oscillating rings (B1)
#   unit_puf stalled   the synthesis view with dead oscillators: must abort (B1)
set -e
mkdir -p build
status=0
V="verilator --cc --exe --build -j 8 -Wall -Wno-DECLFILENAME"
rm -rf build/obj_tdc
$V --top-module dregg_distance_tdc -Mdir build/obj_tdc rtl/qsag_cells.sv rtl/dregg_distance_tdc.sv tb/unit_tdc.cpp -o unit_tdc \
    > build/unit_tdc_build.log 2>&1 || { tail -40 build/unit_tdc_build.log; exit 1; }
build/obj_tdc/unit_tdc || status=1
rm -rf build/obj_puf_t
$V --timing -DQSAG_SIM_DELAYS -O2 -CFLAGS "-O2" --top-module dregg_ro_puf_bch -Mdir build/obj_puf_t rtl/qsag_cells.sv rtl/dregg_ro_puf_bch.sv tb/unit_puf.cpp -o unit_puf \
    > build/unit_puf_t_build.log 2>&1 || { tail -40 build/unit_puf_t_build.log; exit 1; }
build/obj_puf_t/unit_puf timed || status=1
rm -rf build/obj_puf_s
$V --timing -DSYNTHESIS --top-module dregg_ro_puf_bch -Mdir build/obj_puf_s rtl/qsag_cells.sv rtl/dregg_ro_puf_bch.sv tb/unit_puf.cpp -o unit_puf \
    > build/unit_puf_s_build.log 2>&1 || { tail -40 build/unit_puf_s_build.log; exit 1; }
build/obj_puf_s/unit_puf stalled || status=1
exit "$status"

#!/bin/sh
# Full-chip testbench (remote, cwd = project root).
#   tb/run_sim.sh build [extra verilator defines]     compile the timed model
#   tb/run_sim.sh <config> [scenario] [script]        run one configuration
set -e
mkdir -p build
[ -f rtl/qsag_p2_rc.sv ] || python3 scripts/gen_p2_rc.py rtl/qsag_p2_rc.sv > /dev/null
if [ "$1" = build ]; then
    shift
    sh tb/run_model.sh > build/model.log 2>&1 || { cat build/model.log; exit 1; }
    rm -rf build/obj_sim
    verilator --cc --exe --build -j 12 --timing -Wall -Wno-DECLFILENAME -DQSAG_SIM_DELAYS "$@" \
        -O2 -CFLAGS "-O2" --top-module tb_top -Mdir build/obj_sim \
        -f rtl/qsag_ni_180.f tb/tb_top.sv tb/sim_qsag_ni_180.cpp -o sim_qsag_ni_180 > build/sim_build.log 2>&1 \
        || { grep -A6 '%Error\|error:' build/sim_build.log | head -60; exit 1; }
    echo "build ok: $(grep -c '^%Warning' build/sim_build.log) verilator warnings"
    exit 0
fi
status=0
cfg=$1; scen=${2:-script}; script=${3:-build/script_full.txt}
build/obj_sim/sim_qsag_ni_180 $script $cfg $scen > build/sim_${cfg}_${scen}.log 2>&1 || status=$?
grep -v '^  \[ok\]' build/sim_${cfg}_${scen}.log | tail -${TAILN:-25}

exit "$status"

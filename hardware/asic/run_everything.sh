#!/usr/bin/env bash
# bb2 only: regenerate RTL/vectors, run Verilator KAT + real QSAGSTA1/DuetFold traces,
# discharge Obend Lean 4 + 100% compositional LEC suite, and run 4-PDK synthesis + OpenSTA + OpenROAD.
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p logs
export TMPDIR="$PWD/logs"

./run_sim.sh gen   > logs/everything.log 2>&1
./run_sim.sh lint >> logs/everything.log 2>&1
./run_sim.sh units > logs/run_sim_units.log 2>&1
./run_sim.sh top   > logs/run_sim_top.log 2>&1
./obend/run_obend.sh > logs/obend_run.out 2>&1
./lec/run_all.sh     > logs/lec_batch.out 2>&1
./synth/run_all.sh   > logs/synth_all.out 2>&1
echo ALL_DONE >> logs/everything.log

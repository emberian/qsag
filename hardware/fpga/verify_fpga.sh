#!/usr/bin/env bash
# QSAG-NI FPGA verification gate: lint, Verilator differential simulation against the Lean
# oracle vectors, Z3 equivalence proofs. Run on a build box, never on the Mac:
#   source <oss-cad-suite>/environment
#   SWARM_MEM_MAX=16G swarm-build timeout --kill-after=10s 600s ./verify_fpga.sh <step>
# Steps, each sized for one 600 s slot: lint, units, top, lec-gl, lec-glmut, lec-gf, lec-try, lec-anf.
# QSAG_FIXTURE points at validation/tests/fixtures/lean_external_oracle_vectors.json.
set -euo pipefail
cd "$(dirname "$0")"
HERE="$PWD"
FIXTURE="${QSAG_FIXTURE:-$HERE/../../validation/tests/fixtures/lean_external_oracle_vectors.json}"
SRC="$(sed "s|^|$HERE/|" synth/srcs.txt | tr '\n' ' ')"
JOBS="${JOBS:-8}"
what="${1:-all}"
mkdir -p build

kat() { python3 tb/gen_kat.py "$FIXTURE" build/kat_vectors.h; }

sim() {  # sim <UNITS|TOP> <top module> <extra sources>
    local mode="$1" top="$2" extra="${3:-}"
    kat
    verilator --cc --exe --build -j "$JOBS" -Wall -sv -O3 --x-initial unique \
        --Mdir "build/obj_$mode" --top-module "$top" \
        -CFLAGS "-O2 -std=c++17 ${SIM_CFLAGS:-} -DQSAG_$mode -I$HERE/build -I$HERE/tb" \
        $SRC $extra ${SIM_PARAMS:-} "$HERE/tb/sim_qsag_ni_fpga.cpp" -o "sim_$mode" > "build/verilate_$mode.log" 2>&1 \
        || { cat "build/verilate_$mode.log"; exit 1; }
    "build/obj_$mode/sim_$mode" +verilator+rand+reset+2 +verilator+seed+20261116 "build/trace_report_$mode.txt" \
        | tee "build/sim_$mode.log"
}

case "$what" in
    lint)  ./lint.sh ;;
    units) sim UNITS qsag_units_tb "$HERE/tb/qsag_units_tb.sv" ;;
    top)   sim TOP qsag_ni_fpga_top ;;
    compact) SIM_CFLAGS=-DQSAG_COMPACT SIM_PARAMS="-GPROFILE_COMPACT=1 -GFOLD_TAW=11 -GKECCAK_RPC=1 -GAW=16 -GBW=16" sim TOP qsag_ni_fpga_top ;;
    pipe) SIM_CFLAGS=-DQSAG_PIPE SIM_PARAMS="-GP2_UNROLLED=1 -GKECCAK_PIPE=1 -GCHAIN_SLOTW=8" sim TOP qsag_ni_fpga_top ;;
    lec-*) ./lec/lec.sh "${what#lec-}" ;;
    all)   ./lint.sh; sim UNITS qsag_units_tb "$HERE/tb/qsag_units_tb.sv"; sim TOP qsag_ni_fpga_top; ./lec/lec.sh ;;
    *) echo "usage: $0 [lint|units|top|lec-gl|lec-glmut|lec-gf|lec-try|lec-anf|all]"; exit 2 ;;
esac

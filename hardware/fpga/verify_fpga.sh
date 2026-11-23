#!/usr/bin/env bash
# QSAG-NI FPGA verification gate: lint, Verilator differential simulation against the Lean
# oracle vectors, Z3 equivalence proofs. Run on a build box, never on the Mac:
#   scripts/remote_run.sh ./verify_fpga.sh compact
# QSAG_FIXTURE can override the checked-in Lean oracle vectors.
set -euo pipefail
cd "$(dirname "$0")"
HERE="$PWD"
FIXTURE="${QSAG_FIXTURE:-$HERE/tb/fixtures/lean_oracle.json}"
SRC="$(sed "s|^|$HERE/|" synth/srcs.txt | tr '\n' ' ')"
JOBS="${JOBS:-6}"
[[ "$JOBS" =~ ^[1-6]$ ]] || { echo "JOBS must be 1..6" >&2; exit 2; }
what="${1:-all}"
mkdir -p build

kat() { python3 tb/gen_kat.py "$FIXTURE" build/kat_vectors.h; }

sim() {  # sim <tag> <UNITS|TOP> <top module> <extra sources>
    local tag="$1" mode="$2" top="$3" extra="${4:-}"
    kat
    verilator --cc --exe --build -j "$JOBS" -Wall -sv -O3 --x-initial unique \
        --Mdir "build/obj_$tag" --top-module "$top" \
        -CFLAGS "-O2 -std=c++17 ${SIM_CFLAGS:-} -DQSAG_$mode -I$HERE/build -I$HERE/tb" \
        $SRC $extra ${SIM_PARAMS:-} "$HERE/tb/sim_qsag_ni_fpga.cpp" -o "sim_$tag" > "build/verilate_$tag.log" 2>&1 \
        || { cat "build/verilate_$tag.log"; exit 1; }
    "build/obj_$tag/sim_$tag" +verilator+rand+reset+2 +verilator+seed+20261116 "build/trace_report_$tag.txt" \
        | tee "build/sim_$tag.log"
}

case "$what" in
    lint)    ./lint.sh ;;
    units)   sim UNITS UNITS qsag_units_tb "$HERE/tb/qsag_units_tb.sv" ;;
    top)     sim TOP TOP qsag_ni_fpga_top ;;
    ecp5_fullrate) SIM_CFLAGS=-DQSAG_ECP5_FULLRATE SIM_PARAMS="-DQSAG_ECP5_CARRY -GPROFILE_COMPACT=1 -GECP5_FULLRATE=1 -GFOLD_TAW=11 -GKECCAK_RPC=1 -GAW=16 -GBW=16" sim ECP5_FULLRATE TOP qsag_ni_fpga_top ;;
    compact) SIM_CFLAGS=-DQSAG_COMPACT SIM_PARAMS="-DQSAG_ECP5_CARRY -GPROFILE_COMPACT=1 -GFOLD_TAW=11 -GKECCAK_RPC=1 -GAW=16 -GBW=16" sim COMPACT TOP qsag_ni_fpga_top ;;
    pipe)    SIM_CFLAGS=-DQSAG_PIPE SIM_PARAMS="-GP2_UNROLLED=1 -GKECCAK_PIPE=1 -GCHAIN_SLOTW=8" sim PIPE TOP qsag_ni_fpga_top ;;
    lec-*)   ./lec/lec.sh "${what#lec-}" ;;
    all)     for step in lint units compact ecp5_fullrate top pipe; do "$0" "$step"; done; ./lec/lec.sh ;;
    *) echo "usage: $0 [lint|units|top|ecp5_fullrate|compact|pipe|lec-gl|lec-glmut|lec-ext5|lec-gf|lec-tower|lec-comp|lec-anf|all]"; exit 2 ;;
esac

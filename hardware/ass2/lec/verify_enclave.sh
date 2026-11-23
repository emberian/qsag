#!/usr/bin/env bash
# Run from hardware/ass2 on a Linux host after sourcing the OSS CAD environment.
set -euo pipefail
cd "$(dirname "$0")/.."
[[ $(uname -s) == Linux ]]
export TMPDIR="$PWD/tmp"
mkdir -p "$TMPDIR"
work=$(mktemp -d "$TMPDIR/ass2-verify.XXXXXXXX")
trap 'rm -rf "$work"' EXIT
rtl=(rtl/qsag_ass2_pkg.sv)
for f in rtl/*.sv; do [[ $f == "${rtl[0]}" ]] || rtl+=("$f"); done

python3 lec/lec_ass2.py
python3 lec/lec_timing.py
for seed in 19 42; do python3 lec/core_vectors.py "$seed" >"$work/$seed.vec"; done

build_and_run() {
    local top=$1 harness=$2 obj=$3
    shift 3
    echo "Checking $top ($obj)"
    verilator --lint-only -Wall "$@" --top-module "$top" "${rtl[@]}"
    verilator --cc --exe --build -j 3 -Wall "$@" --Mdir "$work/$obj" \
        --top-module "$top" "${rtl[@]}" "$PWD/lec/$harness" >"$work/build.log" || {
        cat "$work/build.log"
        return 1
    }
    if [[ $top == qsag_ass2_core ]]; then
        "$work/$obj/V$top" "$work/19.vec" "$work/42.vec"
    else
        "$work/$obj/V$top"
    fi
}

build_and_run qsag_ass2_core core_sanity.cpp core
build_and_run qsag_ass2_enclave_top enclave_sanity.cpp bram -DUSE_ANALOG_PINS
build_and_run qsag_ass2_enclave_top enclave_sanity.cpp macro -DGF180_SRAM_MACRO

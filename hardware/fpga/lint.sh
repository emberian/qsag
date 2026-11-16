#!/usr/bin/env bash
# verilator --lint-only -Wall over every module as its own top. Run on the build box.
set -euo pipefail
cd "$(dirname "$0")"
SRC="$(tr '\n' ' ' < synth/srcs.txt)"
mkdir -p build
rc=0
for top in qsag_ni_fpga_top qsag_poseidon2_12_pipe; do
    if verilator --lint-only -Wall -sv $SRC --top-module "$top" > "build/lint_$top.log" 2>&1; then
        echo "lint $top: 0 warnings"
    else
        echo "lint $top: FAILED"; cat "build/lint_$top.log"; rc=1
    fi
done
exit $rc

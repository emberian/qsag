#!/usr/bin/env bash
# verilator --lint-only -Wall over every module as its own top. Run on the build box.
set -euo pipefail
cd "$(dirname "$0")"
SRC="$(tr '\n' ' ' < synth/srcs.txt)"
mkdir -p build
rc=0
for top in qsag_ni_fpga_top qsag_poseidon2_12_pipe qsag_gf128_tower_mul qsag_ext5_mac; do
    if verilator --lint-only -Wall -sv $SRC --top-module "$top" > "build/lint_$top.log" 2>&1; then
        echo "lint $top: 0 warnings"
    else
        echo "lint $top: FAILED"; cat "build/lint_$top.log"; rc=1
    fi
done
for params in \
    '-DQSAG_ECP5_CARRY -GPROFILE_COMPACT=1 -GFOLD_TAW=11 -GKECCAK_RPC=1 -GAW=16 -GBW=16' \
    '-DQSAG_ECP5_CARRY -GPROFILE_COMPACT=1 -GECP5_FULLRATE=1 -GFOLD_TAW=11 -GKECCAK_RPC=1 -GAW=16 -GBW=16' \
    '-GP2_UNROLLED=1 -GKECCAK_PIPE=1 -GCHAIN_SLOTW=8'; do
    verilator --lint-only -Wall -sv $SRC --top-module qsag_ni_fpga_top $params || rc=1
done
exit $rc

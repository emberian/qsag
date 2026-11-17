#!/bin/sh
# verilator --lint-only -Wall over chip_core and every submodule (remote, cwd = project root).
# DECLFILENAME is waived: several small leaf modules share a file with their parent.
set -e
mkdir -p build
[ -f rtl/qsag_p2_rc.sv ] || python3 scripts/gen_p2_rc.py rtl/qsag_p2_rc.sv > /dev/null
status=0
for cfg in ${LINT_CFGS:-"" "-DQSAG_ICG" "-DQSAG_SIM_DELAYS --timing" "-DQSAG_ICG -DQSAG_LATCH_RF"}; do
    verilator --lint-only -Wall -Wno-DECLFILENAME $cfg --top-module chip_core -f rtl/qsag_ni_180.f > build/lint.log 2>&1 || status=1
    echo "lint [$cfg]: $(grep -c '^%Warning' build/lint.log) warnings, $(grep -c '^%Error' build/lint.log) errors"
    grep -A3 '^%Warning\|^%Error' build/lint.log | head -${LINT_HEAD:-60}
done

exit "$status"

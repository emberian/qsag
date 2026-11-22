#!/usr/bin/env bash
set -euo pipefail
mkdir -p formal
yosys -Q -q -p 'read_verilog -sv rtl/qsag_asic_gl64_csa.sv lec/addsub.sv; prep -top addsub_miter -flatten; write_smt2 -stbv formal/addsub.smt2'
cat >>formal/addsub.smt2 <<'QUERY'
(declare-const s |addsub_miter_s|)
(assert (|addsub_miter_n bad| s))
(check-sat)
QUERY
for solver in z3 bitwuzla; do
    status=0
    answer=$("$solver" formal/addsub.smt2) || status=$?
    [[ "$status" == 0 || "$status" == 20 ]]
    echo "canonical add/sub $solver $answer"
    test "$answer" = unsat
done

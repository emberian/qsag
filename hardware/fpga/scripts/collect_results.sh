#!/usr/bin/env bash
# Gather the raw outputs of the last gate and synthesis runs under build/ into RESULTS.md.
set -euo pipefail
cd "$(dirname "$0")/.."
{
    echo "# QSAG-NI FPGA: raw results"
    echo
    echo "Collected $(date -u +%Y-%m-%dT%H:%MZ) on $(hostname) from \`build/\`. Tools: $(yosys -V | cut -d' ' -f1-2), $(verilator --version | cut -d' ' -f1-2), $(z3 --version | cut -d' ' -f1-3), $(nextpnr-ecp5 --version 2>&1 | head -1)."
    echo
    echo "## Lint"; echo '```'; grep -h "^lint" build/step_lint.log 2>/dev/null || true; echo '```'
    echo "## Simulation: units"; echo '```'; grep -a -h "^\[\|^  \|^UNITS" build/sim_UNITS.log; echo '```'
    echo "## Simulation: top"; echo '```'; grep -a -h "^\[\|^  \|^TOP\|^QSAGSTA1\|^16-variable" build/sim_TOP.log; echo '```'
    echo "## Trace report"; echo '```'; cat build/trace_report_TOP.txt; echo '```'
    echo "## Formal checks (z3)"
    echo
    echo "| result | check | expected | z3 | time | statement |"
    echo "|---|---|---|---|---|---|"
    for g in gl glmut gf try; do
        [ -f "build/lec/results_$g.txt" ] && awk -F'\t' '{printf "| %s | `%s` | %s | %s | %s | %s |\n", $1, $2, $3, $4, $5, $6}' "build/lec/results_$g.txt"
    done
    echo
    echo "## Canonical-form check of the carry-less multiplier"; echo '```'
    cat build/lec/results_anf.txt 2>/dev/null || true; echo '```'
    for fam in xcup ecp5; do
        echo "## Yosys synthesis: $fam"; echo '```'
        for f in build/synth/*."$fam".summary; do cat "$f"; done
        grep -a -h "FAILED" "build/synth/run_$fam.log" 2>/dev/null || true
        echo '```'
    done
    echo "## nextpnr-ecp5 (LFE5UM5G-85F, CABGA381, speed 8)"; echo '```'
    grep -a -h "^==\|^  \|FAILED" build/run_fmax*.log 2>/dev/null || true; echo '```'
} > RESULTS.md
echo "wrote RESULTS.md ($(wc -l < RESULTS.md) lines)"

#!/usr/bin/env bash
# Gather the raw outputs of the last gate and synthesis runs under build/ into RESULTS.md.
set -euo pipefail
cd "$(dirname "$0")/.."
{
    echo "# QSAG-NI FPGA: raw results"
    echo
    echo "Collected $(date -u +%Y-%m-%dT%H:%MZ) on $(hostname) from \`build/\`. Tools: $(yosys -V | cut -d' ' -f1-2), $(verilator --version | cut -d' ' -f1-2), $(z3 --version | cut -d' ' -f1-3), $(nextpnr-ecp5 --version 2>&1 | head -1)."
    echo
    echo "## Lint"; echo '```'; cat build/step_lint.log 2>/dev/null || true; echo '```'
    echo "## Simulation: units"; echo '```'; grep -a -h "^\[\|^  \|^UNITS" build/sim_UNITS.log; echo '```'
    echo "## Simulation: top (XCUP_RING)"; echo '```'; grep -a -h "^\[\|^  \|^TOP\|^QSAGSTA1\|^16-variable\|^REAL PROOF" build/sim_TOP.log; echo '```'
    if [ -f build/sim_ECP5_FULLRATE.log ]; then
        echo "## Simulation: top (ECP5_FULLRATE — 117/156 DSPs on \$45 ECP5-85F)"; echo '```'; grep -a -h "^\[\|^  \|^TOP\|^REAL PROOF" build/sim_ECP5_FULLRATE.log; echo '```'
    fi
    if [ -f build/sim_COMPACT.log ]; then
        echo "## Simulation: top (ECP5_COMPACT — 18/156 DSPs)"; echo '```'; grep -a -h "^\[\|^  \|^TOP\|^REAL PROOF" build/sim_COMPACT.log; echo '```'
    fi
    echo "## Trace report"; echo '```'; cat build/trace_report_TOP.txt; echo '```'
    echo "## Formal checks (Z3 + Bitwuzla)"
    echo
    echo "| result | check | expected | solver | time | statement |"
    echo "|---|---|---|---|---|---|"
    for g in gl glmut ext5 gf comp tower; do
        [ -f "build/lec/results_$g.txt" ] && awk -F'\t' '{printf "| %s | `%s` | %s | %s | %s | %s |\n", $1, $2, $3, $4, $5, $6}' "build/lec/results_$g.txt"
    done
    echo
    echo "## Canonical-form check of the carry-less multiplier"; echo '```'
    cat build/lec/results_anf.txt 2>/dev/null || true; echo '```'
    for fam in xcup ecp5; do
        echo "## Yosys synthesis: $fam"; echo '```'
        for f in build/synth/*."$fam".summary; do [ -f "$f" ] && cat "$f"; done
        grep -a -h "FAILED" "build/synth/run_$fam.log" 2>/dev/null || true
        echo '```'
    done
    echo "## nextpnr-ecp5 (LFE5U-85F-6BG381C, \$45 ECP5-85F, CABGA381, speed 6)"; echo '```'
    grep -a -h "^==\|^  \|FAILED" build/run_fmax*.log 2>/dev/null || true; echo '```'
} > RESULTS.md
echo "wrote RESULTS.md ($(wc -l < RESULTS.md) lines)"

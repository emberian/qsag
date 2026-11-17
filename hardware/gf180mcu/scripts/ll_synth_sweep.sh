#!/bin/sh
# Compare LibreLane synthesis strategies on the current RTL (remote, cwd = project root).
#   scripts/ll_synth_sweep.sh "AREA 0" "AREA 1" ...
# One run per strategy (tag syn_<strategy>), only up to Yosys.Synthesis, in parallel; prints the
# standard-cell count and area of each. Nothing after synthesis is run.
set -eu
PDK_ROOT="${PDK_ROOT:-/work/proj/gf180mcu}"
mkdir -p build
[ -f rtl/qsag_p2_rc.sv ] || python3 scripts/gen_p2_rc.py rtl/qsag_p2_rc.sv > /dev/null
make -s defines > /dev/null
CFG="librelane/slots/slot_0p5x0p5.yaml librelane/macros/macros_qsag.yaml librelane/config.yaml librelane/config_qsag.yaml"
pids=""
for strat in "$@"; do
    tag="syn_$(echo "$strat" | tr ' ' '_')"
    (
        SRAM_DEFINE=SRAM_gf180mcu_fd_ip_sram timeout --kill-after=20s 1500s librelane $CFG \
            --pdk gf180mcuD --pdk-root "$PDK_ROOT" --manual-pdk --scl gf180mcu_fd_sc_mcu7t5v0 --pad gf180mcu_fd_io \
            --run-tag "$tag" --overwrite -c "SYNTH_STRATEGY=$strat" --to Yosys.Synthesis > "build/ll_$tag.log" 2>&1 || echo "$tag: librelane rc=$?"
    ) &
    pids="$pids $!"
done
for p in $pids; do wait "$p" || true; done
for strat in "$@"; do
    tag="syn_$(echo "$strat" | tr ' ' '_')"
    rpt=$(ls librelane/runs/$tag/*-yosys-synthesis/reports/stat.rpt 2>/dev/null | head -1)
    if [ -n "$rpt" ]; then
        awk -v t="$strat" '/=== chip_top ===/ {f=1} f && /gf180mcu_fd_sc/ {a+=$2; n+=$1} f && /Chip area/ {f=0}
            END {printf "%-10s %6d std cells %10.0f um^2  %5.2f %% of core\n", t, n, a, 100*a/(1052*1647)}' "$rpt"
    else
        echo "$strat: no report"; tail -5 "build/ll_$tag.log"
    fi
done

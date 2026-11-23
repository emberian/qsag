#!/bin/sh
# Whole-chip Yosys synthesis reports (remote, cwd = project root):
#   build/synth_chip_hier.stat   per-module area (hierarchy kept)
#   build/synth_chip.stat        flattened total
# kGE figures use the lane's unit (8.7808 um^2); the report also gives um^2, the share of the
# SLOT_0P5X0P5 core (1052 x 1647 um) and the count in real NAND2_1 cells (10.976 um^2).
set -e
FILES=$(cat rtl/qsag_ni_180.f | tr '\n' ' ')
FLATTEN=" " synth/synth.sh chip_core chip_hier "$FILES" > /dev/null
synth/synth.sh chip_core chip "$FILES" > /dev/null
report() {
    awk -v t="$1" '/Chip area for (top )?module/ {a=$NF} /of which used for sequential/ {s=$(NF-1)}
        END {printf "%-10s %9.0f um^2 | %6.2f kGE @8.78 | %6.2f kGE @nand2_1 | %5.2f %% of core | sequential %.0f um^2\n",
             t, a, a/8780.8, a/10976, 100*a/(1052*1647), s}' $2
}
report hierarchy build/synth_chip_hier.stat
report flat build/synth_chip.stat
echo "-- per module (exclusive of submodules), kGE @8.78"
grep -n "^=== \|Chip area for module" build/synth_chip_hier.stat | paste - - | \
    awk '{n=$2; gsub(/\$paramod[^\\]*\\/,"",n); printf "%-34s %8.2f\n", substr(n,1,34), $NF/8780.8}' | sort -k2 -n -r | head -32
echo "-- cell census (flat)"
grep -E "dff|icg|lat|addf|mux2|xor|xnor" build/synth_chip.stat | awk '{n=$3; gsub(/gf180mcu_fd_sc_mcu7t5v0__/,"",n); printf "%s:%s ", n, $1} END {print ""}'
grep -E "^ +[0-9]+ .* cells$" build/synth_chip.stat | tail -1

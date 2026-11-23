#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source verif/sources.sh
source verif/hdk_sources.sh
work=${BUILD_DIR:?set BUILD_DIR to an absolute build directory}
mkdir -p "$work"
# Slang needs the original parameter declarations for primitive overrides.
cells=$(yosys-config --datdir)/xilinx/cells_xtra.v
awk '/^module (SYSMONE4|DNA_PORTE2|BUFGCE_DIV)\(/ {p=1} p; /^endmodule/ {p=0}' "$cells" > "$work/primitives.v"
for top in ${SYNTH_TOPS:-cl_qsag_f2_top cl_qsag_f2}; do
  sources=("${rtl[@]}")
  [[ $top != cl_qsag_f2 ]] || sources+=("$ddr_stub" design/cl_qsag_f2.sv)
  script="$work/$top.ys"
  cat > "$script" <<EOF
plugin -i slang
read_slang --top $top --keep-hierarchy --blackboxed-module DNA_PORTE2 --blackboxed-module SYSMONE4 --blackboxed-module BUFGCE_DIV $work/primitives.v -DSYNTHESIS -DQSAG_F2_NI -DQSAG_F2_CLOUD_CUSTODY -Idesign -Idesign/ni -I$interfaces ${sources[*]}
hierarchy -check -top $top
proc
opt
design -save premap
attrmap -remove keep_hierarchy -remove KEEP_HIERARCHY
flatten
opt_clean
scc -expect 0
design -load premap
design -delete premap
# Slang specializes every leaf by instance. Map datapaths as groups so ABC
# does not traverse the whole design once for each adder or enable register.
# Map DSPs, BRAMs, CARRY8s, and FFs via synth_xilinx, map LUT1..LUT6 via abc -lut 6 +
# xilinx/lut_map.v (avoiding Yosys 0.71 XAIGER2 O(N^2) box export), then flatten all
# LUTs at line 47 for global post-LUT-map scc -expect 0.
opt_clean
synth_xilinx -family xcup -run :map_ffs -top $top
opt_expr -mux_undef -noclkinv
abc -lut 6
clean
techmap -map +/xilinx/lut_map.v -map +/xilinx/cells_map.v -D LUT_WIDTH=6
xilinx_dffopt
opt_lut_ins -tech xilinx
synth_xilinx -family xcup -run finalize: -top $top
write_rtlil $work/$top.mapped.il
tee -o $work/$top.stat.json stat -json
select -assert-any t:BUFGCE_DIV
select -assert-count 1 t:DNA_PORTE2
select -assert-any t:SYSMONE4
select -assert-any t:DSP48E2
select -assert-any t:RAMB36E2
attrmap -modattr -remove keep_hierarchy -remove KEEP_HIERARCHY
attrmap -remove keep_hierarchy -remove KEEP_HIERARCHY
flatten
techmap -map verif/xcup_scc_luts.v t:LUT1 t:LUT2 t:LUT3 t:LUT4 t:LUT5 t:LUT6
techmap -map +/xilinx/cells_sim.v t:MUXF* t:CARRY* t:INV t:IBUF t:OBUF
scc -expect 0
EOF
  yosys -Q -l "$work/$top.log" -s "$script" > "$work/$top.console"
  python3 - "$work/$top.stat.json" <<'CHECK'
import json, sys
with open(sys.argv[1]) as report:
    counts = json.load(report)["design"]["num_cells_by_type"]
for cell in ("BUFGCE_DIV", "DNA_PORTE2", "SYSMONE4"):
    if counts.get(cell) != 1:
        raise SystemExit(f"{sys.argv[1]}: expected one {cell}, got {counts.get(cell, 0)}")
CHECK
done
if [[ -f $work/cl_qsag_f2_top.stat.json ]]; then
  cp "$work/cl_qsag_f2_top.stat.json" "$work/stat.json"
fi

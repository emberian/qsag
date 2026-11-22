#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source verif/sources.sh
work=${BUILD_DIR:?set BUILD_DIR to a temporary build directory}
mkdir -p "$work"
sv2v -DSYNTHESIS -Idesign -Idesign/ni "${rtl[@]}" > "$work/qsag.v"
yosys -Q -l "$work/xcup.log" -p "read_verilog -sv $work/qsag.v; synth_xilinx -family xcup -top cl_qsag_f2_top; tee -o $work/stat.json stat -json" > "$work/xcup.console"

#!/usr/bin/env bash
# Hierarchical Verilation preserves the actual gate-level leaf implementations.
set -euo pipefail
top=${1:-tb_auto_v2}
dir=${2:-obj_auto_hier}
export MAKEFLAGS="VM_HIER_VERILATOR=$(command -v verilator) ${MAKEFLAGS:-}"
extra=()
if [[ "$top" == tb_auto_v2 ]]; then
  extra=(-DAUTO_CAMPAIGN "$PWD/tb/auto_campaign.cpp")
fi
verilator -j "${JOBS:-3}" --cc --main --exe --hierarchical --timing --timescale 1ns/1ps -Wall tb/lint.vlt tb/auto_hierarchy.vlt \
    --output-split 5000 -Irtl rtl/qsag*.sv tb/sram_dp_model.sv "tb/${top}.sv" "${extra[@]}" \
    --top-module "$top" --Mdir "$dir" -o sim
make -C "$dir" -f "V${top}_hier.mk" -j "${JOBS:-3}" VM_HIER_VERILATOR="$(command -v verilator)" hier_build

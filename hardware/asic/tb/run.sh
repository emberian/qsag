#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
rtl=(rtl/qsag*.sv)
top=${1:-lint}
if [[ $top == lint ]]; then
  exec verilator --lint-only -Wall tb/lint.vlt -Irtl "${rtl[@]}" tb/sram_dp_model.sv --top-module qsag_ni_asic_top
fi
case "$top" in
  tb_units|tb_top|tb_zkhem_v2_top|tb_auto_v2) ;;
  *) echo "unknown testbench $top" >&2; exit 2 ;;
esac
dir=${BUILD_DIR:-${TMPDIR:?}/$top}
mkdir -p "$dir" logs
if [[ ${HIERARCHICAL:-0} == 1 || $top == tb_auto_v2 ]]; then
  bash tb/auto_sim.sh "$top" "$dir" >"logs/build_$top.log" 2>&1
else
  verilator --binary --timing --timescale 1ns/1ps -Wall tb/lint.vlt -Irtl -j "${JOBS:-4}" "${rtl[@]}" \
    tb/sram_dp_model.sv tb/"$top".sv --top-module "$top" --Mdir "$dir" -o sim >"logs/build_$top.log" 2>&1
fi
case "$top" in
  tb_auto_v2) AUTO_SIM="$dir/sim" bash tb/verify_auto.sh edges page page_hqm multi page_multi tamper zk hqm ;;
  tb_top) "$dir/sim" +trace=vec/trace_kat.hex ;;
  tb_zkhem_v2_top) "$dir/sim" +trace=vec/trace_v2.hex ;;
  tb_units) "$dir/sim" | tee logs/units.log; grep -q 'TB_UNITS PASS' logs/units.log ;;
esac

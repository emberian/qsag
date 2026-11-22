#!/usr/bin/env bash
# Run from the staged ASIC directory with the reference vectors in vec/.
set -euo pipefail
mkdir -p logs
rtl=(rtl/qsag*.sv)
case "${1:-lint}" in
  lint) verilator --lint-only -Wall tb/lint.vlt -Irtl "${rtl[@]}" tb/sram_dp_model.sv --top-module qsag_ni_asic_top ;;
  *) top="$1"
     verilator --binary --timing --timescale 1ns/1ps -Wall tb/lint.vlt -Irtl -j "${JOBS:-4}" "${rtl[@]}" \
       tb/sram_dp_model.sv tb/"$top".sv --top-module "$top" --Mdir obj_"$top" -o sim >logs/build_"$top".log 2>&1
     case "$top" in
       tb_units) ./obj_tb_units/sim | tee logs/units.log; grep -q 'TB_UNITS PASS' logs/units.log ;;
       tb_top) for tag in kat sta1_p2 sta1_p2_tamper sta1_ts sta1_ts_tamper duet_comp duet_comp_tamper fold16; do
           ./obj_tb_top/sim +trace=vec/trace_"$tag".hex > logs/"$tag".log
           grep -q 'TB_TOP PASS' logs/"$tag".log
         done ;;
       tb_zkhem_v2_top) ./obj_"$top"/sim +trace=vec/trace_v2.hex | tee logs/v2.log ;;
     esac ;;
esac

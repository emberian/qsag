#!/usr/bin/env bash
# Mapped-area comparison on the IHP SG13G2 (or Sky130 HD) typical-corner foundry liberty.
set -euo pipefail
design=${1:?source directory}
label=${2:?result label}
lib=${LIBERTY:?set LIBERTY to sg13g2_stdcell_typ_1p20V_25C.lib or sky130_fd_sc_hd__tt_025C_1v80.lib}
mkdir -p logs
yosys -Q -T -l "logs/area_$label.log" -p "
  plugin -i slang
  read_slang -I$design/rtl $design/rtl/*.sv --top qsag_ni_asic_top
  hierarchy -check -top qsag_ni_asic_top
  synth -top qsag_ni_asic_top -noabc
  dfflibmap -liberty $lib
  abc -liberty $lib -script +strash;dretime;map
  opt_clean
  tee -o logs/area_$label.stat stat -liberty $lib
" >/dev/null

#!/usr/bin/env bash
# From the build directory. Use the same frontend, library and mapping for both designs.
set -euo pipefail
design=${1:?source directory}
label=${2:?result label}
lib=${LIBERTY:?set LIBERTY to the Nangate45 typical liberty path}
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

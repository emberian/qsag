#!/usr/bin/env bash
# bb2 only. Yosys + ABC standard-cell synthesis.
#   run_synth.sh pre                  elaborate qsag_ni_asic_top (the slang frontend flattens it) and run `synth` once
#   run_synth.sh top   <lib>          map the whole flat top (SRAM macro stays a black box): total standard-cell area
#   run_synth.sh stage <lib> <module> [ks]  one flattened module or register-to-register stage: mapped area and
#                                     critical-path delay (ABC stime)
#   run_synth.sh nand  <module>       generic NAND2/INV mapping: gate counts, CMOS transistor count, logic depth
# libs: sky130 ihp130 nangate45 asap7 (Liberty files under /home/build/qsag-ni-asic/pdk)
set -uo pipefail
cd "$(dirname "$0")/.."
export PATH=/home/build/qsag-ni-asic/tools/oss-cad-suite/bin:$PATH
RUN="env SWARM_MEM_MAX=16G swarm-build timeout --kill-after=10s 600s"
ABCS="+strash;dretime;&get,-n;&dch,-f;&nf,{D};&put;buffer,-c;topo;upsize,{D};dnsize,{D};stime,-p"
PDK=/home/build/qsag-ni-asic/pdk
RTL="rtl/qsag_asic_gl64_csa.sv rtl/qsag_asic_gl64_csa_gen.sv rtl/qsag_asic_ext4_p2_gen.sv rtl/qsag_asic_ext4_p2_shared.sv rtl/qsag_asic_tower_maps_gen.sv rtl/qsag_asic_keccak_clmul.sv rtl/qsag_ni_asic_top.sv rtl/sram_dp_blackbox.sv synth/stages.sv"
mode="$1"; mkdir -p synth/logs synth/netlists
libs() {
  case "$1" in
    sky130)    echo "$PDK/sky130_fd_sc_hd__tt_025C_1v80.lib" ;;
    ihp130)    echo "$PDK/sg13g2_stdcell_typ_1p20V_25C.lib" ;;
    nangate45) echo "$PDK/NangateOpenCellLibrary_typical.lib" ;;
    asap7)     echo "$PDK/asap7_merged_RVT_TT.lib" ;;
  esac
}
if [[ $mode == pre ]]; then
  # library-independent part, once: elaborate and run `synth` (hierarchy kept) up to generic gates
  $RUN yosys -l synth/logs/top_pre.log -p "
    plugin -i slang
    read_slang -Irtl $RTL --top qsag_ni_asic_top
    hierarchy -check -top qsag_ni_asic_top
    synth -top qsag_ni_asic_top -noabc
    write_rtlil synth/netlists/top_pre.il
  " > /dev/null 2>&1
  echo "pre: exit $?"
elif [[ $mode == top ]]; then
  lib="$(libs "$2")"; log="synth/logs/top_$2.log"
  $RUN yosys -l "$log" -p "
    read_rtlil synth/netlists/top_pre.il
    dfflibmap -liberty $lib
    abc -liberty $lib -D 1 -script $ABCS
    opt_clean
    tee -o synth/logs/top_$2.stat stat -liberty $lib
    tee -o synth/logs/top_$2.hier.stat stat -top qsag_ni_asic_top -liberty $lib
  " > /dev/null 2>&1
  echo "top $2: exit $? $(grep -i 'chip area for top' synth/logs/top_$2.hier.stat 2>/dev/null | tr -s ' ')"
elif [[ $mode == stage ]]; then
  # optional 4th argument "ks": Kogge-Stone carry networks (yosys +/choices/kogge-stone.v) instead of Brent-Kung
  lib="$(libs "$2")"; st="$3"; var="${4:-bk}"; log="synth/logs/stage_${st}_$2_${var}.log"
  pre=""
  [[ $var == ks ]] && pre="proc; flatten; opt -fast; wreduce; peepopt; opt_clean; alumacc; opt -fast; techmap -max_iter 1 t:\$macc; techmap -max_iter 1 t:\$alu; techmap -map +/choices/kogge-stone.v;"
  $RUN yosys -l "$log" -p "
    plugin -i slang
    read_slang -Irtl $RTL --top $st
    hierarchy -check -top $st
    $pre
    synth -top $st -flatten -noabc
    dfflibmap -liberty $lib
    abc -liberty $lib -D 1 -script $ABCS
    opt_clean
    tee -o synth/logs/stage_${st}_$2_${var}.stat stat -liberty $lib
  " > /dev/null 2>&1
  echo "stage $st $2 $var: exit $? $(grep -o 'Delay = *[0-9.]* ps' "$log" | tail -1) $(grep -i 'chip area' synth/logs/stage_${st}_$2_${var}.stat | tail -1 | tr -s ' ')"
elif [[ $mode == nand ]]; then
  st="$2"; log="synth/logs/nand_${st}.log"
  $RUN yosys -l "$log" -p "
    plugin -i slang
    read_slang -Irtl $RTL --top $st
    hierarchy -check -top $st
    synth -top $st -flatten -noabc
    abc -g NAND -D 1
    opt_clean
    tee -o synth/logs/nand_${st}.stat stat -tech cmos
    tee -o synth/logs/nand_${st}.ltp ltp -noff
  " > /dev/null 2>&1
  echo "nand $st: exit $? $(grep -E 'NAND|NOT' synth/logs/nand_${st}.stat | tr -s ' ' | tr '\n' ' ') $(grep -i 'transistors' synth/logs/nand_${st}.stat | tail -1) $(grep -i 'longest topological path' synth/logs/nand_${st}.ltp | tail -1)"
fi

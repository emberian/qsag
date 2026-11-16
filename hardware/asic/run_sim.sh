#!/usr/bin/env bash
# bb2 only: generate RTL + vectors, lint (-Wall, 0 warnings), build and run unit + real-proof co-simulations.
set -euo pipefail
cd "$(dirname "$0")"
export PATH=/home/build/qsag-ni-asic/tools/oss-cad-suite/bin:$PATH
RUN="env SWARM_MEM_MAX=16G swarm-build timeout --kill-after=10s 600s"
RTL="rtl/qsag_asic_gl64_csa.sv rtl/qsag_asic_gl64_csa_gen.sv rtl/qsag_asic_ext4_p2_gen.sv rtl/qsag_asic_ext4_p2_shared.sv rtl/qsag_asic_tower_maps_gen.sv rtl/qsag_asic_keccak_clmul.sv rtl/qsag_ni_asic_top.sv"
VFLAGS="-Wall -Wno-fatal tb/lint.vlt -Irtl --x-assign fast --x-initial fast -CFLAGS -O1 -j 16"
mkdir -p logs vec
step="${1:-all}"
if [[ $step == gen || $step == all ]]; then
  $RUN python3 gen/gen_rtl.py rtl 2>&1 | tee logs/gen_rtl.log
  $RUN python3 gen/gen_vectors.py fixtures/lean_external_oracle_vectors.json vec 2>&1 | tee logs/gen_vectors.log
fi
if [[ $step == lint || $step == all ]]; then
  $RUN verilator --lint-only -Wall -Wno-fatal tb/lint.vlt -Irtl $RTL tb/sram_dp_model.sv --top-module qsag_ni_asic_top 2>&1 | tee logs/lint.log
  wcnt="$(grep -c '^%Warning' logs/lint.log || true)"
  echo "lint warnings: $wcnt" | tee -a logs/lint.log
  [[ "$wcnt" == "0" ]]
fi
if [[ $step == units || $step == all ]]; then
  $RUN verilator --binary --timing $VFLAGS $RTL tb/tb_units.sv --top-module tb_units --Mdir obj_units -o tb_units > logs/build_units.log 2>&1 || { tail -40 logs/build_units.log; exit 1; }
  $RUN ./obj_units/tb_units 2>&1 | tee logs/sim_units.log
fi
if [[ $step == top || $step == all ]]; then
  $RUN verilator --binary --timing $VFLAGS $RTL tb/sram_dp_model.sv tb/tb_top.sv --top-module tb_top --Mdir obj_top -o tb_top > logs/build_top.log 2>&1 || { tail -40 logs/build_top.log; exit 1; }
  for t in kat sta1_p2 sta1_p2_tamper sta1_ts sta1_ts_tamper duet_comp duet_comp_tamper fold16; do
    $RUN ./obj_top/tb_top +trace=vec/trace_$t.hex 2>&1 | grep -v '^MARK tag=0 ' | tee logs/sim_top_$t.log | tail -40
  done
fi

#!/usr/bin/env bash
# bb2 only:
#   1. Regenerate synth/RESULTS.md across all 4 PDKs (Sky130, IHP130, Nangate45, ASAP7),
#   2. Run full delay-driven hierarchical 4-PDK Liberty synthesis (`run_hier.py`),
#   3. Run multi-corner PVT OpenSTA (`run_sta.py`),
#   4. Run OpenROAD Symmetric-SRAM Basin 1 floorplan -> placement -> CTS -> global & detailed route (`0` DRC!).
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH=/home/build/qsag-ni-asic/tools/oss-cad-suite/bin:$PATH
PDK=/home/build/qsag-ni-asic/pdk
[[ -f "$PDK/asap7_merged_RVT_TT.lib" ]] || python3 synth/merge_lib.py \
  "$PDK/asap7_merged_RVT_TT.lib" \
  "$PDK/asap7sc7p5t_SIMPLE_RVT_TT_nldm_211120.lib" \
  "$PDK/asap7sc7p5t_INVBUF_RVT_TT_nldm_220122.lib" \
  "$PDK/asap7sc7p5t_AO_RVT_TT_nldm_211120.lib" \
  "$PDK/asap7sc7p5t_OA_RVT_TT_nldm_211120.lib" \
  "$PDK/asap7sc7p5t_SEQ_RVT_TT_nldm_220123.lib"

mkdir -p synth/logs synth/netlists
rm -f synth/logs/summary.txt
./synth/run_synth.sh pre | tee -a synth/logs/pre.out

{
  for lib in sky130 ihp130 nangate45 asap7; do
    echo "topfast $lib"
    for st in qsag_gl64_mul_tree qsag_gl64_fold qsag_gl64_mul_csa qsag_keccak_round \
              stage_ext4 stage_gf128 stage_keccak2 stage_me stage_tower128; do
      echo "stage $lib $st bk"
    done
    for st in stage_partial stage_reduce stage_reduce_ref stage_sbox stage_sbox_ref; do
      echo "stage $lib $st bk"
      echo "stage $lib $st ks"
    done
  done
  for st in stage_reduce stage_reduce_ref stage_keccak2 qsag_gl64_mul_tree qsag_gl64_fold qsag_gl64_mul_csa stage_gf128 stage_me; do
    echo "nand $st"
  done
} | xargs -P 4 -L 1 ./synth/run_synth.sh | tee synth/logs/summary.txt

python3 synth/summarize.py synth/logs/summary.txt synth/RESULTS.md

rm -rf synth/hier
python3 synth/run_hier.py all
python3 synth/run_sta.py
python3 synth/run_openroad.py --force

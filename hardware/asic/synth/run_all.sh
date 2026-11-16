#!/usr/bin/env bash
# bb2 only: full delay-driven hierarchical 4-PDK Liberty synthesis + multi-corner OpenSTA + OpenROAD PnR.
set -euo pipefail
cd "$(dirname "$0")/.."
PDK=/home/build/qsag-ni-asic/pdk
[[ -f "$PDK/asap7_merged_RVT_TT.lib" ]] || python3 synth/merge_lib.py \
  "$PDK/asap7_merged_RVT_TT.lib" \
  "$PDK/asap7sc7p5t_SIMPLE_RVT_TT_nldm_211120.lib" \
  "$PDK/asap7sc7p5t_INVBUF_RVT_TT_nldm_220122.lib" \
  "$PDK/asap7sc7p5t_AO_RVT_TT_nldm_211120.lib" \
  "$PDK/asap7sc7p5t_OA_RVT_TT_nldm_211120.lib" \
  "$PDK/asap7sc7p5t_SEQ_RVT_TT_nldm_220123.lib"

python3 synth/run_hier.py all
python3 synth/run_sta.py
python3 synth/run_openroad.py

#!/usr/bin/env bash
# bb2 only: run the complete compositional LEC suite (100% decided, 0 undecided!) + ANF certificate.
set -euo pipefail
cd "$(dirname "$0")/.."
rm -f logs/lec.log logs/lec_sorted.log

{
  for c in \
    mul_slice mul_slice_mut mul_comb8 mul_comb8_mut \
    reduce reduce_ref reduce_gl reduce_mut \
    fold_pair fold_pair_mut final final_mut step step_mut \
    kara_in kara_in_mut \
    kara_c0 kara_c0_mut kara_c1 kara_c1_mut \
    kara_c2a kara_c2a_mut kara_c2b kara_c2b_mut \
    kara_c3a kara_c3a_mut kara_c3b kara_c3b_mut \
    m4 m4_gl m4_mut me_col me_col_mut sum6 sum6_mut \
    canopy_ff canopy_ff_mut \
    clmul8 clmul8_mut gf_red gf_red_mut \
    tower_fwd tower_fwd_mut tower_bwd tower_bwd_mut tower_lin tower_lin_mut
  do
    echo "$c"
  done
  for h in 8 16 32 64; do
    echo "clmul_kara $h"
    echo "clmul_kara_mut $h"
  done
  for l in 0 1 2 3 4 5 6 7 8 9 10 11; do
    echo "mi_lane $l"
  done
  echo "mi_lane_mut 0"
  echo "mi_lane_mut 7"
} | xargs -P 6 -L 1 lec/run_lec.sh

python3 lec/run_composed.py
python3 lec/check_anf.py

sort logs/lec.log > logs/lec_sorted.log
undec=$(grep -c "=> UNDECIDED" logs/lec_sorted.log || true)
fail=$(grep -c "=> FAIL" logs/lec_sorted.log || true)
ok=$(grep -c "=> OK" logs/lec_sorted.log || true)
echo "LEC SUMMARY: ok=$ok undecided=$undec fail=$fail" | tee -a logs/lec_sorted.log
[[ "$undec" == "0" && "$fail" == "0" ]]

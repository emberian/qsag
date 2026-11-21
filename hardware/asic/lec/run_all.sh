#!/usr/bin/env bash
# bb2 only: run the complete compositional LEC suite (100% decided, 0 undecided!)
# + independent CSA & ANF algebraic equivalence certificates.
set -euo pipefail
cd "$(dirname "$0")/.."
rm -f logs/lec.log logs/lec_sorted.log

{
  for c in \
    mul_slice32 mul_slice32_mut \
    mul_slice33 mul_slice33_mut \
    mul_comb33_top mul_comb33_top_mut \
    reduce reduce_ref reduce_gl reduce_mut \
    fold_hi fold_hi_mut \
    sk_c0 sk_c0_mut sk_c1 sk_c1_mut \
    sk_sh32 sk_sh32_mut \
    sk_m0 sk_m0_mut sk_m1 sk_m1_mut \
    fold_s2 fold_s2_mut \
    final final_mut step step_mut \
    kara_in kara_in_mut \
    fp2_re fp2_re_mut fp2_im fp2_im_mut \
    kara_r0 kara_r0_mut kara_r1 kara_r1_mut \
    kara_sub2 kara_sub2_mut kara_r2 kara_r2_mut kara_r3 kara_r3_mut \
    csa3 csa3_mut csa4 csa4_mut \
    m4_lane m4_lane_gl m4_lane_mut \
    me_col_lane me_col_lane_mut \
    sum4_csa sum4_csa_mut \
    canopy_ff canopy_ff_mut \
    clmul8 clmul8_mut gf_red gf_red_mut \
    tower_basis_fwd tower_basis_fwd_mut \
    tower_basis_bwd tower_basis_bwd_mut \
    tower_lin_fwd tower_lin_fwd_mut \
    tower_lin_bwd tower_lin_bwd_mut \
    tower_gen tower_gen_mut
  do
    echo "$c"
  done
  for lvl in 1 2 3; do
    echo "mul_comb32 $lvl"
    echo "mul_comb32_mut $lvl"
    echo "mul_comb33 $lvl"
    echo "mul_comb33_mut $lvl"
  done
  for h in 8 16 32 64; do
    echo "clmul_kara $h"
    echo "clmul_kara_mut $h"
  done
  for l in 0 1 2 3 4 5 6 7 8 9 10 11; do
    echo "mi_lane $l"
    echo "mi_lane_mut $l"
  done
} | xargs -P "${LEC_JOBS:-4}" -L 1 lec/run_lec.sh

python3 lec/run_composed.py
python3 lec/check_anf.py
python3 lec/check_csa.py .

sort logs/lec.log > logs/lec_sorted.log
undec=$(grep -c "=> UNDECIDED" logs/lec_sorted.log || true)
fail=$(grep -c "=> FAIL" logs/lec_sorted.log || true)
ok=$(grep -c "=> OK" logs/lec_sorted.log || true)
echo "LEC SUMMARY: ok=$ok undecided=$undec fail=$fail" | tee -a logs/lec_sorted.log
[[ "$undec" == "0" && "$fail" == "0" ]]

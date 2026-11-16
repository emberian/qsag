#!/usr/bin/env bash
# bb2 only. Compositional SMT-LIB2 equivalence miters (< 55s cap per solver, 0 undecided!).
# Usage: run_lec.sh <case> [param]
set -uo pipefail
cd "$(dirname "$0")/.."
export PATH=/home/build/qsag-ni-asic/tools/oss-cad-suite/bin:$PATH
RUN="env SWARM_MEM_MAX=16G swarm-build timeout --kill-after=10s 600s"
SECS="${LEC_SECS:-55}"
case="$1"; param="${2:-}"
RTL="rtl/qsag_asic_gl64_csa.sv rtl/qsag_asic_gl64_csa_gen.sv rtl/qsag_asic_ext4_p2_gen.sv rtl/qsag_asic_tower_maps_gen.sv rtl/qsag_asic_keccak_clmul.sv obend/emitted/qsag_ni_gl_reduce128_spec.sv lec/lec_wrappers.sv"

expect=unsat; synth=""; gpar=""
case "$case" in
  # 1. Goldilocks 64x64 4-Row Dadda Tree & CSA Reducer
  mul_slice)      gold=lec_mul_slice_gold;  gate=lec_mul_slice_gate ;;
  mul_slice_mut)  gold=lec_mul_slice_gold;  gate=lec_mul_slice_mut; expect=sat ;;
  mul_comb)       gold=lec_mul_comb_gold;   gate=lec_mul_comb_gate; gpar="-G LVL=$param" ;;
  mul_comb_mut)   gold=lec_mul_comb_gold;   gate=lec_mul_comb_mut;  gpar="-G LVL=$param"; expect=sat ;;
  reduce)         gold=lec_reduce_gold;     gate=lec_reduce_gate ;;
  reduce_ref)     gold=lec_reduce_gold;     gate=lec_reduce_ref ;;
  reduce_gl)      gold=lec_reduce_gold;     gate=lec_reduce_gate; synth=1 ;;
  reduce_mut)     gold=lec_reduce_gold;     gate=lec_reduce_mut; expect=sat ;;
  fold_hi)        gold=lec_fold_hi_gold;    gate=lec_fold_hi_gate ;;
  fold_hi_mut)    gold=lec_fold_hi_gold;    gate=lec_fold_hi_mut; expect=sat ;;
  fold_s1)        gold=lec_fold_s1_gold;    gate=lec_fold_s1_gate ;;
  fold_s1_mut)    gold=lec_fold_s1_gold;    gate=lec_fold_s1_mut; expect=sat ;;
  fold_s2)        gold=lec_fold_s2_gold;    gate=lec_fold_s2_gate ;;
  fold_s2_mut)    gold=lec_fold_s2_gold;    gate=lec_fold_s2_mut; expect=sat ;;
  final)          gold=lec_final_gold;      gate=lec_final_gate ;;
  final_mut)      gold=lec_final_gold;      gate=lec_final_mut; expect=sat ;;
  step)           gold=lec_step_gold;       gate=lec_step_gate ;;
  step_mut)       gold=lec_step_gold;       gate=lec_step_mut; expect=sat ;;

  # 2. 2-Level 9-Product Tower Karatsuba GoldilocksExt4
  kara_in)        gold=lec_kara_in_gold;    gate=lec_kara_in_gate ;;
  kara_in_mut)    gold=lec_kara_in_gold;    gate=lec_kara_in_mut; expect=sat ;;
  fp2_re)         gold=lec_fp2_re_gold;     gate=lec_fp2_re_gate ;;
  fp2_re_mut)     gold=lec_fp2_re_gold;     gate=lec_fp2_re_mut; expect=sat ;;
  fp2_im)         gold=lec_fp2_im_gold;     gate=lec_fp2_im_gate ;;
  fp2_im_mut)     gold=lec_fp2_im_gold;     gate=lec_fp2_im_mut; expect=sat ;;
  kara_r0)        gold=lec_kara_r0_gold;    gate=lec_kara_r0_gate ;;
  kara_r0_mut)    gold=lec_kara_r0_gold;    gate=lec_kara_r0_mut; expect=sat ;;
  kara_r1)        gold=lec_kara_r1_gold;    gate=lec_kara_r1_gate ;;
  kara_r1_mut)    gold=lec_kara_r1_gold;    gate=lec_kara_r1_mut; expect=sat ;;
  kara_sub2)      gold=lec_kara_sub2_gold;  gate=lec_kara_sub2_gate ;;
  kara_sub2_mut)  gold=lec_kara_sub2_gold;  gate=lec_kara_sub2_mut; expect=sat ;;
  kara_r2)        gold=lec_kara_r2_gold;    gate=lec_kara_r2_gate ;;
  kara_r2_mut)    gold=lec_kara_r2_gold;    gate=lec_kara_r2_mut; expect=sat ;;
  kara_r3)        gold=lec_kara_r3_gold;    gate=lec_kara_r3_gate ;;
  kara_r3_mut)    gold=lec_kara_r3_gold;    gate=lec_kara_r3_mut; expect=sat ;;

  # 3. Poseidon2 csa3/csa4, M_4 Lane, M_E Column Lane, sum4, M_I Lanes 0..11, & Canopy FF
  csa3)           gold=lec_csa3_gold;        gate=lec_csa3_gate ;;
  csa3_mut)       gold=lec_csa3_gold;        gate=lec_csa3_mut; expect=sat ;;
  csa4)           gold=lec_csa4_gold;        gate=lec_csa4_gate ;;
  csa4_mut)       gold=lec_csa4_gold;        gate=lec_csa4_mut; expect=sat ;;
  m4_lane)        gold=lec_m4_lane_gold;     gate=lec_m4_lane_gate ;;
  m4_lane_gl)     gold=lec_m4_lane_gold;     gate=lec_m4_lane_gate; synth=1 ;;
  m4_lane_mut)    gold=lec_m4_lane_gold;     gate=lec_m4_lane_mut; expect=sat ;;
  me_col_lane)     gold=lec_me_col_lane_gold; gate=lec_me_col_lane_gate ;;
  me_col_lane_mut) gold=lec_me_col_lane_gold; gate=lec_me_col_lane_mut; expect=sat ;;
  sum4_csa)       gold=lec_sum4_csa_gold;    gate=lec_sum4_csa_gate ;;
  sum4_csa_mut)   gold=lec_sum4_csa_gold;    gate=lec_sum4_csa_mut; expect=sat ;;
  mi_lane)        gold=lec_mi_lane_gold;     gate=lec_mi_lane_gate; gpar="-G LANE=$param" ;;
  mi_lane_mut)    gold=lec_mi_lane_gold;     gate=lec_mi_lane_mut;  gpar="-G LANE=$param"; expect=sat ;;
  canopy_ff)      gold=lec_canopy_ff_gold;   gate=lec_canopy_ff_gate ;;
  canopy_ff_mut)  gold=lec_canopy_ff_gold;   gate=lec_canopy_ff_mut; expect=sat ;;

  # 4. GF(2^128) Recursive Karatsuba CLMUL, 0x87 Reducer, & Cantor/Wiedemann psiTower128
  clmul8)              gold=lec_clmul8_gold;          gate=lec_clmul8_gate ;;
  clmul8_mut)          gold=lec_clmul8_gold;          gate=lec_clmul8_mut; expect=sat ;;
  clmul_kara)          gold=lec_clmul_kara_gold;      gate=lec_clmul_kara_gate; gpar="-G H=$param" ;;
  clmul_kara_mut)      gold=lec_clmul_kara_gold;      gate=lec_clmul_kara_mut;  gpar="-G H=$param"; expect=sat ;;
  gf_red)              gold=lec_gf_red_gold;          gate=lec_gf_red_gate ;;
  gf_red_mut)          gold=lec_gf_red_gold;          gate=lec_gf_red_mut; expect=sat ;;
  tower_basis_fwd)     gold=lec_tower_basis_fwd_gold; gate=lec_tower_basis_fwd_gate ;;
  tower_basis_fwd_mut) gold=lec_tower_basis_fwd_gold; gate=lec_tower_basis_fwd_mut; expect=sat ;;
  tower_basis_bwd)     gold=lec_tower_basis_bwd_gold; gate=lec_tower_basis_bwd_gate ;;
  tower_basis_bwd_mut) gold=lec_tower_basis_bwd_gold; gate=lec_tower_basis_bwd_mut; expect=sat ;;
  tower_lin_fwd)       gold=lec_tower_lin_fwd_gold;   gate=lec_tower_lin_fwd_gate ;;
  tower_lin_fwd_mut)   gold=lec_tower_lin_fwd_gold;   gate=lec_tower_lin_fwd_mut; expect=sat ;;
  tower_lin_bwd)       gold=lec_tower_lin_bwd_gold;   gate=lec_tower_lin_bwd_gate ;;
  tower_lin_bwd_mut)   gold=lec_tower_lin_bwd_gold;   gate=lec_tower_lin_bwd_mut; expect=sat ;;
  tower_gen)           gold=lec_tower_gen_gold;       gate=lec_tower_gen_gate ;;
  tower_gen_mut)       gold=lec_tower_gen_gold;       gate=lec_tower_gen_mut; expect=sat ;;
  *) echo "unknown case $case"; exit 2 ;;
esac

tag="$case${param:+_p$param}"
work="lec/work/$tag"; mkdir -p "$work" logs
export TMPDIR="$PWD/$work"
gatesynth=""
[[ -n "$synth" ]] && gatesynth="synth -top gate -flatten; abc -g NAND; opt_clean; stat;"

$RUN yosys -q -l "$work/yosys.log" -p "
  plugin -i slang
  read_slang -Irtl $RTL --top $gold $gpar; proc; flatten; opt_clean; rename $gold gold; design -stash gold
  read_slang -Irtl $RTL --top $gate $gpar; proc; flatten; opt_clean; rename $gate gate; $gatesynth design -stash gate
  design -copy-from gold -as gold gold; design -copy-from gate -as gate gate
  miter -equiv -flatten -make_outputs gold gate miter
  hierarchy -top miter; opt -fast; opt_clean
  write_smt2 -wires $work/miter.smt2
" >/dev/null 2>"$work/yosys.err" || { echo "LEC $tag: yosys failed"; tail -8 "$work/yosys.err"; exit 1; }

{ cat "$work/miter.smt2"; echo '(declare-const s |miter_s|)'; echo '(assert (|miter_n trigger| s))'; echo '(check-sat)'; } > "$work/query.smt2"
cells=$(grep -c 'define-fun' "$work/miter.smt2")

# Run bitwuzla first (typically 0.1s - 10s); only run z3 if bitwuzla didn't decide or for cross-solver spot check
t0=$(date +%s.%N)
vb=$($RUN bitwuzla -t "$((SECS * 1000))" "$work/query.smt2" 2>&1 | grep -v swarm-build | head -1)
dtb=$(printf '%.2f' "$(echo "$(date +%s.%N) - $t0" | bc)")

vz="skip"; dtz="0.00"
if [[ "$vb" != "sat" && "$vb" != "unsat" ]] || [[ "$cells" -lt 350 ]]; then
  t1=$(date +%s.%N)
  vz=$($RUN z3 -T:20 "$work/query.smt2" 2>&1 | grep -v swarm-build | head -1)
  dtz=$(printf '%.2f' "$(echo "$(date +%s.%N) - $t1" | bc)")
fi

res="bitwuzla=$vb(${dtb}s) z3=$vz(${dtz}s)"
verdict=FAIL
if [[ "$vb" == "$expect" ]] || [[ "$vz" == "$expect" ]]; then verdict=OK; fi
other=$([[ $expect == sat ]] && echo unsat || echo sat)
if [[ "$vb" == "$other" ]] || [[ "$vz" == "$other" ]]; then verdict=FAIL; fi
if [[ "$vb" != "sat" && "$vb" != "unsat" && "$vz" != "sat" && "$vz" != "unsat" ]]; then verdict=UNDECIDED; fi

rm -rf "$work"
echo "LEC $tag: $gold vs $gate${synth:+ (NAND2 gate-level)} expect=$expect : $res smt_defs=$cells => $verdict" | tee -a logs/lec.log
[[ "$verdict" == "OK" ]]

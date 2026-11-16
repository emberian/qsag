#!/usr/bin/env bash
# bb2 only. SMT-LIB2 equivalence miters: yosys (slang frontend) reads both sides, builds the miter,
# `write_smt2`; z3 (and bitwuzla as a second solver) must answer unsat for equal pairs and sat for
# planted faults. Usage: run_lec.sh <case> [lane]
#   cases: reduce reduce_ref reduce_gl reduce_mut fold fold_mut final me me_mut mi mi_mut gf gf_mut mul
set -uo pipefail
cd "$(dirname "$0")/.."
export PATH=/home/build/qsag-ni-asic/tools/oss-cad-suite/bin:$PATH
RUN="env SWARM_MEM_MAX=16G swarm-build timeout --kill-after=10s 600s"
SECS="${LEC_SECS:-540}"
case="$1"; lane="${2:-}"
RTL="rtl/qsag_asic_gl64_csa.sv rtl/qsag_asic_gl64_csa_gen.sv rtl/qsag_asic_ext4_p2_gen.sv rtl/qsag_asic_tower_maps_gen.sv rtl/qsag_asic_keccak_clmul.sv obend/emitted/qsag_ni_gl_reduce128_spec.sv obend/emitted/qsag_ni_gl_mul_spec.sv obend/emitted/qsag_ni_p2_me_spec.sv obend/emitted/qsag_ni_p2_mi_spec.sv lec/lec_wrappers.sv"
expect=unsat; synth=""
case "$case" in
  reduce)     gold=lec_reduce_gold; gate=lec_reduce_gate ;;
  reduce_ref) gold=lec_reduce_gold; gate=lec_reduce_ref ;;
  reduce_gl)  gold=lec_reduce_gold; gate=lec_reduce_gate; synth=1 ;;   # gate = NAND2/INV netlist after synth + abc
  reduce_mut) gold=lec_reduce_gold; gate=lec_reduce_mut; expect=sat ;;
  fold)       gold=lec_fold_gold;   gate=lec_fold_gate ;;
  fold_mut)   gold=lec_fold_gold;   gate=lec_fold_mut; expect=sat ;;
  final)      gold=lec_final_gold;  gate=lec_final_gate ;;
  me)         gold=lec_me_gold;     gate=lec_me_gate ;;
  me_gl)      gold=lec_me_gold;     gate=lec_me_gate; synth=1 ;;
  me_mut)     gold=lec_me_gold;     gate=lec_me_mut; expect=sat ;;
  mi)         gold=lec_mi_gold;     gate=lec_mi_gate ;;
  mi_mut)     gold=lec_mi_gold;     gate=lec_mi_mut; expect=sat ;;
  gf)         gold=lec_gf_gold;     gate=lec_gf_gate ;;
  gf_mut)     gold=lec_gf_gold;     gate=lec_gf_mut; expect=sat ;;
  mul)        gold=lec_mul_gold;    gate=lec_mul_gate ;;
  *) echo "unknown case $case"; exit 2 ;;
esac
tag="$case${lane:+_l$lane}"
work="lec/work/$tag"; mkdir -p "$work" logs
par=""; [[ -n "$lane" ]] && par="-G LANE=$lane"
gatesynth=""
[[ -n "$synth" ]] && gatesynth="synth -top gate -flatten; abc -g NAND; opt_clean; stat;"
# each side is elaborated separately (same parameter override), renamed, then joined in one miter
yosys -q -l "$work/yosys.log" -p "
  plugin -i slang
  read_slang -Irtl $RTL --top $gold $par; proc; flatten; opt_clean; rename $gold gold; design -stash gold
  read_slang -Irtl $RTL --top $gate $par; proc; flatten; opt_clean; rename $gate gate; $gatesynth design -stash gate
  design -copy-from gold -as gold gold; design -copy-from gate -as gate gate
  miter -equiv -flatten -make_outputs gold gate miter
  hierarchy -top miter; opt_clean
  write_smt2 -wires $work/miter.smt2
" >/dev/null 2>"$work/yosys.err" || { echo "LEC $tag: yosys failed"; tail -5 "$work/yosys.err"; exit 1; }
{ cat "$work/miter.smt2"; echo '(declare-const s |miter_s|)'; echo '(assert (|miter_n trigger| s))'; echo '(check-sat)'; } > "$work/query.smt2"
cells=$(grep -c 'define-fun' "$work/miter.smt2")
res=""
for solver in z3 bitwuzla; do
  t0=$(date +%s.%N)
  if [[ $solver == z3 ]]; then v=$($RUN z3 -T:"$SECS" "$work/query.smt2" 2>&1 | grep -v swarm-build | head -1)
  else v=$($RUN bitwuzla -t "$SECS" "$work/query.smt2" 2>&1 | grep -v swarm-build | head -1); fi
  dt=$(printf '%.1f' "$(echo "$(date +%s.%N) - $t0" | bc)")
  res="$res $solver=$v(${dt}s)"
done
verdict=FAIL
if grep -q "z3=$expect" <<<"$res" || grep -q "bitwuzla=$expect" <<<"$res"; then verdict=OK; fi
if grep -Eq "=(sat|unsat)" <<<"$res"; then
  other=$([[ $expect == sat ]] && echo unsat || echo sat)
  grep -q "=$other(" <<<"$res" && verdict=FAIL
else verdict=UNDECIDED; fi
echo "LEC $tag: $gold vs $gate${synth:+ (gate-level NAND netlist)} expect=$expect :$res smt_defs=$cells => $verdict" | tee -a logs/lec.log

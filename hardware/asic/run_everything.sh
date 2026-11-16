#!/usr/bin/env bash
# bb2 only, detached: regenerate, simulate, prove, synthesize. Each tool invocation inside is its own
# bounded swarm-build scope; this driver only sequences them.
cd "$(dirname "$0")"
./run_sim.sh gen  > logs/everything.log 2>&1
./run_sim.sh lint >> logs/everything.log 2>&1
( ./run_sim.sh units; ./run_sim.sh top ) > logs/run_sim_all.log 2>&1 &
obend/run_obend.sh > logs/obend_run.out 2>&1
rm -f logs/lec.log
{
  for c in reduce reduce_ref reduce_gl reduce_mut final step fold_c0 fold_s0 fold fold_mut clmul gf gf_mut mul; do echo "$c"; done
  for l in 0 1 2 3 4 5 6 7 8 9 10 11; do echo "me_int $l"; echo "mi_int $l"; done
  echo "me_int_mut 1"; echo "mi_int_mut 2"; echo "me_spec 0"; echo "mi_spec 1"
} | LEC_SECS=${LEC_SECS:-150} xargs -P 5 -L 1 lec/run_lec.sh > logs/lec_batch.out 2>&1 &
rm -f synth/netlists/top_pre.il synth/logs/*
synth/run_synth.sh pre > synth/logs/summary_pre.txt 2>&1
STAGES="stage_sbox stage_sbox_ref stage_partial stage_me stage_reduce stage_reduce_ref stage_keccak2 stage_gf128 stage_tower128 qsag_gl64_mul_tree"
MODS="qsag_gl64_fold qsag_ext4_coef0 qsag_ext4_coef1 qsag_ext4_coef2 qsag_ext4_coef3 qsag_p2_mi_fused qsag_p2_canopy_ff qsag_keccak_2rpc qsag_gl64_addsub"
{
  for lib in sky130 ihp130 nangate45 asap7; do
    for s in $STAGES; do echo "stage $lib $s"; done
    for s in stage_sbox stage_sbox_ref stage_partial stage_reduce stage_reduce_ref; do echo "stage $lib $s ks"; done
    echo "topfast $lib"
  done
  for s in $MODS; do echo "stage sky130 $s"; done
  for s in stage_reduce stage_reduce_ref stage_me stage_keccak2 stage_gf128 qsag_gl64_mul_tree qsag_gl64_fold; do echo "nand $s"; done
  for lib in sky130 asap7; do echo "stage $lib stage_ext4"; done
} | xargs -P 5 -L 1 synth/run_synth.sh > synth/logs/summary.txt 2>&1
wait
sort logs/lec.log > logs/lec_sorted.log
echo ALL_DONE >> logs/everything.log

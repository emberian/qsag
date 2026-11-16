#!/usr/bin/env bash
# bb2 only: the whole synthesis batch (four jobs at a time). Summary lines go to synth/logs/summary.txt.
cd "$(dirname "$0")/.."
PDK=/home/build/qsag-ni-asic/pdk
# one Liberty file for ASAP7 (the PDK ships the RVT TT cells in five files)
[[ -f $PDK/asap7_merged_RVT_TT.lib ]] || python3 synth/merge_lib.py $PDK/asap7_merged_RVT_TT.lib $PDK/asap7sc7p5t_SIMPLE_RVT_TT_nldm_211120.lib $PDK/asap7sc7p5t_INVBUF_RVT_TT_nldm_220122.lib $PDK/asap7sc7p5t_AO_RVT_TT_nldm_211120.lib $PDK/asap7sc7p5t_OA_RVT_TT_nldm_211120.lib $PDK/asap7sc7p5t_SEQ_RVT_TT_nldm_220123.lib
[[ -f synth/netlists/top_pre.il ]] || synth/run_synth.sh pre > synth/logs/summary_pre.txt 2>&1
STAGES="stage_sbox stage_sbox_ref stage_partial stage_ext4 stage_me stage_reduce stage_reduce_ref stage_keccak2 stage_gf128 stage_tower128"
MODS="qsag_gl64_mul_tree qsag_gl64_fold qsag_ext4_coef0 qsag_ext4_coef1 qsag_ext4_coef2 qsag_ext4_coef3 qsag_p2_mi_fused qsag_p2_canopy_ff qsag_keccak_2rpc qsag_gl64_addsub"
{
  for lib in sky130 ihp130 nangate45 asap7; do
    echo "top $lib"
    for s in $STAGES; do echo "stage $lib $s"; done
    for s in stage_sbox stage_sbox_ref stage_partial stage_reduce stage_reduce_ref; do echo "stage $lib $s ks"; done
  done
  for s in $MODS; do echo "stage sky130 $s"; done
  for s in $STAGES qsag_gl64_mul_tree qsag_gl64_fold qsag_keccak_2rpc; do echo "nand $s"; done
} | xargs -P 4 -L 1 synth/run_synth.sh > synth/logs/summary.txt 2>&1

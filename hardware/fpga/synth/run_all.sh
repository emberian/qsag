#!/usr/bin/env bash
# Synthesise every unit and the top for one family; each Yosys run sits in its own
# 600 s / 16 GB build slot (hierarchy kept). Usage: synth/run_all.sh <xcup|ecp5>
set -u
cd "$(dirname "$0")/.."
fam="$1"
run() { SWARM_MEM_MAX=16G swarm-build timeout --kill-after=10s 600s synth/synth.sh "$fam" "$@" \
            || echo "== $1 ${2:-} [$fam] FAILED or timed out (rc=$?)"; }
run qsag_gl64_reduce
run qsag_gl64_dsp_mul
run qsag_p2_sbox7
run qsag_p2_linear
run qsag_ext4_mac
run qsag_ext4_mac_bfly qsag_ext4_mac_bfly_taw10 -chparam TAW 10
run qsag_keccak_turboshake qsag_keccak_rpc1 -chparam RPC 1
run qsag_keccak_turboshake qsag_keccak_rpc2 -chparam RPC 2
run qsag_gf128_clmul
run qsag_p2_chain_engine
run qsag_poseidon2_12_fpga
run qsag_poseidon2_12_pipe
run qsag_ni_fpga_top qsag_ni_fpga_top_taw10 -chparam FOLD_TAW 10
run qsag_ni_fpga_top qsag_ni_fpga_top_taw16 -chparam FOLD_TAW 16
echo "ALL DONE $fam"

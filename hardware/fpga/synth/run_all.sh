#!/usr/bin/env bash
# Synthesise every unit and top profile for one family; each Yosys run sits in its own
# 600 s / 16 GB build slot (hierarchy kept). Usage: synth/run_all.sh <xcup|ecp5>
set -u
cd "$(dirname "$0")/.."
fam="$1"
run() {
    local mod="$1"; local tag="${2:-$1}"
    if [ -s "build/synth/$tag.$fam.summary" ]; then
        cat "build/synth/$tag.$fam.summary"
        return 0
    fi
    timeout --kill-after=10s 1200s synth/synth.sh "$fam" "$@" \
        || echo "== $1 ${2:-} [$fam] FAILED or timed out (rc=$?)"
}
run qsag_gl64_reduce
run qsag_gl64_dsp_mul
run qsag_p2_sbox7
run qsag_p2_linear
run qsag_ext5_mac
run qsag_ext5_mac_bfly qsag_ext5_mac_bfly_taw10 -chparam TAW 10
run qsag_fp5_compact_bfly qsag_fp5_compact_bfly_taw11 -chparam TAW 11
run qsag_keccak_turboshake qsag_keccak_rpc1 -chparam RPC 1
run qsag_keccak_turboshake qsag_keccak_rpc2 -chparam RPC 2
run qsag_keccak_compact
run qsag_gf128_clmul
run qsag_gf128_tower_mul
run qsag_p2_chain_engine
run qsag_poseidon2_12_fpga
run qsag_poseidon2_12_pipe
run qsag_ni_fpga_top qsag_ni_fpga_top_ecp5_fullrate -chparam PROFILE_COMPACT 1 -chparam ECP5_FULLRATE 1 -chparam FOLD_TAW 11 -chparam KECCAK_RPC 1
run qsag_ni_fpga_top qsag_ni_fpga_top_ecp5_compact  -chparam PROFILE_COMPACT 1 -chparam ECP5_FULLRATE 0 -chparam FOLD_TAW 11 -chparam KECCAK_RPC 1
run qsag_ni_fpga_top qsag_ni_fpga_top_taw10 -chparam FOLD_TAW 10
run qsag_ni_fpga_top qsag_ni_fpga_top_taw16 -chparam FOLD_TAW 16
echo "ALL DONE $fam"

#!/usr/bin/env bash
# nextpnr-ecp5 place and route of the units that fit an LFE5UM5G-85F, one 600 s slot each.
# The Keccak wrappers (1,600-bit state) need router2 to finish inside a slot.
set -u
cd "$(dirname "$0")/.."
run() { SWARM_MEM_MAX=16G swarm-build timeout --kill-after=10s 600s synth/fmax_ecp5.sh "$@" \
            || echo "== ${2:-$1} [nextpnr-ecp5] FAILED or timed out (rc=$?)"; }
for t in "$@"; do
    case "$t" in
        mul)     run fmax_gl64_dsp_mul ;;
        gf)      run fmax_gf128_clmul ;;
        kec1)    NEXTPNR_ARGS="--router router2" run fmax_keccak fmax_keccak_rpc1 -chparam RPC 1 ;;
        kec2)    NEXTPNR_ARGS="--router router2" run fmax_keccak fmax_keccak_rpc2 -chparam RPC 2 ;;
        linear)  NEXTPNR_ARGS="--router router2" run fmax_p2_linear ;;
        sbox)    run fmax_p2_sbox7 ;;
    esac
done
echo "ALL DONE fmax $*"

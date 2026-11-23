#!/usr/bin/env bash
# nextpnr-ecp5 place and route on LFE5U-85F-6BG381C ($45 ECP5-85F, CABGA381, speed 6).
set -u
cd "$(dirname "$0")/.."
export PNR_THREADS="${PNR_THREADS:-1}"
failed=0
run() {
    timeout --kill-after=10s "${FMAX_TIMEOUT:-3600s}" synth/fmax_ecp5.sh "$@" || {
        echo "== ${2:-$1} [nextpnr-ecp5] FAILED or timed out (rc=$?)" >&2
        failed=1
    }
}
targets=("$@")
[ ${#targets[@]} -eq 0 ] && targets=(mul sbox ext5 kcmp gf linear compact_top fullrate_top)
for t in "${targets[@]}"; do
    case "$t" in
        mul)          FREQ=50 run fmax_gl64_dsp_mul ;;
        sbox)         FREQ=50 run fmax_p2_sbox7 ;;
        ext5)         HEAP_BETA=0.65 FREQ=25 run fmax_ext5_mac ;;
        kcmp)         FREQ=30  run fmax_keccak_compact ;;
        gf)           FREQ=65 run fmax_gf128_clmul ;;
        linear)       FREQ=45  run fmax_p2_linear ;;
        compact_top)  HEAP_BETA=0.65 FREQ=20 run fmax_compact_top ;;
        fullrate_top) HEAP_BETA=0.65 FREQ=20 run fmax_ecp5_fullrate_top ;;
        *) echo "unknown PnR target $t" >&2; failed=1 ;;
    esac
done
(( failed == 0 )) || exit 1
echo "ALL DONE fmax ${targets[*]}"

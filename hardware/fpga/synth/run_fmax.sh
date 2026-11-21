#!/usr/bin/env bash
# nextpnr-ecp5 place and route on LFE5U-85F-6BG381C ($45 ECP5-85F, CABGA381, speed 6).
set -u
cd "$(dirname "$0")/.."
run() {
    local tag="${2:-$1}"
    if [ -s "build/synth/$tag.pnr.report.json" ]; then
        python3 - "build/synth/$tag.pnr.report.json" "$tag" "${ECP5_LABEL:-LFE5U-85F-6BG381C}" <<'PY'
import json, sys
r = json.load(open(sys.argv[1]))
fm = {k: v["achieved"] for k, v in r["fmax"].items()}
u = r["utilization"]
keep = {k: (v["used"], v["available"]) for k, v in u.items() if v["used"] and k in ("TRELLIS_COMB", "TRELLIS_FF", "MULT18X18D", "DP16KD", "TRELLIS_RAMW")}
print(f"== {sys.argv[2]} [nextpnr-ecp5 {sys.argv[3]}]")
for k, v in fm.items():
    print(f"  Fmax {k.split('$')[-1]:20s} {v:.2f} MHz")
for k, (a, b) in keep.items():
    pct = 100.0 * a / b if b else 0.0
    print(f"  {k:24s} {a}/{b} ({pct:.1f}%)")
PY
        return 0
    fi
    SWARM_MEM_MAX=20G timeout --kill-after=10s "${FMAX_TIMEOUT:-1200s}" synth/fmax_ecp5.sh "$@" \
        || echo "== ${2:-$1} [nextpnr-ecp5] FAILED or timed out (rc=$?)"
}
targets=("$@")
[ ${#targets[@]} -eq 0 ] && targets=(mul sbox ext4 ext5 kcmp gf linear compact_top fullrate_top kec1 kec2)
for t in "${targets[@]}"; do
    case "$t" in
        mul)          FREQ=150 run fmax_gl64_dsp_mul ;;
        sbox)         FREQ=150 run fmax_p2_sbox7 ;;
        ext4)         FREQ=120 run fmax_ext4_mac ;;
        ext5)         FREQ=45  run fmax_ext5_mac ;;
        kcmp)         FREQ=80  run fmax_keccak_compact ;;
        gf)           FREQ=100 run fmax_gf128_clmul ;;
        linear)       FREQ=80  run fmax_p2_linear ;;
        compact_top)  FREQ=35  run fmax_compact_top ;;
        fullrate_top) FREQ=35  run fmax_ecp5_fullrate_top ;;
        kec1)         FMAX_TIMEOUT=300s FREQ=80 run fmax_keccak fmax_keccak_rpc1 -chparam RPC 1 ;;
        kec2)         FMAX_TIMEOUT=300s FREQ=60 run fmax_keccak fmax_keccak_rpc2 -chparam RPC 2 ;;
    esac
done
echo "ALL DONE fmax ${targets[*]}"

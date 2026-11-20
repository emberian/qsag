#!/usr/bin/env bash
# Place and route one wrapped unit or full accelerator top on the $45 Lattice ECP5-85F
# (`LFE5U-85F-6BG381C`, `--85k --package CABGA381 --speed 6`) with nextpnr-ecp5 and print
# exact post-PnR Fmax and resource utilization.
# Usage: synth/fmax_ecp5.sh <wrapper top> [tag] [-chparam ...]
set -euo pipefail
cd "$(dirname "$0")/.."
top="$1"; tag="${2:-$top}"; shift; [ $# -gt 0 ] && shift
mkdir -p build/synth
SRC="$(tr '\n' ' ' < synth/srcs.txt) synth/fmax_wrap.sv"
out="build/synth/$tag.pnr"
ECP5_DEV="${ECP5_DEV:---85k --package CABGA381 --speed 6}"
ECP5_LABEL="${ECP5_LABEL:-LFE5U-85F-6BG381C}"
INLINE_CSA="flatten t:*qsag_csa_reduce2*; flatten t:*qsag_csa_reduce2*; flatten t:*qsag_csa_reduce2*; flatten t:*qsag_csa_reduce2*; flatten t:*qsag_csa_reduce2*; flatten t:*qsag_csa_reduce2*; opt -fast;"
if [ "${NOFLAT:-0}" = "1" ]; then
    yosys -l "$out.yosys.log" -q -p "read_verilog -sv $SRC; hierarchy -top $top $*; proc; $INLINE_CSA synth_ecp5 -nowidelut -noflatten -top $top -json $out.json" > /dev/null
else
    yosys -l "$out.yosys.log" -q -p "read_verilog -sv $SRC; hierarchy -top $top $*; proc; $INLINE_CSA synth_ecp5 -nowidelut -top $top -json $out.json" > /dev/null
fi
nextpnr-ecp5 $ECP5_DEV --json "$out.json" --freq "${FREQ:-120}" \
    --timing-allow-fail --seed "${SEED:-1}" --threads 8 ${NEXTPNR_ARGS:---router router2} \
    --report "$out.report.json" -q -l "$out.log"
python3 - "$out.report.json" "$tag" "$ECP5_LABEL" <<'PY'
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

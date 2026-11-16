#!/usr/bin/env bash
# Place and route one wrapped unit on a Lattice ECP5 (LFE5UM5G-85F, CABGA381, speed grade 8)
# with nextpnr-ecp5 and print the achieved Fmax. Usage: synth/fmax_ecp5.sh <wrapper top> [tag] [-chparam ...]
set -euo pipefail
cd "$(dirname "$0")/.."
top="$1"; tag="${2:-$top}"; shift; [ $# -gt 0 ] && shift
mkdir -p build/synth
SRC="$(tr '\n' ' ' < synth/srcs.txt) synth/fmax_wrap.sv"
out="build/synth/$tag.pnr"
INLINE_CSA="flatten t:*qsag_sum_csa*; flatten t:*qsag_csa_reduce2*; flatten t:*qsag_csa_reduce2*; flatten t:*qsag_csa_reduce2*; flatten t:*qsag_csa_reduce2*; flatten t:*qsag_csa_reduce2*; flatten t:*qsag_csa_reduce2*; flatten t:*qsag_add_split*; opt -fast;"
if [ "${NOFLAT:-0}" = "1" ]; then
    yosys -l "$out.yosys.log" -q -p "read_verilog -sv $SRC; hierarchy -top $top $*; proc; $INLINE_CSA synth_ecp5 -noflatten -top $top; flatten; opt_clean; write_json $out.json" > /dev/null
else
    yosys -l "$out.yosys.log" -q -p "read_verilog -sv $SRC; hierarchy -top $top $*; proc; $INLINE_CSA synth_ecp5 -top $top -json $out.json" > /dev/null
fi
nextpnr-ecp5 --um5g-85k --package CABGA381 --speed 8 --json "$out.json" --freq "${FREQ:-150}" \
    --timing-allow-fail --seed "${SEED:-1}" --threads 8 ${NEXTPNR_ARGS:-} --report "$out.report.json" -q -l "$out.log" || true
python3 - "$out.report.json" "$tag" <<'PY'
import json, sys
r = json.load(open(sys.argv[1]))
fm = {k: v["achieved"] for k, v in r["fmax"].items()}
u = r["utilization"]
keep = {k: (v["used"], v["available"]) for k, v in u.items() if v["used"] and k in ("TRELLIS_COMB", "TRELLIS_FF", "MULT18X18D", "DP16KD", "TRELLIS_RAMW")}
print(f"== {sys.argv[2]} [nextpnr-ecp5 LFE5UM5G-85F-8]")
for k, v in fm.items():
    print(f"  Fmax {k.split('$')[-1]:20s} {v:.2f} MHz")
for k, (a, b) in keep.items():
    print(f"  {k:24s} {a}/{b}")
PY

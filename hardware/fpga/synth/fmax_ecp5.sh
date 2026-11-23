#!/usr/bin/env bash
# Place and route one wrapped unit or full accelerator top on the $45 Lattice ECP5-85F
# (`LFE5U-85F-6BG381C`, `--85k --package CABGA381 --speed 6`) with timing-driven nextpnr-ecp5
# and print the checked post-route frequency and utilization.
# Usage: synth/fmax_ecp5.sh <wrapper top> [tag] [-chparam ...]
set -euo pipefail
cd "$(dirname "$0")/.."
top="$1"; tag="${2:-$top}"; shift; [ $# -gt 0 ] && shift
mkdir -p build/synth
SRC="$(tr '\n' ' ' < synth/srcs.txt) synth/fmax_wrap.sv"
out="build/synth/$tag.pnr"
freq="${FREQ:-25}"
ECP5_LABEL=LFE5U-85F-6BG381C
CARRY_FLAT="flatten t:*qsag_sum_csa*; flatten t:*qsag_sum_csa*; flatten t:*qsag_sum_csa*; flatten t:*qsag_sum_csa*; flatten t:*qsag_add_split*; opt -fast;"
flatten_flag=""
if [ "${NOFLAT:-0}" = 1 ]; then flatten_flag="-noflatten"; fi
synth_cmd="read_verilog -sv -DQSAG_ECP5_CARRY $SRC; hierarchy -top $top $*; proc; $CARRY_FLAT synth_ecp5 -nowidelut $flatten_flag -top $top"

use_opt=0
case "$top" in
    fmax_ext5_mac|fmax_compact_top|fmax_ecp5_fullrate_top) use_opt=1 ;;
esac
mkdir -p "$(dirname "$out")"
exec 9>"$out.lock"
flock 9
synth_key="$( { sha256sum $SRC; [ "$use_opt" = 1 ] && sha256sum synth/ecp5_opt.py; yosys -V; echo "$synth_cmd $use_opt"; } | sha256sum)"
prior_key="$(cat "$out.synth-key" 2>/dev/null || true)"
identical=0
if [[ ! -s "$out.json" || "$(cat "$out.synth-key" 2>/dev/null)" != "$synth_key" ]]; then
    if [ "$use_opt" = 1 ]; then
        yosys -l "$out.yosys.log" -q -p "$synth_cmd -json $out.raw.json"
        python3 synth/ecp5_opt.py "$out.raw.json" "$top" "$out.new.json" >>"$out.yosys.log"
        rm -f "$out.raw.json"
    else
        yosys -l "$out.yosys.log" -q -p "$synth_cmd -json $out.new.json"
    fi
    if cmp -s "$out.new.json" "$out.json"; then identical=1; fi
    : >"$out.synth-key"
    mv "$out.new.json" "$out.json"
    echo "$synth_key" >"$out.synth-key"
fi

default_beta=0.78
place_script="synth/ecp5_place.py"
plan_extra=""
case "$top" in
    fmax_compact_top|fmax_ecp5_fullrate_top)
        place_script="synth/ecp5_top_place.py"
        case "${PLACEMENT:-plan}" in
            heap) place_script="" ;;
            plan) ;;
            *) echo "PLACEMENT must be heap or plan" >&2; exit 2 ;;
        esac
        plan_extra="$(sha256sum synth/ecp5_plan.py)"
        ;;
esac
threads="${PNR_THREADS:-4}"
[[ "$threads" =~ ^[1-4]$ ]] || { echo "PNR_THREADS must be 1..4" >&2; exit 2; }
args=(--85k --package CABGA381 --speed 6 --freq "$freq" --seed "${SEED:-1}"
      --threads "$threads" --placer heap --router router2
      --placer-heap-beta "${HEAP_BETA:-$default_beta}")
case "$top" in
    fmax_ext5_mac|fmax_compact_top|fmax_ecp5_fullrate_top)
        if [[ -n "$place_script" ]]; then args+=(--pre-place "$place_script"); fi
        ;;
esac
route_signature() {
    { echo "$1"; if [[ -n "$place_script" ]]; then sha256sum "$place_script"; fi
      echo "$plan_extra"; printf '%s\n' "${args[@]}"; nextpnr-ecp5 --version 2>&1; ecppack --version 2>&1
    } | sha256sum
}
route_key="$(route_signature "$synth_key")"

check_route() {
    python3 - "$1" "$2" "$out.log" "$freq" "$tag" "$ECP5_LABEL" <<'PY_CHECK'
import json
import math
import re
import sys
from pathlib import Path

report, bit, log = map(Path, sys.argv[1:4])
freq, tag, device = sys.argv[4:]
size = bit.stat().st_size
if not size:
    sys.exit(f"{bit} is empty")
data = json.loads(report.read_text())
if not data["fmax"]:
    sys.exit(f"{report} contains no constrained clocks")
print(f"== {tag} [{device} | {size} bytes]")
for clock, v in data["fmax"].items():
    print(f"  {clock}: achieved {v['achieved']:.3f} MHz, constraint {v['constraint']:.3f} MHz")
    if not math.isclose(v["constraint"], float(freq), rel_tol=1e-7):
        sys.exit(f"{report}: expected {freq} MHz constraint on {clock}")
    if not (v["achieved"] >= v["constraint"] and v["achieved"] >= float(freq)):
        sys.exit(f"{report}: failed {freq} MHz constraint on {clock}")
overused = re.findall(r"\boverused=(\d+)", log.read_text())
if not overused or int(overused[-1]) != 0:
    sys.exit(f"{log}: missing congestion-free final router iteration")
for key in ("TRELLIS_COMB", "TRELLIS_FF", "MULT18X18D", "DP16KD", "TRELLIS_RAMW"):
    u = data["utilization"][key]
    print(f"  {key:24s} {u['used']}/{u['available']}")
PY_CHECK
}

cached="$(cat "$out.route-key" 2>/dev/null || true)"
# A source-only change can resynthesize to the identical mapped JSON. Retain
# timing evidence only if both the netlist and the entire route recipe match.
if [[ -s "$out.bit" && -s "$out.report.json" && -s "$out.log" ]] &&
   { [[ "$cached" == "$route_key" ]] ||
     { [[ "$identical" == 1 ]] && [[ "$cached" == "$(route_signature "$prior_key")" ]]; }; }; then
    check_route "$out.report.json" "$out.bit"
    echo "$route_key" >"$out.route-key"
else
    rm -f "$out.route-key" "$out.bit" "$out.report.json"
    trap 'rm -f "$out.config" "$out.new.bit" "$out.new.report.json"' EXIT
    case "$top" in
        fmax_compact_top|fmax_ecp5_fullrate_top)
            [[ -z "$place_script" ]] || python3 synth/ecp5_plan.py "$out.json" "$top" "$out.plan.json" >>"$out.yosys.log"
            ;;
    esac
    QSAG_ECP5_TOP="$top" QSAG_ECP5_PLAN="$out.plan.json" stdbuf -oL -eL nextpnr-ecp5 "${args[@]}" \
        --json "$out.json" --textcfg "$out.config" --report "$out.new.report.json" >"$out.log" 2>&1
    ecppack --compress "$out.config" "$out.new.bit"
    check_route "$out.new.report.json" "$out.new.bit"
    mv "$out.new.report.json" "$out.report.json"
    mv "$out.new.bit" "$out.bit"
    echo "$route_key" >"$out.route-key"
fi
# Keep a conventional synthesis-log name alongside the driver log.
ln -sf "$(basename "$out").yosys.log" "$out.ys.log"

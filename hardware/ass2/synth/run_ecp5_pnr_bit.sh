#!/usr/bin/env bash
set -euo pipefail
[[ $(uname -s) == Linux ]] || { echo "Run on bb2" >&2; exit 2; }
here=$(cd "$(dirname "$0")" && pwd)
rtl=$(cd "$here/../rtl" && pwd)
top=ecp5_top_wrap
[[ -s "$rtl/qsag_ass2_enclave_top.sv" ]] || { echo "Missing $rtl/qsag_ass2_enclave_top.sv" >&2; exit 2; }
export PATH="/home/build/qsag-ni-asic/tools/oss-cad-suite/bin:$PATH"
mkdir -p "${OUT:-$here/out/ecp5}"
cd "${OUT:-$here/out/ecp5}"
# Slang handles the SystemVerilog packages and unpacked arrays. The native
# frontend retains the IO tristates until synth_ecp5 maps them to TRELLIS_IO.
source "$here/rtl_sources.sh"
printf '"%s"\n' "${rtl_sources[@]}" > rtl.f
cat > synth.ys <<YS
read_slang --top qsag_ass2_enclave_top -I"$rtl" -f rtl.f
read_verilog -sv "$here/ecp5_top_wrap.sv"
hierarchy -check -top $top
synth_ecp5 -nowidelut -top $top -json ass2.json
stat
YS
yosys -Q -l synth.log -s synth.ys > /dev/null
pins=(--lpf-allow-unconstrained)
if [[ -n ${LPF:-} ]]; then pins=(--lpf "$LPF"); fi
nextpnr-ecp5 --85k --package CABGA381 --speed 6 --json ass2.json --freq "${FREQ_MHZ:-40}" \
    --seed 1 --threads "${JOBS:-4}" --router "${ROUTER:-router2}" --timing-allow-fail "${pins[@]}" \
    --report report.json --textcfg ass2.config -l pnr.log -q
help=$(ecppack --help 2>&1 || true)
pack=()
# Project Trellis 1.4 emits an uncompressed image by default.
if [[ "$help" == *--compress-mode* ]]; then pack=(--compress-mode none); fi
ecppack "${pack[@]}" ass2.config ass2.bit
ecpunpack ass2.bit unpacked.config
ecppack "${pack[@]}" unpacked.config repacked.bit
sha256sum ass2.bit repacked.bit | tee sha256.txt
cmp ass2.bit repacked.bit
python3 - <<'PY'
import collections, json, pathlib
report = json.loads(pathlib.Path('report.json').read_text())
synth = json.loads(pathlib.Path('ass2.json').read_text())
counts = collections.Counter(c['type'] for c in synth['modules']['ecp5_top_wrap']['cells'].values())
print('LUT4', counts['LUT4'])
for name in ('TRELLIS_COMB', 'TRELLIS_FF', 'MULT18X18D', 'DP16KD'):
    print(name, report['utilization'][name]['used'])
for name, freq in report['fmax'].items():
    print(name, freq['achieved'], 'MHz (target', freq['constraint'], 'MHz)')
PY

#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
rtl=$(cd "$here/../rtl" && pwd)
source "$here/../synth/rtl_sources.sh"
python3 -B "$here/../tools/build_rom.py" --check
work=$(mktemp -d "${TMPDIR:-/tmp}/ass2-enclave-tb.XXXXXX")
trap 'rm -rf "$work"' EXIT
verilator -DASS2_FAST_ENTROPY --cc --exe --build -j 4 -Wall -O2 -LDFLAGS "-lcrypto" --Mdir "$work/obj" \
    --top-module qsag_ass2_enclave_top \
    "${rtl_sources[@]}" "$here/sim_enclave_top.cpp" \
    -o "$work/sim_enclave_top" >/dev/null
"$work/sim_enclave_top" | tee "$work/results"
python3 -B "$here/check_resident.py" "$work/results"

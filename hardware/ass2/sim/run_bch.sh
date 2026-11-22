#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
rtl="$here/../rtl"
work=$(mktemp -d "${TMPDIR:-/tmp}/ass2-bch.XXXXXX")
trap 'rm -rf "$work"' EXIT
verilator --cc --exe --build -Wall -DASS2_FAST_ENTROPY --top-module dregg_ro_puf_bch \
    --Mdir "$work" -I"$rtl" "$rtl/dregg_ro_puf_bch.sv" "$here/sim_bch.cpp" >/dev/null
"$work/Vdregg_ro_puf_bch"

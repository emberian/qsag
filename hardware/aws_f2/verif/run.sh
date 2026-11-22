#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source verif/sources.sh
args=(-Wall verif/filenames.vlt -DASS2_FAST_ENTROPY -Idesign -Idesign/ni --top-module cl_qsag_f2_top)
if [[ ${1:-sim} == lint ]]; then
  for n in 1 2 3 4; do verilator --lint-only "${args[@]}" -GN_NI=$n "${rtl[@]}"; done
else
  work=${BUILD_DIR:?set BUILD_DIR to a temporary build directory}
  verilator --cc --exe --build -j "${JOBS:-4}" --Mdir "$work" "${args[@]}" "${rtl[@]}" \
    "$PWD/verif/sim_cl_qsag_f2.cpp" -LDFLAGS "-lcrypto"
  "$work/Vcl_qsag_f2_top"
fi

#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source verif/sources.sh
args=(-Wall verif/filenames.vlt -DQSAG_F2_NI -DQSAG_F2_CLOUD_CUSTODY -Idesign -Idesign/ni --top-module cl_qsag_f2_top)
if [[ ${1:-sim} == lint ]]; then
  for n in 1 2 3 4; do echo "Linting N_NI=$n"; verilator --lint-only "${args[@]}" -GN_NI=$n "${rtl[@]}" verif/scrub_monitor.sv; done
else
  work=${BUILD_DIR:?set BUILD_DIR to a temporary build directory}
  verilator --cc --exe --build -j "${JOBS:-4}" -O3 -CFLAGS "-O3" -MAKEFLAGS "OPT_FAST=-O3" --Mdir "$work" "${args[@]}" "${rtl[@]}" verif/scrub_monitor.sv \
    "$PWD/verif/sim_cl_qsag_f2.cpp"
  "$work/Vcl_qsag_f2_top"
fi

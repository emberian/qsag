#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source verif/sources.sh
source verif/hdk_sources.sh
args=(-Wall verif/filenames.vlt verif/hdkwrapper.vlt --top-module cl_qsag_f2
      -DQSAG_F2_NI -DQSAG_F2_CLOUD_CUSTODY -Idesign -Idesign/ni -I"$interfaces")
sources=("${rtl[@]}" verif/scrub_monitor.sv "$ddr_stub" design/cl_qsag_f2.sv)
if [[ ${1:-sim} == lint ]]; then
  verilator --lint-only "${args[@]}" "${sources[@]}"
else
  work=${BUILD_DIR:?set BUILD_DIR to a temporary build directory}
  verilator "${args[@]}" --cc --exe --build -j "${JOBS:-4}" -O3 -MAKEFLAGS "OPT_FAST=-O3" --Mdir "$work" \
      "${sources[@]}" -CFLAGS "-O3 -DHDK_WRAPPER" "$PWD/verif/sim_cl_qsag_f2.cpp"
  "$work/Vcl_qsag_f2"
fi

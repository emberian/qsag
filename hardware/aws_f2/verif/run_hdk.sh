#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source verif/sources.sh
shell=${HDK_SHELL_DIR:?source hdk_setup.sh}
verilator -Wall verif/filenames.vlt verif/hdkwrapper.vlt --cc --exe --build -j "${JOBS:-4}" --top-module cl_qsag_f2 \
    --Mdir "${BUILD_DIR:?set BUILD_DIR to a temporary build directory}" -DQSAG_F2_CLOUD_BRINGUP \
    -Idesign -Idesign/ni -I"$shell/design/interfaces" "${rtl[@]}" \
    "$shell/design/sh_ddr/sh_ddr.stub.sv" design/cl_qsag_f2.sv \
    -CFLAGS "-DHDK_BRINGUP" -LDFLAGS "-lcrypto" "$PWD/verif/sim_cl_qsag_f2.cpp"
"$BUILD_DIR/Vcl_qsag_f2"

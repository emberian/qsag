#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
verilator --binary --timing --top-module anchor_tb --Mdir "${BUILD_DIR:?set BUILD_DIR}" \
  -DQSAG_F2_CLOUD_CUSTODY -Idesign/ni design/ni/qsag_asic_keccak_clmul.sv \
  design/qsag_f2_{turboshake,cloud_entropy_anchor,fram_model}.sv verif/anchor_tb.sv
"$BUILD_DIR/Vanchor_tb"

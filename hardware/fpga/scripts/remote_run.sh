#!/usr/bin/env bash
# Run a command inside a remote Linux FPGA workspace (${QSAG_BUILD_HOST:?}).
set -euo pipefail
printf -v task '%q ' "$@"
ssh -o ServerAliveInterval=15 -o ServerAliveCountMax=3 "${QSAG_BUILD_HOST:?set QSAG_BUILD_HOST}" \
    'export TMPDIR=${QSAG_WORK_DIR:-/home/build/qsag-work}/work_tmp && mkdir -p "$TMPDIR" &&
     export PATH="${OSS_CAD_BIN:-/opt/oss-cad-suite/bin}:$PATH" JOBS=6 &&
     cd "${QSAG_REPO_DIR:-/home/build/qsag}/hardware/fpga" && '"$task"

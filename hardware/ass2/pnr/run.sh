#!/usr/bin/env bash
set -eo pipefail
cd "$(dirname "$0")"
[ -f "${QSAG_EDA_ENV:-/work/qsag/dev_env.sh}" ] && source "${QSAG_EDA_ENV:-/work/qsag/dev_env.sh}"
export SRAM_DEFINE=SRAM_gf180mcu_fd_ip_sram
exec librelane librelane/{slot_0p5x0p5,macros_5v,config,ass2}.yaml --manual-pdk --pdk gf180mcuD --pdk-root "${PDK_ROOT:-/work/qsag/pdk}" --scl gf180mcu_fd_sc_mcu7t5v0 --pad gf180mcu_fd_io -j 8 --hide-progress-bar "$@"

#!/usr/bin/env bash
set -eo pipefail
cd /work/ass2-excellence/pnr
source /work/wave-e5/dev_env.sh
export SRAM_DEFINE=SRAM_gf180mcu_fd_ip_sram
exec librelane librelane/{slot_0p5x0p5,macros_5v,config,ass2}.yaml --manual-pdk --pdk gf180mcuD --pdk-root /work/wave-e5/pdk --scl gf180mcu_fd_sc_mcu7t5v0 --pad gf180mcu_fd_io -j 8 --hide-progress-bar "$@"

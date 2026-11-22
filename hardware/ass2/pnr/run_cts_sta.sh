#!/usr/bin/env bash
set -eo pipefail
cd /work/ass2-pnr
source dev_env.sh
export AUDIT_ENV=$(realpath librelane/runs/ass2/30-openroad-cts/_env.tcl)
export AUDIT_ODB=$(realpath librelane/runs/ass2/30-openroad-cts/chip_top.odb)
mkdir -p postcts
for pvt in tt_025C_5v00 ff_n40C_5v50 ss_125C_4v50; do
    export AUDIT_PVT=$pvt
    openroad -threads 1 -no_splash -exit postcts_sta.tcl > "postcts/$pvt.log" 2>&1
    test "$(grep -c '^PATH ' "postcts/$pvt.log")" = 4
done

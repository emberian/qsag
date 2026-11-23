#!/bin/sh
# One bounded LibreLane stage per invocation, inside scripts/rx.sh.
# first <step> creates a new run; <step> <step> resumes it. Never erase a run.
set -eu
PDK_ROOT=${PDK_ROOT:-/work/proj/gf180mcu}
RUN_TAG=${RUN_TAG:-dregg180}
mkdir -p build
make -s defines > /dev/null
CFG="librelane/slots/slot_0p5x0p5.yaml librelane/macros/macros_qsag.yaml librelane/config.yaml librelane/config_qsag.yaml"
OPTS="--pdk gf180mcuD --pdk-root $PDK_ROOT --manual-pdk --scl gf180mcu_fd_sc_mcu7t5v0 --pad gf180mcu_fd_io --run-tag $RUN_TAG"
status=0
if [ "$1" = first ]; then
    test ! -e "librelane/runs/$RUN_TAG" || { echo "Run exists: $RUN_TAG; resume explicitly"; exit 1; }
    SRAM_DEFINE=SRAM_gf180mcu_fd_ip_sram librelane $CFG $OPTS --to "$2" > build/ll_first.log 2>&1 || status=$?
    tail -${TAILN:-25} build/ll_first.log
else
    test "$1" = "$2" || { echo "Use one stage per invocation"; exit 1; }
    SRAM_DEFINE=SRAM_gf180mcu_fd_ip_sram librelane $CFG $OPTS --from "$1" --to "$2" ${LL_EXTRA:-} > "build/ll_$1.log" 2>&1 || status=$?
    tail -${TAILN:-25} "build/ll_$1.log"
fi
exit "$status"

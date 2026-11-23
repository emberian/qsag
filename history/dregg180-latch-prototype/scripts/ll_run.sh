#!/bin/sh
# LibreLane `Chip` flow, one step per librelane invocation, each step under its own wall-clock
# limit (remote, cwd = project root, inside the dev shell).
#   scripts/ll_run.sh <run-tag> <last-step> [<first-step>]
# Without <first-step> a new run is created (it must not exist). With it, the existing run is
# resumed from that step. A step that fails or times out stops the loop; its directory is left in
# place for inspection (remove a step directory without state_out.json before resuming from it).
# Environment: STEP_TIMEOUT (seconds, default 1800), STEP_MEM_GB (address-space limit of every
# step, default 28: the container has no memory limit of its own, and one repair_design run at
# 94 % placement density grew to 30 GB), PDK_ROOT (default /work/proj/gf180mcu).
set -eu
ulimit -v $(( ${STEP_MEM_GB:-28} * 1024 * 1024 ))
TAG="$1"; LAST="$2"; FIRST="${3:-}"
STEP_TIMEOUT="${STEP_TIMEOUT:-1800}"
PDK_ROOT="${PDK_ROOT:-/work/proj/gf180mcu}"
mkdir -p build
[ -f rtl/qsag_p2_rc.sv ] || python3 scripts/gen_p2_rc.py rtl/qsag_p2_rc.sv > /dev/null
make -s defines > /dev/null
CFG="librelane/slots/slot_0p5x0p5.yaml librelane/macros/macros_qsag.yaml librelane/config.yaml librelane/config_qsag.yaml"
OPTS="--pdk gf180mcuD --pdk-root $PDK_ROOT --manual-pdk --scl gf180mcu_fd_sc_mcu7t5v0 --pad gf180mcu_fd_io --run-tag $TAG"
STEPS=$(python3 librelane/list_steps.py)
case " $STEPS " in *" $LAST "*) ;; *) echo "unknown last step $LAST"; exit 2 ;; esac
if [ -z "$FIRST" ]; then
    test ! -e "librelane/runs/$TAG" || { echo "run $TAG exists: give a first step to resume"; exit 2; }
    started=1
else
    case " $STEPS " in *" $FIRST "*) ;; *) echo "unknown first step $FIRST"; exit 2 ;; esac
    started=0
fi
new=1
[ -n "$FIRST" ] && new=0
for s in $STEPS; do
    if [ "$started" = 0 ]; then
        [ "$s" = "$FIRST" ] || continue
        started=1
    fi
    t0=$(date +%s)
    rc=0
    if [ "$new" = 1 ]; then
        SRAM_DEFINE=SRAM_gf180mcu_fd_ip_sram timeout --kill-after=20s "${STEP_TIMEOUT}s" librelane $CFG $OPTS --to "$s" > "build/ll_${TAG}_$s.log" 2>&1 || rc=$?
        new=0
    else
        SRAM_DEFINE=SRAM_gf180mcu_fd_ip_sram timeout --kill-after=20s "${STEP_TIMEOUT}s" librelane $CFG $OPTS --from "$s" --to "$s" > "build/ll_${TAG}_$s.log" 2>&1 || rc=$?
    fi
    echo "STEP $s rc=$rc $(( $(date +%s) - t0 ))s"
    if [ "$rc" != 0 ]; then
        tail -n 40 "build/ll_${TAG}_$s.log"
        exit "$rc"
    fi
    [ "$s" = "$LAST" ] && break
done
echo "ll_run: reached $LAST"

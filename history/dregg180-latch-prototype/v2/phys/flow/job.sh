#!/bin/sh
# hbox host side. Start one stage slice of flow/pnr.tcl in the fable-dregg180-phys container, detached,
# with a PID file (jobs/<job>.pid), a log (jobs/<job>.log; OpenROAD's own log is exp/<run>/<job>.log)
# and a return-code file (jobs/<job>.rc). One heavy job at a time: refuses to start while another runs.
#   job.sh <run> <from> <to> <timeout-s> [KEY=VAL ...]      e.g. job.sh a1 place place 3600 P_DENSITY=0.6
# To stop a slice: docker exec fable-dregg180-phys kill $(cat jobs/<job>.inpid), then kill $(cat jobs/<job>.pid).
# Containment: the container has --memory 24g (OpenROAD runs inside it); the client side is wrapped in
# SWARM_MEM_MAX=24G swarm-build timeout --kill-after=10s by bg.sh.
set -eu
W=/var/tmp/fable-dregg180-phys
run=$1; from=$2; to=$3; tmo=$4; shift 4
job=${run}_${from}_${to}
for p in $W/jobs/*.pid; do
    [ -f "$p" ] || continue
    n=$(basename $p .pid)
    if [ ! -f $W/jobs/$n.rc ] && kill -0 "$(cat $p)" 2>/dev/null; then echo "job $n still running (pid $(cat $p))"; exit 3; fi
done
{
    echo "export P_IN=${P_IN:-/work/in/px0.odb}"
    echo "export P_OUT=/work/exp/$run P_SDC=/work/proj/v2/phys/flow/chip_top_phys.sdc P_FROM=$from P_TO=$to"
    for kv in "$@"; do echo "export ${kv%%=*}='${kv#*=}'"; done
    echo "mkdir -p /work/exp/$run && cd /work/exp/$run"
    echo "openroad -exit -threads ${THREADS:-12} -no_splash /work/proj/v2/phys/flow/pnr.tcl > /work/exp/$run/$job.log 2>&1 &"
    echo "echo \$! > /work/jobs/$job.inpid"       # PID inside the container: stop with docker exec ... kill
    echo "wait \$!"
    echo "echo OPENROAD_RC=\$?"
} > $W/jobs/$job.cmd
$W/bg.sh $job $tmo

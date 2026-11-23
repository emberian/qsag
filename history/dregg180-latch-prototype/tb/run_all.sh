#!/bin/sh
# Run several testbench configurations in parallel (remote, cwd = project root).
#   tb/run_all.sh "<config>:<scenario>:<script> ..."
status=0
pids=""
for job in $1; do
    cfg=$(echo $job | cut -d: -f1); scen=$(echo $job | cut -d: -f2); scr=$(echo $job | cut -d: -f3)
    # each simulation carries its own wall-clock limit so that none outlives a cut-off shell
    ( timeout -k 5 ${SIM_TIMEOUT:-540} build/obj_sim/sim_qsag_ni_180 build/script_${scr:-full}.txt $cfg $scen > build/sim_${cfg}_${scen}.log 2>&1 ) &
    pids="$pids $!"
done
for pid in $pids; do wait "$pid" || status=1; done
for job in $1; do
    cfg=$(echo $job | cut -d: -f1); scen=$(echo $job | cut -d: -f2)
    echo "== $cfg / $scen: $(grep -c '^  \[ok\]' build/sim_${cfg}_${scen}.log) ok lines"
    grep -v '^  \[ok\]' build/sim_${cfg}_${scen}.log | tail -${TAILN:-12}
done

exit "$status"

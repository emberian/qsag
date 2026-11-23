#!/bin/sh
# hbox host side. Run stage slices one after another (one heavy job at a time), detached:
#   nohup setsid sh queue.sh <queue-file> > jobs/queue.log 2>&1 < /dev/null & echo $! > jobs/queue.pid
# Each line of the queue file: <run> <from> <to> <timeout-s> [KEY=VAL ...]   (use ~ for a space inside a value)
# A slice whose OpenROAD log has no "STAMP done" stops the remaining slices OF THAT RUN only.
W=/var/tmp/fable-dregg180-phys
bad=""
while read run from to tmo rest; do
    [ -z "$run" ] && continue
    case "$run" in \#*) continue ;; esac
    case " $bad " in *" $run "*) echo "skip $run $from $to (earlier slice failed)"; continue ;; esac
    set --
    for kv in $rest; do set -- "$@" "$(echo "$kv" | tr '~' ' ')"; done
    echo "$(date +%T) start $run $from $to"
    sh $W/proj/v2/phys/flow/job.sh "$run" "$from" "$to" "$tmo" "$@" || { echo "launch failed"; bad="$bad $run"; continue; }
    job=${run}_${from}_${to}
    until [ -f $W/jobs/$job.rc ]; do sleep 5; done
    if grep -q "^STAMP done" $W/exp/$run/$job.log 2>/dev/null; then echo "$(date +%T) done  $job rc=$(cat $W/jobs/$job.rc)"
    else echo "$(date +%T) FAIL  $job rc=$(cat $W/jobs/$job.rc)"; bad="$bad $run"; fi
done < "$1"
echo "$(date +%T) queue finished"

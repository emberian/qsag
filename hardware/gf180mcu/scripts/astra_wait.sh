#!/bin/sh
# Wait (bounded) for a job started by scripts/astra_bg.sh, then print its exit code and log tail.
#   scripts/astra_wait.sh <job-name> [max-wait-s] [tail-lines]
set -eu
HOST="${ASTRA_HOST:-hbox}"
RDIR="${ASTRA_RDIR:-/var/tmp/dregg180-astra}"
name="$1"; max="${2:-540}"; n="${3:-40}"
ssh -o ConnectTimeout=25 "$HOST" "cd $RDIR/jobs; t=0; while [ ! -e $name.rc ] && [ \$t -lt $max ]; do sleep 5; t=\$((t+5)); done; if [ -e $name.rc ]; then echo \"$name: rc=\$(cat $name.rc)\"; else echo \"$name: still running after ${max}s\"; fi; tail -n $n $name.log"

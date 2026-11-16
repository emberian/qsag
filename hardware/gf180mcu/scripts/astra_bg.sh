#!/bin/sh
# Start a detached job in the dregg180-astra container on the build host.
#   scripts/astra_bg.sh <job-name> <timeout-s> "<shell command, cwd = /work>"
# Writes <RDIR>/jobs/<job-name>.{pid,log,rc} on the host. The PID file names the setsid group
# leader of the job itself; stop a job only through that PID file.
set -eu
HOST="${ASTRA_HOST:-hbox}"
RDIR="${ASTRA_RDIR:-/var/tmp/dregg180-astra}"
name="$1"; to="$2"; cmd="$3"
printf '%s\n' "$cmd" | ssh -o ConnectTimeout=25 "$HOST" "mkdir -p $RDIR/jobs && cat > $RDIR/jobs/$name.cmd && cd $RDIR/jobs && rm -f $name.rc && (nohup setsid sh -c 'docker exec -i dregg180-astra timeout --kill-after=10s ${to}s nix --extra-experimental-features \"nix-command flakes\" --accept-flake-config develop path:/work/env --command sh -s < $name.cmd > $name.log 2>&1; echo \$? > $name.rc' < /dev/null > /dev/null 2>&1 & echo \$! > $name.pid) && cat $name.pid"

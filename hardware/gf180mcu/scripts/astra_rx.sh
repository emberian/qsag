#!/bin/sh
# All EDA execution stays in the dedicated persvati container. Command on stdin
# avoids interpolating caller text into an SSH shell command.
set -eu
TO=${ASTRARX_TIMEOUT:-1800}
TO_IN=$((TO - 15))
printf '%s\n' "$1" | ssh -o ConnectTimeout=25 persvati-remote \
  "SWARM_MEM_MAX=20G swarm-build timeout --kill-after=10s ${TO}s docker exec -i dregg180-astra timeout --kill-after=10s ${TO_IN}s nix --extra-experimental-features 'nix-command flakes' --accept-flake-config develop path:/work/env --command sh -s"

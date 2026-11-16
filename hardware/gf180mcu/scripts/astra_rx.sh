#!/bin/sh
# All EDA execution stays in the dedicated persvati container. Command on stdin
# avoids interpolating caller text into an SSH shell command.
set -eu
printf '%s\n' "$1" | ssh -o ConnectTimeout=25 persvati-remote \
  'SWARM_MEM_MAX=16G swarm-build timeout --kill-after=10s 600s docker exec -i dregg180-astra timeout --kill-after=10s 590s nix --extra-experimental-features "nix-command flakes" --accept-flake-config develop path:/work/env --command sh -s'

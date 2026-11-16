#!/bin/sh
# All EDA execution runs remotely inside `dregg180-astra` (defaults to fast `hbox`, 5.1 GHz / 123 GiB).
set -eu
HOST="${ASTRA_HOST:-hbox}"
TO="${ASTRARX_TIMEOUT:-1800}"
TO_IN=$((TO - 15))
if [ "$HOST" = "persvati-remote" ]; then
  WRAP="SWARM_MEM_MAX=20G swarm-build timeout --kill-after=10s ${TO}s"
else
  WRAP="timeout --kill-after=10s ${TO}s"
fi
printf '%s\n' "$1" | ssh -o ConnectTimeout=25 "$HOST" \
  "$WRAP docker exec -i dregg180-astra timeout --kill-after=10s ${TO_IN}s nix --extra-experimental-features 'nix-command flakes' --accept-flake-config develop path:/work/env --command sh -s"

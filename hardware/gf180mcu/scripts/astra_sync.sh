#!/bin/sh
set -eu
here="$(cd "$(dirname "$0")/.." && pwd)"
HOST="${ASTRA_HOST:-hbox}"
RDIR="${ASTRA_RDIR:-/var/tmp/dregg180-astra}"
if [ "$HOST" = "persvati-remote" ]; then RDIR="/tmp/dregg180-astra"; fi
rsync -rlt --omit-dir-times --exclude gf180mcu/ --exclude build/ --exclude runs/ --exclude 'librelane/runs/' \
  --exclude final/ --exclude 'spice/' --exclude 'pcb/' --exclude '__pycache__/' --exclude '*.pyc' --exclude .git/ --exclude .github/ \
  "$here"/ "${HOST}:${RDIR}/proj/"
rsync -rlt --omit-dir-times "$here/flake.nix" "$here/flake.lock" "${HOST}:${RDIR}/env/"

#!/bin/sh
# Push this directory to the build hosts (no EDA tool ever runs on the Mac).
#   scripts/rsync_to_remote.sh            -> persvati-remote:/tmp/qsag-ni-gf180mcu/proj
#   scripts/rsync_to_remote.sh hbox-remote
set -e
host="${1:-persvati-remote}"
here="$(cd "$(dirname "$0")/.." && pwd)"
ssh "$host" mkdir -p /tmp/qsag-ni-gf180mcu/proj
rsync -a --exclude gf180mcu/ --exclude build/ --exclude librelane/runs/ --exclude final/ \
    "$here"/ "$host":/tmp/qsag-ni-gf180mcu/proj/

#!/usr/bin/env bash
# Push sources to remote Linux build host (${QSAG_REMOTE_ASIC:-build-host:/work/qsag-asic/src}) / pull summaries back.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
case "${1:-push}" in
  push)
    rsync -a \
      --exclude logs \
      --exclude 'vec/*.hex' \
      --exclude 'synth/hier' \
      --exclude 'synth/netlists' \
      --exclude 'synth/work_*' \
      --exclude 'obj_*' \
      "$here"/ "${QSAG_REMOTE_ASIC:?set QSAG_REMOTE_ASIC=host:/path/to/asic/src}/"
    ;;
  pull)
    rsync -a \
      --exclude 'obj_*' \
      --exclude '*.o' \
      --exclude 'vec/*.hex' \
      --exclude 'synth/hier/*/*.v' \
      --exclude 'synth/hier/*/*.ys' \
      --exclude 'synth/netlists' \
      --exclude 'synth/work_*' \
      --exclude 'lec/work' \
      "${QSAG_REMOTE_ASIC:?set QSAG_REMOTE_ASIC=host:/path/to/asic/src}/" "$here"/
    ;;
esac

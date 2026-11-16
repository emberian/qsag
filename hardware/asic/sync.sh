#!/usr/bin/env bash
# Push sources to bb2 (builds run only there) / pull compact summaries, logs, and emitted specs back.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
case "${1:-push}" in
  push)
    rsync -a \
      --exclude logs \
      --exclude 'vec/*.hex' \
      --exclude 'vec/workloads.json' \
      --exclude 'synth/hier' \
      --exclude 'synth/netlists' \
      --exclude 'synth/work_*' \
      --exclude 'obj_*' \
      "$here"/ bb2:/home/build/qsag-ni-asic/src/
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
      bb2:/home/build/qsag-ni-asic/src/ "$here"/
    ;;
esac

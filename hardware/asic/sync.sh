#!/usr/bin/env bash
# Push sources to bb2 (builds run only there) / pull logs and generated files back.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
case "${1:-push}" in
  push) rsync -a --exclude logs --exclude 'obj_*' "$here"/ bb2:/home/build/qsag-ni-asic/src/ ;;
  pull) rsync -a --exclude 'obj_*' --exclude '*.o' --exclude 'work' bb2:/home/build/qsag-ni-asic/src/ "$here"/ ;;
esac

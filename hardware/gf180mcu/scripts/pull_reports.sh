#!/bin/sh
# Fetch result logs and reports from the build host into the tree (text only, no build output).
set -e
host="${1:-persvati-remote}"
here="$(cd "$(dirname "$0")/.." && pwd)"
r="$host:/tmp/qsag-ni-gf180mcu/proj"
mkdir -p "$here/tb/logs" "$here/lec/logs" "$here/synth/reports" "$here/librelane/reports"
rsync -a --include 'sim_*.log' --include 'lint.log' --exclude '*' "$r/build/" "$here/tb/logs/"
rsync -a --include 'lec_*.log' --exclude '*' "$r/build/" "$here/lec/logs/"
rsync -a --include 'synth_chip*.stat' --include 'area.txt' --include 'sta_*.txt' --exclude '*' "$r/build/" "$here/synth/reports/"
rsync -a --include 'll_*.log' --include 'll_summary.txt' --exclude '*' "$r/build/" "$here/librelane/reports/" 2>/dev/null || true

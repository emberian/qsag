#!/bin/sh
set -eu
here="$(cd "$(dirname "$0")/.." && pwd)"
rsync -rlt --omit-dir-times --exclude gf180mcu/ --exclude build/ --exclude runs/ --exclude 'librelane/runs/' \
  --exclude final/ --exclude 'spice/' --exclude 'pcb/' --exclude '__pycache__/' --exclude '*.pyc' --exclude .git/ --exclude .github/ \
  "$here"/ persvati-remote:/tmp/dregg180-astra/proj/
rsync -rlt --omit-dir-times "$here/flake.nix" "$here/flake.lock" persvati-remote:/tmp/dregg180-astra/env/

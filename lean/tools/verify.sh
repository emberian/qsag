#!/usr/bin/env bash
set -euo pipefail
if [[ "$(uname -s)" != Linux ]]; then
  echo 'Verification must run on Linux.' >&2
  exit 2
fi
cd "$(dirname "$0")/.."
export SWARM_MEM_MAX=12G
timeout --kill-after=10s 600s lake build
timeout --kill-after=10s 600s lake build AuditAxioms
timeout --kill-after=10s 600s lake comparator --paranoid

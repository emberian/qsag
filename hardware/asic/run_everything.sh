#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
bash run_sim.sh gen
exec bash tb/verify_auto.sh

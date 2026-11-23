#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
case "${1:-all}" in
  gen)
    python3 gen/gen_rtl.py rtl
    python3 gen/gen_vectors.py fixtures/lean_external_oracle_vectors.json vec ;;
  lint) exec bash tb/run.sh lint ;;
  units) exec bash tb/run.sh tb_units ;;
  top) exec bash tb/run.sh tb_top ;;
  all)
    bash run_sim.sh gen
    bash tb/verify_auto.sh lint command ;;
  *) exit 2 ;;
esac

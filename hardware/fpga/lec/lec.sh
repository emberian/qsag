#!/usr/bin/env bash
# Z3 / Bitwuzla equivalence proofs and canonical-form check of the carry-less multiplier.
#   lec.sh                         every required group in turn
#   lec.sh gl|glmut|gf|tower|anf   one group, sized to fit a 600 s slot
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p build/lec
groups=("$@")
[ ${#groups[@]} -eq 0 ] && groups=(gl glmut gf tower anf)
for g in "${groups[@]}"; do
    if [ "$g" = anf ]; then python3 lec/anf_check.py; else python3 lec/lec.py "$g"; fi
done

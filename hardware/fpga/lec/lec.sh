#!/usr/bin/env bash
# Z3 equivalence proofs and the canonical-form check of the carry-less multiplier.
#   lec.sh            every group in turn (longer than one 600 s build slot)
#   lec.sh gl|glmut|gf|try|anf   one group, sized to fit a 600 s slot
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p build/lec
groups=("$@")
[ ${#groups[@]} -eq 0 ] && groups=(gl glmut gf try anf)
for g in "${groups[@]}"; do
    if [ "$g" = anf ]; then python3 lec/anf_check.py; else python3 lec/lec.py "$g"; fi
done

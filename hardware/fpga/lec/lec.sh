#!/usr/bin/env bash
# Z3 / Bitwuzla equivalence proofs and canonical-form check of the carry-less multiplier.
#   lec.sh                                    every required group in turn
#   lec.sh gl|glmut|ext5|gf|comp|tower|anf|xbank    one group, sized to fit a 600 s slot
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p build/lec
groups=("$@")
[ ${#groups[@]} -eq 0 ] && groups=(gl glmut ext5 gf comp tower anf xbank)
for g in "${groups[@]}"; do
    if [ "$g" = anf ]; then
        mkdir -p build/verif_logs
        python3 lec/anf_check.py | tee build/verif_logs/anf_check.log
    else
        python3 lec/lec.py "$g"
    fi
done

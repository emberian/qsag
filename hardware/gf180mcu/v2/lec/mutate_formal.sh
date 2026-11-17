#!/bin/bash
# The proofs must fail on a broken design: each line of v2/tb/mutants.txt that touches dregg_rules.sv,
# dregg_seq.sv or dregg_egress.sv is applied to a copy of v2/rtl and the proofs are run on the copy.
# Prints, per mutant, whether a proof failed (found) or all passed (not seen by the properties).
B=build/v2
mkdir -p $B/fvmut
while IFS='|' read -r name file expr; do
    case "$file" in dregg_rules.sv|dregg_seq.sv) t=seq ;; dregg_egress.sv) t=egress ;; *) continue ;; esac
    d=$B/fvmut/$name
    rm -rf $d; mkdir -p $d/rtl
    cp v2/rtl/*.sv v2/rtl/*.svh $d/rtl/
    sed -i "$expr" $d/rtl/$file
    cmp -s $d/rtl/$file v2/rtl/$file && { echo "FORMAL MUTANT $name: the edit did not apply"; continue; }
    if RTLDIR=$d/rtl FVOUT=$d/fv bash v2/lec/run_formal.sh $t > $d/log.txt 2>&1 < /dev/null; then r="not seen by the properties"; else r="found"; fi
    echo "FORMAL MUTANT $name: $r"
done < v2/tb/mutants.txt | tee $B/fvmut/summary.txt

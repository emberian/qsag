#!/bin/bash
# Mutation check of the co-simulation: each mutant is one edit of a copy of v2/rtl; the bench must FAIL on
# it. Run from the chip directory:   bash v2/tb/mutate.sh
# A mutant the bench passes is printed as SURVIVED and the script exits 1.
# The list is v2/tb/mutants.txt: name | file | sed expression.
B=build/v2
mkdir -p $B/mut
while IFS='|' read -r name file expr; do
    [ -z "$name" ] && continue
    case "$name" in \#*) continue ;; esac
    d=$B/mut/$name
    rm -rf $d; mkdir -p $d
    cp v2/rtl/*.sv v2/rtl/*.svh $d/
    sed -i "$expr" $d/$file
    if cmp -s $d/$file v2/rtl/$file; then echo "MUTANT $name: the edit did not apply"; continue; fi
    if RTLDIR=$d JOBS=${JOBS:-16} bash v2/tb/run.sh fast 72 mut_$name > $B/mut/$name.log 2>&1 < /dev/null; then r=SURVIVED; else r=killed; fi
    grep -q "shards: 16 finished" $B/mut/$name.log || r="$r (run incomplete)"
    echo "MUTANT $name: $r   [$(grep -h 'ERROR\|ASSERT' $B/mut/$name.log | sed 's/transaction [0-9]*/transaction N/; s/(op [0-9a-f]*)//' | cut -c1-70 | sort | uniq -c | sort -rn | head -2 | tr '\n' ';')]"
    rm -rf $B/obj_mut_$name $d
done < v2/tb/mutants.txt | tee $B/mut/summary.txt
if grep -q "SURVIVED\|did not apply\|incomplete" $B/mut/summary.txt; then exit 1; fi
exit 0

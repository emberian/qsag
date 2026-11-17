#!/bin/sh
# hbox host side: key figures of one or more runs.  summ.sh <run> ...
W=/var/tmp/fable-dregg180-phys
for r in "$@"; do
  echo "================ $r"
  for L in $W/exp/$r/${r}_*.log; do
    [ -f "$L" ] || continue
    echo "--- $(basename $L)"
    grep -E "^METRIC (synth|placed|cts|ctsrt|grt)_(stdcell_area_um2|stdcells|added_cells|added_area_um2)|^METRIC .*(failed|fillcap)|^STAMP" $L | tr "\n" ";" | sed 's/METRIC //g; s/STAMP //g'; echo
    grep -E "RSZ-003[4-9]|Inserted [0-9]+ (buffers|hold)|RSZ-00(4[0-9]|5[0-9])|DPL-003[46]|DPL-0004|CTS-0018|CTS-0098|GPL_ERROR|RSZ_ERROR|CTS_ERROR|GRT_ERROR|DRT_ERROR|GRT-0018|GRT-0012|DRT-0199|DRT-0198|Number of violations|ANT-000[0-9]" $L | sed 's/\[INFO //;s/\[WARNING //;s/\[ERROR //' | sort | uniq -c | sort -rn | head -14 | cut -c1-130
    grep -E "legalized HPWL|original HPWL|average displacement|max displacement" $L | tail -4 | tr -s " " | tr "\n" ";"; echo
    awk '/Final congestion report/{f=1} f&&/^(Metal|Total)/{print}' $L | tail -6 | cut -c1-110
    for t in gpl placed cts ctsrt grt fin; do
      sed -n "/==== timing $t\$/,/==== end timing $t/p" $L | awk -v t=$t '
        /^---- corner/ {c=$3" "$4}
        /slack|^[A-Za-z_\[\]0-9\/.]+ .* -?[0-9]+\.[0-9]+ *$/ && c!="" { if ($0 ~ /-?[0-9]+\.[0-9]+ *$/) { if (!(c in s) || $NF+0 < s[c]+0) s[c]=$NF } }
        /^tns|^wns|^worst slack/ {all=all" "$0";"}
        END { for (k in s) printf "  %s %-14s worst %s\n", t, k, s[k]; if (all!="") print "  " t " all:" all }' | sort
    done
  done
done

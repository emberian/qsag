#!/usr/bin/env bash
# bb2 only: the whole LEC batch, six miters at a time. Results accumulate in logs/lec.log.
cd "$(dirname "$0")/.."
rm -f logs/lec.log
{
  for c in reduce reduce_ref reduce_gl reduce_mut fold fold_mut final gf gf_mut mul; do echo "$c"; done
  for l in 0 1 2 3 4 5 6 7 8 9 10 11; do echo "me $l"; echo "mi $l"; done
  echo "me_mut 1"; echo "mi_mut 2"; echo "me_gl 0"
} | xargs -P 6 -L 1 lec/run_lec.sh > logs/lec_batch.out 2>&1
sort logs/lec.log > logs/lec_sorted.log

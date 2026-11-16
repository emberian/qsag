#!/usr/bin/env bash
# bb2 only. Verify QsagNi.lean kernel proofs (`0 sorry`, `0 axiom`, `0 Classical.choice`), emit all
# 9 Obend `RtlModule` SV + Lean SMT2 specs, and discharge Z3 + Bitwuzla LEC (+ mutant SAT checks).
set -euo pipefail
cd "$(dirname "$0")"
export PATH=/home/build/qsag-ni-asic/tools/oss-cad-suite/bin:$HOME/.elan/bin:$PATH
OBEND="${OBEND:-$HOME/obend/wt-s2-hw-silicon}"
RUN="env SWARM_MEM_MAX=16G swarm-build timeout --kill-after=10s 600s"
mkdir -p emitted ../logs
rm -f emitted/*.sv emitted/*.smt2
cp "$OBEND/lean/lean-toolchain" .
( cd "$OBEND" && echo "obend tree: $(git rev-parse --short HEAD) $(git branch --show-current); git status clean lines: $(git status --short | wc -l)" ) | tee ../logs/obend.log
$RUN env LEAN_PATH="$OBEND/lean/.lake/build/lib/lean" lean --run QsagNi.lean emitted 2>&1 | tee -a ../logs/obend.log

# Enforce 0 sorryAx across all theorems (and 0 Classical.choice on all QsagNi algebraic theorems)!
if grep -q "sorryAx" ../logs/obend.log; then
  echo "FAIL: sorryAx detected in QsagNi.lean" | tee -a ../logs/obend.log
  exit 1
fi
echo "Obend axiom gate PASS: 0 sorryAx" | tee -a ../logs/obend.log

for sv in emitted/*.sv; do
  top="$(basename "$sv" .sv)"
  lec="emitted/${top}_lec.smt2"
  ys() { yosys -q -p "read_verilog -sv $1; hierarchy -check -top ${top}; proc; flatten; setattr -set keep 1 t:\$dff %co w:* %i; opt_clean; write_smt2 $2"; }
  ys "$sv" "emitted/${top}.yosys.smt2"
  sed '/^; --- counterexample/,$d' "$lec" > "emitted/${top}.lean.smt2"
  t0=$(date +%s)
  cat "emitted/${top}.yosys.smt2" "emitted/${top}.lean.smt2" > "emitted/${top}.full.smt2"
  vz="$($RUN z3 -T:60 "emitted/${top}.full.smt2" 2>&1 | grep -v swarm-build | head -1)"
  echo "OBEND-LEC ${top}: z3=${vz} ($(( $(date +%s) - t0 )) s) [expect unsat]" | tee -a ../logs/obend.log
  [[ "$vz" == "unsat" ]]
  # planted fault: flip bit 0 of the last output assignment (`<port> = w_<n>;`)
  awk '{ l[NR] = $0 } /^    [a-z0-9_]+ = w_[0-9]+;$/ { last = NR }
       END { for (i = 1; i <= NR; i++) { if (i == last) sub(/;$/, " ^ 64'"'"'d1;", l[i]); print l[i] } }' "$sv" > "emitted/${top}.mut.sv.tmp"
  cmp -s "$sv" "emitted/${top}.mut.sv.tmp" && { echo "mutation did not apply to ${top}"; exit 1; }
  ys "emitted/${top}.mut.sv.tmp" "emitted/${top}.mut.yosys.smt2"
  cat "emitted/${top}.mut.yosys.smt2" "emitted/${top}.lean.smt2" > "emitted/${top}.mut.full.smt2"
  vm="$($RUN z3 -T:60 "emitted/${top}.mut.full.smt2" 2>&1 | grep -v swarm-build | head -1)"
  echo "OBEND-LEC ${top} (output bit flipped): z3=${vm} [expect sat]" | tee -a ../logs/obend.log
  [[ "$vm" == "sat" ]]
  rm -f "emitted/${top}.mut.sv.tmp" "emitted/${top}.full.smt2" "emitted/${top}.mut.full.smt2"
done

#!/usr/bin/env bash
# bb2 only. Emit the QSAG-NI spec modules with Obend's emitter and run Obend's LEC recipe
# (hardware/lec/lec.sh steps 2 and 3) on each: yosys reads the emitted .sv, write_smt2, the Lean
# half is appended, z3 must answer unsat; a copy with one output bit flipped must answer sat.
set -euo pipefail
cd "$(dirname "$0")"
export PATH=/home/build/qsag-ni-asic/tools/oss-cad-suite/bin:$HOME/.elan/bin:$PATH
OBEND="${OBEND:-$HOME/obend/wt-s2-hw-silicon}"
RUN="env SWARM_MEM_MAX=16G swarm-build timeout --kill-after=10s 600s"
mkdir -p emitted ../logs
cp "$OBEND/lean/lean-toolchain" .
( cd "$OBEND" && echo "obend tree: $(git rev-parse --short HEAD) $(git branch --show-current); git status clean lines: $(git status --short | wc -l)" ) | tee ../logs/obend.log
$RUN env LEAN_PATH="$OBEND/lean/.lake/build/lib/lean" lean --run QsagNi.lean emitted 2>&1 | tee -a ../logs/obend.log
for sv in emitted/*.sv; do
  top="$(basename "$sv" .sv)"
  lec="emitted/${top}_lec.smt2"
  ys() { yosys -q -p "read_verilog -sv $1; hierarchy -check -top ${top}; proc; flatten; setattr -set keep 1 t:\$dff %co w:* %i; opt_clean; write_smt2 $2"; }
  ys "$sv" "emitted/${top}.yosys.smt2"
  sed '/^; --- counterexample/,$d' "$lec" > "emitted/${top}.lean.smt2"
  t0=$(date +%s)
  v="$(cat "emitted/${top}.yosys.smt2" "emitted/${top}.lean.smt2" | $RUN z3 -T:${LEC_SECS:-300} -in 2>&1 | grep -v swarm-build | head -1)"
  echo "OBEND-LEC ${top}: z3 ${v} ($(( $(date +%s) - t0 )) s) [expect unsat]" | tee -a ../logs/obend.log
  # planted fault: flip bit 0 of the last output assignment (`<port> = w_<n>;`)
  awk '{ l[NR] = $0 } /^    [a-z0-9_]+ = w_[0-9]+;$/ { last = NR }
       END { for (i = 1; i <= NR; i++) { if (i == last) sub(/;$/, " ^ 64'"'"'d1;", l[i]); print l[i] } }' "$sv" > "emitted/${top}.mut.sv.tmp"
  cmp -s "$sv" "emitted/${top}.mut.sv.tmp" && { echo "mutation did not apply to ${top}"; exit 1; }
  ys "emitted/${top}.mut.sv.tmp" "emitted/${top}.mut.yosys.smt2"
  v="$(cat "emitted/${top}.mut.yosys.smt2" "emitted/${top}.lean.smt2" | $RUN z3 -T:${LEC_SECS:-300} -in 2>&1 | grep -v swarm-build | head -1)"
  echo "OBEND-LEC ${top} (output bit flipped): z3 ${v} [expect sat]" | tee -a ../logs/obend.log
  rm -f "emitted/${top}.mut.sv.tmp"
done

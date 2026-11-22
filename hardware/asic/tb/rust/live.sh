#!/usr/bin/env bash
# Execute the Rust verifier with a live bidirectional command port.
set -euo pipefail
dir=$(mktemp -d "${TMPDIR:-$PWD}/live.XXXXXX")
mkfifo "$dir/tx" "$dir/rx"
./obj_tb_zkhem_v2_top/sim "+trace=$dir/tx" "+reply=$dir/rx" > "$dir/sim.log" 2>&1 &
sim_pid=$!
trap 'kill "$sim_pid" 2>/dev/null || true' EXIT
rust-unified/target/release/examples/deep5_live "$dir/tx" "$dir/rx" | tee "$dir/proof.log"
wait "$sim_pid"
grep -q 'RTL accepted full proof' "$dir/proof.log"
grep -q 'V2 PASS' "$dir/sim.log"
cp "$dir/proof.log" logs/live_proof.log
cp "$dir/sim.log" logs/live_port.log

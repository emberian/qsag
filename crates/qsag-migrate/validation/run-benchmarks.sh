#!/bin/sh
# Run from a QSAG workspace root on the designated Linux build host.
# Each invocation runs the full 438-repetition profile, including verification.
set -eu
logdir=crates/qsag-migrate/validation
mkdir -p "$logdir"
: > "$logdir/benchmark-host.log"
for test in \
    benchmarks::local_four_curve_benchmark \
    co_zk_mpc::tests::complete_distributed_bitcoin_proof_verifies \
    co_zk_mpc::tests::complete_distributed_ed25519_proof_verifies \
    co_zk_mpc::tests::complete_distributed_pallas_ak_proof_verifies \
    co_zk_mpc::tests::complete_distributed_bls12_381_pubkey_proof_verifies
do
    name=${test##*::}
    printf "%s\n" "$test" >> "$logdir/benchmark-host.log"
    date -u >> "$logdir/benchmark-host.log"
    uptime >> "$logdir/benchmark-host.log"
    cargo test --release -p qsag-migrate "$test" -- --exact --ignored --nocapture > "$logdir/$name.log" 2>&1
done

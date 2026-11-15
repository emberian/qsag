#!/usr/bin/env bash
# Run from the dedicated Linux validation checkout; never build on the Mac workspace.
set -euo pipefail
[[ $(uname -s) == Linux ]] || { echo 'Run this on hbox-remote.' >&2; exit 2; }
cd "$(dirname "$0")/../../.."
mkdir -p logs
export CARGO_BUILD_JOBS=${CARGO_BUILD_JOBS:-2}
export SWARM_MEM_MAX=${SWARM_MEM_MAX:-8G}
export MALLOC_ARENA_MAX=${MALLOC_ARENA_MAX:-2}
filters=(
    zk_hem::tests
    zk_hem::relation::tests
    zk_hem::protocol::tests
    zk_hem::blind_vc::tests
    zk_hem::multisig::tests
    zk_hem::recursive_whir::tests
    pcs::affine_schedule::
    pcs::pcs_unit_tests::explicit_classical_pcs_works_without_authorizing_aggregates
    recursion_census::tests
    recursive_fold::tests
    pcs::pcs_unit_tests::security_regimes_roundtrip_and_query_budgets
    pcs::pcs_unit_tests::whir_schedules_cover_all_supported_num_vars
    pcs::pcs_unit_tests::cdhz25_and_poseidon2_regimes_accept_honest_and_reject_tampered_openings
    tests::test_cdhz25_and_poseidon2_aggregates_end_to_end
    tests::test_shard_caps_match_pcs_limit
    recursive::tests::succinct_outer_hem_three_shards_roundtrip_and_tamper_rejection
    recursive::tests::commitment_relation_accepts_unbacked_summaries_and_evidence_gate_refuses_them
)
if (($#)); then filters=("$@"); fi
for filter in "${filters[@]}"; do
    log="logs/astra-${filter//::/-}.log"
    swarm-build timeout --kill-after=10s 600s cargo test --release -p qsag-agg --lib \
        "$filter" -- --nocapture --test-threads=1 > "$log" 2>&1
    rg 'test result:' "$log"
    if rg -q 'running 0 tests' "$log"; then echo "Unmatched test filter: $filter" >&2; exit 1; fi
done
swarm-build timeout 600s cargo clippy -p qsag-agg --all-targets --no-deps -- -D warnings \
    > logs/astra-clippy.log 2>&1
swarm-build timeout 600s cargo check -p qsag-agg --no-default-features \
    > logs/astra-nostd.log 2>&1
echo 'Targeted zk-Hem algebra, committed protocol and applications, child PCS, hierarchy boundary, clippy and no_std checks passed.'

#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0 OR MIT
#
# External Differential Validation, Property-Based Testing (`proptest`),
# Lean 4 Executable Specification Oracle, and `libFuzzer` Harness Runner.
#
# Usage:
#   ./scripts/run_differential_validation.sh                # Run full differential proptest + Lean spec-oracle suite
#   ./scripts/run_differential_validation.sh --regen-lean   # Regenerate Lean 4 spec-oracle vectors via `lake` first
#   ./scripts/run_differential_validation.sh --fuzz [secs]  # Also run coverage-guided libFuzzer campaign (default 15s/target)
#   ./scripts/run_differential_validation.sh --fuzz-only [secs] # Resume just the fuzz campaign

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REGEN_LEAN=0
RUN_FUZZ=0
RUN_TESTS=1
FUZZ_SECS=15

while [[ $# -gt 0 ]]; do
    case "$1" in
        --regen-lean)
            REGEN_LEAN=1
            shift
            ;;
        --fuzz|--fuzz-only)
            if [[ "$1" == --fuzz-only ]]; then RUN_TESTS=0; fi
            RUN_FUZZ=1
            if [[ $# -ge 2 && "$2" =~ ^[0-9]+$ ]]; then
                FUZZ_SECS="$2"
                shift 2
            else
                shift
            fi
            ;;
        *)
            echo "Unknown option: $1" >&2
            exit 2
            ;;
    esac
done

if [[ "$RUN_FUZZ" -eq 1 ]]; then
    # Normalize decimal input (including 08), rejecting zero and arithmetic overflow.
    if [[ ! "$FUZZ_SECS" =~ ^0*([1-9][0-9]{0,4})$ ]]; then
        echo "Fuzz duration must be 1..86400 seconds." >&2
        exit 2
    fi
    FUZZ_SECS=$((10#${BASH_REMATCH[1]}))
    if [[ "$FUZZ_SECS" -gt 86400 ]]; then
        echo "Fuzz duration must be 1..86400 seconds." >&2
        exit 2
    fi
fi

if [[ "$REGEN_LEAN" -eq 1 ]]; then
    echo "==> Regenerating Lean 4 executable specification vectors..."
    FIXTURES_DIR="${REPO_ROOT}/validation/tests/fixtures"
    mkdir -p "${FIXTURES_DIR}"
    (
        cd "${REPO_ROOT}/lean"
        lake build qsag-kat
        lake env lean --run "${REPO_ROOT}/validation/lean/ExternalSpecOracle.lean" \
            > "${FIXTURES_DIR}/lean_external_oracle_vectors.json"
        ./.lake/build/bin/qsag-kat --cross-kat \
            > "${FIXTURES_DIR}/lean_cross_kat.jsonl"
        ./.lake/build/bin/qsag-kat \
            > "${FIXTURES_DIR}/lean_kat_snapshot.json"
        lake env lean --run "${FIXTURES_DIR}/lean_pack256_limbs56.gen.lean" \
            > "${FIXTURES_DIR}/lean_pack256_limbs56.jsonl"
    )
fi

if [[ "$RUN_TESTS" -eq 1 ]]; then
    echo "==> Running external differential validation & property-based test suite..."
    (
        cd "${REPO_ROOT}/validation"
        cargo test --release --locked -- --nocapture
    )
fi

if [[ "$RUN_FUZZ" -eq 1 ]]; then
    echo "==> Running coverage-guided libFuzzer campaign (${FUZZ_SECS}s per target)..."
    # `-sanitizer-coverage-level` defaults to 0. At that level the sancov pass inserts
    # no counters and the other three flags do nothing, so the level must be explicit.
    SANCOV_RUSTFLAGS="--cfg fuzzing -Cpasses=sancov-module -Cllvm-args=-sanitizer-coverage-level=4 -Cllvm-args=-sanitizer-coverage-inline-8bit-counters -Cllvm-args=-sanitizer-coverage-pc-table -Cllvm-args=-sanitizer-coverage-trace-compares"
    (
        cd "${REPO_ROOT}/fuzz"
        # These LLVM coverage flags work with the repository's pinned stable compiler.
        # Use the same toolchain for host detection and compilation; an unrelated
        # installed nightly can predate our dependencies' minimum Rust version.
        HOST_TRIPLE="$(rustc -vV | awk '/^host:/ { print $2 }')"
        RUSTFLAGS="${SANCOV_RUSTFLAGS}" cargo build --release --locked --target "${HOST_TRIPLE}"
        for target in \
            fuzz_whir_agg_verify \
            fuzz_blind_vc_and_agg_decode \
            fuzz_fips205_and_fts_decode \
            fuzz_diff_hashes_and_ntt \
            fuzz_quorum_frames \
            fuzz_policy_tokens \
            fuzz_cred_wire \
            fuzz_hologram_and_subtree_decode; do
            echo "--- Fuzzing ${target} (${FUZZ_SECS}s) ---"
            CORPUS_DIR="${REPO_ROOT}/fuzz/corpus/${target}"
            ARTIFACT_DIR="${REPO_ROOT}/fuzz/artifacts/${target}"
            mkdir -p "${CORPUS_DIR}" "${ARTIFACT_DIR}"
            if [[ "$target" == fuzz_whir_agg_verify ]]; then
                # Deterministic entry into the structured real-capability proof mutator.
                # Keep an existing seed intact when resuming a corpus.
                if [[ ! -e "${CORPUS_DIR}/capability-structured" ]]; then
                    printf '\312\120' > "${CORPUS_DIR}/capability-structured"
                fi
            fi
            RUN_LOG="${ARTIFACT_DIR}/last_run.log"
            "./target/${HOST_TRIPLE}/release/${target}" "${CORPUS_DIR}" \
                -max_total_time="${FUZZ_SECS}" \
                -max_len=1048576 -timeout=20 -rss_limit_mb=4096 \
                -artifact_prefix="${ARTIFACT_DIR}/" \
                -print_final_stats=1 2>&1 | tee "${RUN_LOG}"
            # An uninstrumented binary still runs and exits 0; it just never reports
            # an edge count. Refuse to call that a fuzzing campaign.
            if ! grep -Eq '^#[0-9]+[[:space:]]+DONE[[:space:]]+cov: [1-9]' "${RUN_LOG}"; then
                echo "${target}: libFuzzer reported no edge coverage; the build is not instrumented." >&2
                exit 1
            fi
        done
    )
fi

echo "==> External differential validation completed cleanly."

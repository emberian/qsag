# Hem WHIR MIR Verification (`aeneas/lean-whir`)

Run `AENEAS_TOOLS_DIR=<tool-directory> ./aeneas/extract_whir.sh` from the repository root on Linux. The script runs standalone Rust tests on `aeneas/qsag-whir-verified`, extracts Rust MIR to LLBC via Charon, translates LLBC to Lean 4.35 via Aeneas (`Types.lean` and `Funs.lean`, zero `*External.lean`), normalizes module headers, builds both default targets (`QsagWhirVerified` and `audit-whir-mir-axioms`) under `lake build --wfail`, executes the kernel dependency audit, and checks production linkage, hierarchy tests, Clippy (`-D warnings`), and `no_std` compilation. Generated `Types.lean` and `Funs.lean` are checked in; regenerate them instead of editing their bodies, and check SHA-256 provenance via `python3 scripts/check_extraction_provenance.py --crate qsag-whir-verified`.

## Production Linkage (`crates/qsag-agg`)

`qsag-whir-verified` is a zero-dependency `#![no_std]` + `#![forbid(unsafe_code)]` Rust crate linked by `crates/qsag-agg`. Production callers and library-only coverage are distinguished below:

- **Canonical Wire Decoding (`field.rs`):** `decode_canonical_u64` and `decode_canonical_ext4` enforce `< GOLDILOCKS_P` on all 64-bit and 256-bit wire elements.
- **Quartic Extension & Affine/CWYZ Folding (`pcs/affine.rs`, `pcs.rs`):** Production calls `cwyz_bridge_claim_step`, `eval_quadratic_sumcheck_wire`, and `affine_cascade_claim_step`. The acceptance wrappers `verify_affine_duet_fold_step`, `verify_cwyz_duet_fold_step`, and `verify_cwyz_bridge_claim_step` have test-only callers. `qsag_whir_verified::Ext4` uses polynomial order `[1, u, u², u³]` modulo `u⁴ − 7`; the production adapter maps its Karatsuba tower order `[1, u², u, u³]`, and `towerToPoly_mul_hom` in `Arithmetic.lean` proves exact multiplicative isomorphism.
- **Terminal/OOD Equality, PoW, & Query Indexing (`pcs.rs`, `arithmetize.rs`):** Production calls `verify_ood_pin_eq`, `verify_stage_pow_mask`, and `canonical_query_group_idx`. The arbitrary-slice polynomial pin wrapper `verify_ext4_univariate_at_base_pin` currently has test-only callers.
- **Indexed Canopy Merkle Ordering (`pcs.rs`):** `step_merkle_pair_order` returns `MerklePair` carrying `TAG_CANOPY_MERKLE_INTERNAL = 0x00` along with direction-bit-ordered `(left, right)` 32-byte siblings, consumed directly by `hash_merkle_internal` inside `verify_canopy_multiproof` (where internal nodes use tag `0x00` and the tree root uses tag `0x01`).
- **Overflow-Free Hierarchical Quorum Summation (`recursive.rs`):** `checked_quorum_sum` validates non-empty equal-length slices, positive per-shard and global quorum floors, per-shard threshold satisfaction, and checked 64-bit natural-number summation.

## Fold and Horner integration contract

The extracted Rust exports `fold_duet_affine_ext4(v0, v1, inv_two_xk, inv_two,
xk_sq, theta, alpha, beta)` and `eval_univariate_ext4_at_base(coeffs, z)` are
ready for the production PCS adapters. They delegate to the extracted
CWYZ fold (`cwyz_duet_fold`) and descending-index Horner loop
(`eval_ext4_univariate_at_base`); the production names themselves are
present in generated `Funs.lean`. `Proofs.lean` proves their total refinements
and the stronger coset-recovery / ascending-polynomial statements.

Inputs and outputs use `Ext4` in polynomial basis, with base-field parameters as
`u64`. Convert production tower limbs with permutation `[0, 2, 1, 3]` in both
directions. Horner coefficients are ordered by ascending degree, and an empty
slice returns zero. Production integration must adapt the coefficient slice as
well as the result. These functions retain the extracted modular arithmetic;
performance parity with the optimized production field implementation is not
established by the proofs.

The standalone Rust tests in `tests/production_entrypoints.rs` recover known
even/odd components from cosets, verify dual-functional bridge steps, check
perturbation rejection across all four `verify_*` entrypoints, and compare
polynomial evaluation against an ascending power sum, including zero, empty,
and modulus-boundary cases. Switching the current `pcs.rs` fold and `field.rs`
Horner call sites to these exports remains a separate integration change; their
availability does not establish production adoption.

## Lean 4.35 Theorem Coverage, Six-Kernel Replay, & Axiom Audit

- **`Arithmetic.lean`:** Proves total checked-integer modular refinements (`add_refines`, `sub_refines`, `mul_refines`), full Goldilocks and `Ext4` (`u⁴ = 7`) commutative ring laws via a constructive Horner normalizer (`0 Classical.choice`), Karatsuba tower isomorphism (`towerToPoly_mul_hom`), algebraic coset soundness for `duet_fold` and `cwyz_duet_fold`, dual linear-functional soundness for `cwyz_bridge_claim_step`, Boolean hypercube sum soundness for `eval_quadratic_sumcheck_wire`, `affine_cascade_claim_step` refinement, and ascending-degree Horner equivalence (`hornerSpec_eq_evalPolyAscending`).
- **`Proofs.lean`:** Proves totality and exact bidirectional `Result.ok ... ↔ spec` theorems for all extracted functions, constants, and verifier gates — including arbitrary-slice `loopFuel` invariants for `eval_ext4_univariate_at_base`, `eval_univariate_ext4_at_base`, `verify_ext4_univariate_at_base_pin`, `verify_ood_pin_eq`, and `checked_quorum_sum`, coset-recovery theorems for `duet_fold`, `cwyz_duet_fold`, `fold_duet_affine_ext4`, `verify_affine_duet_fold_step`, and `verify_cwyz_duet_fold_step`, dual-functional soundness for `cwyz_bridge_claim_step` and `verify_cwyz_bridge_claim_step`, BitVec/modulo characterization for `verify_stage_pow_mask`, tag+ordering characterization (`step_merkle_pair_order_tag_eq`, `tag = TAG_CANOPY_MERKLE_INTERNAL = 0#u8`) for `step_merkle_pair_order`, and `MAX_U64_WORD` quorum-bound linkage (`checked_quorum_sum_le_max_u64_word`) — paired with 10 `#tooth` mutation-sensitivity and premise-inhabitedness witnesses.
- **`AuditWhirMirAxioms.lean` & `scripts/check_lean_policy.py`:** Default build target (`lake build --wfail`) with a `Classical.choice` negative control, 83 anchored `.thmInfo` declarations, and a 100% `QsagWhirVerified/Funs.lean` symbol-coverage gate (`37/37` definitions: `31` extracted Rust items plus `6` split `_loop` / `_loop.body` helpers, excluding `tooth_*` witnesses so concrete test theorems cannot mask a missing specification theorem, verified by three built-in negative controls). Walks every constant (including private declarations via `setExporting false`) across `QsagWhirVerified*` and `Aeneas*`, permitting only `{propext, Quot.sound}` (`0 sorry`, `0 Classical.choice`, `0 Lean.ofReduceBool`). `scripts/check_lean_policy.py` independently enforces the same 100% non-`tooth_*` statement coverage across `Arithmetic.lean` + `Proofs.lean`, `QsagWhirVerifiedChallenge.lean`, `comparator.json`, and `AuditWhirMirAxioms.lean`.
- **`QsagWhirVerifiedChallenge.lean` & `comparator.json`:** Independent challenge statement module (`0` proof-module imports, 57 replayed theorems: 47 non-`tooth_*` specification/soundness theorems covering 100% of extracted `Funs.lean` items plus 10 `#tooth` witnesses) replayed by `lake comparator --paranoid` inside a read-only `bubblewrap` sandbox across all six kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`).

Every Lean file in `aeneas/lean-whir` stays within the `<= 12` `@[expose]` declaration limit and avoids file-wide `@[expose] public section`. The mask-to-modulo proof uses a constructive bit induction, so the audit also rejects indirect dependencies on choice in imported arithmetic lemmas.

From the repository root, run `python3 crates/qsag-agg/tests/check_affine_witness_parity.py` to
check all 46 deployed Rust witness rows against `AffineProximityGaps` and pin both folding
thresholds to `< 2000`. This read-only check complements the Rust finite-witness test and the
Lean certificate.

## Scope & Protocol Assumptions

These theorems prove exact MIR-to-specification refinement of the extracted verifier kernels and loop invariants, not the end-to-end cryptographic security reduction of WHIR. Hash collision resistance, Fiat–Shamir random-oracle unpredictability, and out-of-band authentication of the ordered disjoint `ShardHemPolicy` registry remain protocol-level assumptions. Two-layer hierarchical aggregation (`crates/qsag-agg/src/recursive.rs`) verifies every regional `JortsPoseidon2` or `CorduroyPoseidon2` `Hem` proof in parallel and binds the length-framed (`encode_multi_frame`) policy registry root, message digest, epoch floor, and `checked_quorum_sum` quorum weights without compressing child verifiers into a recursive SNARK circuit.

All production scoped workers in `qsag-agg`, including nested arithmetic kernels, share one
nonblocking permit budget. Saturated budgets and OS thread-creation failures execute the job
on the caller, and chunk results retain input order.

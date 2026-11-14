# Hem WHIR MIR Verification (`aeneas/lean-whir`)

Run `AENEAS_TOOLS_DIR=<tool-directory> ./aeneas/extract_whir.sh` from the repository root on Linux. The script runs standalone Rust tests on `aeneas/qsag-whir-verified`, extracts Rust MIR to LLBC via Charon, translates LLBC to Lean 4.35 via Aeneas (`Types.lean` and `Funs.lean`, zero `*External.lean`), normalizes module headers, builds both default targets (`QsagWhirVerified` and `audit-whir-mir-axioms`) under `lake build --wfail`, executes the kernel dependency audit, and checks production linkage, hierarchy tests, Clippy (`-D warnings`), and `no_std` compilation. Generated `Types.lean` and `Funs.lean` are checked in; regenerate them instead of editing their bodies.

## Production Linkage (`crates/qsag-agg`)

`qsag-whir-verified` is a zero-dependency `#![no_std]` + `#![forbid(unsafe_code)]` Rust crate directly linked by `crates/qsag-agg` across every hot verifier gate:

- **Canonical Wire Decoding (`field.rs`):** `decode_canonical_u64` and `decode_canonical_ext4` enforce `< GOLDILOCKS_P` on all 64-bit and 256-bit wire elements.
- **Quartic Extension & Affine/CWYZ Folding (`pcs/affine.rs`, `pcs.rs`):** `verify_affine_duet_fold_step`, `verify_cwyz_duet_fold_step`, `cwyz_bridge_claim_step`, `verify_cwyz_bridge_claim_step`, `eval_quadratic_sumcheck_wire`, and `affine_cascade_claim_step`. `qsag_whir_verified::Ext4` uses polynomial order `[1, u, u², u³]` modulo `u⁴ − 7`; the production adapter maps its Karatsuba tower order `[1, u², u, u³]`, and `towerToPoly_mul_hom` in `Arithmetic.lean` proves exact multiplicative isomorphism.
- **Arbitrary-Slice Polynomial Pin, Terminal/OOD Equality, PoW, & Query Indexing (`pcs.rs`, `arithmetize.rs`):** `eval_ext4_univariate_at_base`, `verify_ext4_univariate_at_base_pin`, `verify_ood_pin_eq`, `verify_stage_pow_mask`, and `canonical_query_group_idx`.
- **Indexed Canopy Merkle Ordering (`pcs.rs`):** `step_merkle_pair_order` returns `MerklePair` carrying `TAG_CANOPY_MERKLE_INTERNAL = 0x00` along with direction-bit-ordered `(left, right)` 32-byte siblings, consumed directly by `hash_merkle_internal` inside `verify_canopy_multiproof` (where internal nodes use tag `0x00` and the tree root uses tag `0x01`).
- **Overflow-Free Hierarchical Quorum Summation (`recursive.rs`):** `checked_quorum_sum` validates non-empty equal-length slices, positive per-shard and global quorum floors, per-shard threshold satisfaction, and checked 64-bit natural-number summation.

## Lean 4.35 Theorem Coverage & Kernel Axiom Audit

- **`Arithmetic.lean`:** Proves total checked-integer modular refinements (`add_refines`, `sub_refines`, `mul_refines`), full Goldilocks and `Ext4` (`u⁴ = 7`) commutative ring laws via a constructive Horner normalizer (`0 Classical.choice`), Karatsuba tower isomorphism (`towerToPoly_mul_hom`), algebraic coset soundness for `duet_fold` and `cwyz_duet_fold`, dual linear-functional soundness for `cwyz_bridge_claim_step`, Boolean hypercube sum soundness for `eval_quadratic_sumcheck_wire`, `affine_cascade_claim_step` refinement, and ascending-degree Horner equivalence (`hornerSpec_eq_evalPolyAscending`).
- **`Proofs.lean`:** Proves totality and exact bidirectional `Result.ok ... ↔ spec` theorems for all extracted verifier gates — including arbitrary-slice `loopFuel` invariants for `eval_ext4_univariate_at_base`, `verify_ext4_univariate_at_base_pin`, `verify_ood_pin_eq`, and `checked_quorum_sum`, general BitVec/modulo characterization for `verify_stage_pow_mask`, and tag+ordering characterization (`tag = 0#u8`) for `step_merkle_pair_order` — paired with `#tooth` mutation-sensitivity witnesses.
- **`AuditWhirMirAxioms.lean`:** Default build target (`lake build --wfail`) with a `Classical.choice` negative control that walks every constant in `QsagWhirVerified*` and `Aeneas*`, permitting only `{propext, Quot.sound}` (`0 sorry`, `0 Classical.choice`, `0 Lean.ofReduceBool`).

The package retains 12 `@[expose]` definitions. The mask-to-modulo proof uses a constructive
bit induction, so the audit also rejects indirect dependencies on choice in imported arithmetic
lemmas. The compatibility elaborator contains only the options and marker attributes used by
this extraction.

From the repository root, run `python3 crates/qsag-agg/tests/check_affine_witness_parity.py` to
check all 46 deployed Rust witness rows against `AffineProximityGaps` and pin both folding
thresholds to `< 2000`. This read-only check complements the Rust finite-witness test and the
Lean certificate.

## Scope & Protocol Assumptions

These theorems prove exact MIR-to-specification refinement of the extracted verifier kernels and loop invariants, not the end-to-end cryptographic security reduction of WHIR. Hash collision resistance, Fiat–Shamir random-oracle unpredictability, and out-of-band authentication of the ordered disjoint `ShardHemPolicy` registry remain protocol-level assumptions. Two-layer hierarchical aggregation (`crates/qsag-agg/src/recursive.rs`) verifies every regional `JortsPoseidon2` or `CorduroyPoseidon2` `Hem` proof in parallel and binds the length-framed (`encode_multi_frame`) policy registry root, message digest, epoch floor, and `checked_quorum_sum` quorum weights without compressing child verifiers into a recursive SNARK circuit.

All production scoped workers in `qsag-agg`, including nested arithmetic kernels, share one
nonblocking permit budget. Saturated budgets and OS thread-creation failures execute the job
on the caller, and chunk results retain input order.

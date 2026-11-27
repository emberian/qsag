# Quintic `Fp5` WHIR & `QSAGHQM2` MIR Verification (`aeneas/lean-whir`)

Run `AENEAS_TOOLS_DIR=<tool-directory> ./aeneas/extract_whir.sh` from the repository root on Linux. The script runs standalone Rust tests on `aeneas/qsag-whir-verified`, extracts Rust MIR to LLBC via Charon, translates LLBC to Lean 4.35 via Aeneas (`Types.lean` and `Funs.lean`, zero `*External.lean`), normalizes module headers, builds the default targets (`Aeneas`, `QsagWhirVerified`, `QsagWhirSpecWeld`, `AuditWhirMirAxioms`, and `audit-whir-mir-axioms`) under `lake build --wfail`, executes the kernel dependency audit, and checks production linkage, hierarchy tests, Clippy (`-D warnings`), and `no_std` compilation. Generated `Types.lean` and `Funs.lean` are checked in; regenerate them instead of editing their bodies, and check SHA-256 provenance via `python3 scripts/check_extraction_provenance.py --crate qsag-whir-verified`.

## Production Linkage (`crates/qsag-agg`)

`qsag-whir-verified` is a zero-dependency `#![no_std]` + `#![forbid(unsafe_code)]` Rust crate linked directly by `crates/qsag-agg` on its live quintic `Fp5 = F_p[X]/(X^5 - 3)` (`p = 2^64 - 2^32 + 1`, `FP5_NONRESIDUE_W = 3`) `zk-Hem v2` and `QSAGHQM2` verification paths:

- **Canonical Wire Decoding (`zk_hem/v2/field5.rs`, `zk_hem/v2/pcs.rs`):** `load_le_u64_40`, `load_le_u64_56`, `decode_canonical_u64`, `decode_canonical_fp5_limbs`, `decode_canonical_fp5` (40-byte LE `Fp5`), `decode_canonical_gl24_limbs`, and `decode_canonical_gl24_digest` (56-byte LE 7-limb `Poseidon2-GL-w24` digest) enforce `< GOLDILOCKS_P` on every wire limb.
- **Quintic `Fp5` Ring, Frobenius & Affine/CWYZ Folding (`zk_hem/v2/field5.rs`, `zk_hem/v2/pcs.rs`):** `fp5_zero`, `fp5_one`, `fp5_from_base`, `fp5_eq`, `fp5_add`, `fp5_sub`, `fp5_neg`, `fp5_scale`, `fp5_mul` (`X^5 = 3`), and `fp5_frobenius` (`FROBENIUS_ZETA5_1..4`) use the exact power basis `[1, X, X^2, X^3, X^4]` shared coordinate-for-coordinate with `Qsag.QuinticGoldilocks`. Production folding and dual-bridge gates call `affine_combine_fp5`, `duet_fold_fp5`, `verify_affine_duet_fold_step_fp5`, `cwyz_duet_fold_fp5`, `verify_cwyz_duet_fold_step_fp5`, `cwyz_bridge_claim_step_fp5`, `verify_cwyz_bridge_claim_step_fp5`, and `eval_quadratic_sumcheck_wire_fp5`.
- **Horner, OOD Pin & Query Indexing (`zk_hem/v2/pcs.rs`):** `eval_fp5_univariate_at_base`, `verify_fp5_univariate_at_base_pin`, `verify_ood_pin_eq_fp5`, and `canonical_query_group_idx`.
- **400-Bit & `Poseidon2-GL-w24` Canopy Merkle Ordering (`zk_hem/v2/pcs.rs`):** `step_merkle_pair_order_400` orders 50-byte (`400`-bit `TurboSHAKE256`) child digests by direction bit `(idx >> level) & 1` with `level < 64`; `step_merkle_pair_order_gl24` enforces 7-limb Goldilocks canonicity on both `(node, sibling)` `Gl24Digest` inputs before ordering.
- **Quorum Summation & `QSAGHQM2` / Schedule Envelopes (`recursive.rs`, `zk_hem/v2/`):** `checked_quorum_sum` validates overflow-free 64-bit hierarchical quorum sums; `verify_qsaghqm2_header` checks the 8-byte `"QSAGHQM2"` ASCII magic, `QSAGHQM2_PROFILE_TURBO400 = 1` / `QSAGHQM2_PROFILE_GL24 = 2`, active signer bounds, and payload length equality; `verify_quintic_schedule_envelope` enforces `log_cells ∈ [16, 28]`, stage count `3` (`≤ 22`) or `4` (`23..28`), `early_stop_vars ∈ [1, 8]`, and `early_stop_vars + folded_vars_sum = log_cells`.

## Row sumcheck and Canopy openings

The live row verifier absorbs each 360-byte round and passes the resulting challenges to `verify_qsaghqm2_row_rounds_at`. The extracted function starts at zero, checks all nine canonical samples per accepted round, enforces the Boolean sum, and interpolates at the transcript challenge. The production verifier checks the resulting claim against the trace columns.

For each sampled query set, `qsaghqm2_opening_bounds` returns the end of the fiber symbols and the end of the sibling commitments. The extracted function validates each field limb, counts siblings from the sorted query indices, and enforces the selected digest encoding. The production verifier hashes the same slices and reconstructs the committed root with `verify_canopy`. The live verifier passes every 200-byte CWYZ fold block and its transcript challenges to `verify_qsaghqm2_cwyz_folds_at`. After the final queries are known, `verify_qsaghqm2_multiproof_and_rounds` checks the entire payload and its exact end. Its returned row claim must equal the claim already checked against the trace relation.

## Lean verification

`Proofs.lean` gives total `Result.ok` specifications for canonical decoding, row interpolation, and sibling counting. `Canonical.lean` interprets the row chain in `Qsag.QuinticGoldilocks`. `CanopyCount.lean` proves that the number of siblings computed from adjacent sorted indices is exactly `Qsag.steinerSiblingCount`. `Opening.lean` relates accepted byte intervals and profile-specific digest encodings to those specifications.

`QsagWhirSpecWeld` checks canonical coverage of all 86 extracted definitions, including the generated loop helpers. The MIR audit checks every anchored theorem and requires every comparator obligation to have an anchor. The allowed axioms are `propext` and `Quot.sound`. Run the external checker replay from this package with the configured toolchain.

```sh
COMPARATOR_BWRAP="$PWD/comparator-bwrap.py" lake comparator --paranoid
```

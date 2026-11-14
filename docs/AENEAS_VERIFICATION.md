# Aeneas Rust MIR verification

This reference describes the generated Rust MIR model and the Lean 4.35.0 interface
`QsagMirProofs`. The inventory below describes the earlier primitive export surface;
the live export files are authoritative as protocol guards are added.

## Pants guards and production linkage

The project now comprises 13 crates: 12 root workspace packages plus this separate
extraction workspace. Its guard surface includes WOTS+C, BDOZ, BeltLatch,
Waistband and poison-latch transitions in addition to arithmetic and sponges.
The extraction policy is **0 FunsExternal / 0 Classical.choice / 0 sorry**.
Claims attach to the generated functions and theorem premises, not every similarly
named production implementation. Fresh Charon/Aeneas extraction, comparison of
generated bodies, direct production dependencies and bridges over `QsagVerified.Funs`
remain active integration work.

A verified authorization check does not establish complete mediation while callers
can own raw shares, construct outputs independently or reuse unrelated permits.
The remaining boundary must own secrets and bind candidate bytes, message/profile,
party set, resource lease, poison generation and durable receipt before release.
Safe Rust can forget an affine value; resource burn must precede release capability
creation and must not rely solely on `Drop`.

**Verify your code, test your specs:** native `lake exe spec-oracle`, Rust↔Lean
differential/metamorphic cases and clause-drop mutations complement these proofs.
They must consume freshly generated artifacts and exercise nonempty domains;
finite parity tests do not establish universal refinement. Six-kernel
`comparator --paranoid` CI challenges replay selected exports; full generated-module
axiom coverage and exact-source release gating remain explicit obligations.
See [ASSURANCE.md](../ASSURANCE.md) for the protocol/POSIX/QROM and ISA/ELF pillars.

## Source correspondence and scope

The extraction input, `aeneas/qsag-verified`, is a self-contained `#![no_std]` crate
with `#![forbid(unsafe_code)]`.

| Category | Surface | Evidence and boundary |
| --- | --- | --- |
| Differential-parity primitives | Goldilocks and GoldilocksExt2; Wiedemann Gf16, Gf256, Tower128; Shamir evaluation and Lagrange reconstruction; Keccak-f[1600], SHAKE256, cSHAKE256; FIPS 205 ADRS, WOTS+, F, and TSW | `tests/parity_qsag_core.rs` compares executed cases bit-for-bit with `crates/qsag-core`. `tests/unit_kat.rs` includes NIST FIPS 202 and SP 800-185 known-answer tests. Testing complements the MIR proofs; it does not prove universal correspondence between the crates. |
| Standalone reference models | Affine EpochLatch with randomizer binding; affine BdozVerifierSession2Lane two-lane MAC verifier; two-of-three RssShare64 gates; Tower256 | The extracted crate defines these models independently. Their Lean theorems apply to those definitions. Crash-safe EpochLatch durability requires the caller to persist its write-ahead log before releasing a grant. |

Goldilocks inversion has an exact modular-exponent specification and canonical output
bound. The seven-input witness checks one multiplicative inverse; these statements do
not establish primality or a universal nonzero inverse law. The Keccak zero-state
witness excludes a constant-zero implementation, without excluding every constant
function or establishing cryptographic security.

The BDOZ exports prove totality for arbitrary opening slices, exact single-opening
acceptance, rejection of incorrect MAC lanes, and irreversible burn with zeroed key
lanes after rejection. Every subsequent request on a burned session rejects.
The extracted session stores `alpha_lanes`, and each opening has one `chal_weight`;
the acceptance specification uses that weight's exact nonzero check.

## Extraction and proof architecture

`extract.sh` invokes Rust checking, Charon MIR extraction, and Aeneas with
`-backend lean -split-files`. `QsagVerified/Types.lean` and `QsagVerified/Funs.lean`
are machine-generated artifacts. Rust changes require regeneration. Guarded
customization-length arithmetic uses primitive unsigned operations without an
external-function axiom module.

The hand-written `QsagVerified/Proofs.lean` imports Common, Goldilocks, Gf256,
TowerBdoz, ShamirDkg, HashEpoch, and Bdoz. Binary-field algebra and wide-tower
operations compile independently. HashEpoch groups separately compiled WOTS, ADRS,
sponge, TSW, epoch, and Keccak witness modules. The sponge proofs have no ADRS
dependency, so authentication and address proofs can proceed in parallel. Keccak's concrete witness uses kernel-checked
primitive-operation certificates for each round. Library precompilation is disabled.
Each long hand-written Lean file has at most twelve exposure attributes. Public
specification definitions are exposed where downstream reduction requires them.
`QsagMirProofs.lean` includes reduction examples and a one-step trace check.

## Trusted computing base and prelude semantics

The semantic chain includes Rust source and MIR generation, Charon, Aeneas, the
hand-written Lean 4.35 prelude, and Lean's kernel. The functional claims do not verify
LLVM compilation, hardware timing, physical randomness, or storage durability.

The prelude fixes `usize` to 64 bits. Checked arithmetic, shifts, and indexing return
`.fail` when their guards fail. `Array.from_slice` enforces its length invariant.
Arrays carry exact lengths; slices carry machine-size length bounds. Generated loops
use `loopMaxFuel = 2^65`, returning `.div` on exhaustion. Successful loop proofs exhibit
bounded evaluations and transfer them through `loop_ok_of_loopFuel`. Rust domain
errors are values: `.ok (.Err e)` differs from prelude execution failure `.fail e`.

`@[discriminant]` maps discriminantless enum constructors to constructor indices.
`core::fmt::Debug` formatting strings are excluded from cryptographic functional
specifications. Array cloning applies the provided element clone operation and
preserves length.

The complete exported axiom census contains only `propext` and `Quot.sound`, the
standard propositional-extensionality and quotient-soundness axioms. Every exported
theorem has zero transitive `Classical.choice` dependencies. There are zero
`sorryAx`, custom axioms, `Lean.ofReduceBool`, and `Lean.trustCompiler` dependencies.
The proofs use neither admitted obligations nor native evaluation as proof evidence.
The census checks dependency closure; a source scan alone would not establish it.

## Reproducible checks

Run tests and extraction on the designated Linux toolchains. From the repository root:

```sh
cargo test --manifest-path aeneas/qsag-verified/Cargo.toml
```

After refreshing the extraction, run the clean check from `aeneas/lean`:

```sh
LEAN_NUM_THREADS=4 lake build
```

The measured clean build completed all 37 jobs in **17.91 seconds** with zero errors
and warnings, using Lean 4.35.0 and 20 threads on Linux. This is a historical measurement, not a current build-time guarantee. Build concurrency and available CPU resources affect the measurement.

This one-line census, also run from `aeneas/lean`, prints the transitive axioms of every
exported declaration, including every theorem:

```sh
python3 -c 'from pathlib import Path; s=Path("QsagMirProofs.lean").read_text().split("export qsag_verified.proofs (",1)[1].split(")",1)[0]; print("import QsagMirProofs"); print("\n".join("#print axioms qsag_verified.proofs."+n for n in s.split()))' | lake env lean --stdin
```

## Export inventory

Targets are relative to `qsag_verified` unless identified as model components.
Statements apply with the premises in their corresponding Lean declarations.

| Export | MIR target or model | Statement |
| --- | --- | --- |
| `bdoz_authenticate_open_total` | `tower.verify_mac_2lane_with_burn` | Every session, batch, and opening slice returns a session and Boolean result. |
| `bdoz_authenticate_open_spec` | `tower.verify_mac_2lane_with_burn` | One-opening acceptance iff the input session is unburned, the weight is nonzero, the commitment matches, and both MAC lanes match. |
| `bdoz_mac_one_time_burn_spec` | `tower.verify_mac_2lane_with_burn` | Totality; rejection or an already burned session yields a burned session with zero key lanes, and all subsequent requests reject. |
| `bdoz_tampered_mac_rejected` | `tower.verify_mac_2lane_with_burn` | Any incorrect peer MAC lanes force rejection of a single opening. |
| `pureTower128Mul` | `tower.tower128_mul` | Pure result of the total Tower128 multiplication. |
| `bdozMaskedSum` | `BDOZ model component` | Masked value plus the challenge-weighted opening. |
| `bdozFoldedKey` | `BDOZ model component` | Per-lane masked key plus the challenge-weighted wire key. |
| `bdozExpectedMacLanes` | `BDOZ model component` | The two expected authentication lanes, using the folded keys and session keys. |
| `bdozOpening1` | `BDOZ model component` | Length-one opening slice. |
| `GoldilocksP` | `goldilocks.GOLDILOCKS_PRIME` | Natural-number modulus 2^64 − 2^32 + 1. |
| `goldilocks_canon_spec` | `goldilocks.goldilocks_canon` | Canonical residue and output bound for every u64 input. |
| `goldilocks_add_spec` | `goldilocks.goldilocks_add` | Canonical modular addition of the two input residues. |
| `goldilocks_sub_spec` | `goldilocks.goldilocks_sub` | Canonical modular subtraction of the two input residues. |
| `goldilocks_reduce128_spec` | `goldilocks.goldilocks_reduce128` | Canonical reduction of a u128 input modulo p. |
| `goldilocks_mul_spec` | `goldilocks.goldilocks_mul` | Canonical product of the two input residues. |
| `goldilocks_pow7_spec` | `goldilocks.goldilocks_pow7` | Canonical seventh power. |
| `goldilocks_inv_spec` | `goldilocks.goldilocks_inv` | None exactly for zero residue or zero computed inverse; some for a nonzero computed inverse. |
| `goldilocks_inv_or_zero_spec` | `goldilocks.goldilocks_inv_or_zero` | Totality; exact (a mod p)^(p−2) mod p, canonical bound, and zero-input behavior. |
| `tooth_goldilocks_inv_seven` | `goldilocks.goldilocks_inv_or_zero; goldilocks.goldilocks_mul` | The computed inverse of seven multiplies by seven to one. |
| `tooth_epoch_acquire_and_retry_ok` | `threshold.EpochLatch.new; threshold.EpochLatch.acquire_or_retry` | Initialization, successful fresh acquisition, and successful exact retry with preserved grant binding and changed retry flag. |
| `goldilocks_inv_or_zero_total` | `goldilocks.goldilocks_inv_or_zero` | Total canonical output; this theorem does not assert a multiplicative inverse law for Goldilocks. |
| `tower_gf256_boolean_iff_frobenius` | `tower.gf256_frobenius_residual; tower.gf256_is_boolean_frobenius` | Residual zero exactly at 0 and 1; exact Boolean result. |
| `tower128_mul_total` | `tower.tower128_mul` | Totality for all inputs. |
| `tower_gf256_inv_or_zero_spec` | `tower.gf256_inv_or_zero` | Zero maps to zero; every nonzero input multiplies with the returned value to one. |
| `pureGf256Mul` | `tower.gf256_mul` | Pure Wiedemann multiplication expression. |
| `gf256_mul_eq_pure` | `tower.gf256_mul` | Exact MIR-to-pure multiplication equality. |
| `pureGf256Mul_comm` | `tower.gf256_mul via gf256_mul_eq_pure` | Commutativity. |
| `pureGf256Mul_xor_right` | `tower.gf256_mul via gf256_mul_eq_pure` | Right distributivity over XOR. |
| `pureGf256Mul_xor_left` | `tower.gf256_mul via gf256_mul_eq_pure` | Left distributivity over XOR. |
| `dkg_beaver_frobenius_eval_spec` | `threshold.dkg_beaver_frobenius_eval_gf256` | Under the stated Beaver-product premise, evaluation returns the Frobenius residual of the secret. |
| `verify_mac_2lane_rejects_empty` | `tower.verify_mac_2lane` | An empty opening slice is rejected. |
| `verify_mac_2lane_burn_irreversible` | `tower.verify_mac_2lane_with_burn` | A burned session rejects with zeroed lanes; every returned rejection burns the session and zeroes its lanes. |
| `rss_reconstruct_share_roundtrip` | `threshold.rss_share_u64; threshold.rss_reconstruct` | Sharing with arbitrary masks and reconstructing returns the secret. |
| `rss_xor_homomorphic` | `threshold.rss_xor` | Reconstruction commutes with sharewise XOR. |
| `rss_not_spec` | `threshold.rss_not` | Reconstruction commutes with bitwise negation. |
| `tooth_dkg_inconsistent_shares_rejected` | `threshold.dkg_verify_shamir_2of3_key_bit_gf256` | Points [1,2,3] and inconsistent shares [0,1,1] return false. |
| `rss_and_gate_spec` | `threshold.rss_and_gate` | Recombining the three output shares gives AND of the recombined input shares. |
| `rss_keccak_chi_lane_spec` | `threshold.rss_keccak_chi_lane` | Recombining the output gives the Keccak chi lane expression. |
| `pureGf256Mul_zero` | `tower.gf256_mul via gf256_mul_eq_pure` | Right zero law. |
| `pureGf256Mul_zero_left` | `tower.gf256_mul via gf256_mul_eq_pure` | Left zero law. |
| `pureGf256Mul_one` | `tower.gf256_mul via gf256_mul_eq_pure` | Right identity law. |
| `pureGf256Mul_assoc` | `tower.gf256_mul via gf256_mul_eq_pure` | Associativity by linear extension from 512 basis triples. |
| `tower_gf256_field_laws` | `tower.gf256_mul` | Combined zero, identity, commutativity, associativity, and distributivity laws; inverse and cancellation laws are separate declarations. |
| `tower_gf256_inv_spec` | `tower.gf256_inv` | Zero returns none; nonzero inputs return an inverse whose MIR multiplication gives one. |
| `pureGf256Mul_eq_zero_iff` | `tower.gf256_mul via gf256_mul_eq_pure` | A product is zero exactly when at least one factor is zero. |
| `pureGf256Inv` | `tower.gf256_inv_or_zero` | Pure exponentiation expression used by the extracted inverse. |
| `gf256_inv_or_zero_eq_pure` | `tower.gf256_inv_or_zero` | Exact MIR-to-pure inversion equality. |
| `pureGf256Inv_mul` | `tower.gf256_inv_or_zero; tower.gf256_mul` | Inverse of a product is the product of inverses, including zero inputs. |
| `goldilocks_from_canonical_spec` | `goldilocks.goldilocks_from_canonical` | Acceptance exactly below p; noncanonical inputs return their raw value in the error. |
| `goldilocks_neg_spec` | `goldilocks.goldilocks_neg` | Canonical additive negation. |
| `goldilocks_ext2_add_spec` | `goldilocks.goldilocks_ext2_add` | Canonical componentwise modular addition. |
| `goldilocks_ext2_mul_spec` | `goldilocks.goldilocks_ext2_mul` | Canonical extension product using the generated Karatsuba expression and nonresidue 7. |
| `tower256_mul_total` | `tower.tower256_mul` | Totality for all inputs. |
| `pureHornerGf256Prefix` | `threshold.shamir_eval_poly_gf256` | Pure descending-coefficient Horner recurrence with an explicit accumulator and prefix length. |
| `pureHornerGf256` | `threshold.shamir_eval_poly_gf256` | Horner evaluation of the whole coefficient list from zero. |
| `shamir_eval_poly_gf256_spec` | `threshold.shamir_eval_poly_gf256` | Arbitrary-length slice refinement through structural fuel induction and loop_ok_of_loopFuel. |
| `pureHornerGoldilocksPrefix` | `threshold.shamir_eval_poly_goldilocks` | Pure descending-coefficient Horner recurrence with an explicit accumulator and prefix length. |
| `pureHornerGoldilocks` | `threshold.shamir_eval_poly_goldilocks` | Horner evaluation of the whole coefficient list from zero. |
| `shamir_eval_poly_goldilocks_spec` | `threshold.shamir_eval_poly_goldilocks` | Arbitrary-length slice refinement through structural fuel induction and loop_ok_of_loopFuel. |
| `shamir_validate_points_gf256_rejects_empty` | `threshold.shamir_validate_points_gf256` | The empty point list returns false. |
| `shamir_validate_points_gf256_3_spec` | `threshold.shamir_validate_points_gf256` | Three points are accepted exactly when nonzero and pairwise distinct; both nested MIR loops use bounded-fuel witnesses. |
| `shamir_lagrange_at_zero_gf256_rejects_invalid` | `threshold.shamir_lagrange_at_zero_gf256` | An empty point list or a share-length mismatch returns none. |
| `keccak_f1600_round_total` | `keccak.keccak_f1600_round` | All fixed-index accesses and updates succeed for one round. |
| `keccak_f1600_zero_state_nonconstant` | `keccak.keccak_f1600` | The zero input returns a nonzero output, excluding constant-zero behavior. |
| `keccak_f1600_total` | `keccak.keccak_f1600` | Totality of the 24-round composition using the round theorem. |
| `ct_eq_bytes32_spec` | `tower.ct_eq_bytes32` | The returned Boolean is exactly decidable equality of the two arrays. |
| `fips205_wots_chain_oob_none` | `fips205.fips205_wots_chain` | A start above 15 or a start-plus-steps above 15 returns none. |
| `fips205_wots_chain_zero_steps` | `fips205.fips205_wots_chain` | At a valid start, zero steps returns the input; the actual loop is discharged with one unit of fuel. |
| `tsw_canonical_target_sum_spec` | `fips205.tsw_canonical_target_sum` | Widths below two return none; otherwise the returned value is floor(ell1*(w−1)/2). |
| `WellFormedWal` | `threshold.EpochLatch` | The next epoch does not exceed the maximum; any bound record refers to an earlier epoch. |
| `epoch_latch_new_spec` | `threshold.EpochLatch.new` | Initialization at epoch zero, unbound state, invariant, and exact key and maximum fields. |
| `epoch_latch_advance_spec` | `threshold.epoch_latch_advance` | Totality on well-formed states; complete success and error predicates. Success binds the request key and epoch, assigns next, increments it, and clears the record. |
| `epoch_latch_advance_seals_prior_epochs` | `threshold.epoch_latch_advance; threshold.EpochLatch.acquire_or_retry` | After a successful advance, a matching-key request below the new next epoch returns NonSequentialEpoch. |
| `gfSlice2` | `threshold Shamir functions` | Two- and three-element array-to-slice constructors. |
| `gfSlice3` | `threshold Shamir functions` | Two- and three-element array-to-slice constructors. |
| `shamir_lagrange_at_zero_gf256_2of2_spec` | `threshold.shamir_eval_poly_gf256; threshold.shamir_lagrange_at_zero_gf256` | Linear polynomial evaluation and reconstruction of its constant at distinct nonzero points. |
| `shamir_lagrange_at_zero_gf256_3of3_spec` | `threshold.shamir_eval_poly_gf256; threshold.shamir_lagrange_at_zero_gf256` | Quadratic polynomial evaluation and reconstruction at three distinct nonzero points. |
| `shamir_degree_reduce_2of3_gf256_spec` | `threshold.shamir_degree_reduce_2of3_gf256` | Degree-two local products are reshared with arbitrary slopes; two reduced shares reconstruct the original constant. |
| `ValidPoints3` | `Shamir model` | Three nonzero, pairwise distinct array elements. |
| `dkg_linear_key_bit_gf256_spec` | `threshold.dkg_verify_shamir_2of3_key_bit_gf256` | Affine shares at valid points are accepted exactly for zero-or-one constant. |
| `dkg_inconsistent_reconstructions_rejected` | `threshold.dkg_verify_shamir_2of3_key_bit_gf256` | Unequal adjacent-pair reconstructions at valid points force rejection. |
| `dkg_verify_shamir_2of3_key_bit_gf256_spec` | `threshold.dkg_verify_shamir_2of3_key_bit_gf256` | Totality for arbitrary point and share arrays; acceptance iff points are valid and shares lie on one affine polynomial with zero-or-one constant. |
| `fips205AdrsTypeTag` | `fips205.decode_fips205_adrs` | Big-endian word at bytes 16 through 19. |
| `fips205_adrs_decode_encode_spec` | `fips205.decode_fips205_adrs; fips205.encode_fips205_adrs` | Any successful decoding re-encodes to its exact input bytes, including tree_hi. |
| `fips205_adrs_roundtrip_spec` | `fips205.encode_fips205_adrs; fips205.decode_fips205_adrs` | Every address encodes successfully and decodes to itself. |
| `fips205_adrs_decode_invalid_type_none` | `fips205.decode_fips205_adrs` | Every type word above six returns none. |
| `natPrefixSum` | `fips205 WOTS functions` | Natural prefix sum, checksum sum, and high/low nibble specifications. |
| `wotsChecksumNat` | `fips205 WOTS functions` | Natural prefix sum, checksum sum, and high/low nibble specifications. |
| `wotsBase16Digits` | `fips205 WOTS functions` | Natural prefix sum, checksum sum, and high/low nibble specifications. |
| `wots_extract_base16_digits_spec` | `fips205.wots_extract_base16_digits` | Thirty-two bounded digits with exact high/low nibble values. |
| `wots_checksum_base16_spec` | `fips205.wots_checksum_base16` | Exact sum of 15 minus each low nibble, bounded by 480. |
| `fips205_wots_checksum_spec` | `fips205.fips205_wots_checksum` | Thirty-five bounded digits; the prefix preserves the message digits and the final three digits encode the checksum. |
| `wots_checksum_strict_antitone` | `fips205.wots_checksum_base16` | A componentwise decrease with at least one strict decrease strictly increases the checksum. |
| `fips205_f_total` | `fips205.fips205_f` | Totality through address encoding, three sponge absorbs, finalization, and squeezing. |
| `fips205_wots_chain_compose` | `fips205.fips205_wots_chain` | Two consecutive bounded chains equal the combined chain, with total successful intermediate and final results. |
| `digitsNatSum` | `fips205.tsw_check_target_sum` | Natural-number sum of the complete digit list. |
| `tsw_check_target_sum_spec` | `fips205.tsw_check_target_sum` | Totality and acceptance exactly when length, digit range, and natural sum match the requested parameters. |
| `EpochAdvanceError` | `threshold.epoch_latch_advance` | Exact key, sequence, and exhaustion error guards. |
| `EpochFreshError` | `threshold.EpochLatch.acquire_or_retry` | Exact fresh-request sequence and exhaustion error guards. |
| `EpochAcquireError` | `threshold.EpochLatch.acquire_or_retry` | Complete error predicate for key, state, sequence, exhaustion, digest, and randomizer checks. |
| `epochWitnessBytes` | `Executable epoch witnesses` | A fixed 32-byte binding value. |
| `epochWitnessChanged` | `Executable epoch witnesses` | A distinct 32-byte binding value. |
| `traceAssignedEpochs` | `EpochTrace` | Epochs assigned by successful explicit advances. |
| `EpochAcquireSuccess` | `threshold.EpochLatch.acquire_or_retry` | Successful-grant invariant, bindings, and exact retry-versus-fresh transition predicate. |
| `epoch_latch_acquire_or_retry_spec` | `threshold.EpochLatch.acquire_or_retry` | Totality on well-formed states and complete success and error predicates, including fresh grants and exact retries. |
| `epoch_latch_key_binding_mismatch` | `threshold.EpochLatch.acquire_or_retry` | Explicit key, message, and retry-randomizer rejection branches. |
| `epoch_latch_equivocation_rejected` | `threshold.EpochLatch.acquire_or_retry` | Explicit key, message, and retry-randomizer rejection branches. |
| `epoch_latch_randomizer_mismatch` | `threshold.EpochLatch.acquire_or_retry` | Explicit key, message, and retry-randomizer rejection branches. |
| `EpochTurn` | `threshold.EpochLatch.acquire_or_retry; threshold.epoch_latch_advance` | Multi-turn execution relation and historical grant projection. |
| `EpochTrace` | `threshold.EpochLatch.acquire_or_retry; threshold.epoch_latch_advance` | Multi-turn execution relation and historical grant projection. |
| `traceGrants` | `threshold.EpochLatch.acquire_or_retry; threshold.epoch_latch_advance` | Multi-turn execution relation and historical grant projection. |
| `epoch_latch_multiturn_safety` | `threshold.EpochLatch` | Invariant preservation, bounded grants and assigned epochs, consistent repeated grants, distinct advance epochs, and disjointness between advance epochs and grant epochs. |
| `tooth_goldilocks_noncanonical_rejected` | `goldilocks.goldilocks_from_canonical` | The raw modulus is rejected. |
| `tooth_gf256_nonboolean_rejected` | `tower.gf256_is_boolean_frobenius` | The element 2 is rejected. |
| `tooth_shamir_duplicate_points_rejected` | `threshold.shamir_validate_points_gf256` | The point list [1,1,2] is rejected through the three-point theorem. |
| `tooth_adrs_invalid_type_rejected` | `fips205.decode_fips205_adrs` | Address bytes with type word 7 are rejected. |
| `tooth_tsw_wrong_sum_rejected` | `fips205.tsw_check_target_sum` | A single digit 7 is rejected for target 8, via the actual MIR loop. |
| `tooth_epoch_equivocation_rejected` | `threshold.EpochLatch.acquire_or_retry` | Changing the digest on a bound epoch is rejected. |
| `tooth_epoch_r_rand_drift_rejected` | `threshold.EpochLatch.acquire_or_retry` | Changing the randomizer on a bound epoch is rejected. |
| `tooth_epoch_advance_seals_retry` | `threshold.epoch_latch_advance; threshold.EpochLatch.acquire_or_retry` | Advancing from a bound state clears the record; retrying its prior epoch then returns NonSequentialEpoch. |

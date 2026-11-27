# Aeneas Rust MIR verification

This reference describes the two generated Rust MIR verification workspaces in this
repository and their Lean 4.35.0 interfaces:

1. **`aeneas/qsag-verified` → `aeneas/lean`** (`QsagVerified`, `QsagMirProofs`,
   `QsagSpecWeld`, `QsagCustodyWeld`, `AuditMirAxioms`, `QsagVerifiedChallenge`)
2. **`aeneas/qsag-whir-verified` → `aeneas/lean-whir`** (`QsagWhirVerified`,
   `AuditWhirMirAxioms`, `QsagWhirVerifiedChallenge`)

## Workspace layout, custody welds, and production linkage

The repository comprises **13 root Cargo workspace packages** under `crates/`
and **2** standalone `#![no_std]` + `#![forbid(unsafe_code)]` Aeneas MIR extraction
packages (`aeneas/qsag-verified` and `aeneas/qsag-whir-verified`).

Both extraction workspaces enforce **0 `FunsExternal` / 0 `Classical.choice` / 0 `sorry`**
across all library and proof modules, with SHA-256 source/prelude/output provenance
checked by `scripts/check_extraction_provenance.py`:

- **Core primitives, protocol guards, and custody weld (`aeneas/qsag-verified` → `aeneas/lean`):**
  Covers Goldilocks (`p = 2^64 - 2^32 + 1`) and `GoldilocksExt2`, Wiedemann binary
  towers (`Gf16`, `Gf256`, `Tower128`, `Tower256`), Shamir sharing and degree
  reduction, Keccak-f[1600] / SHAKE256 / cSHAKE256, FIPS 205 ADRS / WOTS+ / TSW,
  two-lane BDOZ MAC sessions (`BdozVerifierSession2Lane`, `BdozOpeningGuard2Lane`),
  `EpochLatch`, `VerifiedBeltQuorumGuard` (`authenticated_belt`), and `RssShare64`.
  `QsagSpecWeld.lean` is the root of the primitive welds (`RealSpecFieldWeld`,
  `RealSpecHashWeld`, `RealSpecTowerWeld`, `RealSpecKeccakWeld`), which identify the extracted
  Goldilocks, binary-tower and Keccak-f[1600] functions with the canonical `lean/Qsag`
  specifications (`Qsag.keccakF1600`, `Qsag.towerMul`). `QsagCustodyWeld.lean` is the root of
  the protocol-level welds: `RealSpecBeltWeld` relates `VerifiedBeltQuorumGuard` grants to the
  custodian masks of `Qsag.JortsBeltLatchAndQuorumSwitching`, and
  `AuthenticatedBeltAndRealSpecWeld` / `RealSpecGuardBoundary` relate the extracted RSS cut
  session, velocity guard, ML-DSA release gate and belt-latch kernel to their
  `Qsag.MirSpecBridge` machines by lockstep forward simulation.
- **Quintic WHIR verifier kernels (`aeneas/qsag-whir-verified` → `aeneas/lean-whir`).**
  The public Hem and committed-mask paths use the same five-limb power basis for
  `Fp5 = F_p[X]/(X^5 - 3)`, with `FP5_NONRESIDUE_W = 3`. The table follows the
  calls from `crates/qsag-agg/src/` into the extracted library.

| Operation | Rust consumer and extracted symbols |
| --- | --- |
| Canonical decoding | `field.rs` calls `decode_canonical_u64`. `zk_hem/v2/field5.rs` calls `decode_canonical_fp5` (40 bytes) and `hem_quintic/tree.rs` calls `decode_canonical_gl24_digest` (56 bytes). Their limb constructors `decode_canonical_fp5_limbs` and `decode_canonical_gl24_limbs` enforce a strict modulus check on every coefficient. |
| Folding and bridge | `zk_hem/v2/pcs.rs` calls `cwyz_duet_fold_fp5` and `cwyz_bridge_claim_step_fp5`. Their arithmetic reaches `fp5_add`, `fp5_sub`, `fp5_scale`, `fp5_mul` and `affine_combine_fp5`. `zk_hem/v2/protocol.rs` calls `eval_quadratic_sumcheck_wire_fp5`. |
| Terminal checks and indexing | `zk_hem/v2/pcs.rs` uses `eval_fp5_univariate_at_base`, `verify_fp5_univariate_at_base_pin` and `verify_ood_pin_eq_fp5`. The public verifier also checks the OOD pin in `hem_quintic/rows.rs` and `hem_quintic/whir.rs`. The challenge sampler in `zk_hem/v2/hash.rs` calls `canonical_query_group_idx`. |
| Merkle, envelope and quorum | `hem_quintic/tree.rs` uses `step_merkle_pair_order_400` and `step_merkle_pair_order_gl24`. `hem_quintic.rs` checks `verify_qsaghqm2_header` and `verify_quintic_schedule_envelope`. `zk_hem/v2/params.rs` also checks the schedule envelope. `recursive.rs` uses `checked_quorum_sum`. |

The extraction also covers `fp5_neg`, `fp5_frobenius`, the affine-only
`duet_fold_fp5`, and the predicates `verify_affine_duet_fold_step_fp5`,
`verify_cwyz_duet_fold_step_fp5` and `verify_cwyz_bridge_claim_step_fp5`.
The PCS recomputes CWYZ fold and bridge values directly. The parity tests in `field5.rs` compare extracted field operations and CWYZ predicates with native arithmetic. The standalone `tests/production_entrypoints.rs` also exercises the affine predicate.

A verified authorization check does not establish complete mediation while callers
can own raw shares, construct outputs independently or reuse unrelated permits.
The remaining boundary must own secrets and bind candidate bytes, message/profile,
party set, resource lease, poison generation and durable receipt before release.
Safe Rust can forget an affine value; resource burn must precede release capability
creation and must not rely solely on `Drop`.

**Verify your code, test your specs:** native `lake exe spec-oracle`, Rust↔Lean
differential/metamorphic cases and `#tooth` mutation-sensitivity witnesses complement
these proofs. Six-kernel `comparator --paranoid` CI challenges replay both
`QsagVerifiedChallenge` (`aeneas/lean`) and `QsagWhirVerifiedChallenge`
(`aeneas/lean-whir`), paired with private-environment (`setExporting false`) axiom
audits (`AuditMirAxioms` and `AuditWhirMirAxioms`).
See [ASSURANCE.md](../ASSURANCE.md) for the protocol/POSIX/QROM and ISA/ELF pillars.

## Production-called versus standalone functions (`extraction-coverage.json`)

A proof about an extracted function says something about production only if production calls
that function, or is related to it through a shared specification.
`scripts/gen_extraction_coverage.py` records this for every `pub fn` of
`aeneas/qsag-verified/src/**` in `aeneas/qsag-verified/extraction-coverage.json` (and the
rendered `extraction-coverage.md`). The analysis is lexical: comments and literals are blanked,
`use` trees and aliases are resolved, `#[cfg(test)]` modules are separated, and nothing is
type-checked, so `direct-lexical` and `reached` through a `.method(` edge are
over-approximations.

The manifest on disk classifies **197** functions, each with exactly one status:

| Status | Functions | Meaning |
| --- | ---: | --- |
| `direct` | 82 | A non-test call site in `crates/**` names the function. |
| `direct-lexical` | 56 | Only `.method(` call sites, in files whose `use` imports the receiver type. |
| `reached` | 36 | Not called from `crates/**`, but called transitively inside `qsag-verified` by a function that is. |
| **Production-called** | **174 (88.3%)** | |
| `spec-welded` | 0 | No production path; a Lean weld refers to the definition. |
| `proof-only` | 13 | No production path and no weld; only Lean proofs refer to it. |
| `test-only` | 8 | Referred to by tests alone. |
| `unreferenced` | 2 | Nothing refers to it. |
| **Standalone library** | **23 (11.7%)** | |
| **Total** | **197** | `pub fn`s with no definition in `Funs.lean`: 0. |

The production-called subtotal includes direct, direct-lexical and reached functions. The standalone subtotal includes the remaining four classes.

| Source module | `direct` | `direct-lexical` | `reached` | `spec-welded` | `proof-only` | `test-only` | `unreferenced` | Total |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `authenticated_belt.rs` | 3 | 12 | 0 | 0 | 0 | 0 | 0 | 15 |
| `belt_latch_kernel.rs` | 3 | 5 | 1 | 0 | 0 | 0 | 0 | 9 |
| `cred_and_hd_guards.rs` | 4 | 4 | 4 | 0 | 5 | 2 | 2 | 21 |
| `fips205.rs` | 8 | 0 | 4 | 0 | 0 | 0 | 0 | 12 |
| `goldilocks.rs` | 15 | 0 | 0 | 0 | 0 | 0 | 0 | 15 |
| `keccak.rs` | 4 | 0 | 5 | 0 | 0 | 0 | 0 | 9 |
| `opening_guard.rs` | 1 | 3 | 0 | 0 | 0 | 4 | 0 | 8 |
| `pants_and_quorum_guards.rs` | 7 | 15 | 14 | 0 | 1 | 0 | 0 | 37 |
| `policy_and_addr.rs` | 9 | 10 | 4 | 0 | 0 | 0 | 0 | 23 |
| `rss_cut_session.rs` | 2 | 7 | 1 | 0 | 0 | 0 | 0 | 10 |
| `threshold.rs` | 16 | 0 | 1 | 0 | 7 | 2 | 0 | 26 |
| `tower.rs` | 10 | 0 | 2 | 0 | 0 | 0 | 0 | 12 |

Production calls include Goldilocks, GF(16), GF(256) and Tower128 arithmetic in `qsag-core`,
Keccak and FIPS 205/TSW entry points, Shamir/RSS helpers, and protocol guards (`BeltLatchKernel`,
`VerifiedBeltQuorumGuard`, `RssCutReleaseGuard`, `StatefulVelocityGuard`, `MlDsaReleaseGate`).
Verify the [manifest](../aeneas/qsag-verified/extraction-coverage.json)
with `python3 scripts/gen_extraction_coverage.py --check`.

`aeneas/qsag-whir-verified` has no such manifest. Its production linkage is the list of call
sites given above, which can be re-derived with
`rg 'qsag_whir_verified::' crates/qsag-agg/src`.

## Source correspondence and scope

Both `aeneas/qsag-verified` and `aeneas/qsag-whir-verified` are zero-dependency
`#![no_std]` crates with `#![forbid(unsafe_code)]`.

| Package | Surface | Evidence and boundary |
| --- | --- | --- |
| `aeneas/qsag-verified` (differential-parity primitives) | Goldilocks and GoldilocksExt2; Wiedemann Gf16, Gf256, Tower128; Shamir evaluation and Lagrange reconstruction; Keccak-f[1600], SHAKE256, cSHAKE256; FIPS 205 ADRS, WOTS+, F, and TSW | `tests/parity_qsag_core.rs` compares executed cases bit-for-bit with `crates/qsag-core`. `tests/unit_kat.rs` includes NIST FIPS 202 and SP 800-185 known-answer tests. `QsagSpecWeld` proves universal equivalence of extracted Keccak-f[1600] and of the binary towers (GF(256), `Tower128`) against `lean/Qsag`; `SpongeFraming` extends this to the emitted SHAKE256 and cSHAKE256 bytes (see below). |
| `aeneas/qsag-verified` (protocol guards & custody weld) | `EpochLatch` with randomizer binding; `BeltLatchKernel`; `VerifiedBeltQuorumGuard` (`authenticated_belt`); `RssCutReleaseGuard` (`rss_cut_session`); two-of-three `RssShare64` gates | `QsagCustodyWeld` proves `RealSpecBeltWeld` against the custodian masks of `Qsag.JortsBeltLatchAndQuorumSwitching`, and in `AuthenticatedBeltAndRealSpecWeld` and `RealSpecGuardBoundary` that the extracted RSS cut session, `StatefulVelocityGuard`, `MlDsaReleaseGate` and `BeltLatchKernel` forward-simulate `Qsag.mirRssCutMachine`, `Qsag.mirVelocityMachine`, `Qsag.mirMlDsaReleaseMachine` and `Qsag.mirBeltLatchKernelMachine`. Crash-safe `EpochLatch` durability requires the caller to persist its write-ahead log before releasing a grant. |
| `aeneas/qsag-whir-verified` | Canonical Quintic and GL24 decoding, Steiner multiproof counting, row-round and CWYZ fold payload checks, quorum and wire envelopes | The production entry points above use kernels linked from the extracted crate. The Lean coverage gate checks all 86 generated symbols, including internal helpers. |

Goldilocks inversion has an exact modular-exponent specification and canonical output
bound. Beyond the seven-input witness, `RealSpecFieldWeld.lean` proves the universal nonzero
residue law `goldilocks_inverse_mul_eq_one`, the exact zero-residue option behavior
`goldilocks_inv_none_iff_zero`, and `goldilocks_inv_some_mul_eq_one`, using the canonical
Goldilocks field laws. The Keccak zero-state
witness excludes a constant-zero implementation, without excluding every constant
function or establishing cryptographic security.

## Extraction and proof architecture

`aeneas/extract.sh` and `aeneas/extract_whir.sh` invoke Rust checking, Charon MIR
extraction, and Aeneas with `-backend lean -split-files`, then record SHA-256
manifests in `extraction-provenance.json`. `Types.lean` and `Funs.lean` in both
workspaces are machine-generated artifacts; Rust changes require regeneration.

- In `aeneas/lean`, `QsagVerified/Proofs/` holds the verified custody and arithmetic proof modules (`Common`, `Goldilocks`,
  `Gf256`, `TowerBdoz`, `ShamirDkg`, `Epoch`, `Sponge`, `SpongeConformance`,
  `SpongeFraming`, the guard and belt custody modules, `MirWpKit`, `MirRefinementKit`,
  `ElfMirTriangles` and the `RealSpec*Weld` modules), plus the nine `KeccakWitness/` group files.
  They are re-exported through `QsagMirProofs.lean` and welded to `lean/Qsag` in
  `QsagSpecWeld.lean` and `QsagCustodyWeld.lean`. `aeneas/lean/comparator.json` replays 68
  theorems and 21 definitions against `QsagVerifiedChallenge`. All 6/6
  paranoid kernels accepted 5,371 exported declarations across 46 project modules (2,327 declarations, 1,026 theorems, 0 rejected).
  - **`Proofs/MirWpKit.lean`** is the weakest-precondition layer over the Aeneas
    `Result` monad. `Result.wp r P` is total correctness (`r = .ok v` with `P v`);
    `Result.wlp r P Qerr` is fail-closed correctness (`.ok v` with `P v`, or `.fail e` with
    `Qerr e`, never `.div`). Step rules: `wp_ok`, `wp_pure`, `wp_lift`, `wp_fail_elim`,
    `wp_iff_exists_ok`, `wp_of_eq_ok`, `wp_mono`, `wp_let`, `wp_ite`, `wlp_of_wp`. Checked
    arithmetic: `wp_uscalar_add`, `wp_uscalar_sub`, `wp_uscalar_mul` reduce a checked
    `UScalar` operation to its range guard and a pure postcondition. `MirRel1` / `MirRel2`
    (`MirRel1.comp_bind`) relate a pure specification function to a monadic MIR function. The
    tactics `mir_wp` and `mir_sim_step` apply these rules, and `mirCheckedDeltaCheck_wp_spec`
    with `tooth_mirCheckedDeltaCheck_exceeds_cap_fails` is the worked instance. The kit adds no
    statement about any extracted function.
  - **`Proofs/RealSpecKeccakWeld.lean`** proves `keccak_round_refines_qsag`,
    `keccak_f1600_refines_qsag`, `keccak_f1600_array_refines_qsag` and
    `keccak_f1600_result_iff`: the extracted 24-round permutation equals `Qsag.keccakF1600`
    for every state. It also fixes the streaming phase law.
    **`shake256_absorb_after_squeezing_fails`** states that for any sponge with
    `squeezing = true` and any input, `keccak.Shake256Sponge.absorb s data = .fail
    .assertionFailure`: the extracted `absorb` asserts `!self.squeezing`
    (`aeneas/qsag-verified/src/keccak.rs`), as production `Cshake256Xof::absorb` panics, so a
    late absorb is never a successful no-op. `shake256_absorb_ok_iff_absorbing`, despite its name, proves only
    success implies `squeezing = false`; it does not prove success for every arbitrary
    state with that flag. `shake256_finalize_after_squeezing` proves that repeated finalization leaves the
    state unchanged.
  - **`Proofs/SpongeFraming.lean`** closes the byte-level gap that the
    permutation weld leaves open: `shake256_absorb_pad_refines` (any split of the input into
    `absorb` calls, then `finalize`, holds `Qsag.absorbPadded (Qsag.padForRate input 0x1f)`),
    `shake256_32_refines`, `shake256_squeeze_refines` and `cshake256_squeeze_refines` (the
    first squeeze into a destination of any length equals `Qsag.shake256Xof` /
    `Qsag.cshake256Xof` of the concatenated input, for every customization), with the teeth
    `tooth_squeezing_not_absorbed`, `tooth_last_block_suffix_sensitive` and
    `tooth_multiblock_squeeze_permuted_beyond_136`.
  - **`Proofs/RealSpecTowerWeld.lean`** identifies the extracted Wiedemann-tower
    additions and multiplications with the recursive field `Qsag.TowerElem k` of `Qsag.Math.Gf2Pow128` under
    `Qsag.unpackTower`: `gf256_add_refines_qsag`, `gf256_mul_refines_qsag` (`k = 3`),
    `tower128_add_refines_qsag`, `tower128_mul_refines_qsag`, and `tower128_mul_eq_zero_iff`
    (`k = 7`). The wide levels come from a level-generic Karatsuba
    step instantiated at 16, 32, 64 and 128 bits; no level above GF(256) is checked by
    enumeration. See the manifest for the callers of each operation.

  - **`Proofs/ElfMirTriangles.lean`** binds seven MIR/specification/decoded-archive triangles, exported and gated by `QsagCustodyWeld.lean`. Each retains the archive symbol lookup and byte decoder; these are functional refinements under the stated entry conditions, not a compiler-correctness theorem:
    - `elf_mir_goldilocks_add_x86_64`, `elf_mir_goldilocks_sub_x86_64`, `elf_mir_goldilocks_mul_x86_64`: canonical field operands in `rdi/rsi`, `pc = 0`, not halted, and fuel at least 25/31/33; termination, unchanged memory and return value equal to the extracted result.
    - `elf_mir_goldilocks_mul_aarch64`: canonical operands in `x0/x1`, the same entry flags and fuel at least 30, with the corresponding result and memory guarantee.
    - `elf_mir_keccak_f1600_avx2_4x`: all four lanes equal the full 24-round `Qsag.keccakF1600` and extracted permutation after 6,661 modeled steps, with zero YMM state and clean upper-state flag. `keccak4xFullEntry` requires canonical round constants and disjoint state, constant-table, stack-scratch and saved-frame-pointer regions.
    - `elf_mir_gf256_gfni`: one 32-byte block (`rcx = 1`), 35 decoded steps, byte-for-byte agreement with `tower.gf256_mul`, termination and a clean upper-YMM flag, alongside the slice noninterference certificate.
    - `elf_mir_tower128_pclmul`: one product (`rcx = 1`), 50 steps, with the output equal to the initial accumulator plus the extracted `tower128_mul` result through the proved basis isomorphism. This is the `gf2_128_mul_acc_pclmul` symbol, not a complete BDOZ protocol theorem.
- In `aeneas/lean-whir`, the 14 audited modules cover `QsagWhirVerified` (`707` project declarations and `461` theorems, `0` rejected, `0` external model files), connecting all 86 `Funs.lean` symbols to canonical `Qsag` definitions including `Qsag.QuinticGoldilocks`, GL24 digests, Steiner multiproof counting, the public row/CWYZ fold payload verifiers, and the 13 deployed schedules. [Extraction and weld inventory](../aeneas/lean-whir/README.md)
- The WHIR comparator selects 141 challenge theorems and 19 definitions. All 6/6 paranoid kernels accepted its 4,829 exported declarations. [WHIR comparator roster](../aeneas/lean-whir/comparator.json)

Every hand-written Lean file over 80 lines avoids file-wide `@[expose] public section`
and stays within at most 12 `@[expose]` attributes (`scripts/check_lean_policy.py`).

## Trusted computing base and prelude semantics

The semantic chain includes Rust source and MIR generation, Charon, Aeneas, the
hand-written Lean 4.35 prelude, and Lean's kernel (plus the five independent replay
kernels in `lake comparator --paranoid`: `leanchecker-paranoid`, `lean4lean`,
`nanoda_bin`, `con-leche`, and `con-ron`). The functional claims do not verify
LLVM compilation, hardware timing, physical randomness, or storage durability.

The prelude fixes `usize` to 64 bits. Checked arithmetic, shifts, and indexing return
`.fail` when their guards fail. `Array.from_slice` enforces its length invariant.
Arrays carry exact lengths; slices carry machine-size length bounds. Generated loops
use `loopMaxFuel = 2^65`, returning `.div` on exhaustion. Successful loop proofs exhibit
bounded evaluations and transfer them through `loop_ok_of_loopFuel`. Rust domain
errors are values: `.ok (.Err e)` differs from prelude execution failure `.fail e`.

The complete dependency-closure axiom audits (`AuditMirAxioms` and
`AuditWhirMirAxioms`, run with `setExporting false` so private proof lemmas are
included) permit only `propext` and `Quot.sound`. Every declaration has zero
transitive `Classical.choice`, `sorryAx`, custom `axiom`, `Lean.ofReduceBool`,
`Lean.ofReduceNat`, and `Lean.trustCompiler` dependencies.

## Reproducible checks

Run tests and builds on the designated Linux toolchains. From the repository root:

```sh
cargo test --manifest-path aeneas/qsag-verified/Cargo.toml --release
cargo test --manifest-path aeneas/qsag-whir-verified/Cargo.toml --release
python3 scripts/check_lean_policy.py
python3 aeneas/lean/check_audit_coverage.py
python3 scripts/check_extraction_provenance.py
```

Build and audit `aeneas/lean`:

```sh
cd aeneas/lean
LEAN_NUM_THREADS=4 lake build --wfail QsagVerified QsagSpecWeld QsagCustodyWeld AuditMirAxioms QsagMirProofs audit-mir-axioms
.lake/build/bin/audit-mir-axioms
python3 ../../scripts/run_mir_comparator.py
```

Build, audit, and replay `aeneas/lean-whir`:

```sh
cd aeneas/lean-whir
LEAN_NUM_THREADS=4 lake build --wfail QsagWhirVerified AuditWhirMirAxioms audit-whir-mir-axioms
lake build QsagWhirVerifiedChallenge
.lake/build/bin/audit-whir-mir-axioms
COMPARATOR_BWRAP="$PWD/comparator-bwrap.py" lake comparator --paranoid
```

## Export inventory (`QsagMirProofs`)

Targets below are relative to `qsag_verified` unless identified as model components;
see `aeneas/lean/QsagCustodyWeld.lean` for the belt custody weld theorems and
`aeneas/lean-whir/README.md` (`QsagWhirVerified/Proofs.lean`) for the full WHIR MIR
theorem inventory. The extraction manifest identifies callers for each Rust target. Statements apply under the premises of the corresponding Lean declarations.

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

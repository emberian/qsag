module
/-
# Qsag.Spec.Parameters — Normative Cryptographic Parameter Profiles

These records describe the referenced Rust profiles. The balanced eleven-tap PCG profile
tracks the E10 Rust overlay. The live Rust checkout inspected during integration uses three taps.
1. Tweakable-hash hypertree signing (`pq128StatelessProfile`, `corduroyCustody128Profile`,
   `jortsPoseidon2HashProfile`: `crates/qsag-core/src/tsw_baggy.rs`) with `HashSigProfile.WellFormed`
   following `PqHashParams::is_well_formed`, and the NIST FIPS-205 reference shape
   (`slhDsaShake128fProfile`, `HashSigProfile.Fips205Shaped`),
2. FORS-free stateful epoch XMSS/Jorts signing (`pq128StatefulEpochProfile`, `hemJortsXmssProfile`),
3. Quartic-Goldilocks Reed-Solomon IOP succinct aggregation (`hemGoldilocksExt4Profile`),
4. `PiBlindVc` credentials (`pqCredentialProfile`): at most `32` attributes, a 2-of-5 replicated
   TOPRF, `438` ZKBoo issuance repetitions, and `N = 256`, `33`-repetition `GF(p^5)`
   selective-disclosure presentations; FIPS-204 `ML-DSA-44`,
5. Dense dual-LPN PCG (`densePcgV3Profile`: `64` trees, `2^21` columns at depth `15`, `11` balanced
   taps per tree, row weight `704`) and `RLWE-1024` preprocessing, and
6. Separated threshold custody quorum geometry (`CustodyQuorumProfile`).

The `WellFormed` predicates state the parameter equations the Rust validators enforce together
with two-sided bounds on the security label; each comes with rejection theorems for the
ill-formed variants it excludes.
-/

public import Qsag.Spec.Primitives
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spec

set_option autoImplicit false
set_option exponentiation.threshold 512

/-- Normative parameter profile for tweakable-hash hypertree signing (supporting both stateless
    FORS/TSW presets and FORS-free stateful `Jorts` presets with `forsTrees = 0`). Mirrors
    `PqHashParams` (`crates/qsag-core/src/tsw_baggy.rs:608`): `winternitzRadix = w`,
    `wotsChainCount = ell1`, `subtreeHeight = h'`, `hypertreeLayers = d`, `forsTrees = k`,
    `forsTreeHeight = a`. `winternitzLog2` is `log2 w` (Rust derives it as `w.trailing_zeros()`). -/
structure HashSigProfile where
  digestBytes : Nat
  winternitzRadix : Nat
  winternitzLog2 : Nat
  wotsChainCount : Nat
  subtreeHeight : Nat
  hypertreeLayers : Nat
  forsTrees : Nat
  forsTreeHeight : Nat
  maxSigsLog2 : Nat
  statefulBottomLayer : Bool
  deriving DecidableEq, Repr

/-- Security label of a hash-signature profile, derived from the digest width: half of the
    `8 * digestBytes` digest bits, the exponent a generic quantum preimage search leaves an
    `n`-bit hash. It is a derived label: `WellFormed` forces `digestBytes = 32`, so it is the
    constant `128` on every well-formed profile (`HashSigProfile.WellFormed.securityBits_eq`).
    It is not derived from a budget theorem and proves nothing about the scheme. -/
def HashSigProfile.securityBits (p : HashSigProfile) : Nat := 4 * p.digestBytes

/-- Parameter equations of a deployed `HashSigProfile`, following `PqHashParams::is_well_formed`
    (`crates/qsag-core/src/tsw_baggy.rs:630`) extended to the 64-bit `CorduroyPoseidon2` leaf space
    (`crates/qsag-agg/src/sig.rs:36-45`):
    * `w = 2 ^ lg w` with `1 ≤ lg w ≤ 8` (Rust: `2 ≤ w ≤ 256`, power of two);
    * the target-sum WOTS chains carry the whole digest: `ell1 * lg w = 8 * digestBytes = 256`
      (Rust: `digest_bits != 256` is rejected; there are no checksum chains);
    * `0 < h' ≤ 30`, `a ≤ 30`, `0 < d`, total height `d * h' ≤ 64`, and `h' * (d - 1) ≤ 60`
      (`u64` subtree-index shift guard across all `0 ..< d` layers);
    * `0 < maxSigsLog2 ≤ d * h'`: the signature budget never exceeds the number of leaves;
    * stateless profiles have `0 < k`, `0 < a`; stateful profiles have `k = a = 0`.

    The security label is not a field: `HashSigProfile.securityBits` is derived as half the digest
    width. Stateless profiles additionally need at least that many bits of FORS index material
    (`4 * digestBytes ≤ k * a`). These are necessary conditions, not a security proof. -/
@[expose] def HashSigProfile.WellFormed (p : HashSigProfile) : Prop :=
  1 ≤ p.winternitzLog2 ∧ p.winternitzLog2 ≤ 8 ∧
  p.winternitzRadix = 2 ^ p.winternitzLog2 ∧
  p.digestBytes = 32 ∧
  p.wotsChainCount * p.winternitzLog2 = 8 * p.digestBytes ∧
  0 < p.subtreeHeight ∧ p.subtreeHeight ≤ 30 ∧
  p.forsTreeHeight ≤ 30 ∧
  0 < p.hypertreeLayers ∧
  p.hypertreeLayers * p.subtreeHeight ≤ 64 ∧
  p.subtreeHeight * (p.hypertreeLayers - 1) ≤ 60 ∧
  0 < p.maxSigsLog2 ∧
  p.maxSigsLog2 ≤ p.hypertreeLayers * p.subtreeHeight ∧
  ((p.statefulBottomLayer = false ∧ 0 < p.forsTrees ∧ 0 < p.forsTreeHeight ∧
      4 * p.digestBytes ≤ p.forsTrees * p.forsTreeHeight) ∨
   (p.statefulBottomLayer = true ∧ p.forsTrees = 0 ∧ p.forsTreeHeight = 0))

/-- Exact raw signature byte length for a stateless FORS/TSW `HashSigProfile`
    (`crates/qsag-agg/src/sig.rs:88-90`). -/
def HashSigProfile.rawSigBytes (p : HashSigProfile) : Nat :=
  p.digestBytes + p.forsTrees * (1 + p.forsTreeHeight) * p.digestBytes +
    p.hypertreeLayers * (4 + p.wotsChainCount * p.digestBytes + p.subtreeHeight * p.digestBytes)

/-- Shape of a NIST FIPS-205 `SLH-DSA` reference parameter set, which is NOT a deployed
    `PqHashParams` profile: checksum WOTS+ with `lg w = 4` and `len = 2n + 3` chains
    (`len1 = 8n / 4 = 2n`, `len2 = 3`), at least `8n` bits of FORS index material, total height at most `66 = 64 + 2`
    and at least the `2^64` signature budget. -/
def HashSigProfile.Fips205Shaped (p : HashSigProfile) : Prop :=
  p.winternitzLog2 = 4 ∧
  p.winternitzRadix = 2 ^ p.winternitzLog2 ∧
  (p.digestBytes = 16 ∨ p.digestBytes = 24 ∨ p.digestBytes = 32) ∧
  p.wotsChainCount = 2 * p.digestBytes + 3 ∧
  p.statefulBottomLayer = false ∧
  0 < p.forsTrees ∧ 0 < p.forsTreeHeight ∧
  8 * p.digestBytes ≤ p.forsTrees * p.forsTreeHeight ∧
  0 < p.subtreeHeight ∧ 0 < p.hypertreeLayers ∧
  p.maxSigsLog2 = 64 ∧
  p.maxSigsLog2 ≤ p.hypertreeLayers * p.subtreeHeight ∧
  p.hypertreeLayers * p.subtreeHeight ≤ 66

/-- Deployed 128-bit PQ stateless `Baggy-128f` profile (`PqHashParams::BAGGY_TSW_128F`,
    `crates/qsag-core/src/tsw_baggy.rs:749`: 32-byte digest, `w = 4, ell1 = 128`, `d = 16, h' = 2`
    (`h = 32`), `k = 33, a = 6`, `Q_max = 2^16`). -/
@[expose] def pq128StatelessProfile : HashSigProfile where
  digestBytes := 32
  winternitzRadix := 4
  winternitzLog2 := 2
  wotsChainCount := 128
  subtreeHeight := 2
  hypertreeLayers := 16
  forsTrees := 33
  forsTreeHeight := 6
  maxSigsLog2 := 16
  statefulBottomLayer := false

/-- Deployed 128-bit PQ stateless `Corduroy-Custody-128` profile (`PqHashParams::CORDUROY_CUSTODY_128`,
    `crates/qsag-core/src/tsw_baggy.rs:737`: 32-byte digest, `w = 4, ell1 = 128`, `d = 7, h' = 4`
    (`h = 28`), `k = 33, a = 6`, `Q_max = 2^12`). -/
@[expose] def corduroyCustody128Profile : HashSigProfile where
  digestBytes := 32
  winternitzRadix := 4
  winternitzLog2 := 2
  wotsChainCount := 128
  subtreeHeight := 4
  hypertreeLayers := 7
  forsTrees := 33
  forsTreeHeight := 6
  maxSigsLog2 := 12
  statefulBottomLayer := false

/-- Deployed FORS-free stateful `JortsPoseidon2` `HashSigProfile` (`PqHashParams::JORTS_POSEIDON2`,
    `crates/qsag-core/src/tsw_baggy.rs:761`: `w = 4, ell1 = 128`, `d = 1, h' = 16`, `k = a = 0`,
    `Q_max = 2^16`). -/
def jortsPoseidon2HashProfile : HashSigProfile where
  digestBytes := 32
  winternitzRadix := 4
  winternitzLog2 := 2
  wotsChainCount := 128
  subtreeHeight := 16
  hypertreeLayers := 1
  forsTrees := 0
  forsTreeHeight := 0
  maxSigsLog2 := 16
  statefulBottomLayer := true

/-- Deployed stateless `CorduroyPoseidon2` aggregation profile (`AggSigProfile::CorduroyPoseidon2`,
    `crates/qsag-agg/src/sig.rs:33-45, 67-68, 87-91`: 32-byte digest, `w = 4, ell1 = 128`,
    `d = 16, h' = 4` (`h = 64`, `h' * (d - 1) = 60`), `k = 32, a = 8`, `Q_max = 2^20`,
    `76,896`-byte raw signature). -/
def corduroyPoseidon2Profile : HashSigProfile where
  digestBytes := 32
  winternitzRadix := 4
  winternitzLog2 := 2
  wotsChainCount := 128
  subtreeHeight := 4
  hypertreeLayers := 16
  forsTrees := 32
  forsTreeHeight := 8
  maxSigsLog2 := 20
  statefulBottomLayer := false

/-- Normative parameter profile for `Baggy` hypertree-over-`PORS+FP` signing
    (`BaggyParams`, `crates/qsag-core/src/baggy.rs:131-213` and `pors_fp.rs:38-87`). -/
structure BaggyPorsFpProfile where
  digestBytes : Nat
  winternitzRadix : Nat
  winternitzLog2 : Nat
  wotsChainCount : Nat
  wotsZeroDigits : Nat
  wotsTargetSum : Nat
  subtreeHeight : Nat
  hypertreeLayers : Nat
  maxGrind : Nat
  porsTreeHeight : Nat
  porsReveal : Nat
  porsMaxAuthNodes : Nat
  maxSigBytes : Nat
  deriving DecidableEq, Repr

/-- Worst-case byte length of a `PORS+FP` opening (`32 * reveal + 2 + 32 * max_auth_nodes`,
    `crates/qsag-core/src/pors_fp.rs:85-87`). -/
def BaggyPorsFpProfile.porsOpeningBytesMax (p : BaggyPorsFpProfile) : Nat :=
  p.digestBytes * p.porsReveal + 2 + p.digestBytes * p.porsMaxAuthNodes

/-- Worst-case byte length of a serialized `BaggySig` (`36 + pors_bytes + d * (4 + 32*chains + 32*h')`,
    `crates/qsag-core/src/baggy.rs:189-213`). -/
def BaggyPorsFpProfile.sigBytesMax (p : BaggyPorsFpProfile) : Nat :=
  36 + p.porsOpeningBytesMax +
    p.hypertreeLayers * (4 + p.digestBytes * p.wotsChainCount + p.digestBytes * p.subtreeHeight)

/-- Parameter equations of `BaggyParams::is_well_formed` (`baggy.rs:166-185`) and
    `PorsFpParams::is_well_formed` (`pors_fp.rs:64-73`). -/
def BaggyPorsFpProfile.WellFormed (p : BaggyPorsFpProfile) : Prop :=
  p.digestBytes = 32 ∧
  p.winternitzRadix = 4 ∧ p.winternitzLog2 = 2 ∧
  p.wotsChainCount = 128 ∧ p.wotsZeroDigits = 0 ∧ p.wotsTargetSum = 192 ∧
  1 ≤ p.subtreeHeight ∧ p.subtreeHeight ≤ 8 ∧
  1 ≤ p.hypertreeLayers ∧ p.hypertreeLayers ≤ 62 ∧
  p.hypertreeLayers * p.subtreeHeight ≤ 62 ∧
  0 < p.maxGrind ∧ p.maxGrind < 2 ^ 32 ∧
  1 ≤ p.porsTreeHeight ∧ p.porsTreeHeight ≤ 20 ∧
  1 ≤ p.porsReveal ∧ p.porsReveal ≤ 1024 ∧
  p.porsReveal ≤ (2 ^ p.porsTreeHeight) / 2 ∧
  1 ≤ p.porsMaxAuthNodes ∧ p.porsMaxAuthNodes ≤ p.porsReveal * p.porsTreeHeight ∧
  p.maxSigBytes = p.sigBytesMax

/-- Deployed `BaggyParams::SHA3_128F` profile (`crates/qsag-core/src/baggy.rs:145-151` &
    `pors_fp.rs:51-55`: `d = 16, h' = 2` (`h = 32`), `WotsCParams::V128`, `PORS+FP`
    `tree_height = 11, reveal = 28, max_auth_nodes = 128`, max signature `71,654` bytes). -/
def baggySha3_128fProfile : BaggyPorsFpProfile where
  digestBytes := 32
  winternitzRadix := 4
  winternitzLog2 := 2
  wotsChainCount := 128
  wotsZeroDigits := 0
  wotsTargetSum := 192
  subtreeHeight := 2
  hypertreeLayers := 16
  maxGrind := 2 ^ 26
  porsTreeHeight := 11
  porsReveal := 28
  porsMaxAuthNodes := 128
  maxSigBytes := 71654

theorem baggySha3_128fProfile_maxSigBytes : baggySha3_128fProfile.maxSigBytes = 71654 := by
  unfold baggySha3_128fProfile
  rfl

/-- NIST FIPS-205 `SLH-DSA-SHAKE-128f` reference profile (`n = 16`-byte digest, `w = 16`,
    `len = 35 = 32 + 3`, `d = 22, h' = 3` (`h = 66`), `k = 33, a = 6`, `2^64` signatures). Not a
    deployed `PqHashParams` preset; it satisfies `Fips205Shaped`, not `WellFormed`. -/
def slhDsaShake128fProfile : HashSigProfile where
  digestBytes := 16
  winternitzRadix := 16
  winternitzLog2 := 4
  wotsChainCount := 35
  subtreeHeight := 3
  hypertreeLayers := 22
  forsTrees := 33
  forsTreeHeight := 6
  maxSigsLog2 := 64
  statefulBottomLayer := false

theorem pq128StatelessProfile_wellFormed :
    pq128StatelessProfile.WellFormed ∧
    corduroyCustody128Profile.WellFormed ∧
    corduroyPoseidon2Profile.WellFormed ∧
    jortsPoseidon2HashProfile.WellFormed ∧
    slhDsaShake128fProfile.Fips205Shaped := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold HashSigProfile.WellFormed pq128StatelessProfile
    decide
  · unfold HashSigProfile.WellFormed corduroyCustody128Profile
    decide
  · unfold HashSigProfile.WellFormed corduroyPoseidon2Profile
    decide
  · unfold HashSigProfile.WellFormed jortsPoseidon2HashProfile
    decide
  · unfold HashSigProfile.Fips205Shaped slhDsaShake128fProfile
    decide

theorem corduroyPoseidon2Profile_params :
    corduroyPoseidon2Profile.WellFormed ∧
    corduroyPoseidon2Profile.hypertreeLayers = 16 ∧
    corduroyPoseidon2Profile.subtreeHeight = 4 ∧
    corduroyPoseidon2Profile.forsTrees = 32 ∧
    corduroyPoseidon2Profile.forsTreeHeight = 8 ∧
    corduroyPoseidon2Profile.maxSigsLog2 = 20 ∧
    corduroyPoseidon2Profile.rawSigBytes = 76896 := by
  unfold HashSigProfile.WellFormed HashSigProfile.rawSigBytes corduroyPoseidon2Profile
  decide

theorem baggySha3_128fProfile_wellFormed :
    baggySha3_128fProfile.WellFormed ∧
    baggySha3_128fProfile.porsOpeningBytesMax = 4994 ∧
    baggySha3_128fProfile.sigBytesMax = 71654 ∧
    baggySha3_128fProfile.hypertreeLayers = 16 ∧
    baggySha3_128fProfile.subtreeHeight = 2 ∧
    baggySha3_128fProfile.porsTreeHeight = 11 ∧
    baggySha3_128fProfile.porsReveal = 28 ∧
    baggySha3_128fProfile.porsMaxAuthNodes = 128 := by
  unfold BaggyPorsFpProfile.WellFormed BaggyPorsFpProfile.sigBytesMax
    BaggyPorsFpProfile.porsOpeningBytesMax baggySha3_128fProfile
  decide

/-- Tooth: `BaggyPorsFpProfile.WellFormed` rejects multiproof caps above `reveal * treeHeight`,
    oversized reveal counts above half the leaves, and mismatched `maxSigBytes`. -/
theorem BaggyPorsFpProfile.wellFormed_rejects_bad_pors_or_bytes :
    ¬ (({ baggySha3_128fProfile with porsMaxAuthNodes := 309 } : BaggyPorsFpProfile).WellFormed ∨
       ({ baggySha3_128fProfile with porsReveal := 1025 } : BaggyPorsFpProfile).WellFormed ∨
       ({ baggySha3_128fProfile with maxSigBytes := 71655 } : BaggyPorsFpProfile).WellFormed) := by
  unfold BaggyPorsFpProfile.WellFormed BaggyPorsFpProfile.sigBytesMax
    BaggyPorsFpProfile.porsOpeningBytesMax baggySha3_128fProfile
  decide

/-- The derived label of a well-formed profile is `128`: a consequence of the 256-bit digest. -/
theorem HashSigProfile.WellFormed.securityBits_eq {p : HashSigProfile} (h : p.WellFormed) :
    p.securityBits = 128 := by
  obtain ⟨_, _, _, hDig, _⟩ := h
  unfold HashSigProfile.securityBits
  rw [hDig]

/-- A well-formed profile has exactly as many WOTS chains as the 256-bit digest has base-`w`
    digits (`ell1 * lg w = 256`, `tsw_baggy.rs:640`). -/
theorem HashSigProfile.WellFormed.wotsChainCount_mul_log2 {p : HashSigProfile} (h : p.WellFormed) :
    p.wotsChainCount * p.winternitzLog2 = 256 ∧ p.winternitzRadix = 2 ^ p.winternitzLog2 := by
  obtain ⟨_, _, hRad, hDig, hChain, _⟩ := h
  rw [hDig] at hChain
  exact ⟨hChain, hRad⟩

/-- The signature budget of a well-formed profile fits in its `2 ^ (d * h')` hypertree leaves, of
    which there are at most `2 ^ 64`, with `h' * (d - 1) ≤ 60` subtree-index bits. -/
theorem HashSigProfile.WellFormed.maxSigs_le_leaves {p : HashSigProfile} (h : p.WellFormed) :
    2 ^ p.maxSigsLog2 ≤ 2 ^ (p.hypertreeLayers * p.subtreeHeight) ∧
    2 ^ (p.hypertreeLayers * p.subtreeHeight) ≤ 2 ^ 64 ∧
    p.subtreeHeight * (p.hypertreeLayers - 1) ≤ 60 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hTot, hShift, _, hSigs, _⟩ := h
  exact ⟨Nat.pow_le_pow_right (by decide) hSigs, Nat.pow_le_pow_right (by decide) hTot, hShift⟩

/-- Tooth (audit #28): a 16-byte digest, whose derived label would be `64`, is rejected even with
    the matching `64` chains. -/
theorem HashSigProfile.wellFormed_rejects_short_digest :
    ¬ ({ pq128StatelessProfile with digestBytes := 16, wotsChainCount := 64 } :
        HashSigProfile).WellFormed := by
  unfold HashSigProfile.WellFormed pq128StatelessProfile
  decide

/-- Tooth (audit #28): a positive WOTS chain count that does not cover the digest is rejected. -/
theorem HashSigProfile.wellFormed_rejects_wrong_wotsChainCount :
    ¬ ({ pq128StatelessProfile with wotsChainCount := 35 } : HashSigProfile).WellFormed := by
  unfold HashSigProfile.WellFormed pq128StatelessProfile
  decide

/-- Tooth (audit #28): a signature budget above the number of hypertree leaves is rejected. -/
theorem HashSigProfile.wellFormed_rejects_maxSigs_above_leaves :
    ¬ ({ pq128StatelessProfile with maxSigsLog2 := 33 } : HashSigProfile).WellFormed := by
  unfold HashSigProfile.WellFormed pq128StatelessProfile
  decide

/-- The FIPS-205 reference shape (16-byte digest, checksum chains, `h = 66`) is not a deployed
    `PqHashParams` profile. -/
theorem slhDsaShake128fProfile_not_wellFormed : ¬ slhDsaShake128fProfile.WellFormed := by
  unfold HashSigProfile.WellFormed slhDsaShake128fProfile
  decide

/-- Normative parameter profile for FORS-free stateful epoch XMSS/Jorts signing. -/
structure StatefulJortsProfile where
  digestBytes : Nat
  winternitzRadix : Nat
  winternitzLog2 : Nat
  wotsChainCount : Nat
  treeHeight : Nat
  maxEpochLeavesLog2 : Nat
  deriving DecidableEq, Repr

/-- Security label derived from the digest width (half of `8 * digestBytes`): a derived label,
    constant `128` under `WellFormed`; not derived from a budget theorem. -/
def StatefulJortsProfile.securityBits (p : StatefulJortsProfile) : Nat := 4 * p.digestBytes

/-- Parameter equations of a FORS-free `StatefulJortsProfile` (the stateful, single-layer case of
    `PqHashParams::is_well_formed`, `crates/qsag-core/src/tsw_baggy.rs:630`): `w = 2 ^ lg w`,
    `1 ≤ lg w ≤ 8`, `ell1 * lg w = 8 * digestBytes = 256`, `0 < h ≤ 30`, one epoch leaf per
    signature (`maxEpochLeavesLog2 = h`). The label `StatefulJortsProfile.securityBits` is derived. -/
@[expose] def StatefulJortsProfile.WellFormed (p : StatefulJortsProfile) : Prop :=
  1 ≤ p.winternitzLog2 ∧ p.winternitzLog2 ≤ 8 ∧
  p.winternitzRadix = 2 ^ p.winternitzLog2 ∧
  p.digestBytes = 32 ∧
  p.wotsChainCount * p.winternitzLog2 = 8 * p.digestBytes ∧
  0 < p.treeHeight ∧ p.treeHeight ≤ 30 ∧
  p.maxEpochLeavesLog2 = p.treeHeight

/-- Deployed stateful `JortsPoseidon2` profile (`PqHashParams::JORTS_POSEIDON2`,
    `crates/qsag-core/src/tsw_baggy.rs:761`: FORS-free, `w = 4, ell1 = 128`, `h = 16`, `2^16` leaves). -/
@[expose] def pq128StatefulEpochProfile : StatefulJortsProfile where
  digestBytes := 32
  winternitzRadix := 4
  winternitzLog2 := 2
  wotsChainCount := 128
  treeHeight := 16
  maxEpochLeavesLog2 := 16

/-- Committee shard `HEM_JORTS` XMSS profile (`HEM_JORTS_XMSS_HEIGHT = 6` in `poseidon2_mpc.rs`:
    FORS-free, `w = 4, ell1 = 128`, `h = 6`, `64` leaves). -/
def hemJortsXmssProfile : StatefulJortsProfile where
  digestBytes := 32
  winternitzRadix := 4
  winternitzLog2 := 2
  wotsChainCount := 128
  treeHeight := 6
  maxEpochLeavesLog2 := 6

theorem pq128StatefulEpochProfile_wellFormed :
    pq128StatefulEpochProfile.WellFormed ∧
    hemJortsXmssProfile.WellFormed := by
  unfold StatefulJortsProfile.WellFormed pq128StatefulEpochProfile hemJortsXmssProfile
  decide

/-- A well-formed stateful profile has derived label `128` and `256 / lg w` chains. -/
theorem StatefulJortsProfile.WellFormed.securityBits_eq {p : StatefulJortsProfile}
    (h : p.WellFormed) :
    p.securityBits = 128 ∧ p.wotsChainCount * p.winternitzLog2 = 256 := by
  obtain ⟨_, _, _, hDig, hChain, _⟩ := h
  rw [hDig] at hChain
  refine ⟨?_, hChain⟩
  unfold StatefulJortsProfile.securityBits
  rw [hDig]

/-- Tooth (audit #28): neither a 16-byte digest nor a non-covering chain count is accepted. -/
theorem StatefulJortsProfile.wellFormed_rejects_oversized_or_wrong_chains :
    ¬ (({ pq128StatefulEpochProfile with digestBytes := 16 } : StatefulJortsProfile).WellFormed ∨
       ({ pq128StatefulEpochProfile with wotsChainCount := 64 } : StatefulJortsProfile).WellFormed) := by
  unfold StatefulJortsProfile.WellFormed pq128StatefulEpochProfile
  decide

/-- The two encodings of the deployed `JortsPoseidon2` preset agree field by field. -/
theorem jortsPoseidon2HashProfile_eq_statefulEpochProfile :
    jortsPoseidon2HashProfile.securityBits = pq128StatefulEpochProfile.securityBits ∧
    jortsPoseidon2HashProfile.digestBytes = pq128StatefulEpochProfile.digestBytes ∧
    jortsPoseidon2HashProfile.winternitzRadix = pq128StatefulEpochProfile.winternitzRadix ∧
    jortsPoseidon2HashProfile.wotsChainCount = pq128StatefulEpochProfile.wotsChainCount ∧
    jortsPoseidon2HashProfile.hypertreeLayers * jortsPoseidon2HashProfile.subtreeHeight =
      pq128StatefulEpochProfile.treeHeight ∧
    jortsPoseidon2HashProfile.maxSigsLog2 = pq128StatefulEpochProfile.maxEpochLeavesLog2 := by
  unfold HashSigProfile.securityBits StatefulJortsProfile.securityBits
    jortsPoseidon2HashProfile pq128StatefulEpochProfile
  decide

/-- Normative parameter profile for quartic-Goldilocks Reed-Solomon IOP succinct aggregation (`HEM`/`WHIR`),
    matching `Aggregation.productionAggParams` and `crates/qsag-agg/src/pcs.rs`. -/
structure AggregationProfile where
  basePrime : Nat
  extDegree : Nat
  maxPcsVars : Nat
  earlyStopVars : Nat
  logTraceCols : Nat
  rowSumcheckDegree : Nat
  stageBlowups : List Nat
  johnsonQromQueries : List Nat
  johnsonClassicalQueries : List Nat
  cdhzQromQueries : List Nat
  cdhzZeroPowQueries : List Nat := [216, 109, 74, 56]
  grindingBits : Nat
  maxMergeDepth : Nat
  maxBatchPolys : Nat := 16
  deriving DecidableEq, Repr

/-- Production `GoldilocksExt4` (`p = 2^64 - 2^32 + 1`, degree `4`) 4-stage `WHIR`/`HEM` profile:
    `maxPcsVars = 28` (`pcs.rs:86`), `maxBatchPolys = 16` (`pcs.rs:93`), blowups `B = [4, 16, 64, 256]`,
    `[BCIKS20]` Johnson QROM-128 queries `q = [258, 130, 88, 66]`, classical-128 queries
    `[129, 65, 44, 33]`, `[CDHZ25]` 16-bit PoW QROM queries `[202, 102, 70, 52]` (`tags 5, 7`), and
    `[CDHZ25]` zero-PoW QROM queries `[216, 109, 74, 56]` (`tags 6, 8`, `pcs.rs:289-290`). -/
@[expose] def hemGoldilocksExt4Profile : AggregationProfile where
  basePrime := 18446744069414584321
  extDegree := 4
  maxPcsVars := 28
  earlyStopVars := 8
  logTraceCols := 8
  rowSumcheckDegree := 8
  stageBlowups := [4, 16, 64, 256]
  johnsonQromQueries := [258, 130, 88, 66]
  johnsonClassicalQueries := [129, 65, 44, 33]
  cdhzQromQueries := [202, 102, 70, 52]
  cdhzZeroPowQueries := [216, 109, 74, 56]
  grindingBits := 16
  maxMergeDepth := 16
  maxBatchPolys := 16

/-- Parameter equations of an `AggregationProfile` (`crates/qsag-agg/src/pcs.rs`):
    * the field is the degree-`4` extension of Goldilocks, of at least `255` bits;
    * `earlyStopVars ≤ maxPcsVars ≤ 28`, `0 < maxBatchPolys ≤ 16`, and the PoW of the default
      regime is `16` bits (`pcs.rs:86`, `:93`, `:234-244`);
    * the stage blowups start at `4` and quadruple, and there is one query count per stage across
      all four schedules (`johnsonClassical`, `johnsonQrom`, `cdhzQrom`, `cdhzZeroPow`);
    * per stage with blowup `B`, the classical Johnson count is `⌈256 / log₂ B⌉ + 1` and the QROM
      Johnson count is `⌈512 / log₂ B⌉ + 2` (`pcs.rs:282-285`);
    * the `[CDHZ25]` 16-bit PoW (`[202, 102, 70, 52]`) and zero-PoW (`[216, 109, 74, 56]`) tables
      satisfy `cdhzQrom < cdhzZeroPow < johnsonQrom` at every stage (`pcs.rs:286-290`). -/
def AggregationProfile.WellFormed (p : AggregationProfile) : Prop :=
  p.basePrime = 2 ^ 64 - 2 ^ 32 + 1 ∧ p.extDegree = 4 ∧
  2 ^ 255 ≤ p.basePrime ^ p.extDegree ∧
  p.earlyStopVars ≤ p.maxPcsVars ∧ p.maxPcsVars ≤ 28 ∧
  0 < p.maxBatchPolys ∧ p.maxBatchPolys ≤ 16 ∧
  p.grindingBits = 16 ∧
  p.stageBlowups.head? = some 4 ∧
  (p.stageBlowups.zip p.stageBlowups.tail).all (fun x => decide (x.2 = 4 * x.1)) = true ∧
  p.johnsonClassicalQueries.length = p.stageBlowups.length ∧
  p.johnsonQromQueries.length = p.stageBlowups.length ∧
  p.cdhzQromQueries.length = p.stageBlowups.length ∧
  p.cdhzZeroPowQueries.length = p.stageBlowups.length ∧
  (p.stageBlowups.zip p.johnsonClassicalQueries).all (fun x =>
    decide (2 ≤ x.2) && decide (2 ^ 256 ≤ x.1 ^ (x.2 - 1)) &&
      decide (x.1 ^ (x.2 - 2) < 2 ^ 256)) = true ∧
  (p.stageBlowups.zip p.johnsonQromQueries).all (fun x =>
    decide (3 ≤ x.2) && decide (2 ^ 512 ≤ x.1 ^ (x.2 - 2)) &&
      decide (x.1 ^ (x.2 - 3) < 2 ^ 512)) = true ∧
  (p.cdhzQromQueries.zip p.cdhzZeroPowQueries).all (fun x => decide (x.1 < x.2)) = true ∧
  (p.cdhzZeroPowQueries.zip p.johnsonQromQueries).all (fun x => decide (x.1 < x.2)) = true

theorem hemGoldilocksExt4Profile_wellFormed : hemGoldilocksExt4Profile.WellFormed := by
  simp [AggregationProfile.WellFormed, hemGoldilocksExt4Profile]

/-- A well-formed aggregation profile has one query count of each kind per stage, and at least
    one stage. -/
theorem AggregationProfile.WellFormed.query_lists_aligned {p : AggregationProfile}
    (h : p.WellFormed) :
    p.johnsonClassicalQueries.length = p.stageBlowups.length ∧
    p.johnsonQromQueries.length = p.stageBlowups.length ∧
    p.cdhzQromQueries.length = p.stageBlowups.length ∧
    p.cdhzZeroPowQueries.length = p.stageBlowups.length ∧
    p.stageBlowups.head? = some 4 := by
  obtain ⟨_, _, _, _, _, _, _, _, hHead, _, hC, hQ, hZ, hZP, _⟩ := h
  exact ⟨hC, hQ, hZ, hZP, hHead⟩

/-- Tooth: a stage with one query fewer than `⌈512 / log₂ B⌉ + 2`, a dropped stage count, a zero
    batch cap, or a PoW other than `16` bits is rejected. -/
theorem AggregationProfile.wellFormed_rejects_short_queries :
    ¬ (({ hemGoldilocksExt4Profile with johnsonQromQueries := [257, 130, 88, 66] } :
          AggregationProfile).WellFormed ∨
       ({ hemGoldilocksExt4Profile with johnsonClassicalQueries := [129, 65, 44] } :
          AggregationProfile).WellFormed ∨
       ({ hemGoldilocksExt4Profile with cdhzZeroPowQueries := [202, 109, 74, 56] } :
          AggregationProfile).WellFormed ∨
       ({ hemGoldilocksExt4Profile with maxBatchPolys := 0 } :
          AggregationProfile).WellFormed ∨
       ({ hemGoldilocksExt4Profile with grindingBits := 0 } : AggregationProfile).WellFormed) := by
  simp [AggregationProfile.WellFormed, hemGoldilocksExt4Profile]

theorem hemGoldilocksExt4Profile_basePrime_eq :
    hemGoldilocksExt4Profile.basePrime = 2 ^ 64 - 2 ^ 32 + 1 ∧
    hemGoldilocksExt4Profile.extDegree = 4 ∧
    hemGoldilocksExt4Profile.stageBlowups = [4, 16, 64, 256] ∧
    hemGoldilocksExt4Profile.johnsonQromQueries = [258, 130, 88, 66] ∧
    hemGoldilocksExt4Profile.cdhzQromQueries = [202, 102, 70, 52] := by
  unfold hemGoldilocksExt4Profile
  decide

theorem hemGoldilocksExt4Profile_highCap_and_zeroPow_eq :
    hemGoldilocksExt4Profile.maxPcsVars = 28 ∧
    hemGoldilocksExt4Profile.maxBatchPolys = 16 ∧
    hemGoldilocksExt4Profile.cdhzZeroPowQueries = [216, 109, 74, 56] := by
  unfold hemGoldilocksExt4Profile
  decide

/-- Normative parameter profile for `PiBlindVc` credentials (`crates/qsag-cred/src/blind_vc.rs`),
    the replicated threshold OPRF (`crates/qsag-cred/src/voprf.rs`), and `ThresholdMlDsa`
    (`MlDsa44Parameters`). Issuance and presentation are different proof systems with separate
    fields: issuance commitments use 3-party Goldilocks ZKBoo (`issuance*`), selective-disclosure
    membership presentations use the `N = 256` seed-tree MPC-in-the-head check over `GF(p^5)`
    (`sd*`). -/
structure CredentialProfile where
  maxAttrs : Nat
  accumulatorDepth : Nat
  spongeRate : Nat
  spongeCapacity : Nat
  toprfServers : Nat
  toprfThreshold : Nat
  toprfMaxCorrupt : Nat
  toprfOnlineServers : Nat
  toprfMaxBatch : Nat
  toprfCounterWindow : Nat
  issuanceParties : Nat
  issuanceRepsClassical : Nat
  issuanceRepsQuantum : Nat
  sdLimboParties : Nat
  sdGgmDepth : Nat
  sdExtDegree : Nat
  sdRepsClassical : Nat
  sdRepsQuantum : Nat
  mlDsaModulus : Nat
  mlDsaChallengeWeight : Nat
  mlDsaEta : Nat
  mlDsaGamma1 : Nat
  mlDsaBeta : Nat
  mlDsaSacrificeExtDegree : Nat
  deriving DecidableEq, Repr

/-- Parameter equations of a `CredentialProfile`:
    * credentials have between `1` and `maxAttrs` attributes, so `0 < maxAttrs`
      (`blind_vc.rs:179`: `(1..=MAX_VC_ATTRS).contains(&attrs.len())`), and `0 < accumulatorDepth`;
    * the sponge capacity holds at least `256` bits of `63`-bit-or-wider Goldilocks limbs;
    * TOPRF committee (`voprf.rs:4`–`17`): `maxCorrupt < threshold ≤ online ≤ servers`, and each
      cross term is held by the `servers - 2` parties other than its two component holders, of
      which a strict majority is honest (`2 * maxCorrupt < servers - 2`); `0 < maxBatch`;
    * issuance ZKBoo: the quantum repetition count is twice the classical one, and the classical
      count `r` makes the `(2/3)^r` challenge-guessing probability at most `2^-128`
      (`2^128 * 2^r ≤ 3^r`);
    * presentation: `sdLimboParties = 2 ^ sdGgmDepth`, and guessing the hidden party in every
      repetition has probability at most `2^-128` (classical) and `2^-256` (quantum count), with
      a check field of more than `256` bits;
    * `ML-DSA`: `q = 2^23 - 2^13 + 1`, `β = τ * η`, `β < γ₁`.
    These are the arithmetic preconditions of the cited soundness arguments, not those arguments. -/
@[expose] def CredentialProfile.WellFormed (p : CredentialProfile) : Prop :=
  0 < p.maxAttrs ∧ 0 < p.accumulatorDepth ∧
  256 ≤ 63 * p.spongeCapacity ∧
  p.toprfMaxCorrupt < p.toprfThreshold ∧
  p.toprfThreshold ≤ p.toprfOnlineServers ∧
  p.toprfOnlineServers ≤ p.toprfServers ∧
  2 * p.toprfMaxCorrupt + 2 < p.toprfServers ∧
  0 < p.toprfMaxBatch ∧
  p.issuanceParties = 3 ∧
  p.issuanceRepsQuantum = 2 * p.issuanceRepsClassical ∧
  2 ^ 128 * 2 ^ p.issuanceRepsClassical ≤ 3 ^ p.issuanceRepsClassical ∧
  p.sdLimboParties = 2 ^ p.sdGgmDepth ∧
  128 ≤ p.sdRepsClassical * p.sdGgmDepth ∧
  256 ≤ p.sdRepsQuantum * p.sdGgmDepth ∧
  256 ≤ 63 * p.sdExtDegree ∧
  p.mlDsaModulus = 2 ^ 23 - 2 ^ 13 + 1 ∧
  p.mlDsaBeta = p.mlDsaChallengeWeight * p.mlDsaEta ∧
  p.mlDsaBeta < p.mlDsaGamma1

/-- Production credential profile.
    * `maxAttrs = 32`: `MAX_VC_ATTRS`, `crates/qsag-cred/src/blind_vc.rs:42`;
    * `accumulatorDepth = 20`: `VC_ACCUMULATOR_DEPTH`, `blind_vc.rs:44`;
    * rate-6 / capacity-6 Poseidon2 sponge: `blind_vc.rs:10`–`11`;
    * `toprfServers = 5`: `SERVERS`, `crates/qsag-cred/src/voprf.rs:70`; threshold `t = 2`, at most
      one statically corrupt server, four servers online: `voprf.rs:4`–`5`; `MAX_BATCH = 64`,
      `voprf.rs:71`; `MAX_COUNTER_WINDOW = 64`, `voprf.rs:76`;
    * issuance: 3-party ZKBoo, `219` classical / `438` quantum repetitions
      (`ZkSoundnessProfile::repetitions`, `blind_vc.rs:65`–`66`; `VC_ZKBOO_REPS = 438`, `blind_vc.rs:46`);
    * selective-disclosure presentation: `VC_SD_LIMBO_PARTIES = 256` (`blind_vc.rs:57`),
      `VC_SD_GGM_DEPTH = 8` (`blind_vc.rs:59`), `17` classical / `33` quantum repetitions
      (`ZkSoundnessProfile::sd_repetitions`, `blind_vc.rs:74`–`75`) over
      `GF(p^5) = GF(p)[T]/(T^5 - 3)` (`blind_vc.rs:14`);
    * `ML-DSA-44`: `q = 8380417`, `τ = 39`, `η = 2`, `γ₁ = 2^17`, `β = 78`; `𝔽_{q^6}` sacrifice. -/
@[expose] def pqCredentialProfile : CredentialProfile where
  maxAttrs := 32
  accumulatorDepth := 20
  spongeRate := 6
  spongeCapacity := 6
  toprfServers := 5
  toprfThreshold := 2
  toprfMaxCorrupt := 1
  toprfOnlineServers := 4
  toprfMaxBatch := 64
  toprfCounterWindow := 64
  issuanceParties := 3
  issuanceRepsClassical := 219
  issuanceRepsQuantum := 438
  sdLimboParties := 256
  sdGgmDepth := 8
  sdExtDegree := 5
  sdRepsClassical := 17
  sdRepsQuantum := 33
  mlDsaModulus := 8380417
  mlDsaChallengeWeight := 39
  mlDsaEta := 2
  mlDsaGamma1 := 131072
  mlDsaBeta := 78
  mlDsaSacrificeExtDegree := 6

/-- Normative parameter profile for the dense dual-LPN PCG (`crates/qsag-core/src/pcg_dense.rs`)
    and the `RLWE-1024` base-OT preprocessing (`crates/qsag-core/src/preprocessing.rs`). -/
structure DensePcgProfile where
  defaultTreeDepth : Nat
  leavesPerTree : Nat
  treesPerBundle : Nat
  bundleAmbientDim : Nat
  tapsPerTree : Nat
  lpnRowWeight : Nat
  numPackedWords : Nat
  numBoolTriples : Nat
  numFullFieldCompanions : Nat
  spcotCheckReps : Nat
  maxSeedWireBytes : Nat
  rlweRingDim : Nat
  rlweModulus : Nat
  rlweZkpokReps : Nat
  rlweChallengeBits : Nat
  deriving DecidableEq, Repr

/-- Canonical wire length in bytes of a 2-party (one-peer) seed at the profile's tree depth:
    `max_wire_seed_bytes(2, depth)` (`crates/qsag-core/src/pcg_dense.rs:84`), i.e. a `64`-byte
    header plus one peer record `2 + 32 + 2t + 32·d·t + 16t + 32 + 16·reps + 32`. -/
@[expose] def DensePcgProfile.twoPartySeedWireBytes (p : DensePcgProfile) : Nat :=
  64 + (2 + 32 + 2 * p.treesPerBundle + 32 * p.defaultTreeDepth * p.treesPerBundle +
    16 * p.treesPerBundle + 32 + 16 * p.spcotCheckReps + 32)

/-- Parameter equations of a `DensePcgProfile`: production depth `14` or `15`
    (`PcgTreeDepth`, `pcg_dense.rs:130`), `leavesPerTree = 2 ^ depth`, ambient dimension
    `trees * leaves`, row weight `trees * taps`, `64` Boolean triples per packed word
    (`pcg_dense.rs:68`), the exact 2-party wire length within the advertised bound, an
    NTT-friendly RLWE modulus (`q ≡ 1 mod 2n`), and at least `256` joint challenge bits in the
    RLWE proof of knowledge. -/
@[expose] def DensePcgProfile.WellFormed (p : DensePcgProfile) : Prop :=
  (p.defaultTreeDepth = 14 ∨ p.defaultTreeDepth = 15) ∧
  p.leavesPerTree = 2 ^ p.defaultTreeDepth ∧
  p.bundleAmbientDim = p.treesPerBundle * p.leavesPerTree ∧
  p.lpnRowWeight = p.treesPerBundle * p.tapsPerTree ∧
  p.numBoolTriples = p.numPackedWords * 64 ∧
  0 < p.spcotCheckReps ∧
  p.twoPartySeedWireBytes ≤ p.maxSeedWireBytes ∧
  p.rlweModulus % (2 * p.rlweRingDim) = 1 ∧
  256 ≤ p.rlweZkpokReps * p.rlweChallengeBits

/-- Production dense-PCG profile (`crates/qsag-core/src/pcg_dense.rs`):
    * `treesPerBundle = 64`: `DENSE_PCG_NUM_TREES`, `pcg_dense.rs:59`;
    * `tapsPerTree = 11`: `DENSE_PCG_TAPS_PER_TREE`, `pcg_dense.rs:62`; row weight `64 · 11 = 704`;
    * depth `15`, `2^15 = 32768` leaves per tree, `64 · 2^15 = 2^21 = 2097152` columns:
      `PcgTreeDepth::Depth15`, `pcg_dense.rs:137`–`138`;
    * `numPackedWords = 1024`: `DENSE_PCG_NUM_WORDS`, `pcg_dense.rs:65`;
    * `numBoolTriples = 65536`: `DENSE_PCG_NUM_BOOL_TRIPLES`, `pcg_dense.rs:68`;
    * `numFullFieldCompanions = 64`: `DENSE_PCG_NUM_VOLE128`, `pcg_dense.rs:71`;
    * `spcotCheckReps = 2`: `SPCOT_CHECK_REPS`, `pcg_dense.rs:703`;
    * `maxSeedWireBytes = 36864`: `DENSE_PCG_MAX_SEED_BYTES`, `pcg_dense.rs:75`;
    * `RLWE_N = 1024`, `RLWE_Q = 12289`, `RLWE_ZKPOK_REPS = 24`, `RLWE_ZKPOK_CHAL_BITS = 11`:
      `crates/qsag-core/src/preprocessing.rs:616`, `:626`, `:1080`, `:1083`. -/
@[expose] def densePcgV3Profile : DensePcgProfile where
  defaultTreeDepth := 15
  leavesPerTree := 32768
  treesPerBundle := 64
  bundleAmbientDim := 2097152
  tapsPerTree := 11
  lpnRowWeight := 704
  numPackedWords := 1024
  numBoolTriples := 65536
  numFullFieldCompanions := 64
  spcotCheckReps := 2
  maxSeedWireBytes := 36864
  rlweRingDim := 1024
  rlweModulus := 12289
  rlweZkpokReps := 24
  rlweChallengeBits := 11

theorem pqCredentialProfile_wellFormed :
    pqCredentialProfile.WellFormed ∧ densePcgV3Profile.WellFormed := by
  unfold CredentialProfile.WellFormed DensePcgProfile.WellFormed
    DensePcgProfile.twoPartySeedWireBytes pqCredentialProfile densePcgV3Profile
  decide

/-- Rust-parity literals of the production credential and dense-PCG profiles. -/
theorem pqCredentialProfile_soundness_params :
    pqCredentialProfile.maxAttrs = 32 ∧
    pqCredentialProfile.sdLimboParties = 2 ^ pqCredentialProfile.sdGgmDepth ∧
    pqCredentialProfile.sdLimboParties = 256 ∧
    pqCredentialProfile.sdExtDegree = 5 ∧
    pqCredentialProfile.sdRepsQuantum = 33 ∧
    pqCredentialProfile.mlDsaChallengeWeight = 39 ∧
    densePcgV3Profile.bundleAmbientDim = densePcgV3Profile.treesPerBundle * densePcgV3Profile.leavesPerTree ∧
    densePcgV3Profile.lpnRowWeight = densePcgV3Profile.treesPerBundle * densePcgV3Profile.tapsPerTree := by
  unfold pqCredentialProfile densePcgV3Profile
  decide

/-- Rust-parity literals added with the `voprf.rs` / `pcg_dense.rs` update: five TOPRF servers with
    threshold two, `438` issuance repetitions against `33` presentation repetitions, and the dense
    PCG geometry (`tapsPerTree = 11`, `lpnRowWeight = 704`) with its exact 2-party seed length. -/
theorem pqCredentialProfile_rust_parity :
    pqCredentialProfile.toprfServers = 5 ∧
    pqCredentialProfile.toprfThreshold = 2 ∧
    pqCredentialProfile.issuanceRepsQuantum = 438 ∧
    pqCredentialProfile.sdRepsQuantum = 33 ∧
    densePcgV3Profile.treesPerBundle = 64 ∧
    densePcgV3Profile.tapsPerTree = 11 ∧
    densePcgV3Profile.bundleAmbientDim = 2097152 ∧
    densePcgV3Profile.lpnRowWeight = 704 ∧
    densePcgV3Profile.numPackedWords = 1024 ∧
    densePcgV3Profile.numBoolTriples = 65536 ∧
    densePcgV3Profile.numFullFieldCompanions = 64 ∧
    densePcgV3Profile.maxSeedWireBytes = 36864 ∧
    densePcgV3Profile.twoPartySeedWireBytes = 32066 := by
  unfold DensePcgProfile.twoPartySeedWireBytes pqCredentialProfile densePcgV3Profile
  decide

/-- A well-formed credential profile admits no empty credential and its presentation party count
    is the size of its GGM tree. -/
theorem CredentialProfile.WellFormed.attrs_and_parties {p : CredentialProfile} (h : p.WellFormed) :
    0 < p.maxAttrs ∧ p.sdLimboParties = 2 ^ p.sdGgmDepth ∧
    p.toprfMaxCorrupt < p.toprfThreshold ∧ p.toprfThreshold ≤ p.toprfServers := by
  obtain ⟨hA, _, _, hC, hT, hO, _, _, _, _, _, hN, _⟩ := h
  exact ⟨hA, hN, hC, Nat.le_trans hT hO⟩

/-- Tooth (audit #10): a 3-server committee fails the honest-majority equation, an issuance proof
    with presentation-sized repetition counts fails the ZKBoo budget, and `maxAttrs = 0` is rejected. -/
theorem CredentialProfile.wellFormed_rejects_stale_committee_and_reps :
    ¬ (({ pqCredentialProfile with toprfServers := 3 } : CredentialProfile).WellFormed ∨
       ({ pqCredentialProfile with issuanceRepsClassical := 17, issuanceRepsQuantum := 34 } :
          CredentialProfile).WellFormed ∨
       ({ pqCredentialProfile with maxAttrs := 0 } : CredentialProfile).WellFormed) := by
  unfold CredentialProfile.WellFormed pqCredentialProfile
  decide

/-- Tooth (rust-spec-parity #6): the retired 4-tree geometry with the current ambient dimension,
    and an advertised seed bound below the real wire length, are both rejected. -/
theorem DensePcgProfile.wellFormed_rejects_stale_geometry :
    ¬ (({ densePcgV3Profile with treesPerBundle := 4 } : DensePcgProfile).WellFormed ∨
       ({ densePcgV3Profile with maxSeedWireBytes := 24576 } : DensePcgProfile).WellFormed) := by
  unfold DensePcgProfile.WellFormed DensePcgProfile.twoPartySeedWireBytes densePcgV3Profile
  decide

/-- Normative quorum profile for separated threshold custody (`0 < threshold ≤ numParties`). -/
structure CustodyQuorumProfile where
  numParties : Nat
  threshold : Nat
  spendCap : Nat
  h_pos : 0 < threshold
  h_le : threshold ≤ numParties
  deriving DecidableEq, Repr

/-- Honest-custodian intersection guarantee: when strictly fewer than `threshold` parties are
    corrupted, every `threshold`-sized approval set contains at least one honest custodian. -/
@[expose] def CustodyQuorumProfile.ToleratesCorrupt
    (p : CustodyQuorumProfile) (corruptCount : Nat) : Prop :=
  corruptCount < p.threshold

theorem CustodyQuorumProfile.honest_quorum_intersection
    (p : CustodyQuorumProfile) {corruptCount approvalCount : Nat}
    (hTol : p.ToleratesCorrupt corruptCount)
    (hQuorum : p.threshold ≤ approvalCount) :
    0 < approvalCount - corruptCount := by
  unfold CustodyQuorumProfile.ToleratesCorrupt at hTol
  omega

#verify_constructive
  Qsag.Spec.pq128StatelessProfile_wellFormed
  Qsag.Spec.corduroyPoseidon2Profile_params
  Qsag.Spec.baggySha3_128fProfile_wellFormed
  Qsag.Spec.HashSigProfile.WellFormed.securityBits_eq
  Qsag.Spec.HashSigProfile.WellFormed.wotsChainCount_mul_log2
  Qsag.Spec.HashSigProfile.WellFormed.maxSigs_le_leaves
  Qsag.Spec.slhDsaShake128fProfile_not_wellFormed
  Qsag.Spec.pq128StatefulEpochProfile_wellFormed
  Qsag.Spec.StatefulJortsProfile.WellFormed.securityBits_eq
  Qsag.Spec.jortsPoseidon2HashProfile_eq_statefulEpochProfile
  Qsag.Spec.hemGoldilocksExt4Profile_basePrime_eq
  Qsag.Spec.hemGoldilocksExt4Profile_highCap_and_zeroPow_eq
  Qsag.Spec.hemGoldilocksExt4Profile_wellFormed
  Qsag.Spec.AggregationProfile.WellFormed.query_lists_aligned
  Qsag.Spec.pqCredentialProfile_wellFormed
  Qsag.Spec.pqCredentialProfile_soundness_params
  Qsag.Spec.pqCredentialProfile_rust_parity
  Qsag.Spec.CredentialProfile.WellFormed.attrs_and_parties
  Qsag.Spec.CustodyQuorumProfile.honest_quorum_intersection

#tooth_pair Qsag.Spec.baggySha3_128fProfile_wellFormed vs
  Qsag.Spec.BaggyPorsFpProfile.wellFormed_rejects_bad_pors_or_bytes

#tooth_pair Qsag.Spec.HashSigProfile.WellFormed.securityBits_eq vs
  Qsag.Spec.HashSigProfile.wellFormed_rejects_short_digest
#tooth_pair Qsag.Spec.HashSigProfile.WellFormed.wotsChainCount_mul_log2 vs
  Qsag.Spec.HashSigProfile.wellFormed_rejects_wrong_wotsChainCount
#tooth_pair Qsag.Spec.HashSigProfile.WellFormed.maxSigs_le_leaves vs
  Qsag.Spec.HashSigProfile.wellFormed_rejects_maxSigs_above_leaves
#tooth_pair Qsag.Spec.AggregationProfile.WellFormed.query_lists_aligned vs
  Qsag.Spec.AggregationProfile.wellFormed_rejects_short_queries
#tooth_pair Qsag.Spec.StatefulJortsProfile.WellFormed.securityBits_eq vs
  Qsag.Spec.StatefulJortsProfile.wellFormed_rejects_oversized_or_wrong_chains
#tooth_pair Qsag.Spec.CredentialProfile.WellFormed.attrs_and_parties vs
  Qsag.Spec.CredentialProfile.wellFormed_rejects_stale_committee_and_reps
#tooth_pair Qsag.Spec.pqCredentialProfile_wellFormed vs
  Qsag.Spec.DensePcgProfile.wellFormed_rejects_stale_geometry

end Qsag.Spec
end

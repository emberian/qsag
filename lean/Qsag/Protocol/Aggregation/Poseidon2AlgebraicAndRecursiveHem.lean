module
/-
# Qsag.Protocol.Aggregation.Poseidon2AlgebraicAndRecursiveHem — Poseidon2 Algebraic Margins & 2-Layer `Hem` Extraction

1. **§1 Power maps on `Goldilocks`.** Fermat on the field carrier (`goldilocksPow_fermat`), the
   exponent-inverse law `d * e = k * (p - 1) + 1 → (x ^ d) ^ e = x`
   (`goldilocksPow_pow_of_exponent_inverse`), its `d = 7` instance, and non-injectivity of
   `x ↦ x ^ d` for every `2 ≤ d < 7` (`sbox7_is_minimal_nontrivial_power_permutation`,
   `tooth_d3_not_permutation_on_goldilocks`, `tooth_d5_not_permutation_on_goldilocks`).
2. **§2 Width-16 external layer.** `applyM4` is `circ(2, 3, 1, 1)` (`applyM4_eq_circ_2_3_1_1`);
   the width-16 layer `M_E = circ(2 M_4, M_4, M_4, M_4)` has a two-sided inverse
   (`applyME16Inv_applyME16`, `applyME16_applyME16Inv`) and maps non-zero states to non-zero
   states. The deployed permutation `poseidon2Perm12` has width 12; its layer is inverted in
   `Qsag.Poseidon2`.
3. **§3 Round-count arithmetic for `R_F = 8`, `R_P = 22`, `d = 7`.** The nominal degree `7 ^ r`
   first reaches `p` at `r = 23` (`poseidon2_nominal_degree_threshold`), `2 ^ 84 < 7 ^ 30 < 2 ^ 85`
   (`tooth_univariate_degree_alone_below_two_pow_128`), the interpolation round inequality
   `1 + ⌈64 log_7 2⌉ + ⌈log_7 t⌉ ≤ R_F + R_P` for `t ∈ {12, 16}` with a failing `R_P = 17`
   tooth, and the sample lower bound behind it: any `n` sample points admit a non-zero polynomial
   with `n + 1` coefficients vanishing on all of them (`univariate_interpolation_underdetermined`).
   These are statements about the parameter set and about polynomials of a given degree. The
   degree of the permutation's actual interpolation polynomial is not computed here.
4. **§4 Two-layer hierarchical `Hem`.** Root verifiers (`verifyHierarchicalHem`, `verifyHemHierarchy`,
   and direct policy check `verifyHemHierarchyAgainstRegistry`) over `M` shard certificates, each a
   `verifySuccinctAggregate` proof on `shardBoundMessage shardId epochFloor msg`, with
   pairwise-distinct shard ids, pairwise-disjoint committees, and an injective commitment to the
   shard policy registry (`ShardRegistration` binding `shardId`, `threshold`, `suiteId`, `params`,
   and `committee`, with `1 ≤ threshold ≤ |committee|`). `extractShardEnvFromTranscript` grounds
   `StagesBound` in prover commitment-opening transcripts with exact opening-cost accounting
   (`hierarchyTranscriptQueryCost`) and composes with `extractHierarchicalHemQuorums`
   (`extractHierarchicalHemFromTranscripts`). `hierarchical_hem_soundness_error_bound` establishes
   the finite-coin union bound under authenticated registry digests (`HashCollisionWitness H` on
   root mismatch), paired with `#tooth` theorems `tooth_forged_lower_shard_threshold_rejected` and
   `tooth_unscoped_shard_id_allows_quorum_replay_multiplication`. The root verifies shard
   certificates directly; no verifier is arithmetized inside another proof.
5. **§5 Deployed width-12 inverses and exact M4 branch number.** Both actual linear layers and
   both round types have two-sided inverses. The deployed permutation is injective. Cofactor
   certificates for all 69 square minors establish the universal M4 branch bound, with a unit
   vector attaining five; `m4_mds_branch_number_eq_five` uses the `Fin 4 → Goldilocks` interface.
6. **§6 Actual four-lane differential and symbolic circuits.** The seventh-power S-box preserves
   differential support. Two consecutive four-lane rounds have at least five active S-boxes;
   eight such rounds have at least twenty. A polynomial-expression circuit evaluates to the
   actual four-lane round and has degree at most `7^r` after `r` rounds. These are component
   bounds, not a differential probability or interpolation-degree lower bound for width 12.
7. **§7 Concrete hierarchical certificates & prover transcripts.** Two distinct singleton committees
   with threshold one use the honest two-stage WHIR prover, verified commitment-opening transcripts,
   and a Poseidon2 registry commitment, alongside concrete Poseidon2 forged-threshold rejection
   witnesses (`1 → 0` and `2 → 1` on a two-key committee) and unconditional replay rejection. The
   example uses the field-based signature suite from `Aggregation`, not a claimed secure
   instantiation of that suite.
8. **§8 Width-12 `M_E` & `M_I` differential and linear branch numbers.** Exact 12-lane differential
   and transpose-linear branch bounds for `applyME` (single-block `≥ 7 ≥ 5`, multi-block `≥ 8`,
   universal `= 7`) and `applyMI` (nonzero-sum `= 13` with full 12-lane diffusion on single-lane
   inputs, universal `≥ 4`).
9. **§9 `sbox7` differential uniformity `≤ 6` and width-12 activity.**
   Degree-6 root bound on `(x + Δ)^7 - x^7 = δ` (`Δ ≠ 0`), `≥ 28` active S-boxes across the
   deployed 30-round `poseidon2Perm12`, and arithmetic powers of component bounds. No
   fixed-permutation differential probability or Fourier linear-trail theorem is proved.
10. **§10 Width-12 symbolic circuit and nominal CICO arithmetic.**
    `PoseidonExpr` evaluation equals `poseidon2Perm12`; affine inputs have syntactic degree
    at most `7^30`. Exponent and matrix-size inequalities do not prove actual degree,
    semi-regularity, matrix rank, or attack-complexity lower bounds.
11. **§11 Succinct outer recursive `Hem` aggregation & soundness composition.** Single outer
    `bciksJohnsonQrom128` certificate over length-framed compressed shard headers with constructive
    witness extraction and finite-coin error bound `M · ε_hem + ε_outer`.
-/

public import Qsag.Math.Goldilocks
import all Qsag.Math.Goldilocks
public import Qsag.Oracle.Poseidon2
import all Qsag.Oracle.Poseidon2
public import Qsag.Protocol.Aggregation.Aggregation
import all Qsag.Protocol.Aggregation.Aggregation
import Lean

import Qsag.Tactic.AssuranceKit
import Qsag.Math.Tactic.CommRing

public section
namespace Qsag

open Aggregation RoundPoly

set_option autoImplicit false

/-! ## 4. Two-Layer Hierarchical `Hem`: Root Verifier, Tree Extractor, Union Bound -/

def hemShardDomainTag : List UInt8 := "QSAG.HEM.SHARD/v1".toUTF8.toList

/-- Shard-scoped signing message: every field is length-framed by `encodeMultiFrame`. -/
def shardBoundMessage (shardId epochFloor msg : List UInt8) : List UInt8 :=
  encodeMultiFrame [hemShardDomainTag, shardId, epochFloor, msg]

theorem shardBoundMessage_injective {s₁ e₁ m₁ s₂ e₂ m₂ : List UInt8}
    (h : shardBoundMessage s₁ e₁ m₁ = shardBoundMessage s₂ e₂ m₂) :
    s₁ = s₂ ∧ e₁ = e₂ ∧ m₁ = m₂ := by
  have hList := encodeMultiFrame_injective h
  simp only [List.cons.injEq, and_true, true_and] at hList
  exact hList

/-- One regional shard certificate presented to the root verifier. -/
structure HemShardProof where
  shardId : List UInt8
  threshold : Nat
  inst : AggPublicInstance
  proof : SuccinctAggregateProof
  fs : List UInt8

/-- Registry row: a shard id together with its authorized quorum threshold, hash suite id,
    signature parameter profile, and custodian cluster's committee. -/
structure ShardRegistration where
  shardId : List UInt8
  threshold : Nat
  suiteId : List UInt8
  params : PqHashParams
  committee : List PqPublicKey
  deriving DecidableEq

/-- A shard policy row is well-formed when its required quorum threshold satisfies
    `1 ≤ threshold ≤ |committee|`. -/
def ShardRegistration.WellFormed (r : ShardRegistration) : Bool :=
  decide (1 ≤ r.threshold) && decide (r.threshold ≤ r.committee.length)

def HemShardProof.registration (s : HemShardProof) : ShardRegistration :=
  ⟨s.shardId, s.threshold, s.inst.suite.suiteId, s.inst.params, s.inst.committee⟩

/-- Canonical length-framed serialization of all 8 fields of `PqHashParams`. -/
def encodePqHashParams (p : PqHashParams) : List UInt8 :=
  encodeMultiFrame [
    leb128 p.w,
    leb128 p.ell1,
    leb128 p.subtreeHeight,
    leb128 p.numLayers,
    leb128 p.forsTrees,
    leb128 p.forsHeight,
    leb128 p.maxSigsLog2,
    [if p.statefulJorts then 1 else 0]
  ]

/-- Canonical length-framed serialization of all 5 fields of `ShardRegistration`. -/
def encodeRegistration (r : ShardRegistration) : List UInt8 :=
  encodeMultiFrame [
    r.shardId,
    leb128 r.threshold,
    r.suiteId,
    encodePqHashParams r.params,
    encodeMultiFrame (r.committee.map fun pk => encodeMultiFrame [pk.pkSeed, pk.pkRoot])
  ]

def encodeRegistry (rs : List ShardRegistration) : List UInt8 :=
  encodeMultiFrame (rs.map encodeRegistration)

private theorem leb128_injective {a b : Nat} (h : leb128 a = leb128 b) : a = b :=
  (leb128_prefix_inj (r₁ := []) (r₂ := []) (by simpa using h)).1

private theorem map_inj_of_inj {α β : Type} {f : α → β} (hf : ∀ a b, f a = f b → a = b) :
    ∀ {l l' : List α}, l.map f = l'.map f → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l, b :: l', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hf a b h.1, map_inj_of_inj hf h.2]

private theorem encodePk_injective (a b : PqPublicKey)
    (h : encodeMultiFrame [a.pkSeed, a.pkRoot] = encodeMultiFrame [b.pkSeed, b.pkRoot]) :
    a = b := by
  have h0 := encodeMultiFrame_injective h
  obtain ⟨hSeed, h1⟩ := List.cons.inj h0
  obtain ⟨hRoot, _⟩ := List.cons.inj h1
  cases a; cases b
  simp only at hSeed hRoot
  rw [hSeed, hRoot]

theorem encodePqHashParams_injective {a b : PqHashParams}
    (h : encodePqHashParams a = encodePqHashParams b) : a = b := by
  have h0 := encodeMultiFrame_injective h
  obtain ⟨hw, h1⟩ := List.cons.inj h0
  obtain ⟨hell, h2⟩ := List.cons.inj h1
  obtain ⟨hsub, h3⟩ := List.cons.inj h2
  obtain ⟨hlay, h4⟩ := List.cons.inj h3
  obtain ⟨hft, h5⟩ := List.cons.inj h4
  obtain ⟨hfh, h6⟩ := List.cons.inj h5
  obtain ⟨hmax, h7⟩ := List.cons.inj h6
  obtain ⟨hst, _⟩ := List.cons.inj h7
  have hb : a.statefulJorts = b.statefulJorts := by
    cases ha : a.statefulJorts <;> cases hb' : b.statefulJorts <;>
      simp [ha, hb'] at hst <;> rfl
  cases a; cases b
  simp only at hw hell hsub hlay hft hfh hmax hb
  rw [leb128_injective hw, leb128_injective hell, leb128_injective hsub,
      leb128_injective hlay, leb128_injective hft, leb128_injective hfh,
      leb128_injective hmax, hb]

theorem encodeRegistration_injective {a b : ShardRegistration}
    (h : encodeRegistration a = encodeRegistration b) : a = b := by
  have h0 := encodeMultiFrame_injective h
  obtain ⟨hSid, h1⟩ := List.cons.inj h0
  obtain ⟨hThr, h2⟩ := List.cons.inj h1
  obtain ⟨hSuite, h3⟩ := List.cons.inj h2
  obtain ⟨hParams, h4⟩ := List.cons.inj h3
  obtain ⟨hComRaw, _⟩ := List.cons.inj h4
  have hThrEq := leb128_injective hThr
  have hParamsEq := encodePqHashParams_injective hParams
  have hCom := map_inj_of_inj encodePk_injective (encodeMultiFrame_injective hComRaw)
  cases a; cases b
  simp only at hSid hThrEq hSuite hParamsEq hCom
  rw [hSid, hThrEq, hSuite, hParamsEq, hCom]

theorem encodeRegistry_injective {rs₁ rs₂ : List ShardRegistration}
    (h : encodeRegistry rs₁ = encodeRegistry rs₂) : rs₁ = rs₂ :=
  map_inj_of_inj (fun _ _ => encodeRegistration_injective) (encodeMultiFrame_injective h)

/-- Two distinct registries under one digest are a concrete collision of `H`. -/
def registryCollision (H : Hash) {digest : List UInt8} {claimed registry : List ShardRegistration}
    (hClaimed : H (encodeRegistry claimed) = digest) (hReg : H (encodeRegistry registry) = digest)
    (hNe : claimed ≠ registry) : HashCollisionWitness H :=
  ⟨encodeRegistry claimed, encodeRegistry registry,
    fun h => hNe (encodeRegistry_injective h), hClaimed.trans hReg.symm⟩

/-- Per-shard check: shard-scoped message, well-formed threshold (`1 ≤ threshold ≤ |committee|`),
    threshold met by the bitmap, and accepting succinct aggregate certificate. -/
def verifyHemShard (arith : RowArithmetization) (dom : WhirDomain)
    (epochFloor msg : List UInt8) (s : HemShardProof) : Bool :=
  decide (s.inst.message = shardBoundMessage s.shardId epochFloor msg) &&
  decide (1 ≤ s.threshold) &&
  decide (s.threshold ≤ s.inst.committee.length) &&
  decide (s.threshold ≤ bitmapPopcountSpec s.proof.agg.bitmap) &&
  verifySuccinctAggregate arith dom s.inst s.proof s.fs

def hierarchicalShardIds : List HemShardProof → List (List UInt8)
  | [] => []
  | s :: rest => s.shardId :: hierarchicalShardIds rest

def hierarchicalCommittee : List HemShardProof → List PqPublicKey
  | [] => []
  | s :: rest => s.inst.committee ++ hierarchicalCommittee rest

def hierarchicalClaimedWeight : List HemShardProof → Nat
  | [] => 0
  | s :: rest => bitmapPopcountSpec s.proof.agg.bitmap + hierarchicalClaimedWeight rest

def hierarchicalThresholdSum : List HemShardProof → Nat
  | [] => 0
  | s :: rest => s.threshold + hierarchicalThresholdSum rest

def registryThresholdSum : List ShardRegistration → Nat
  | [] => 0
  | r :: rest => r.threshold + registryThresholdSum rest

theorem hierarchicalThresholdSum_eq_registryThresholdSum :
    ∀ shards : List HemShardProof,
      hierarchicalThresholdSum shards =
        registryThresholdSum (shards.map HemShardProof.registration)
  | [] => rfl
  | s :: rest => by
    simp only [List.map_cons, hierarchicalThresholdSum, registryThresholdSum,
      HemShardProof.registration, hierarchicalThresholdSum_eq_registryThresholdSum rest]

/-- Root verifier of the two-layer hierarchy: registry commitment, pairwise-distinct shard ids,
    pairwise-disjoint duplicate-free committees, and every shard certificate. -/
def verifyHierarchicalHem (H : Hash) (arith : RowArithmetization) (dom : WhirDomain)
    (registryDigest epochFloor msg : List UInt8) (shards : List HemShardProof) : Bool :=
  decide (H (encodeRegistry (shards.map HemShardProof.registration)) = registryDigest) &&
  decide ((hierarchicalShardIds shards).Nodup) &&
  decide ((hierarchicalCommittee shards).Nodup) &&
  shards.all (verifyHemShard arith dom epochFloor msg)

abbrev verifyHemHierarchy := verifyHierarchicalHem

/-- Direct registered-policy root verifier: enforces `ShardRegistration.WellFormed` on every row
    and exact structural equality between `shards.map HemShardProof.registration` and `registry`. -/
def verifyHemHierarchyAgainstRegistry (arith : RowArithmetization) (dom : WhirDomain)
    (registry : List ShardRegistration) (epochFloor msg : List UInt8)
    (shards : List HemShardProof) : Bool :=
  registry.all ShardRegistration.WellFormed &&
  decide (shards.map HemShardProof.registration = registry) &&
  decide ((hierarchicalShardIds shards).Nodup) &&
  decide ((hierarchicalCommittee shards).Nodup) &&
  shards.all (verifyHemShard arith dom epochFloor msg)

theorem verifyHemShard_facts {arith : RowArithmetization} {dom : WhirDomain}
    {epochFloor msg : List UInt8} {s : HemShardProof}
    (h : verifyHemShard arith dom epochFloor msg s = true) :
    s.inst.message = shardBoundMessage s.shardId epochFloor msg ∧
    1 ≤ s.threshold ∧
    s.threshold ≤ s.inst.committee.length ∧
    s.threshold ≤ bitmapPopcountSpec s.proof.agg.bitmap ∧
    verifySuccinctAggregate arith dom s.inst s.proof s.fs = true := by
  unfold verifyHemShard at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem verifyHemShard_wellFormed {arith : RowArithmetization} {dom : WhirDomain}
    {epochFloor msg : List UInt8} {s : HemShardProof}
    (h : verifyHemShard arith dom epochFloor msg s = true) :
    s.registration.WellFormed = true := by
  have hF := verifyHemShard_facts h
  exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hF.2.1, decide_eq_true hF.2.2.1⟩

theorem verifyHierarchicalHem_facts {H : Hash} {arith : RowArithmetization} {dom : WhirDomain}
    {registryDigest epochFloor msg : List UInt8} {shards : List HemShardProof}
    (h : verifyHierarchicalHem H arith dom registryDigest epochFloor msg shards = true) :
    H (encodeRegistry (shards.map HemShardProof.registration)) = registryDigest ∧
    (hierarchicalShardIds shards).Nodup ∧
    (hierarchicalCommittee shards).Nodup ∧
    ∀ s ∈ shards, verifyHemShard arith dom epochFloor msg s = true := by
  unfold verifyHierarchicalHem at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem verifyHemHierarchyAgainstRegistry_facts {arith : RowArithmetization} {dom : WhirDomain}
    {registry : List ShardRegistration} {epochFloor msg : List UInt8}
    {shards : List HemShardProof}
    (h : verifyHemHierarchyAgainstRegistry arith dom registry epochFloor msg shards = true) :
    (∀ r ∈ registry, r.WellFormed = true) ∧
    shards.map HemShardProof.registration = registry ∧
    (hierarchicalShardIds shards).Nodup ∧
    (hierarchicalCommittee shards).Nodup ∧
    ∀ s ∈ shards, verifyHemShard arith dom epochFloor msg s = true := by
  unfold verifyHemHierarchyAgainstRegistry at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem verifyHemHierarchyAgainstRegistry_implies_verifyHierarchicalHem (H : Hash)
    {arith : RowArithmetization} {dom : WhirDomain}
    {registry : List ShardRegistration} {registryDigest epochFloor msg : List UInt8}
    {shards : List HemShardProof}
    (hReg : H (encodeRegistry registry) = registryDigest)
    (h : verifyHemHierarchyAgainstRegistry arith dom registry epochFloor msg shards = true) :
    verifyHierarchicalHem H arith dom registryDigest epochFloor msg shards = true := by
  have hF := verifyHemHierarchyAgainstRegistry_facts h
  unfold verifyHierarchicalHem
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  rw [hF.2.1]
  exact ⟨⟨⟨hReg, hF.2.2.1⟩, hF.2.2.2.1⟩, hF.2.2.2.2⟩

/-- Signing slot of the hierarchy: one committee key of one shard. -/
structure HemSlot where
  shardId : List UInt8
  suite : TweakableHashSuite
  params : PqHashParams
  pk : PqPublicKey

/-- An extracted signature, valid for its slot on the shard-scoped message. -/
structure ExtractedQuorumSig (epochFloor msg : List UInt8) where
  slot : HemSlot
  sig : PqHashSig
  valid : verifyPqHashSig slot.suite slot.params slot.pk
    (shardBoundMessage slot.shardId epochFloor msg) sig = true

def activeKeys : List PqPublicKey → SignerBitmapSpec → List PqPublicKey
  | pk :: pks, b :: bs => if b then pk :: activeKeys pks bs else activeKeys pks bs
  | _, _ => []

def shardActiveSlots (s : HemShardProof) : List HemSlot :=
  (activeKeys s.inst.committee s.proof.agg.bitmap).map
    (HemSlot.mk s.shardId s.inst.suite s.inst.params)

def hierarchicalActiveSlots : List HemShardProof → List HemSlot
  | [] => []
  | s :: rest => shardActiveSlots s ++ hierarchicalActiveSlots rest

theorem activeKeys_sublist :
    ∀ (pks : List PqPublicKey) (bs : SignerBitmapSpec), (activeKeys pks bs).Sublist pks
  | [], _ => by simp [activeKeys]
  | _ :: _, [] => by simp [activeKeys]
  | pk :: pks, true :: bs => by
    simp only [activeKeys, ite_true]
    exact (activeKeys_sublist pks bs).cons_cons pk
  | pk :: pks, false :: bs => by
    simp only [activeKeys, Bool.false_eq_true, ite_false]
    exact (activeKeys_sublist pks bs).cons pk

theorem hierarchicalActiveSlots_pk_sublist :
    ∀ shards : List HemShardProof,
      ((hierarchicalActiveSlots shards).map HemSlot.pk).Sublist (hierarchicalCommittee shards)
  | [] => by simp [hierarchicalActiveSlots, hierarchicalCommittee]
  | s :: rest => by
    simp only [hierarchicalActiveSlots, hierarchicalCommittee, List.map_append]
    refine List.Sublist.append ?_ (hierarchicalActiveSlots_pk_sublist rest)
    have hMap : (shardActiveSlots s).map HemSlot.pk =
        activeKeys s.inst.committee s.proof.agg.bitmap := by
      unfold shardActiveSlots
      rw [List.map_map]
      exact List.map_id _
    rw [hMap]
    exact activeKeys_sublist _ _

/-- Signatures of the active signers of one shard, read off an all-active-signers check. -/
def collectShardSigs (epochFloor msg shardId : List UInt8) (suite : TweakableHashSuite)
    (params : PqHashParams) :
    (pks : List PqPublicKey) → (bs : SignerBitmapSpec) → (sigs : List PqHashSig) →
    checkAllActiveSigners suite params (shardBoundMessage shardId epochFloor msg) pks bs sigs
      = true →
    List (ExtractedQuorumSig epochFloor msg)
  | [], [], _, _ => []
  | [], _ :: _, _, h => absurd h (by simp [checkAllActiveSigners])
  | _ :: _, [], _, h => absurd h (by simp [checkAllActiveSigners])
  | _ :: _, _ :: _, [], h => absurd h (by simp [checkAllActiveSigners])
  | pk :: pks, true :: bs, sig :: sigs, h =>
    have h' : verifyPqHashSig suite params pk (shardBoundMessage shardId epochFloor msg) sig = true ∧
        checkAllActiveSigners suite params (shardBoundMessage shardId epochFloor msg) pks bs sigs
          = true := by
      simpa [checkAllActiveSigners] using h
    ⟨⟨shardId, suite, params, pk⟩, sig, h'.1⟩ ::
      collectShardSigs epochFloor msg shardId suite params pks bs sigs h'.2
  | _ :: pks, false :: bs, _ :: sigs, h =>
    collectShardSigs epochFloor msg shardId suite params pks bs sigs
      (by simpa [checkAllActiveSigners] using h)

theorem collectShardSigs_slots (epochFloor msg shardId : List UInt8) (suite : TweakableHashSuite)
    (params : PqHashParams) :
    ∀ (pks : List PqPublicKey) (bs : SignerBitmapSpec) (sigs : List PqHashSig)
      (h : checkAllActiveSigners suite params (shardBoundMessage shardId epochFloor msg) pks bs sigs
        = true),
      (collectShardSigs epochFloor msg shardId suite params pks bs sigs h).map (·.slot) =
        (activeKeys pks bs).map (HemSlot.mk shardId suite params) ∧
      (collectShardSigs epochFloor msg shardId suite params pks bs sigs h).length =
        bitmapPopcountSpec bs
  | [], [], _, _ => by simp [collectShardSigs, activeKeys, bitmapPopcountSpec]
  | [], _ :: _, _, h => absurd h (by simp [checkAllActiveSigners])
  | _ :: _, [], _, h => absurd h (by simp [checkAllActiveSigners])
  | _ :: _, _ :: _, [], h => absurd h (by simp [checkAllActiveSigners])
  | pk :: pks, true :: bs, sig :: sigs, h => by
    have h' : checkAllActiveSigners suite params (shardBoundMessage shardId epochFloor msg)
        pks bs sigs = true := by
      have := h
      simp [checkAllActiveSigners] at this
      exact this.2
    have ih := collectShardSigs_slots epochFloor msg shardId suite params pks bs sigs h'
    refine ⟨?_, ?_⟩
    · simp only [collectShardSigs, activeKeys, ite_true, List.map_cons, ih.1]
    · have h2 := ih.2
      simp only [collectShardSigs, bitmapPopcountSpec, ite_true, List.length_cons]
      omega
  | _ :: pks, false :: bs, _ :: sigs, h => by
    have h' : checkAllActiveSigners suite params (shardBoundMessage shardId epochFloor msg)
        pks bs sigs = true := by
      simpa [checkAllActiveSigners] using h
    have ih := collectShardSigs_slots epochFloor msg shardId suite params pks bs sigs h'
    refine ⟨?_, ?_⟩
    · simp only [collectShardSigs, activeKeys, Bool.false_eq_true, ite_false]
      exact ih.1
    · have h2 := ih.2
      simp only [collectShardSigs, bitmapPopcountSpec, Bool.false_eq_true, ite_false]
      omega

/-- Extraction context of one shard: its certificate with the lawful arithmetization and the
    committed tables the single-layer extractor reads. -/
structure HemShardEnv (arith : RowArithmetization) (dom : WhirDomain) where
  shard : HemShardProof
  law : arith.Lawful dom shard.inst
  view : SuccinctExtractionView
  bound : StagesBound view.authPath dom.stages view.allTables shard.proof.stages

/-- Break witness of the single-layer extractor for one shard certificate. -/
@[expose] def HemShardBreak (arith : RowArithmetization) (dom : WhirDomain)
    (proof : SuccinctAggregateProof) (view : SuccinctExtractionView) : Type :=
  PSum (SumcheckSchwartzZippelHit 8 proof.agg.roundPolys
      (adaptivePolys (arith.honestRound ((view.allTables.headD []).headD [])) proof.agg.challenges)
      proof.agg.challenges)
    (PSum (HashCollisionWitness pcsMerkleHash)
      (PSum (WhirStageQueryMiss proof.finalWord dom view.allTables proof)
        (WhirProximityHit arith dom proof.finalWord view.allTables proof)))

/-- Single-shard step: the active signers' signatures on the shard-scoped message, or the
    single-layer break witness. -/
def extractShardQuorum (arith : RowArithmetization) (dom : WhirDomain)
    (epochFloor msg : List UInt8) (e : HemShardEnv arith dom)
    (h : verifyHemShard arith dom epochFloor msg e.shard = true) :
    PSum { sigs : List (ExtractedQuorumSig epochFloor msg) //
        sigs.map (·.slot) = shardActiveSlots e.shard ∧
        sigs.length = bitmapPopcountSpec e.shard.proof.agg.bitmap }
      (HemShardBreak arith dom e.shard.proof e.view) :=
  have hF := verifyHemShard_facts h
  match succinct_aggregation_knowledge_soundness arith dom e.shard.inst e.law e.shard.proof
      e.shard.fs e.view hF.2.2.2.2 e.bound with
  | .inl ⟨_, hAll⟩ =>
    have hAll' : checkAllActiveSigners e.shard.inst.suite e.shard.inst.params
        (shardBoundMessage e.shard.shardId epochFloor msg) e.shard.inst.committee
        e.shard.proof.agg.bitmap
        (arith.decodeSigs ((e.view.allTables.headD []).headD [])) = true := by
      rw [← hF.1]; exact hAll
    .inl ⟨collectShardSigs epochFloor msg e.shard.shardId e.shard.inst.suite e.shard.inst.params
        e.shard.inst.committee e.shard.proof.agg.bitmap _ hAll',
      collectShardSigs_slots epochFloor msg e.shard.shardId e.shard.inst.suite
        e.shard.inst.params _ _ _ hAll'⟩
  | .inr brk => .inr brk

/-- Shard-by-shard tree walk: all shards' signatures, or the first shard index with a break. -/
def extractShardList (arith : RowArithmetization) (dom : WhirDomain)
    (epochFloor msg : List UInt8) :
    (envs : List (HemShardEnv arith dom)) →
    (∀ e ∈ envs, verifyHemShard arith dom epochFloor msg e.shard = true) →
    PSum { sigs : List (ExtractedQuorumSig epochFloor msg) //
        sigs.map (·.slot) = hierarchicalActiveSlots (envs.map (·.shard)) ∧
        sigs.length = hierarchicalClaimedWeight (envs.map (·.shard)) }
      (Σ j : Fin envs.length,
        HemShardBreak arith dom (envs.get j).shard.proof (envs.get j).view)
  | [], _ => .inl ⟨[], rfl, rfl⟩
  | e :: es, h =>
    match extractShardQuorum arith dom epochFloor msg e (h e (List.mem_cons_self ..)) with
    | .inr brk => .inr ⟨⟨0, Nat.succ_pos _⟩, brk⟩
    | .inl ⟨s0, h0⟩ =>
      match extractShardList arith dom epochFloor msg es
          (fun e' he' => h e' (List.mem_cons_of_mem _ he')) with
      | .inr ⟨⟨j, hj⟩, brk⟩ => .inr ⟨⟨j + 1, Nat.succ_lt_succ hj⟩, brk⟩
      | .inl ⟨ss, hs⟩ => .inl ⟨s0 ++ ss, by
          refine ⟨?_, ?_⟩
          · simp only [List.map_cons, List.map_append, hierarchicalActiveSlots, h0.1, hs.1]
          · have h1 := h0.2
            have h2 := hs.2
            simp only [List.map_cons, hierarchicalClaimedWeight, List.length_append]
            omega⟩

theorem hierarchicalThresholdSum_le_claimedWeight {arith : RowArithmetization} {dom : WhirDomain}
    {epochFloor msg : List UInt8} :
    ∀ shards : List HemShardProof,
      (∀ s ∈ shards, verifyHemShard arith dom epochFloor msg s = true) →
      hierarchicalThresholdSum shards ≤ hierarchicalClaimedWeight shards
  | [], _ => Nat.le_refl _
  | s :: rest, h => by
    have hs := (verifyHemShard_facts (h s (List.mem_cons_self ..))).2.2.2.1
    have ih := hierarchicalThresholdSum_le_claimedWeight rest
      (fun s' hs' => h s' (List.mem_cons_of_mem _ hs'))
    simp only [hierarchicalThresholdSum, hierarchicalClaimedWeight]
    omega

/-- Constructive policy-binding theorem for `verifyHierarchicalHem`: under an authenticated
    registry digest `H (encodeRegistry registry) = registryDigest`, acceptance either yields a
    concrete `HashCollisionWitness H`, or guarantees that `verifyHemHierarchyAgainstRegistry`
    accepts, every shard's `(shardId, threshold, suiteId, params, committee)` equals its registered
    row in `registry` with `1 ≤ threshold ≤ |committee|`, and
    `hierarchicalThresholdSum shards = registryThresholdSum registry ≤ hierarchicalClaimedWeight shards`. -/
def verifyHierarchicalHem_authenticates_registry (H : Hash) (arith : RowArithmetization)
    (dom : WhirDomain) (registryDigest epochFloor msg : List UInt8)
    (registry : List ShardRegistration)
    (hReg : H (encodeRegistry registry) = registryDigest)
    (shards : List HemShardProof)
    (hAccept : verifyHierarchicalHem H arith dom registryDigest epochFloor msg shards = true) :
    PSum
      (PLift (verifyHemHierarchyAgainstRegistry arith dom registry epochFloor msg shards = true ∧
        shards.map HemShardProof.registration = registry ∧
        (∀ r ∈ registry, r.WellFormed = true ∧ 1 ≤ r.threshold ∧ r.threshold ≤ r.committee.length) ∧
        hierarchicalThresholdSum shards = registryThresholdSum registry ∧
        registryThresholdSum registry ≤ hierarchicalClaimedWeight shards))
      (HashCollisionWitness H) :=
  have hF := verifyHierarchicalHem_facts hAccept
  if hEq : shards.map HemShardProof.registration = registry then
    .inl ⟨by
      have hWf : ∀ r ∈ registry,
          r.WellFormed = true ∧ 1 ≤ r.threshold ∧ r.threshold ≤ r.committee.length := by
        intro r hr
        rw [← hEq] at hr
        obtain ⟨s, hsMem, rfl⟩ := List.mem_map.mp hr
        have hsF := verifyHemShard_facts (hF.2.2.2 s hsMem)
        exact ⟨verifyHemShard_wellFormed (hF.2.2.2 s hsMem), hsF.2.1, hsF.2.2.1⟩
      have hSumEq : hierarchicalThresholdSum shards = registryThresholdSum registry := by
        rw [hierarchicalThresholdSum_eq_registryThresholdSum, hEq]
      have hSumLe : registryThresholdSum registry ≤ hierarchicalClaimedWeight shards := by
        rw [← hSumEq]
        exact hierarchicalThresholdSum_le_claimedWeight shards hF.2.2.2
      have hAgainst :
          verifyHemHierarchyAgainstRegistry arith dom registry epochFloor msg shards = true := by
        unfold verifyHemHierarchyAgainstRegistry
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
        exact ⟨⟨⟨⟨fun r hr => (hWf r hr).1, hEq⟩, hF.2.1⟩, hF.2.2.1⟩, hF.2.2.2⟩
      exact ⟨hAgainst, hEq, hWf, hSumEq, hSumLe⟩⟩
  else
    .inr (registryCollision H hF.1 hReg hEq)

/-- Left outcome of the tree extractor: one valid signature per active slot of every shard, for
    exactly the registered policies (`shardId`, `threshold`, `suiteId`, `params`, `committee`). -/
structure HierarchicalQuorumWitness (epochFloor msg : List UInt8)
    (registry : List ShardRegistration) (shards : List HemShardProof) where
  sigs : List (ExtractedQuorumSig epochFloor msg)
  slots_eq : sigs.map (·.slot) = hierarchicalActiveSlots shards
  weight_eq : sigs.length = hierarchicalClaimedWeight shards
  registry_eq : shards.map HemShardProof.registration = registry

/-- Right outcome: a registry hash collision at the root, or a shard index with a single-layer
    break witness. -/
@[expose] def HemHierarchyBreak (H : Hash) (arith : RowArithmetization) (dom : WhirDomain)
    (envs : List (HemShardEnv arith dom)) : Type :=
  PSum (HashCollisionWitness H)
    (Σ j : Fin envs.length, HemShardBreak arith dom (envs.get j).shard.proof (envs.get j).view)

/-- **Two-layer tree witness extractor (`extractHierarchicalHemQuorums`)**: from an accepting
    root verification against a committed registry, returns the signatures of all active signers
    of all shards, or a `HemHierarchyBreak`. -/
def extractHierarchicalHemQuorums (H : Hash) (arith : RowArithmetization) (dom : WhirDomain)
    (registryDigest epochFloor msg : List UInt8) (registry : List ShardRegistration)
    (hReg : H (encodeRegistry registry) = registryDigest)
    (envs : List (HemShardEnv arith dom))
    (hAccept : verifyHierarchicalHem H arith dom registryDigest epochFloor msg
      (envs.map (·.shard)) = true) :
    PSum (HierarchicalQuorumWitness epochFloor msg registry (envs.map (·.shard)))
      (HemHierarchyBreak H arith dom envs) :=
  have hF := verifyHierarchicalHem_facts hAccept
  if hEq : (envs.map (·.shard)).map HemShardProof.registration = registry then
    match extractShardList arith dom epochFloor msg envs
        (fun e he => hF.2.2.2 e.shard (List.mem_map.mpr ⟨e, he, rfl⟩)) with
    | .inl ⟨sigs, hSlots, hLen⟩ => .inl ⟨sigs, hSlots, hLen, hEq⟩
    | .inr brk => .inr (.inr brk)
  else
    .inr (.inl (registryCollision H hF.1 hReg hEq))

/-- **Two-layer hierarchical knowledge soundness
    (`recursive_hem_two_layer_knowledge_soundness`)**: an accepting root verification against a
    committed registry yields signatures `sigs` with one entry per active slot, at least
    `registryThresholdSum registry` (`= Σ_j K_j`) of them, under pairwise-distinct public keys
    taken from the registered committees with well-formed thresholds; otherwise there is a registry
    hash collision or a shard index with a single-layer break. -/
theorem recursive_hem_two_layer_knowledge_soundness (H : Hash) (arith : RowArithmetization)
    (dom : WhirDomain) (registryDigest epochFloor msg : List UInt8)
    (registry : List ShardRegistration) (hReg : H (encodeRegistry registry) = registryDigest)
    (envs : List (HemShardEnv arith dom))
    (hAccept : verifyHierarchicalHem H arith dom registryDigest epochFloor msg
      (envs.map (·.shard)) = true) :
    (∃ sigs : List (ExtractedQuorumSig epochFloor msg),
      sigs.map (·.slot) = hierarchicalActiveSlots (envs.map (·.shard)) ∧
      sigs.length = hierarchicalClaimedWeight (envs.map (·.shard)) ∧
      hierarchicalThresholdSum (envs.map (·.shard)) = registryThresholdSum registry ∧
      registryThresholdSum registry ≤ sigs.length ∧
      (sigs.map (·.slot.pk)).Nodup ∧
      (∀ r ∈ registry, r.WellFormed = true) ∧
      (envs.map (·.shard)).map HemShardProof.registration = registry) ∨
    Nonempty (HemHierarchyBreak H arith dom envs) := by
  have hF := verifyHierarchicalHem_facts hAccept
  match extractHierarchicalHemQuorums H arith dom registryDigest epochFloor msg registry hReg
      envs hAccept with
  | .inr brk => exact .inr ⟨brk⟩
  | .inl w =>
    have hSumEq :
        hierarchicalThresholdSum (envs.map (·.shard)) = registryThresholdSum registry := by
      rw [hierarchicalThresholdSum_eq_registryThresholdSum, w.registry_eq]
    refine .inl ⟨w.sigs, w.slots_eq, w.weight_eq, hSumEq, ?_, ?_, ?_, w.registry_eq⟩
    · rw [w.weight_eq, ← hSumEq]
      exact hierarchicalThresholdSum_le_claimedWeight _ hF.2.2.2
    · have hMap : w.sigs.map (·.slot.pk) = (w.sigs.map (·.slot)).map HemSlot.pk := by
        rw [List.map_map]; rfl
      rw [hMap, w.slots_eq]
      exact (hierarchicalActiveSlots_pk_sublist _).nodup hF.2.2.1
    · intro r hr
      rw [← w.registry_eq] at hr
      obtain ⟨s, hsMem, rfl⟩ := List.mem_map.mp hr
      exact verifyHemShard_wellFormed (hF.2.2.2 s hsMem)

/-! ### Prover commitment-opening transcript extraction (`StagesBound` grounding & query cost) -/

/-- Additional Merkle duet opening collected from a rewound prover run at `(stagePos, layer, cosetIdx)`. -/
structure RewoundDuetOpening where
  stagePos : Nat
  layer : Nat
  cosetIdx : Nat
  opening : FoldLayerOpening

/-- Prover commitment-opening transcript for one WHIR proof: `stageLayerOpenings[pos][layer][g]`
    records the prover's Merkle duet opening for coset `g` at `(stagePos = pos, layer)`, and
    `rewoundOpenings` records any auxiliary coset openings from rewound prover runs against the
    same committed Merkle roots. Contains zero unproved `Prop` assumptions. -/
structure CommittedTableTranscript where
  stageLayerOpenings : List (List (List FoldLayerOpening))
  rewoundOpenings : List RewoundDuetOpening := []

/-- Shard prover extraction bundle pairing a shard certificate with its `CommittedTableTranscript`. -/
structure ShardProverTranscript (arith : RowArithmetization) (dom : WhirDomain) where
  shard : HemShardProof
  law : arith.Lawful dom shard.inst
  transcript : CommittedTableTranscript

/-- Number of coset duet openings required across `foldLayers` intra-stage folding layers
    starting from `groups` initial cosets. -/
def stageLayerQueryCost : Nat → Nat → Nat
  | _, 0 => 0
  | groups, k + 1 => groups + stageLayerQueryCost (groups / 2) k

/-- Number of coset duet openings required to sweep all folding layers of stage `sdom`. -/
def stageTranscriptQueryCost (sdom : WhirStageDomain) : Nat :=
  stageLayerQueryCost sdom.groups0 sdom.foldLayers

/-- Number of coset duet openings required to sweep every stage in `dom`. -/
def domainTranscriptQueryCost (dom : WhirDomain) : Nat :=
  dom.stages.foldr (fun sdom acc => stageTranscriptQueryCost sdom + acc) 0

/-- Total base coset-sweep opening cost across `numShards` regional shards on `dom`. -/
def hierarchyTranscriptQueryCost (dom : WhirDomain) (numShards : Nat) : Nat :=
  numShards * domainTranscriptQueryCost dom

def layerOpeningsCount : List (List FoldLayerOpening) → Nat
  | [] => 0
  | ops :: rest => ops.length + layerOpeningsCount rest

def transcriptSweepOpeningCount (tr : CommittedTableTranscript) : Nat :=
  tr.stageLayerOpenings.foldr (fun stOps acc => layerOpeningsCount stOps + acc) 0

def transcriptTotalOpeningCount (tr : CommittedTableTranscript) : Nat :=
  transcriptSweepOpeningCount tr + tr.rewoundOpenings.length

def hierarchySweepOpeningCount {arith : RowArithmetization} {dom : WhirDomain}
    (trs : List (ShardProverTranscript arith dom)) : Nat :=
  trs.foldr (fun t acc => transcriptSweepOpeningCount t.transcript + acc) 0

def defaultFoldOpening : FoldLayerOpening :=
  ⟨GoldilocksExt4.zero, GoldilocksExt4.zero, []⟩

def layerGroupsAt : Nat → Nat → Nat
  | groups, 0 => groups
  | groups, l + 1 => layerGroupsAt (groups / 2) l

/-- Executable check that `op` is a valid Merkle duet opening at `(stageIdx, layer, g)` to `root`. -/
def verifyDuetCosetOpening (stageIdx layer groups : Nat) (root : List UInt8)
    (g : Nat) (op : FoldLayerOpening) : Bool :=
  decide (op.path.length = merkleDepth groups) &&
  decide (merklePathRoot pcsMerkleHash
    (pcsMerkleHash (duetLeafFrame stageIdx layer g op.v0 op.v1)) g op.path = root)

def verifyLayerSweepAux (stageIdx layer groups : Nat) (root : List UInt8) :
    Nat → List FoldLayerOpening → Bool
  | _, [] => true
  | g, op :: ops =>
    verifyDuetCosetOpening stageIdx layer groups root g op &&
    verifyLayerSweepAux stageIdx layer groups root (g + 1) ops

def verifyLayerSweep (stageIdx layer groups : Nat) (root : List UInt8)
    (ops : List FoldLayerOpening) : Bool :=
  decide (ops.length = groups) &&
  verifyLayerSweepAux stageIdx layer groups root 0 ops

def verifyStageLayerSweeps (stageIdx : Nat) :
    Nat → Nat → List (List FoldLayerOpening) → List (List UInt8) → Bool
  | _, _, [], [] => true
  | layer, groups, ops :: restOps, root :: roots =>
    verifyLayerSweep stageIdx layer groups root ops &&
    verifyStageLayerSweeps stageIdx (layer + 1) (groups / 2) restOps roots
  | _, _, _, _ => false

def verifyAllStageSweeps :
    List WhirStageDomain → List (List (List FoldLayerOpening)) → List WhirStageProof → Bool
  | [], [], [] => true
  | sdom :: sdoms, stOps :: restOps, sp :: sps =>
    decide (stOps ≠ []) &&
    verifyStageLayerSweeps sdom.stageIdx 0 sdom.groups0 stOps (stageAllRoots sp) &&
    verifyAllStageSweeps sdoms restOps sps
  | _, _, _ => false

def verifyRewoundOpening (dom : WhirDomain) (proof : SuccinctAggregateProof)
    (ro : RewoundDuetOpening) : Bool :=
  match dom.stages[ro.stagePos]?, proof.stages[ro.stagePos]? with
  | some sdom, some sp =>
    match (stageAllRoots sp)[ro.layer]? with
    | some root =>
      let groups := layerGroupsAt sdom.groups0 ro.layer
      decide (ro.cosetIdx < groups) &&
      verifyDuetCosetOpening sdom.stageIdx ro.layer groups root ro.cosetIdx ro.opening
    | none => false
  | _, _ => false

/-- Executable Boolean acceptor for a prover commitment-opening transcript against `(dom, proof)`. -/
def verifyCommittedTableTranscript (dom : WhirDomain) (proof : SuccinctAggregateProof)
    (tr : CommittedTableTranscript) : Bool :=
  decide ((dom.stages.map (·.stageIdx)).Nodup) &&
  verifyAllStageSweeps dom.stages tr.stageLayerOpenings proof.stages &&
  tr.rewoundOpenings.all (verifyRewoundOpening dom proof)

/-- Reconstruct the length-`2 * ops.length` layer codeword from its `ops.length` coset duet openings. -/
def reconstructLayerTable (ops : List FoldLayerOpening) : List GoldilocksExt4 :=
  ops.map (·.v0) ++ ops.map (·.v1)

def lookupStageOpenings :
    List WhirStageDomain → List (List (List FoldLayerOpening)) → Nat →
      List (List FoldLayerOpening)
  | sdom :: sdoms, stOps :: restOps, stageIdx =>
    if sdom.stageIdx = stageIdx then stOps
    else lookupStageOpenings sdoms restOps stageIdx
  | _, _, _ => []

def transcriptAuthPath (dom : WhirDomain) (tr : CommittedTableTranscript)
    (stageIdx layer g : Nat) : List (List UInt8) :=
  (((lookupStageOpenings dom.stages tr.stageLayerOpenings stageIdx).getD layer []).getD
    g defaultFoldOpening).path

/-- Reconstruct the `SuccinctExtractionView` directly from a `CommittedTableTranscript`. -/
def reconstructSuccinctView (dom : WhirDomain) (tr : CommittedTableTranscript) :
    SuccinctExtractionView where
  allTables := tr.stageLayerOpenings.map (fun stOps => stOps.map reconstructLayerTable)
  authPath := transcriptAuthPath dom tr

private theorem getD_append_left {α : Type} (d : α) :
    ∀ (xs ys : List α) (i : Nat), i < xs.length → (xs ++ ys).getD i d = xs.getD i d
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: xs, ys, i + 1, h => getD_append_left d xs ys i (Nat.lt_of_succ_lt_succ h)

private theorem getD_append_right {α : Type} (d : α) :
    ∀ (xs ys : List α) (i : Nat), (xs ++ ys).getD (i + xs.length) d = ys.getD i d
  | [], _, _ => rfl
  | _ :: xs, ys, i => by
    have hEq : i + (xs.length + 1) = (i + xs.length) + 1 := by omega
    rw [List.cons_append, List.length_cons, hEq]
    exact getD_append_right d xs ys i

private theorem getD_map_of_lt {α β : Type} (f : α → β) (da : α) (db : β) :
    ∀ (xs : List α) (i : Nat), i < xs.length → (xs.map f).getD i db = f (xs.getD i da)
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: xs, i + 1, h => getD_map_of_lt f da db xs i (Nat.lt_of_succ_lt_succ h)

private theorem reconstructLayerTable_getD_left (ops : List FoldLayerOpening) (g : Nat)
    (hg : g < ops.length) :
    (reconstructLayerTable ops).getD g CommRingOps.zero =
      (ops.getD g defaultFoldOpening).v0 := by
  unfold reconstructLayerTable
  rw [getD_append_left _ _ _ g (by simpa using hg)]
  exact getD_map_of_lt (·.v0) defaultFoldOpening CommRingOps.zero ops g hg

private theorem reconstructLayerTable_getD_right (ops : List FoldLayerOpening) (g : Nat)
    (hg : g < ops.length) :
    (reconstructLayerTable ops).getD (g + ops.length) CommRingOps.zero =
      (ops.getD g defaultFoldOpening).v1 := by
  unfold reconstructLayerTable
  have hLen : (ops.map (·.v0)).length = ops.length := List.length_map _
  rw [← hLen, getD_append_right]
  exact getD_map_of_lt (·.v1) defaultFoldOpening CommRingOps.zero ops g hg

private theorem verifyLayerSweepAux_getD {stageIdx layer groups : Nat} {root : List UInt8} :
    ∀ (ops : List FoldLayerOpening) (base i : Nat),
      i < ops.length →
      verifyLayerSweepAux stageIdx layer groups root base ops = true →
      verifyDuetCosetOpening stageIdx layer groups root (base + i)
        (ops.getD i defaultFoldOpening) = true
  | [], _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | _ :: _, base, 0, _, h => by
    rw [Nat.add_zero]
    exact (Bool.and_eq_true_iff.mp h).1
  | _ :: ops, base, i + 1, hi, h => by
    have ih := verifyLayerSweepAux_getD ops (base + 1) i (Nat.lt_of_succ_lt_succ hi)
      (Bool.and_eq_true_iff.mp h).2
    have hAdd : base + (i + 1) = (base + 1) + i := by omega
    rw [hAdd]
    exact ih

private theorem verifyLayerSweep_at {stageIdx layer groups : Nat} {root : List UInt8}
    {ops : List FoldLayerOpening}
    (h : verifyLayerSweep stageIdx layer groups root ops = true) :
    ops.length = groups ∧
    ∀ g, g < groups →
      verifyDuetCosetOpening stageIdx layer groups root g (ops.getD g defaultFoldOpening) = true := by
  obtain ⟨hLen, hAux⟩ := Bool.and_eq_true_iff.mp h
  have hEq : ops.length = groups := of_decide_eq_true hLen
  refine ⟨hEq, fun g hg => ?_⟩
  simpa only [Nat.zero_add] using
    verifyLayerSweepAux_getD ops 0 g (hEq.symm ▸ hg) hAux

private theorem verifyDuetCosetOpening_facts {stageIdx layer groups : Nat} {root : List UInt8}
    {g : Nat} {op : FoldLayerOpening}
    (h : verifyDuetCosetOpening stageIdx layer groups root g op = true) :
    op.path.length = merkleDepth groups ∧
    merklePathRoot pcsMerkleHash
      (pcsMerkleHash (duetLeafFrame stageIdx layer g op.v0 op.v1)) g op.path = root := by
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩

private theorem stageLayersBound_of_sweeps (authPath : Nat → Nat → Nat → List (List UInt8))
    (stageIdx : Nat) :
    ∀ (stOps : List (List FoldLayerOpening)) (roots : List (List UInt8)) (baseLayer groups : Nat),
      (∀ k g, authPath stageIdx (baseLayer + k) g =
        ((stOps.getD k []).getD g defaultFoldOpening).path) →
      verifyStageLayerSweeps stageIdx baseLayer groups stOps roots = true →
      StageLayersBound authPath stageIdx baseLayer groups (stOps.map reconstructLayerTable) roots
  | [], [], _, _, _, _ => trivial
  | [], _ :: _, _, _, _, h => absurd h Bool.false_ne_true
  | _ :: _, [], _, _, _, h => absurd h Bool.false_ne_true
  | ops :: restOps, root :: roots, baseLayer, groups, hAuth, hSw => by
    obtain ⟨hHead, hTail⟩ := Bool.and_eq_true_iff.mp hSw
    obtain ⟨hLen, hAt⟩ := verifyLayerSweep_at hHead
    refine ⟨fun g hg => ?_, ?_⟩
    · have hgOps : g < ops.length := hLen.symm ▸ hg
      have hOpen := verifyDuetCosetOpening_facts (hAt g hg)
      have hPath : authPath stageIdx baseLayer g = (ops.getD g defaultFoldOpening).path := by
        have h0 := hAuth 0 g
        rw [Nat.add_zero] at h0
        exact h0
      rw [reconstructLayerTable_getD_left ops g hgOps,
          ← hLen, reconstructLayerTable_getD_right ops g hgOps, hLen, hPath]
      exact ⟨hOpen.2, hOpen.1⟩
    · apply stageLayersBound_of_sweeps authPath stageIdx restOps roots (baseLayer + 1) (groups / 2)
      · intro k g
        have hAdd : (baseLayer + 1) + k = baseLayer + (k + 1) := by omega
        rw [hAdd]
        exact hAuth (k + 1) g
      · exact hTail

private theorem lookupStageOpenings_of_nodup :
    ∀ (sdoms : List WhirStageDomain) (allOps : List (List (List FoldLayerOpening)))
      (pos : Nat) (sdom : WhirStageDomain) (stOps : List (List FoldLayerOpening)),
      (sdoms.map (·.stageIdx)).Nodup →
      sdoms[pos]? = some sdom →
      allOps[pos]? = some stOps →
      lookupStageOpenings sdoms allOps sdom.stageIdx = stOps
  | [], _, _, _, _, _, hd, _ => by cases hd
  | _ :: _, [], _, _, _, _, _, ha => by cases ha
  | sd :: sds, ops0 :: rest, 0, sdom, stOps, _, hd, ha => by
    cases hd; cases ha
    simp [lookupStageOpenings]
  | sd :: sds, ops0 :: rest, pos + 1, sdom, stOps, hNd, hd, ha => by
    obtain ⟨hNotMem, hNdTail⟩ := List.nodup_cons.mp hNd
    have hMem : sdom ∈ sds := List.mem_of_getElem? hd
    have hNe : sd.stageIdx ≠ sdom.stageIdx := fun hEq =>
      hNotMem (List.mem_map.mpr ⟨sdom, hMem, hEq.symm⟩)
    simp only [lookupStageOpenings, hNe, ↓reduceIte]
    exact lookupStageOpenings_of_nodup sds rest pos sdom stOps hNdTail hd ha

private theorem stagesBound_of_sweeps (authPath : Nat → Nat → Nat → List (List UInt8)) :
    ∀ (sdoms : List WhirStageDomain) (allOps : List (List (List FoldLayerOpening)))
      (sps : List WhirStageProof),
      (∀ (pos : Nat) (sdom : WhirStageDomain) (stOps : List (List FoldLayerOpening)),
        sdoms[pos]? = some sdom → allOps[pos]? = some stOps →
        ∀ layer g, authPath sdom.stageIdx layer g =
          ((stOps.getD layer []).getD g defaultFoldOpening).path) →
      verifyAllStageSweeps sdoms allOps sps = true →
      StagesBound authPath sdoms (allOps.map (fun stOps => stOps.map reconstructLayerTable)) sps
  | [], [], [], _, _ => trivial
  | [], _ :: _, _, _, h => absurd h Bool.false_ne_true
  | [], [], _ :: _, _, h => absurd h Bool.false_ne_true
  | _ :: _, [], _, _, h => absurd h Bool.false_ne_true
  | _ :: _, _ :: _, [], _, h => absurd h Bool.false_ne_true
  | sdom :: sdoms, stOps :: restOps, sp :: sps, hAuth, hSw => by
    rcases Bool.and_eq_true_iff.mp hSw with ⟨h12, hRest⟩
    rcases Bool.and_eq_true_iff.mp h12 with ⟨hNeDec, hLayers⟩
    have hNe : stOps ≠ [] := of_decide_eq_true hNeDec
    refine ⟨fun hMapNil => hNe (List.map_eq_nil_iff.mp hMapNil), ?_, ?_⟩
    · apply stageLayersBound_of_sweeps authPath sdom.stageIdx stOps (stageAllRoots sp)
        0 sdom.groups0
      · intro k g
        rw [Nat.zero_add]
        exact hAuth 0 sdom stOps rfl rfl k g
      · exact hLayers
    · exact stagesBound_of_sweeps authPath sdoms restOps sps
        (fun pos sd ops hd ha => hAuth (pos + 1) sd ops hd ha) hRest

/-- Every accepted `CommittedTableTranscript` satisfies `StagesBound` on its reconstructed view. -/
theorem reconstructSuccinctView_stagesBound (dom : WhirDomain) (proof : SuccinctAggregateProof)
    (tr : CommittedTableTranscript)
    (hTr : verifyCommittedTableTranscript dom proof tr = true) :
    StagesBound (reconstructSuccinctView dom tr).authPath dom.stages
      (reconstructSuccinctView dom tr).allTables proof.stages := by
  rcases Bool.and_eq_true_iff.mp hTr with ⟨h12, _⟩
  rcases Bool.and_eq_true_iff.mp h12 with ⟨hNdDec, hSweeps⟩
  have hNd : (dom.stages.map (·.stageIdx)).Nodup := of_decide_eq_true hNdDec
  refine stagesBound_of_sweeps (transcriptAuthPath dom tr) dom.stages tr.stageLayerOpenings
    proof.stages ?_ hSweeps
  intro pos sdom stOps hd ha layer g
  unfold transcriptAuthPath
  rw [lookupStageOpenings_of_nodup dom.stages tr.stageLayerOpenings pos sdom stOps hNd hd ha]

private theorem verifyAllStageSweeps_at :
    ∀ (sdoms : List WhirStageDomain) (allOps : List (List (List FoldLayerOpening)))
      (sps : List WhirStageProof) (pos : Nat) (sdom : WhirStageDomain) (sp : WhirStageProof),
      verifyAllStageSweeps sdoms allOps sps = true →
      sdoms[pos]? = some sdom →
      sps[pos]? = some sp →
      verifyStageLayerSweeps sdom.stageIdx 0 sdom.groups0 (allOps.getD pos [])
        (stageAllRoots sp) = true
  | [], _, _, _, _, _, _, hd, _ => by cases hd
  | _ :: _, [], _, _, _, _, h, _, _ => absurd h Bool.false_ne_true
  | _ :: _, _ :: _, [], _, _, _, h, _, _ => absurd h Bool.false_ne_true
  | sd :: _, stOps :: _, sp0 :: _, 0, sdom, sp, h, hd, hp => by
    cases hd; cases hp
    exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2
  | _ :: sds, _ :: restOps, _ :: sps, pos + 1, sdom, sp, h, hd, hp =>
    verifyAllStageSweeps_at sds restOps sps pos sdom sp (Bool.and_eq_true_iff.mp h).2 hd hp

private theorem verifyStageLayerSweeps_at (stageIdx : Nat) :
    ∀ (stOps : List (List FoldLayerOpening)) (roots : List (List UInt8))
      (baseLayer groups layer : Nat) (root : List UInt8),
      verifyStageLayerSweeps stageIdx baseLayer groups stOps roots = true →
      roots[layer]? = some root →
      verifyLayerSweep stageIdx (baseLayer + layer) (layerGroupsAt groups layer)
        root (stOps.getD layer []) = true
  | _, [], _, _, _, _, _, hr => by cases hr
  | [], _ :: _, _, _, _, _, h, _ => absurd h Bool.false_ne_true
  | _ :: _, _ :: _, baseLayer, groups, 0, root, h, hr => by
    cases hr
    rw [Nat.add_zero]
    exact (Bool.and_eq_true_iff.mp h).1
  | _ :: restOps, _ :: roots, baseLayer, groups, l + 1, root, h, hr => by
    have ih := verifyStageLayerSweeps_at stageIdx restOps roots (baseLayer + 1) (groups / 2)
      l root (Bool.and_eq_true_iff.mp h).2 hr
    have hAdd : (baseLayer + 1) + l = baseLayer + (l + 1) := by omega
    rw [← hAdd]
    exact ih

/-- Constructively cross-check one rewound opening against the base coset sweep: either the duet
    values agree with the reconstructed table, or `duetOpeningCollision` extracts a concrete
    `HashCollisionWitness pcsMerkleHash`. -/
def checkOneRewoundOpening (dom : WhirDomain) (proof : SuccinctAggregateProof)
    (tr : CommittedTableTranscript) (ro : RewoundDuetOpening)
    (hSweeps : verifyAllStageSweeps dom.stages tr.stageLayerOpenings proof.stages = true)
    (hRo : verifyRewoundOpening dom proof ro = true) :
    let sweepOp := ((tr.stageLayerOpenings.getD ro.stagePos []).getD ro.layer []).getD
      ro.cosetIdx defaultFoldOpening
    PSum (PLift (ro.opening.v0 = sweepOp.v0 ∧ ro.opening.v1 = sweepOp.v1))
      (HashCollisionWitness pcsMerkleHash) :=
  let sweepOp := ((tr.stageLayerOpenings.getD ro.stagePos []).getD ro.layer []).getD
    ro.cosetIdx defaultFoldOpening
  if hEq : ro.opening.v0 = sweepOp.v0 ∧ ro.opening.v1 = sweepOp.v1 then
    .inl ⟨hEq⟩
  else
    match hd : dom.stages[ro.stagePos]?, hp : proof.stages[ro.stagePos]? with
    | none, _ => by simp [verifyRewoundOpening, hd] at hRo
    | some _, none => by simp [verifyRewoundOpening, hd, hp] at hRo
    | some sdom, some sp =>
      match hr : (stageAllRoots sp)[ro.layer]? with
      | none => by simp [verifyRewoundOpening, hd, hp, hr] at hRo
      | some root =>
        have hRo' : ro.cosetIdx < layerGroupsAt sdom.groups0 ro.layer ∧
            verifyDuetCosetOpening sdom.stageIdx ro.layer
              (layerGroupsAt sdom.groups0 ro.layer) root ro.cosetIdx ro.opening = true := by
          have h0 : (decide (ro.cosetIdx < layerGroupsAt sdom.groups0 ro.layer) &&
              verifyDuetCosetOpening sdom.stageIdx ro.layer
                (layerGroupsAt sdom.groups0 ro.layer) root ro.cosetIdx ro.opening) = true := by
            simpa [verifyRewoundOpening, hd, hp, hr] using hRo
          exact ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp h0).1, (Bool.and_eq_true_iff.mp h0).2⟩
        have hStSw := verifyAllStageSweeps_at dom.stages tr.stageLayerOpenings proof.stages
          ro.stagePos sdom sp hSweeps hd hp
        have hLaySw : verifyLayerSweep sdom.stageIdx ro.layer
            (layerGroupsAt sdom.groups0 ro.layer) root
            ((tr.stageLayerOpenings.getD ro.stagePos []).getD ro.layer []) = true := by
          simpa only [Nat.zero_add] using
            verifyStageLayerSweeps_at sdom.stageIdx _ (stageAllRoots sp) 0 sdom.groups0
              ro.layer root hStSw hr
        have hSwOpen := verifyDuetCosetOpening_facts
          ((verifyLayerSweep_at hLaySw).2 ro.cosetIdx hRo'.1)
        have hRoOpen := verifyDuetCosetOpening_facts hRo'.2
        .inr (duetOpeningCollision sdom.stageIdx ro.layer ro.cosetIdx
          ro.opening.v0 ro.opening.v1 sweepOp.v0 sweepOp.v1
          ro.opening.path sweepOp.path root hEq
          (hRoOpen.1.trans hSwOpen.1.symm) hRoOpen.2 hSwOpen.2)

def checkRewoundOpeningsList (dom : WhirDomain) (proof : SuccinctAggregateProof)
    (tr : CommittedTableTranscript)
    (hSweeps : verifyAllStageSweeps dom.stages tr.stageLayerOpenings proof.stages = true) :
    (ros : List RewoundDuetOpening) →
    ros.all (verifyRewoundOpening dom proof) = true →
    PSum
      (PLift (∀ ro ∈ ros,
        let sweepOp := ((tr.stageLayerOpenings.getD ro.stagePos []).getD ro.layer []).getD
          ro.cosetIdx defaultFoldOpening
        ro.opening.v0 = sweepOp.v0 ∧ ro.opening.v1 = sweepOp.v1))
      (HashCollisionWitness pcsMerkleHash)
  | [], _ => .inl ⟨fun _ h => by cases h⟩
  | ro :: ros, hAll =>
    have hSplit := Bool.and_eq_true_iff.mp hAll
    match checkOneRewoundOpening dom proof tr ro hSweeps hSplit.1 with
    | .inr col => .inr col
    | .inl ⟨hHead⟩ =>
      match checkRewoundOpeningsList dom proof tr hSweeps ros hSplit.2 with
      | .inr col => .inr col
      | .inl ⟨hTail⟩ => .inl ⟨fun ro' hMem => by
          rcases List.mem_cons.mp hMem with rfl | hRest
          · exact hHead
          · exact hTail ro' hRest⟩

/-- **Constructive Prover-Transcript `HemShardEnv` Extractor (`extractShardEnvFromTranscript`,
    `0 Classical.choice`)**:
    Given an accepted `CommittedTableTranscript` for shard `t`, reconstructs the committed stage
    tables and authentication paths, cross-checks all rewound openings against the sweep tables,
    and returns either a verified `HemShardEnv arith dom` (with proved `StagesBound`) or a
    concrete `HashCollisionWitness pcsMerkleHash`. -/
def extractShardEnvFromTranscript (arith : RowArithmetization) (dom : WhirDomain)
    (t : ShardProverTranscript arith dom)
    (hTr : verifyCommittedTableTranscript dom t.shard.proof t.transcript = true) :
    PSum (HemShardEnv arith dom) (HashCollisionWitness pcsMerkleHash) :=
  have hSweeps : verifyAllStageSweeps dom.stages t.transcript.stageLayerOpenings
      t.shard.proof.stages = true :=
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hTr).1).2
  have hRew : t.transcript.rewoundOpenings.all (verifyRewoundOpening dom t.shard.proof) = true :=
    (Bool.and_eq_true_iff.mp hTr).2
  match checkRewoundOpeningsList dom t.shard.proof t.transcript hSweeps
      t.transcript.rewoundOpenings hRew with
  | .inr col => .inr col
  | .inl _ =>
    .inl { shard := t.shard
           law := t.law
           view := reconstructSuccinctView dom t.transcript
           bound := reconstructSuccinctView_stagesBound dom t.shard.proof t.transcript hTr }

theorem extractShardEnvFromTranscript_inl_eq {arith : RowArithmetization} {dom : WhirDomain}
    {t : ShardProverTranscript arith dom}
    {hTr : verifyCommittedTableTranscript dom t.shard.proof t.transcript = true}
    {env : HemShardEnv arith dom}
    (h : extractShardEnvFromTranscript arith dom t hTr = .inl env) :
    env.shard = t.shard ∧ env.view = reconstructSuccinctView dom t.transcript := by
  unfold extractShardEnvFromTranscript at h
  dsimp only at h
  split at h
  · cases h
  · cases h; exact ⟨rfl, rfl⟩

/-- `#tooth` Equivocation sensitivity of `extractShardEnvFromTranscript`: if an accepted prover
    transcript contains any rewound opening `ro ∈ t.transcript.rewoundOpenings` whose duet pair
    `(v0, v1)` differs from the base coset-sweep opening at `(ro.stagePos, ro.layer, ro.cosetIdx)`,
    `extractShardEnvFromTranscript` cannot return `.inl` and constructively extracts a
    `HashCollisionWitness pcsMerkleHash`. -/
theorem extractShardEnvFromTranscript_equivocation_extracts_collision
    (arith : RowArithmetization) (dom : WhirDomain)
    (t : ShardProverTranscript arith dom)
    (hTr : verifyCommittedTableTranscript dom t.shard.proof t.transcript = true)
    (ro : RewoundDuetOpening) (hMem : ro ∈ t.transcript.rewoundOpenings)
    (hDisagree : ¬ (ro.opening.v0 =
        (((t.transcript.stageLayerOpenings.getD ro.stagePos []).getD ro.layer []).getD
          ro.cosetIdx defaultFoldOpening).v0 ∧
      ro.opening.v1 =
        (((t.transcript.stageLayerOpenings.getD ro.stagePos []).getD ro.layer []).getD
          ro.cosetIdx defaultFoldOpening).v1)) :
    ∃ col : HashCollisionWitness pcsMerkleHash,
      extractShardEnvFromTranscript arith dom t hTr = .inr col := by
  unfold extractShardEnvFromTranscript
  dsimp only
  generalize hChk : checkRewoundOpeningsList dom t.shard.proof t.transcript _
    t.transcript.rewoundOpenings _ = res
  cases res with
  | inr col => exact ⟨col, rfl⟩
  | inl hall => exact False.elim (hDisagree (hall.down ro hMem))

/-- Canonical honest-prover transcript builder converting any `StagesBound` view into a
    `CommittedTableTranscript` (`rewoundOpenings = []`). -/
def mapCosetsAux {α : Type} (f : Nat → α) : Nat → Nat → List α
  | _, 0 => []
  | base, k + 1 => f base :: mapCosetsAux f (base + 1) k

def buildLayerOpeningsFromTable (authPath : Nat → Nat → Nat → List (List UInt8))
    (stageIdx : Nat) : Nat → Nat → List (List GoldilocksExt4) → List (List FoldLayerOpening)
  | _, _, [] => []
  | layer, groups, w :: ws =>
    mapCosetsAux
      (fun g => { v0 := w.getD g CommRingOps.zero
                  v1 := w.getD (g + groups) CommRingOps.zero
                  path := authPath stageIdx layer g }) 0 groups ::
      buildLayerOpeningsFromTable authPath stageIdx (layer + 1) (groups / 2) ws

def buildStageOpeningsFromView (authPath : Nat → Nat → Nat → List (List UInt8)) :
    List WhirStageDomain → List (List (List GoldilocksExt4)) →
      List (List (List FoldLayerOpening))
  | sdom :: sdoms, stTables :: restTables =>
    buildLayerOpeningsFromTable authPath sdom.stageIdx 0 sdom.groups0 stTables ::
      buildStageOpeningsFromView authPath sdoms restTables
  | _, _ => []

def transcriptOfBoundView (dom : WhirDomain) (view : SuccinctExtractionView) :
    CommittedTableTranscript where
  stageLayerOpenings := buildStageOpeningsFromView view.authPath dom.stages view.allTables
  rewoundOpenings := []

private theorem mapCosetsAux_length {α : Type} (f : Nat → α) :
    ∀ (base k : Nat), (mapCosetsAux f base k).length = k
  | _, 0 => rfl
  | base, k + 1 => congrArg Nat.succ (mapCosetsAux_length f (base + 1) k)

private theorem verifyLayerSweepAux_mapCosetsAux (stageIdx layer groups : Nat) (root : List UInt8)
    (f : Nat → FoldLayerOpening) :
    ∀ (base k : Nat),
      (∀ g, base ≤ g → g < base + k → verifyDuetCosetOpening stageIdx layer groups root g (f g) = true) →
      verifyLayerSweepAux stageIdx layer groups root base (mapCosetsAux f base k) = true
  | _, 0, _ => rfl
  | base, k + 1, h => by
    simp only [mapCosetsAux, verifyLayerSweepAux, Bool.and_eq_true]
    refine ⟨h base (Nat.le_refl _) (by omega),
      verifyLayerSweepAux_mapCosetsAux stageIdx layer groups root f (base + 1) k
        (fun g hge hlt => h g (by omega) (by omega))⟩

private theorem verifyStageLayerSweeps_buildLayerOpenings
    (authPath : Nat → Nat → Nat → List (List UInt8)) (stageIdx : Nat) :
    ∀ (stTables : List (List GoldilocksExt4)) (roots : List (List UInt8)) (layer groups : Nat),
      StageLayersBound authPath stageIdx layer groups stTables roots →
      verifyStageLayerSweeps stageIdx layer groups
        (buildLayerOpeningsFromTable authPath stageIdx layer groups stTables) roots = true
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, hB => False.elim hB
  | _ :: _, [], _, _, hB => False.elim hB
  | w :: ws, root :: roots, layer, groups, hB => by
    simp only [buildLayerOpeningsFromTable, verifyStageLayerSweeps, verifyLayerSweep,
      Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨mapCosetsAux_length _ 0 groups, ?_⟩,
      verifyStageLayerSweeps_buildLayerOpenings authPath stageIdx ws roots (layer + 1) (groups / 2) hB.2⟩
    apply verifyLayerSweepAux_mapCosetsAux
    intro g _ hg
    have hOpen := hB.1 g (by omega)
    simp only [verifyDuetCosetOpening, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hOpen.2, hOpen.1⟩

private theorem verifyAllStageSweeps_buildStageOpenings
    (authPath : Nat → Nat → Nat → List (List UInt8)) :
    ∀ (sdoms : List WhirStageDomain) (allTables : List (List (List GoldilocksExt4)))
      (sps : List WhirStageProof),
      StagesBound authPath sdoms allTables sps →
      verifyAllStageSweeps sdoms (buildStageOpeningsFromView authPath sdoms allTables) sps = true
  | [], [], [], _ => rfl
  | [], _ :: _, _, hB => False.elim hB
  | [], [], _ :: _, hB => False.elim hB
  | _ :: _, [], _, hB => False.elim hB
  | _ :: _, _ :: _, [], hB => False.elim hB
  | sdom :: sdoms, stTables :: restTables, sp :: sps, hB => by
    have hNe : buildLayerOpeningsFromTable authPath sdom.stageIdx 0 sdom.groups0 stTables ≠ [] := by
      cases stTables with
      | nil => exact False.elim (hB.1 rfl)
      | cons _ _ => simp [buildLayerOpeningsFromTable]
    simp only [buildStageOpeningsFromView, verifyAllStageSweeps, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hNe, verifyStageLayerSweeps_buildLayerOpenings authPath sdom.stageIdx stTables
      (stageAllRoots sp) 0 sdom.groups0 hB.2.1⟩,
      verifyAllStageSweeps_buildStageOpenings authPath sdoms restTables sps hB.2.2⟩

/-- Completeness of `transcriptOfBoundView`: every `StagesBound` view on a stage-distinct `WhirDomain`
    produces a valid `CommittedTableTranscript` accepted by `verifyCommittedTableTranscript`. -/
theorem verifyCommittedTableTranscript_transcriptOfBoundView (dom : WhirDomain)
    (proof : SuccinctAggregateProof) (view : SuccinctExtractionView)
    (hNodup : (dom.stages.map (·.stageIdx)).Nodup)
    (hBound : StagesBound view.authPath dom.stages view.allTables proof.stages) :
    verifyCommittedTableTranscript dom proof (transcriptOfBoundView dom view) = true := by
  unfold verifyCommittedTableTranscript transcriptOfBoundView
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨hNodup, verifyAllStageSweeps_buildStageOpenings view.authPath dom.stages view.allTables
    proof.stages hBound⟩

private theorem layerOpeningsCount_eq_stageLayerQueryCost (stageIdx : Nat) :
    ∀ (stOps : List (List FoldLayerOpening)) (roots : List (List UInt8)) (layer groups : Nat),
      verifyStageLayerSweeps stageIdx layer groups stOps roots = true →
      layerOpeningsCount stOps = stageLayerQueryCost groups roots.length
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => absurd h Bool.false_ne_true
  | _ :: _, [], _, _, h => absurd h Bool.false_ne_true
  | ops :: restOps, _ :: roots, layer, groups, h => by
    obtain ⟨hHead, hTail⟩ := Bool.and_eq_true_iff.mp h
    have hLen := (verifyLayerSweep_at hHead).1
    have ih := layerOpeningsCount_eq_stageLayerQueryCost stageIdx restOps roots
      (layer + 1) (groups / 2) hTail
    simp only [layerOpeningsCount, List.length_cons, stageLayerQueryCost, hLen, ih]

private theorem verifyOneWhirStage_allRoots_len {rowChalls finalWord : List GoldilocksExt4}
    {prior : List UInt8} {sdom : WhirStageDomain} {sp : WhirStageProof}
    {nextInfo : Option (WhirStageDomain × List UInt8)}
    (h : verifyOneWhirStage rowChalls finalWord prior sdom sp nextInfo = true) :
    (stageAllRoots sp).length = sdom.foldLayers := by
  unfold verifyOneWhirStage at h
  dsimp only at h
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨h, _⟩
  rcases Bool.and_eq_true_iff.mp h with ⟨_, hRoots⟩
  exact of_decide_eq_true hRoots

private theorem sweepCount_eq_domainCost_aux {rowChalls finalWord : List GoldilocksExt4} :
    ∀ (prior : List UInt8) (sdoms : List WhirStageDomain)
      (allOps : List (List (List FoldLayerOpening))) (sps : List WhirStageProof),
      verifyWhirStages rowChalls finalWord prior sdoms sps = true →
      verifyAllStageSweeps sdoms allOps sps = true →
      allOps.foldr (fun stOps acc => layerOpeningsCount stOps + acc) 0 =
        sdoms.foldr (fun sdom acc => stageTranscriptQueryCost sdom + acc) 0
  | _, [], [], [], _, _ => rfl
  | _, [], _ :: _, _, _, hSw => absurd hSw Bool.false_ne_true
  | _, [], [], _ :: _, hVer, _ => absurd hVer Bool.false_ne_true
  | _, _ :: _, [], _, _, hSw => absurd hSw Bool.false_ne_true
  | _, _ :: _, _ :: _, [], _, hSw => absurd hSw Bool.false_ne_true
  | prior, [sdom], [stOps], [sp], hVer, hSw => by
    have hRootsLen := verifyOneWhirStage_allRoots_len hVer
    have hLay := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hSw).1).2
    have hEq := layerOpeningsCount_eq_stageLayerQueryCost sdom.stageIdx stOps (stageAllRoots sp)
      0 sdom.groups0 hLay
    simp only [List.foldr_cons, List.foldr_nil, stageTranscriptQueryCost, hEq, hRootsLen]
  | _, [_], _ :: _ :: _, [_], _, hSw =>
    absurd (Bool.and_eq_true_iff.mp hSw).2 Bool.false_ne_true
  | _, [_], _, _ :: _ :: _, hVer, _ => absurd hVer Bool.false_ne_true
  | _, _ :: _ :: _, _, [_], hVer, _ => absurd hVer Bool.false_ne_true
  | _, _ :: _ :: _, [_], _ :: _ :: _, _, hSw =>
    absurd (Bool.and_eq_true_iff.mp hSw).2 Bool.false_ne_true
  | prior, sdom :: nextDom :: restDoms, stOps :: nextOps :: restOps,
      sp :: nextSp :: restSps, hVer, hSw => by
    obtain ⟨hVer0, hVerRest⟩ := Bool.and_eq_true_iff.mp hVer
    rcases Bool.and_eq_true_iff.mp hSw with ⟨hSw0, hSwRest⟩
    have hRootsLen := verifyOneWhirStage_allRoots_len hVer0
    have hLay := (Bool.and_eq_true_iff.mp hSw0).2
    have hEq := layerOpeningsCount_eq_stageLayerQueryCost sdom.stageIdx stOps (stageAllRoots sp)
      0 sdom.groups0 hLay
    have ih := sweepCount_eq_domainCost_aux _ (nextDom :: restDoms) (nextOps :: restOps)
      (nextSp :: restSps) hVerRest hSwRest
    simp only [List.foldr_cons, stageTranscriptQueryCost, hEq, hRootsLen, ih]

theorem transcriptSweepOpeningCount_eq_domainQueryCost {arith : RowArithmetization}
    {dom : WhirDomain} {epochFloor msg : List UInt8}
    {t : ShardProverTranscript arith dom}
    (hShard : verifyHemShard arith dom epochFloor msg t.shard = true)
    (hTr : verifyCommittedTableTranscript dom t.shard.proof t.transcript = true) :
    transcriptSweepOpeningCount t.transcript = domainTranscriptQueryCost dom := by
  have hAcc := (verifyHemShard_facts hShard).2.2.2.2
  have hWhir := (succinct_acceptance_facts arith dom t.shard.inst t.shard.proof
    t.shard.fs hAcc).2.2.2.2.2.2
  have hSw := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hTr).1).2
  exact sweepCount_eq_domainCost_aux _ dom.stages t.transcript.stageLayerOpenings
    t.shard.proof.stages hWhir hSw

/-- **Exact Prover-Transcript Query Cost Accounting (`hierarchySweepOpeningCount_eq_queryCost`)**:
    across any list `trs` of accepted shard certificates and prover commitment transcripts, the
    total number of verified coset-sweep Merkle duet openings equals
    `hierarchyTranscriptQueryCost dom trs.length` (`= trs.length * domainTranscriptQueryCost dom`). -/
theorem hierarchySweepOpeningCount_eq_queryCost {arith : RowArithmetization}
    {dom : WhirDomain} {epochFloor msg : List UInt8} :
    ∀ (trs : List (ShardProverTranscript arith dom)),
      (∀ t ∈ trs, verifyHemShard arith dom epochFloor msg t.shard = true ∧
        verifyCommittedTableTranscript dom t.shard.proof t.transcript = true) →
      hierarchySweepOpeningCount trs = hierarchyTranscriptQueryCost dom trs.length
  | [], _ => by simp [hierarchySweepOpeningCount, hierarchyTranscriptQueryCost]
  | t :: rest, h => by
    have ht := h t (List.mem_cons_self ..)
    have hHead := transcriptSweepOpeningCount_eq_domainQueryCost ht.1 ht.2
    have ih := hierarchySweepOpeningCount_eq_queryCost rest
      (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))
    change transcriptSweepOpeningCount t.transcript + hierarchySweepOpeningCount rest =
      hierarchyTranscriptQueryCost dom (rest.length + 1)
    rw [hHead, ih, hierarchyTranscriptQueryCost, hierarchyTranscriptQueryCost,
        Nat.add_one_mul, Nat.add_comm]

/-- Shard-by-shard transcript conversion into `HemShardEnv`, preserving shards and reconstructed views. -/
def extractShardEnvsFromTranscripts (arith : RowArithmetization) (dom : WhirDomain) :
    (trs : List (ShardProverTranscript arith dom)) →
    (∀ t ∈ trs, verifyCommittedTableTranscript dom t.shard.proof t.transcript = true) →
    PSum { envs : List (HemShardEnv arith dom) //
        envs.map (·.shard) = trs.map (·.shard) ∧
        envs.length = trs.length ∧
        ∀ (i : Nat) (he : i < envs.length) (ht : i < trs.length),
          (envs[i]'he).shard = (trs[i]'ht).shard ∧
          (envs[i]'he).view = reconstructSuccinctView dom (trs[i]'ht).transcript }
      (Fin trs.length × HashCollisionWitness pcsMerkleHash)
  | [], _ => .inl ⟨[], rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | t :: ts, hTrs =>
    have ht0 := hTrs t (List.mem_cons_self ..)
    match hExt0 : extractShardEnvFromTranscript arith dom t ht0 with
    | .inr col => .inr ⟨⟨0, Nat.succ_pos _⟩, col⟩
    | .inl env0 =>
      have hEq0 := extractShardEnvFromTranscript_inl_eq hExt0
      match extractShardEnvsFromTranscripts arith dom ts
          (fun t' ht' => hTrs t' (List.mem_cons_of_mem _ ht')) with
      | .inr ⟨⟨j, hj⟩, col⟩ => .inr ⟨⟨j + 1, Nat.succ_lt_succ hj⟩, col⟩
      | .inl ⟨envsRest, hMap, hLen, hIdx⟩ =>
        .inl ⟨env0 :: envsRest, by
          refine ⟨by simp [hEq0.1, hMap], congrArg Nat.succ hLen, ?_⟩
          intro i he ht
          cases i with
          | zero => exact hEq0
          | succ k =>
            exact hIdx k (Nat.lt_of_succ_lt_succ he) (Nat.lt_of_succ_lt_succ ht)⟩

/-- Unified break outcome for transcript-grounded hierarchical extraction. -/
@[expose] def HemTranscriptHierarchyBreak (H : Hash) (arith : RowArithmetization)
    (dom : WhirDomain) (trs : List (ShardProverTranscript arith dom)) : Type :=
  PSum (HashCollisionWitness H)
    (Σ j : Fin trs.length,
      HemShardBreak arith dom (trs.get j).shard.proof
        (reconstructSuccinctView dom (trs.get j).transcript))

/-- **Transcript-Grounded Two-Layer Hierarchical Extractor (`extractHierarchicalHemFromTranscripts`,
    `0 Classical.choice`)**:
    Composes `extractShardEnvFromTranscript` with `extractHierarchicalHemQuorums` so hierarchical
    extraction is grounded directly in prover commitment-opening transcripts (`CommittedTableTranscript`)
    rather than externally assumed `StagesBound` proofs. -/
def extractHierarchicalHemFromTranscripts (H : Hash) (arith : RowArithmetization)
    (dom : WhirDomain) (registryDigest epochFloor msg : List UInt8)
    (registry : List ShardRegistration)
    (hReg : H (encodeRegistry registry) = registryDigest)
    (trs : List (ShardProverTranscript arith dom))
    (hTrs : ∀ t ∈ trs, verifyCommittedTableTranscript dom t.shard.proof t.transcript = true)
    (hAccept : verifyHierarchicalHem H arith dom registryDigest epochFloor msg
      (trs.map (·.shard)) = true) :
    PSum (HierarchicalQuorumWitness epochFloor msg registry (trs.map (·.shard)))
      (HemTranscriptHierarchyBreak H arith dom trs) :=
  match extractShardEnvsFromTranscripts arith dom trs hTrs with
  | .inr ⟨j, merkleCol⟩ => .inr (.inr ⟨j, .inr (.inl merkleCol)⟩)
  | .inl ⟨envs, hShards, hLen, hIdx⟩ =>
    have hAccEnvs : verifyHierarchicalHem H arith dom registryDigest epochFloor msg
        (envs.map (·.shard)) = true := by
      rwa [hShards]
    match extractHierarchicalHemQuorums H arith dom registryDigest epochFloor msg registry hReg
        envs hAccEnvs with
    | .inl w =>
      .inl ⟨w.sigs, hShards ▸ w.slots_eq, hShards ▸ w.weight_eq, hShards ▸ w.registry_eq⟩
    | .inr (.inl rootCol) => .inr (.inl rootCol)
    | .inr (.inr ⟨j, brk⟩) =>
      let j' : Fin trs.length := ⟨j.val, hLen ▸ j.isLt⟩
      have hPair := hIdx j.val j.isLt j'.isLt
      have hProofEq : (envs.get j).shard.proof = (trs.get j').shard.proof :=
        congrArg HemShardProof.proof hPair.1
      have hViewEq : (envs.get j).view = reconstructSuccinctView dom (trs.get j').transcript :=
        hPair.2
      .inr (.inr ⟨j', by rw [← hProofEq, ← hViewEq]; exact brk⟩)

theorem recursive_hem_transcript_knowledge_soundness (H : Hash) (arith : RowArithmetization)
    (dom : WhirDomain) (registryDigest epochFloor msg : List UInt8)
    (registry : List ShardRegistration) (hReg : H (encodeRegistry registry) = registryDigest)
    (trs : List (ShardProverTranscript arith dom))
    (hTrs : ∀ t ∈ trs, verifyCommittedTableTranscript dom t.shard.proof t.transcript = true)
    (hAccept : verifyHierarchicalHem H arith dom registryDigest epochFloor msg
      (trs.map (·.shard)) = true) :
    (∃ sigs : List (ExtractedQuorumSig epochFloor msg),
      sigs.map (·.slot) = hierarchicalActiveSlots (trs.map (·.shard)) ∧
      sigs.length = hierarchicalClaimedWeight (trs.map (·.shard)) ∧
      hierarchicalThresholdSum (trs.map (·.shard)) = registryThresholdSum registry ∧
      registryThresholdSum registry ≤ sigs.length ∧
      (sigs.map (·.slot.pk)).Nodup ∧
      (∀ r ∈ registry, r.WellFormed = true) ∧
      (trs.map (·.shard)).map HemShardProof.registration = registry) ∧
      hierarchySweepOpeningCount trs = hierarchyTranscriptQueryCost dom trs.length ∨
    Nonempty (HemTranscriptHierarchyBreak H arith dom trs) := by
  have hF := verifyHierarchicalHem_facts hAccept
  match extractHierarchicalHemFromTranscripts H arith dom registryDigest epochFloor msg registry
      hReg trs hTrs hAccept with
  | .inr brk => exact .inr ⟨brk⟩
  | .inl w =>
    have hSumEq :
        hierarchicalThresholdSum (trs.map (·.shard)) = registryThresholdSum registry := by
      rw [hierarchicalThresholdSum_eq_registryThresholdSum, w.registry_eq]
    have hCost : hierarchySweepOpeningCount trs = hierarchyTranscriptQueryCost dom trs.length :=
      hierarchySweepOpeningCount_eq_queryCost trs (fun t ht =>
        ⟨hF.2.2.2 t.shard (List.mem_map.mpr ⟨t, ht, rfl⟩), hTrs t ht⟩)
    refine .inl ⟨⟨w.sigs, w.slots_eq, w.weight_eq, hSumEq, ?_, ?_, ?_, w.registry_eq⟩, hCost⟩
    · rw [w.weight_eq, ← hSumEq]
      exact hierarchicalThresholdSum_le_claimedWeight _ hF.2.2.2
    · have hMap : w.sigs.map (·.slot.pk) = (w.sigs.map (·.slot)).map HemSlot.pk := by
        rw [List.map_map]; rfl
      rw [hMap, w.slots_eq]
      exact (hierarchicalActiveSlots_pk_sublist _).nodup hF.2.2.1
    · intro r hr
      rw [← w.registry_eq] at hr
      obtain ⟨s, hsMem, rfl⟩ := List.mem_map.mp hr
      exact verifyHemShard_wellFormed (hF.2.2.2 s hsMem)

/-! ### Union bound `ε_hier ≤ ε_root + Σ_j ε_shard(j)` over a finite coin space -/

def countTrue {Ω : Type} (p : Ω → Bool) : List Ω → Nat
  | [] => 0
  | ω :: rest => (if p ω then 1 else 0) + countTrue p rest

def sumOver : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | m + 1, f => sumOver m f + f m

private theorem sumOver_add (m : Nat) (f g : Nat → Nat) :
    sumOver m (fun j => f j + g j) = sumOver m f + sumOver m g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [sumOver, ih]
    omega

private theorem le_sumOver_of_lt (m : Nat) (f : Nat → Nat) (j : Nat) (hj : j < m) :
    f j ≤ sumOver m f := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [sumOver]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · have := ih hlt
      omega
    · omega

/-- Counting union bound: if every bad outcome of the hierarchy is a root-bad outcome or a
    shard-bad outcome for some `j < m`, the bad counts add up accordingly. Dividing by
    `coins.length` gives `ε_hier ≤ ε_root + Σ_{j < m} ε_shard(j)`. -/
theorem countTrue_union_bound {Ω : Type} (coins : List Ω) (m : Nat)
    (hierBad rootBad : Ω → Bool) (shardBad : Nat → Ω → Bool)
    (hCover : ∀ ω, hierBad ω = true →
      rootBad ω = true ∨ ∃ j, j < m ∧ shardBad j ω = true) :
    countTrue hierBad coins ≤
      countTrue rootBad coins + sumOver m (fun j => countTrue (shardBad j) coins) := by
  induction coins with
  | nil => exact Nat.zero_le _
  | cons ω rest ih =>
    have hs : sumOver m (fun j => countTrue (shardBad j) (ω :: rest)) =
        sumOver m (fun j => if shardBad j ω then 1 else 0) +
        sumOver m (fun j => countTrue (shardBad j) rest) := by
      rw [← sumOver_add]
      rfl
    have hstep : (if hierBad ω then 1 else 0) ≤
        (if rootBad ω then 1 else 0) + sumOver m (fun j => if shardBad j ω then 1 else 0) := by
      cases hb : hierBad ω with
      | false => exact Nat.zero_le _
      | true =>
        rcases hCover ω hb with hr | ⟨j, hj, hsj⟩
        · rw [hr]
          exact Nat.le_add_right _ _
        · have hle : (if shardBad j ω then 1 else 0) ≤
              sumOver m (fun j => if shardBad j ω then 1 else 0) :=
            le_sumOver_of_lt m (fun j => if shardBad j ω then 1 else 0) j hj
          rw [hsj] at hle
          exact Nat.le_trans hle (Nat.le_add_left _ _)
    rw [hs]
    simp only [countTrue]
    omega

/-- **Composed soundness error of the two-layer hierarchy
    (`hierarchical_hem_soundness_error_bound`)**: over a finite coin space, let `hierBad` mark
    coins where the root verifier accepts against the authenticated `registryDigest ω =
    H (encodeRegistry (registry ω))` although no `HierarchicalQuorumWitness` exists, let `rootBad`
    mark every coin whose run yields a concrete `HashCollisionWitness H`, and let `shardBad j` mark
    every coin whose run contains a single-layer break at shard `j`. Then
    `#hierBad ≤ #rootBad + Σ_{j < m} #shardBad j`. -/
theorem hierarchical_hem_soundness_error_bound {Ω : Type} (coins : List Ω) (m : Nat)
    (H : Hash) (arith : RowArithmetization) (dom : WhirDomain)
    (registryDigest epochFloor msg : Ω → List UInt8)
    (registry : Ω → List ShardRegistration)
    (envs : Ω → List (HemShardEnv arith dom))
    (hLen : ∀ ω, (envs ω).length ≤ m)
    (hierBad rootBad : Ω → Bool) (shardBad : Nat → Ω → Bool)
    (hHier : ∀ ω, hierBad ω = true →
      verifyHierarchicalHem H arith dom (registryDigest ω) (epochFloor ω) (msg ω)
        ((envs ω).map (·.shard)) = true ∧
      (HierarchicalQuorumWitness (epochFloor ω) (msg ω) (registry ω)
        ((envs ω).map (·.shard)) → False))
    (hRegAuth : ∀ ω, hierBad ω = true → H (encodeRegistry (registry ω)) = registryDigest ω)
    (hRoot : ∀ ω, HashCollisionWitness H → rootBad ω = true)
    (hShard : ∀ ω (j : Fin (envs ω).length),
      HemShardBreak arith dom ((envs ω).get j).shard.proof ((envs ω).get j).view →
      shardBad j.val ω = true) :
    countTrue hierBad coins ≤
      countTrue rootBad coins + sumOver m (fun j => countTrue (shardBad j) coins) := by
  apply countTrue_union_bound
  intro ω hb
  obtain ⟨hAcc, hNo⟩ := hHier ω hb
  have hF := verifyHierarchicalHem_facts hAcc
  if hEq : ((envs ω).map (·.shard)).map HemShardProof.registration = registry ω then
    match extractShardList arith dom (epochFloor ω) (msg ω) (envs ω)
        (fun e he => hF.2.2.2 e.shard (List.mem_map.mpr ⟨e, he, rfl⟩)) with
    | .inl ⟨sigs, hSlots, hWeight⟩ => exact (hNo ⟨sigs, hSlots, hWeight, hEq⟩).elim
    | .inr ⟨j, brk⟩ =>
      exact .inr ⟨j.val, Nat.lt_of_lt_of_le j.isLt (hLen ω), hShard ω j brk⟩
  else
    exact .inl (hRoot ω (registryCollision H hF.1 (hRegAuth ω hb) hEq))

/-- Transcript-grounded finite-coin union bound composing `extractHierarchicalHemFromTranscripts`
    with `countTrue_union_bound`. -/
theorem hierarchical_hem_transcript_soundness_error_bound {Ω : Type} (coins : List Ω) (m : Nat)
    (H : Hash) (arith : RowArithmetization) (dom : WhirDomain)
    (registryDigest epochFloor msg : Ω → List UInt8)
    (registry : Ω → List ShardRegistration)
    (trs : Ω → List (ShardProverTranscript arith dom))
    (hLen : ∀ ω, (trs ω).length ≤ m)
    (hierBad rootBad : Ω → Bool) (shardBad : Nat → Ω → Bool)
    (hHier : ∀ ω, hierBad ω = true →
      verifyHierarchicalHem H arith dom (registryDigest ω) (epochFloor ω) (msg ω)
        ((trs ω).map (·.shard)) = true ∧
      (∀ t ∈ trs ω, verifyCommittedTableTranscript dom t.shard.proof t.transcript = true) ∧
      (HierarchicalQuorumWitness (epochFloor ω) (msg ω) (registry ω)
        ((trs ω).map (·.shard)) → False))
    (hRegAuth : ∀ ω, hierBad ω = true → H (encodeRegistry (registry ω)) = registryDigest ω)
    (hRoot : ∀ ω, HashCollisionWitness H → rootBad ω = true)
    (hShard : ∀ ω (j : Fin (trs ω).length),
      HemShardBreak arith dom ((trs ω).get j).shard.proof
        (reconstructSuccinctView dom ((trs ω).get j).transcript) →
      shardBad j.val ω = true) :
    countTrue hierBad coins ≤
      countTrue rootBad coins + sumOver m (fun j => countTrue (shardBad j) coins) := by
  apply countTrue_union_bound
  intro ω hb
  obtain ⟨hAcc, hTrs, hNo⟩ := hHier ω hb
  match extractHierarchicalHemFromTranscripts H arith dom (registryDigest ω) (epochFloor ω)
      (msg ω) (registry ω) (hRegAuth ω hb) (trs ω) hTrs hAcc with
  | .inl w => exact (hNo w).elim
  | .inr (.inl col) => exact .inl (hRoot ω col)
  | .inr (.inr ⟨j, brk⟩) =>
    exact .inr ⟨j.val, Nat.lt_of_lt_of_le j.isLt (hLen ω), hShard ω j brk⟩

/-! ### `#tooth`: lowered shard threshold & unscoped shard replay refutations -/

/-- Constructive forged-threshold refutation (`0 Classical.choice`): if any shard `i` presents a
    threshold strictly below its registered threshold `(shards[i]).threshold < (registry[i]).threshold`
    under `registryDigest = H (encodeRegistry registry)`, then `verifyHemHierarchyAgainstRegistry`
    unconditionally rejects and either `verifyHierarchicalHem` rejects or `registryCollision`
    constructively extracts a `HashCollisionWitness H`. -/
def forgedLowerThreshold_rejected_or_collision (H : Hash)
    (arith : RowArithmetization) (dom : WhirDomain)
    (registryDigest epochFloor msg : List UInt8)
    (registry : List ShardRegistration)
    (hReg : H (encodeRegistry registry) = registryDigest)
    (shards : List HemShardProof)
    (i : Nat) (hiS : i < shards.length) (hiR : i < registry.length)
    (hLower : (shards[i]'hiS).threshold < (registry[i]'hiR).threshold) :
    PSum
      (PLift (verifyHierarchicalHem H arith dom registryDigest epochFloor msg shards = false ∧
        verifyHemHierarchyAgainstRegistry arith dom registry epochFloor msg shards = false))
      (HashCollisionWitness H) :=
  have hNe : shards.map HemShardProof.registration ≠ registry := fun hEq => by
    have hAt : (shards.map HemShardProof.registration)[i]? = registry[i]? :=
      congrArg (·[i]?) hEq
    rw [List.getElem?_map, List.getElem?_eq_getElem hiS, List.getElem?_eq_getElem hiR,
        Option.map_some, Option.some.injEq] at hAt
    have hThr : (shards[i]'hiS).threshold = (registry[i]'hiR).threshold :=
      congrArg ShardRegistration.threshold hAt
    omega
  have hDirectFalse :
      verifyHemHierarchyAgainstRegistry arith dom registry epochFloor msg shards = false := by
    unfold verifyHemHierarchyAgainstRegistry
    simp [decide_eq_false hNe]
  if hAcc : verifyHierarchicalHem H arith dom registryDigest epochFloor msg shards = true then
    .inr (registryCollision H (verifyHierarchicalHem_facts hAcc).1 hReg hNe)
  else
    .inl ⟨Bool.eq_false_iff.mpr hAcc, hDirectFalse⟩

/-- Root verifier with the shard-id and committee-disjointness checks removed. -/
def verifyHierarchicalHemUnscoped (arith : RowArithmetization) (dom : WhirDomain)
    (shards : List HemShardProof) : Bool :=
  shards.all fun s =>
    decide (1 ≤ s.threshold) &&
    decide (s.threshold ≤ s.inst.committee.length) &&
    decide (s.threshold ≤ bitmapPopcountSpec s.proof.agg.bitmap) &&
    verifySuccinctAggregate arith dom s.inst s.proof s.fs

private theorem hierarchicalClaimedWeight_replicate (s : HemShardProof) :
    ∀ m : Nat, hierarchicalClaimedWeight (List.replicate m s) =
      m * bitmapPopcountSpec s.proof.agg.bitmap
  | 0 => by simp [hierarchicalClaimedWeight]
  | m + 1 => by
    simp only [List.replicate_succ, hierarchicalClaimedWeight,
      hierarchicalClaimedWeight_replicate s m, Nat.succ_mul]
    omega

private theorem hierarchicalActiveSlots_replicate (s : HemShardProof) :
    ∀ (m : Nat) (q : HemSlot), q ∈ hierarchicalActiveSlots (List.replicate m s) →
      q ∈ shardActiveSlots s
  | 0, _, h => by simp [hierarchicalActiveSlots] at h
  | m + 1, q, h => by
    simp only [List.replicate_succ, hierarchicalActiveSlots, List.mem_append] at h
    rcases h with h | h
    · exact h
    · exact hierarchicalActiveSlots_replicate s m q h

private theorem hierarchicalShardIds_replicate (s : HemShardProof) :
    ∀ m : Nat, hierarchicalShardIds (List.replicate m s) = List.replicate m s.shardId
  | 0 => rfl
  | m + 1 => by
    simp only [List.replicate_succ, hierarchicalShardIds, hierarchicalShardIds_replicate s m]

/-- **Replay multiplication without shard scoping**: any shard certificate accepted by
    `verifyHemShard`, repeated `m ≥ 2` times, passes the unscoped root check with claimed weight
    `m` times the shard's weight and `m` times its threshold, although every active slot is one
    of the single shard's slots. `verifyHierarchicalHem` rejects the same list. -/
theorem tooth_unscoped_shard_id_allows_quorum_replay_multiplication (H : Hash)
    (arith : RowArithmetization) (dom : WhirDomain) (registryDigest epochFloor msg : List UInt8)
    (s : HemShardProof) (m : Nat) (hm : 2 ≤ m)
    (hs : verifyHemShard arith dom epochFloor msg s = true) :
    verifyHierarchicalHemUnscoped arith dom (List.replicate m s) = true ∧
    hierarchicalClaimedWeight (List.replicate m s) = m * bitmapPopcountSpec s.proof.agg.bitmap ∧
    m * s.threshold ≤ hierarchicalClaimedWeight (List.replicate m s) ∧
    (∀ q ∈ hierarchicalActiveSlots (List.replicate m s), q ∈ shardActiveSlots s) ∧
    verifyHierarchicalHem H arith dom registryDigest epochFloor msg (List.replicate m s)
      = false := by
  have hF := verifyHemShard_facts hs
  refine ⟨?_, hierarchicalClaimedWeight_replicate s m, ?_,
    hierarchicalActiveSlots_replicate s m, ?_⟩
  · unfold verifyHierarchicalHemUnscoped
    rw [List.all_eq_true]
    intro x hx
    rw [List.eq_of_mem_replicate hx]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨hF.2.1, hF.2.2.1⟩, hF.2.2.2.1⟩, hF.2.2.2.2⟩
  · rw [hierarchicalClaimedWeight_replicate]
    exact Nat.mul_le_mul_left m hF.2.2.2.1
  · apply Bool.eq_false_iff.mpr
    intro hAcc
    have hNodup := (verifyHierarchicalHem_facts hAcc).2.1
    rw [hierarchicalShardIds_replicate] at hNodup
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    simp [List.replicate_succ] at hNodup


/-! ## 7. Concrete accepting hierarchical certificates & prover transcripts -/

/-- Two distinct singleton committees use the same relation `x^7 = 0`, represented by
    `(seed, root) = (0, 0)` and `(1, 1)`. Both use the honest two-stage WHIR prover.
    This is an inhabitedness example for the field-based signature suite, not a security
    assertion about that suite. The threshold and the actual signer count are both one. -/
def concreteHemShard (second : Bool) : HemShardProof :=
  let seed := if second then Goldilocks.one else Goldilocks.zero
  let sid : List UInt8 := [if second then 1 else 0]
  let msg := shardBoundMessage sid [] []
  let bundle := buildHonestSbox7WhirBundle seed Goldilocks.zero Goldilocks.one msg
  { shardId := sid, threshold := 1, inst := rsSbox7Inst seed seed msg,
    proof := bundle.1, fs := bundle.2.1 }

def concreteHemArith : RowArithmetization := rsSbox7TraceArith Goldilocks.zero Goldilocks.zero

def concreteHemRegistry : List ShardRegistration :=
  [concreteHemShard false, concreteHemShard true].map HemShardProof.registration

def concreteHemRegistryDigest : List UInt8 :=
  poseidon2Hash32 (encodeRegistry concreteHemRegistry)

private theorem concreteHemArith_eq_seed (second : Bool) :
    let seed := if second then Goldilocks.one else Goldilocks.zero
    rsSbox7TraceArith seed (CommRingOps.add (pow7Goldilocks Goldilocks.zero) seed) =
      concreteHemArith := by
  cases second <;>
    (dsimp only [concreteHemArith, rsSbox7TraceArith]
     congr 1)

private theorem concreteSeedRoot_eq (second : Bool) :
    let seed := if second then Goldilocks.one else Goldilocks.zero
    CommRingOps.add (pow7Goldilocks Goldilocks.zero) seed = seed := by
  cases second <;> decide

theorem concreteHemShard_accepts (second : Bool) :
    verifyHemShard concreteHemArith rsSbox7WhirDomain [] [] (concreteHemShard second) = true := by
  have hAcc := (honestSbox7WhirProof_accepts
    (if second then Goldilocks.one else Goldilocks.zero)
    Goldilocks.zero Goldilocks.one
    (shardBoundMessage [if second then 1 else 0] [] [])).1
  rw [concreteHemArith_eq_seed second, concreteSeedRoot_eq second] at hAcc
  have c1 : decide ((concreteHemShard second).inst.message =
      shardBoundMessage (concreteHemShard second).shardId [] []) = true := by
    cases second <;> exact decide_eq_true rfl
  have c2 : decide (1 ≤ (concreteHemShard second).threshold) = true := by
    cases second <;> decide
  have c3 : decide ((concreteHemShard second).threshold ≤
      (concreteHemShard second).inst.committee.length) = true := by
    cases second <;> decide
  have c4 : decide ((concreteHemShard second).threshold ≤
      bitmapPopcountSpec (concreteHemShard second).proof.agg.bitmap) = true := by
    cases second <;> exact decide_eq_true (Nat.le_refl 1)
  unfold verifyHemShard
  rw [c1, c2, c3, c4]
  exact hAcc

theorem concreteHemShard_lawful (second : Bool) :
    concreteHemArith.Lawful rsSbox7WhirDomain (concreteHemShard second).inst := by
  cases second
  · exact rsSbox7TraceArith_lawful Goldilocks.zero Goldilocks.zero (shardBoundMessage [0] [] [])
  · have hLaw := rsSbox7TraceArith_lawful Goldilocks.one Goldilocks.one (shardBoundMessage [1] [] [])
    have hEq : rsSbox7TraceArith Goldilocks.one Goldilocks.one = concreteHemArith := by
      dsimp only [concreteHemArith, rsSbox7TraceArith]
      congr 1
    rwa [hEq] at hLaw

/-- Concrete prover commitment-opening transcript for `concreteHemShard second`. -/
def concreteHemShardTranscript (second : Bool) :
    ShardProverTranscript concreteHemArith rsSbox7WhirDomain :=
  let seed := if second then Goldilocks.one else Goldilocks.zero
  let sid : List UInt8 := [if second then 1 else 0]
  let msg := shardBoundMessage sid [] []
  let bundle := buildHonestSbox7WhirBundle seed Goldilocks.zero Goldilocks.one msg
  { shard := concreteHemShard second
    law := concreteHemShard_lawful second
    transcript := transcriptOfBoundView rsSbox7WhirDomain bundle.2.2 }

theorem concreteHemShardTranscript_accepts (second : Bool) :
    verifyCommittedTableTranscript rsSbox7WhirDomain (concreteHemShard second).proof
      (concreteHemShardTranscript second).transcript = true := by
  have hBound := (honestSbox7WhirProof_accepts
    (if second then Goldilocks.one else Goldilocks.zero)
    Goldilocks.zero Goldilocks.one
    (shardBoundMessage [if second then 1 else 0] [] [])).2
  have hNodup : (rsSbox7WhirDomain.stages.map (·.stageIdx)).Nodup := by decide
  exact verifyCommittedTableTranscript_transcriptOfBoundView rsSbox7WhirDomain _ _ hNodup hBound

/-- A root certificate with two distinct shard ids, two distinct public keys, and two active
    signers. Its registry commitment is computed by the deployed Poseidon2 hash. -/
theorem inhabited_verifyHierarchicalHem_two_shards :
    verifyHierarchicalHem poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
      concreteHemRegistryDigest [] [] [concreteHemShard false, concreteHemShard true] = true ∧
    verifyHemHierarchyAgainstRegistry concreteHemArith rsSbox7WhirDomain
      concreteHemRegistry [] [] [concreteHemShard false, concreteHemShard true] = true ∧
    hierarchicalClaimedWeight [concreteHemShard false, concreteHemShard true] = 2 ∧
    hierarchicalThresholdSum [concreteHemShard false, concreteHemShard true] = 2 ∧
    registryThresholdSum concreteHemRegistry = 2 := by
  have hIds : (hierarchicalShardIds [concreteHemShard false, concreteHemShard true]).Nodup := by
    decide
  have hKeys : (hierarchicalCommittee [concreteHemShard false, concreteHemShard true]).Nodup := by
    decide
  have hall : [concreteHemShard false, concreteHemShard true].all
      (verifyHemShard concreteHemArith rsSbox7WhirDomain [] []) = true := by
    simp only [List.all_cons, List.all_nil, concreteHemShard_accepts, Bool.and_self]
  have hWf : concreteHemRegistry.all ShardRegistration.WellFormed = true := by decide
  have hDig : decide (poseidon2Hash32 (encodeRegistry
      ([concreteHemShard false, concreteHemShard true].map HemShardProof.registration)) =
      concreteHemRegistryDigest) = true := decide_eq_true rfl
  have hRegEq : decide ([concreteHemShard false, concreteHemShard true].map
      HemShardProof.registration = concreteHemRegistry) = true := decide_eq_true rfl
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · unfold verifyHierarchicalHem
    rw [hDig, decide_eq_true hIds, decide_eq_true hKeys, hall]
    rfl
  · unfold verifyHemHierarchyAgainstRegistry
    rw [hWf, hRegEq, decide_eq_true hIds, decide_eq_true hKeys, hall]
    rfl

/-- End-to-end inhabitedness of transcript-grounded hierarchical extraction & query cost accounting:
    two concrete prover transcripts pass `verifyCommittedTableTranscript` with exact sweep cost
    `hierarchyTranscriptQueryCost rsSbox7WhirDomain 2 = 24`. -/
theorem inhabited_transcript_grounded_two_shards :
    let trs := [concreteHemShardTranscript false, concreteHemShardTranscript true]
    (∀ t ∈ trs, verifyCommittedTableTranscript rsSbox7WhirDomain t.shard.proof t.transcript = true) ∧
    verifyHierarchicalHem poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
      concreteHemRegistryDigest [] [] (trs.map (·.shard)) = true ∧
    hierarchySweepOpeningCount trs = 24 ∧
    hierarchyTranscriptQueryCost rsSbox7WhirDomain trs.length = 24 := by
  intro trs
  have hAllTr : ∀ t ∈ trs,
      verifyCommittedTableTranscript rsSbox7WhirDomain t.shard.proof t.transcript = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact concreteHemShardTranscript_accepts false
    · rcases List.mem_cons.mp ht' with rfl | hNil
      · exact concreteHemShardTranscript_accepts true
      · cases hNil
  have hVer : verifyHierarchicalHem poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
      concreteHemRegistryDigest [] [] (trs.map (·.shard)) = true :=
    inhabited_verifyHierarchicalHem_two_shards.1
  have hF := verifyHierarchicalHem_facts hVer
  have hCostEq : hierarchySweepOpeningCount trs =
      hierarchyTranscriptQueryCost rsSbox7WhirDomain trs.length :=
    hierarchySweepOpeningCount_eq_queryCost trs (fun t ht =>
      ⟨hF.2.2.2 t.shard (List.mem_map.mpr ⟨t, ht, rfl⟩), hAllTr t ht⟩)
  have hQuery24 : hierarchyTranscriptQueryCost rsSbox7WhirDomain trs.length = 24 := by decide
  exact ⟨hAllTr, hVer, hCostEq.trans hQuery24, hQuery24⟩

/-- Kernel-reducible UTF-8 bytes of `"QSAG.PQ.SUITE.SBOX7/v1"` for concrete Poseidon2 evaluation. -/
def concretePoseidonSuiteTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2e, 0x50, 0x51, 0x2e, 0x53, 0x55, 0x49, 0x54,
   0x45, 0x2e, 0x53, 0x42, 0x4f, 0x58, 0x37, 0x2f, 0x76, 0x31]

def concreteTwoKeyCommittee : List PqPublicKey :=
  [mkSbox7Pk Goldilocks.zero Goldilocks.zero, mkSbox7Pk Goldilocks.one Goldilocks.one]

def concreteTwoKeyRegistry : List ShardRegistration :=
  [{ shardId := [0]
     threshold := 2
     suiteId := concretePoseidonSuiteTag
     params := sbox7Params
     committee := concreteTwoKeyCommittee }]

def concreteTwoKeyRegistryDigest : List UInt8 :=
  poseidon2Hash32 (encodeRegistry concreteTwoKeyRegistry)

def concreteLoweredTwoKeyShard : HemShardProof :=
  let base := concreteHemShard false
  { shardId := [0]
    threshold := 1
    inst := { rsSbox7Inst Goldilocks.zero Goldilocks.zero (shardBoundMessage [0] [] []) with
              suite := { sbox7FieldSuite with suiteId := concretePoseidonSuiteTag }
              committee := concreteTwoKeyCommittee }
    proof := base.proof
    fs := base.fs }

set_option maxRecDepth 16384 in
/-- `#tooth` **Forged Lower Shard Threshold Rejected (`tooth_forged_lower_shard_threshold_rejected`)**:
    (a) **General security refutation**: for any hash `H`, registered policy `registry`, and
        submitted `shards`, if shard `i` lowers `threshold < (registry[i]).threshold` under an
        unchanged `registryDigest = H (encodeRegistry registry)`, then
        `verifyHemHierarchyAgainstRegistry` unconditionally returns `false`, and either
        `verifyHierarchicalHem` returns `false` or `forgedLowerThreshold_rejected_or_collision`
        constructively extracts a `HashCollisionWitness H`.
    (b) **Concrete `poseidon2Hash32` witnesses**:
        1. Lowering shard `0`'s threshold from `1` to `0` on the accepted two-shard Poseidon2
           hierarchy flips `verifyHierarchicalHem` from `true` to `false`.
        2. Lowering a 2-key committee's threshold from `2` to `1` (while keeping `1 ≤ 1 ≤ 2`
           well-formed and keeping `shardId`, `suiteId`, `params`, and `committee` identical)
           changes the concrete `poseidon2Hash32` registry digest and causes
           `verifyHierarchicalHem` to evaluate to `false`. -/
theorem tooth_forged_lower_shard_threshold_rejected :
    (∀ (H : Hash) (arith : RowArithmetization) (dom : WhirDomain)
       (registryDigest epochFloor msg : List UInt8) (registry : List ShardRegistration)
       (_hReg : H (encodeRegistry registry) = registryDigest)
       (shards : List HemShardProof) (i : Nat)
       (hiS : i < shards.length) (hiR : i < registry.length),
      (shards[i]'hiS).threshold < (registry[i]'hiR).threshold →
      verifyHemHierarchyAgainstRegistry arith dom registry epochFloor msg shards = false ∧
      (verifyHierarchicalHem H arith dom registryDigest epochFloor msg shards = false ∨
       Nonempty (HashCollisionWitness H))) ∧
    verifyHierarchicalHem poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
      concreteHemRegistryDigest [] []
      [{ concreteHemShard false with threshold := 0 }, concreteHemShard true] = false ∧
    concreteLoweredTwoKeyShard.registration.WellFormed = true ∧
    poseidon2Hash32 (encodeRegistry [concreteLoweredTwoKeyShard.registration]) ≠
      concreteTwoKeyRegistryDigest ∧
    verifyHierarchicalHem poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
      concreteTwoKeyRegistryDigest [] [] [concreteLoweredTwoKeyShard] = false := by
  have hDigNe :
      poseidon2Hash32 (encodeRegistry [concreteLoweredTwoKeyShard.registration]) ≠
        concreteTwoKeyRegistryDigest := by
    unfold concreteTwoKeyRegistryDigest
    decide
  refine ⟨?_, ?_, by decide, hDigNe, ?_⟩
  · intro H arith dom registryDigest epochFloor msg registry hReg shards i hiS hiR hLower
    match forgedLowerThreshold_rejected_or_collision H arith dom registryDigest epochFloor msg
        registry hReg shards i hiS hiR hLower with
    | .inl ⟨hHierFalse, hDirectFalse⟩ => exact ⟨hDirectFalse, .inl hHierFalse⟩
    | .inr col =>
      have hNe : shards.map HemShardProof.registration ≠ registry := fun hEq => by
        have hAt : (shards.map HemShardProof.registration)[i]? = registry[i]? :=
          congrArg (·[i]?) hEq
        rw [List.getElem?_map, List.getElem?_eq_getElem hiS, List.getElem?_eq_getElem hiR,
            Option.map_some, Option.some.injEq] at hAt
        have hThr : (shards[i]'hiS).threshold = (registry[i]'hiR).threshold :=
          congrArg ShardRegistration.threshold hAt
        exact absurd (hThr ▸ hLower) (Nat.lt_irrefl _)
      refine ⟨?_, .inr ⟨col⟩⟩
      unfold verifyHemHierarchyAgainstRegistry
      simp [decide_eq_false hNe]
  · apply Bool.eq_false_iff.mpr
    intro hAcc
    have hAll := (verifyHierarchicalHem_facts hAcc).2.2.2
    have h0 := hAll { concreteHemShard false with threshold := 0 } (List.mem_cons_self ..)
    have hGe1 := (verifyHemShard_facts h0).2.1
    simp at hGe1
  · unfold verifyHierarchicalHem
    have hDigNeMap :
        poseidon2Hash32 (encodeRegistry ([concreteLoweredTwoKeyShard].map
          HemShardProof.registration)) ≠ concreteTwoKeyRegistryDigest := hDigNe
    rw [decide_eq_false hDigNeMap]
    rfl

/-- Unconditional replay: the same actual accepting one-signer certificate is counted twice
    by the unscoped verifier, while the scoped root rejects it. No accepted-shard premise. -/
theorem tooth_concrete_unscoped_shard_replay :
    verifyHierarchicalHemUnscoped concreteHemArith rsSbox7WhirDomain
      [concreteHemShard false, concreteHemShard false] = true ∧
    hierarchicalClaimedWeight [concreteHemShard false, concreteHemShard false] = 2 ∧
    bitmapPopcountSpec (concreteHemShard false).proof.agg.bitmap = 1 ∧
    (∀ q ∈ hierarchicalActiveSlots [concreteHemShard false, concreteHemShard false],
      q ∈ shardActiveSlots (concreteHemShard false)) ∧
    verifyHierarchicalHem poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
      concreteHemRegistryDigest [] [] [concreteHemShard false, concreteHemShard false] = false := by
  have h := tooth_unscoped_shard_id_allows_quorum_replay_multiplication
    poseidon2Hash32 concreteHemArith rsSbox7WhirDomain concreteHemRegistryDigest [] []
    (concreteHemShard false) 2 (by decide) (concreteHemShard_accepts false)
  exact ⟨h.1, rfl, rfl, h.2.2.2.1, h.2.2.2.2⟩

/-- Nonvacuity of the deployed-width interpolation-margin premise. -/
/-! ## 11. Succinct Outer Recursive `Hem` Aggregation (`bciksJohnsonQrom128`) & Soundness Composition -/

def hemOuterDomainTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2e, 0x48, 0x45, 0x4d, 0x2e, 0x4f, 0x55, 0x54, 0x45, 0x52, 0x2f, 0x76, 0x31]

/-- Compact shard header carried by a succinct outer `Hem` certificate (`O(1)` outer WHIR proof,
    shipping zero child `SuccinctAggregateProof` payloads). -/
structure ShardCompressedHeader where
  shardId : List UInt8
  threshold : Nat
  suiteId : List UInt8
  params : PqHashParams
  committee : List PqPublicKey
  bitmap : SignerBitmapSpec
  childProofDigest : List UInt8
  deriving DecidableEq

def ShardCompressedHeader.registration (h : ShardCompressedHeader) : ShardRegistration :=
  ⟨h.shardId, h.threshold, h.suiteId, h.params, h.committee⟩

def encodeBitmapBytes (bm : SignerBitmapSpec) : List UInt8 :=
  bm.map (fun b => if b then 1 else 0)

private theorem encodeBitmapBytes_injective {a b : SignerBitmapSpec}
    (h : encodeBitmapBytes a = encodeBitmapBytes b) : a = b :=
  map_inj_of_inj (fun x y hxy => by cases x <;> cases y <;> first | rfl | cases hxy) h

def encodeShardCompressedHeader (h : ShardCompressedHeader) : List UInt8 :=
  encodeMultiFrame [
    encodeRegistration h.registration,
    encodeBitmapBytes h.bitmap,
    h.childProofDigest
  ]

def encodeCompressedHeaderChain (hs : List ShardCompressedHeader) : List UInt8 :=
  encodeMultiFrame (hs.map encodeShardCompressedHeader)

theorem encodeShardCompressedHeader_injective {a b : ShardCompressedHeader}
    (h : encodeShardCompressedHeader a = encodeShardCompressedHeader b) : a = b := by
  have h0 := encodeMultiFrame_injective h
  obtain ⟨hReg, h1⟩ := List.cons.inj h0
  obtain ⟨hBm, h2⟩ := List.cons.inj h1
  obtain ⟨hDig, _⟩ := List.cons.inj h2
  have hr := encodeRegistration_injective hReg
  have hb := encodeBitmapBytes_injective hBm
  cases a; cases b
  unfold ShardCompressedHeader.registration at hr
  cases hr
  subst hb hDig
  rfl

theorem encodeCompressedHeaderChain_injective {a b : List ShardCompressedHeader}
    (h : encodeCompressedHeaderChain a = encodeCompressedHeaderChain b) : a = b :=
  map_inj_of_inj (fun _ _ => encodeShardCompressedHeader_injective) (encodeMultiFrame_injective h)

def succinctOuterBoundMessage (registryDigest epochFloor msg headerChainDigest : List UInt8) :
    List UInt8 :=
  encodeMultiFrame [hemOuterDomainTag, registryDigest, epochFloor, msg, headerChainDigest]

theorem succinctOuterBoundMessage_injective {r1 e1 m1 c1 r2 e2 m2 c2 : List UInt8}
    (h : succinctOuterBoundMessage r1 e1 m1 c1 = succinctOuterBoundMessage r2 e2 m2 c2) :
    r1 = r2 ∧ e1 = e2 ∧ m1 = m2 ∧ c1 = c2 := by
  have h0 := encodeMultiFrame_injective h
  simp only [List.cons.injEq, and_true, true_and] at h0
  exact h0

/-- Succinct outer recursive `Hem` certificate: `headers` carries only compact shard metadata and
    32-byte child digests, verified by ONE outer `bciksJohnsonQrom128` `SuccinctAggregateProof`. -/
structure SuccinctOuterHemCertificate where
  headers : List ShardCompressedHeader
  outerInst : AggPublicInstance
  outerProof : SuccinctAggregateProof
  outerFs : List UInt8

def headerCommitteeFlat : List ShardCompressedHeader → List PqPublicKey
  | [] => []
  | h :: rest => h.committee ++ headerCommitteeFlat rest

def headerClaimedWeight : List ShardCompressedHeader → Nat
  | [] => 0
  | h :: rest => bitmapPopcountSpec h.bitmap + headerClaimedWeight rest

def verifyHeaderQuorum (h : ShardCompressedHeader) : Bool :=
  decide (1 ≤ h.threshold) &&
  decide (h.threshold ≤ h.committee.length) &&
  decide (h.threshold ≤ bitmapPopcountSpec h.bitmap)

/-- Executable verifier for succinct outer recursive `Hem` aggregation, pinning the outer proof and
    instance to unconditional `.bciksJohnsonQrom128` and binding `encodeCompressedHeaderChain`. -/
def verifySuccinctRecursiveHem (H : Hash) (outerArith : RowArithmetization) (outerDom : WhirDomain)
    (registryDigest epochFloor msg : List UInt8) (cert : SuccinctOuterHemCertificate) : Bool :=
  decide (1 ≤ cert.headers.length) &&
  decide (H (encodeRegistry (cert.headers.map ShardCompressedHeader.registration)) = registryDigest) &&
  decide ((cert.headers.map (·.shardId)).Nodup) &&
  decide ((headerCommitteeFlat cert.headers).Nodup) &&
  cert.headers.all verifyHeaderQuorum &&
  decide (cert.outerInst.regime = .bciksJohnsonQrom128) &&
  decide (cert.outerProof.agg.regime = .bciksJohnsonQrom128) &&
  decide (cert.outerInst.message =
    succinctOuterBoundMessage registryDigest epochFloor msg
      (H (encodeCompressedHeaderChain cert.headers))) &&
  verifySuccinctAggregate outerArith outerDom cert.outerInst cert.outerProof cert.outerFs

def shardToCompressedHeader (digestProof : SuccinctAggregateProof → List UInt8)
    (s : HemShardProof) : ShardCompressedHeader :=
  { shardId := s.shardId
    threshold := s.threshold
    suiteId := s.inst.suite.suiteId
    params := s.inst.params
    committee := s.inst.committee
    bitmap := s.proof.agg.bitmap
    childProofDigest := digestProof s.proof }

/-- Extraction witness bundle for succinct outer recursive `Hem`: connects the outer `Hem` committed
    table to the `M` inner shard extraction environments verified by the outer relation. -/
structure SuccinctRecursiveHemEnv (H : Hash)
    (outerArith : RowArithmetization) (outerDom : WhirDomain)
    (innerArith : RowArithmetization) (innerDom : WhirDomain)
    (epochFloor msg : List UInt8)
    (cert : SuccinctOuterHemCertificate) where
  digestProof : SuccinctAggregateProof → List UInt8
  outerLaw : outerArith.Lawful outerDom cert.outerInst
  outerView : SuccinctExtractionView
  outerBound : StagesBound outerView.authPath outerDom.stages outerView.allTables cert.outerProof.stages
  innerEnvs : List (HemShardEnv innerArith innerDom)
  outerRelationSound :
    checkAllActiveSigners cert.outerInst.suite cert.outerInst.params cert.outerInst.message
      cert.outerInst.committee cert.outerProof.agg.bitmap
      (outerArith.decodeSigs ((outerView.allTables.headD []).headD [])) = true →
    (innerEnvs.map (fun e => shardToCompressedHeader digestProof e.shard) = cert.headers ∧
     ∀ e ∈ innerEnvs,
       e.shard.inst.message = shardBoundMessage e.shard.shardId epochFloor msg ∧
       verifySuccinctAggregate innerArith innerDom e.shard.inst e.shard.proof e.shard.fs = true)

private theorem verifySuccinctRecursiveHem_facts {H : Hash}
    {outerArith : RowArithmetization} {outerDom : WhirDomain}
    {registryDigest epochFloor msg : List UInt8} {cert : SuccinctOuterHemCertificate}
    (h : verifySuccinctRecursiveHem H outerArith outerDom registryDigest epochFloor msg cert = true) :
    1 ≤ cert.headers.length ∧
    H (encodeRegistry (cert.headers.map ShardCompressedHeader.registration)) = registryDigest ∧
    (cert.headers.map (·.shardId)).Nodup ∧
    (headerCommitteeFlat cert.headers).Nodup ∧
    (∀ hd ∈ cert.headers, verifyHeaderQuorum hd = true) ∧
    cert.outerInst.regime = .bciksJohnsonQrom128 ∧
    cert.outerProof.agg.regime = .bciksJohnsonQrom128 ∧
    cert.outerInst.message =
      succinctOuterBoundMessage registryDigest epochFloor msg
        (H (encodeCompressedHeaderChain cert.headers)) ∧
    verifySuccinctAggregate outerArith outerDom cert.outerInst cert.outerProof cert.outerFs = true := by
  unfold verifySuccinctRecursiveHem at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2,
    h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

private theorem map_reg_of_headers (dp : SuccinctAggregateProof → List UInt8) :
    ∀ shards : List HemShardProof,
      ((shards.map (shardToCompressedHeader dp)).map ShardCompressedHeader.registration) =
        shards.map HemShardProof.registration
  | [] => rfl
  | _ :: rest => congrArg (_ :: ·) (map_reg_of_headers dp rest)

private theorem map_sid_of_headers (dp : SuccinctAggregateProof → List UInt8) :
    ∀ shards : List HemShardProof,
      ((shards.map (shardToCompressedHeader dp)).map (·.shardId)) = hierarchicalShardIds shards
  | [] => rfl
  | _ :: rest => congrArg (_ :: ·) (map_sid_of_headers dp rest)

private theorem flat_com_of_headers (dp : SuccinctAggregateProof → List UInt8) :
    ∀ shards : List HemShardProof,
      headerCommitteeFlat (shards.map (shardToCompressedHeader dp)) = hierarchicalCommittee shards
  | [] => rfl
  | _ :: rest => congrArg (_ ++ ·) (flat_com_of_headers dp rest)

/-- Constructive (`0 Classical.choice`) recursive witness extractor composing the outer
    `bciksJohnsonQrom128` `Hem` extractor with the `M`-shard `extractHierarchicalHemQuorums` tree. -/
def extractSuccinctRecursiveHem (H : Hash)
    (outerArith : RowArithmetization) (outerDom : WhirDomain)
    (innerArith : RowArithmetization) (innerDom : WhirDomain)
    (registryDigest epochFloor msg : List UInt8)
    (registry : List ShardRegistration)
    (hReg : H (encodeRegistry registry) = registryDigest)
    (cert : SuccinctOuterHemCertificate)
    (env : SuccinctRecursiveHemEnv H outerArith outerDom innerArith innerDom epochFloor msg cert)
    (hAccept : verifySuccinctRecursiveHem H outerArith outerDom registryDigest epochFloor msg cert = true) :
    PSum (HierarchicalQuorumWitness epochFloor msg registry (env.innerEnvs.map (·.shard)))
      (PSum (HemShardBreak outerArith outerDom cert.outerProof env.outerView)
        (HemHierarchyBreak H innerArith innerDom env.innerEnvs)) :=
  have hF := verifySuccinctRecursiveHem_facts hAccept
  match succinct_aggregation_knowledge_soundness outerArith outerDom cert.outerInst env.outerLaw
      cert.outerProof cert.outerFs env.outerView hF.2.2.2.2.2.2.2.2 env.outerBound with
  | .inr outerBrk => .inr (.inl outerBrk)
  | .inl ⟨_, hOuterAct⟩ =>
    have hRel := env.outerRelationSound hOuterAct
    have hMapHdr : (env.innerEnvs.map (·.shard)).map (shardToCompressedHeader env.digestProof) =
        cert.headers := by
      rw [List.map_map]; exact hRel.1
    have hHierAcc :
        verifyHierarchicalHem H innerArith innerDom registryDigest epochFloor msg
          (env.innerEnvs.map (·.shard)) = true := by
      unfold verifyHierarchicalHem
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
      have hRegDig : H (encodeRegistry ((env.innerEnvs.map (·.shard)).map HemShardProof.registration)) =
          registryDigest := by
        rw [← map_reg_of_headers env.digestProof, hMapHdr]; exact hF.2.1
      have hSidNd : (hierarchicalShardIds (env.innerEnvs.map (·.shard))).Nodup := by
        rw [← map_sid_of_headers env.digestProof, hMapHdr]; exact hF.2.2.1
      have hComNd : (hierarchicalCommittee (env.innerEnvs.map (·.shard))).Nodup := by
        rw [← flat_com_of_headers env.digestProof, hMapHdr]; exact hF.2.2.2.1
      refine ⟨⟨⟨hRegDig, hSidNd⟩, hComNd⟩, ?_⟩
      intro s hsMem
      obtain ⟨e, heMem, rfl⟩ := List.mem_map.mp hsMem
      have hHdrMem : shardToCompressedHeader env.digestProof e.shard ∈ cert.headers := by
        rw [← hMapHdr]; exact List.mem_map.mpr ⟨e.shard, List.mem_map.mpr ⟨e, heMem, rfl⟩, rfl⟩
      have hQ := hF.2.2.2.2.1 _ hHdrMem
      unfold verifyHeaderQuorum at hQ
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hQ
      have hInner := hRel.2 e heMem
      unfold verifyHemShard
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨⟨hInner.1, hQ.1.1⟩, hQ.1.2⟩, hQ.2⟩, hInner.2⟩
    match extractHierarchicalHemQuorums H innerArith innerDom registryDigest epochFloor msg
        registry hReg env.innerEnvs hHierAcc with
    | .inl w => .inl w
    | .inr hierBrk => .inr (.inr hierBrk)

private theorem sumOver_const_le (m bound : Nat) (f : Nat → Nat)
    (hf : ∀ j, j < m → f j ≤ bound) :
    sumOver m f ≤ m * bound := by
  induction m with
  | zero => simp [sumOver]
  | succ m ih =>
    have ih' := ih (fun j hj => hf j (Nat.lt_succ_of_lt hj))
    have hm := hf m (Nat.lt_succ_self m)
    simp only [sumOver, Nat.succ_mul]
    omega

private theorem or_ite_le (a b : Bool) :
    (if (a || b) = true then 1 else 0) ≤ (if a = true then 1 else 0) + (if b = true then 1 else 0) := by
  cases a <;> cases b <;> decide

private theorem countTrue_or_le {α : Type} (f g : α → Bool) :
    ∀ xs : List α, countTrue (fun x => f x || g x) xs ≤ countTrue f xs + countTrue g xs
  | [] => Nat.zero_le 0
  | hd :: rest => by
    have ih := countTrue_or_le f g rest
    have hHd := or_ite_le (f hd) (g hd)
    simp only [countTrue]
    omega

/-- **Succinct Outer Recursive `Hem` Soundness Composition (`succinct_recursive_hem_soundness_composition`)**:
    Over any finite coin space `coins`, if `recBad ω` marks coins where `verifySuccinctRecursiveHem`
    accepts under `H (encodeRegistry (registry ω)) = registryDigest ω` without a valid
    `HierarchicalQuorumWitness` across all `M` shards, then:
    1. `countTrue recBad coins ≤ countTrue outerBad coins + countTrue colBad coins + Σ_{j < m} countTrue (shardBad j) coins`;
    2. When `countTrue outerBad coins ≤ epsOuter`, `countTrue colBad coins = 0` (collision-free transcript),
       and `∀ j < m, countTrue (shardBad j) coins ≤ epsHem`, total bad coins satisfy
       `countTrue recBad coins ≤ m * epsHem + epsOuter`! -/
theorem succinct_recursive_hem_soundness_composition {Ω : Type} (coins : List Ω) (m : Nat)
    (H : Hash) (outerArith : RowArithmetization) (outerDom : WhirDomain)
    (innerArith : RowArithmetization) (innerDom : WhirDomain)
    (registryDigest epochFloor msg : Ω → List UInt8)
    (registry : Ω → List ShardRegistration)
    (cert : Ω → SuccinctOuterHemCertificate)
    (env : (ω : Ω) → SuccinctRecursiveHemEnv H outerArith outerDom innerArith innerDom
      (epochFloor ω) (msg ω) (cert ω))
    (hLen : ∀ ω, (env ω).innerEnvs.length ≤ m)
    (recBad outerBad colBad : Ω → Bool) (shardBad : Nat → Ω → Bool)
    (hRec : ∀ ω, recBad ω = true →
      verifySuccinctRecursiveHem H outerArith outerDom (registryDigest ω) (epochFloor ω) (msg ω)
        (cert ω) = true ∧
      (HierarchicalQuorumWitness (epochFloor ω) (msg ω) (registry ω)
        ((env ω).innerEnvs.map (·.shard)) → False))
    (hRegAuth : ∀ ω, recBad ω = true → H (encodeRegistry (registry ω)) = registryDigest ω)
    (hOuter : ∀ ω, HemShardBreak outerArith outerDom (cert ω).outerProof (env ω).outerView →
      outerBad ω = true)
    (hCol : ∀ ω, HashCollisionWitness H → colBad ω = true)
    (hShard : ∀ ω (j : Fin (env ω).innerEnvs.length),
      HemShardBreak innerArith innerDom ((env ω).innerEnvs.get j).shard.proof
        ((env ω).innerEnvs.get j).view →
      shardBad j.val ω = true) :
    countTrue recBad coins ≤
      countTrue outerBad coins + countTrue colBad coins +
        sumOver m (fun j => countTrue (shardBad j) coins) ∧
    (∀ epsHem epsOuter : Nat,
      countTrue outerBad coins ≤ epsOuter →
      countTrue colBad coins = 0 →
      (∀ j, j < m → countTrue (shardBad j) coins ≤ epsHem) →
      countTrue recBad coins ≤ m * epsHem + epsOuter) := by
  let rootOrOuter : Ω → Bool := fun ω => outerBad ω || colBad ω
  have hUnion : countTrue recBad coins ≤
      countTrue rootOrOuter coins + sumOver m (fun j => countTrue (shardBad j) coins) := by
    apply countTrue_union_bound
    intro ω hb
    obtain ⟨hAcc, hNo⟩ := hRec ω hb
    match extractSuccinctRecursiveHem H outerArith outerDom innerArith innerDom
        (registryDigest ω) (epochFloor ω) (msg ω) (registry ω) (hRegAuth ω hb)
        (cert ω) (env ω) hAcc with
    | .inl w => exact (hNo w).elim
    | .inr (.inl oBrk) =>
      left
      dsimp only [rootOrOuter]
      rw [hOuter ω oBrk]
      rfl
    | .inr (.inr (.inl col)) =>
      left
      dsimp only [rootOrOuter]
      rw [hCol ω col, Bool.or_true]
    | .inr (.inr (.inr ⟨j, sBrk⟩)) =>
      exact .inr ⟨j.val, Nat.lt_of_lt_of_le j.isLt (hLen ω), hShard ω j sBrk⟩
  have hOrLe : countTrue rootOrOuter coins ≤ countTrue outerBad coins + countTrue colBad coins :=
    countTrue_or_le outerBad colBad coins
  have hMain : countTrue recBad coins ≤
      countTrue outerBad coins + countTrue colBad coins +
        sumOver m (fun j => countTrue (shardBad j) coins) := by omega
  refine ⟨hMain, ?_⟩
  intro epsHem epsOuter hO hC hS
  have hSum := sumOver_const_le m epsHem (fun j => countTrue (shardBad j) coins) hS
  omega

def concreteSuccinctOuterHeaders : List ShardCompressedHeader :=
  [concreteHemShard false, concreteHemShard true].map (shardToCompressedHeader (fun _ => [0x01]))

def concreteOuterMsg : List UInt8 :=
  succinctOuterBoundMessage concreteHemRegistryDigest [] []
    (poseidon2Hash32 (encodeCompressedHeaderChain concreteSuccinctOuterHeaders))

private def concreteOuterBundle :=
  buildHonestSbox7WhirBundle Goldilocks.zero Goldilocks.zero Goldilocks.one concreteOuterMsg

/-- Concrete accepting `SuccinctOuterHemCertificate` over the two `concreteHemShard` shards, using
    `poseidon2Hash32` and the honest `bciksJohnsonQrom128` WHIR prover. -/
def concreteSuccinctOuterCert : SuccinctOuterHemCertificate :=
  { headers := concreteSuccinctOuterHeaders
    outerInst := rsSbox7Inst Goldilocks.zero Goldilocks.zero concreteOuterMsg
    outerProof := concreteOuterBundle.1
    outerFs := concreteOuterBundle.2.1 }

theorem inhabited_verifySuccinctRecursiveHem :
    verifySuccinctRecursiveHem poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
      concreteHemRegistryDigest [] [] concreteSuccinctOuterCert = true ∧
    concreteSuccinctOuterCert.outerProof.agg.regime = .bciksJohnsonQrom128 := by
  have hIds : (concreteSuccinctOuterHeaders.map (·.shardId)).Nodup := by
    rw [concreteSuccinctOuterHeaders, map_sid_of_headers]
    decide
  have hCom : (headerCommitteeFlat concreteSuccinctOuterHeaders).Nodup := by
    rw [concreteSuccinctOuterHeaders, flat_com_of_headers]
    decide
  have hLen : 1 ≤ concreteSuccinctOuterHeaders.length :=
    Nat.le_succ 1
  have hHdrQ : ∀ second : Bool,
      verifyHeaderQuorum (shardToCompressedHeader (fun _ => [0x01]) (concreteHemShard second)) = true := by
    intro second
    have c1 : decide (1 ≤ (concreteHemShard second).threshold) = true := by
      cases second <;> decide
    have c2 : decide ((concreteHemShard second).threshold ≤
        (concreteHemShard second).inst.committee.length) = true := by
      cases second <;> decide
    have c3 : decide ((concreteHemShard second).threshold ≤
        bitmapPopcountSpec (concreteHemShard second).proof.agg.bitmap) = true := by
      cases second <;> exact decide_eq_true (Nat.le_refl 1)
    unfold verifyHeaderQuorum shardToCompressedHeader
    dsimp only
    rw [c1, c2, c3]
    rfl
  have hQ : concreteSuccinctOuterHeaders.all verifyHeaderQuorum = true := by
    unfold concreteSuccinctOuterHeaders
    simp only [List.map, List.all_cons, List.all_nil, hHdrQ, Bool.and_self]
  have hAcc : verifySuccinctAggregate concreteHemArith rsSbox7WhirDomain
      (rsSbox7Inst Goldilocks.zero Goldilocks.zero concreteOuterMsg)
      concreteOuterBundle.1 concreteOuterBundle.2.1 = true := by
    have hRaw := (honestSbox7WhirProof_accepts Goldilocks.zero Goldilocks.zero Goldilocks.one concreteOuterMsg).1
    have hz : CommRingOps.add (pow7Goldilocks Goldilocks.zero) Goldilocks.zero = Goldilocks.zero := by decide
    have hArithEq : rsSbox7TraceArith Goldilocks.zero
        (CommRingOps.add (pow7Goldilocks Goldilocks.zero) Goldilocks.zero) = concreteHemArith := by
      rw [hz]; rfl
    rw [hArithEq, hz] at hRaw
    exact hRaw
  have hMapReg : concreteSuccinctOuterHeaders.map ShardCompressedHeader.registration =
      concreteHemRegistry :=
    map_reg_of_headers (fun _ => [0x01]) [concreteHemShard false, concreteHemShard true]
  have hDig : decide (poseidon2Hash32 (encodeRegistry
      (concreteSuccinctOuterHeaders.map ShardCompressedHeader.registration)) =
      concreteHemRegistryDigest) = true := by
    rw [hMapReg]
    exact decide_eq_true rfl
  have hPrfReg : ∀ m : List UInt8,
      (buildHonestSbox7WhirBundle Goldilocks.zero Goldilocks.zero Goldilocks.one m).1.agg.regime =
        .bciksJohnsonQrom128 := fun _ => rfl
  have hRegEq : concreteSuccinctOuterCert.outerProof.agg.regime = .bciksJohnsonQrom128 :=
    hPrfReg concreteOuterMsg
  have hInstReg : decide ((rsSbox7Inst Goldilocks.zero Goldilocks.zero concreteOuterMsg).regime =
      .bciksJohnsonQrom128) = true :=
    decide_eq_true rfl
  have hPrfRegDec : decide (concreteOuterBundle.1.agg.regime = .bciksJohnsonQrom128) = true :=
    decide_eq_true (hPrfReg concreteOuterMsg)
  have hMsgEq : decide ((rsSbox7Inst Goldilocks.zero Goldilocks.zero concreteOuterMsg).message =
      succinctOuterBoundMessage concreteHemRegistryDigest [] []
        (poseidon2Hash32 (encodeCompressedHeaderChain concreteSuccinctOuterHeaders))) = true :=
    decide_eq_true rfl
  refine ⟨?_, hRegEq⟩
  unfold verifySuccinctRecursiveHem
  change (decide (1 ≤ concreteSuccinctOuterHeaders.length) &&
    decide (poseidon2Hash32 (encodeRegistry (concreteSuccinctOuterHeaders.map ShardCompressedHeader.registration)) =
      concreteHemRegistryDigest) &&
    decide ((concreteSuccinctOuterHeaders.map (·.shardId)).Nodup) &&
    decide ((headerCommitteeFlat concreteSuccinctOuterHeaders).Nodup) &&
    concreteSuccinctOuterHeaders.all verifyHeaderQuorum &&
    decide ((rsSbox7Inst Goldilocks.zero Goldilocks.zero concreteOuterMsg).regime = .bciksJohnsonQrom128) &&
    decide (concreteOuterBundle.1.agg.regime = .bciksJohnsonQrom128) &&
    decide ((rsSbox7Inst Goldilocks.zero Goldilocks.zero concreteOuterMsg).message =
      succinctOuterBoundMessage concreteHemRegistryDigest [] []
        (poseidon2Hash32 (encodeCompressedHeaderChain concreteSuccinctOuterHeaders))) &&
    verifySuccinctAggregate concreteHemArith rsSbox7WhirDomain
      (rsSbox7Inst Goldilocks.zero Goldilocks.zero concreteOuterMsg)
      concreteOuterBundle.1 concreteOuterBundle.2.1) = true
  rw [decide_eq_true hLen, hDig, decide_eq_true hIds, decide_eq_true hCom, hQ,
      hInstReg, hPrfRegDec, hMsgEq, hAcc]
  rfl

/-- `#tooth` **Succinct Outer Recursive Regime Downgrade & Header-Chain Tamper Rejection**:
    1. Downgrading `outerInst.regime` to `.bciksJohnsonClassical128` causes `verifySuccinctRecursiveHem`
       to return `false`.
    2. Tampering `headers` to any `headers' ≠ cert.headers` on an accepting certificate forces either
       `verifySuccinctRecursiveHem ... { cert with headers := headers' } = false` or an explicit
       `HashCollisionWitness H` on `encodeCompressedHeaderChain`.
    3. On concrete `concreteSuccinctOuterCert` (with injective transcript hash `fun bs => bs`),
       mutating `childProofDigest` from `[0x01]` to `[0xFF]` causes `verifySuccinctRecursiveHem` to
       evaluate to `false`. -/
theorem tooth_succinctRecursiveHem_rejects_downgrade_and_tamper :
    (∀ H outerArith outerDom regDig ep msg (cert : SuccinctOuterHemCertificate),
      cert.outerInst.regime = .bciksJohnsonClassical128 →
      verifySuccinctRecursiveHem H outerArith outerDom regDig ep msg cert = false) ∧
    (∀ H outerArith outerDom regDig ep msg (cert : SuccinctOuterHemCertificate)
        (headers' : List ShardCompressedHeader),
      verifySuccinctRecursiveHem H outerArith outerDom regDig ep msg cert = true →
      headers' ≠ cert.headers →
      (HashCollisionWitness H → False) →
      verifySuccinctRecursiveHem H outerArith outerDom regDig ep msg
        { cert with headers := headers' } = false) ∧
    verifySuccinctRecursiveHem (fun bs => bs) concreteHemArith rsSbox7WhirDomain
      (encodeRegistry concreteHemRegistry) [] []
      { concreteSuccinctOuterCert with
        headers := concreteSuccinctOuterHeaders.map
          (fun h => { h with childProofDigest := [0xFF] })
        outerInst := rsSbox7Inst Goldilocks.zero Goldilocks.zero
          (succinctOuterBoundMessage (encodeRegistry concreteHemRegistry) [] []
            (encodeCompressedHeaderChain concreteSuccinctOuterHeaders)) } = false := by
  refine ⟨?_, ?_, ?_⟩
  · intro H outerArith outerDom regDig ep msg cert hCl
    apply Bool.eq_false_iff.mpr
    intro hAcc
    have hQr := (verifySuccinctRecursiveHem_facts hAcc).2.2.2.2.2.1
    rw [hCl] at hQr
    cases hQr
  · intro H outerArith outerDom regDig ep msg cert headers' hAcc hNe hNoCol
    apply Bool.eq_false_iff.mpr
    intro hAcc'
    have hMsg := (verifySuccinctRecursiveHem_facts hAcc).2.2.2.2.2.2.2.1
    have hMsg' := (verifySuccinctRecursiveHem_facts hAcc').2.2.2.2.2.2.2.1
    dsimp only at hMsg'
    rw [hMsg] at hMsg'
    have hDigEq := (succinctOuterBoundMessage_injective hMsg').2.2.2
    have hEncNe : encodeCompressedHeaderChain headers' ≠ encodeCompressedHeaderChain cert.headers := by
      intro hEncEq
      exact hNe (encodeCompressedHeaderChain_injective hEncEq)
    exact hNoCol ⟨encodeCompressedHeaderChain headers', encodeCompressedHeaderChain cert.headers,
      hEncNe, hDigEq.symm⟩
  · apply Bool.eq_false_iff.mpr
    intro hAcc'
    have hMsg' := (verifySuccinctRecursiveHem_facts hAcc').2.2.2.2.2.2.2.1
    dsimp only [rsSbox7Inst] at hMsg'
    have hEncEq := (succinctOuterBoundMessage_injective hMsg').2.2.2
    have hHdrEq := encodeCompressedHeaderChain_injective hEncEq
    have hDflt := shardToCompressedHeader (fun _ => [0x01]) (concreteHemShard false)
    have hHead := congrArg (fun hs : List ShardCompressedHeader => (hs.headD hDflt).childProofDigest) hHdrEq
    have hL : (concreteSuccinctOuterHeaders.headD hDflt).childProofDigest = [0x01] := rfl
    have hR : ((concreteSuccinctOuterHeaders.map
        (fun h => { h with childProofDigest := [0xFF] })).headD hDflt).childProofDigest = [0xFF] := rfl
    rw [hL, hR] at hHead
    exact absurd hHead (by decide)

end Qsag

/- Audit every declaration owned by this module, including private certificate helpers, and
    include an explicit negative control confirming `Classical.choice` would be rejected. -/
open Lean Elab Command in
run_cmd do
  let allow (ax : Name) : Bool := ax == ``propext || ax == ``Quot.sound
  let neg ← Lean.collectAxioms ``Classical.choice
  if (neg.filter (!allow ·)).isEmpty then
    throwError "Axiom audit negative control failed: Classical.choice was not rejected"
  let privEnv := (← getEnv).setExporting false
  let mut checked : Nat := 0
  let mut bad : Array String := #[]
  for (name, _) in privEnv.constants.toList do
    if !privEnv.isImportedConst name then
      let roots ← withEnv privEnv <| Lean.collectAxioms name
      let rejected := roots.filter (!allow ·)
      unless rejected.isEmpty do
        bad := bad.push s!"{name}: {rejected}"
      checked := checked + 1
  unless bad.isEmpty do
    throwError "Rejected axioms in declarations: {bad}"
  if checked == 0 then throwError "Empty module axiom audit"


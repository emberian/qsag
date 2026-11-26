module


public import Qsag.Math.Goldilocks
public import Qsag.Oracle.Poseidon2
public import Qsag.Protocol.Aggregation.Aggregation
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


def registryThresholdSum : List ShardRegistration → Nat
  | [] => 0
  | r :: rest => r.threshold + registryThresholdSum rest


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


private theorem exists_false_of_filter_length_lt {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.filter p).length < l.length → ∃ x ∈ l, p x = false
  | [], h => absurd h (Nat.not_lt_zero _)
  | x :: l, h => by
    cases hp : p x with
    | false => exact ⟨x, List.mem_cons_self .., hp⟩
    | true =>
      rw [List.filter_cons_of_pos hp, List.length_cons, List.length_cons] at h
      obtain ⟨y, hy, hpy⟩ := exists_false_of_filter_length_lt p l (Nat.lt_of_succ_lt_succ h)
      exact ⟨y, List.mem_cons_of_mem _ hy, hpy⟩


/-- Signatures of the active signers of one shard, read off an all-active-signers check. -/
def collectShardSigs (epochFloor msg shardId : List UInt8) (suite : TweakableHashSuite)
    (params : PqHashParams) :
    (pks : List PqPublicKey) → (bs : SignerBitmapSpec) → (sigs : List PqHashSig) →
    checkAllActiveSigners suite params (shardBoundMessage shardId epochFloor msg) pks bs sigs
      = true →
    List (ExtractedQuorumSig epochFloor msg)
  | [], [], _, _ => []
  | [], _ :: _, _, h => absurd h (by rw [checkAllActiveSigners_nil_cons]; exact Bool.false_ne_true)
  | _ :: _, [], _, h => absurd h (by rw [checkAllActiveSigners_cons_nil]; exact Bool.false_ne_true)
  | _ :: _, _ :: _, [], h =>
    absurd h (by rw [checkAllActiveSigners_cons_cons_nil]; exact Bool.false_ne_true)
  | pk :: pks, true :: bs, sig :: sigs, h =>
    have h' : verifyPqHashSig suite params pk (shardBoundMessage shardId epochFloor msg) sig = true ∧
        checkAllActiveSigners suite params (shardBoundMessage shardId epochFloor msg) pks bs sigs
          = true := by
      rw [checkAllActiveSigners_cons_cons_cons] at h
      simpa using h
    ⟨⟨shardId, suite, params, pk⟩, sig, h'.1⟩ ::
      collectShardSigs epochFloor msg shardId suite params pks bs sigs h'.2
  | _ :: pks, false :: bs, _ :: sigs, h =>
    collectShardSigs epochFloor msg shardId suite params pks bs sigs
      (by rw [checkAllActiveSigners_cons_cons_cons] at h; simpa using h)

theorem collectShardSigs_slots (epochFloor msg shardId : List UInt8) (suite : TweakableHashSuite)
    (params : PqHashParams) :
    ∀ (pks : List PqPublicKey) (bs : SignerBitmapSpec) (sigs : List PqHashSig)
      (h : checkAllActiveSigners suite params (shardBoundMessage shardId epochFloor msg) pks bs sigs
        = true),
      (collectShardSigs epochFloor msg shardId suite params pks bs sigs h).map (·.slot) =
        (activeKeys pks bs).map (HemSlot.mk shardId suite params) ∧
      (collectShardSigs epochFloor msg shardId suite params pks bs sigs h).length =
        bitmapPopcountSpec bs
  | [], [], _, _ => by simp [collectShardSigs, activeKeys, bitmapPopcountSpec_nil]
  | [], _ :: _, _, h => absurd h (by rw [checkAllActiveSigners_nil_cons]; exact Bool.false_ne_true)
  | _ :: _, [], _, h => absurd h (by rw [checkAllActiveSigners_cons_nil]; exact Bool.false_ne_true)
  | _ :: _, _ :: _, [], h =>
    absurd h (by rw [checkAllActiveSigners_cons_cons_nil]; exact Bool.false_ne_true)
  | pk :: pks, true :: bs, sig :: sigs, h => by
    have h' : checkAllActiveSigners suite params (shardBoundMessage shardId epochFloor msg)
        pks bs sigs = true := by
      have := h
      rw [checkAllActiveSigners_cons_cons_cons] at this
      simp at this
      exact this.2
    have ih := collectShardSigs_slots epochFloor msg shardId suite params pks bs sigs h'
    refine ⟨?_, ?_⟩
    · simp only [collectShardSigs, activeKeys, ite_true, List.map_cons, ih.1]
    · have h2 := ih.2
      simp only [collectShardSigs, bitmapPopcountSpec_cons, ite_true, List.length_cons]
      omega
  | _ :: pks, false :: bs, _ :: sigs, h => by
    have h' : checkAllActiveSigners suite params (shardBoundMessage shardId epochFloor msg)
        pks bs sigs = true := by
      rw [checkAllActiveSigners_cons_cons_cons] at h
      simpa using h
    have ih := collectShardSigs_slots epochFloor msg shardId suite params pks bs sigs h'
    refine ⟨?_, ?_⟩
    · simp only [collectShardSigs, activeKeys, Bool.false_eq_true, ite_false]
      exact ih.1
    · have h2 := ih.2
      simp only [collectShardSigs, bitmapPopcountSpec_cons, Bool.false_eq_true, ite_false]
      omega


/-! ### Prover commitment-opening transcript extraction (`StagesBound` grounding & query cost) -/


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


def layerGroupsAt : Nat → Nat → Nat
  | groups, 0 => groups
  | groups, l + 1 => layerGroupsAt (groups / 2) l


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


/-- Canonical honest-prover transcript builder converting any `StagesBound` view into a
    `CommittedTableTranscript` (`rewoundOpenings = []`). -/
def mapCosetsAux {α : Type} (f : Nat → α) : Nat → Nat → List α
  | _, 0 => []
  | base, k + 1 => f base :: mapCosetsAux f (base + 1) k


private theorem mapCosetsAux_length {α : Type} (f : Nat → α) :
    ∀ (base k : Nat), (mapCosetsAux f base k).length = k
  | _, 0 => rfl
  | base, k + 1 => congrArg Nat.succ (mapCosetsAux_length f (base + 1) k)


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


/-! ### `#tooth`: lowered shard threshold & unscoped shard replay refutations -/


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

theorem encodeBitmapBytes_injective {a b : SignerBitmapSpec}
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


/-! ## Concrete two-layer and succinct-outer fixtures (evaluated here; audited and paired in `Tests/RecursiveAggregationTeeth`) -/


private theorem concreteSeedRoot_eq (second : Bool) :
    let seed := if second then Goldilocks.one else Goldilocks.zero
    CommRingOps.add (pow7Goldilocks Goldilocks.zero) seed = seed := by
  intro seed
  exact sbox7_root_of_zero_preimage seed


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


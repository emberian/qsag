module
/-
# Packed 4-Limb Goldilocks Digests, the Width-12 `Poseidon2` Compression, and Tweak Addresses (`sig.rs`)

The packed `Digest4` (`[Goldilocks; 4]`) representation and the aggregation geometries, the Jive
feed-forward step `poseidon2Compress12FF`, the WOTS+C chain walk, the 256-bit-capacity endpoint
sponge, the 2-block full-`pkSeed` `merkleNodeHash` with 1-based node levels, the injective packed
tweak address `packWotsAddrLimb`, and the FORS node addressing `forsNodeAddr`.
-/

public import Qsag.Protocol.Aggregation.ConcreteSecurityBudget
public import Qsag.Tactic.Prelude
public import Qsag.Math.Goldilocks
public import Qsag.Oracle.Keccak
public import Qsag.Oracle.Poseidon2
public import Qsag.Protocol.Aggregation.UcGames
public import Qsag.Protocol.Aggregation.Aggregation
public import Qsag.Tactic.AssuranceKit
public import Qsag.Math.GoldilocksEncoding
public import Qsag.Math.QuinticExt5
public import Qsag.Oracle.Qrom

public section

namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
attribute [local irreducible] poseidon2Perm12 poseidon2Perm12Inv

set_option autoImplicit false
set_option exponentiation.threshold 2048

/-! ## §1. Packed 4-Limb Goldilocks Field-Native Corduroy / XMSS Signature Engine (`sig.rs`) -/

/-- Packed 4-limb Goldilocks digest `[Goldilocks; 4]` (`256`-bit sponge block, `sig.rs:28`). -/
abbrev Digest4 := Lane4

/-- Signature profile selector matching `AggSigProfile` in `crates/qsag-agg/src/sig.rs`. -/
inductive AggSigProfile where
  | xmssPoseidon2
  | corduroyPoseidon2
  deriving DecidableEq, Repr

/-- Production stateful `JortsPoseidon2` (`AggSigProfile::JortsPoseidon2 = 1` in `sig.rs:71`)
    constructor alias for `.xmssPoseidon2`. -/
@[match_pattern] abbrev AggSigProfile.jortsPoseidon2 : AggSigProfile := .xmssPoseidon2

/-- Exact 64-bit ASCII domain-separation tags from `crates/qsag-agg/src/sig.rs`. -/
def domainPrfWots : Goldilocks := Goldilocks.ofNat 0x5153414757505246
def domainWotsStep : Goldilocks := Goldilocks.ofNat 0x5153414757535450
def domainWotsPk : Goldilocks := Goldilocks.ofNat 0x5153414757504B31
def domainMerkleNode : Goldilocks := Goldilocks.ofNat 0x515341474D524B4C
def domainHMsgStateful : Goldilocks := Goldilocks.ofNat 0x51534147484D5331
#export_eqns domainHMsgStateful
def domainHMsgDetTree : Goldilocks := Goldilocks.ofNat 0x5153414748445452
def domainHMsgStateless : Goldilocks := Goldilocks.ofNat 0x515341474853544C
def domainPrfMsg : Goldilocks := Goldilocks.ofNat 0x515341475052464d
def domainForsPrf : Goldilocks := Goldilocks.ofNat 0x5153414746505246
def domainForsLeaf : Goldilocks := Goldilocks.ofNat 0x51534147464C4546
def domainForsNode : Goldilocks := Goldilocks.ofNat 0x51534147464E4F44
def domainForsRoots : Goldilocks := Goldilocks.ofNat 0x5153414746525453
def poseidon2IvTag : Goldilocks := Goldilocks.ofNat 0x504F53325F474C31

theorem aggSigDomains_nonzero_and_distinct :
    domainPrfWots ≠ Goldilocks.zero ∧
    domainWotsStep ≠ Goldilocks.zero ∧
    domainWotsPk ≠ Goldilocks.zero ∧
    domainMerkleNode ≠ Goldilocks.zero ∧
    domainHMsgStateful ≠ Goldilocks.zero ∧
    domainHMsgDetTree ≠ Goldilocks.zero ∧
    domainPrfMsg ≠ Goldilocks.zero ∧
    domainPrfWots ≠ domainWotsStep ∧
    domainPrfMsg ≠ domainPrfWots ∧
    domainMerkleNode ≠ domainForsNode ∧
    domainHMsgStateful ≠ domainHMsgDetTree := by
  decide +kernel

/-- Parameterized geometry for field-native WOTS+C + XMSS / FORS hypertree signatures. -/
structure AggSigGeometry where
  profile       : AggSigProfile
  wotsChains    : Nat
  targetSum     : Nat
  numLayers     : Nat
  subtreeHeight : Nat
  forsTrees     : Nat
  forsHeight    : Nat
  deriving DecidableEq, Repr

/-- Well-formedness of an `AggSigGeometry` (`w = 4` chains, non-trivial target sum `< 3 * ell1`). -/
@[expose] def AggSigGeometry.wellFormed (g : AggSigGeometry) : Bool :=
  (0 < g.wotsChains) &&
  (g.wotsChains % 2 == 0) &&
  (g.wotsChains ≤ 128) &&
  (0 < g.targetSum) &&
  (g.targetSum < 3 * g.wotsChains) &&
  (0 < g.numLayers) &&
  (0 < g.subtreeHeight) &&
  (g.numLayers * g.subtreeHeight ≤ 64) &&
  (if g.forsTrees == 0 then g.forsHeight == 0
   else (g.forsTrees % 2 == 0) && (g.forsTrees ≤ 32) && (0 < g.forsHeight) && (g.forsHeight ≤ 8))

/-- Deployed stateful `JortsPoseidon2` / `XmssPoseidon2` geometry (`ell1 = 128, targetSum = 192, d = 1, h' = 6`). -/
@[expose] def xmssPoseidon2Geom : AggSigGeometry where
  profile       := .xmssPoseidon2
  wotsChains    := 128
  targetSum     := 192
  numLayers     := 1
  subtreeHeight := 6
  forsTrees     := 0
  forsHeight    := 0

/-- Alias of `xmssPoseidon2Geom` matching `AggSigProfile::JortsPoseidon2` in `sig.rs`. -/
abbrev jortsPoseidon2Geom : AggSigGeometry := xmssPoseidon2Geom

/-- Exact raw serialized byte length of an `AggSigGeometry` (`AggSigProfile::raw_signature_bytes`
    in `sig.rs:183-195`). -/
def AggSigGeometry.rawSignatureBytes (g : AggSigGeometry) : Nat :=
  if g.forsTrees == 0 then
    32 + 4 + 4 + g.wotsChains * 32 + g.subtreeHeight * 32
  else
    32 + g.forsTrees * (1 + g.forsHeight) * 32 +
      g.numLayers * (4 + g.wotsChains * 32 + g.subtreeHeight * 32)

/-- Raw serialized signature size (`4,328` bytes) of `JortsPoseidon2` (`32B r_rand + 4B leaf_idx +
    4B tsw_ctr + 128*32B WOTS + 6*32B XMSS`, `sig.rs:187`). -/
def jortsPoseidon2RawSigBytes : Nat :=
  32 + 4 + 4 + 128 * 32 + 6 * 32

/-- Raw serialized signature size (`76,896` bytes) of `CorduroyPoseidon2` (`sig.rs:191-192`). -/
def aggCorduroyPoseidon2RawSigBytes : Nat :=
  32 + 32 * (1 + 8) * 32 + 16 * (4 + 128 * 32 + 4 * 32)

/-- Raw serialized byte length per `AggSigProfile` (`sig.rs:183`). -/
def AggSigProfile.rawSignatureBytes : AggSigProfile → Nat
  | .xmssPoseidon2 => jortsPoseidon2RawSigBytes
  | .corduroyPoseidon2 => aggCorduroyPoseidon2RawSigBytes

/-- Deployed stateless `CorduroyPoseidon2` geometry (`ell1 = 128, targetSum = 192, k = 32, a = 8, d = 16, h' = 4`). -/
@[expose] def corduroyPoseidon2Geom : AggSigGeometry where
  profile       := .corduroyPoseidon2
  wotsChains    := 128
  targetSum     := 192
  numLayers     := 16
  subtreeHeight := 4
  forsTrees     := 32
  forsHeight    := 8

theorem jortsPoseidon2RawSigBytes_eq :
    jortsPoseidon2RawSigBytes = 4328 ∧
    jortsPoseidon2Geom.rawSignatureBytes = 4328 ∧
    AggSigProfile.jortsPoseidon2.rawSignatureBytes = 4328 ∧
    aggCorduroyPoseidon2RawSigBytes = 76896 ∧
    corduroyPoseidon2Geom.rawSignatureBytes = 76896 ∧
    AggSigProfile.corduroyPoseidon2.rawSignatureBytes = 76896 := by
  decide

/-- Compact kernel-computable audit geometry (`ell1 = 2, targetSum = 3, d = 1, h' = 1`) for build-time `#tooth` tests. -/
def compactAuditGeom : AggSigGeometry where
  profile       := .xmssPoseidon2
  wotsChains    := 2
  targetSum     := 3
  numLayers     := 1
  subtreeHeight := 1
  forsTrees     := 0
  forsHeight    := 0

theorem deployedAggGeometries_wellFormed :
    xmssPoseidon2Geom.wellFormed = true ∧
    corduroyPoseidon2Geom.wellFormed = true ∧
    compactAuditGeom.wellFormed = true := by
  decide +kernel

/-- Validator public key (`65`-byte wire model: `profile` + 4-limb `pkSeed` + 4-limb `pkRoot`). -/
structure AggValidatorPk where
  profile : AggSigProfile
  pkSeed  : Digest4
  pkRoot  : Digest4
  deriving DecidableEq, Repr

/-- Weighted Jive feed-forward 12-to-4 `Poseidon2` compression
    `perm.b0 + in0 + 2·in1 + 4·tweak` (`poseidon2_compress12_ff` in `sponge.rs`). -/
def poseidon2Compress12FF (in0 in1 tweak : Digest4) : Digest4 :=
  poseidon2CompressWeighted ⟨in0, in1, tweak⟩

/-- Bijective `< 2^62` packed WOTS+C address limb (`pack_wots_addr_limb` in `sig.rs:285`). -/
def packWotsAddrLimb (layer kpIdx chainIdx stepIdx : Nat) : Goldilocks :=
  Goldilocks.ofNat
    ((layer % 64) * (2 ^ 44) +
     (kpIdx % (2 ^ 28)) * (2 ^ 16) +
     (chainIdx % 4096) * 16 +
     (stepIdx % 16))

private theorem pack4_unpack {l k c s : Nat}
    (hl : l < 64) (hk : k < 2 ^ 28) (hc : c < 4096) (hs : s < 16) :
    let v := l * 2 ^ 44 + k * 2 ^ 16 + c * 16 + s
    v < goldilocksPrime ∧
    v % 16 = s ∧
    (v / 16) % 4096 = c ∧
    ((v / 16) / 4096) % (2 ^ 28) = k ∧
    ((v / 16) / 4096) / (2 ^ 28) = l := by
  intro v
  have h1 : c * 16 + s < 2 ^ 16 := by
    have h16 : (2 : Nat) ^ 16 = 65536 := rfl
    rw [h16]; omega
  have h2 : k * 2 ^ 16 + (c * 16 + s) < 2 ^ 44 := by
    calc k * 2 ^ 16 + (c * 16 + s)
      _ < k * 2 ^ 16 + 2 ^ 16 := Nat.add_lt_add_left h1 _
      _ = (k + 1) * 2 ^ 16 := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ (2 ^ 28) * 2 ^ 16 := Nat.mul_le_mul_right _ hk
      _ = 2 ^ 44 := rfl
  have hLtP : v < goldilocksPrime := by
    calc v
      _ = l * 2 ^ 44 + (k * 2 ^ 16 + (c * 16 + s)) := by dsimp only [v]; simp [Nat.add_assoc]
      _ < l * 2 ^ 44 + 2 ^ 44 := Nat.add_lt_add_left h2 _
      _ = (l + 1) * 2 ^ 44 := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ 64 * 2 ^ 44 := Nat.mul_le_mul_right _ hl
      _ < goldilocksPrime := by decide
  have hFac : v = s + ((c + (k + l * 2 ^ 28) * 4096) * 16) := by
    dsimp only [v]
    have e1 : (2 : Nat) ^ 44 = (2 ^ 28) * (4096 * 16) := rfl
    have e2 : (2 : Nat) ^ 16 = 4096 * 16 := rfl
    rw [e1, e2]
    simp only [Nat.add_mul, Nat.mul_assoc, Nat.add_comm]
  have hsMod : v % 16 = s := by
    rw [hFac, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  have hv16 : v / 16 = c + (k + l * 2 ^ 28) * 4096 := by
    rw [hFac, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt hs, Nat.zero_add]
  have hcMod : (v / 16) % 4096 = c := by
    rw [hv16, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  have hv4096 : (v / 16) / 4096 = k + l * 2 ^ 28 := by
    rw [hv16, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt hc, Nat.zero_add]
  have hkMod : ((v / 16) / 4096) % (2 ^ 28) = k := by
    rw [hv4096, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  have hlDiv : ((v / 16) / 4096) / (2 ^ 28) = l := by
    rw [hv4096, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)), Nat.div_eq_of_lt hk, Nat.zero_add]
  exact ⟨hLtP, hsMod, hcMod, hkMod, hlDiv⟩

theorem packWotsAddrLimb_injective
    {l1 k1 c1 s1 l2 k2 c2 s2 : Nat}
    (hl1 : l1 < 64) (hk1 : k1 < 2 ^ 28) (hc1 : c1 < 4096) (hs1 : s1 < 16)
    (hl2 : l2 < 64) (hk2 : k2 < 2 ^ 28) (hc2 : c2 < 4096) (hs2 : s2 < 16)
    (hEq : packWotsAddrLimb l1 k1 c1 s1 = packWotsAddrLimb l2 k2 c2 s2) :
    l1 = l2 ∧ k1 = k2 ∧ c1 = c2 ∧ s1 = s2 := by
  have hVal := congrArg Goldilocks.val hEq
  unfold packWotsAddrLimb Goldilocks.ofNat at hVal
  dsimp only at hVal
  rw [Nat.mod_eq_of_lt hl1, Nat.mod_eq_of_lt hk1, Nat.mod_eq_of_lt hc1, Nat.mod_eq_of_lt hs1,
      Nat.mod_eq_of_lt hl2, Nat.mod_eq_of_lt hk2, Nat.mod_eq_of_lt hc2, Nat.mod_eq_of_lt hs2] at hVal
  obtain ⟨hb1, hs1', hc1', hk1', hl1'⟩ := pack4_unpack hl1 hk1 hc1 hs1
  obtain ⟨hb2, hs2', hc2', hk2', hl2'⟩ := pack4_unpack hl2 hk2 hc2 hs2
  rw [Nat.mod_eq_of_lt hb1, Nat.mod_eq_of_lt hb2] at hVal
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hl1', ← hl2', hVal]
  · rw [← hk1', ← hk2', hVal]
  · rw [← hc1', ← hc2', hVal]
  · rw [← hs1', ← hs2', hVal]

/-- Secret chain start `PRF_wots(skSeed, pkSeed, layer, treeIdx, kpIdx, chainIdx)` (`sig.rs:124`). -/
def wotsSecretStart (skSeed pkSeed : Digest4) (layer treeIdx kpIdx chainIdx : Nat) : Digest4 :=
  let tweak : Digest4 :=
    ⟨domainPrfWots,
     packWotsAddrLimb layer kpIdx chainIdx 0,
     Goldilocks.ofNat (treeIdx % (2 ^ 32)),
     Goldilocks.ofNat ((treeIdx / (2 ^ 32)) % (2 ^ 32))⟩
  poseidon2Compress12FF skSeed pkSeed tweak

/-- Domain-separated WOTS+C chain step hash (`wots_step_hash_injective` in `sig.rs:295`). -/
def wotsStepHash (pkSeed cur : Digest4) (layer treeIdx kpIdx chainIdx stepIdx : Nat) : Digest4 :=
  let tweak : Digest4 :=
    ⟨domainWotsStep,
     packWotsAddrLimb layer kpIdx chainIdx stepIdx,
     Goldilocks.ofNat (treeIdx % (2 ^ 32)),
     Goldilocks.ofNat ((treeIdx / (2 ^ 32)) % (2 ^ 32))⟩
  poseidon2Compress12FF cur pkSeed tweak

@[expose] def natIterAt {σ : Type} (step : Nat → σ → σ) : Nat → Nat → σ → σ
  | 0, _, s => s
  | n + 1, idx, s => natIterAt step n (idx + 1) (step idx s)

theorem natIterAt_add {σ : Type} (step : Nat → σ → σ) :
    ∀ (a b idx : Nat) (s : σ),
      natIterAt step (a + b) idx s = natIterAt step b (idx + a) (natIterAt step a idx s)
  | 0, b, idx, s => by
    rw [Nat.zero_add, Nat.add_zero]
    rfl
  | a + 1, b, idx, s => by
    rw [Nat.succ_add]
    dsimp only [natIterAt]
    rw [natIterAt_add step a b (idx + 1)]
    have hShift : idx + 1 + a = idx + (a + 1) := by omega
    rw [hShift]

/-- Iterated WOTS+C forward chain walk starting at `startStep` for `numSteps` applications. -/
@[expose] def wotsChainWalk (pkSeed : Digest4) (layer treeIdx kpIdx chainIdx startStep steps : Nat)
    (cur : Digest4) : Digest4 :=
  natIterAt (fun stp v => wotsStepHash pkSeed v layer treeIdx kpIdx chainIdx stp) steps startStep cur

theorem wotsChainWalk_add (pkSeed : Digest4) (layer treeIdx kpIdx chainIdx : Nat)
    (a b startStep : Nat) (cur : Digest4) :
    wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx startStep (a + b) cur =
      wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx (startStep + a) b
        (wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx startStep a cur) :=
  natIterAt_add _ a b startStep cur

@[expose] def absorbPairsPoly {D S : Type} (perm1 : S → D → S) (perm2 : S → D → D → S) :
    List D → S → Option D → S
  | [], st, none => st
  | [], st, some e0 => perm1 st e0
  | e :: rest, st, none => absorbPairsPoly perm1 perm2 rest st (some e)
  | e1 :: rest, st, some e0 => absorbPairsPoly perm1 perm2 rest (perm2 st e0 e1) none

def absorbDigest4Pairs (st : Poseidon2State12) (xs : List Digest4) : Poseidon2State12 :=
  absorbPairsPoly
    (fun s e0 => poseidon2Perm12 ⟨lane4Add s.b0 e0, s.b1, s.b2⟩)
    (fun s e0 e1 => poseidon2Perm12 ⟨lane4Add s.b0 e0, lane4Add s.b1 e1, s.b2⟩)
    xs st none

/-- 256-bit-capacity `Poseidon2` sponge compressing WOTS+C endpoints (`compress_wots_endpoints_sponge`, `sig.rs:318`). -/
def compressWotsEndpointsSponge (pkSeed : Digest4) (layer treeIdx kpIdx : Nat)
    (endpoints : List Digest4) : Digest4 :=
  let layerKp := Goldilocks.ofNat ((layer % (2 ^ 32)) * (2 ^ 32) + (kpIdx % (2 ^ 32)))
  let initSt : Poseidon2State12 :=
    ⟨pkSeed,
     ⟨layerKp,
      Goldilocks.ofNat (treeIdx % (2 ^ 32)),
      Goldilocks.ofNat ((treeIdx / (2 ^ 32)) % (2 ^ 32)),
      Goldilocks.ofNat endpoints.length⟩,
     ⟨domainWotsPk, Goldilocks.zero, Goldilocks.zero, poseidon2IvTag⟩⟩
  let st0 := poseidon2Perm12 initSt
  let stAbs := absorbDigest4Pairs st0 endpoints
  let stPad : Poseidon2State12 :=
    ⟨⟨Goldilocks.add stAbs.b0.x0 Goldilocks.one, stAbs.b0.x1, stAbs.b0.x2, stAbs.b0.x3⟩,
     stAbs.b1, stAbs.b2⟩
  (poseidon2Perm12 stPad).b0

/-- 2-block full-`pkSeed` binary Merkle node sponge (`merkle_node_hash` in `sig.rs:358`). -/
def merkleNodeHash (domainTag : Goldilocks) (pkSeed : Digest4)
    (layer treeIdx level nodeIdx : Nat) (left right : Digest4) : Digest4 :=
  let meta0 := Goldilocks.ofNat
    ((layer % 65536) * (2 ^ 48) + (level % 65536) * (2 ^ 32) + (nodeIdx % (2 ^ 32)))
  let st0 := poseidon2Perm12
    ⟨pkSeed,
     left,
     ⟨domainTag,
      meta0,
      Goldilocks.ofNat (treeIdx % (2 ^ 32)),
      Goldilocks.ofNat ((treeIdx / (2 ^ 32)) % (2 ^ 32))⟩⟩
  let b0' := lane4Add st0.b0 right
  let b1' : Digest4 :=
    ⟨Goldilocks.add st0.b1.x0 Goldilocks.one,
     Goldilocks.add st0.b1.x1 poseidon2IvTag,
     st0.b1.x2,
     st0.b1.x3⟩
  (poseidon2Perm12 ⟨b0', b1', st0.b2⟩).b0

@[expose] def merkleWalkPoly {D : Type} (nodeHash : Nat → Nat → D → D → D) :
    List D → Nat → Nat → D → D
  | [], _, _, cur => cur
  | sib :: rest, lvl, idx, cur =>
    let parentIdx := idx / 2
    let parent :=
      if idx % 2 == 0 then nodeHash lvl parentIdx cur sib
      else nodeHash lvl parentIdx sib cur
    merkleWalkPoly nodeHash rest (lvl + 1) parentIdx parent

def buildMerkleNodePoly {D : Type} (nodeHash : Nat → Nat → D → D → D) :
    Nat → (Nat → D) → Nat → Nat → D
  | 0, leafFn, _, nodeIdx => leafFn nodeIdx
  | h + 1, leafFn, lvl, nodeIdx =>
    let left := buildMerkleNodePoly nodeHash h leafFn lvl (2 * nodeIdx)
    let right := buildMerkleNodePoly nodeHash h leafFn lvl (2 * nodeIdx + 1)
    nodeHash (lvl + h) nodeIdx left right

def buildMerkleAuthPathPoly {D : Type} (nodeHash : Nat → Nat → D → D → D) :
    Nat → (Nat → D) → Nat → Nat → List D
  | 0, _, _, _ => []
  | h + 1, leafFn, lvl, idx =>
    let sibIdx := if idx % 2 == 0 then idx + 1 else idx - 1
    let sib := leafFn sibIdx
    let parentLeafFn := fun pIdx => nodeHash lvl pIdx (leafFn (2 * pIdx)) (leafFn (2 * pIdx + 1))
    sib :: buildMerkleAuthPathPoly nodeHash h parentLeafFn (lvl + 1) (idx / 2)

private theorem buildMerkleNodePoly_shift {D : Type} (nodeHash : Nat → Nat → D → D → D) :
    ∀ (h : Nat) (leafFn : Nat → D) (lvl nodeIdx : Nat),
      buildMerkleNodePoly nodeHash h
        (fun pIdx => nodeHash lvl pIdx (leafFn (2 * pIdx)) (leafFn (2 * pIdx + 1)))
        (lvl + 1) nodeIdx =
      buildMerkleNodePoly nodeHash (h + 1) leafFn lvl nodeIdx
  | 0, _, _, _ => rfl
  | h + 1, leafFn, lvl, nodeIdx => by
    let pFn := fun pIdx => nodeHash lvl pIdx (leafFn (2 * pIdx)) (leafFn (2 * pIdx + 1))
    change nodeHash ((lvl + 1) + h) nodeIdx
        (buildMerkleNodePoly nodeHash h pFn (lvl + 1) (2 * nodeIdx))
        (buildMerkleNodePoly nodeHash h pFn (lvl + 1) (2 * nodeIdx + 1)) =
      nodeHash (lvl + (h + 1)) nodeIdx
        (buildMerkleNodePoly nodeHash (h + 1) leafFn lvl (2 * nodeIdx))
        (buildMerkleNodePoly nodeHash (h + 1) leafFn lvl (2 * nodeIdx + 1))
    rw [buildMerkleNodePoly_shift nodeHash h leafFn lvl (2 * nodeIdx),
        buildMerkleNodePoly_shift nodeHash h leafFn lvl (2 * nodeIdx + 1)]
    have hLvl : (lvl + 1) + h = lvl + (h + 1) := by omega
    rw [hLvl]

private theorem buildMerkleAuthPathPoly_length {D : Type} (nodeHash : Nat → Nat → D → D → D) :
    ∀ (h : Nat) (leafFn : Nat → D) (lvl idx : Nat),
      (buildMerkleAuthPathPoly nodeHash h leafFn lvl idx).length = h
  | 0, _, _, _ => rfl
  | h + 1, leafFn, lvl, idx => by
    dsimp only [buildMerkleAuthPathPoly]
    rw [List.length_cons, buildMerkleAuthPathPoly_length nodeHash h]

private theorem merkleWalkPoly_buildMerkleAuthPathPoly {D : Type} (nodeHash : Nat → Nat → D → D → D) :
    ∀ (h : Nat) (leafFn : Nat → D) (lvl idx : Nat),
      idx < 2 ^ h →
      merkleWalkPoly nodeHash (buildMerkleAuthPathPoly nodeHash h leafFn lvl idx) lvl idx (leafFn idx) =
        buildMerkleNodePoly nodeHash h leafFn lvl 0
  | 0, _, _, idx, hLt => by
    have h0 : idx = 0 := by simp at hLt; omega
    subst h0
    rfl
  | h + 1, leafFn, lvl, idx, hLt => by
    dsimp only [buildMerkleAuthPathPoly, merkleWalkPoly]
    let parentLeafFn := fun pIdx => nodeHash lvl pIdx (leafFn (2 * pIdx)) (leafFn (2 * pIdx + 1))
    have hDivLt : idx / 2 < 2 ^ h := by
      rw [Nat.pow_succ] at hLt
      omega
    have hParEq :
        (if idx % 2 == 0 then
          nodeHash lvl (idx / 2) (leafFn idx) (leafFn (if idx % 2 == 0 then idx + 1 else idx - 1))
        else
          nodeHash lvl (idx / 2) (leafFn (if idx % 2 == 0 then idx + 1 else idx - 1)) (leafFn idx)) =
        parentLeafFn (idx / 2) := by
      cases hPar : (idx % 2 == 0)
      · have hOdd : idx % 2 = 1 := by
          cases hRem : idx % 2 with
          | zero => simp [hRem] at hPar
          | succ m => omega
        have hL : idx - 1 = 2 * (idx / 2) := by omega
        have hR : idx = 2 * (idx / 2) + 1 := by omega
        simp only [Bool.false_eq_true, ↓reduceIte]
        dsimp only [parentLeafFn]
        rw [hL, ← hR]
      · have hEven : idx % 2 = 0 := eq_of_beq hPar
        have hL : idx = 2 * (idx / 2) := by omega
        have hR : idx + 1 = 2 * (idx / 2) + 1 := by omega
        simp only [↓reduceIte]
        dsimp only [parentLeafFn]
        rw [hR]
        conv => lhs; arg 3; rw [hL]
    rw [hParEq,
        merkleWalkPoly_buildMerkleAuthPathPoly nodeHash h parentLeafFn (lvl + 1) (idx / 2) hDivLt,
        buildMerkleNodePoly_shift nodeHash h leafFn lvl 0]

private structure PolyMerkleCollision {D : Type} (nodeHash : Nat → Nat → D → D → D) where
  level    : Nat
  nodeIdx  : Nat
  left1    : D
  right1   : D
  left2    : D
  right2   : D
  neInputs : (left1, right1) ≠ (left2, right2)
  hashEq   : nodeHash level nodeIdx left1 right1 = nodeHash level nodeIdx left2 right2

private def extractMerkleLeafPoly {D : Type} [DecidableEq D] (nodeHash : Nat → Nat → D → D → D) :
    ∀ (h : Nat) (leafFn : Nat → D) (lvl idx : Nat) (forgedLeaf : D) (path : List D),
      path.length = h →
      idx < 2 ^ h →
      merkleWalkPoly nodeHash path lvl idx forgedLeaf = buildMerkleNodePoly nodeHash h leafFn lvl 0 →
      PSum (forgedLeaf = leafFn idx) (PolyMerkleCollision nodeHash)
  | 0, leafFn, _, idx, forgedLeaf, [], _, hLt, hRoot =>
    have hIdx0 : idx = 0 := by simp at hLt; omega
    .inl (by subst hIdx0; exact hRoot)
  | h + 1, leafFn, lvl, idx, forgedLeaf, sib :: rest, hCons, hLt, hRoot =>
    let parentLeafFn := fun pIdx => nodeHash lvl pIdx (leafFn (2 * pIdx)) (leafFn (2 * pIdx + 1))
    let pIdx := idx / 2
    let l1 := if idx % 2 == 0 then forgedLeaf else sib
    let r1 := if idx % 2 == 0 then sib else forgedLeaf
    let forgedParent := nodeHash lvl pIdx l1 r1
    have hStepWalk :
        merkleWalkPoly nodeHash rest (lvl + 1) pIdx forgedParent =
          buildMerkleNodePoly nodeHash h parentLeafFn (lvl + 1) 0 := by
      have hParEq :
          (if idx % 2 == 0 then nodeHash lvl pIdx forgedLeaf sib
           else nodeHash lvl pIdx sib forgedLeaf) = forgedParent := by
        dsimp only [forgedParent, l1, r1]
        cases (idx % 2 == 0) <;> rfl
      rw [buildMerkleNodePoly_shift, ← hRoot]
      dsimp only [merkleWalkPoly]
      change merkleWalkPoly nodeHash rest (lvl + 1) pIdx forgedParent =
        merkleWalkPoly nodeHash rest (lvl + 1) pIdx
          (if idx % 2 == 0 then nodeHash lvl pIdx forgedLeaf sib
           else nodeHash lvl pIdx sib forgedLeaf)
      rw [hParEq]
    have hDivLt : pIdx < 2 ^ h := by
      dsimp only [pIdx]
      rw [Nat.pow_succ] at hLt
      omega
    match extractMerkleLeafPoly nodeHash h parentLeafFn (lvl + 1) pIdx
            forgedParent rest (Nat.succ.inj hCons) hDivLt hStepWalk with
    | .inr col => .inr col
    | .inl hParentEq =>
      if hPair : (l1, r1) = (leafFn (2 * pIdx), leafFn (2 * pIdx + 1)) then
        .inl (by
          have hFst := congrArg Prod.fst hPair
          have hSnd := congrArg Prod.snd hPair
          dsimp only [l1, r1, pIdx] at hFst hSnd
          cases hEven : (idx % 2 == 0)
          · simp only [hEven, Bool.false_eq_true, ↓reduceIte] at hSnd
            have hOddEq : 2 * (idx / 2) + 1 = idx := by
              cases hRem : idx % 2 with
              | zero => simp [hRem] at hEven
              | succ m => omega
            rw [hOddEq] at hSnd
            exact hSnd
          · simp only [hEven, ↓reduceIte] at hFst
            have hEvenEq : 2 * (idx / 2) = idx := by
              have hr : idx % 2 = 0 := eq_of_beq hEven
              omega
            rw [hEvenEq] at hFst
            exact hFst)
      else
        .inr {
          level    := lvl
          nodeIdx  := pIdx
          left1    := l1
          right1   := r1
          left2    := leafFn (2 * pIdx)
          right2   := leafFn (2 * pIdx + 1)
          neInputs := hPair
          hashEq   := hParentEq
        }

/-- Node addressing of an XMSS subtree (`verify_individual_signature`): at every level the
    `node_idx` limb is the in-tree parent index. -/
def xmssNodeAddr : Nat → Nat → Nat := fun _ parentIdx => parentIdx

/-- Node addressing of FORS tree `j` under key pair `kpIdx` (`recover_fors_pk`): at the 1-based
    `level = lvl + 1` the `node_idx` limb is
    `(kp_idx << 16) | ((j << (FORS_HEIGHT - 1 - lvl)) + parent_idx)`. -/
@[expose] def forsNodeAddr (forsHeight kpIdx j : Nat) : Nat → Nat → Nat :=
  fun level parentIdx => (kpIdx <<< 16) + ((j <<< (forsHeight - level)) + parentIdx)

/-- The 2-block node hash of one tree under the node addressing `addr : level → parentIdx → node_idx`. -/
@[expose] def merkleAddrNodeHash (domainTag : Goldilocks) (pkSeed : Digest4) (layer treeIdx : Nat)
    (addr : Nat → Nat → Nat) : Nat → Nat → Digest4 → Digest4 → Digest4 :=
  fun level parentIdx => merkleNodeHash domainTag pkSeed layer treeIdx level (addr level parentIdx)

/-- Walk an authentication path from `(leafIdx, curNode)` up to the subtree root. -/
@[expose] def merkleWalkRoot (domainTag : Goldilocks) (pkSeed : Digest4) (layer treeIdx : Nat)
    (addr : Nat → Nat → Nat) (lvl idx : Nat)
    (cur : Digest4) (path : List Digest4) : Digest4 :=
  merkleWalkPoly (merkleAddrNodeHash domainTag pkSeed layer treeIdx addr) path lvl idx cur

/-- Deterministic binary Merkle subtree root at level `lvl` and node offset `nodeIdx` of remaining height `h`. -/
def buildMerkleNodeAt (domainTag : Goldilocks) (pkSeed : Digest4) (layer treeIdx : Nat)
    (addr : Nat → Nat → Nat) (leafFn : Nat → Digest4) (h lvl nodeIdx : Nat) : Digest4 :=
  buildMerkleNodePoly (merkleAddrNodeHash domainTag pkSeed layer treeIdx addr) h leafFn lvl nodeIdx

/-- Constructive sibling authentication path for `idx < 2^h` from level `lvl`. -/
def buildMerkleAuthPathAt (domainTag : Goldilocks) (pkSeed : Digest4) (layer treeIdx : Nat)
    (addr : Nat → Nat → Nat) (leafFn : Nat → Digest4) (h lvl idx : Nat) : List Digest4 :=
  buildMerkleAuthPathPoly (merkleAddrNodeHash domainTag pkSeed layer treeIdx addr) h leafFn lvl idx

theorem buildMerkleAuthPathAt_length (domainTag : Goldilocks) (pkSeed : Digest4)
    (layer treeIdx : Nat) (addr : Nat → Nat → Nat) (leafFn : Nat → Digest4) (h lvl idx : Nat) :
    (buildMerkleAuthPathAt domainTag pkSeed layer treeIdx addr leafFn h lvl idx).length = h :=
  buildMerkleAuthPathPoly_length _ h leafFn lvl idx

theorem merkleWalkRoot_buildMerkleAuthPathAt (domainTag : Goldilocks) (pkSeed : Digest4)
    (layer treeIdx : Nat) (addr : Nat → Nat → Nat) (h : Nat) (leafFn : Nat → Digest4)
    (lvl idx : Nat) (hLt : idx < 2 ^ h) :
    merkleWalkRoot domainTag pkSeed layer treeIdx addr lvl idx (leafFn idx)
      (buildMerkleAuthPathAt domainTag pkSeed layer treeIdx addr leafFn h lvl idx) =
    buildMerkleNodeAt domainTag pkSeed layer treeIdx addr leafFn h lvl 0 :=
  merkleWalkPoly_buildMerkleAuthPathPoly _ h leafFn lvl idx hLt

/-- Concrete witness of a 2-block `merkleNodeHash` collision under `pkSeed`. -/
structure MerkleNodeCollisionWitness (pkSeed : Digest4) where
  domainTag : Goldilocks
  layer     : Nat
  treeIdx   : Nat
  level     : Nat
  nodeIdx   : Nat
  left1     : Digest4
  right1    : Digest4
  left2     : Digest4
  right2    : Digest4
  neInputs  : (left1, right1) ≠ (left2, right2)
  hashEq    : merkleNodeHash domainTag pkSeed layer treeIdx level nodeIdx left1 right1 =
              merkleNodeHash domainTag pkSeed layer treeIdx level nodeIdx left2 right2

/-- Constructive Merkle path extractor: if a walked path from `forgedLeaf`
    equals the honest subtree root `buildMerkleNodeAt ... h lvl 0`, either `forgedLeaf = leafFn idx`
    or we extract an explicit `MerkleNodeCollisionWitness pkSeed`! -/
def extractMerkleLeafOrCollision (domainTag : Goldilocks) (pkSeed : Digest4)
    (layer treeIdx : Nat) (addr : Nat → Nat → Nat) (h : Nat) (leafFn : Nat → Digest4) (lvl idx : Nat)
    (forgedLeaf : Digest4) (path : List Digest4)
    (hLen : path.length = h) (hLt : idx < 2 ^ h)
    (hRoot : merkleWalkRoot domainTag pkSeed layer treeIdx addr lvl idx forgedLeaf path =
               buildMerkleNodeAt domainTag pkSeed layer treeIdx addr leafFn h lvl 0) :
    PSum (forgedLeaf = leafFn idx) (MerkleNodeCollisionWitness pkSeed) :=
  match extractMerkleLeafPoly (merkleAddrNodeHash domainTag pkSeed layer treeIdx addr)
          h leafFn lvl idx forgedLeaf path hLen hLt hRoot with
  | .inl hEq => .inl hEq
  | .inr col => .inr {
      domainTag := domainTag
      layer     := layer
      treeIdx   := treeIdx
      level     := col.level
      nodeIdx   := addr col.level col.nodeIdx
      left1     := col.left1
      right1    := col.right1
      left2     := col.left2
      right2    := col.right2
      neInputs  := col.neInputs
      hashEq    := col.hashEq
    }

end Qsag

end

public section

namespace Qsag

#export_eqns compressWotsEndpointsSponge
#export_eqns corduroyPoseidon2Geom
#export_eqns forsNodeAddr
#export_eqns merkleAddrNodeHash
#export_eqns merkleNodeHash
#export_eqns packWotsAddrLimb
#export_eqns poseidon2Compress12FF
#export_eqns wotsStepHash
#export_eqns xmssNodeAddr
#export_eqns xmssPoseidon2Geom
#export_eqns absorbPairsPoly absorbDigest4Pairs merkleWalkRoot merkleWalkPoly
theorem foldl_fixed_step {A B : Type} (f : A → B → A) (a : A)
    (is : List B) (h : ∀ i ∈ is, f a i = a) : is.foldl f a = a := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    rw [List.foldl_cons, h i (List.mem_cons_self ..)]
    exact ih (fun j hj => h j (List.mem_cons_of_mem _ hj))

end Qsag

end

public section

namespace Qsag

#export_eqns buildMerkleNodeAt buildMerkleAuthPathAt buildMerkleNodePoly buildMerkleAuthPathPoly
-- Field values of the audit geometry for `Tests/CompositionInstances`; no body is exposed.
#export_eqns compactAuditGeom domainMerkleNode poseidon2IvTag
/-! ### Symbolic bridges from `compactAuditGeom` to `Oracle/Poseidon2` `compactJorts*` -/

theorem compactWotsStep_eq (pkSeed cur : Digest4)
    (layer treeIdx kpIdx chainIdx stepIdx : Nat) :
    wotsStepHash pkSeed cur layer treeIdx kpIdx chainIdx stepIdx =
      compactWotsStep pkSeed cur layer treeIdx kpIdx chainIdx stepIdx := by
  unfold wotsStepHash poseidon2Compress12FF domainWotsStep packWotsAddrLimb
  rw [compactWotsStep_eq_def, compactPackWotsAddr_eq]

theorem compactWotsSecret_eq (skSeed pkSeed : Digest4)
    (layer treeIdx kpIdx chainIdx : Nat) :
    wotsSecretStart skSeed pkSeed layer treeIdx kpIdx chainIdx =
      compactWotsSecret skSeed pkSeed layer treeIdx kpIdx chainIdx := by
  unfold wotsSecretStart poseidon2Compress12FF domainPrfWots packWotsAddrLimb
  rw [compactWotsSecret_eq_def, compactPackWotsAddr_eq]

theorem compactWotsWalk_eq (pkSeed : Digest4)
    (layer treeIdx kpIdx chainIdx : Nat) :
    ∀ (steps startStep : Nat) (cur : Digest4),
      wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx startStep steps cur =
        compactWotsWalk pkSeed layer treeIdx kpIdx chainIdx steps startStep cur
  | 0, startStep, cur => by
    rw [compactWotsWalk_zero]
    rfl
  | steps + 1, startStep, cur => by
    rw [compactWotsWalk_succ]
    show wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx (startStep + 1) steps
        (wotsStepHash pkSeed cur layer treeIdx kpIdx chainIdx startStep) = _
    rw [compactWotsStep_eq, compactWotsWalk_eq pkSeed layer treeIdx kpIdx chainIdx steps (startStep + 1)]

theorem compactWotsPk2_eq (pkSeed : Digest4) (layer treeIdx kpIdx : Nat)
    (e0 e1 : Digest4) :
    compressWotsEndpointsSponge pkSeed layer treeIdx kpIdx [e0, e1] =
      compactWotsPk2 pkSeed layer treeIdx kpIdx e0 e1 := by
  unfold compressWotsEndpointsSponge absorbDigest4Pairs absorbPairsPoly
    domainWotsPk poseidon2IvTag
  rw [compactWotsPk2_eq_def]
  rfl

theorem compactMerkleNode_eq (pkSeed : Digest4)
    (layer treeIdx level nodeIdx : Nat) (left right : Digest4) :
    merkleNodeHash domainMerkleNode pkSeed layer treeIdx level nodeIdx left right =
      compactMerkleNode pkSeed layer treeIdx level nodeIdx left right := by
  unfold merkleNodeHash domainMerkleNode poseidon2IvTag
  rw [compactMerkleNode_eq_def]

end Qsag
end

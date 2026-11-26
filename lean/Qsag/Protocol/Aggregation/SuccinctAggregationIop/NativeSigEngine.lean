module
/-
# FORS / Hypertree Signing and Verification and Secret-Anchored Forgery Extraction (`sig.rs`)

FORS and hypertree signing and verification with unconditional completeness
(`aggNativeSig_completeness`), and secret-anchored forgery extraction: an accepted signature
that differs from the honest one yields an explicit WOTS+C chain preimage or a Merkle / sponge
collision (`aggNativeSig_wots_merkle_soundness`). FORS instance addressing follows
`recover_fors_pk` (`forsNodeAddr_injective`).
-/

public import Qsag.Protocol.Aggregation.SuccinctAggregationIop.Base4DigitsAndMessageMu

public section

namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
attribute [local irreducible] poseidon2Perm12 poseidon2Perm12Inv
set_option autoImplicit false
set_option exponentiation.threshold 2048

/-! ### FORS & Hypertree Signing, Verification, Completeness, and Constructive Soundness -/

/-- FORS tree opening (`secretVal` + sibling authentication path of height `forsHeight`). -/
structure AggForsTreeOpening where
  secretVal : Digest4
  authPath  : List Digest4
  deriving DecidableEq, Repr

/-- Single hypertree layer signature (`tswCtr` + `wotsChains` + `merklePath`). -/
structure WotsLayerSig where
  tswCtr     : Nat
  wotsChains : List Digest4
  merklePath : List Digest4
  deriving DecidableEq, Repr

/-- Field-native validator signature matching `ValidatorSignature` in `crates/qsag-agg/src/sig.rs`. -/
structure AggNativeSignature where
  profile         : AggSigProfile
  rRand           : Digest4
  statefulLeafIdx : Nat
  forsOpenings    : List AggForsTreeOpening
  layers          : List WotsLayerSig
  deriving DecidableEq, Repr

/-- Key-pair index of the bottom hypertree leaf that owns the FORS instance
    (`kp_idx = leaf_global_idx & ((1 << CORDUROY_SUBTREE_HEIGHT) - 1)` in `recover_fors_pk`). -/
def forsKpIdx (geom : AggSigGeometry) (leafGlobalIdx : Nat) : Nat :=
  leafGlobalIdx % 2 ^ geom.subtreeHeight

/-- Bottom-layer hypertree tree index of the FORS instance
    (`tree_idx = leaf_global_idx >> CORDUROY_SUBTREE_HEIGHT` in `recover_fors_pk`). -/
def forsHyperTreeIdx (geom : AggSigGeometry) (leafGlobalIdx : Nat) : Nat :=
  leafGlobalIdx / 2 ^ geom.subtreeHeight

/-- In the deployed geometry the split is `(leaf_global_idx & 0xF, leaf_global_idx >> 4)`. -/
theorem corduroy_fors_addr_split (leafGlobalIdx : Nat) :
    forsKpIdx corduroyPoseidon2Geom leafGlobalIdx = leafGlobalIdx % 16 ∧
    forsHyperTreeIdx corduroyPoseidon2Geom leafGlobalIdx = leafGlobalIdx / 16 :=
  ⟨rfl, rfl⟩

/-- Packed FORS leaf address limb `(kp_idx << 24) | ((j << FORS_HEIGHT) | idx_j)`. -/
def forsLeafAddr (geom : AggSigGeometry) (leafGlobalIdx j idx : Nat) : Nat :=
  (forsKpIdx geom leafGlobalIdx <<< 24) ||| ((j <<< geom.forsHeight) ||| idx)

/-- In the deployed geometry the leaf address limb is `(kp_idx << 24) | (j << 8) | idx_j`. -/
theorem corduroy_forsLeafAddr (leafGlobalIdx j idx : Nat) :
    forsLeafAddr corduroyPoseidon2Geom leafGlobalIdx j idx =
      ((leafGlobalIdx % 16) <<< 24) ||| ((j <<< 8) ||| idx) := by
  unfold forsLeafAddr forsKpIdx
  rfl

/-- Tweak of the FORS leaf PRF / leaf hash:
    `[domain, (kp_idx << 24) | (j << FORS_HEIGHT) | idx_j, tree_idx & 0xFFFF_FFFF, tree_idx >> 32]`. -/
def forsLeafTweak4 (domainTag : Goldilocks) (geom : AggSigGeometry)
    (leafGlobalIdx j idx : Nat) : Digest4 :=
  ⟨domainTag,
   Goldilocks.ofNat (forsLeafAddr geom leafGlobalIdx j idx),
   Goldilocks.ofNat (forsHyperTreeIdx geom leafGlobalIdx % (2 ^ 32)),
   Goldilocks.ofNat ((forsHyperTreeIdx geom leafGlobalIdx / (2 ^ 32)) % (2 ^ 32))⟩

/-- FORS leaf secret of leaf `idx` in FORS tree `j` (`fors_leaf_secret` in `sig.rs`). -/
def forsSecretVal (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (leafGlobalIdx j idx : Nat) : Digest4 :=
  poseidon2Compress12FF skSeed pkSeed (forsLeafTweak4 domainForsPrf geom leafGlobalIdx j idx)

/-- FORS leaf hash of leaf `idx` in FORS tree `j` (`recover_fors_pk` in `sig.rs`). -/
def forsLeafHash (geom : AggSigGeometry) (pkSeed val : Digest4)
    (leafGlobalIdx j idx : Nat) : Digest4 :=
  poseidon2Compress12FF val pkSeed (forsLeafTweak4 domainForsLeaf geom leafGlobalIdx j idx)

/-- Node addressing of FORS tree `j` of the instance at `leafGlobalIdx`. -/
def forsTreeNodeAddr (geom : AggSigGeometry) (leafGlobalIdx j : Nat) : Nat → Nat → Nat :=
  forsNodeAddr geom.forsHeight (forsKpIdx geom leafGlobalIdx) j

/-- Rate-8 sponge over the FORS roots (`recover_fors_pk`): the capacity block is
    `[kp_idx, tree_idx & 0xFFFF_FFFF, tree_idx >> 32, FORS_TREES]`. -/
def compressForsRootsSponge (geom : AggSigGeometry) (pkSeed : Digest4) (leafGlobalIdx : Nat)
    (roots : List Digest4) : Digest4 :=
  let initSt : Poseidon2State12 :=
    ⟨pkSeed,
     ⟨Goldilocks.ofNat (forsKpIdx geom leafGlobalIdx),
      Goldilocks.ofNat (forsHyperTreeIdx geom leafGlobalIdx % (2 ^ 32)),
      Goldilocks.ofNat ((forsHyperTreeIdx geom leafGlobalIdx / (2 ^ 32)) % (2 ^ 32)),
      Goldilocks.ofNat geom.forsTrees⟩,
     ⟨domainForsRoots, Goldilocks.zero, Goldilocks.zero, poseidon2IvTag⟩⟩
  let st0 := poseidon2Perm12 initSt
  let stAbs := absorbDigest4Pairs st0 roots
  let stPad : Poseidon2State12 :=
    ⟨⟨Goldilocks.add stAbs.b0.x0 Goldilocks.one, stAbs.b0.x1, stAbs.b0.x2, stAbs.b0.x3⟩,
     stAbs.b1, stAbs.b2⟩
  (poseidon2Perm12 stPad).b0

/-- Two-block stateless XOF sponge state (`derive_stateless_fors_and_leaf_checked`, `sig.rs:494`). -/
def statelessXofSpongeState (pk : AggValidatorPk) (rRand : Digest4) (mu : Digest5) : Poseidon2State12 :=
  let st0 := poseidon2Perm12
    ⟨pk.pkSeed, pk.pkRoot, ⟨domainHMsgStateless, mu.limb4, Goldilocks.zero, poseidon2IvTag⟩⟩
  let muLow : Digest4 := ⟨mu.limb0, mu.limb1, mu.limb2, mu.limb3⟩
  poseidon2Perm12 ⟨lane4Add st0.b0 rRand, lane4Add st0.b1 muLow, st0.b2⟩

/-- Source limb of a stateless FORS index; the fifth source supplies the final four bytes. -/
@[expose] def statelessForsSourceLimb (st : Poseidon2State12) : Nat → Nat
  | 0 => st.b0.x0.val
  | 1 => st.b0.x1.val
  | 2 => st.b0.x2.val
  | 3 => st.b0.x3.val
  | _ => st.b1.x0.val

/-- Stateless XOF deriving `leafGlobalIdx` and `forsTrees` leaf offsets (`derive_stateless_fors_and_leaf_checked`, `sig.rs:494`). -/
def deriveStatelessLeafAndForsChecked (geom : AggSigGeometry) (pk : AggValidatorPk)
    (rRand : Digest4) (mu : Digest5) : Option (Nat × List Nat) :=
  let st1 := statelessXofSpongeState pk rRand mu
  let sq := [st1.b0.x0, st1.b0.x1, st1.b0.x2, st1.b0.x3, st1.b1.x0, st1.b1.x1, st1.b1.x2]
  if sq.all (fun l => decide (l.val < 2 ^ 63)) then
    let totalTreeBits := geom.numLayers * geom.subtreeHeight
    let rawLeaf := (st1.b1.x1.val % (2 ^ 32)) + ((st1.b1.x2.val % (2 ^ 32)) * (2 ^ 32))
    let leafGlobalIdx := rawLeaf % (2 ^ totalTreeBits)
    let treeMod := 2 ^ geom.forsHeight
    let indices := (List.range geom.forsTrees).map fun t =>
      let limbVal := statelessForsSourceLimb st1 (t / 7)
      (limbVal / (256 ^ (t % 7))) % treeMod
    some (leafGlobalIdx, indices)
  else
    none

/-- Honest WOTS+C chain endpoints for `(layer, treeIdx, kpIdx)`. -/
def honestWotsEndpoints (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (layer treeIdx kpIdx : Nat) : List Digest4 :=
  (List.range geom.wotsChains).map fun c =>
    wotsChainWalk pkSeed layer treeIdx kpIdx c 0 3
      (wotsSecretStart skSeed pkSeed layer treeIdx kpIdx c)

/-- Honest WOTS+C public key leaf for `(layer, treeIdx, kpIdx)`. -/
def honestWotsPk (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (layer treeIdx kpIdx : Nat) : Digest4 :=
  compressWotsEndpointsSponge pkSeed layer treeIdx kpIdx
    (honestWotsEndpoints geom skSeed pkSeed layer treeIdx kpIdx)

/-- Honest XMSS subtree root at `(layer, treeIdx)`. -/
def honestSubtreeRoot (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (layer treeIdx : Nat) : Digest4 :=
  buildMerkleNodeAt domainMerkleNode pkSeed layer treeIdx xmssNodeAddr
    (honestWotsPk geom skSeed pkSeed layer treeIdx) geom.subtreeHeight 1 0

/-- Derive validator public key from `(geom, skSeed, pkSeed)`. -/
@[expose] def deriveAggPublicKey (geom : AggSigGeometry) (skSeed pkSeed : Digest4) : AggValidatorPk :=
  { profile := geom.profile
    pkSeed  := pkSeed
    pkRoot  := honestSubtreeRoot geom skSeed pkSeed (geom.numLayers - 1) 0 }

/-- Honest FORS leaf `off` of FORS tree `j` at `leafGlobalIdx`. -/
def honestForsLeaf (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (leafGlobalIdx j off : Nat) : Digest4 :=
  forsLeafHash geom pkSeed (forsSecretVal geom skSeed pkSeed leafGlobalIdx j off) leafGlobalIdx j off

/-- Honest root of FORS tree `j` at `leafGlobalIdx`. -/
def honestForsTreeRoot (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (leafGlobalIdx j : Nat) : Digest4 :=
  buildMerkleNodeAt domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
    (forsTreeNodeAddr geom leafGlobalIdx j)
    (honestForsLeaf geom skSeed pkSeed leafGlobalIdx j)
    geom.forsHeight 1 0

/-- Honest FORS public key at `leafGlobalIdx`. -/
def honestForsPk (geom : AggSigGeometry) (skSeed pkSeed : Digest4) (leafGlobalIdx : Nat) : Digest4 :=
  compressForsRootsSponge geom pkSeed leafGlobalIdx
    ((List.range geom.forsTrees).map (honestForsTreeRoot geom skSeed pkSeed leafGlobalIdx))

@[expose] def recoverEndpointsPoly {D : Type} (walkFn : Nat → Nat → Nat → D → D) :
    List Nat → List D → Nat → List D
  | [], _, _ => []
  | _, [], _ => []
  | d :: ds, sigVal :: rest, c =>
    walkFn c d (3 - d) sigVal :: recoverEndpointsPoly walkFn ds rest (c + 1)

private theorem recoverEndpointsPoly_honest {D : Type}
    (stepFn : Nat → Nat → D → D) (secretFn : Nat → D) :
    ∀ (digits : List Nat) (startC : Nat),
      (∀ d ∈ digits, d < 4) →
      recoverEndpointsPoly (fun c st n v => natIterAt (stepFn c) n st v)
        digits
        ((List.range digits.length).map fun i =>
          natIterAt (stepFn (startC + i)) (digits[i]!) 0 (secretFn (startC + i)))
        startC =
      (List.range digits.length).map fun i =>
        natIterAt (stepFn (startC + i)) 3 0 (secretFn (startC + i))
  | [], _, _ => rfl
  | d :: ds, startC, hLt => by
    have hd4 : d < 4 := hLt d (List.mem_cons_self ..)
    have hAdd3 : d + (3 - d) = 3 := by omega
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_cons]
    dsimp only [recoverEndpointsPoly]
    simp only [Nat.add_zero, List.getElem!_cons_zero]
    congr 1
    · conv => lhs; arg 3; rw [← Nat.zero_add d]
      rw [← natIterAt_add (stepFn startC) d (3 - d) 0, hAdd3]
    · simp only [List.map_map]
      have hFn1 :
          ((fun i => natIterAt (stepFn (startC + i)) ((d :: ds)[i]!) 0 (secretFn (startC + i))) ∘ Nat.succ) =
          (fun i => natIterAt (stepFn (startC + 1 + i)) (ds[i]!) 0 (secretFn (startC + 1 + i))) := by
        funext i
        have hIdx : startC + (i + 1) = startC + 1 + i := by omega
        simp [Function.comp, hIdx]
      have hFn2 :
          ((fun i => natIterAt (stepFn (startC + i)) 3 0 (secretFn (startC + i))) ∘ Nat.succ) =
          (fun i => natIterAt (stepFn (startC + 1 + i)) 3 0 (secretFn (startC + 1 + i))) := by
        funext i
        have hIdx : startC + (i + 1) = startC + 1 + i := by omega
        simp [Function.comp, hIdx]
      rw [hFn1, hFn2]
      exact recoverEndpointsPoly_honest stepFn secretFn ds (startC + 1)
        (fun x hx => hLt x (List.mem_cons_of_mem _ hx))

/-- Recover WOTS+C endpoints from signature chains and extracted base-4 digits (`0..3`). -/
@[expose] def recoverAggWotsEndpoints (pkSeed : Digest4) (layer treeIdx kpIdx startC : Nat)
    (ds : List Nat) (chains : List Digest4) : List Digest4 :=
  recoverEndpointsPoly (wotsChainWalk pkSeed layer treeIdx kpIdx) ds chains startC

private theorem recoverAggWotsEndpoints_honest (pkSeed skSeed : Digest4) (layer treeIdx kpIdx : Nat)
    (digits : List Nat) (startC : Nat) (hLt : ∀ d ∈ digits, d < 4) :
    recoverAggWotsEndpoints pkSeed layer treeIdx kpIdx startC digits
      ((List.range digits.length).map fun i =>
        wotsChainWalk pkSeed layer treeIdx kpIdx (startC + i) 0 (digits[i]!)
          (wotsSecretStart skSeed pkSeed layer treeIdx kpIdx (startC + i))) =
    (List.range digits.length).map fun i =>
      wotsChainWalk pkSeed layer treeIdx kpIdx (startC + i) 0 3
        (wotsSecretStart skSeed pkSeed layer treeIdx kpIdx (startC + i)) :=
  recoverEndpointsPoly_honest
    (fun c stp v => wotsStepHash pkSeed v layer treeIdx kpIdx c stp)
    (wotsSecretStart skSeed pkSeed layer treeIdx kpIdx)
    digits startC hLt

/-- Verify one WOTS+C + XMSS subtree layer and return the walked subtree root. -/
def verifyWotsLayer (geom : AggSigGeometry) (pk : AggValidatorPk)
    (layer treeIdx kpIdx : Nat) (hmsg : Digest5) (lsig : WotsLayerSig) : Option Digest4 :=
  if lsig.wotsChains.length == geom.wotsChains && lsig.merklePath.length == geom.subtreeHeight then
    match extractWotsDigitsChecked geom hmsg with
    | none => none
    | some digits =>
      if listNatSum digits == geom.targetSum then
        let endpoints := recoverAggWotsEndpoints pk.pkSeed layer treeIdx kpIdx 0 digits lsig.wotsChains
        let wotsPk := compressWotsEndpointsSponge pk.pkSeed layer treeIdx kpIdx endpoints
        some (merkleWalkRoot domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr 1 kpIdx wotsPk
          lsig.merklePath)
      else
        none
  else
    none

@[expose] def verifyForsPoly {OP D : Type} (step : Nat → Nat → OP → Option D) :
    List Nat → List OP → Nat → Option (List D)
  | [], [], _ => some []
  | idx :: idxs, op :: ops, t =>
    match step t idx op with
    | none => none
    | some rt =>
      match verifyForsPoly step idxs ops (t + 1) with
      | none => none
      | some rest => some (rt :: rest)
  | _, _, _ => none

/-- Verify the opening of leaf `idx` of FORS tree `j` (`recover_fors_pk`): the Merkle walk hashes
    under `tree_idx = leaf_global_idx >> h'`, the 1-based level `lvl + 1`, and the node index
    `(kp_idx << 16) + ((j << (FORS_HEIGHT - 1 - lvl)) + parent_idx)`. -/
def verifySingleForsOpening (geom : AggSigGeometry) (pkSeed : Digest4)
    (leafGlobalIdx j idx : Nat) (op : AggForsTreeOpening) : Option Digest4 :=
  if idx < 2 ^ geom.forsHeight && op.authPath.length == geom.forsHeight then
    let leaf := forsLeafHash geom pkSeed op.secretVal leafGlobalIdx j idx
    some (merkleWalkRoot domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
      (forsTreeNodeAddr geom leafGlobalIdx j) 1 idx leaf op.authPath)
  else
    none

/-- Verify FORS openings and recover `forsPk`. -/
def verifyForsTreesAux (geom : AggSigGeometry) (pkSeed : Digest4) (leafGlobalIdx startT : Nat)
    (idxs : List Nat) (ops : List AggForsTreeOpening) : Option (List Digest4) :=
  verifyForsPoly (verifySingleForsOpening geom pkSeed leafGlobalIdx) idxs ops startT

def verifyAndRecoverForsPk (geom : AggSigGeometry) (pkSeed : Digest4) (leafGlobalIdx : Nat)
    (indices : List Nat) (openings : List AggForsTreeOpening) : Option Digest4 :=
  if indices.length == geom.forsTrees && openings.length == geom.forsTrees then
    match verifyForsTreesAux geom pkSeed leafGlobalIdx 0 indices openings with
    | none => none
    | some roots => some (compressForsRootsSponge geom pkSeed leafGlobalIdx roots)
  else
    none

/-- The node address of FORS tree `j` determines `j`: within one key pair and one level, two
    in-range parent indices of trees `j₁`, `j₂` share an address only if `j₁ = j₂`. -/
theorem forsNodeAddr_injective (forsHeight kpIdx j₁ j₂ level p₁ p₂ : Nat)
    (hp₁ : p₁ < 2 ^ (forsHeight - level)) (hp₂ : p₂ < 2 ^ (forsHeight - level))
    (hEq : forsNodeAddr forsHeight kpIdx j₁ level p₁ = forsNodeAddr forsHeight kpIdx j₂ level p₂) :
    j₁ = j₂ ∧ p₁ = p₂ := by
  unfold forsNodeAddr at hEq
  have hPos : 0 < 2 ^ (forsHeight - level) := Nat.pow_pos (by decide)
  have hE : 2 ^ (forsHeight - level) * j₁ + p₁ = 2 ^ (forsHeight - level) * j₂ + p₂ := by
    have h := Nat.add_left_cancel hEq
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.mul_comm j₁, Nat.mul_comm j₂] at h
    exact h
  have hD := congrArg (· / 2 ^ (forsHeight - level)) hE
  have hM := congrArg (· % 2 ^ (forsHeight - level)) hE
  rw [Nat.mul_add_div hPos, Nat.mul_add_div hPos, Nat.div_eq_of_lt hp₁, Nat.div_eq_of_lt hp₂,
    Nat.add_zero, Nat.add_zero] at hD
  rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt hp₁, Nat.mod_eq_of_lt hp₂] at hM
  exact ⟨hD, hM⟩

/-- Top node of a non-empty Merkle walk: the last hash is taken at level `lvl + (len - 1)` and
    parent index `idx / 2 ^ len`. -/
private def merkleWalkPolyTopNode {D : Type} (nodeHash : Nat → Nat → D → D → D) :
    ∀ (path : List D) (lvl idx : Nat) (cur : D), path ≠ [] →
      { lr : D × D // merkleWalkPoly nodeHash path lvl idx cur =
          nodeHash (lvl + (path.length - 1)) (idx / 2 ^ path.length) lr.1 lr.2 }
  | [], _, _, _, h => absurd rfl h
  | [sib], lvl, idx, cur, _ =>
    match hE : (idx % 2 == 0) with
    | true => ⟨(cur, sib), by dsimp only [merkleWalkPoly]; rw [hE]; exact rfl⟩
    | false => ⟨(sib, cur), by dsimp only [merkleWalkPoly]; rw [hE]; exact rfl⟩
  | sib :: s2 :: rest, lvl, idx, cur, _ =>
    let parent :=
      if idx % 2 == 0 then nodeHash lvl (idx / 2) cur sib else nodeHash lvl (idx / 2) sib cur
    let top := merkleWalkPolyTopNode nodeHash (s2 :: rest) (lvl + 1) (idx / 2) parent
      (List.cons_ne_nil _ _)
    ⟨top.1, by
      have hLvl : lvl + 1 + ((s2 :: rest).length - 1) = lvl + ((sib :: s2 :: rest).length - 1) := by
        simp only [List.length_cons]
        omega
      have hIdx : idx / 2 / 2 ^ (s2 :: rest).length = idx / 2 ^ (sib :: s2 :: rest).length := by
        rw [Nat.div_div_eq_div_mul, List.length_cons (a := sib), Nat.pow_succ, Nat.mul_comm]
      rw [← hLvl, ← hIdx]
      exact top.2⟩

/-- One `merkleNodeHash` output shared by the top nodes of two FORS trees `j₁`, `j₂` of one
    instance, whose `node_idx` limbs `(kp_idx << 16) + j₁` and `(kp_idx << 16) + j₂` differ
    whenever `j₁ ≠ j₂`. -/
structure ForsCrossTreeNodeCollision (geom : AggSigGeometry) (pkSeed : Digest4)
    (leafGlobalIdx j₁ j₂ : Nat) where
  left1  : Digest4
  right1 : Digest4
  left2  : Digest4
  right2 : Digest4
  hashEq :
    merkleNodeHash domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx) geom.forsHeight
        ((forsKpIdx geom leafGlobalIdx <<< 16) + j₁) left1 right1 =
      merkleNodeHash domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx) geom.forsHeight
        ((forsKpIdx geom leafGlobalIdx <<< 16) + j₂) left2 right2

theorem forsTreeNodeAddr_top (geom : AggSigGeometry) (leafGlobalIdx j : Nat) :
    forsTreeNodeAddr geom leafGlobalIdx j geom.forsHeight 0 =
      (forsKpIdx geom leafGlobalIdx <<< 16) + j := by
  unfold forsTreeNodeAddr forsNodeAddr
  rw [Nat.sub_self, Nat.shiftLeft_zero, Nat.add_zero]

/-- An opening accepted with the same root in two FORS trees `j₁`, `j₂` exhibits a
    `ForsCrossTreeNodeCollision`: the two walks end in top-node hashes under the two tree
    addresses. -/
def extractForsCrossTreeCollision (geom : AggSigGeometry) (pkSeed : Digest4)
    (leafGlobalIdx j₁ j₂ idx : Nat) (op : AggForsTreeOpening) (rt : Digest4)
    (hH : 0 < geom.forsHeight)
    (h₁ : verifySingleForsOpening geom pkSeed leafGlobalIdx j₁ idx op = some rt)
    (h₂ : verifySingleForsOpening geom pkSeed leafGlobalIdx j₂ idx op = some rt) :
    ForsCrossTreeNodeCollision geom pkSeed leafGlobalIdx j₁ j₂ := by
  unfold verifySingleForsOpening at h₁ h₂
  cases hChk : (decide (idx < 2 ^ geom.forsHeight) && (op.authPath.length == geom.forsHeight))
  · exact absurd h₁ (by simp [hChk])
  · simp only [hChk, ↓reduceIte, Option.some.injEq] at h₁ h₂
    rcases Bool.and_eq_true_iff.mp hChk with ⟨hIdxLtDec, hPathLenBeq⟩
    have hIdxLt : idx < 2 ^ geom.forsHeight := of_decide_eq_true hIdxLtDec
    have hPathLen : op.authPath.length = geom.forsHeight := eq_of_beq hPathLenBeq
    have hNeNil : op.authPath ≠ [] := by
      intro hNil
      rw [hNil] at hPathLen
      exact absurd hPathLen.symm (Nat.ne_of_gt hH)
    have hTop : ∀ (j : Nat) (a b : Digest4),
        merkleAddrNodeHash domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
            (forsTreeNodeAddr geom leafGlobalIdx j)
            (1 + (op.authPath.length - 1)) (idx / 2 ^ op.authPath.length) a b =
          merkleNodeHash domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
            geom.forsHeight ((forsKpIdx geom leafGlobalIdx <<< 16) + j) a b := by
      intro j a b
      have hL : 1 + (op.authPath.length - 1) = geom.forsHeight := by
        rw [hPathLen]
        omega
      have hI : idx / 2 ^ op.authPath.length = 0 := by
        rw [hPathLen]
        exact Nat.div_eq_of_lt hIdxLt
      rw [hL, hI]
      unfold merkleAddrNodeHash
      rw [forsTreeNodeAddr_top]
    let t1 := merkleWalkPolyTopNode
      (merkleAddrNodeHash domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
        (forsTreeNodeAddr geom leafGlobalIdx j₁))
      op.authPath 1 idx (forsLeafHash geom pkSeed op.secretVal leafGlobalIdx j₁ idx) hNeNil
    let t2 := merkleWalkPolyTopNode
      (merkleAddrNodeHash domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
        (forsTreeNodeAddr geom leafGlobalIdx j₂))
      op.authPath 1 idx (forsLeafHash geom pkSeed op.secretVal leafGlobalIdx j₂ idx) hNeNil
    exact
      { left1 := t1.1.1, right1 := t1.1.2, left2 := t2.1.1, right2 := t2.1.2
        hashEq := (hTop j₁ _ _).symm.trans
          ((t1.2.symm.trans h₁).trans ((t2.2.symm.trans h₂).symm.trans (hTop j₂ _ _))) }

/-- **`#tooth`: cross-FORS-tree node transplant.** With `j₁ ≠ j₂` the top-node addresses of
    the two trees differ, and an opening accepted in tree `j₁` is rejected in tree `j₂` unless
    the two differently-addressed top-node hashes collide. -/
theorem tooth_fors_cross_tree_transplant_rejected (geom : AggSigGeometry) (pkSeed : Digest4)
    (leafGlobalIdx j₁ j₂ idx : Nat) (op : AggForsTreeOpening) (rt : Digest4)
    (hH : 0 < geom.forsHeight) (hNe : j₁ ≠ j₂)
    (hNoCol : ForsCrossTreeNodeCollision geom pkSeed leafGlobalIdx j₁ j₂ → False)
    (h₁ : verifySingleForsOpening geom pkSeed leafGlobalIdx j₁ idx op = some rt) :
    forsTreeNodeAddr geom leafGlobalIdx j₁ geom.forsHeight 0 ≠
        forsTreeNodeAddr geom leafGlobalIdx j₂ geom.forsHeight 0 ∧
      verifySingleForsOpening geom pkSeed leafGlobalIdx j₂ idx op ≠ some rt := by
  refine ⟨?_, fun h₂ =>
    hNoCol (extractForsCrossTreeCollision geom pkSeed leafGlobalIdx j₁ j₂ idx op rt hH h₁ h₂)⟩
  rw [forsTreeNodeAddr_top, forsTreeNodeAddr_top]
  exact fun h => hNe (Nat.add_left_cancel h)

@[expose] def verifyUpperPoly {LS D : Type} (step : Nat → Nat → D → LS → Option (Nat × D)) :
    List LS → Nat → Nat → D → Option D
  | [], _, _, curRoot => some curRoot
  | lsig :: rest, layer, remTreeIdx, curRoot =>
    match step layer remTreeIdx curRoot lsig with
    | none => none
    | some (nextRem, nextRoot) => verifyUpperPoly step rest (layer + 1) nextRem nextRoot

/-- Walk upper hypertree layers `startLayer .. startLayer + remLayers - 1` from `curChildRoot`. -/
@[expose] def verifyUpperLayers (geom : AggSigGeometry) (pk : AggValidatorPk)
    (layer remTreeIdx : Nat) (curRoot : Digest4) (ls : List WotsLayerSig) : Option Digest4 :=
  verifyUpperPoly
    (fun l rem cur lsig =>
      let kpIdx := rem % (2 ^ geom.subtreeHeight)
      let treeIdx := rem / (2 ^ geom.subtreeHeight)
      let hmsg := computeHmsgDetTree pk l treeIdx kpIdx lsig.tswCtr cur
      match verifyWotsLayer geom pk l treeIdx kpIdx hmsg lsig with
      | none => none
      | some nextRoot => some (treeIdx, nextRoot))
    ls layer remTreeIdx curRoot

@[expose] def verifyAggNativeSigStateful (geom : AggSigGeometry) (pk : AggValidatorPk)
    (mu : Digest5) (sig : AggNativeSignature) (lsig0 : WotsLayerSig) (upperLayers : List WotsLayerSig) : Bool :=
  if !sig.forsOpenings.isEmpty ||
     !(sig.statefulLeafIdx < 2 ^ (geom.numLayers * geom.subtreeHeight)) then
    false
  else
    let kpIdx0 := sig.statefulLeafIdx % (2 ^ geom.subtreeHeight)
    let treeIdx0 := sig.statefulLeafIdx / (2 ^ geom.subtreeHeight)
    let hmsg0 := computeHmsgStateful pk sig.rRand mu kpIdx0 lsig0.tswCtr
    match verifyWotsLayer geom pk 0 treeIdx0 kpIdx0 hmsg0 lsig0 with
    | none => false
    | some root0 =>
      match verifyUpperLayers geom pk 1 treeIdx0 root0 upperLayers with
      | none => false
      | some topRoot => topRoot == pk.pkRoot

def evalStatelessFlow {Idx Ops FPk R0 Rt : Type}
    (statefulNz : Bool)
    (xofRes : Option (Idx × Ops))
    (verFors : Idx → Ops → Option FPk)
    (verLayer0 : Idx → FPk → Option R0)
    (verUpper : Idx → R0 → Option Rt)
    (checkTop : Rt → Bool) : Bool :=
  if statefulNz then false
  else match xofRes with
  | none => false
  | some pair =>
    match verFors pair.1 pair.2 with
    | none => false
    | some fpk =>
      match verLayer0 pair.1 fpk with
      | none => false
      | some r0 =>
        match verUpper pair.1 r0 with
        | none => false
        | some top => checkTop top

theorem evalStatelessFlow_ok {Idx Ops FPk R0 Rt : Type}
    (xofRes : Option (Idx × Ops))
    (verFors : Idx → Ops → Option FPk)
    (verLayer0 : Idx → FPk → Option R0)
    (verUpper : Idx → R0 → Option Rt)
    (checkTop : Rt → Bool)
    (idx : Idx) (ops : Ops) (fpk : FPk) (r0 : R0) (top : Rt)
    (hXof : xofRes = some (idx, ops))
    (hFors : verFors idx ops = some fpk)
    (hL0 : verLayer0 idx fpk = some r0)
    (hUp : verUpper idx r0 = some top)
    (hTop : checkTop top = true) :
    evalStatelessFlow false xofRes verFors verLayer0 verUpper checkTop = true := by
  subst hXof
  simp only [evalStatelessFlow, Bool.false_eq_true, ↓reduceIte, hFors, hL0, hUp]
  exact hTop

structure StatelessFlowUnpack {Idx Ops FPk R0 Rt : Type}
    (statefulNz : Bool)
    (xofRes : Option (Idx × Ops))
    (verFors : Idx → Ops → Option FPk)
    (verLayer0 : Idx → FPk → Option R0)
    (verUpper : Idx → R0 → Option Rt)
    (checkTop : Rt → Bool) where
  idx   : Idx
  ops   : Ops
  fpk   : FPk
  r0    : R0
  top   : Rt
  hNz   : statefulNz = false
  hXof  : xofRes = some (idx, ops)
  hFors : verFors idx ops = some fpk
  hL0   : verLayer0 idx fpk = some r0
  hUp   : verUpper idx r0 = some top
  hTop  : checkTop top = true

def unpackStatelessFlow {Idx Ops FPk R0 Rt : Type}
    {statefulNz : Bool}
    {xofRes : Option (Idx × Ops)}
    {verFors : Idx → Ops → Option FPk}
    {verLayer0 : Idx → FPk → Option R0}
    {verUpper : Idx → R0 → Option Rt}
    {checkTop : Rt → Bool}
    (hOk : evalStatelessFlow statefulNz xofRes verFors verLayer0 verUpper checkTop = true) :
    StatelessFlowUnpack statefulNz xofRes verFors verLayer0 verUpper checkTop := by
  cases hNz : statefulNz
  · simp only [evalStatelessFlow, hNz, Bool.false_eq_true, ↓reduceIte] at hOk
    cases hXof : xofRes with
    | none => simp [hXof] at hOk
    | some pair =>
      rcases pair with ⟨idx, ops⟩
      simp only [hXof] at hOk
      cases hFors : verFors idx ops with
      | none => simp [hFors] at hOk
      | some fpk =>
        simp only [hFors] at hOk
        cases hL0 : verLayer0 idx fpk with
        | none => simp [hL0] at hOk
        | some r0 =>
          simp only [hL0] at hOk
          cases hUp : verUpper idx r0 with
          | none => simp [hUp] at hOk
          | some top =>
            simp only [hUp] at hOk
            exact ⟨idx, ops, fpk, r0, top, rfl, rfl, hFors, hL0, hUp, hOk⟩
  · simp [evalStatelessFlow, hNz] at hOk

@[expose] def verifyAggNativeSigStateless (geom : AggSigGeometry) (pk : AggValidatorPk)
    (mu : Digest5) (sig : AggNativeSignature) (lsig0 : WotsLayerSig) (upperLayers : List WotsLayerSig) : Bool :=
  evalStatelessFlow
    (sig.statefulLeafIdx != 0)
    (deriveStatelessLeafAndForsChecked geom pk sig.rRand mu)
    (fun leafGlobalIdx forsIndices =>
      verifyAndRecoverForsPk geom pk.pkSeed leafGlobalIdx forsIndices sig.forsOpenings)
    (fun leafGlobalIdx forsPk =>
      let kpIdx0 := leafGlobalIdx % (2 ^ geom.subtreeHeight)
      let treeIdx0 := leafGlobalIdx / (2 ^ geom.subtreeHeight)
      let hmsg0 := computeHmsgDetTree pk 0 treeIdx0 kpIdx0 lsig0.tswCtr forsPk
      verifyWotsLayer geom pk 0 treeIdx0 kpIdx0 hmsg0 lsig0)
    (fun leafGlobalIdx root0 =>
      verifyUpperLayers geom pk 1 (leafGlobalIdx / 2 ^ geom.subtreeHeight) root0 upperLayers)
    (fun topRoot => topRoot == pk.pkRoot)

/-- Full standalone verifier for `AggNativeSignature` (`verify_individual_signature` in `sig.rs`). -/
@[expose] def verifyAggNativeSig (geom : AggSigGeometry) (pk : AggValidatorPk)
    (msg : List UInt8) (sig : AggNativeSignature) : Bool :=
  if !geom.wellFormed || pk.profile != geom.profile || sig.profile != geom.profile ||
     sig.layers.length != geom.numLayers then
    false
  else
    let mu := computeMessageMu pk msg
    match sig.layers with
    | [] => false
    | lsig0 :: upperLayers =>
      if geom.forsTrees == 0 then
        verifyAggNativeSigStateful geom pk mu sig lsig0 upperLayers
      else
        verifyAggNativeSigStateless geom pk mu sig lsig0 upperLayers

/-- Sign a single WOTS+C + XMSS subtree layer given valid target-sum `digits` (`digits.length = geom.wotsChains`). -/
def signWotsLayerWithDigits (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (layer treeIdx kpIdx tswCtr : Nat) (digits : List Nat) : WotsLayerSig :=
  let chains := (List.range digits.length).map fun c =>
    wotsChainWalk pkSeed layer treeIdx kpIdx c 0 (digits[c]!)
      (wotsSecretStart skSeed pkSeed layer treeIdx kpIdx c)
  let path := buildMerkleAuthPathAt domainMerkleNode pkSeed layer treeIdx xmssNodeAddr
    (honestWotsPk geom skSeed pkSeed layer treeIdx) geom.subtreeHeight 1 kpIdx
  { tswCtr := tswCtr, wotsChains := chains, merklePath := path }

@[simp] private theorem signWotsLayerWithDigits_tswCtr (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (layer treeIdx kpIdx tswCtr : Nat) (digits : List Nat) :
    (signWotsLayerWithDigits geom skSeed pkSeed layer treeIdx kpIdx tswCtr digits).tswCtr = tswCtr :=
  rfl

attribute [local irreducible] forsSecretVal forsLeafHash forsLeafTweak4 compressForsRootsSponge statelessXofSpongeState

/-- Witness bundle of pre-searched `tsw_ctr` counters whose extracted base-4 digits hit `geom.targetSum`. -/
structure ValidSigningCtrs (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (msg : List UInt8) (rRand : Digest4) (statefulLeafIdx : Nat) where
  layer0Ctr    : Nat
  upperCtrs    : List Nat
  lenUpper     : upperCtrs.length + 1 = geom.numLayers
  leafInRange  : geom.forsTrees = 0 → statefulLeafIdx < 2 ^ (geom.numLayers * geom.subtreeHeight)
  statelessZero : geom.forsTrees ≠ 0 → statefulLeafIdx = 0
  statelessXofOk : geom.forsTrees ≠ 0 →
    deriveStatelessLeafAndForsChecked geom pk rRand (computeMessageMu pk msg) ≠ none
  layer0Valid  :
    let mu := computeMessageMu pk msg
    let leafIdx :=
      if geom.forsTrees == 0 then statefulLeafIdx
      else match deriveStatelessLeafAndForsChecked geom pk rRand mu with
           | some pair => pair.1
           | none => 0
    let kp0 := leafIdx % (2 ^ geom.subtreeHeight)
    let tr0 := leafIdx / (2 ^ geom.subtreeHeight)
    let hmsg0 :=
      if geom.forsTrees == 0 then computeHmsgStateful pk rRand mu kp0 layer0Ctr
      else computeHmsgDetTree pk 0 tr0 kp0 layer0Ctr (honestForsPk geom skSeed pk.pkSeed leafIdx)
    ∃ ds0, extractWotsDigitsChecked geom hmsg0 = some ds0 ∧ listNatSum ds0 = geom.targetSum
  upperValid   :
    let mu := computeMessageMu pk msg
    let leafIdx :=
      if geom.forsTrees == 0 then statefulLeafIdx
      else match deriveStatelessLeafAndForsChecked geom pk rRand mu with
           | some pair => pair.1
           | none => 0
    ∀ (j : Nat) (hj : j < upperCtrs.length),
      let l := j + 1
      let remIdx := leafIdx / (2 ^ (l * geom.subtreeHeight))
      let kpL := remIdx % (2 ^ geom.subtreeHeight)
      let trL := remIdx / (2 ^ geom.subtreeHeight)
      let childRt := honestSubtreeRoot geom skSeed pk.pkSeed j remIdx
      let hmsgL := computeHmsgDetTree pk l trL kpL (upperCtrs[j]'hj) childRt
      ∃ dsL, extractWotsDigitsChecked geom hmsgL = some dsL ∧ listNatSum dsL = geom.targetSum

private def signUpperPoly {LS : Type} (step : Nat → Nat → Nat → (Nat × LS)) :
    List Nat → Nat → Nat → List LS
  | [], _, _ => []
  | ctr :: rest, layer, remTreeIdx =>
    let (treeIdx, lsig) := step layer remTreeIdx ctr
    lsig :: signUpperPoly step rest (layer + 1) treeIdx

private theorem signUpperPoly_length {LS : Type} (step : Nat → Nat → Nat → (Nat × LS)) :
    ∀ (cs : List Nat) (layer remIdx : Nat),
      (signUpperPoly step cs layer remIdx).length = cs.length
  | [], _, _ => rfl
  | _ :: rest, layer, remIdx => by
    dsimp only [signUpperPoly]
    rw [List.length_cons, signUpperPoly_length step rest]
    rfl

private def signUpperLayersAux (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (layer remTreeIdx : Nat) (cs : List Nat) : List WotsLayerSig :=
  signUpperPoly
    (fun l rem ctr =>
      let kpIdx := rem % (2 ^ geom.subtreeHeight)
      let treeIdx := rem / (2 ^ geom.subtreeHeight)
      let childRt := honestSubtreeRoot geom skSeed pk.pkSeed (l - 1) rem
      let hmsg := computeHmsgDetTree pk l treeIdx kpIdx ctr childRt
      let digits := (extractWotsDigitsChecked geom hmsg).getD []
      (treeIdx, signWotsLayerWithDigits geom skSeed pk.pkSeed l treeIdx kpIdx ctr digits))
    cs layer remTreeIdx

private def signForsPoly {OP : Type} (step : Nat → Nat → OP) :
    List Nat → Nat → List OP
  | [], _ => []
  | off :: offs, t => step t off :: signForsPoly step offs (t + 1)

private theorem signForsPoly_length {OP : Type} (step : Nat → Nat → OP) :
    ∀ (offs : List Nat) (t : Nat), (signForsPoly step offs t).length = offs.length
  | [], _ => rfl
  | _ :: offs, t => by
    dsimp only [signForsPoly]
    rw [List.length_cons, signForsPoly_length step offs (t + 1)]
    rfl

/-- Sign all FORS openings at `leafGlobalIdx` for `indices`. -/
def signForsTreesAux (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (leafGlobalIdx startT : Nat) (offs : List Nat) : List AggForsTreeOpening :=
  signForsPoly
    (fun t off =>
      let sec := forsSecretVal geom skSeed pkSeed leafGlobalIdx t off
      let path := buildMerkleAuthPathAt domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
        (forsTreeNodeAddr geom leafGlobalIdx t)
        (honestForsLeaf geom skSeed pkSeed leafGlobalIdx t)
        geom.forsHeight 1 off
      { secretVal := sec, authPath := path })
    offs startT

/-- Honest `AggNativeSignature` constructor matching `sign_stateful` / `sign_stateless` in `sig.rs`. -/
def signAggNative (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (msg : List UInt8) (rRand : Digest4) (statefulLeafIdx : Nat)
    (layer0Ctr : Nat) (upperCtrs : List Nat) : AggNativeSignature :=
  let mu := computeMessageMu pk msg
  let (leafIdx, forsOps) :=
    if geom.forsTrees == 0 then
      (statefulLeafIdx, [])
    else
      match deriveStatelessLeafAndForsChecked geom pk rRand mu with
      | none => (0, [])
      | some pair =>
        (pair.1, signForsTreesAux geom skSeed pk.pkSeed pair.1 0 pair.2)
  let kp0 := leafIdx % (2 ^ geom.subtreeHeight)
  let tr0 := leafIdx / (2 ^ geom.subtreeHeight)
  let hmsg0 :=
    if geom.forsTrees == 0 then computeHmsgStateful pk rRand mu kp0 layer0Ctr
    else computeHmsgDetTree pk 0 tr0 kp0 layer0Ctr (honestForsPk geom skSeed pk.pkSeed leafIdx)
  let digits0 := (extractWotsDigitsChecked geom hmsg0).getD []
  let lsig0 := signWotsLayerWithDigits geom skSeed pk.pkSeed 0 tr0 kp0 layer0Ctr digits0
  let upper := signUpperLayersAux geom skSeed pk 1 tr0 upperCtrs
  { profile         := geom.profile
    rRand           := rRand
    statefulLeafIdx := if geom.forsTrees == 0 then statefulLeafIdx else 0
    forsOpenings    := forsOps
    layers          := lsig0 :: upper }

private theorem verifyWotsLayer_signWotsLayerWithDigits
    (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (hChainsLe : geom.wotsChains ≤ 128)
    (layer treeIdx kpIdx tswCtr : Nat)
    (hKpLt : kpIdx < 2 ^ geom.subtreeHeight)
    (hmsg : Digest5) (digits : List Nat)
    (hExt : extractWotsDigitsChecked geom hmsg = some digits)
    (hSum : listNatSum digits = geom.targetSum) :
    verifyWotsLayer geom pk layer treeIdx kpIdx hmsg
      (signWotsLayerWithDigits geom skSeed pk.pkSeed layer treeIdx kpIdx tswCtr digits) =
    some (honestSubtreeRoot geom skSeed pk.pkSeed layer treeIdx) := by
  obtain ⟨hLenD, hLt4⟩ := extractWotsDigitsChecked_spec hChainsLe hExt
  unfold verifyWotsLayer signWotsLayerWithDigits
  have hChainsLen :
      ((List.range digits.length).map fun c =>
        wotsChainWalk pk.pkSeed layer treeIdx kpIdx c 0 (digits[c]!)
          (wotsSecretStart skSeed pk.pkSeed layer treeIdx kpIdx c)).length = geom.wotsChains := by
    rw [List.length_map, List.length_range, hLenD]
  have hPathLen :
      (buildMerkleAuthPathAt domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr
        (honestWotsPk geom skSeed pk.pkSeed layer treeIdx) geom.subtreeHeight 1 kpIdx).length =
      geom.subtreeHeight :=
    buildMerkleAuthPathAt_length _ _ _ _ _ _ _ _ _
  simp only [hChainsLen, hPathLen, beq_self_eq_true, Bool.and_self, ↓reduceIte, hExt, hSum]
  have hZeroMap :
      ((List.range digits.length).map fun c =>
        wotsChainWalk pk.pkSeed layer treeIdx kpIdx c 0 (digits[c]!)
          (wotsSecretStart skSeed pk.pkSeed layer treeIdx kpIdx c)) =
      ((List.range digits.length).map fun i =>
        wotsChainWalk pk.pkSeed layer treeIdx kpIdx (0 + i) 0 (digits[i]!)
          (wotsSecretStart skSeed pk.pkSeed layer treeIdx kpIdx (0 + i))) := by
    congr 1; funext i; simp
  rw [hZeroMap, recoverAggWotsEndpoints_honest pk.pkSeed skSeed layer treeIdx kpIdx digits 0 hLt4]
  simp only [Nat.zero_add]
  have hEpEq :
      ((List.range digits.length).map fun i =>
        wotsChainWalk pk.pkSeed layer treeIdx kpIdx i 0 3
          (wotsSecretStart skSeed pk.pkSeed layer treeIdx kpIdx i)) =
      honestWotsEndpoints geom skSeed pk.pkSeed layer treeIdx kpIdx := by
    unfold honestWotsEndpoints
    rw [hLenD]
  rw [hEpEq]
  have hWotsEq :
      compressWotsEndpointsSponge pk.pkSeed layer treeIdx kpIdx
        (honestWotsEndpoints geom skSeed pk.pkSeed layer treeIdx kpIdx) =
      honestWotsPk geom skSeed pk.pkSeed layer treeIdx kpIdx := rfl
  rw [hWotsEq]
  rw [merkleWalkRoot_buildMerkleAuthPathAt domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr
        geom.subtreeHeight (honestWotsPk geom skSeed pk.pkSeed layer treeIdx) 1 kpIdx hKpLt]
  rfl

private theorem signUpperLayersAux_length (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (layer remIdx : Nat) (ctrs : List Nat) :
    (signUpperLayersAux geom skSeed pk layer remIdx ctrs).length = ctrs.length :=
  signUpperPoly_length _ ctrs layer remIdx

private theorem verifyUpperPoly_signUpperPoly {LS D : Type}
    (vStep : Nat → Nat → D → LS → Option (Nat × D))
    (sStep : Nat → Nat → Nat → (Nat × LS))
    (rootAt : Nat → Nat → D)
    (subH : Nat) :
    ∀ (ctrs : List Nat) (startLayer remIdx : Nat),
      0 < startLayer →
      (∀ (j : Nat) (hj : j < ctrs.length),
        let l := startLayer + j
        let curRem := remIdx / (2 ^ (j * subH))
        let (trOut, lsig) := sStep l curRem (ctrs[j]'hj)
        trOut = curRem / (2 ^ subH) ∧
        vStep l curRem (rootAt (l - 1) curRem) lsig =
          some (curRem / (2 ^ subH), rootAt l (curRem / (2 ^ subH)))) →
      verifyUpperPoly vStep (signUpperPoly sStep ctrs startLayer remIdx) startLayer remIdx
        (rootAt (startLayer - 1) remIdx) =
      some (rootAt (startLayer + ctrs.length - 1) (remIdx / (2 ^ (ctrs.length * subH))))
  | [], startLayer, remIdx, _, _ => by
    dsimp only [signUpperPoly, verifyUpperPoly]
    simp only [List.length_nil, Nat.add_zero, Nat.zero_mul, Nat.pow_zero, Nat.div_one]
  | ctr :: rest, startLayer, remIdx, hPos, hValid => by
    dsimp only [signUpperPoly]
    have h0 := hValid 0 (Nat.zero_lt_succ _)
    simp only [Nat.add_zero, Nat.zero_mul, Nat.pow_zero, Nat.div_one, List.getElem_cons_zero] at h0
    obtain ⟨tr0, lsig0, hs0⟩ : ∃ tr0 lsig0, sStep startLayer remIdx ctr = (tr0, lsig0) := ⟨_, _, rfl⟩
    simp only [hs0, verifyUpperPoly] at h0 ⊢
    rcases h0 with ⟨hTr0, hv0⟩
    rw [hTr0, hv0]
    dsimp only
    have hNextSub :
        rootAt startLayer (remIdx / 2 ^ subH) = rootAt ((startLayer + 1) - 1) (remIdx / 2 ^ subH) :=
      congrArg (fun l => rootAt l (remIdx / 2 ^ subH)) (Nat.add_sub_cancel startLayer 1).symm
    rw [hNextSub]
    have hRestValid :
        ∀ (j : Nat) (hj : j < rest.length),
          let l := (startLayer + 1) + j
          let curRem := (remIdx / 2 ^ subH) / (2 ^ (j * subH))
          let (trOut, lsig) := sStep l curRem (rest[j]'hj)
          trOut = curRem / (2 ^ subH) ∧
          vStep l curRem (rootAt (l - 1) curRem) lsig =
            some (curRem / (2 ^ subH), rootAt l (curRem / (2 ^ subH))) := by
      intro j hj
      have hStep := hValid (j + 1) (Nat.succ_lt_succ hj)
      have hL : startLayer + (j + 1) = (startLayer + 1) + j := by omega
      have hDivEq :
          (remIdx / 2 ^ subH) / (2 ^ (j * subH)) = remIdx / (2 ^ ((j + 1) * subH)) := by
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
        have hExp : subH + j * subH = (j + 1) * subH := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
        rw [hExp]
      simpa only [hL, hDivEq, List.getElem_cons_succ] using hStep
    rw [verifyUpperPoly_signUpperPoly vStep sStep rootAt subH rest
          (startLayer + 1) (remIdx / 2 ^ subH) (by omega) hRestValid]
    have hEndL : (startLayer + 1) + rest.length - 1 = startLayer + (ctr :: rest).length - 1 := by
      simp only [List.length_cons]; omega
    have hEndRem :
        (remIdx / 2 ^ subH) / (2 ^ (rest.length * subH)) =
        remIdx / (2 ^ ((ctr :: rest).length * subH)) := by
      simp only [List.length_cons]
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
      have hExp : subH + rest.length * subH = (rest.length + 1) * subH := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      rw [hExp]
    rw [hEndL, hEndRem]

private theorem verifyUpperLayers_signUpperLayersAux
    (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (hChainsLe : geom.wotsChains ≤ 128)
    (ctrs : List Nat) (startLayer remIdx : Nat)
    (hPos : 0 < startLayer)
    (hValid : ∀ (j : Nat) (hj : j < ctrs.length),
      let l := startLayer + j
      let curRem := remIdx / (2 ^ (j * geom.subtreeHeight))
      let kpL := curRem % (2 ^ geom.subtreeHeight)
      let trL := curRem / (2 ^ geom.subtreeHeight)
      let childRt := honestSubtreeRoot geom skSeed pk.pkSeed (l - 1) curRem
      let hmsgL := computeHmsgDetTree pk l trL kpL (ctrs[j]'hj) childRt
      ∃ dsL, extractWotsDigitsChecked geom hmsgL = some dsL ∧ listNatSum dsL = geom.targetSum) :
    verifyUpperLayers geom pk startLayer remIdx
      (honestSubtreeRoot geom skSeed pk.pkSeed (startLayer - 1) remIdx)
      (signUpperLayersAux geom skSeed pk startLayer remIdx ctrs) =
    some (honestSubtreeRoot geom skSeed pk.pkSeed (startLayer + ctrs.length - 1)
            (remIdx / (2 ^ (ctrs.length * geom.subtreeHeight)))) := by
  unfold verifyUpperLayers signUpperLayersAux
  refine verifyUpperPoly_signUpperPoly _ _ (honestSubtreeRoot geom skSeed pk.pkSeed)
    geom.subtreeHeight ctrs startLayer remIdx hPos ?_
  intro j hj
  obtain ⟨dsL, hExtL, hSumL⟩ := hValid j hj
  dsimp only
  refine ⟨rfl, ?_⟩
  have hGetD :
      (extractWotsDigitsChecked geom
        (computeHmsgDetTree pk (startLayer + j)
          ((remIdx / 2 ^ (j * geom.subtreeHeight)) / 2 ^ geom.subtreeHeight)
          ((remIdx / 2 ^ (j * geom.subtreeHeight)) % 2 ^ geom.subtreeHeight)
          (ctrs[j]'hj)
          (honestSubtreeRoot geom skSeed pk.pkSeed (startLayer + j - 1)
            (remIdx / 2 ^ (j * geom.subtreeHeight))))).getD [] = dsL := by
    rw [hExtL]; rfl
  rw [hGetD, signWotsLayerWithDigits_tswCtr]
  have hKpLt :
      (remIdx / 2 ^ (j * geom.subtreeHeight)) % (2 ^ geom.subtreeHeight) < 2 ^ geom.subtreeHeight :=
    Nat.mod_lt _ (Nat.pow_pos (by decide))
  rw [verifyWotsLayer_signWotsLayerWithDigits geom skSeed pk hChainsLe
        (startLayer + j)
        ((remIdx / 2 ^ (j * geom.subtreeHeight)) / 2 ^ geom.subtreeHeight)
        ((remIdx / 2 ^ (j * geom.subtreeHeight)) % 2 ^ geom.subtreeHeight)
        (ctrs[j]'hj) hKpLt _ dsL hExtL hSumL]

private theorem signForsTreesAux_length (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (leafGlobalIdx t : Nat) (offs : List Nat) :
    (signForsTreesAux geom skSeed pkSeed leafGlobalIdx t offs).length = offs.length :=
  signForsPoly_length _ offs t

private theorem verifyForsPoly_signForsPoly {OP D : Type}
    (vStep : Nat → Nat → OP → Option D)
    (sStep : Nat → Nat → OP)
    (rootAt : Nat → D) :
    ∀ (offs : List Nat) (startT : Nat),
      (∀ off ∈ offs, ∀ t, vStep t off (sStep t off) = some (rootAt t)) →
      verifyForsPoly vStep offs (signForsPoly sStep offs startT) startT =
      some ((List.range offs.length).map fun i => rootAt (startT + i))
  | [], _ => fun _ => rfl
  | off :: offs, startT => fun hStep => by
    dsimp only [signForsPoly, verifyForsPoly]
    rw [hStep off (List.mem_cons_self ..) startT]
    rw [verifyForsPoly_signForsPoly vStep sStep rootAt offs (startT + 1)
          (fun o ho => hStep o (List.mem_cons_of_mem _ ho))]
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, Nat.add_zero]
    simp only [Option.some.injEq, List.cons.injEq]
    refine ⟨rfl, ?_⟩
    rw [List.map_map]
    congr 1
    funext i
    have hShift : startT + (i + 1) = startT + 1 + i := by omega
    simp [Function.comp, hShift]

private theorem verifyForsTreesAux_signForsTreesAux
    (geom : AggSigGeometry) (skSeed pkSeed : Digest4) (leafGlobalIdx : Nat)
    (offs : List Nat) (startT : Nat)
    (hLt : ∀ o ∈ offs, o < 2 ^ geom.forsHeight) :
    verifyForsTreesAux geom pkSeed leafGlobalIdx startT offs
      (signForsTreesAux geom skSeed pkSeed leafGlobalIdx startT offs) =
    some ((List.range offs.length).map fun i =>
      honestForsTreeRoot geom skSeed pkSeed leafGlobalIdx (startT + i)) := by
  unfold verifyForsTreesAux signForsTreesAux
  refine verifyForsPoly_signForsPoly _ _
    (honestForsTreeRoot geom skSeed pkSeed leafGlobalIdx) offs startT ?_
  intro off ho t
  have hOffLt : off < 2 ^ geom.forsHeight := hLt off ho
  dsimp only [verifySingleForsOpening]
  have hPathLen :
      (buildMerkleAuthPathAt domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
        (forsTreeNodeAddr geom leafGlobalIdx t)
        (honestForsLeaf geom skSeed pkSeed leafGlobalIdx t)
        geom.forsHeight 1 off).length = geom.forsHeight :=
    buildMerkleAuthPathAt_length _ _ _ _ _ _ _ _ _
  simp only [hOffLt, decide_true, hPathLen, beq_self_eq_true, Bool.and_self, ↓reduceIte]
  exact congrArg some
    (merkleWalkRoot_buildMerkleAuthPathAt domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
      (forsTreeNodeAddr geom leafGlobalIdx t) geom.forsHeight
      (honestForsLeaf geom skSeed pkSeed leafGlobalIdx t) 1 off hOffLt)

attribute [local irreducible]
  honestSubtreeRoot honestForsTreeRoot verifyWotsLayer signWotsLayerWithDigits
  verifyUpperLayers signUpperLayersAux verifyForsTreesAux signForsTreesAux

private theorem deriveStatelessLeafAndForsChecked_spec
    {geom : AggSigGeometry} {pk : AggValidatorPk} {rRand : Digest4} {mu : Digest5}
    {leafIdx : Nat} {indices : List Nat}
    (hExt : deriveStatelessLeafAndForsChecked geom pk rRand mu = some (leafIdx, indices)) :
    leafIdx < 2 ^ (geom.numLayers * geom.subtreeHeight) ∧
    indices.length = geom.forsTrees ∧
    (∀ idx ∈ indices, idx < 2 ^ geom.forsHeight) := by
  unfold deriveStatelessLeafAndForsChecked at hExt
  generalize statelessXofSpongeState pk rRand mu = st1 at hExt
  dsimp only at hExt
  cases hAll : ([st1.b0.x0, st1.b0.x1, st1.b0.x2, st1.b0.x3, st1.b1.x0, st1.b1.x1, st1.b1.x2].all
      (fun l => decide (l.val < 2 ^ 63)))
  · simp [hAll] at hExt
  · simp only [hAll, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hExt
    rcases hExt with ⟨hL, hI⟩
    subst hL hI
    refine ⟨Nat.mod_lt _ (Nat.pow_pos (by decide)), by simp, ?_⟩
    intro idx hMem
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hMem
    exact Nat.mod_lt _ (Nat.pow_pos (by decide))

attribute [local irreducible] deriveStatelessLeafAndForsChecked honestForsPk computeMessageMu

private theorem signAggNative_profile
    (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (msg : List UInt8) (rRand : Digest4) (statefulLeafIdx layer0Ctr : Nat) (upperCtrs : List Nat) :
    (signAggNative geom skSeed pk msg rRand statefulLeafIdx layer0Ctr upperCtrs).profile = geom.profile :=
  rfl

private theorem signAggNative_layers_length
    (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (msg : List UInt8) (rRand : Digest4) (statefulLeafIdx layer0Ctr : Nat) (upperCtrs : List Nat) :
    (signAggNative geom skSeed pk msg rRand statefulLeafIdx layer0Ctr upperCtrs).layers.length =
      upperCtrs.length + 1 := by
  unfold signAggNative
  dsimp only
  rw [List.length_cons, signUpperLayersAux_length]

private theorem signAggNative_stateful_eq
    (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (msg : List UInt8) (rRand : Digest4) (statefulLeafIdx layer0Ctr : Nat) (upperCtrs : List Nat)
    (hFors0 : (geom.forsTrees == 0) = true) :
    signAggNative geom skSeed pk msg rRand statefulLeafIdx layer0Ctr upperCtrs =
      let mu := computeMessageMu pk msg
      let kp0 := statefulLeafIdx % (2 ^ geom.subtreeHeight)
      let tr0 := statefulLeafIdx / (2 ^ geom.subtreeHeight)
      let hmsg0 := computeHmsgStateful pk rRand mu kp0 layer0Ctr
      let digits0 := (extractWotsDigitsChecked geom hmsg0).getD []
      { profile := geom.profile
        rRand := rRand
        statefulLeafIdx := statefulLeafIdx
        forsOpenings := []
        layers := signWotsLayerWithDigits geom skSeed pk.pkSeed 0 tr0 kp0 layer0Ctr digits0 ::
                  signUpperLayersAux geom skSeed pk 1 tr0 upperCtrs } := by
  unfold signAggNative
  simp only [hFors0, ↓reduceIte]

private theorem signAggNative_stateless_eq
    (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (msg : List UInt8) (rRand : Digest4) (statefulLeafIdx layer0Ctr : Nat) (upperCtrs : List Nat)
    (idx : Nat) (forsIndices : List Nat)
    (hFors0 : (geom.forsTrees == 0) = false)
    (hXof : deriveStatelessLeafAndForsChecked geom pk rRand (computeMessageMu pk msg) = some (idx, forsIndices)) :
    signAggNative geom skSeed pk msg rRand statefulLeafIdx layer0Ctr upperCtrs =
      let kp0 := idx % (2 ^ geom.subtreeHeight)
      let tr0 := idx / (2 ^ geom.subtreeHeight)
      let hmsg0 := computeHmsgDetTree pk 0 tr0 kp0 layer0Ctr (honestForsPk geom skSeed pk.pkSeed idx)
      let digits0 := (extractWotsDigitsChecked geom hmsg0).getD []
      { profile := geom.profile
        rRand := rRand
        statefulLeafIdx := 0
        forsOpenings := signForsTreesAux geom skSeed pk.pkSeed idx 0 forsIndices
        layers := signWotsLayerWithDigits geom skSeed pk.pkSeed 0 tr0 kp0 layer0Ctr digits0 ::
                  signUpperLayersAux geom skSeed pk 1 tr0 upperCtrs } := by
  unfold signAggNative
  simp only [hFors0, Bool.false_eq_true, ↓reduceIte, hXof]

attribute [local irreducible] signAggNative

private theorem honestForsPk_def (geom : AggSigGeometry) (skSeed pkSeed : Digest4) (leafGlobalIdx : Nat) :
    compressForsRootsSponge geom pkSeed leafGlobalIdx
      ((List.range geom.forsTrees).map fun i => honestForsTreeRoot geom skSeed pkSeed leafGlobalIdx i) =
    honestForsPk geom skSeed pkSeed leafGlobalIdx := by
  unfold honestForsPk
  rfl

attribute [local irreducible] verifyAggNativeSigStateful verifyAggNativeSigStateless verifyAndRecoverForsPk

theorem verifyAggNativeSig_stateful_of_ok
    (geom : AggSigGeometry) (pk : AggValidatorPk) (msg : List UInt8) (rRand : Digest4)
    (statefulLeafIdx : Nat) (lsig0 : WotsLayerSig) (upperLayers : List WotsLayerSig)
    (root0 : Digest4)
    (hWf : geom.wellFormed = true)
    (hPkProf : pk.profile = geom.profile)
    (hLen : upperLayers.length + 1 = geom.numLayers)
    (hFors0 : (geom.forsTrees == 0) = true)
    (hLeafLt : statefulLeafIdx < 2 ^ (geom.numLayers * geom.subtreeHeight))
    (hW0 : verifyWotsLayer geom pk 0 (statefulLeafIdx / 2 ^ geom.subtreeHeight)
             (statefulLeafIdx % 2 ^ geom.subtreeHeight)
             (computeHmsgStateful pk rRand (computeMessageMu pk msg)
               (statefulLeafIdx % 2 ^ geom.subtreeHeight) lsig0.tswCtr) lsig0 = some root0)
    (hUp : verifyUpperLayers geom pk 1 (statefulLeafIdx / 2 ^ geom.subtreeHeight) root0 upperLayers =
             some pk.pkRoot) :
    verifyAggNativeSig geom pk msg
      { profile := geom.profile, rRand := rRand, statefulLeafIdx := statefulLeafIdx,
        forsOpenings := [], layers := lsig0 :: upperLayers } = true := by
  unfold verifyAggNativeSig
  simp only [hWf, hPkProf, List.length_cons, hLen, bne_self_eq_false, Bool.not_true, Bool.or_self,
    Bool.false_eq_true, ↓reduceIte, hFors0]
  unfold verifyAggNativeSigStateful
  simp only [List.isEmpty_nil, Bool.not_true, hLeafLt, decide_true, Bool.or_self,
    Bool.false_eq_true, ↓reduceIte, hW0, hUp, beq_self_eq_true]

theorem verifyAggNativeSig_stateless_of_ok
    (geom : AggSigGeometry) (pk : AggValidatorPk) (msg : List UInt8) (rRand : Digest4)
    (forsOps : List AggForsTreeOpening) (lsig0 : WotsLayerSig) (upperLayers : List WotsLayerSig)
    (leafIdx : Nat) (forsIndices : List Nat) (forsPk root0 : Digest4)
    (hWf : geom.wellFormed = true)
    (hPkProf : pk.profile = geom.profile)
    (hLen : upperLayers.length + 1 = geom.numLayers)
    (hFors0 : (geom.forsTrees == 0) = false)
    (hXof : deriveStatelessLeafAndForsChecked geom pk rRand (computeMessageMu pk msg) =
              some (leafIdx, forsIndices))
    (hForsVer : verifyAndRecoverForsPk geom pk.pkSeed leafIdx forsIndices forsOps = some forsPk)
    (hW0 : verifyWotsLayer geom pk 0 (leafIdx / 2 ^ geom.subtreeHeight)
             (leafIdx % 2 ^ geom.subtreeHeight)
             (computeHmsgDetTree pk 0 (leafIdx / 2 ^ geom.subtreeHeight)
               (leafIdx % 2 ^ geom.subtreeHeight) lsig0.tswCtr forsPk) lsig0 = some root0)
    (hUp : verifyUpperLayers geom pk 1 (leafIdx / 2 ^ geom.subtreeHeight) root0 upperLayers =
             some pk.pkRoot) :
    verifyAggNativeSig geom pk msg
      { profile := geom.profile, rRand := rRand, statefulLeafIdx := 0,
        forsOpenings := forsOps, layers := lsig0 :: upperLayers } = true := by
  unfold verifyAggNativeSig
  simp only [hWf, hPkProf, List.length_cons, hLen, bne_self_eq_false, Bool.not_true, Bool.or_self,
    Bool.false_eq_true, ↓reduceIte, hFors0]
  delta verifyAggNativeSigStateless
  exact evalStatelessFlow_ok _ _ _ _ _ leafIdx forsIndices forsPk root0 pk.pkRoot
    hXof hForsVer hW0 hUp (beq_iff_eq.mpr rfl)

private theorem wellFormed_chainsLe (geom : AggSigGeometry) (hWf : geom.wellFormed = true) :
    geom.wotsChains ≤ 128 := by
  unfold AggSigGeometry.wellFormed at hWf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hWf
  exact hWf.1.1.1.1.1.1.2

/-- **Packed 4-Limb `AggNativeSignature` Completeness (`aggNativeSig_completeness`)**:
    For every well-formed `AggSigGeometry` (both `XmssPoseidon2` stateful XMSS and
    `CorduroyPoseidon2` stateless FORS + 16-layer hypertree) and any `ValidSigningCtrs` witness
    bundle, `signAggNative` produces a signature accepted by `verifyAggNativeSig`! -/
theorem aggNativeSig_completeness
    (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (msg : List UInt8) (rRand : Digest4) (statefulLeafIdx : Nat)
    (hWf : geom.wellFormed = true)
    (ctrs : ValidSigningCtrs geom skSeed (deriveAggPublicKey geom skSeed pkSeed) msg rRand statefulLeafIdx) :
    verifyAggNativeSig geom (deriveAggPublicKey geom skSeed pkSeed) msg
      (signAggNative geom skSeed (deriveAggPublicKey geom skSeed pkSeed)
        msg rRand statefulLeafIdx ctrs.layer0Ctr ctrs.upperCtrs) = true := by
  have hChainsLe : geom.wotsChains ≤ 128 := wellFormed_chainsLe geom hWf
  have hPowSubPos : 0 < 2 ^ geom.subtreeHeight := Nat.pow_pos (by decide)
  cases hFors0 : (geom.forsTrees == 0)
  · -- Stateless FORS + Hypertree (`geom.forsTrees ≠ 0`)
    have hForsNe : geom.forsTrees ≠ 0 := by
      intro hZ; rw [hZ] at hFors0; simp at hFors0
    have hXofSome := ctrs.statelessXofOk hForsNe
    cases hXof : deriveStatelessLeafAndForsChecked geom (deriveAggPublicKey geom skSeed pkSeed) rRand
                   (computeMessageMu (deriveAggPublicKey geom skSeed pkSeed) msg) with
    | none => exact False.elim (hXofSome hXof)
    | some pair =>
      rcases pair with ⟨leafIdx, forsIndices⟩
      obtain ⟨hLeafLt, hForsLen, hForsAllLt⟩ := deriveStatelessLeafAndForsChecked_spec hXof
      have hL0 := ctrs.layer0Valid
      simp only [hFors0, Bool.false_eq_true, ↓reduceIte, hXof] at hL0
      obtain ⟨ds0, hExt0, hSum0⟩ := hL0
      have hUpperV :
          ∀ (j : Nat) (hj : j < ctrs.upperCtrs.length),
            let l := 1 + j
            let curRem := (leafIdx / 2 ^ geom.subtreeHeight) / (2 ^ (j * geom.subtreeHeight))
            let kpL := curRem % (2 ^ geom.subtreeHeight)
            let trL := curRem / (2 ^ geom.subtreeHeight)
            let childRt := honestSubtreeRoot geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed (l - 1) curRem
            let hmsgL := computeHmsgDetTree (deriveAggPublicKey geom skSeed pkSeed) l trL kpL (ctrs.upperCtrs[j]'hj) childRt
            ∃ dsL, extractWotsDigitsChecked geom hmsgL = some dsL ∧ listNatSum dsL = geom.targetSum := by
        intro j hj
        have hU := ctrs.upperValid j hj
        simp only [hFors0, Bool.false_eq_true, ↓reduceIte, hXof] at hU
        have hDiv :
            (leafIdx / 2 ^ geom.subtreeHeight) / (2 ^ (j * geom.subtreeHeight)) =
            leafIdx / (2 ^ ((j + 1) * geom.subtreeHeight)) := by
          rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
          have hE : geom.subtreeHeight + j * geom.subtreeHeight = (j + 1) * geom.subtreeHeight := by
            rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
          rw [hE]
        have h1j : 1 + j = j + 1 := Nat.add_comm 1 j
        simpa only [h1j, Nat.add_sub_cancel, hDiv] using hU
      rw [signAggNative_stateless_eq geom skSeed (deriveAggPublicKey geom skSeed pkSeed)
            msg rRand statefulLeafIdx ctrs.layer0Ctr ctrs.upperCtrs leafIdx forsIndices hFors0 hXof]
      refine verifyAggNativeSig_stateless_of_ok geom (deriveAggPublicKey geom skSeed pkSeed)
        msg rRand _ _ _ leafIdx forsIndices
        (honestForsPk geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed leafIdx)
        (honestSubtreeRoot geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed 0
          (leafIdx / 2 ^ geom.subtreeHeight))
        hWf rfl ?_ hFors0 hXof ?_ ?_ ?_
      · rw [signUpperLayersAux_length]; exact ctrs.lenUpper
      · unfold verifyAndRecoverForsPk
        have hOpsLen :
            (signForsTreesAux geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed leafIdx 0 forsIndices).length =
            geom.forsTrees := by
          rw [signForsTreesAux_length, hForsLen]
        simp only [hForsLen, hOpsLen, beq_self_eq_true, Bool.and_self, ↓reduceIte]
        rw [verifyForsTreesAux_signForsTreesAux geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed
              leafIdx forsIndices 0 hForsAllLt]
        simp only [Nat.zero_add, hForsLen, Option.some.injEq]
        exact honestForsPk_def geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed leafIdx
      · have hGetD0 :
            (extractWotsDigitsChecked geom
              (computeHmsgDetTree (deriveAggPublicKey geom skSeed pkSeed) 0
                (leafIdx / 2 ^ geom.subtreeHeight) (leafIdx % 2 ^ geom.subtreeHeight) ctrs.layer0Ctr
                (honestForsPk geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed leafIdx))).getD [] = ds0 := by
          rw [hExt0]; rfl
        rw [hGetD0, signWotsLayerWithDigits_tswCtr]
        exact verifyWotsLayer_signWotsLayerWithDigits geom skSeed (deriveAggPublicKey geom skSeed pkSeed)
          hChainsLe 0 (leafIdx / 2 ^ geom.subtreeHeight) (leafIdx % 2 ^ geom.subtreeHeight)
          ctrs.layer0Ctr (Nat.mod_lt _ hPowSubPos) _ ds0 hExt0 hSum0
      · have hSub10 :
            honestSubtreeRoot geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed 0
              (leafIdx / 2 ^ geom.subtreeHeight) =
            honestSubtreeRoot geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed (1 - 1)
              (leafIdx / 2 ^ geom.subtreeHeight) := rfl
        rw [hSub10, verifyUpperLayers_signUpperLayersAux geom skSeed (deriveAggPublicKey geom skSeed pkSeed)
              hChainsLe ctrs.upperCtrs 1 (leafIdx / 2 ^ geom.subtreeHeight) (by decide) hUpperV]
        have hTopLayer : 1 + ctrs.upperCtrs.length - 1 = geom.numLayers - 1 := by
          have hL := ctrs.lenUpper; omega
        have hTopTree :
            (leafIdx / 2 ^ geom.subtreeHeight) / (2 ^ (ctrs.upperCtrs.length * geom.subtreeHeight)) = 0 := by
          rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
          have hE : geom.subtreeHeight + ctrs.upperCtrs.length * geom.subtreeHeight =
              geom.numLayers * geom.subtreeHeight := by
            rw [← ctrs.lenUpper, Nat.add_mul, Nat.one_mul, Nat.add_comm]
          rw [hE]
          exact Nat.div_eq_of_lt hLeafLt
        rw [hTopLayer, hTopTree]
        rfl
  · -- Stateful XMSS (`geom.forsTrees = 0`)
    have hForsEq0 : geom.forsTrees = 0 := eq_of_beq hFors0
    have hLeafLt := ctrs.leafInRange hForsEq0
    have hL0 := ctrs.layer0Valid
    simp only [hFors0, ↓reduceIte] at hL0
    obtain ⟨ds0, hExt0, hSum0⟩ := hL0
    have hUpperV :
        ∀ (j : Nat) (hj : j < ctrs.upperCtrs.length),
          let l := 1 + j
          let curRem := (statefulLeafIdx / 2 ^ geom.subtreeHeight) / (2 ^ (j * geom.subtreeHeight))
          let kpL := curRem % (2 ^ geom.subtreeHeight)
          let trL := curRem / (2 ^ geom.subtreeHeight)
          let childRt := honestSubtreeRoot geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed (l - 1) curRem
          let hmsgL := computeHmsgDetTree (deriveAggPublicKey geom skSeed pkSeed) l trL kpL (ctrs.upperCtrs[j]'hj) childRt
          ∃ dsL, extractWotsDigitsChecked geom hmsgL = some dsL ∧ listNatSum dsL = geom.targetSum := by
      intro j hj
      have hU := ctrs.upperValid j hj
      simp only [hFors0, ↓reduceIte] at hU
      have hDiv :
          (statefulLeafIdx / 2 ^ geom.subtreeHeight) / (2 ^ (j * geom.subtreeHeight)) =
          statefulLeafIdx / (2 ^ ((j + 1) * geom.subtreeHeight)) := by
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
        have hE : geom.subtreeHeight + j * geom.subtreeHeight = (j + 1) * geom.subtreeHeight := by
          rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
        rw [hE]
      have h1j : 1 + j = j + 1 := Nat.add_comm 1 j
      simpa only [h1j, Nat.add_sub_cancel, hDiv] using hU
    rw [signAggNative_stateful_eq geom skSeed (deriveAggPublicKey geom skSeed pkSeed)
          msg rRand statefulLeafIdx ctrs.layer0Ctr ctrs.upperCtrs hFors0]
    refine verifyAggNativeSig_stateful_of_ok geom (deriveAggPublicKey geom skSeed pkSeed)
      msg rRand statefulLeafIdx _ _
      (honestSubtreeRoot geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed 0
        (statefulLeafIdx / 2 ^ geom.subtreeHeight))
      hWf rfl ?_ hFors0 hLeafLt ?_ ?_
    · rw [signUpperLayersAux_length]; exact ctrs.lenUpper
    · have hGetD0 :
          (extractWotsDigitsChecked geom
            (computeHmsgStateful (deriveAggPublicKey geom skSeed pkSeed) rRand
              (computeMessageMu (deriveAggPublicKey geom skSeed pkSeed) msg)
              (statefulLeafIdx % 2 ^ geom.subtreeHeight) ctrs.layer0Ctr)).getD [] = ds0 := by
        rw [hExt0]; rfl
      rw [hGetD0, signWotsLayerWithDigits_tswCtr]
      exact verifyWotsLayer_signWotsLayerWithDigits geom skSeed (deriveAggPublicKey geom skSeed pkSeed)
        hChainsLe 0 (statefulLeafIdx / 2 ^ geom.subtreeHeight) (statefulLeafIdx % 2 ^ geom.subtreeHeight)
        ctrs.layer0Ctr (Nat.mod_lt _ hPowSubPos) _ ds0 hExt0 hSum0
    · have hSub10 :
          honestSubtreeRoot geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed 0
            (statefulLeafIdx / 2 ^ geom.subtreeHeight) =
          honestSubtreeRoot geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed (1 - 1)
            (statefulLeafIdx / 2 ^ geom.subtreeHeight) := rfl
      rw [hSub10, verifyUpperLayers_signUpperLayersAux geom skSeed (deriveAggPublicKey geom skSeed pkSeed)
            hChainsLe ctrs.upperCtrs 1 (statefulLeafIdx / 2 ^ geom.subtreeHeight) (by decide) hUpperV]
      have hTopLayer : 1 + ctrs.upperCtrs.length - 1 = geom.numLayers - 1 := by
        have hL := ctrs.lenUpper; omega
      have hTopTree :
          (statefulLeafIdx / 2 ^ geom.subtreeHeight) / (2 ^ (ctrs.upperCtrs.length * geom.subtreeHeight)) = 0 := by
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
        have hE : geom.subtreeHeight + ctrs.upperCtrs.length * geom.subtreeHeight =
            geom.numLayers * geom.subtreeHeight := by
          rw [← ctrs.lenUpper, Nat.add_mul, Nat.one_mul, Nat.add_comm]
        rw [hE]
        exact Nat.div_eq_of_lt hLeafLt
      rw [hTopLayer, hTopTree]
      rfl

/-! ### Constructive Secret-Key-Anchored Forgery Extraction (`aggNativeSig_wots_merkle_soundness`) -/

/-- Collision in `compressWotsEndpointsSponge` (`T_ell` WOTS+C public-key compression). -/
structure WotsPkSpongeCollisionWitness (pkSeed : Digest4) where
  layer     : Nat
  treeIdx   : Nat
  kpIdx     : Nat
  eps1      : List Digest4
  eps2      : List Digest4
  neInputs  : eps1 ≠ eps2
  spongeEq  : compressWotsEndpointsSponge pkSeed layer treeIdx kpIdx eps1 =
              compressWotsEndpointsSponge pkSeed layer treeIdx kpIdx eps2

/-- Collision in a single domain-separated WOTS+C chain step (`wotsStepHash`). -/
structure WotsStepCollisionWitness (pkSeed : Digest4) where
  layer    : Nat
  treeIdx  : Nat
  kpIdx    : Nat
  chainIdx : Nat
  stepIdx  : Nat
  in1      : Digest4
  in2      : Digest4
  neInputs : in1 ≠ in2
  stepEq   : wotsStepHash pkSeed in1 layer treeIdx kpIdx chainIdx stepIdx =
             wotsStepHash pkSeed in2 layer treeIdx kpIdx chainIdx stepIdx

/-- Collision in `forsLeafHash`. -/
structure ForsLeafCollisionWitness (geom : AggSigGeometry) (pkSeed : Digest4) where
  leafGlobalIdx : Nat
  treeIdx       : Nat
  leafOffset    : Nat
  val1          : Digest4
  val2          : Digest4
  neInputs      : val1 ≠ val2
  hashEq        : forsLeafHash geom pkSeed val1 leafGlobalIdx treeIdx leafOffset =
                  forsLeafHash geom pkSeed val2 leafGlobalIdx treeIdx leafOffset

/-- Collision in `compressForsRootsSponge`. -/
structure ForsRootsSpongeCollisionWitness (geom : AggSigGeometry) (pkSeed : Digest4) where
  leafGlobalIdx : Nat
  roots1        : List Digest4
  roots2        : List Digest4
  neInputs      : roots1 ≠ roots2
  spongeEq      : compressForsRootsSponge geom pkSeed leafGlobalIdx roots1 =
                  compressForsRootsSponge geom pkSeed leafGlobalIdx roots2

/-- Concrete record of a previously queried WOTS+C OTS keypair `(layer, treeIdx, kpIdx)`. -/
structure QueriedWotsEntry where
  tswCtr     : Nat
  rRand      : Digest4
  queriedMsg : List UInt8
  digits     : List Nat
  deriving DecidableEq, Repr

/-- Oracle mapping `(layer, treeIdx, kpIdx)` to an optional `QueriedWotsEntry`. -/
abbrev QueriedWotsDigitsOracle := Nat → Nat → Nat → Option QueriedWotsEntry

/-- Secret-key-anchored WOTS+C chain preimage break (`0` unconstrained fields):
    1. Either recovers the exact secret-derived chain node `x_c^{(d)}` at `d < 3` on an OTS
       `(layer, treeIdx, kpIdx)` that was **never** queried (`qWots layer treeIdx kpIdx = none`),
    2. Or on a queried OTS (`qWots layer treeIdx kpIdx = some entry`) inverts `wotsStepHash` **1 step
       backward** behind the revealed chain position `entry.digits[c]` (`≥ 1`), recovering
       `x_c^{(entry.digits[c] - 1)}`! -/
inductive WotsSecretChainBreak (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (qWots : QueriedWotsDigitsOracle) : Type where
  | unqueriedChainPreimage
      (layer treeIdx kpIdx chainIdx digit : Nat)
      (forgedNode : Digest4)
      (hFreshOts : qWots layer treeIdx kpIdx = none)
      (hChainLt : chainIdx < geom.wotsChains)
      (hDigitLt : digit < 3)
      (hExactSecret :
        forgedNode = wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx 0 digit
          (wotsSecretStart skSeed pkSeed layer treeIdx kpIdx chainIdx))
      (hWalkToPub :
        wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx digit (3 - digit) forgedNode =
          wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx 0 3
            (wotsSecretStart skSeed pkSeed layer treeIdx kpIdx chainIdx))
  | queriedBackwardInversion
      (layer treeIdx kpIdx chainIdx : Nat)
      (entry : QueriedWotsEntry) (hCQ : chainIdx < entry.digits.length)
      (preNode : Digest4)
      (hQueried : qWots layer treeIdx kpIdx = some entry)
      (hDqPos : 1 ≤ entry.digits[chainIdx]'hCQ)
      (hExactPre :
        preNode = wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx 0 ((entry.digits[chainIdx]'hCQ) - 1)
          (wotsSecretStart skSeed pkSeed layer treeIdx kpIdx chainIdx))
      (hStepInverts :
        wotsStepHash pkSeed preNode layer treeIdx kpIdx chainIdx ((entry.digits[chainIdx]'hCQ) - 1) =
          wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx 0 (entry.digits[chainIdx]'hCQ)
            (wotsSecretStart skSeed pkSeed layer treeIdx kpIdx chainIdx))

/-- Secret-key-anchored unqueried FORS leaf recovery (`op.secretVal = forsSecretVal ...` outside `revealedFors`). -/
structure ForsUnqueriedSecretBreak (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (revealedFors : List (Nat × Nat × Nat)) where
  leafGlobalIdx : Nat
  treeIdx       : Nat
  leafOffset    : Nat
  secretVal     : Digest4
  notRevealed   : (leafGlobalIdx, treeIdx, leafOffset) ∉ revealedFors
  exactSecret   : secretVal = forsSecretVal geom skSeed pkSeed leafGlobalIdx treeIdx leafOffset

/-- Codeword or `mu` collision witness when a queried OTS receives identical WOTS+C digits on a distinct input. -/
inductive HmsgOrMuCollisionBreak (geom : AggSigGeometry) (pk : AggValidatorPk) : Type where
  | muPoseidon2Collision (col : HashCollisionWitness poseidon2Hash32)
  | statefulCodewordCollision
      (kpIdx : Nat) (r1 r2 : Digest4) (mu1 mu2 : Digest5) (ctr1 ctr2 : Nat) (digits : List Nat)
      (hNe : (r1, mu1, ctr1) ≠ (r2, mu2, ctr2))
      (hExt1 : extractWotsDigitsChecked geom (computeHmsgStateful pk r1 mu1 kpIdx ctr1) = some digits)
      (hExt2 : extractWotsDigitsChecked geom (computeHmsgStateful pk r2 mu2 kpIdx ctr2) = some digits)
  | detTreeCodewordCollision
      (layer treeIdx kpIdx ctr1 ctr2 : Nat) (rt1 rt2 : Digest4) (digits : List Nat)
      (hNe : (ctr1, rt1) ≠ (ctr2, rt2))
      (hExt1 : extractWotsDigitsChecked geom (computeHmsgDetTree pk layer treeIdx kpIdx ctr1 rt1) = some digits)
      (hExt2 : extractWotsDigitsChecked geom (computeHmsgDetTree pk layer treeIdx kpIdx ctr2 rt2) = some digits)

/-- Stateless FORS multi-target subset-cover event (only inhabited when `geom.forsTrees > 0` and all
    `k` derived FORS leaves were previously revealed across adaptive signing queries). -/
structure StatelessForsSubsetCoverBreak (geom : AggSigGeometry) (pk : AggValidatorPk)
    (msg : List UInt8) (rRand : Digest4) (revealedFors : List (Nat × Nat × Nat)) where
  forsPos       : 0 < geom.forsTrees
  leafGlobalIdx : Nat
  indices       : List Nat
  xofEq         : deriveStatelessLeafAndForsChecked geom pk rRand (computeMessageMu pk msg) =
                  some (leafGlobalIdx, indices)
  allCovered    : ∀ (t : Nat) (ht : t < indices.length), (leafGlobalIdx, t, indices[t]'ht) ∈ revealedFors

/-- Complete constructive forgery break sum for `AggNativeSignature` (`sig.rs`). -/
inductive AggNativeForgeryBreak (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (msg : List UInt8) (rRand : Digest4)
    (qWots : QueriedWotsDigitsOracle) (revealedFors : List (Nat × Nat × Nat)) : Type where
  | merkleCollision      (w : MerkleNodeCollisionWitness pk.pkSeed)
  | wotsPkCollision      (w : WotsPkSpongeCollisionWitness pk.pkSeed)
  | wotsStepCollision    (w : WotsStepCollisionWitness pk.pkSeed)
  | wotsSecretChainBreak (w : WotsSecretChainBreak geom skSeed pk.pkSeed qWots)
  | forsLeafCollision    (w : ForsLeafCollisionWitness geom pk.pkSeed)
  | forsRootsCollision   (w : ForsRootsSpongeCollisionWitness geom pk.pkSeed)
  | forsUnqueriedSecret  (w : ForsUnqueriedSecretBreak geom skSeed pk.pkSeed revealedFors)
  | hmsgOrMuCollision    (w : HmsgOrMuCollisionBreak geom pk)
  | statelessForsCover   (w : StatelessForsSubsetCoverBreak geom pk msg rRand revealedFors)

private structure PolyStepCollision {σ : Type} (step : Nat → σ → σ) where
  stepIdx  : Nat
  in1      : σ
  in2      : σ
  neInputs : in1 ≠ in2
  stepEq   : step stepIdx in1 = step stepIdx in2

private def extractNatIterEqOrCol {σ : Type} [DecidableEq σ] (step : Nat → σ → σ) :
    ∀ (steps startStep : Nat) (v1 v2 : σ),
      natIterAt step steps startStep v1 = natIterAt step steps startStep v2 →
      PSum (v1 = v2) (PolyStepCollision step)
  | 0, _, _, _, hEq => .inl hEq
  | steps + 1, startStep, v1, v2, hEq =>
    if hIn : v1 = v2 then
      .inl hIn
    else
      let nx1 := step startStep v1
      let nx2 := step startStep v2
      if hStep : nx1 = nx2 then
        .inr { stepIdx := startStep, in1 := v1, in2 := v2, neInputs := hIn, stepEq := hStep }
      else
        match extractNatIterEqOrCol step steps (startStep + 1) nx1 nx2 hEq with
        | .inl hNxEq => False.elim (hStep hNxEq)
        | .inr col => .inr col

/-- Constructive step-by-step WOTS+C walk extractor: if two walks from
    `startStep` for `steps` iterations end at the same `Digest4`, either `v1 = v2` or an explicit
    `WotsStepCollisionWitness` occurred along the chain! -/
def extractChainWalkEqOrStepCollision (pkSeed : Digest4)
    (layer treeIdx kpIdx chainIdx steps startStep : Nat) (v1 v2 : Digest4)
    (hEq : wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx startStep steps v1 =
             wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx startStep steps v2) :
    PSum (v1 = v2) (WotsStepCollisionWitness pkSeed) :=
  match extractNatIterEqOrCol (fun stp v => wotsStepHash pkSeed v layer treeIdx kpIdx chainIdx stp)
          steps startStep v1 v2 hEq with
  | .inl h => .inl h
  | .inr col => .inr {
      layer    := layer
      treeIdx  := treeIdx
      kpIdx    := kpIdx
      chainIdx := chainIdx
      stepIdx  := col.stepIdx
      in1      := col.in1
      in2      := col.in2
      neInputs := col.neInputs
      stepEq   := col.stepEq
    }

private theorem recoverEndpointsPoly_length {D : Type} (walkFn : Nat → Nat → Nat → D → D) :
    ∀ (ds : List Nat) (chains : List D) (startC : Nat),
      ds.length = chains.length →
      (recoverEndpointsPoly walkFn ds chains startC).length = ds.length
  | [], [], _, _ => rfl
  | [], _ :: _, _, hLen => False.elim (Nat.succ_ne_zero _ hLen.symm)
  | _ :: _, [], _, hLen => False.elim (Nat.succ_ne_zero _ hLen)
  | _ :: ds, _ :: cs, startC, hLen => by
    dsimp only [recoverEndpointsPoly]
    rw [List.length_cons, recoverEndpointsPoly_length walkFn ds cs (startC + 1) (Nat.succ.inj hLen)]
    rfl

private theorem recoverEndpointsPoly_getElem {D : Type} (walkFn : Nat → Nat → Nat → D → D) :
    ∀ (ds : List Nat) (chains : List D) (startC idx : Nat)
      (hLen : ds.length = chains.length)
      (hIdx : idx < ds.length)
      (hOut : idx < (recoverEndpointsPoly walkFn ds chains startC).length),
      (recoverEndpointsPoly walkFn ds chains startC)[idx]'hOut =
        walkFn (startC + idx) (ds[idx]'hIdx) (3 - (ds[idx]'hIdx)) (chains[idx]'(hLen ▸ hIdx))
  | [], _, _, _, _, hIdx, _ => False.elim (by simp at hIdx)
  | _ :: _, [], _, _, hLen, _, _ => False.elim (by simp at hLen)
  | _ :: _, _ :: _, _, 0, _, _, _ => rfl
  | _ :: ds, _ :: cs, startC, idx + 1, hLen, hIdx, hOut => by
    have ih := recoverEndpointsPoly_getElem walkFn ds cs (startC + 1) idx
      (Nat.succ.inj hLen) (Nat.lt_of_succ_lt_succ hIdx) (Nat.lt_of_succ_lt_succ hOut)
    have hShift : startC + 1 + idx = startC + (idx + 1) := by omega
    rw [hShift] at ih
    exact ih

private theorem recoverAggWotsEndpoints_length (pkSeed : Digest4) (layer treeIdx kpIdx startC : Nat)
    (ds : List Nat) (chains : List Digest4) (hLen : ds.length = chains.length) :
    (recoverAggWotsEndpoints pkSeed layer treeIdx kpIdx startC ds chains).length = ds.length :=
  recoverEndpointsPoly_length _ ds chains startC hLen

private theorem recoverAggWotsEndpoints_getElem (pkSeed : Digest4) (layer treeIdx kpIdx : Nat)
    (ds : List Nat) (chains : List Digest4) (startC idx : Nat)
    (hLen : ds.length = chains.length)
    (hIdx : idx < ds.length)
    (hOut : idx < (recoverAggWotsEndpoints pkSeed layer treeIdx kpIdx startC ds chains).length) :
    (recoverAggWotsEndpoints pkSeed layer treeIdx kpIdx startC ds chains)[idx]'hOut =
      wotsChainWalk pkSeed layer treeIdx kpIdx (startC + idx)
        (ds[idx]'hIdx) (3 - (ds[idx]'hIdx)) (chains[idx]'(hLen ▸ hIdx)) :=
  recoverEndpointsPoly_getElem _ ds chains startC idx hLen hIdx hOut

private theorem bytes32ToDigest5_vals_of_len32 {bs : List UInt8} (hLen : bs.length = 32) :
    (bytes32ToDigest5 bs).limb0.val = ofBE (bs.take 7) ∧
    (bytes32ToDigest5 bs).limb1.val = ofBE ((bs.drop 7).take 7) ∧
    (bytes32ToDigest5 bs).limb2.val = ofBE ((bs.drop 14).take 7) ∧
    (bytes32ToDigest5 bs).limb3.val = ofBE ((bs.drop 21).take 7) ∧
    (bytes32ToDigest5 bs).limb4.val = ofBE ((bs.drop 28).take 4) := by
  let b := (bs ++ List.replicate (32 - bs.length) (0 : UInt8)).take 32
  have hB : b = bs := by
    dsimp only [b]
    rw [hLen]
    simp only [Nat.sub_self, List.replicate_zero, List.append_nil]
    exact List.take_of_length_le (Nat.le_of_eq hLen)
  have e0 : (bytes32ToDigest5 bs).limb0.val = ofBE (b.take 7) := rfl
  have e1 : (bytes32ToDigest5 bs).limb1.val = ofBE ((b.drop 7).take 7) := rfl
  have e2 : (bytes32ToDigest5 bs).limb2.val = ofBE ((b.drop 14).take 7) := rfl
  have e3 : (bytes32ToDigest5 bs).limb3.val = ofBE ((b.drop 21).take 7) := rfl
  have e4 : (bytes32ToDigest5 bs).limb4.val = ofBE ((b.drop 28).take 4) := rfl
  rw [hB] at e0 e1 e2 e3 e4
  exact ⟨e0, e1, e2, e3, e4⟩

private theorem unpack_bytes32ToDigest5_of_len32 {bs : List UInt8} (hLen : bs.length = 32) :
    be 7 (bytes32ToDigest5 bs).limb0.val ++
    be 7 (bytes32ToDigest5 bs).limb1.val ++
    be 7 (bytes32ToDigest5 bs).limb2.val ++
    be 7 (bytes32ToDigest5 bs).limb3.val ++
    be 4 (bytes32ToDigest5 bs).limb4.val = bs := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := bytes32ToDigest5_vals_of_len32 hLen
  rw [e0, e1, e2, e3, e4]
  have hBeOfBE : ∀ (xs : List UInt8) (k : Nat), xs.length = k → be k (ofBE xs) = xs := by
    intro xs k hk
    subst hk
    simpa [ofBE, be] using be_foldl_acc xs 0 0
  rw [hBeOfBE (bs.take 7) 7 (by simp [hLen]),
      hBeOfBE ((bs.drop 7).take 7) 7 (by simp [hLen]),
      hBeOfBE ((bs.drop 14).take 7) 7 (by simp [hLen]),
      hBeOfBE ((bs.drop 21).take 7) 7 (by simp [hLen]),
      hBeOfBE ((bs.drop 28).take 4) 4 (by simp [hLen])]
  have hSplit32 :
      bs.take 7 ++ ((bs.drop 7).take 7 ++ ((bs.drop 14).take 7 ++ ((bs.drop 21).take 7 ++ (bs.drop 28).take 4))) =
      bs := by
    have h28 : (bs.drop 28).take 4 = bs.drop 28 :=
      List.take_of_length_le (by simp [hLen])
    have h21 : (bs.drop 21).take 7 ++ bs.drop 28 = bs.drop 21 := by
      have hDrop : (bs.drop 21).drop 7 = bs.drop 28 := by rw [List.drop_drop]
      rw [← hDrop, List.take_append_drop]
    have h14 : (bs.drop 14).take 7 ++ bs.drop 21 = bs.drop 14 := by
      have hDrop : (bs.drop 14).drop 7 = bs.drop 21 := by rw [List.drop_drop]
      rw [← hDrop, List.take_append_drop]
    have h7 : (bs.drop 7).take 7 ++ bs.drop 14 = bs.drop 7 := by
      have hDrop : (bs.drop 7).drop 7 = bs.drop 14 := by rw [List.drop_drop]
      rw [← hDrop, List.take_append_drop]
    rw [h28, h21, h14, h7, List.take_append_drop]
  simpa only [List.append_assoc] using hSplit32

theorem bytes32ToDigest5_injective {b1 b2 : List UInt8}
    (h1 : b1.length = 32) (h2 : b2.length = 32)
    (hEq : bytes32ToDigest5 b1 = bytes32ToDigest5 b2) : b1 = b2 := by
  rw [← unpack_bytes32ToDigest5_of_len32 h1, ← unpack_bytes32ToDigest5_of_len32 h2, hEq]

/-- Constructive single-layer WOTS+C + XMSS extractor: given `verifyWotsLayer = some rt` where
    `rt = honestSubtreeRoot geom skSeed pk.pkSeed layer treeIdx`, either:
    1. `(qWots layer treeIdx kpIdx = some entry ∧ dsF = entry.digits)` (the exact queried digit vector was replayed), OR
    2. Extracts a concrete Merkle / WOTS-sponge / WOTS-step / secret-chain break! -/
def extractSingleWotsLayerOrBreak
    (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (qWots : QueriedWotsDigitsOracle)
    (hChainsLe : geom.wotsChains ≤ 128)
    (hTargetBound : geom.targetSum < 3 * geom.wotsChains)
    (layer treeIdx kpIdx : Nat) (hKpLt : kpIdx < 2 ^ geom.subtreeHeight)
    (hmsg : Digest5) (lsig : WotsLayerSig) (rt : Digest4)
    (hVer : verifyWotsLayer geom pk layer treeIdx kpIdx hmsg lsig = some rt)
    (hRtEq : rt = honestSubtreeRoot geom skSeed pk.pkSeed layer treeIdx)
    (hOracleValid : ∀ entry, qWots layer treeIdx kpIdx = some entry →
      entry.digits.length = geom.wotsChains ∧
      listNatSum entry.digits = geom.targetSum ∧
      (∀ x ∈ entry.digits, x < 4)) :
    PSum { entry : QueriedWotsEntry // qWots layer treeIdx kpIdx = some entry ∧
                                       extractWotsDigitsChecked geom hmsg = some entry.digits }
         (PSum (MerkleNodeCollisionWitness pk.pkSeed)
           (PSum (WotsPkSpongeCollisionWitness pk.pkSeed)
             (PSum (WotsStepCollisionWitness pk.pkSeed)
               (WotsSecretChainBreak geom skSeed pk.pkSeed qWots)))) := by
  unfold verifyWotsLayer at hVer
  cases hLengths : (lsig.wotsChains.length == geom.wotsChains && lsig.merklePath.length == geom.subtreeHeight)
  · simp [hLengths] at hVer
  · simp only [hLengths, ↓reduceIte] at hVer
    rcases Bool.and_eq_true_iff.mp hLengths with ⟨hChainLenBeq, hPathLenBeq⟩
    have hChainLen : lsig.wotsChains.length = geom.wotsChains := eq_of_beq hChainLenBeq
    have hPathLen : lsig.merklePath.length = geom.subtreeHeight := eq_of_beq hPathLenBeq
    cases hExt : extractWotsDigitsChecked geom hmsg with
    | none => simp [hExt] at hVer
    | some dsF =>
      simp only [hExt] at hVer
      cases hSumBeq : (listNatSum dsF == geom.targetSum)
      · simp [hSumBeq] at hVer
      · simp only [hSumBeq, ↓reduceIte, Option.some.injEq] at hVer
        have hSumF : listNatSum dsF = geom.targetSum := eq_of_beq hSumBeq
        obtain ⟨hDsFLen, _⟩ := extractWotsDigitsChecked_spec hChainsLe hExt
        let epsF := recoverAggWotsEndpoints pk.pkSeed layer treeIdx kpIdx 0 dsF lsig.wotsChains
        let wotsPkF := compressWotsEndpointsSponge pk.pkSeed layer treeIdx kpIdx epsF
        unfold honestSubtreeRoot at hRtEq
        have hWalkEq :
            merkleWalkRoot domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr 1 kpIdx wotsPkF
                lsig.merklePath =
              buildMerkleNodeAt domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr
                (honestWotsPk geom skSeed pk.pkSeed layer treeIdx) geom.subtreeHeight 1 0 :=
          hVer.trans hRtEq
        match extractMerkleLeafOrCollision domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr
                geom.subtreeHeight (honestWotsPk geom skSeed pk.pkSeed layer treeIdx)
                1 kpIdx wotsPkF lsig.merklePath hPathLen hKpLt hWalkEq with
        | .inr mCol => exact .inr (.inl mCol)
        | .inl hWotsPkEq =>
          let epsH := honestWotsEndpoints geom skSeed pk.pkSeed layer treeIdx kpIdx
          if hEpsEq : epsF = epsH then
            cases hQ : qWots layer treeIdx kpIdx with
            | none =>
              have hSumLt3 : listNatSum dsF < 3 * dsF.length := by
                rw [hSumF, hDsFLen]; exact hTargetBound
              let ⟨c, hCF, hCLt3⟩ := findDigitLtThreeIdx dsF hSumLt3
              have hCG : c < geom.wotsChains := hDsFLen ▸ hCF
              have hCLen : dsF.length = lsig.wotsChains.length := hDsFLen.trans hChainLen.symm
              have hEpsFLen : epsF.length = dsF.length :=
                recoverAggWotsEndpoints_length pk.pkSeed layer treeIdx kpIdx 0 dsF lsig.wotsChains hCLen
              have hCEpsF : c < epsF.length := hEpsFLen.symm ▸ hCF
              have hCEpsH : c < epsH.length := by simp [epsH, honestWotsEndpoints, hCG]
              have hEndEq : epsF[c]'hCEpsF = epsH[c]'hCEpsH := by simp [hEpsEq]
              have hFGet := recoverAggWotsEndpoints_getElem pk.pkSeed layer treeIdx kpIdx
                dsF lsig.wotsChains 0 c hCLen hCF hCEpsF
              simp only [Nat.zero_add] at hFGet
              have hHGet : epsH[c]'hCEpsH =
                  wotsChainWalk pk.pkSeed layer treeIdx kpIdx c 0 3
                    (wotsSecretStart skSeed pk.pkSeed layer treeIdx kpIdx c) := by
                simp only [epsH, honestWotsEndpoints, List.getElem_map, List.getElem_range]
              let dC := dsF[c]'hCF
              let forgedVal := lsig.wotsChains[c]'(hCLen ▸ hCF)
              let honestMid := wotsChainWalk pk.pkSeed layer treeIdx kpIdx c 0 dC
                (wotsSecretStart skSeed pk.pkSeed layer treeIdx kpIdx c)
              have hSplit3 :
                  wotsChainWalk pk.pkSeed layer treeIdx kpIdx c 0 3
                    (wotsSecretStart skSeed pk.pkSeed layer treeIdx kpIdx c) =
                  wotsChainWalk pk.pkSeed layer treeIdx kpIdx c dC (3 - dC) honestMid := by
                have hAdd : dC + (3 - dC) = 3 := by omega
                conv => lhs; rw [← hAdd]
                rw [wotsChainWalk_add, Nat.zero_add]
              have hWalkBoth :
                  wotsChainWalk pk.pkSeed layer treeIdx kpIdx c dC (3 - dC) forgedVal =
                  wotsChainWalk pk.pkSeed layer treeIdx kpIdx c dC (3 - dC) honestMid := by
                calc wotsChainWalk pk.pkSeed layer treeIdx kpIdx c dC (3 - dC) forgedVal
                  _ = epsF[c]'hCEpsF := hFGet.symm
                  _ = epsH[c]'hCEpsH := hEndEq
                  _ = _ := hHGet.trans hSplit3
              match extractChainWalkEqOrStepCollision pk.pkSeed layer treeIdx kpIdx c
                      (3 - dC) dC forgedVal honestMid hWalkBoth with
              | .inr sCol => exact .inr (.inr (.inr (.inl sCol)))
              | .inl hExact =>
                exact .inr (.inr (.inr (.inr
                  (.unqueriedChainPreimage layer treeIdx kpIdx c dC forgedVal
                    hQ hCG hCLt3 hExact (by rw [hExact, ← hSplit3])))))
            | some entry =>
              if hDsEq : dsF = entry.digits then
                exact .inl ⟨entry, rfl, congrArg some hDsEq⟩
              else
                obtain ⟨hDqLen, hDqSum, hDqLt4⟩ := hOracleValid entry hQ
                have hLenEq : entry.digits.length = dsF.length := hDqLen.trans hDsFLen.symm
                have hSumLe : listNatSum dsF ≤ listNatSum entry.digits := by
                  rw [hSumF, hDqSum]; exact Nat.le_refl _
                let ⟨c, hCQ, hCF, hStrictLt⟩ := findSmallerDigitIdx entry.digits dsF hLenEq hSumLe hDsEq
                have hCG : c < geom.wotsChains := hDqLen ▸ hCQ
                have hCLen : dsF.length = lsig.wotsChains.length := hDsFLen.trans hChainLen.symm
                have hEpsFLen : epsF.length = dsF.length :=
                  recoverAggWotsEndpoints_length pk.pkSeed layer treeIdx kpIdx 0 dsF lsig.wotsChains hCLen
                have hCEpsF : c < epsF.length := hEpsFLen.symm ▸ hCF
                have hCEpsH : c < epsH.length := by simp [epsH, honestWotsEndpoints, hCG]
                have hEndEq : epsF[c]'hCEpsF = epsH[c]'hCEpsH := by simp [hEpsEq]
                have hFGet := recoverAggWotsEndpoints_getElem pk.pkSeed layer treeIdx kpIdx
                  dsF lsig.wotsChains 0 c hCLen hCF hCEpsF
                simp only [Nat.zero_add] at hFGet
                have hHGet : epsH[c]'hCEpsH =
                    wotsChainWalk pk.pkSeed layer treeIdx kpIdx c 0 3
                      (wotsSecretStart skSeed pk.pkSeed layer treeIdx kpIdx c) := by
                  simp only [epsH, honestWotsEndpoints, List.getElem_map, List.getElem_range]
                let dFC := dsF[c]'hCF
                let dQC := entry.digits[c]'hCQ
                have hDqC4 : dQC < 4 := hDqLt4 dQC (List.getElem_mem hCQ)
                let forgedVal := lsig.wotsChains[c]'(hCLen ▸ hCF)
                let honestAtFC := wotsChainWalk pk.pkSeed layer treeIdx kpIdx c 0 dFC
                  (wotsSecretStart skSeed pk.pkSeed layer treeIdx kpIdx c)
                have hSplit3 :
                    wotsChainWalk pk.pkSeed layer treeIdx kpIdx c 0 3
                      (wotsSecretStart skSeed pk.pkSeed layer treeIdx kpIdx c) =
                    wotsChainWalk pk.pkSeed layer treeIdx kpIdx c dFC (3 - dFC) honestAtFC := by
                  have hAdd : dFC + (3 - dFC) = 3 := by omega
                  conv => lhs; rw [← hAdd]
                  rw [wotsChainWalk_add, Nat.zero_add]
                have hWalkBoth :
                    wotsChainWalk pk.pkSeed layer treeIdx kpIdx c dFC (3 - dFC) forgedVal =
                    wotsChainWalk pk.pkSeed layer treeIdx kpIdx c dFC (3 - dFC) honestAtFC := by
                  calc wotsChainWalk pk.pkSeed layer treeIdx kpIdx c dFC (3 - dFC) forgedVal
                    _ = epsF[c]'hCEpsF := hFGet.symm
                    _ = epsH[c]'hCEpsH := hEndEq
                    _ = _ := hHGet.trans hSplit3
                match extractChainWalkEqOrStepCollision pk.pkSeed layer treeIdx kpIdx c
                        (3 - dFC) dFC forgedVal honestAtFC hWalkBoth with
                | .inr sCol => exact .inr (.inr (.inr (.inl sCol)))
                | .inl hExactFC =>
                  let preSteps := (dQC - 1) - dFC
                  let preNode := wotsChainWalk pk.pkSeed layer treeIdx kpIdx c dFC preSteps forgedVal
                  have hPreExact :
                      preNode = wotsChainWalk pk.pkSeed layer treeIdx kpIdx c 0 (dQC - 1)
                        (wotsSecretStart skSeed pk.pkSeed layer treeIdx kpIdx c) := by
                    dsimp only [preNode, preSteps]
                    rw [hExactFC]
                    dsimp only [honestAtFC]
                    have hZeroAdd : dFC = 0 + dFC := (Nat.zero_add dFC).symm
                    conv => lhs; arg 6; rw [hZeroAdd]
                    rw [← wotsChainWalk_add]
                    have hAdd : dFC + ((dQC - 1) - dFC) = dQC - 1 := by omega
                    rw [hAdd]
                  have hStepInv :
                      wotsStepHash pk.pkSeed preNode layer treeIdx kpIdx c (dQC - 1) =
                        wotsChainWalk pk.pkSeed layer treeIdx kpIdx c 0 dQC
                          (wotsSecretStart skSeed pk.pkSeed layer treeIdx kpIdx c) := by
                    rw [hPreExact]
                    have hSucc : dQC = (dQC - 1) + 1 := by omega
                    conv => rhs; rw [hSucc, wotsChainWalk_add]
                    rw [Nat.zero_add]
                    rfl
                  exact .inr (.inr (.inr (.inr
                    (.queriedBackwardInversion layer treeIdx kpIdx c entry hCQ preNode
                      hQ (by omega) hPreExact hStepInv))))
          else
            exact .inr (.inr (.inl {
              layer    := layer
              treeIdx  := treeIdx
              kpIdx    := kpIdx
              eps1     := epsF
              eps2     := epsH
              neInputs := hEpsEq
              spongeEq := hWotsPkEq
            }))

private def extractUpperPoly {LS D BRK : Type}
    (vStep : Nat → Nat → D → LS → Option (Nat × D))
    (rootAt : Nat → Nat → D)
    (subH : Nat)
    (hRem : ∀ l rem cur lsig trOut nextRt,
      vStep l rem cur lsig = some (trOut, nextRt) → trOut = rem / 2 ^ subH)
    (stepExt : ∀ (l rem : Nat) (cur nextRt : D) (lsig : LS),
      0 < l →
      vStep l rem cur lsig = some (rem / 2 ^ subH, nextRt) →
      nextRt = rootAt l (rem / 2 ^ subH) →
      PSum (cur = rootAt (l - 1) rem) BRK) :
    ∀ (upperLayers : List LS) (startLayer remTreeIdx : Nat) (curRoot topRoot : D),
      0 < startLayer →
      verifyUpperPoly vStep upperLayers startLayer remTreeIdx curRoot = some topRoot →
      topRoot = rootAt (startLayer + upperLayers.length - 1) (remTreeIdx / 2 ^ (upperLayers.length * subH)) →
      PSum (curRoot = rootAt (startLayer - 1) remTreeIdx) BRK
  | [], startLayer, remTreeIdx, curRoot, topRoot, _, hVer, hTop => by
    dsimp only [verifyUpperPoly] at hVer
    simp only [Option.some.injEq] at hVer
    simp only [List.length_nil, Nat.add_zero, Nat.zero_mul, Nat.pow_zero, Nat.div_one] at hTop
    exact .inl (hVer.trans hTop)
  | lsig :: rest, startLayer, remTreeIdx, curRoot, topRoot, hPos, hVer, hTop => by
    dsimp only [verifyUpperPoly] at hVer
    cases hSt : vStep startLayer remTreeIdx curRoot lsig with
    | none => simp [hSt] at hVer
    | some pair =>
      rcases pair with ⟨nextRem, nextRoot⟩
      simp only [hSt] at hVer
      have hRemEq : nextRem = remTreeIdx / 2 ^ subH := hRem _ _ _ _ _ _ hSt
      subst hRemEq
      have hTopShift :
          topRoot = rootAt ((startLayer + 1) + rest.length - 1)
            ((remTreeIdx / 2 ^ subH) / 2 ^ (rest.length * subH)) := by
        have hL : startLayer + (lsig :: rest).length - 1 = (startLayer + 1) + rest.length - 1 := by
          simp only [List.length_cons]; omega
        have hR : remTreeIdx / 2 ^ ((lsig :: rest).length * subH) =
            (remTreeIdx / 2 ^ subH) / 2 ^ (rest.length * subH) := by
          simp only [List.length_cons]
          rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
          have hE : subH + rest.length * subH = (rest.length + 1) * subH := by
            rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
          rw [hE]
        rwa [← hL, ← hR]
      match extractUpperPoly vStep rootAt subH hRem stepExt rest
              (startLayer + 1) (remTreeIdx / 2 ^ subH) nextRoot topRoot (by omega) hVer hTopShift with
      | .inr brk => exact .inr brk
      | .inl hNextEq =>
        exact stepExt startLayer remTreeIdx curRoot nextRoot lsig hPos hSt hNextEq

/-- Downward multi-layer hypertree extractor (`startLayer .. top`): given
    `verifyUpperLayers geom pk startLayer remTreeIdx curRoot upperLayers = some topRoot` where
    `topRoot = honestSubtreeRoot geom skSeed pk.pkSeed ...`, constructively proves EITHER
    `curRoot = honestSubtreeRoot geom skSeed pk.pkSeed (startLayer - 1) remTreeIdx` OR extracts a
    concrete `AggNativeForgeryBreak`! -/
def extractUpperHypertreeOrBreak
    (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (msg : List UInt8) (rRand : Digest4)
    (qWots : QueriedWotsDigitsOracle) (revealedFors : List (Nat × Nat × Nat))
    (hChainsLe : geom.wotsChains ≤ 128)
    (hTargetBound : geom.targetSum < 3 * geom.wotsChains)
    (hOracleValid : ∀ l tr kp entry, qWots l tr kp = some entry →
      entry.digits.length = geom.wotsChains ∧
      listNatSum entry.digits = geom.targetSum ∧
      (∀ x ∈ entry.digits, x < 4))
    (hUpperHonest : ∀ (l rem : Nat) (entry : QueriedWotsEntry),
      0 < l →
      qWots l (rem / 2 ^ geom.subtreeHeight) (rem % 2 ^ geom.subtreeHeight) = some entry →
      extractWotsDigitsChecked geom
        (computeHmsgDetTree pk l (rem / 2 ^ geom.subtreeHeight) (rem % 2 ^ geom.subtreeHeight)
          entry.tswCtr (honestSubtreeRoot geom skSeed pk.pkSeed (l - 1) rem)) = some entry.digits)
    (upperLayers : List WotsLayerSig) (startLayer remTreeIdx : Nat) (curRoot topRoot : Digest4)
    (hPos : 0 < startLayer)
    (hVer : verifyUpperLayers geom pk startLayer remTreeIdx curRoot upperLayers = some topRoot)
    (hTop : topRoot = honestSubtreeRoot geom skSeed pk.pkSeed (startLayer + upperLayers.length - 1)
                        (remTreeIdx / 2 ^ (upperLayers.length * geom.subtreeHeight))) :
    PSum (curRoot = honestSubtreeRoot geom skSeed pk.pkSeed (startLayer - 1) remTreeIdx)
         (AggNativeForgeryBreak geom skSeed pk msg rRand qWots revealedFors) := by
  unfold verifyUpperLayers at hVer
  refine extractUpperPoly _ (honestSubtreeRoot geom skSeed pk.pkSeed) geom.subtreeHeight
    (fun l rem cur lsig trOut nextRt hSt => by
      dsimp only at hSt
      cases hW : verifyWotsLayer geom pk l (rem / 2 ^ geom.subtreeHeight) (rem % 2 ^ geom.subtreeHeight)
                   (computeHmsgDetTree pk l (rem / 2 ^ geom.subtreeHeight) (rem % 2 ^ geom.subtreeHeight)
                     lsig.tswCtr cur) lsig with
      | none => simp [hW] at hSt
      | some rt =>
        simp only [hW, Option.some.injEq, Prod.mk.injEq] at hSt
        exact hSt.1.symm)
    (fun l rem cur nextRt lsig hLPos hSt hNextHonest => by
      dsimp only at hSt
      let kpIdx := rem % (2 ^ geom.subtreeHeight)
      let treeIdx := rem / (2 ^ geom.subtreeHeight)
      let hmsg := computeHmsgDetTree pk l treeIdx kpIdx lsig.tswCtr cur
      cases hWots : verifyWotsLayer geom pk l treeIdx kpIdx hmsg lsig with
      | none =>
        change (match verifyWotsLayer geom pk l treeIdx kpIdx hmsg lsig with
                | none => none | some nextRoot => some (treeIdx, nextRoot)) = some _ at hSt
        rw [hWots] at hSt; cases hSt
      | some rtOut =>
        change (match verifyWotsLayer geom pk l treeIdx kpIdx hmsg lsig with
                | none => none | some nextRoot => some (treeIdx, nextRoot)) = some _ at hSt
        rw [hWots] at hSt
        simp only [Option.some.injEq, Prod.mk.injEq] at hSt
        rcases hSt with ⟨_, rfl⟩
        have hKpLt : kpIdx < 2 ^ geom.subtreeHeight := Nat.mod_lt _ (Nat.pow_pos (by decide))
        match extractSingleWotsLayerOrBreak geom skSeed pk qWots hChainsLe hTargetBound
                l treeIdx kpIdx hKpLt hmsg lsig rtOut hWots hNextHonest
                (hOracleValid l treeIdx kpIdx) with
        | .inr (.inl mCol) => exact .inr (.merkleCollision mCol)
        | .inr (.inr (.inl pCol)) => exact .inr (.wotsPkCollision pCol)
        | .inr (.inr (.inr (.inl sCol))) => exact .inr (.wotsStepCollision sCol)
        | .inr (.inr (.inr (.inr chBrk))) => exact .inr (.wotsSecretChainBreak chBrk)
        | .inl ⟨entry, hQ, hExtF⟩ =>
          let honestChildRt := honestSubtreeRoot geom skSeed pk.pkSeed (l - 1) rem
          if hChildEq : cur = honestChildRt then
            exact .inl hChildEq
          else
            have hHonExt := hUpperHonest l rem entry hLPos hQ
            have hPairNe : (lsig.tswCtr, cur) ≠ (entry.tswCtr, honestChildRt) :=
              fun hEq => hChildEq (congrArg Prod.snd hEq)
            exact .inr (.hmsgOrMuCollision
              (.detTreeCodewordCollision l treeIdx kpIdx lsig.tswCtr entry.tswCtr
                cur honestChildRt entry.digits hPairNe hExtF hHonExt)))
    upperLayers startLayer remTreeIdx curRoot topRoot hPos hVer hTop

private def extractForsPoly {OP D BRK : Type}
    (vStep : Nat → Nat → OP → Option D)
    (rootAt : Nat → D)
    (covPred : Nat → Nat → Prop)
    (treeExt : ∀ (t idx : Nat) (op : OP) (rt : D),
      vStep t idx op = some rt →
      rt = rootAt t →
      PSum { _u : Unit // covPred t idx } BRK) :
    ∀ (indices : List Nat) (ops : List OP) (startT : Nat) (roots : List D),
      verifyForsPoly vStep indices ops startT = some roots →
      roots = (List.range indices.length).map (fun i => rootAt (startT + i)) →
      PSum { _u : Unit // ∀ (i : Nat) (hi : i < indices.length), covPred (startT + i) (indices[i]'hi) } BRK
  | [], [], _, _, _, _ => .inl ⟨(), fun _ hi => False.elim (by simp at hi)⟩
  | [], _ :: _, _, _, hVer, _ => False.elim (by dsimp only [verifyForsPoly] at hVer; cases hVer)
  | _ :: _, [], _, _, hVer, _ => False.elim (by dsimp only [verifyForsPoly] at hVer; cases hVer)
  | idx :: idxs, op :: ops, startT, roots, hVer, hRootsEq => by
    dsimp only [verifyForsPoly] at hVer
    cases hSt : vStep startT idx op with
    | none => simp [hSt] at hVer
    | some rt =>
      simp only [hSt] at hVer
      cases hRest : verifyForsPoly vStep idxs ops (startT + 1) with
      | none => simp [hRest] at hVer
      | some restRoots =>
        simp only [hRest, Option.some.injEq] at hVer
        subst hVer
        rw [List.length_cons, List.range_succ_eq_map, List.map_cons, Nat.add_zero, List.map_map] at hRootsEq
        obtain ⟨hHeadRt, hTailRts⟩ := List.cons.inj hRootsEq
        have hTailShift :
            restRoots = (List.range idxs.length).map (fun i => rootAt (startT + 1 + i)) := by
          rw [hTailRts]
          congr 1
          funext i
          have hS : startT + (i + 1) = startT + 1 + i := by omega
          simp [Function.comp, hS]
        match treeExt startT idx op rt hSt hHeadRt with
        | .inr brk => exact .inr brk
        | .inl ⟨_, hHeadCov⟩ =>
          match extractForsPoly vStep rootAt covPred treeExt idxs ops (startT + 1) restRoots hRest hTailShift with
          | .inr brk => exact .inr brk
          | .inl ⟨_, hRestCov⟩ =>
            exact .inl ⟨(), fun i hi => by
              cases i with
              | zero => simpa only [Nat.add_zero, List.getElem_cons_zero] using hHeadCov
              | succ i' =>
                have hStep := hRestCov i' (Nat.lt_of_succ_lt_succ hi)
                have hS : startT + 1 + i' = startT + (i' + 1) := by omega
                simpa only [hS, List.getElem_cons_succ] using hStep⟩

/-- Constructive FORS tree-by-tree opening extractor. -/
def extractForsTreesOrBreak
    (geom : AggSigGeometry) (skSeed pkSeed : Digest4) (leafGlobalIdx : Nat)
    (revealedFors : List (Nat × Nat × Nat))
    (startT : Nat) (indices : List Nat) (ops : List AggForsTreeOpening) (roots : List Digest4)
    (hVer : verifyForsTreesAux geom pkSeed leafGlobalIdx startT indices ops = some roots)
    (hRootsEq : roots = (List.range indices.length).map (fun i =>
      honestForsTreeRoot geom skSeed pkSeed leafGlobalIdx (startT + i))) :
    PSum { _u : Unit // ∀ (i : Nat) (hi : i < indices.length),
                          (leafGlobalIdx, startT + i, indices[i]'hi) ∈ revealedFors }
         (PSum (MerkleNodeCollisionWitness pkSeed)
           (PSum (ForsLeafCollisionWitness geom pkSeed)
             (ForsUnqueriedSecretBreak geom skSeed pkSeed revealedFors))) := by
  unfold verifyForsTreesAux at hVer
  refine extractForsPoly
    (verifySingleForsOpening geom pkSeed leafGlobalIdx)
    (honestForsTreeRoot geom skSeed pkSeed leafGlobalIdx)
    (fun t o => (leafGlobalIdx, t, o) ∈ revealedFors)
    (fun t idx op rt hSt hRtEq => by
      dsimp only [verifySingleForsOpening] at hSt
      cases hChk : (decide (idx < 2 ^ geom.forsHeight) && (op.authPath.length == geom.forsHeight))
      · simp [hChk] at hSt
      · simp only [hChk, ↓reduceIte, Option.some.injEq] at hSt
        rcases Bool.and_eq_true_iff.mp hChk with ⟨hIdxLtDec, hPathLenBeq⟩
        have hIdxLt : idx < 2 ^ geom.forsHeight := of_decide_eq_true hIdxLtDec
        have hPathLen : op.authPath.length = geom.forsHeight := eq_of_beq hPathLenBeq
        unfold honestForsTreeRoot at hRtEq
        have hWalkEq := hSt.trans hRtEq
        let leafFn := honestForsLeaf geom skSeed pkSeed leafGlobalIdx t
        let forgedLeaf := forsLeafHash geom pkSeed op.secretVal leafGlobalIdx t idx
        match extractMerkleLeafOrCollision domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
                (forsTreeNodeAddr geom leafGlobalIdx t)
                geom.forsHeight leafFn 1 idx forgedLeaf op.authPath hPathLen hIdxLt hWalkEq with
        | .inr mCol => exact .inr (.inl mCol)
        | .inl hLeafEq =>
          let honestSec := forsSecretVal geom skSeed pkSeed leafGlobalIdx t idx
          if hSecEq : op.secretVal = honestSec then
            if hRev : (leafGlobalIdx, t, idx) ∈ revealedFors then
              exact .inl ⟨(), hRev⟩
            else
              exact .inr (.inr (.inr {
                leafGlobalIdx := leafGlobalIdx
                treeIdx       := t
                leafOffset    := idx
                secretVal     := op.secretVal
                notRevealed   := hRev
                exactSecret   := hSecEq
              }))
          else
            exact .inr (.inr (.inl {
              leafGlobalIdx := leafGlobalIdx
              treeIdx       := t
              leafOffset    := idx
              val1          := op.secretVal
              val2          := honestSec
              neInputs      := hSecEq
              hashEq        := hLeafEq
            })))
    indices ops startT roots hVer hRootsEq

/-- **Constructive Forgery Extractor (`extractAggNativeForgeryBreak`)**:
    Given `pk = deriveAggPublicKey geom skSeed pkSeed` and any signature `forgedSig` accepted on an
    unqueried message `msg ∉ queriedMsgs`, constructively extracts a concrete `AggNativeForgeryBreak`! -/
def extractAggNativeForgeryBreak
    (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (msg : List UInt8) (forgedSig : AggNativeSignature)
    (queriedMsgs : List (List UInt8))
    (qWots : QueriedWotsDigitsOracle)
    (revealedFors : List (Nat × Nat × Nat))
    (hFreshMsg : msg ∉ queriedMsgs)
    (hVer : verifyAggNativeSig geom (deriveAggPublicKey geom skSeed pkSeed) msg forgedSig = true)
    (hOracleValid : ∀ l tr kp entry, qWots l tr kp = some entry →
      entry.digits.length = geom.wotsChains ∧
      listNatSum entry.digits = geom.targetSum ∧
      (∀ x ∈ entry.digits, x < 4))
    (hUpperHonest : ∀ (l rem : Nat) (entry : QueriedWotsEntry),
      0 < l →
      qWots l (rem / 2 ^ geom.subtreeHeight) (rem % 2 ^ geom.subtreeHeight) = some entry →
      extractWotsDigitsChecked geom
        (computeHmsgDetTree (deriveAggPublicKey geom skSeed pkSeed) l
          (rem / 2 ^ geom.subtreeHeight) (rem % 2 ^ geom.subtreeHeight)
          entry.tswCtr (honestSubtreeRoot geom skSeed pkSeed (l - 1) rem)) = some entry.digits)
    (hStatefulHonest0 : geom.forsTrees = 0 →
      ∀ (tr0 kp0 : Nat) (entry : QueriedWotsEntry),
        qWots 0 tr0 kp0 = some entry →
        entry.queriedMsg ∈ queriedMsgs ∧
        extractWotsDigitsChecked geom
          (computeHmsgStateful (deriveAggPublicKey geom skSeed pkSeed) entry.rRand
            (computeMessageMu (deriveAggPublicKey geom skSeed pkSeed) entry.queriedMsg)
            kp0 entry.tswCtr) = some entry.digits)
    (hStatelessHonest0 : geom.forsTrees ≠ 0 →
      ∀ (leafIdx : Nat) (entry : QueriedWotsEntry),
        qWots 0 (leafIdx / 2 ^ geom.subtreeHeight) (leafIdx % 2 ^ geom.subtreeHeight) = some entry →
        extractWotsDigitsChecked geom
          (computeHmsgDetTree (deriveAggPublicKey geom skSeed pkSeed) 0
            (leafIdx / 2 ^ geom.subtreeHeight) (leafIdx % 2 ^ geom.subtreeHeight)
            entry.tswCtr (honestForsPk geom skSeed pkSeed leafIdx)) = some entry.digits) :
    AggNativeForgeryBreak geom skSeed (deriveAggPublicKey geom skSeed pkSeed)
      msg forgedSig.rRand qWots revealedFors := by
  let pk := deriveAggPublicKey geom skSeed pkSeed
  change verifyAggNativeSig geom pk msg forgedSig = true at hVer
  unfold verifyAggNativeSig at hVer
  cases hHdr : (!geom.wellFormed || pk.profile != geom.profile ||
                forgedSig.profile != geom.profile || forgedSig.layers.length != geom.numLayers)
  · simp only [hHdr, Bool.false_eq_true, ↓reduceIte] at hVer
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false', bne_eq_false_iff_eq] at hHdr
    have hWf : geom.wellFormed = true := hHdr.1.1.1
    have hLayersLen : forgedSig.layers.length = geom.numLayers := hHdr.2
    have hWfUnpack : geom.wotsChains ≤ 128 ∧ geom.targetSum < 3 * geom.wotsChains := by
      unfold AggSigGeometry.wellFormed at hWf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hWf
      exact ⟨hWf.1.1.1.1.1.1.2, hWf.1.1.1.1.2⟩
    obtain ⟨hChainsLe, hTargetBound⟩ := hWfUnpack
    let mu := computeMessageMu pk msg
    cases hLayers : forgedSig.layers with
    | nil => simp [hLayers] at hVer
    | cons lsig0 upperLayers =>
      simp only [hLayers] at hVer
      have hUpperLen : upperLayers.length + 1 = geom.numLayers := by
        rw [← hLayersLen, hLayers]; simp
      have hPowPos : 0 < 2 ^ geom.subtreeHeight := Nat.pow_pos (by decide)
      cases hFors0 : (geom.forsTrees == 0)
      · -- Stateless Corduroy (`geom.forsTrees ≠ 0`)
        simp only [hFors0, Bool.false_eq_true, ↓reduceIte] at hVer
        delta verifyAggNativeSigStateless at hVer
        have hForsNe : geom.forsTrees ≠ 0 := by intro hZ; rw [hZ] at hFors0; simp at hFors0
        have hForsPos : 0 < geom.forsTrees := Nat.pos_of_ne_zero hForsNe
        rcases unpackStatelessFlow hVer with
          ⟨leafGlobalIdx, forsIndices, forsPk, root0, topRoot, _, hXof, hForsVer, hW0, hUp, hTopBeq⟩
        have hTopEq : topRoot = pk.pkRoot := eq_of_beq hTopBeq
        obtain ⟨hLeafLt, hForsIdxLen, _⟩ := deriveStatelessLeafAndForsChecked_spec hXof
        let kp0 := leafGlobalIdx % (2 ^ geom.subtreeHeight)
        let tr0 := leafGlobalIdx / (2 ^ geom.subtreeHeight)
        let hmsg0 := computeHmsgDetTree pk 0 tr0 kp0 lsig0.tswCtr forsPk
        have hTopHonest :
            topRoot = honestSubtreeRoot geom skSeed pk.pkSeed
              (1 + upperLayers.length - 1) (tr0 / 2 ^ (upperLayers.length * geom.subtreeHeight)) := by
          have hL : 1 + upperLayers.length - 1 = geom.numLayers - 1 := by omega
          have hR : tr0 / 2 ^ (upperLayers.length * geom.subtreeHeight) = 0 := by
            dsimp only [tr0]
            rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
            have hE : geom.subtreeHeight + upperLayers.length * geom.subtreeHeight =
                geom.numLayers * geom.subtreeHeight := by
              rw [← hUpperLen, Nat.add_mul, Nat.one_mul, Nat.add_comm]
            rw [hE]
            exact Nat.div_eq_of_lt hLeafLt
          rw [hL, hR]
          exact hTopEq
        match extractUpperHypertreeOrBreak geom skSeed pk msg forgedSig.rRand qWots revealedFors
                hChainsLe hTargetBound hOracleValid hUpperHonest
                upperLayers 1 tr0 root0 topRoot (by decide) hUp hTopHonest with
        | .inr brk => exact brk
        | .inl hRoot0Eq =>
          match extractSingleWotsLayerOrBreak geom skSeed pk qWots hChainsLe hTargetBound
                  0 tr0 kp0 (Nat.mod_lt _ hPowPos) hmsg0 lsig0 root0 hW0 hRoot0Eq
                  (hOracleValid 0 tr0 kp0) with
          | .inr (.inl mCol) => exact .merkleCollision mCol
          | .inr (.inr (.inl pCol)) => exact .wotsPkCollision pCol
          | .inr (.inr (.inr (.inl sCol))) => exact .wotsStepCollision sCol
          | .inr (.inr (.inr (.inr chBrk))) => exact .wotsSecretChainBreak chBrk
          | .inl ⟨entry0, hQ0, hExt0⟩ =>
            let honestFPk := honestForsPk geom skSeed pkSeed leafGlobalIdx
            if hFPkEq : forsPk = honestFPk then
              unfold verifyAndRecoverForsPk at hForsVer
              cases hFLen : (forsIndices.length == geom.forsTrees &&
                             forgedSig.forsOpenings.length == geom.forsTrees)
              · simp [hFLen] at hForsVer
              · simp only [hFLen, ↓reduceIte] at hForsVer
                cases hFTrees : verifyForsTreesAux geom pk.pkSeed leafGlobalIdx 0
                                  forsIndices forgedSig.forsOpenings with
                | none => simp [hFTrees] at hForsVer
                | some rootsF =>
                  simp only [hFTrees, Option.some.injEq] at hForsVer
                  let rootsH := (List.range geom.forsTrees).map
                    (honestForsTreeRoot geom skSeed pkSeed leafGlobalIdx)
                  if hRtsEq : rootsF = rootsH then
                    have hRtsShift :
                        rootsF = (List.range forsIndices.length).map (fun i =>
                          honestForsTreeRoot geom skSeed pk.pkSeed leafGlobalIdx (0 + i)) := by
                      have hPkSeed : pk.pkSeed = pkSeed := rfl
                      rw [hRtsEq, hForsIdxLen, hPkSeed]
                      dsimp only [rootsH]
                      congr 1
                      funext i
                      rw [Nat.zero_add]
                    match extractForsTreesOrBreak geom skSeed pk.pkSeed leafGlobalIdx revealedFors
                            0 forsIndices forgedSig.forsOpenings rootsF hFTrees hRtsShift with
                    | .inr (.inl mCol) => exact .merkleCollision mCol
                    | .inr (.inr (.inl lCol)) => exact .forsLeafCollision lCol
                    | .inr (.inr (.inr uSec)) => exact .forsUnqueriedSecret uSec
                    | .inl ⟨_, hAllCov⟩ =>
                      exact .statelessForsCover {
                        forsPos       := hForsPos
                        leafGlobalIdx := leafGlobalIdx
                        indices       := forsIndices
                        xofEq         := hXof
                        allCovered    := fun t ht => by
                          simpa only [Nat.zero_add] using hAllCov t ht
                      }
                  else
                    have hHonFPkDef : honestFPk = compressForsRootsSponge geom pk.pkSeed leafGlobalIdx rootsH := by
                      dsimp only [honestFPk, rootsH, pk, deriveAggPublicKey]
                      unfold honestForsPk
                      rfl
                    exact .forsRootsCollision {
                      leafGlobalIdx := leafGlobalIdx
                      roots1        := rootsF
                      roots2        := rootsH
                      neInputs      := hRtsEq
                      spongeEq      := hForsVer.trans (hFPkEq.trans hHonFPkDef)
                    }
            else
              have hHon0 := hStatelessHonest0 hForsNe leafGlobalIdx entry0 hQ0
              have hPairNe : (lsig0.tswCtr, forsPk) ≠ (entry0.tswCtr, honestFPk) :=
                fun hEq => hFPkEq (congrArg Prod.snd hEq)
              exact .hmsgOrMuCollision
                (.detTreeCodewordCollision 0 tr0 kp0 lsig0.tswCtr entry0.tswCtr
                  forsPk honestFPk entry0.digits hPairNe hExt0 hHon0)
      · -- Stateful XMSS (`geom.forsTrees = 0`)
        simp only [hFors0, ↓reduceIte] at hVer
        unfold verifyAggNativeSigStateful at hVer
        have hForsEq0 : geom.forsTrees = 0 := eq_of_beq hFors0
        cases hSChk : (!forgedSig.forsOpenings.isEmpty ||
                       !(decide (forgedSig.statefulLeafIdx < 2 ^ (geom.numLayers * geom.subtreeHeight))))
        · simp only [hSChk, Bool.false_eq_true, ↓reduceIte] at hVer
          simp only [Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq] at hSChk
          have hLeafLt := hSChk.2
          let kp0 := forgedSig.statefulLeafIdx % (2 ^ geom.subtreeHeight)
          let tr0 := forgedSig.statefulLeafIdx / (2 ^ geom.subtreeHeight)
          let hmsg0 := computeHmsgStateful pk forgedSig.rRand mu kp0 lsig0.tswCtr
          change (match verifyWotsLayer geom pk 0 tr0 kp0 hmsg0 lsig0 with
                  | none => false
                  | some root0 =>
                    match verifyUpperLayers geom pk 1 tr0 root0 upperLayers with
                    | none => false
                    | some topRoot => topRoot == pk.pkRoot) = true at hVer
          cases hW0 : verifyWotsLayer geom pk 0 tr0 kp0 hmsg0 lsig0 with
          | none => rw [hW0] at hVer; cases hVer
          | some root0 =>
            rw [hW0] at hVer
            dsimp only at hVer
            cases hUp : verifyUpperLayers geom pk 1 tr0 root0 upperLayers with
            | none => rw [hUp] at hVer; cases hVer
            | some topRoot =>
              rw [hUp] at hVer
              dsimp only at hVer
              have hTopEq : topRoot = pk.pkRoot := eq_of_beq hVer
              have hTopHonest :
                  topRoot = honestSubtreeRoot geom skSeed pk.pkSeed
                    (1 + upperLayers.length - 1) (tr0 / 2 ^ (upperLayers.length * geom.subtreeHeight)) := by
                have hL : 1 + upperLayers.length - 1 = geom.numLayers - 1 := by omega
                have hR : tr0 / 2 ^ (upperLayers.length * geom.subtreeHeight) = 0 := by
                  dsimp only [tr0]
                  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
                  have hE : geom.subtreeHeight + upperLayers.length * geom.subtreeHeight =
                      geom.numLayers * geom.subtreeHeight := by
                    rw [← hUpperLen, Nat.add_mul, Nat.one_mul, Nat.add_comm]
                  rw [hE]
                  exact Nat.div_eq_of_lt hLeafLt
                rw [hL, hR]
                exact hTopEq
              match extractUpperHypertreeOrBreak geom skSeed pk msg forgedSig.rRand qWots revealedFors
                      hChainsLe hTargetBound hOracleValid hUpperHonest
                      upperLayers 1 tr0 root0 topRoot (by decide) hUp hTopHonest with
              | .inr brk => exact brk
              | .inl hRoot0Eq =>
                match extractSingleWotsLayerOrBreak geom skSeed pk qWots hChainsLe hTargetBound
                        0 tr0 kp0 (Nat.mod_lt _ hPowPos) hmsg0 lsig0 root0 hW0 hRoot0Eq
                        (hOracleValid 0 tr0 kp0) with
                | .inr (.inl mCol) => exact .merkleCollision mCol
                | .inr (.inr (.inl pCol)) => exact .wotsPkCollision pCol
                | .inr (.inr (.inr (.inl sCol))) => exact .wotsStepCollision sCol
                | .inr (.inr (.inr (.inr chBrk))) => exact .wotsSecretChainBreak chBrk
                | .inl ⟨entry0, hQ0, hExt0⟩ =>
                  obtain ⟨hMsgInQ, hHon0⟩ := hStatefulHonest0 hForsEq0 tr0 kp0 entry0 hQ0
                  have hMsgNe : msg ≠ entry0.queriedMsg := fun hEq => hFreshMsg (hEq ▸ hMsgInQ)
                  let muQ := computeMessageMu pk entry0.queriedMsg
                  if hMuEq : mu = muQ then
                    let f1 := encodeMultiFrame [qsagMuTagBytes, encodeAggValidatorPkBytes pk, msg]
                    let f2 := encodeMultiFrame [qsagMuTagBytes, encodeAggValidatorPkBytes pk, entry0.queriedMsg]
                    have hFrameNe : f1 ≠ f2 := fun hFEq => by
                      have hListEq := encodeMultiFrame_injective hFEq
                      simp only [List.cons.injEq, and_true, true_and] at hListEq
                      exact hMsgNe hListEq
                    have hHashEq : poseidon2Hash32 f1 = poseidon2Hash32 f2 := by
                      have hMuUnfold : bytes32ToDigest5 (poseidon2Hash32 f1) = bytes32ToDigest5 (poseidon2Hash32 f2) := by
                        dsimp only [mu, muQ, f1, f2] at hMuEq ⊢
                        unfold computeMessageMu at hMuEq
                        exact hMuEq
                      exact bytes32ToDigest5_injective (poseidon2Hash32_length f1) (poseidon2Hash32_length f2) hMuUnfold
                    exact .hmsgOrMuCollision (.muPoseidon2Collision ⟨f1, f2, hFrameNe, hHashEq⟩)
                  else
                    have hTupNe : (forgedSig.rRand, mu, lsig0.tswCtr) ≠
                                  (entry0.rRand, muQ, entry0.tswCtr) :=
                      fun hEq => hMuEq (congrArg (fun t => t.2.1) hEq)
                    exact .hmsgOrMuCollision
                      (.statefulCodewordCollision kp0 forgedSig.rRand entry0.rRand mu muQ
                        lsig0.tswCtr entry0.tswCtr entry0.digits hTupNe hExt0 hHon0)
        · simp [hSChk] at hVer
  · simp [hHdr] at hVer

/-- **Packed 4-Limb `Poseidon2` WOTS+C + Merkle EUF-CMA Soundness (`aggNativeSig_wots_merkle_soundness`)**:
    Any accepted signature `forgedSig` on an unqueried message `msg ∉ queriedMsgs` constructively
    yields a concrete `AggNativeForgeryBreak` (secret-anchored WOTS+C backward
    chain preimage, unqueried FORS secret, Merkle/sponge/step collision, or stateless FORS subset cover)! -/
theorem aggNativeSig_wots_merkle_soundness
    (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (msg : List UInt8) (forgedSig : AggNativeSignature)
    (queriedMsgs : List (List UInt8))
    (qWots : QueriedWotsDigitsOracle)
    (revealedFors : List (Nat × Nat × Nat))
    (hFreshMsg : msg ∉ queriedMsgs)
    (hVer : verifyAggNativeSig geom (deriveAggPublicKey geom skSeed pkSeed) msg forgedSig = true)
    (hOracleValid : ∀ l tr kp entry, qWots l tr kp = some entry →
      entry.digits.length = geom.wotsChains ∧
      listNatSum entry.digits = geom.targetSum ∧
      (∀ x ∈ entry.digits, x < 4))
    (hUpperHonest : ∀ (l rem : Nat) (entry : QueriedWotsEntry),
      0 < l →
      qWots l (rem / 2 ^ geom.subtreeHeight) (rem % 2 ^ geom.subtreeHeight) = some entry →
      extractWotsDigitsChecked geom
        (computeHmsgDetTree (deriveAggPublicKey geom skSeed pkSeed) l
          (rem / 2 ^ geom.subtreeHeight) (rem % 2 ^ geom.subtreeHeight)
          entry.tswCtr (honestSubtreeRoot geom skSeed pkSeed (l - 1) rem)) = some entry.digits)
    (hStatefulHonest0 : geom.forsTrees = 0 →
      ∀ (tr0 kp0 : Nat) (entry : QueriedWotsEntry),
        qWots 0 tr0 kp0 = some entry →
        entry.queriedMsg ∈ queriedMsgs ∧
        extractWotsDigitsChecked geom
          (computeHmsgStateful (deriveAggPublicKey geom skSeed pkSeed) entry.rRand
            (computeMessageMu (deriveAggPublicKey geom skSeed pkSeed) entry.queriedMsg)
            kp0 entry.tswCtr) = some entry.digits)
    (hStatelessHonest0 : geom.forsTrees ≠ 0 →
      ∀ (leafIdx : Nat) (entry : QueriedWotsEntry),
        qWots 0 (leafIdx / 2 ^ geom.subtreeHeight) (leafIdx % 2 ^ geom.subtreeHeight) = some entry →
        extractWotsDigitsChecked geom
          (computeHmsgDetTree (deriveAggPublicKey geom skSeed pkSeed) 0
            (leafIdx / 2 ^ geom.subtreeHeight) (leafIdx % 2 ^ geom.subtreeHeight)
            entry.tswCtr (honestForsPk geom skSeed pkSeed leafIdx)) = some entry.digits) :
    Nonempty (AggNativeForgeryBreak geom skSeed (deriveAggPublicKey geom skSeed pkSeed)
                msg forgedSig.rRand qWots revealedFors) :=
  ⟨extractAggNativeForgeryBreak geom skSeed pkSeed msg forgedSig queriedMsgs qWots revealedFors
     hFreshMsg hVer hOracleValid hUpperHonest hStatefulHonest0 hStatelessHonest0⟩

/-- **`#tooth` Wrong WOTS+C Target-Sum Rejection (`tooth_wrong_wots_sum_rejected`)**:
    Any layer signature whose extracted base-4 digits fail `listNatSum ds = geom.targetSum` is
    unconditionally rejected by `verifyWotsLayer`. -/
theorem tooth_wrong_wots_sum_rejected
    (geom : AggSigGeometry) (pk : AggValidatorPk) (layer treeIdx kpIdx : Nat)
    (hmsg : Digest5) (lsig : WotsLayerSig) (ds : List Nat)
    (hExt : extractWotsDigitsChecked geom hmsg = some ds)
    (hBadSum : listNatSum ds ≠ geom.targetSum) :
    verifyWotsLayer geom pk layer treeIdx kpIdx hmsg lsig = none := by
  unfold verifyWotsLayer
  cases hLen : (lsig.wotsChains.length == geom.wotsChains && lsig.merklePath.length == geom.subtreeHeight)
  · simp
  · simp only [↓reduceIte, hExt]
    have hBeqF : (listNatSum ds == geom.targetSum) = false := beq_false_of_ne hBadSum
    simp [hBeqF]

/-- **`#tooth` Corrupted Public Root Rejection (`tooth_mismatched_top_root_rejected`)**:
    Replacing `pk.pkRoot` with any root differing from the walked hypertree top root causes
    `verifyAggNativeSig` to reject whenever `mu` is unchanged, and `verifyUpperLayers` comparison
    rejects any mismatched top root directly. -/
theorem tooth_mismatched_top_root_rejected
    (geom : AggSigGeometry) (pk : AggValidatorPk) (msg : List UInt8) (sig : AggNativeSignature)
    (hFors0 : geom.forsTrees = 0)
    (lsig0 : WotsLayerSig) (upper : List WotsLayerSig) (hLayers : sig.layers = lsig0 :: upper)
    (root0 topRoot : Digest4)
    (hW0 : verifyWotsLayer geom pk 0 (sig.statefulLeafIdx / 2 ^ geom.subtreeHeight)
             (sig.statefulLeafIdx % 2 ^ geom.subtreeHeight)
             (computeHmsgStateful pk sig.rRand (computeMessageMu pk msg)
               (sig.statefulLeafIdx % 2 ^ geom.subtreeHeight) lsig0.tswCtr) lsig0 = some root0)
    (hUp : verifyUpperLayers geom pk 1 (sig.statefulLeafIdx / 2 ^ geom.subtreeHeight) root0 upper = some topRoot)
    (hBadRoot : topRoot ≠ pk.pkRoot) :
    verifyAggNativeSig geom pk msg sig = false := by
  unfold verifyAggNativeSig
  cases hHdr : (!geom.wellFormed || pk.profile != geom.profile || sig.profile != geom.profile ||
                sig.layers.length != geom.numLayers)
  · simp only [Bool.false_eq_true, ↓reduceIte, hLayers, hFors0, beq_self_eq_true]
    unfold verifyAggNativeSigStateful
    cases hSChk : (!sig.forsOpenings.isEmpty ||
                   !(decide (sig.statefulLeafIdx < 2 ^ (geom.numLayers * geom.subtreeHeight))))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hW0]
      dsimp only
      rw [hUp]
      exact beq_false_of_ne hBadRoot
    · rfl
  · rfl

/-- Concrete inhabitedness witness for §1 (`xmssPoseidon2Geom` & `corduroyPoseidon2Geom` geometries +
    non-vacuous EUF-CMA reduction pipeline with concrete seeds and empty signing oracle). -/
def auditSkSeed : Digest4 :=
  ⟨Goldilocks.ofNat 11, Goldilocks.ofNat 22, Goldilocks.ofNat 33, Goldilocks.ofNat 44⟩
def auditPkSeed : Digest4 :=
  ⟨Goldilocks.ofNat 55, Goldilocks.ofNat 66, Goldilocks.ofNat 77, Goldilocks.ofNat 88⟩
def auditRRand : Digest4 :=
  ⟨Goldilocks.ofNat 99, Goldilocks.ofNat 101, Goldilocks.ofNat 102, Goldilocks.ofNat 103⟩
def auditMsg : List UInt8 := [0x51, 0x53, 0x41, 0x47]

theorem inhabited_aggNativeSig_euf_cma_pipeline :
    xmssPoseidon2Geom.wellFormed = true ∧
    corduroyPoseidon2Geom.wellFormed = true ∧
    compactAuditGeom.wellFormed = true ∧
    (∀ (ctrs : ValidSigningCtrs xmssPoseidon2Geom auditSkSeed
                 (deriveAggPublicKey xmssPoseidon2Geom auditSkSeed auditPkSeed)
                 auditMsg auditRRand 0),
      let pk := deriveAggPublicKey xmssPoseidon2Geom auditSkSeed auditPkSeed
      let sig := signAggNative xmssPoseidon2Geom auditSkSeed pk
                   auditMsg auditRRand 0 ctrs.layer0Ctr ctrs.upperCtrs
      verifyAggNativeSig xmssPoseidon2Geom pk auditMsg sig = true ∧
      Nonempty (AggNativeForgeryBreak xmssPoseidon2Geom auditSkSeed pk
                  auditMsg sig.rRand (fun _ _ _ => none) [])) := by
  refine ⟨deployedAggGeometries_wellFormed.1,
          deployedAggGeometries_wellFormed.2.1,
          deployedAggGeometries_wellFormed.2.2,
          fun ctrs => ?_⟩
  have hVer := aggNativeSig_completeness xmssPoseidon2Geom auditSkSeed auditPkSeed
    auditMsg auditRRand 0 deployedAggGeometries_wellFormed.1 ctrs
  refine ⟨hVer, ?_⟩
  exact aggNativeSig_wots_merkle_soundness
    xmssPoseidon2Geom auditSkSeed auditPkSeed auditMsg _ [] (fun _ _ _ => none) []
    (by simp) hVer
    (fun _ _ _ _ h => by cases h)
    (fun _ _ _ _ h => by cases h)
    (fun _ _ _ _ h => by cases h)
    (fun hNe => False.elim (hNe rfl))

end Qsag

end

public section

namespace Qsag

#export_eqns compressForsRootsSponge
#export_eqns verifyAggNativeSig
#export_eqns verifyAggNativeSigStateful
#export_eqns verifyAggNativeSigStateless
#export_eqns verifyAndRecoverForsPk
#export_eqns verifyForsTreesAux
#export_eqns verifySingleForsOpening
#export_eqns verifyUpperLayers
#export_eqns verifyWotsLayer
#export_eqns verifyForsPoly verifyUpperPoly recoverAggWotsEndpoints recoverEndpointsPoly
#export_eqns statelessXofSpongeState
#export_eqns forsLeafHash forsLeafAddr forsTreeNodeAddr
#export_eqns forsKpIdx forsHyperTreeIdx forsLeafTweak4
#export_eqns deriveStatelessLeafAndForsChecked
#export_eqns statelessForsSourceLimb
end Qsag

end

public section

namespace Qsag

#export_eqns auditSkSeed auditPkSeed auditRRand auditMsg
private theorem compactHonestWotsPk_eq (skSeed pkSeed : Digest4)
    (layer treeIdx kpIdx : Nat) :
    honestWotsPk compactAuditGeom skSeed pkSeed layer treeIdx kpIdx =
      compactHonestWotsPk skSeed pkSeed layer treeIdx kpIdx := by
  unfold honestWotsPk honestWotsEndpoints
  rw [compactAuditGeom.public_eq_1]
  have hRange2 : List.range 2 = [0, 1] := rfl
  dsimp only
  rw [hRange2, List.map_cons, List.map_cons, List.map_nil,
      compactWotsPk2_eq, compactWotsWalk_eq, compactWotsWalk_eq,
      compactWotsSecret_eq, compactWotsSecret_eq,
      ← compactHonestWotsPk_eq_def]

theorem deriveAggPublicKey_compactAuditGeom (skSeed pkSeed : Digest4) :
    deriveAggPublicKey compactAuditGeom skSeed pkSeed =
      ⟨.xmssPoseidon2, pkSeed, compactJortsPkRoot skSeed pkSeed⟩ := by
  have hProf : compactAuditGeom.profile = .xmssPoseidon2 := by rw [compactAuditGeom.public_eq_1] <;> rfl
  have hSubH : compactAuditGeom.subtreeHeight = 1 := by rw [compactAuditGeom.public_eq_1] <;> rfl
  have hTop : compactAuditGeom.numLayers - 1 = 0 := by rw [compactAuditGeom.public_eq_1] <;> rfl
  unfold deriveAggPublicKey honestSubtreeRoot
  rw [buildMerkleNodeAt.public_eq_1, hProf, hSubH, hTop]
  simp only [buildMerkleNodePoly.public_eqs, merkleAddrNodeHash, xmssNodeAddr.public_eqs]
  rw [compactHonestWotsPk_eq, compactHonestWotsPk_eq, compactMerkleNode_eq,
      ← compactJortsPkRoot_eq_def]

theorem signAggNative_compactAuditGeom (skSeed pkSeed pkRoot : Digest4)
    (msg : List UInt8) (rRand : Digest4) (leafIdx ctr : Nat) :
    signAggNative compactAuditGeom skSeed ⟨.xmssPoseidon2, pkSeed, pkRoot⟩
        msg rRand leafIdx ctr [] =
      let cp := compactJortsSign1 skSeed pkSeed pkRoot msg rRand leafIdx ctr
      ⟨.xmssPoseidon2, rRand, leafIdx, [], [⟨ctr, cp.1, cp.2⟩]⟩ := by
  have hProf : compactAuditGeom.profile = .xmssPoseidon2 := by rw [compactAuditGeom.public_eq_1] <;> rfl
  have hFors : (compactAuditGeom.forsTrees == 0) = true := by rw [compactAuditGeom.public_eq_1] <;> rfl
  have hSubH : compactAuditGeom.subtreeHeight = 1 := by rw [compactAuditGeom.public_eq_1] <;> rfl
  unfold signAggNative signUpperLayersAux signUpperPoly signWotsLayerWithDigits
  simp only [buildMerkleAuthPathAt.public_eq_1, hProf, hFors, hSubH, ↓reduceIte, Nat.pow_one]
  simp only [buildMerkleAuthPathPoly.public_eqs]
  rw [computeHmsgStateful_xmss_eq, extractWotsDigitsChecked_compactAuditGeom]
  have hChk : checkDigest5Limbs63
      (let h := compactJortsHmsgStateful pkSeed pkRoot rRand msg (leafIdx % 2) ctr
       ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩) =
    compactCheck5Limbs63
      (compactJortsHmsgStateful pkSeed pkRoot rRand msg (leafIdx % 2) ctr) := by
    rw [checkDigest5Limbs63.public_eq_1, compactCheck5Limbs63_eq_def]
  rw [hChk, compactJortsSign1_eq_def]
  dsimp only
  rw [compactHonestWotsPk_eq]
  cases compactCheck5Limbs63
      (compactJortsHmsgStateful pkSeed pkRoot rRand msg (leafIdx % 2) ctr) with
  | false => rfl
  | true =>
    simp only [↓reduceIte, Option.getD_some, List.length_cons, List.length_nil]
    have hR2 : List.range 2 = [0, 1] := rfl
    rw [hR2, List.map_cons, List.map_cons, List.map_nil]
    have hGet0 : ∀ (a b : Nat), ([a, b])[0]! = a := fun _ _ => rfl
    have hGet1 : ∀ (a b : Nat), ([a, b])[1]! = b := fun _ _ => rfl
    rw [hGet0, hGet1, compactWotsWalk_eq, compactWotsWalk_eq,
        compactWotsSecret_eq, compactWotsSecret_eq]

theorem verifyAggNativeSig_compactAuditGeom (pkSeed pkRoot : Digest4)
    (msg : List UInt8) (rRand : Digest4) (leafIdx ctr : Nat) (c0 c1 s0 : Digest4) :
    verifyAggNativeSig compactAuditGeom ⟨.xmssPoseidon2, pkSeed, pkRoot⟩ msg
        ⟨.xmssPoseidon2, rRand, leafIdx, [], [⟨ctr, [c0, c1], [s0]⟩]⟩ =
      compactJortsVerify1 pkSeed pkRoot msg rRand leafIdx ctr c0 c1 s0 := by
  have hWf : compactAuditGeom.wellFormed = true := deployedAggGeometries_wellFormed.2.2
  have hTopGuard :
      (!compactAuditGeom.wellFormed ||
       (AggSigProfile.xmssPoseidon2 != compactAuditGeom.profile) ||
       (AggSigProfile.xmssPoseidon2 != compactAuditGeom.profile) ||
       (([⟨ctr, [c0, c1], [s0]⟩] : List WotsLayerSig).length != compactAuditGeom.numLayers)) =
      false := by
    rw [hWf, compactAuditGeom.public_eq_1]; rfl
  have hFors : (compactAuditGeom.forsTrees == 0) = true := by rw [compactAuditGeom.public_eq_1] <;> rfl
  have hChainsOk :
      ((([c0, c1] : List Digest4).length == compactAuditGeom.wotsChains) &&
       (([s0] : List Digest4).length == compactAuditGeom.subtreeHeight)) = true := by
    rw [compactAuditGeom.public_eq_1] <;> rfl
  have hPow : 2 ^ (compactAuditGeom.numLayers * compactAuditGeom.subtreeHeight) = 2 := by rw [compactAuditGeom.public_eq_1] <;> rfl
  have hSubPow : 2 ^ compactAuditGeom.subtreeHeight = 2 := by rw [compactAuditGeom.public_eq_1] <;> rfl
  have hTsum : compactAuditGeom.targetSum = 3 := by rw [compactAuditGeom.public_eq_1] <;> rfl
  unfold verifyAggNativeSig verifyAggNativeSigStateful verifyWotsLayer
    verifyUpperLayers verifyUpperPoly recoverAggWotsEndpoints recoverEndpointsPoly
    merkleWalkRoot merkleWalkPoly merkleAddrNodeHash
  simp only [xmssNodeAddr.public_eqs]
  unfold listNatSum
  simp only [hTopGuard, hFors, hPow, hSubPow, hChainsOk, hTsum,
    Bool.false_eq_true, ↓reduceIte, List.isEmpty_nil, Bool.not_true, Bool.false_or]
  rw [compactJortsVerify1_eq_def]
  cases decide (leafIdx < 2) with
  | false => rfl
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [computeHmsgStateful_xmss_eq, extractWotsDigitsChecked_compactAuditGeom]
    have hChk : checkDigest5Limbs63
        (let h := compactJortsHmsgStateful pkSeed pkRoot rRand msg (leafIdx % 2) ctr
         ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩) =
      compactCheck5Limbs63
        (compactJortsHmsgStateful pkSeed pkRoot rRand msg (leafIdx % 2) ctr) := by
      rw [checkDigest5Limbs63.public_eq_1, compactCheck5Limbs63_eq_def]
    rw [hChk]
    cases compactCheck5Limbs63
        (compactJortsHmsgStateful pkSeed pkRoot rRand msg (leafIdx % 2) ctr) with
    | false => rfl
    | true =>
      simp only [↓reduceIte, listNatSum]
      cases ((compactJortsHmsgStateful pkSeed pkRoot rRand msg (leafIdx % 2) ctr).1.val % 4 +
          ((compactJortsHmsgStateful pkSeed pkRoot rRand msg (leafIdx % 2) ctr).1.val / 4 % 4 + 0) ==
        3) with
      | false => rfl
      | true =>
        simp only [↓reduceIte, recoverEndpointsPoly, merkleWalkPoly]
        rw [compactWotsWalk_eq, compactWotsWalk_eq, compactWotsPk2_eq]
        cases (leafIdx % 2 == 0) with
        | false => simp only [compactMerkleNode_eq]
        | true => simp only [compactMerkleNode_eq]

#verify_constructive
  Qsag.deriveAggPublicKey_compactAuditGeom
  Qsag.signAggNative_compactAuditGeom
  Qsag.verifyAggNativeSig_compactAuditGeom

end Qsag
end

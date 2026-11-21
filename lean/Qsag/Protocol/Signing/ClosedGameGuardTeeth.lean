module
/-
# Qsag.Protocol.Signing.ClosedGameGuardTeeth — Probability-`1` WOTS+C Target-Sum Guard Refutation

Pairs the `hCand`-free adaptive EUF-CMA security bound of `FullAdaptiveEufCma` against an explicit
probability-`1` (`∀ ω, win ω = true`) 1-query, 1-hash-step adaptive forgery refutation when the
WOTS+C target-sum check `checkTargetSum` is disabled (`Guard (b)`):

* `tswGuardSuite_full_adaptive_forger_bound`: with `checkTsw = true` (`checkTargetSum` ON),
  `BeltLatch` ON, and `HashAdrs` ON, `execEufCmaGameWithTsw true` satisfies the universal
  `hCand`-free bound `≤ 12 · εPre` across all adaptive `(qHash, qSign)` adversaries.
* `tooth_disabled_checkTargetSum_one_query_forges_prob_one`: flipping `checkTsw = false` on the
  **identical** suite, parameters, keygen, and `BeltLatch` lets the **1-signing-query,
  1-hash-query** adversary `oneQueryOneStepNoTswForger` hash chain `0` forward by **1 single
  step** and win on **every coin `ω` (`winProb = 1`)**.

(See `AdrsSeparationGuardTeeth` for the companion Guard (c) `HashAdrs` leaf/layer tweak-separation
probability-`1` refutation `tooth_zeroed_adrs_leaf_layer_forges_prob_one`.)
-/

public import Qsag.Protocol.Signing.FullAdaptiveEufCma
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-! ## §1. Guard (b): `checkTargetSum` Disabled (`1` Signing Query + `1` Forward Step Forges `winProb = 1`) -/

def verifyProductionHypertreeLayersWithTsw (checkTsw : Bool)
    (suite : TweakableHashSuite) (params : PqHashParams) (pkSeed pkRoot rRand : List UInt8) :
    Nat → Nat → List UInt8 → List LayerXmssSig → Option (List UInt8)
  | _, _, curRoot, [] => some curRoot
  | layerIdx, globalIdx, curRoot, lsig :: rest =>
    if !(decide (lsig.tswCtr < 2 ^ 32)) then none
    else
      let subLeaves := 2 ^ params.subtreeHeight
      let kpIdx := globalIdx % subLeaves
      let kpU32 := UInt32.ofNat kpIdx
      let treeIdxNat := globalIdx / subLeaves
      let treeIdx := UInt64.ofNat treeIdxNat
      let layerU32 := UInt32.ofNat layerIdx
      let hmsg := productionLayerDigest suite params rRand pkSeed pkRoot curRoot layerIdx
        treeIdx kpU32 lsig.tswCtr
      match extractBaseWDigitsChecked params.w params.ell1 hmsg with
      | none => none
      | some digits =>
        if checkTsw && !(checkTargetSum params.w params.ell1 params.targetSum digits) then none
        else if lsig.wotsChains.length ≠ params.ell1 then none
        else
          let wotsPk := recoverWotsPkFromSig suite params pkSeed layerU32 treeIdx kpIdx digits
            lsig.wotsChains
          match walkMerkleAuthPathKp suite pkSeed layerU32 treeIdx .tree 0 params.subtreeHeight
            0 kpIdx wotsPk lsig.authPath with
          | none => none
          | some nextSubtreeRoot =>
            verifyProductionHypertreeLayersWithTsw checkTsw suite params pkSeed pkRoot rRand
              (layerIdx + 1) treeIdxNat nextSubtreeRoot rest

theorem verifyProductionHypertreeLayersWithTsw_true
    (suite : TweakableHashSuite) (params : PqHashParams) (pkSeed pkRoot rRand : List UInt8) :
    ∀ (layerIdx globalIdx : Nat) (curRoot : List UInt8) (sigs : List LayerXmssSig),
      verifyProductionHypertreeLayersWithTsw true suite params pkSeed pkRoot rRand layerIdx
        globalIdx curRoot sigs =
        verifyProductionHypertreeLayers suite params pkSeed pkRoot rRand layerIdx globalIdx
          curRoot sigs
  | _, _, curRoot, [] => by rw [verifyProductionHypertreeLayers_nil]; rfl
  | layerIdx, globalIdx, curRoot, lsig :: rest => by
    unfold verifyProductionHypertreeLayersWithTsw
    rw [verifyProductionHypertreeLayers_cons]
    dsimp only
    simp only [Bool.true_and]
    cases (!decide (lsig.tswCtr < 2 ^ 32))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases extractBaseWDigitsChecked params.w params.ell1 _ with
      | none => rfl
      | some digits =>
        dsimp only
        cases (!checkTargetSum params.w params.ell1 params.targetSum digits)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          by_cases hLen : lsig.wotsChains.length ≠ params.ell1
          · rw [ite_eq_left hLen, ite_eq_left hLen]
          · rw [ite_eq_right hLen, ite_eq_right hLen]
            cases walkMerkleAuthPathKp suite pkSeed (UInt32.ofNat layerIdx)
                (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) .tree 0
                params.subtreeHeight 0 (globalIdx % 2 ^ params.subtreeHeight) _ lsig.authPath with
            | none => rfl
            | some _ =>
              exact verifyProductionHypertreeLayersWithTsw_true suite params pkSeed pkRoot rRand
                _ _ _ rest
        · simp only [↓reduceIte]
    · simp only [↓reduceIte]

def verifyProductionPqHashSigWithTsw (checkTsw : Bool)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig) : Bool :=
  if !params.productionWellFormed || !params.productionLeafIdxInRange sig.leafGlobalIdx then false
  else if sig.layerSigs.length ≠ params.numLayers || sig.msgTswCtr ≠ 0 then false
  else
    let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
    if params.statefulJorts then
      if !sig.forsOpenings.isEmpty then false
      else
        match verifyProductionHypertreeLayersWithTsw checkTsw suite params pk.pkSeed pk.pkRoot
          sig.rRand 0 sig.leafGlobalIdx mu sig.layerSigs with
        | some computedTopRoot => decide (computedTopRoot = pk.pkRoot)
        | none => false
    else
      if sig.forsOpenings.length ≠ params.forsTrees then false
      else
        match deriveProductionStatelessInputs suite params sig.rRand pk.pkSeed pk.pkRoot mu with
        | none => false
        | some (derivedLeafIdx, idxs) =>
          if sig.leafGlobalIdx ≠ derivedLeafIdx then false
          else
            let subLeaves := 2 ^ params.subtreeHeight
            let kp0 := sig.leafGlobalIdx % subLeaves
            let tree0 := UInt64.ofNat (sig.leafGlobalIdx / subLeaves)
            match recoverProductionForsPk suite params pk.pkSeed tree0 kp0 idxs
              sig.forsOpenings with
            | none => false
            | some forsPk =>
              match verifyProductionHypertreeLayersWithTsw checkTsw suite params pk.pkSeed
                pk.pkRoot sig.rRand 0 sig.leafGlobalIdx forsPk sig.layerSigs with
              | some computedTopRoot => decide (computedTopRoot = pk.pkRoot)
              | none => false

theorem verifyProductionPqHashSigWithTsw_true_eq
    (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig) :
    verifyProductionPqHashSigWithTsw true suite params pk msg sig =
      verifyProductionPqHashSig suite params pk msg sig := by
  unfold verifyProductionPqHashSigWithTsw
  rw [verifyProductionPqHashSig_eq]
  dsimp only
  simp only [verifyProductionHypertreeLayersWithTsw_true]
  rfl

def execEufCmaGameWithTsw {n qHash qSign : Nat} (checkTsw : Bool) (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (keygen : Fin n → PqSecretKey)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) : Spec.FinGame n :=
  ⟨hPos, fun ω =>
    let o := execEufCmaOutcome true suite params keygen adv ω
    verifyProductionPqHashSigWithTsw checkTsw suite params (derivePublicKey suite params o.sk)
      o.msgStar o.sigStar &&
    decide (o.msgStar ∉ (productionSigningLog suite params o.sk o.queries).map Prod.fst)⟩

theorem execEufCmaGameWithTsw_true_win_eq {n qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (keygen : Fin n → PqSecretKey)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) (ω : Fin n) :
    (execEufCmaGameWithTsw true hPos suite params keygen adv).win ω =
      (ExecEufCmaGame hPos suite params keygen adv).win ω := by
  dsimp only [execEufCmaGameWithTsw]
  rw [ExecEufCmaGame, execEufCmaGameWith_win, prodEufCmaWin_eq,
    verifyProductionPqHashSigWithTsw_true_eq]

def stepOneDomDigest : List UInt8 :=
  0x73 :: List.replicate 31 0x33

private theorem stepOneDomDigest_props :
    stepOneDomDigest.length = 32 ∧
    extractBaseWDigitsChecked 4 128 stepOneDomDigest =
      some (extractBaseWDigits 4 128 stepOneDomDigest) ∧
    checkTargetSum 4 128 192 (extractBaseWDigits 4 128 stepOneDomDigest) = false ∧
    (extractBaseWDigits 4 128 stepOneDomDigest).getD 0 0 = 1 ∧
    ∀ r : Nat, 1 ≤ r → r < 128 →
      (extractBaseWDigits 4 128 stepOneDomDigest).getD r 0 =
        (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD r 0 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · unfold stepOneDomDigest
    simp only [extractBaseWDigitsChecked_eq, extractBaseWDigits_eq]
    decide +kernel
  · unfold stepOneDomDigest
    simp only [extractBaseWDigits_eq, checkTargetSum, sumDigits_eq_foldr]
    decide +kernel
  · unfold stepOneDomDigest
    simp only [extractBaseWDigits_eq]
    decide +kernel
  · have hRange : ∀ k ∈ List.range 127,
        (extractBaseWDigits 4 128 stepOneDomDigest).getD (k + 1) 0 =
          (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD (k + 1) 0 := by
      unfold stepOneDomDigest
      rw [encodeSubMsg3Hmsg.public_eqs]
      simp only [extractBaseWDigits_eq]
      decide +kernel
    intro r hr1 hr128
    have hAt := hRange (r - 1) (List.mem_range.mpr (by omega))
    have hk : r - 1 + 1 = r := by omega
    rwa [hk] at hAt

private theorem zero32_tsw_false :
    checkTargetSum 4 128 192 (extractBaseWDigits 4 128 zero32) = false := by
  simp only [zero32.public_eqs, extractBaseWDigits_eq, checkTargetSum, sumDigits_eq_foldr]
  decide +kernel

def tswGuardSuite : TweakableHashSuite where
  suiteId := "QSAG.PQ.SUITE.TSW.GUARD/v1".toByteArray.toList
  rawHash raw :=
    match parseThPreimage raw with
    | some (role, _, adrs, args) =>
      if role = tagHPre then
        match args with
        | [_, [kpB, 3]] =>
          if kpB.toNat < 4 then [0xE1, kpB, 3] ++ List.replicate 29 0x00
          else poly257MultiLeafSuite.rawHash raw
        | _ => poly257MultiLeafSuite.rawHash raw
      else if role = tagHMsg then
        match args with
        | [_, _, 0xE1 :: kpB :: 3 :: rest, _] =>
          if kpB.toNat < 4 ∧ kpB.toNat = adrs.keyPair.toNat ∧ rest = List.replicate 29 0x00 then
            stepOneDomDigest
          else poly257MultiLeafSuite.rawHash raw
        | _ => poly257MultiLeafSuite.rawHash raw
      else poly257MultiLeafSuite.rawHash raw
    | none => poly257MultiLeafSuite.rawHash raw
  rawHash_len raw := by
    split
    · split
      · repeat' split
        all_goals first | rfl | exact poly257MultiLeafSuite.rawHash_len raw
      · split
        · repeat' split
          all_goals first | exact stepOneDomDigest_props.1 |
            exact poly257MultiLeafSuite.rawHash_len raw
        · exact poly257MultiLeafSuite.rawHash_len raw
    · exact poly257MultiLeafSuite.rawHash_len raw

private def SameTreeRoles (s₁ s₂ : TweakableHashSuite) : Prop :=
  ∀ role pkSeed adrs args,
    (role = tagPrf ∨ role = tagPrfMsg ∨ role = tagThF ∨ role = tagThTl ∨ role = tagThH) →
    thCall s₁ role pkSeed adrs args = thCall s₂ role pkSeed adrs args

private theorem sameTreeRoles_wotsSecretBase {s₁ s₂ : TweakableHashSuite} (h : SameTreeRoles s₁ s₂)
    (sk : PqSecretKey) (l : UInt32) (t : UInt64) (kp r : Nat) :
    wotsSecretBase s₁ sk l t kp r = wotsSecretBase s₂ sk l t kp r := by
  rw [wotsSecretBase_eq, wotsSecretBase_eq, thSecretPrf_eq, thSecretPrf_eq]
  exact h _ _ _ _ (.inl rfl)

private theorem sameTreeRoles_thChainF {s₁ s₂ : TweakableHashSuite} (h : SameTreeRoles s₁ s₂)
    (pkSeed : List UInt8) (adrs : HashAdrs) (x : List UInt8) :
    thChainF s₁ pkSeed adrs x = thChainF s₂ pkSeed adrs x := by
  rw [thChainF_eq, thChainF_eq]
  exact h _ _ _ _ (.inr (.inr (.inl rfl)))

private theorem sameTreeRoles_wotsChainSteps {s₁ s₂ : TweakableHashSuite} (h : SameTreeRoles s₁ s₂)
    (pkSeed : List UInt8) (l : UInt32) (t : UInt64) (kp r : Nat) :
    ∀ (k st : Nat) (x : List UInt8),
      wotsChainSteps s₁ pkSeed l t kp r st k x = wotsChainSteps s₂ pkSeed l t kp r st k x
  | 0, st, x => by rw [wotsChainSteps_zero, wotsChainSteps_zero]
  | k + 1, st, x => by
    rw [wotsChainSteps_succ, wotsChainSteps_succ]
    dsimp only
    rw [sameTreeRoles_thChainF h]
    exact sameTreeRoles_wotsChainSteps h pkSeed l t kp r k (st + 1) _

private theorem sameTreeRoles_recoverWotsPk {s₁ s₂ : TweakableHashSuite} (h : SameTreeRoles s₁ s₂)
    (params : PqHashParams) (pkSeed : List UInt8)
    (l : UInt32) (t : UInt64) (kp : Nat) (digits : List Nat) (chains : List (List UInt8)) :
    recoverWotsPkFromSig s₁ params pkSeed l t kp digits chains =
      recoverWotsPkFromSig s₂ params pkSeed l t kp digits chains := by
  rw [recoverWotsPkFromSig_eq, recoverWotsPkFromSig_eq, thTweakTl_eq, thTweakTl_eq,
    h _ _ _ _ (.inr (.inr (.inr (.inl rfl)))), recoverWotsEndpoints_eq, recoverWotsEndpoints_eq]
  congr 1
  apply List.map_congr_left
  intro r _
  exact sameTreeRoles_wotsChainSteps h _ _ _ _ _ _ _ _

private theorem sameTreeRoles_computeWotsPk {s₁ s₂ : TweakableHashSuite} (h : SameTreeRoles s₁ s₂)
    (params : PqHashParams) (sk : PqSecretKey) (l : UInt32) (t : UInt64) (kp : Nat) :
    computeWotsPk s₁ params sk l t kp = computeWotsPk s₂ params sk l t kp := by
  rw [computeWotsPk_eq, computeWotsPk_eq, thTweakTl_eq, thTweakTl_eq,
    h _ _ _ _ (.inr (.inr (.inr (.inl rfl))))]
  congr 1
  apply List.map_congr_left
  intro r _
  rw [sameTreeRoles_wotsSecretBase h, sameTreeRoles_wotsChainSteps h]

private theorem sameTreeRoles_computeMerkleNodeKp {s₁ s₂ : TweakableHashSuite}
    (h : SameTreeRoles s₁ s₂) (pkSeed : List UInt8) (l : UInt32) (t : UInt64)
    (kind : AdrsKind) (kp : UInt32) (f g : Nat → List UInt8) (hfg : ∀ i, f i = g i) :
    ∀ (ht n loc : Nat),
      computeMerkleNodeKp s₁ pkSeed l t kind kp f ht n loc =
        computeMerkleNodeKp s₂ pkSeed l t kind kp g ht n loc
  | 0, _, loc => by rw [computeMerkleNodeKp_zero, computeMerkleNodeKp_zero]; exact hfg loc
  | ht + 1, n, loc => by
    rw [computeMerkleNodeKp_succ, computeMerkleNodeKp_succ]
    rw [thNodeH_eq, thNodeH_eq, h _ _ _ _ (.inr (.inr (.inr (.inr rfl))))]
    congr 1; congr 1
    · exact sameTreeRoles_computeMerkleNodeKp h pkSeed l t kind kp f g hfg ht _ _
    · congr 1
      exact sameTreeRoles_computeMerkleNodeKp h pkSeed l t kind kp f g hfg ht _ _

private theorem sameTreeRoles_computeXmssSubtreeRoot {s₁ s₂ : TweakableHashSuite}
    (h : SameTreeRoles s₁ s₂) (params : PqHashParams) (sk : PqSecretKey)
    (l : UInt32) (t : UInt64) :
    computeXmssSubtreeRoot s₁ params sk l t = computeXmssSubtreeRoot s₂ params sk l t := by
  rw [computeXmssSubtreeRoot_eq, computeXmssSubtreeRoot_eq,
    ← computeMerkleNodeKp_zero_eq, ← computeMerkleNodeKp_zero_eq]
  exact sameTreeRoles_computeMerkleNodeKp h _ _ _ _ _ _ _
    (sameTreeRoles_computeWotsPk h params sk _ _) _ _ _

private theorem sameTreeRoles_derivePublicKey {s₁ s₂ : TweakableHashSuite}
    (h : SameTreeRoles s₁ s₂) (params : PqHashParams) (sk : PqSecretKey) :
    derivePublicKey s₁ params sk = derivePublicKey s₂ params sk := by
  unfold derivePublicKey
  dsimp only
  rw [sameTreeRoles_computeXmssSubtreeRoot h]

private theorem sameTreeRoles_buildMerkleAuthPathKp {s₁ s₂ : TweakableHashSuite}
    (h : SameTreeRoles s₁ s₂) (pkSeed : List UInt8) (l : UInt32) (t : UInt64)
    (kind : AdrsKind) (kp : UInt32) (f g : Nat → List UInt8) (hfg : ∀ i, f i = g i) :
    ∀ (ht root locBase locIdx : Nat),
      buildMerkleAuthPathKp s₁ pkSeed l t kind kp f ht root locBase locIdx =
        buildMerkleAuthPathKp s₂ pkSeed l t kind kp g ht root locBase locIdx
  | 0, _, _, _ => by rw [buildMerkleAuthPathKp.public_eq_1, buildMerkleAuthPathKp.public_eq_1]
  | ht + 1, root, locBase, locIdx => by
    rw [buildMerkleAuthPathKp.public_eq_2, buildMerkleAuthPathKp.public_eq_2]
    dsimp only
    split
    · rw [sameTreeRoles_computeMerkleNodeKp h pkSeed l t kind kp f g hfg ht _ _,
        sameTreeRoles_buildMerkleAuthPathKp h pkSeed l t kind kp f g hfg ht _ _ _]
    · rw [sameTreeRoles_computeMerkleNodeKp h pkSeed l t kind kp f g hfg ht _ _,
        sameTreeRoles_buildMerkleAuthPathKp h pkSeed l t kind kp f g hfg ht _ _ _]

private theorem sameTreeRoles_walkMerkleAuthPathKp {s₁ s₂ : TweakableHashSuite}
    (h : SameTreeRoles s₁ s₂) (pkSeed : List UInt8) (l : UInt32) (t : UInt64)
    (kind : AdrsKind) (kp : UInt32) :
    ∀ (ht root localIdx : Nat) (leaf : List UInt8) (path : List (List UInt8)),
      walkMerkleAuthPathKp s₁ pkSeed l t kind kp ht root localIdx leaf path =
        walkMerkleAuthPathKp s₂ pkSeed l t kind kp ht root localIdx leaf path
  | 0, _, _, _, [] => rfl
  | 0, _, _, _, _ :: _ => rfl
  | _ + 1, _, _, _, [] => rfl
  | ht + 1, root, localIdx, leaf, sib :: rest => by
    unfold walkMerkleAuthPathKp
    dsimp only
    by_cases hHalf : localIdx < 2 ^ ht
    · simp only [hHalf, ↓reduceIte,
        sameTreeRoles_walkMerkleAuthPathKp h pkSeed l t kind kp ht _ _ _ rest]
      cases walkMerkleAuthPathKp s₂ pkSeed l t kind kp ht (2 * root) localIdx leaf rest with
      | none => rfl
      | some _ => dsimp only; rw [thNodeH_eq, thNodeH_eq, h _ _ _ _ (.inr (.inr (.inr (.inr rfl))))]
    · simp only [hHalf, ↓reduceIte,
        sameTreeRoles_walkMerkleAuthPathKp h pkSeed l t kind kp ht _ _ _ rest]
      cases walkMerkleAuthPathKp s₂ pkSeed l t kind kp ht (2 * root + 1) (localIdx - 2 ^ ht)
          leaf rest with
      | none => rfl
      | some _ => dsimp only; rw [thNodeH_eq, thNodeH_eq, h _ _ _ _ (.inr (.inr (.inr (.inr rfl))))]

private theorem tswGuardSuite_sameTreeRoles :
    SameTreeRoles tswGuardSuite poly257MultiLeafSuite := by
  have hNe : tagPrf ≠ tagHPre ∧ tagPrf ≠ tagHMsg ∧
      tagPrfMsg ≠ tagHPre ∧ tagPrfMsg ≠ tagHMsg ∧
      tagThF ≠ tagHPre ∧ tagThF ≠ tagHMsg ∧
      tagThTl ≠ tagHPre ∧ tagThTl ≠ tagHMsg ∧
      tagThH ≠ tagHPre ∧ tagThH ≠ tagHMsg := by
    simp only [tagPrf.public_eqs, tagPrfMsg.public_eqs, tagHPre.public_eqs, tagHMsg.public_eqs,
      tagThF.public_eqs, tagThTl.public_eqs, tagThH.public_eqs]
    decide +kernel
  intro role pkSeed adrs args hRole
  rw [thCall_eq, thCall_eq]
  unfold tswGuardSuite
  dsimp only
  rw [parseThPreimage_thPreimage]
  dsimp only
  rcases hRole with rfl | rfl | rfl | rfl | rfl
  · rw [ite_eq_right hNe.1, ite_eq_right hNe.2.1]
  · rw [ite_eq_right hNe.2.2.1, ite_eq_right hNe.2.2.2.1]
  · rw [ite_eq_right hNe.2.2.2.2.1, ite_eq_right hNe.2.2.2.2.2.1]
  · rw [ite_eq_right hNe.2.2.2.2.2.2.1, ite_eq_right hNe.2.2.2.2.2.2.2.1]
  · rw [ite_eq_right hNe.2.2.2.2.2.2.2.2.1, ite_eq_right hNe.2.2.2.2.2.2.2.2.2]

private theorem tswGuardSuite_thPreHash_eq (pkSeed pkRoot msg : List UInt8) :
    thPreHash tswGuardSuite pkSeed pkRoot msg =
      match msg with
      | [kpB, 3] =>
        if kpB.toNat < 4 then [0xE1, kpB, 3] ++ List.replicate 29 0x00
        else thPreHash poly257MultiLeafSuite pkSeed pkRoot msg
      | _ => thPreHash poly257MultiLeafSuite pkSeed pkRoot msg := by
  rw [thPreHash_eq, thPreHash_eq, thCall_eq, thCall_eq]
  unfold tswGuardSuite
  dsimp only
  rw [parseThPreimage_thPreimage]
  dsimp only
  rw [ite_eq_left rfl]
  cases msg with
  | nil => rfl
  | cons kpB t =>
    cases t with
    | nil => rfl
    | cons b2 rest =>
      cases rest with
      | nil =>
        by_cases hb2 : b2 = 3
        · subst hb2; rfl
        · simp [hb2]
      | cons _ _ => simp

private theorem tswGuardSuite_thHashLeafMsg_eq (rRand pkSeed pkRoot mu : List UInt8)
    (treeIdx : UInt64) (kpIdx : UInt32) (ctr : Nat) :
    thHashLeafMsg tswGuardSuite rRand pkSeed pkRoot mu treeIdx kpIdx ctr =
      match mu with
      | 0xE1 :: kpB :: 3 :: rest =>
        if kpB.toNat < 4 ∧ kpB.toNat = kpIdx.toNat ∧ rest = List.replicate 29 0x00 then
          stepOneDomDigest
        else thHashLeafMsg poly257MultiLeafSuite rRand pkSeed pkRoot mu treeIdx kpIdx ctr
      | _ => thHashLeafMsg poly257MultiLeafSuite rRand pkSeed pkRoot mu treeIdx kpIdx ctr := by
  have hNe : tagHMsg ≠ tagHPre := by
    simp only [tagHMsg.public_eqs, tagHPre.public_eqs]; decide +kernel
  rw [thHashLeafMsg_eq, thHashLeafMsg_eq, thCall_eq, thCall_eq]
  unfold tswGuardSuite
  dsimp only
  rw [parseThPreimage_thPreimage]
  dsimp only
  rw [ite_eq_right hNe, ite_eq_left rfl]
  cases mu with
  | nil => rfl
  | cons b0 t0 =>
    by_cases hb0 : b0 = 0xE1
    · subst hb0
      cases t0 with
      | nil => rfl
      | cons b1 t1 =>
        cases t1 with
        | nil => rfl
        | cons b2 t2 =>
          by_cases hb2 : b2 = 3
          · subst hb2; rfl
          · simp [hb2]
    · simp [hb0]

private theorem tswGuardSuite_thHashLeafMsg_e1 (rRand pkSeed pkRoot : List UInt8)
    (kpB : UInt8) (kpIdx : UInt32) (ctr : Nat) :
    thHashLeafMsg tswGuardSuite rRand pkSeed pkRoot ([0xE1, kpB, 3] ++ List.replicate 29 0x00)
      0 kpIdx ctr =
      if kpB.toNat < 4 ∧ kpB.toNat = kpIdx.toNat then stepOneDomDigest
      else thHashLeafMsg poly257MultiLeafSuite rRand pkSeed pkRoot
        ([0xE1, kpB, 3] ++ List.replicate 29 0x00) 0 kpIdx ctr := by
  rw [tswGuardSuite_thHashLeafMsg_eq]
  simp

private theorem grindTswLeaf_none_of_bad_hmsg (suite : TweakableHashSuite)
    (rRand pkSeed pkRoot mu : List UInt8) (kpIdx : UInt32)
    (hBad : ∀ c : Nat,
      checkTargetSum 4 128 192
        (extractBaseWDigits 4 128
          (thHashLeafMsg suite rRand pkSeed pkRoot mu 0 kpIdx c)) = false) :
    ∀ c rem : Nat,
      grindTswLeafCounterAux suite 4 128 192 rRand pkSeed pkRoot mu 0 kpIdx c rem = none
  | _, 0 => grindTswLeafCounterAux_zero _ _ _ _ _ _ _ _ _ _ _
  | c, rem + 1 => by
    rw [grindTswLeafCounterAux_succ]
    by_cases hLt : c < 2 ^ 32
    · simp only [hLt, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hExt : extractBaseWDigitsChecked 4 128
          (thHashLeafMsg suite rRand pkSeed pkRoot mu 0 kpIdx c) with
      | none => rfl
      | some digits =>
        have hDigEq : digits = extractBaseWDigits 4 128
            (thHashLeafMsg suite rRand pkSeed pkRoot mu 0 kpIdx c) := by
          rw [extractBaseWDigitsChecked_eq] at hExt
          split at hExt
          · exact (Option.some.inj hExt).symm
          · cases hExt
        dsimp only
        rw [hDigEq, hBad c]
        exact grindTswLeaf_none_of_bad_hmsg suite rRand pkSeed pkRoot mu kpIdx hBad (c + 1) rem
    · simp [hLt]

private theorem tswGuardSuite_verify_eq (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig) :
    verifyProductionPqHashSig tswGuardSuite multiLeaf4JortsParams pk msg sig =
      verifyProductionPqHashSig poly257MultiLeafSuite multiLeaf4JortsParams pk msg sig := by
  have hRoles := tswGuardSuite_sameTreeRoles
  rw [verifyProductionPqHashSig_eq, verifyProductionPqHashSig_eq]
  split
  · rfl
  · rename_i hRangeOk
    split
    · rfl
    · rename_i hShapeOk
      have hTree0 : UInt64.ofNat (sig.leafGlobalIdx / 4) = 0 := by
        have hLt4 : sig.leafGlobalIdx < 4 := by
          rw [multiLeaf4JortsParams_productionWellFormed,
            PqHashParams.productionLeafIdxInRange_eq, multiLeaf4JortsParams.public_eqs] at hRangeOk
          revert hRangeOk; simp
        rw [Nat.div_eq_of_lt hLt4]; rfl
      simp only [multiLeaf4JortsParams.public_eqs, ↓reduceIte]
      split
      · rfl
      · cases hLs : sig.layerSigs with
        | nil =>
          rw [hLs, multiLeaf4JortsParams.public_eqs] at hShapeOk
          exact absurd rfl hShapeOk
        | cons lsig rest =>
          have hRestNil : rest = [] := by
            rw [hLs, multiLeaf4JortsParams.public_eqs] at hShapeOk
            cases rest with
            | nil => rfl
            | cons x xs =>
              have hNe1 : (lsig :: x :: xs).length ≠ 1 := by
                simp only [List.length_cons]; omega
              exact False.elim (hShapeOk (by rw [decide_eq_true hNe1, Bool.true_or]))
          subst hRestNil
          rw [verifyProductionHypertreeLayers_cons, verifyProductionHypertreeLayers_cons]
          dsimp only
          cases (!decide (lsig.tswCtr < 2 ^ 32))
          · simp only [Bool.false_eq_true, ↓reduceIte]
            rw [productionLayerDigest_eq, productionLayerDigest_eq, PqHashParams.targetSum_eq]
            simp only [Bool.true_and, decide_true, ↓reduceIte, show 2 ^ 2 = 4 from rfl,
              show (128 * (4 - 1)) / 2 = 192 from rfl, hTree0]
            have hPreSplit :
                (∃ kpB : UInt8, msg = [kpB, 3] ∧ kpB.toNat < 4) ∨
                (thPreHash tswGuardSuite pk.pkSeed pk.pkRoot msg =
                   thPreHash poly257MultiLeafSuite pk.pkSeed pk.pkRoot msg ∧
                 ∀ tail, thPreHash poly257MultiLeafSuite pk.pkSeed pk.pkRoot msg ≠
                   0xE1 :: tail) := by
              have hNotE1 : ∀ tail, thPreHash poly257MultiLeafSuite pk.pkSeed pk.pkRoot msg ≠
                  0xE1 :: tail := by
                intro tail; rw [poly257MultiLeaf_thPreHash_eq]
                cases msg with
                | nil => intro h; cases h
                | cons _ t =>
                  cases t with
                  | nil => intro h; cases h
                  | cons _ r =>
                    cases r with
                    | nil => dsimp only; split <;> (intro h; cases h)
                    | cons _ _ => intro h; cases h
              cases hm : msg with
              | nil => exact .inr ⟨by rw [tswGuardSuite_thPreHash_eq], hm ▸ hNotE1⟩
              | cons kpB t =>
                cases t with
                | nil => exact .inr ⟨by rw [tswGuardSuite_thPreHash_eq], hm ▸ hNotE1⟩
                | cons b2 r =>
                  cases r with
                  | nil =>
                    by_cases hb2 : b2 = 3
                    · subst hb2
                      by_cases hLt : kpB.toNat < 4
                      · exact .inl ⟨kpB, rfl, hLt⟩
                      · exact .inr ⟨by rw [tswGuardSuite_thPreHash_eq]; simp [hLt],
                          hm ▸ hNotE1⟩
                    · exact .inr ⟨by rw [tswGuardSuite_thPreHash_eq]; simp [hb2], hm ▸ hNotE1⟩
                  | cons _ _ => exact .inr ⟨by rw [tswGuardSuite_thPreHash_eq]; simp, hm ▸ hNotE1⟩
            rcases hPreSplit with ⟨kpB, hM, hKpLt⟩ | ⟨hPreEq, hMuNotE1⟩
            · have hNot3 : ¬ (kpB.toNat < 4 ∧ (3 : UInt8).toNat < 3) :=
                fun h => absurd h.2 (by decide)
              rw [hM, tswGuardSuite_thPreHash_eq]
              simp only [hKpLt, ↓reduceIte]
              rw [poly257MultiLeaf_thPreHash_eq]
              dsimp only
              rw [ite_eq_right hNot3, tswGuardSuite_thHashLeafMsg_e1]
              have hPolyZero : thHashLeafMsg poly257MultiLeafSuite sig.rRand pk.pkSeed pk.pkRoot
                  (0xFF :: List.replicate 31 0x00) 0
                  (UInt32.ofNat (sig.leafGlobalIdx % 4)) lsig.tswCtr = zero32 := by
                rw [poly257MultiLeaf_thHashLeafMsg_eq]
                split
                · rename_i _ _ _ hEq; injection hEq with hb _; exact absurd hb (by decide)
                · rfl
              rw [hPolyZero]
              have hZExt : extractBaseWDigitsChecked 4 128 zero32 =
                  some (extractBaseWDigits 4 128 zero32) := by
                simp only [zero32.public_eqs, extractBaseWDigitsChecked_eq, extractBaseWDigits_eq]
                decide +kernel
              rw [hZExt]
              dsimp only
              rw [zero32_tsw_false]
              by_cases hHit : kpB.toNat < 4 ∧
                  kpB.toNat = (UInt32.ofNat (sig.leafGlobalIdx % 4)).toNat
              · rw [ite_eq_left hHit, stepOneDomDigest_props.2.1]
                dsimp only
                rw [stepOneDomDigest_props.2.2.1]
                rfl
              · rw [ite_eq_right hHit]
                have hPolyE1 : thHashLeafMsg poly257MultiLeafSuite sig.rRand pk.pkSeed pk.pkRoot
                    ([0xE1, kpB, 3] ++ List.replicate 29 0x00) 0
                    (UInt32.ofNat (sig.leafGlobalIdx % 4)) lsig.tswCtr = zero32 := by
                  rw [poly257MultiLeaf_thHashLeafMsg_eq]
                  split
                  · rename_i _ _ _ hEq; injection hEq with hb _; exact absurd hb (by decide)
                  · rfl
                rw [hPolyE1, hZExt]
                dsimp only
                rw [zero32_tsw_false]
                rfl
            · rw [hPreEq, tswGuardSuite_thHashLeafMsg_eq]
              have hCollapse : (match thPreHash poly257MultiLeafSuite pk.pkSeed pk.pkRoot msg with
                  | 0xE1 :: kpB :: 3 :: rest =>
                    if kpB.toNat < 4 ∧ kpB.toNat = (UInt32.ofNat (sig.leafGlobalIdx % 4)).toNat ∧
                        rest = List.replicate 29 0x00 then stepOneDomDigest
                    else thHashLeafMsg poly257MultiLeafSuite sig.rRand pk.pkSeed pk.pkRoot
                      (thPreHash poly257MultiLeafSuite pk.pkSeed pk.pkRoot msg) 0
                      (UInt32.ofNat (sig.leafGlobalIdx % 4)) lsig.tswCtr
                  | _ => thHashLeafMsg poly257MultiLeafSuite sig.rRand pk.pkSeed pk.pkRoot
                      (thPreHash poly257MultiLeafSuite pk.pkSeed pk.pkRoot msg) 0
                      (UInt32.ofNat (sig.leafGlobalIdx % 4)) lsig.tswCtr) =
                  thHashLeafMsg poly257MultiLeafSuite sig.rRand pk.pkSeed pk.pkRoot
                    (thPreHash poly257MultiLeafSuite pk.pkSeed pk.pkRoot msg) 0
                    (UInt32.ofNat (sig.leafGlobalIdx % 4)) lsig.tswCtr := by
                cases hMu : thPreHash poly257MultiLeafSuite pk.pkSeed pk.pkRoot msg with
                | nil => rfl
                | cons b0 tail =>
                  by_cases hb0 : b0 = 0xE1
                  · subst hb0; exact absurd hMu (hMuNotE1 tail)
                  · simp [hb0]
              rw [hCollapse]
              cases extractBaseWDigitsChecked 4 128 _ with
              | none => rfl
              | some digits =>
                dsimp only
                cases (!checkTargetSum 4 128 _ digits)
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  by_cases hLenC : lsig.wotsChains.length ≠ 128
                  · rw [ite_eq_left hLenC, ite_eq_left hLenC]
                  · rw [ite_eq_right hLenC, ite_eq_right hLenC,
                      sameTreeRoles_recoverWotsPk hRoles,
                      sameTreeRoles_walkMerkleAuthPathKp hRoles]
                    cases walkMerkleAuthPathKp poly257MultiLeafSuite pk.pkSeed 0 0 .tree 0 2 0
                        (sig.leafGlobalIdx % 4) _ lsig.authPath with
                    | none => rfl
                    | some _ =>
                      dsimp only
                      rw [verifyProductionHypertreeLayers_nil, verifyProductionHypertreeLayers_nil]
                · rfl
          · rfl

private theorem tswGuardSuite_prodSignQuery_eq (sk : PqSecretKey) (q : ProdSigningQuery) :
    prodSignQuery tswGuardSuite multiLeaf4JortsParams sk q =
      prodSignQuery poly257MultiLeafSuite multiLeaf4JortsParams sk q := by
  have hRoles := tswGuardSuite_sameTreeRoles
  rw [prodSignQuery_eq, prodSignQuery_eq]
  have hSt : multiLeaf4JortsParams.statefulJorts = true := by rw [multiLeaf4JortsParams.public_eqs]
  rw [ite_eq_left hSt, ite_eq_left hSt, evalProductionStatefulSign_eq, evalProductionStatefulSign_eq]
  split
  · rfl
  · dsimp only
    rw [sameTreeRoles_derivePublicKey hRoles]
    let pk := derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk
    have hPkSeed : pk.pkSeed = sk.pkSeed := by unfold pk derivePublicKey; rfl
    change signProductionHypertreeCore tswGuardSuite multiLeaf4JortsParams sk pk q.message
        (thPreHash tswGuardSuite pk.pkSeed pk.pkRoot q.message) _ q.epoch none q.grindLimit =
      signProductionHypertreeCore poly257MultiLeafSuite multiLeaf4JortsParams sk pk q.message
        (thPreHash poly257MultiLeafSuite pk.pkSeed pk.pkRoot q.message) _ q.epoch none q.grindLimit
    rw [hPkSeed]
    have hPrfEq : ∀ mu, thPrfMsg tswGuardSuite sk.skPrf q.randomness mu =
        thPrfMsg poly257MultiLeafSuite sk.skPrf q.randomness mu := fun mu => by
      rw [thPrfMsg_eq, thPrfMsg_eq]
      exact hRoles _ _ _ _ (.inr (.inl rfl))
    have hPreAndNotE1 :
        (∃ kpB : UInt8, q.message = [kpB, 3] ∧ kpB.toNat < 4) ∨
        (thPreHash tswGuardSuite sk.pkSeed pk.pkRoot q.message =
           thPreHash poly257MultiLeafSuite sk.pkSeed pk.pkRoot q.message ∧
         ∀ rest, thPreHash poly257MultiLeafSuite sk.pkSeed pk.pkRoot q.message ≠ 0xE1 :: rest) := by
      have hNotE1 : ∀ rest, thPreHash poly257MultiLeafSuite sk.pkSeed pk.pkRoot q.message ≠
          0xE1 :: rest := by
        intro rest; rw [poly257MultiLeaf_thPreHash_eq]
        cases q.message with
        | nil => intro h; cases h
        | cons _ t =>
          cases t with
          | nil => intro h; cases h
          | cons _ r =>
            cases r with
            | nil => dsimp only; split <;> (intro h; cases h)
            | cons _ _ => intro h; cases h
      cases hqm : q.message with
      | nil => exact .inr ⟨by rw [tswGuardSuite_thPreHash_eq], hqm ▸ hNotE1⟩
      | cons kpB t =>
        cases t with
        | nil => exact .inr ⟨by rw [tswGuardSuite_thPreHash_eq], hqm ▸ hNotE1⟩
        | cons b2 rest =>
          cases rest with
          | nil =>
            by_cases hb2 : b2 = 3
            · subst hb2
              by_cases hLt : kpB.toNat < 4
              · exact .inl ⟨kpB, rfl, hLt⟩
              · exact .inr ⟨by rw [tswGuardSuite_thPreHash_eq]; simp [hLt], hqm ▸ hNotE1⟩
            · exact .inr ⟨by rw [tswGuardSuite_thPreHash_eq]; simp [hb2], hqm ▸ hNotE1⟩
          | cons _ _ => exact .inr ⟨by rw [tswGuardSuite_thPreHash_eq]; simp, hqm ▸ hNotE1⟩
    rcases hPreAndNotE1 with ⟨kpB, hM, hKpLt⟩ | ⟨hPreEq, hMuNotE1⟩
    · have hNot3 : ¬ (kpB.toNat < 4 ∧ (3 : UInt8).toNat < 3) := fun h => absurd h.2 (by decide)
      rw [hM, tswGuardSuite_thPreHash_eq]
      simp only [hKpLt, ↓reduceIte]
      rw [poly257MultiLeaf_thPreHash_eq]
      dsimp only
      rw [ite_eq_right hNot3, hPrfEq, poly257MultiLeaf_thPrfMsg_eq, poly257MultiLeaf_thPrfMsg_eq,
        signProductionHypertreeCore_def, signProductionHypertreeCore_def]
      have hNumL : multiLeaf4JortsParams.numLayers = 1 := by rw [multiLeaf4JortsParams.public_eqs]
      have hSubH : multiLeaf4JortsParams.subtreeHeight = 2 := by rw [multiLeaf4JortsParams.public_eqs]
      have hW4 : multiLeaf4JortsParams.w = 4 := by rw [multiLeaf4JortsParams.public_eqs]
      have hEll : multiLeaf4JortsParams.ell1 = 128 := by rw [multiLeaf4JortsParams.public_eqs]
      have hTsw192 : multiLeaf4JortsParams.targetSum = 192 := by
        rw [PqHashParams.targetSum_eq, multiLeaf4JortsParams.public_eqs]; decide
      simp only [hSt, hNumL, ↓reduceIte]
      rw [signProductionHypertreeLayers_succ, signProductionHypertreeLayers_succ]
      simp only [hSt, decide_true, Bool.true_and, ↓reduceIte, hW4, hEll, hSubH, hTsw192,
        show 2 ^ 2 = 4 from rfl]
      have hDiv0 : UInt64.ofNat (q.epoch / 4) = 0 := by
        have hLt4 : q.epoch < 4 := by
          rename_i hNotOut
          rw [multiLeaf4JortsParams_productionWellFormed,
            PqHashParams.productionLeafIdxInRange_eq, multiLeaf4JortsParams.public_eqs] at hNotOut
          revert hNotOut; simp
        rw [Nat.div_eq_of_lt hLt4]; rfl
      rw [hDiv0]
      have hG1 : grindTswLeafCounterAux tswGuardSuite 4 128 192 zero32 sk.pkSeed pk.pkRoot
          ([0xE1, kpB, 3] ++ List.replicate 29 0x00) 0
          (UInt32.ofNat (q.epoch % 4)) 0 q.grindLimit = none :=
        grindTswLeaf_none_of_bad_hmsg _ _ _ _ _ _ (fun c => by
          rw [tswGuardSuite_thHashLeafMsg_e1]
          split
          · exact stepOneDomDigest_props.2.2.1
          · have hZ : thHashLeafMsg poly257MultiLeafSuite zero32 sk.pkSeed pk.pkRoot
                ([0xE1, kpB, 3] ++ List.replicate 29 0x00) 0
                (UInt32.ofNat (q.epoch % 4)) c = zero32 := by
              rw [poly257MultiLeaf_thHashLeafMsg_eq]
              split
              · rename_i _ _ _ hEq; injection hEq with hb _; exact absurd hb (by decide)
              · rfl
            rw [hZ]; exact zero32_tsw_false) _ _
      have hG2 : grindTswLeafCounterAux poly257MultiLeafSuite 4 128 192 zero32 sk.pkSeed pk.pkRoot
          (0xFF :: List.replicate 31 0x00) 0
          (UInt32.ofNat (q.epoch % 4)) 0 q.grindLimit = none :=
        grindTswLeaf_none_of_bad_hmsg _ _ _ _ _ _ (fun c => by
          have hZ : thHashLeafMsg poly257MultiLeafSuite zero32 sk.pkSeed pk.pkRoot
              (0xFF :: List.replicate 31 0x00) 0
              (UInt32.ofNat (q.epoch % 4)) c = zero32 := by
            rw [poly257MultiLeaf_thHashLeafMsg_eq]
            split
            · rename_i _ _ _ hEq; injection hEq with hb _; exact absurd hb (by decide)
            · rfl
          rw [hZ]; exact zero32_tsw_false) _ _
      rw [hG1, hG2]
    · rw [hPreEq, hPrfEq, signProductionHypertreeCore_def, signProductionHypertreeCore_def]
      have hNumL : multiLeaf4JortsParams.numLayers = 1 := by rw [multiLeaf4JortsParams.public_eqs]
      have hSubH : multiLeaf4JortsParams.subtreeHeight = 2 := by rw [multiLeaf4JortsParams.public_eqs]
      have hW4 : multiLeaf4JortsParams.w = 4 := by rw [multiLeaf4JortsParams.public_eqs]
      have hEll : multiLeaf4JortsParams.ell1 = 128 := by rw [multiLeaf4JortsParams.public_eqs]
      have hTsw192 : multiLeaf4JortsParams.targetSum = 192 := by
        rw [PqHashParams.targetSum_eq, multiLeaf4JortsParams.public_eqs]; decide
      simp only [hSt, hNumL, ↓reduceIte]
      rw [signProductionHypertreeLayers_succ, signProductionHypertreeLayers_succ]
      simp only [hSt, decide_true, Bool.true_and, ↓reduceIte, hW4, hEll, hSubH, hTsw192,
        show 2 ^ 2 = 4 from rfl]
      have hDiv0 : UInt64.ofNat (q.epoch / 4) = 0 := by
        have hLt4 : q.epoch < 4 := by
          rename_i hNotOut
          rw [multiLeaf4JortsParams_productionWellFormed,
            PqHashParams.productionLeafIdxInRange_eq, multiLeaf4JortsParams.public_eqs] at hNotOut
          revert hNotOut; simp
        rw [Nat.div_eq_of_lt hLt4]; rfl
      rw [hDiv0]
      have hGrindEq : ∀ c rem : Nat,
          grindTswLeafCounterAux tswGuardSuite 4 128 192
            (thPrfMsg poly257MultiLeafSuite sk.skPrf q.randomness
              (thPreHash poly257MultiLeafSuite sk.pkSeed pk.pkRoot q.message))
            sk.pkSeed pk.pkRoot
            (thPreHash poly257MultiLeafSuite sk.pkSeed pk.pkRoot q.message) 0
            (UInt32.ofNat (q.epoch % 4)) c rem =
          grindTswLeafCounterAux poly257MultiLeafSuite 4 128 192
            (thPrfMsg poly257MultiLeafSuite sk.skPrf q.randomness
              (thPreHash poly257MultiLeafSuite sk.pkSeed pk.pkRoot q.message))
            sk.pkSeed pk.pkRoot
            (thPreHash poly257MultiLeafSuite sk.pkSeed pk.pkRoot q.message) 0
            (UInt32.ofNat (q.epoch % 4)) c rem := by
        intro c rem
        induction rem generalizing c with
        | zero => rw [grindTswLeafCounterAux_zero, grindTswLeafCounterAux_zero]
        | succ rem' ih =>
          rw [grindTswLeafCounterAux_succ, grindTswLeafCounterAux_succ]
          have hHmsg : thHashLeafMsg tswGuardSuite
              (thPrfMsg poly257MultiLeafSuite sk.skPrf q.randomness
                (thPreHash poly257MultiLeafSuite sk.pkSeed pk.pkRoot q.message))
              sk.pkSeed pk.pkRoot
              (thPreHash poly257MultiLeafSuite sk.pkSeed pk.pkRoot q.message) 0
              (UInt32.ofNat (q.epoch % 4)) c =
            thHashLeafMsg poly257MultiLeafSuite
              (thPrfMsg poly257MultiLeafSuite sk.skPrf q.randomness
                (thPreHash poly257MultiLeafSuite sk.pkSeed pk.pkRoot q.message))
              sk.pkSeed pk.pkRoot
              (thPreHash poly257MultiLeafSuite sk.pkSeed pk.pkRoot q.message) 0
              (UInt32.ofNat (q.epoch % 4)) c := by
            rw [tswGuardSuite_thHashLeafMsg_eq]
            cases hMu : thPreHash poly257MultiLeafSuite sk.pkSeed pk.pkRoot q.message with
            | nil => rfl
            | cons b0 tail =>
              by_cases hb0 : b0 = 0xE1
              · subst hb0; exact absurd hMu (hMuNotE1 tail)
              · simp [hb0]
          rw [hHmsg, ih (c + 1)]
      rw [hGrindEq]
      cases grindTswLeafCounterAux poly257MultiLeafSuite 4 128 192
          (thPrfMsg poly257MultiLeafSuite sk.skPrf q.randomness
            (thPreHash poly257MultiLeafSuite sk.pkSeed pk.pkRoot q.message))
          sk.pkSeed pk.pkRoot
          (thPreHash poly257MultiLeafSuite sk.pkSeed pk.pkRoot q.message) 0
          (UInt32.ofNat (q.epoch % 4)) 0 q.grindLimit with
      | none => rfl
      | some triple =>
        rcases triple with ⟨ctr, digits, _⟩
        dsimp only
        rw [signProductionHypertreeLayers_zero, signProductionHypertreeLayers_zero]
        dsimp only
        have hChEq : ((List.range 128).map fun r =>
            wotsChainSteps tswGuardSuite sk.pkSeed 0 0 (q.epoch % 4) r 0 (digits.getD r 0)
              (wotsSecretBase tswGuardSuite sk 0 0 (q.epoch % 4) r)) =
          ((List.range 128).map fun r =>
            wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 (q.epoch % 4) r 0 (digits.getD r 0)
              (wotsSecretBase poly257MultiLeafSuite sk 0 0 (q.epoch % 4) r)) := by
          apply List.map_congr_left; intro r _
          rw [sameTreeRoles_wotsSecretBase hRoles, sameTreeRoles_wotsChainSteps hRoles]
        have hApEq := sameTreeRoles_buildMerkleAuthPathKp hRoles sk.pkSeed 0 0 .tree 0 _ _
          (sameTreeRoles_computeWotsPk hRoles multiLeaf4JortsParams sk 0 0) 2 0 0 (q.epoch % 4)
        rw [show UInt32.ofNat 0 = (0 : UInt32) from rfl] at *
        rw [hChEq, hApEq, tswGuardSuite_verify_eq]

def evalHashLocallyTree {α : Type} (rawHash : List UInt8 → List UInt8) :
    ProdAdaptiveTree α → ProdAdaptiveTree α
  | .pure ret => .pure ret
  | .hashQuery x next => evalHashLocallyTree rawHash (next (rawHash x))
  | .signQuery q next => .signQuery q (fun resp => evalHashLocallyTree rawHash (next resp))

theorem evalHashLocallyTree_bounded {α : Type} (rawHash : List UInt8 → List UInt8) :
    ∀ {qH qS : Nat} (prog : ProdAdaptiveTree α),
      ProdDualBounded qH qS prog → ProdDualBounded 0 qS (evalHashLocallyTree rawHash prog)
  | _, _, .pure _, _ => trivial
  | 0, _, .hashQuery _ _, h => False.elim h
  | _ + 1, _, .hashQuery x next, h => evalHashLocallyTree_bounded rawHash (next (rawHash x)) (h _)
  | _, 0, .signQuery _ _, h => False.elim h
  | _, _ + 1, .signQuery _ next, h =>
    fun resp => evalHashLocallyTree_bounded rawHash (next resp) (h resp)

theorem evalLatched_evalHashLocallyTree {α : Type}
    (raw₁ raw₂ : List UInt8 → List UInt8)
    (sign₁ sign₂ : ProdSigningQuery → Option PqHashSig)
    (hSign : ∀ q, sign₁ q = sign₂ q) :
    ∀ (prog : ProdAdaptiveTree α) (lo : Nat),
      evalLatchedAdaptiveTree true raw₁ sign₁ prog lo =
        evalLatchedAdaptiveTree true raw₂ sign₂ (evalHashLocallyTree raw₁ prog) lo
  | .pure _, _ => by simp only [evalHashLocallyTree, evalLatchedAdaptiveTree.public_eqs]
  | .hashQuery x next, lo => by
    unfold evalHashLocallyTree
    rw [evalLatchedAdaptiveTree.public_eq_2]
    exact evalLatched_evalHashLocallyTree raw₁ raw₂ sign₁ sign₂ hSign (next (raw₁ x)) lo
  | .signQuery q next, lo => by
    unfold evalHashLocallyTree
    rw [evalLatchedAdaptiveTree_sign, evalLatchedAdaptiveTree_sign, hSign q]
    by_cases hLo : lo ≤ q.epoch
    · rw [ite_eq_left (Or.inr hLo), ite_eq_left (Or.inr hLo),
        evalLatched_evalHashLocallyTree raw₁ raw₂ sign₁ sign₂ hSign (next (sign₂ q)) (q.epoch + 1)]
    · have hNot : ¬ ((true = false) ∨ lo ≤ q.epoch) := fun hOr =>
        hOr.elim (fun hb => Bool.noConfusion hb) hLo
      rw [ite_eq_right hNot, ite_eq_right hNot]
      exact evalLatched_evalHashLocallyTree raw₁ raw₂ sign₁ sign₂ hSign (next none) lo

def liftTswGuardAdv {qHash qSign : Nat} (adv : SeedWithheldEufCmaAdv qHash qSign) :
    SeedWithheldEufCmaAdv 0 qSign where
  run pk := evalHashLocallyTree tswGuardSuite.rawHash (adv.run pk)
  bounded pk := evalHashLocallyTree_bounded tswGuardSuite.rawHash (adv.run pk) (adv.bounded pk)

theorem tswGuardSuite_full_adaptive_forger_bound {nA qHash qSign : Nat}
    (hPos : 0 < (256 * pow256 24) * nA)
    (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    {𝒜 : Spec.Code Spec.targetIface Spec.TargetBreak → Prop}
    (hClass : ∀ (s : Fin 12) (c : Fin (pow256 23 * nA)),
      𝒜 (multiLeafInteractivePreAdv (fun a => liftTswGuardAdv (adv a)) s c))
    {εPre : Spec.RatBound}
    (hPre : Spec.SmDtPreHard 𝒜 multiLeafStep0Th 1 1 1 εPre) :
    Spec.GameBound
      (execEufCmaGameWithTsw true hPos tswGuardSuite multiLeaf4JortsParams
        (fun z => multiLeaf24Keygen ((Spec.CoinSplit.prod (256 * pow256 24) nA).chal z))
        (fun z => adv ((Spec.CoinSplit.prod (256 * pow256 24) nA).advc z))).winProb
      (Spec.RatBound.scale 12 εPre) := by
  have hBase := poly257MultiLeaf_full_adaptive_forger_bound hPos
    (fun a => liftTswGuardAdv (adv a)) hClass hPre
  refine Spec.GameBound.trans (Spec.event_le_reduction_win _ _ (fun ω hW => ?_)) hBase
  rw [execEufCmaGameWithTsw_true_win_eq, ExecEufCmaGame, execEufCmaGameWith_win] at hW
  rw [ExecEufCmaGame, execEufCmaGameWith_win]
  let π₀ := Spec.CoinSplit.prod (256 * pow256 24) nA
  let sk := multiLeaf24Keygen (π₀.chal ω)
  have hPk := sameTreeRoles_derivePublicKey tswGuardSuite_sameTreeRoles multiLeaf4JortsParams sk
  have hTree := evalLatched_evalHashLocallyTree tswGuardSuite.rawHash poly257MultiLeafSuite.rawHash
    (prodSignQuery tswGuardSuite multiLeaf4JortsParams sk)
    (prodSignQuery poly257MultiLeafSuite multiLeaf4JortsParams sk)
    (tswGuardSuite_prodSignQuery_eq sk)
    ((adv (π₀.advc ω)).run (derivePublicKey tswGuardSuite multiLeaf4JortsParams sk)) 0
  have hLogEq : ∀ qs, productionSigningLog tswGuardSuite multiLeaf4JortsParams sk qs =
      productionSigningLog poly257MultiLeafSuite multiLeaf4JortsParams sk qs := by
    intro qs; induction qs with
    | nil => rw [productionSigningLog_nil, productionSigningLog_nil]
    | cons q rest ih =>
      rw [productionSigningLog_cons, productionSigningLog_cons, tswGuardSuite_prodSignQuery_eq, ih]
  unfold execEufCmaOutcome at hW ⊢
  unfold liftTswGuardAdv
  dsimp only at hW ⊢
  rw [hPk] at hTree hW
  rw [hTree] at hW
  rw [prodEufCmaWin_eq, hPk, tswGuardSuite_verify_eq, hLogEq] at hW
  rw [prodEufCmaWin_eq]
  exact hW

def oneQueryOneStepNoTswForger : SeedWithheldEufCmaAdv 1 1 where
  run pk :=
    .signQuery ⟨[0, 0], [], 0, 1⟩ (fun sig0Opt =>
      let lsig0 := match sig0Opt with
        | some s => s.layerSigs.headD ⟨0, [], []⟩
        | none => ⟨0, [], []⟩
      let c0 := lsig0.wotsChains.getD 0 zero32
      .hashQuery
        (thPreimage tagThF pk.pkSeed ⟨0, 0, .wotsHash, 0, 0, 0⟩ [c0])
        (fun c0Step1 =>
          .pure ([0, 3],
            { rRand := zero32
              msgTswCtr := 0
              leafGlobalIdx := 0
              forsOpenings := []
              layerSigs := [⟨0, c0Step1 :: lsig0.wotsChains.drop 1, lsig0.authPath⟩] })))
  bounded _ := fun _ _ => trivial

theorem tooth_disabled_checkTargetSum_one_query_forges_prob_one :
    let hPos : 0 < (256 * pow256 24) * 1 :=
      Nat.mul_pos (Nat.mul_pos (by decide) (pow256_pos 24)) Nat.one_pos
    let keygen := fun z : Fin ((256 * pow256 24) * 1) =>
      multiLeaf24Keygen ((Spec.CoinSplit.prod (256 * pow256 24) 1).chal z)
    let adv := fun _ : Fin ((256 * pow256 24) * 1) => oneQueryOneStepNoTswForger
    (∀ ω : Fin ((256 * pow256 24) * 1),
      (execEufCmaGameWithTsw false hPos tswGuardSuite multiLeaf4JortsParams keygen adv).win ω =
        true) ∧
    (∀ ω : Fin ((256 * pow256 24) * 1),
      (execEufCmaGameWithTsw true hPos tswGuardSuite multiLeaf4JortsParams keygen adv).win ω =
        false) ∧
    ¬ Spec.GameBound
        (execEufCmaGameWithTsw false hPos tswGuardSuite multiLeaf4JortsParams keygen adv).winProb
        (Spec.RatBound.scale 12 ⟨2, 256, by decide⟩) := by
  intro hPos keygen adv
  have hWinFalse : ∀ ω : Fin ((256 * pow256 24) * 1),
      (execEufCmaGameWithTsw false hPos tswGuardSuite multiLeaf4JortsParams keygen adv).win ω =
        true := by
    intro ω
    have hRoles := tswGuardSuite_sameTreeRoles
    have hS0 : prodSignQuery tswGuardSuite multiLeaf4JortsParams (keygen ω) ⟨[0, 0], [], 0, 1⟩ =
        some (honestMultiLeafSig (keygen ω) 0 0) := by
      rw [tswGuardSuite_prodSignQuery_eq]
      exact prodSignQuery_poly257MultiLeaf_valid (keygen ω) (by decide : 0 < 4)
        (by decide : 0 < 3) Nat.one_pos []
    have hStep0 : ∀ x, tswGuardSuite.rawHash
        (thPreimage tagThF (keygen ω).pkSeed ⟨0, 0, .wotsHash, 0, 0, 0⟩ [x]) =
        thChainF poly257MultiLeafSuite (keygen ω).pkSeed ⟨0, 0, .wotsHash, 0, 0, 0⟩ x := by
      intro x
      rw [← thCall_eq, hRoles _ _ _ _ (.inr (.inr (.inl rfl))), thChainF_eq]
    have hPkEq := sameTreeRoles_derivePublicKey hRoles multiLeaf4JortsParams (keygen ω)
    have hPkSeed : (derivePublicKey tswGuardSuite multiLeaf4JortsParams (keygen ω)).pkSeed =
        (keygen ω).pkSeed := by
      rw [hPkEq, derivePublicKey_poly257MultiLeaf, pkFromTbl.public_eqs]
    have hOut : execEufCmaOutcome true tswGuardSuite multiLeaf4JortsParams keygen adv ω =
        let lsig0 := (honestMultiLeafSig (keygen ω) 0 0).layerSigs.headD ⟨0, [], []⟩
        let c0 := lsig0.wotsChains.getD 0 zero32
        let c0Step1 := thChainF poly257MultiLeafSuite (keygen ω).pkSeed ⟨0, 0, .wotsHash, 0, 0, 0⟩ c0
        ⟨keygen ω, [⟨[0, 0], [], 0, 1⟩], [0, 3],
         { rRand := zero32
           msgTswCtr := 0
           leafGlobalIdx := 0
           forsOpenings := []
           layerSigs := [⟨0, c0Step1 :: lsig0.wotsChains.drop 1, lsig0.authPath⟩] }⟩ := by
      unfold execEufCmaOutcome
      dsimp only [adv, oneQueryOneStepNoTswForger]
      rw [evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inr (Nat.zero_le 0)), hS0]
      simp only [evalLatchedAdaptiveTree.public_eqs, hPkSeed, hStep0]
    dsimp only [execEufCmaGameWithTsw]
    rw [hOut]
    dsimp only
    rw [productionSigningLog_cons, hS0, productionSigningLog_nil]
    dsimp only [List.append, List.map]
    refine Bool.and_eq_true_iff.mpr ⟨?_, decide_eq_true (by decide : ([0, 3] : List UInt8) ∉ [[0, 0]])⟩
    unfold verifyProductionPqHashSigWithTsw
    have hWf := multiLeaf4JortsParams_productionWellFormed
    have hInRange : multiLeaf4JortsParams.productionLeafIdxInRange 0 = true := by
      rw [PqHashParams.productionLeafIdxInRange_eq, multiLeaf4JortsParams.public_eqs]; decide
    have hPkSeedPoly : (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams
        (keygen ω)).pkSeed = (keygen ω).pkSeed := by
      rw [derivePublicKey_poly257MultiLeaf, pkFromTbl.public_eqs]
    rw [hPkEq, hPkSeedPoly]
    have hShapeFalse : (decide ((1 : Nat) ≠ multiLeaf4JortsParams.numLayers) ||
        decide ((0 : Nat) ≠ 0)) = false := by
      rw [multiLeaf4JortsParams.public_eqs]; rfl
    have hStT : multiLeaf4JortsParams.statefulJorts = true := by rw [multiLeaf4JortsParams.public_eqs]
    simp only [hWf, hInRange, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
      List.length_cons, List.length_nil, hShapeFalse, hStT, List.isEmpty_nil]
    unfold verifyProductionHypertreeLayersWithTsw
    simp only [(by decide : 0 < 2 ^ 32), decide_true, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, Bool.false_and]
    have hSubH : multiLeaf4JortsParams.subtreeHeight = 2 := by rw [multiLeaf4JortsParams.public_eqs]
    have hEll : multiLeaf4JortsParams.ell1 = 128 := by rw [multiLeaf4JortsParams.public_eqs]
    have hW4 : multiLeaf4JortsParams.w = 4 := by rw [multiLeaf4JortsParams.public_eqs]
    simp only [hSubH, hEll, hW4]
    have hLayerDig : productionLayerDigest tswGuardSuite multiLeaf4JortsParams zero32
        (keygen ω).pkSeed
        (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams (keygen ω)).pkRoot
        (thPreHash tswGuardSuite (keygen ω).pkSeed
          (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams (keygen ω)).pkRoot [0, 3])
        0 (UInt64.ofNat (0 / 2 ^ 2)) (UInt32.ofNat (0 % 2 ^ 2)) 0 = stepOneDomDigest := by
      rw [productionLayerDigest_eq]
      simp only [hStT, decide_true, Bool.true_and, ↓reduceIte]
      rw [tswGuardSuite_thPreHash_eq]
      simp only [(by decide : (0 : UInt8).toNat < 4), ↓reduceIte]
      rw [tswGuardSuite_thHashLeafMsg_eq]
      simp
    rw [hLayerDig, stepOneDomDigest_props.2.1]
    dsimp only
    rw [honestMultiLeafSig.public_eqs]
    dsimp only [List.headD]
    have hLen128 : (thChainF poly257MultiLeafSuite (keygen ω).pkSeed ⟨0, 0, .wotsHash, 0, 0, 0⟩
        (((List.range 128).map (fun r =>
          wotsChainSteps poly257MultiLeafSuite (keygen ω).pkSeed 0 0 0 r 0
            ((extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD r 0)
            (wotsSecretBase poly257MultiLeafSuite (keygen ω) 0 0 0 r))).getD 0 zero32) ::
        ((List.range 128).map (fun r =>
          wotsChainSteps poly257MultiLeafSuite (keygen ω).pkSeed 0 0 0 r 0
            ((extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD r 0)
            (wotsSecretBase poly257MultiLeafSuite (keygen ω) 0 0 0 r))).drop 1).length = 128 := by
      rw [List.length_cons, List.length_drop, List.length_map, List.length_range]
    simp only [hLen128, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [sameTreeRoles_recoverWotsPk hRoles, sameTreeRoles_walkMerkleAuthPathKp hRoles]
    have hRecPk : recoverWotsPkFromSig poly257MultiLeafSuite multiLeaf4JortsParams
        (keygen ω).pkSeed 0 0 0 (extractBaseWDigits 4 128 stepOneDomDigest)
        (thChainF poly257MultiLeafSuite (keygen ω).pkSeed ⟨0, 0, .wotsHash, 0, 0, 0⟩
          (((List.range 128).map (fun r =>
            wotsChainSteps poly257MultiLeafSuite (keygen ω).pkSeed 0 0 0 r 0
              ((extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD r 0)
              (wotsSecretBase poly257MultiLeafSuite (keygen ω) 0 0 0 r))).getD 0 zero32) ::
          ((List.range 128).map (fun r =>
            wotsChainSteps poly257MultiLeafSuite (keygen ω).pkSeed 0 0 0 r 0
              ((extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD r 0)
              (wotsSecretBase poly257MultiLeafSuite (keygen ω) 0 0 0 r))).drop 1) =
        leafFromTbl (honestSlotHiLo (keygen ω)) 0 := by
      rw [← poly257MultiLeaf_computeWotsPk_eq (keygen ω) (by decide : 0 < 4),
        recoverWotsPkFromSig_eq, computeWotsPk_eq, recoverWotsEndpoints_eq, hW4, hEll]
      congr 1
      apply List.map_congr_left
      intro r hrMem
      have hr128 : r < 128 := List.mem_range.mp hrMem
      cases r with
      | zero =>
        rw [List.getD_cons_zero,
          list_getD_map_range 128 _ zero32 (by decide : 0 < 128),
          encodeSubMsg3Hmsg_explicit_digits.1, wotsChainSteps_zero,
          stepOneDomDigest_props.2.2.2.1]
        simp [wotsChainSteps_succ, wotsChainSteps_zero]
      | succ r' =>
        have hDropGet : ∀ (l : List (List UInt8)) (k : Nat),
            (l.drop 1).getD k [] = l.getD (k + 1) [] := by
          intro l k; cases l <;> rfl
        rw [List.getD_cons_succ, hDropGet,
          list_getD_map_range 128 _ [] hr128,
          stepOneDomDigest_props.2.2.2.2 (r' + 1) (Nat.succ_pos r') hr128]
        have hdLt : (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD (r' + 1) 0 < 4 := by
          have hAll : ∀ k ∈ List.range 128,
              (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD k 0 < 4 := by
            rw [encodeSubMsg3Hmsg.public_eqs]; simp only [extractBaseWDigits_eq]; decide +kernel
          exact hAll (r' + 1) (List.mem_range.mpr hr128)
        have hAdd := wotsChainSteps_add poly257MultiLeafSuite (keygen ω).pkSeed 0 0 0 (r' + 1)
          ((extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD (r' + 1) 0)
          (4 - 1 - (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD (r' + 1) 0) 0
          (wotsSecretBase poly257MultiLeafSuite (keygen ω) 0 0 0 (r' + 1))
        rw [Nat.zero_add,
          show (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD (r' + 1) 0 +
            (4 - 1 - (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD (r' + 1) 0) = 4 - 1
            by omega] at hAdd
        exact hAdd
    rw [show UInt32.ofNat 0 = (0 : UInt32) from rfl,
        show UInt64.ofNat (0 / 2 ^ 2) = (0 : UInt64) from rfl,
        show 0 % 2 ^ 2 = 0 from rfl]
    rw [hRecPk]
    have hWalk := poly257MultiLeaf_walkAuthPath_honest (keygen ω) (by decide : 0 < 4)
    rw [hWalk]
    unfold verifyProductionHypertreeLayersWithTsw
    exact decide_eq_true rfl
  have hWinTrue : ∀ ω : Fin ((256 * pow256 24) * 1),
      (execEufCmaGameWithTsw true hPos tswGuardSuite multiLeaf4JortsParams keygen adv).win ω =
        false := by
    intro ω
    rw [execEufCmaGameWithTsw_true_win_eq, ExecEufCmaGame, execEufCmaGameWith_win, prodEufCmaWin_eq]
    have hMsgStar : (execEufCmaOutcome true tswGuardSuite multiLeaf4JortsParams keygen adv ω).msgStar =
        [0, 3] := by
      unfold execEufCmaOutcome
      dsimp only [adv, oneQueryOneStepNoTswForger]
      rw [evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inr (Nat.zero_le 0))]
      simp only [evalLatchedAdaptiveTree.public_eqs]
    rw [hMsgStar, tswGuardSuite_verify_eq]
    have hVerFalse : ∀ pk sig,
        verifyProductionPqHashSig poly257MultiLeafSuite multiLeaf4JortsParams pk [0, 3] sig =
          false := by
      intro pk sig
      rw [verifyProductionPqHashSig_eq]
      split
      · rfl
      · rename_i hRangeOk
        have hTree0 : UInt64.ofNat (sig.leafGlobalIdx / 2 ^ 2) = 0 := by
          have hLt4 : sig.leafGlobalIdx < 4 := by
            rw [multiLeaf4JortsParams_productionWellFormed,
              PqHashParams.productionLeafIdxInRange_eq, multiLeaf4JortsParams.public_eqs] at hRangeOk
            revert hRangeOk; simp
          rw [show 2 ^ 2 = 4 from rfl, Nat.div_eq_of_lt hLt4]; rfl
        split
        · rfl
        · rename_i hShapeOk
          simp only [multiLeaf4JortsParams.public_eqs, ↓reduceIte]
          split
          · rfl
          · cases hLs : sig.layerSigs with
            | nil =>
              rw [hLs, multiLeaf4JortsParams.public_eqs] at hShapeOk
              exact absurd rfl hShapeOk
            | cons lsig _ =>
              rw [verifyProductionHypertreeLayers_cons]
              dsimp only
              cases (!decide (lsig.tswCtr < 2 ^ 32))
              · simp only [Bool.false_eq_true, ↓reduceIte]
                rw [productionLayerDigest_eq, PqHashParams.targetSum_eq]
                simp only [Bool.true_and, decide_true, ↓reduceIte, hTree0,
                  show (128 * (4 - 1)) / 2 = 192 from rfl]
                have hNot03 : ¬ ((0 : UInt8).toNat < 4 ∧ (3 : UInt8).toNat < 3) :=
                  fun h => absurd h.2 (by decide)
                rw [poly257MultiLeaf_thPreHash_eq]
                dsimp only
                rw [ite_eq_right hNot03]
                have hHmsgZ : thHashLeafMsg poly257MultiLeafSuite sig.rRand pk.pkSeed pk.pkRoot
                    (0xFF :: List.replicate 31 0x00) 0
                    (UInt32.ofNat (sig.leafGlobalIdx % 2 ^ 2)) lsig.tswCtr = zero32 := by
                  rw [poly257MultiLeaf_thHashLeafMsg_eq]
                  split
                  · rename_i _ _ _ hEq; injection hEq with hb _; exact absurd hb (by decide)
                  · rfl
                have hZExt : extractBaseWDigitsChecked 4 128 zero32 =
                    some (extractBaseWDigits 4 128 zero32) := by
                  simp only [zero32.public_eqs, extractBaseWDigitsChecked_eq, extractBaseWDigits_eq]
                  decide +kernel
                rw [hHmsgZ, hZExt]
                dsimp only
                rw [zero32_tsw_false]
                rfl
              · simp only [↓reduceIte]
    rw [hVerFalse]
    rfl
  exact ⟨hWinFalse, hWinTrue,
    Spec.FinGame.not_bound_of_forall_win _ hWinFalse (by decide)⟩

theorem tooth_disabled_checkTargetSum_refutes_bound :
    ¬ Spec.GameBound
        (execEufCmaGameWithTsw false
          (Nat.mul_pos (Nat.mul_pos (by decide) (pow256_pos 24)) Nat.one_pos)
          tswGuardSuite multiLeaf4JortsParams
          (fun z => multiLeaf24Keygen ((Spec.CoinSplit.prod (256 * pow256 24) 1).chal z))
          (fun _ => oneQueryOneStepNoTswForger)).winProb
        (Spec.RatBound.scale 12 ⟨2, 256, by decide⟩) :=
  tooth_disabled_checkTargetSum_one_query_forges_prob_one.2.2

#verify_constructive
  Qsag.verifyProductionHypertreeLayersWithTsw_true
  Qsag.verifyProductionPqHashSigWithTsw_true_eq
  Qsag.execEufCmaGameWithTsw_true_win_eq
  Qsag.tswGuardSuite_full_adaptive_forger_bound
  Qsag.tooth_disabled_checkTargetSum_one_query_forges_prob_one
  Qsag.tooth_disabled_checkTargetSum_refutes_bound

#tooth_pair Qsag.tswGuardSuite_full_adaptive_forger_bound vs
  Qsag.tooth_disabled_checkTargetSum_refutes_bound

end Qsag
end

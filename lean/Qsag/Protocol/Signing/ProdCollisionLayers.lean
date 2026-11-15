module
public import Qsag.Protocol.Signing.ProdCollisionWitness
import all Qsag.Protocol.Signing.ProdCollisionWitness
import all Qsag.Protocol.Signing.HypertreeEufCma
import all Qsag.Protocol.Signing.HashSigs
import Qsag.Tactic.AssuranceKit

/-!
# Qsag.Protocol.Signing.ProdCollisionLayers — hypertree part of the production extractor

`prodLayerExtract` and `prodHypertreeWalkExtract` are `prod_layer_divergence_break` and
`prod_hypertree_walk_break` as functions. Every case split is on decidable data (log search,
codeword equality, preimage equality), so the returned `ProdTcrWitness` is the collision the
verifier walk meets. The preimage event stays a proposition; its two cases are
`prod_layer_preimage_logged` and `prod_layer_preimage_unused`.

Scope. Deterministic extraction only; see `ProdCollisionWitness`.
-/

public section
namespace Qsag

set_option autoImplicit false

/-! Local abbreviations for positions on the verification path of `sigStar`. They are unhygienic
notations: each expands in place to the term on its right, over the `suite`, `params`, `sk`,
`msgStar`, `sigStar` (and, for `digs⟪i⟫`, `cur`) in scope. -/

-- Hypertree position of the path at layer `i`.
set_option hygiene false in
local notation:max "pos⟪" i "⟫" => sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)
-- Tree address of the path at layer `i`.
set_option hygiene false in
local notation:max "tree⟪" i "⟫" =>
  UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight)
-- Key-pair (leaf) index of the path at layer `i`.
set_option hygiene false in
local notation:max "kp⟪" i "⟫" =>
  (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight)
-- Layer-`i` XMSS signature of the forgery.
set_option hygiene false in
local notation:max "lsig⟪" i "⟫" => (sigStar.layerSigs.getD i ⟨0, [], []⟩)
-- Honest public root.
set_option hygiene false in
local notation:max "PK_ROOT" => (derivePublicKey suite params sk).pkRoot
-- Codeword digits the verifier derives for layer message `cur` at layer `i`.
set_option hygiene false in
local notation:max "digs⟪" i "⟫" =>
  (extractBaseWDigits params.w params.ell1
    (productionLayerDigest suite params sigStar.rRand sk.pkSeed
      (derivePublicKey suite params sk).pkRoot cur i
      (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
        2 ^ params.subtreeHeight))
      (UInt32.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) %
        2 ^ params.subtreeHeight))
      (sigStar.layerSigs.getD i ⟨0, [], []⟩).tswCtr))
-- Root of the top subtree, as the verifier walk reaches it.
set_option hygiene false in
local notation:max "TOP_ROOT" =>
  (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1))
    (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (params.numLayers * params.subtreeHeight))))
-- FORS tree address, key pair and leaf indices of the forgery.
set_option hygiene false in
local notation:max "FORS_TREE" => (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight))
set_option hygiene false in
local notation:max "FORS_KP" => (sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight)
set_option hygiene false in
local notation:max "FORS_IDXS" =>
  (prodSigForsIdxs suite params (derivePublicKey suite params sk) msgStar sigStar)

/-! ### Propositional parts of the traversal -/

theorem prod_list_range_succ_shift {α : Type} (rem : Nat) (f : Nat → α) :
    (List.range (rem + 1)).map f = f 0 :: (List.range rem).map (fun k => f (k + 1)) := by
  induction rem generalizing f with
  | zero => simp
  | succ r ih => rw [List.range_succ, List.map_append, ih f, List.range_succ, List.map_append]; simp

theorem prod_sumDigits_ge_mul (bound : Nat) :
    ∀ (ds : List Nat), (∀ d ∈ ds, bound ≤ d) → bound * ds.length ≤ sumDigits ds
  | [], _ => by simp [sumDigits_nil]
  | d :: ds, hAll => by
    rw [sumDigits_cons, List.length_cons, Nat.mul_succ]
    have hd : bound ≤ d := hAll d (.head ds)
    have hRest := prod_sumDigits_ge_mul bound ds (fun x hx => hAll x (.tail d hx))
    omega

theorem prod_findDigitLt_none (maxVal : Nat) :
    ∀ (ds : List Nat), findDigitLt maxVal ds = none → ∀ d ∈ ds, maxVal ≤ d
  | [], _, _, hMem => by cases hMem
  | d :: ds, hNone, x, hMem => by
    simp only [findDigitLt] at hNone
    by_cases hlt : d < maxVal
    · simp [hlt] at hNone
    · simp only [hlt, ↓reduceIte, Option.map_eq_none_iff] at hNone
      rcases List.mem_cons.mp hMem with rfl | hTail
      · omega
      · exact prod_findDigitLt_none maxVal ds hNone x hTail

/-- Honest chain values under a codeword different from the logged one at the same position
    contain a preimage below the logged digit. -/
theorem prod_layer_preimage_logged (suite : TweakableHashSuite) (params : PqHashParams) (sk :
    PqSecretKey)
    (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hCons : ProdLogConsistent suite params sk log)
    (i : Nat) (hi : i < params.numLayers) (digF : List Nat)
    (hTsw : checkTargetSum params.w params.ell1 params.targetSum digF = true)
    (hChains : ∀ r, r < params.ell1 →
      lsig⟪i⟫.wotsChains.getD r [] =
        honestChainNode suite sk (UInt32.ofNat i) tree⟪i⟫ kp⟪i⟫ r (digF.getD r 0))
    (e : List UInt8 × PqHashSig) (he : e ∈ log) (hOk : ProdLogEntryOk suite params sk e)
    (hPos : e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) = pos⟪i⟫)
    (hDigNe : digF ≠ prodLogLayerDigits suite params sk e i) :
    ProdPreimageBreak suite params sk log msgStar sigStar := by
  have hValidH := prodLogLayerDigits_valid hOk i hi
  obtain ⟨hLenF, _, _⟩ := (checkTargetSum_iff _ _ _ _).mp hTsw
  obtain ⟨r, hr2, hr1, hlt, hbw⟩ :=
    (tsw_incomparable_no_chain_forgery hValidH hTsw (fun hEq => hDigNe hEq.symm)).2
  have hr : r < params.ell1 := by rw [← hLenF]; exact hr2
  have hF : digF.getD r 0 = digF[r] := list_getD_eq_getElem digF 0 hr2
  have hH : (prodLogLayerDigits suite params sk e i).getD r 0 =
      (prodLogLayerDigits suite params sk e i)[r] := list_getD_eq_getElem _ 0 hr1
  refine ProdPreimageBreak.wots i hi r hr (digF.getD r 0) (by omega) ?_ ?_
  · rw [hChains r hr]
    exact honestChainNode_succ suite sk (UInt32.ofNat i) _ _ r (digF.getD r 0)
  · intro e' he' hPos'
    rw [hCons e' he' e he i hi (hPos'.trans hPos.symm)]
    omega

/-- Honest chain values at a position no logged signature used contain a preimage. -/
theorem prod_layer_preimage_unused (suite : TweakableHashSuite) (params : PqHashParams) (sk :
    PqSecretKey)
    (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hw : params.w = 4 ∨ params.w = 16) (hPwf : params.productionWellFormed = true)
    (i : Nat) (hi : i < params.numLayers) (digF : List Nat)
    (hTsw : checkTargetSum params.w params.ell1 params.targetSum digF = true)
    (hChains : ∀ r, r < params.ell1 →
      lsig⟪i⟫.wotsChains.getD r [] =
        honestChainNode suite sk (UInt32.ofNat i) tree⟪i⟫ kp⟪i⟫ r (digF.getD r 0))
    (hNoUse : ∀ e, e ∈ log → ¬ e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) = pos⟪i⟫) :
    ProdPreimageBreak suite params sk log msgStar sigStar := by
  have hGeom := params.productionWellFormed_geom hPwf hw
  have hStrict : params.targetSum < (params.w - 1) * params.ell1 := by
    rw [PqHashParams.targetSum_eq]
    rcases hGeom with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> decide
  obtain ⟨hLenF, hBoundF, hSumF⟩ := (checkTargetSum_iff _ _ _ _).mp hTsw
  cases hFind : findDigitLt (params.w - 1) digF with
  | none =>
    exfalso
    have hAllGe := prod_findDigitLt_none (params.w - 1) digF hFind
    have hGe := prod_sumDigits_ge_mul (params.w - 1) digF hAllGe
    rw [hLenF, hSumF] at hGe
    omega
  | some r =>
    obtain ⟨hrLen, hrVal⟩ := findDigitLt_sound (params.w - 1) hFind
    have hr : r < params.ell1 := by rw [← hLenF]; exact hrLen
    have hF : digF.getD r 0 = digF[r] := list_getD_eq_getElem digF 0 hrLen
    refine ProdPreimageBreak.wots i hi r hr (digF.getD r 0) (by omega) ?_ ?_
    · rw [hChains r hr]
      exact honestChainNode_succ suite sk (UInt32.ofNat i) _ _ r (digF.getD r 0)
    · intro e' he' hPos'
      exact absurd hPos' (hNoUse e' he')

theorem prod_recoverForsTreeRoots_succ_inv (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (treeIdx : UInt64) (kpIdx : Nat)
    (idxs : List Nat) (openings : List ForsTreeOpening) (j rem : Nat) (roots : List (List UInt8))
    (h : recoverProductionForsTreeRoots suite params pkSeed treeIdx kpIdx idxs openings j (rem + 1)
        =
      some roots) :
    ∃ rJ rs,
      walkMerkleAuthPathKp suite pkSeed 0 treeIdx .forsTree (UInt32.ofNat kpIdx)
        params.forsHeight j (idxs.getD j 0)
        (forsIndexedLeafHash suite pkSeed treeIdx kpIdx j (idxs.getD j 0)
          (openings.getD j ⟨[], []⟩).secretVal)
        (openings.getD j ⟨[], []⟩).authPath = some rJ ∧
      recoverProductionForsTreeRoots suite params pkSeed treeIdx kpIdx idxs openings (j + 1) rem =
        some rs ∧
      roots = rJ :: rs := by
  rw [recoverProductionForsTreeRoots_succ] at h
  dsimp only at h
  split at h
  · cases h
  · rename_i rJ hWalk
    split at h
    · cases h
    · rename_i rs hRest
      simp only [Option.some.injEq] at h
      exact ⟨rJ, rs, hWalk, hRest, h.symm⟩

theorem prod_recoverForsPk_some_inv (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (treeIdx : UInt64) (kpIdx : Nat)
    (idxs : List Nat) (openings : List ForsTreeOpening) (pk : List UInt8)
    (h : recoverProductionForsPk suite params pkSeed treeIdx kpIdx idxs openings = some pk) :
    ∃ roots,
      recoverProductionForsTreeRoots suite params pkSeed treeIdx kpIdx idxs openings 0
        params.forsTrees = some roots ∧
      pk = thTweakTl suite pkSeed ⟨0, treeIdx, .forsRoots, UInt32.ofNat kpIdx, 0, 0⟩ roots := by
  rw [recoverProductionForsPk_eq] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i roots hRoots
      simp only [Option.some.injEq] at h
      exact ⟨roots, hRoots, h.symm⟩

/-- What acceptance of a stateless production signature fixes, with the FORS indices named by
    `prodSigForsIdxs` instead of an existential. -/
theorem prod_stateless_accept_facts (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hStateless : params.statefulJorts = false)
    (hAccept : verifyProductionPqHashSig suite params (derivePublicKey suite params sk) msgStar
      sigStar = true) :
    params.productionWellFormed = true ∧ sigStar.layerSigs.length = params.numLayers ∧
    sigStar.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight) ∧
    (FORS_IDXS).length = params.forsTrees ∧
    (∀ idx ∈ (FORS_IDXS), idx < 2 ^ params.forsHeight) ∧
    ∃ forsPkF,
      recoverProductionForsPk suite params sk.pkSeed FORS_TREE FORS_KP (FORS_IDXS)
          sigStar.forsOpenings =
        some forsPkF ∧
      verifyProductionHypertreeLayers suite params sk.pkSeed PK_ROOT sigStar.rRand 0
        sigStar.leafGlobalIdx forsPkF sigStar.layerSigs = some PK_ROOT := by
  obtain ⟨hPwf, hLen, _, idxs, forsPkF, hD, hFors, hHt⟩ :=
    verifyProductionPqHashSig_stateless_inv suite params _ msgStar sigStar hStateless hAccept
  obtain ⟨_, _, hLt, hILen, hIBnd⟩ := deriveProductionStatelessInputs_bounds _ _ _ _ _ _ _ _ hD
  have hI : (FORS_IDXS) = idxs := by
    unfold prodSigForsIdxs
    rw [hD]
  rw [hI]
  exact ⟨hPwf, hLen, hLt, hILen, hIBnd, forsPkF, hFors, hHt⟩

/-- Every accepted production signature names a leaf of the hypertree. -/
theorem production_accept_leaf_lt (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hAccept : verifyProductionPqHashSig suite params (derivePublicKey suite params sk) msgStar
      sigStar = true) :
    sigStar.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight) := by
  cases hSt : params.statefulJorts
  · exact (prod_stateless_accept_facts suite params sk msgStar sigStar hSt hAccept).2.2.1
  · exact (verifyProductionPqHashSig_stateful_inv suite params _ msgStar sigStar hSt hAccept).2.2.1

/-! ### One hypertree layer -/

/-- `prod_layer_divergence_break` as a function: the collision met on the XMSS path, the WOTS
    public-key compression, a chain step or the layer digest, or else the preimage event. -/
def prodLayerExtract (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hw : params.w = 4 ∨ params.w = 16) (hPwf : params.productionWellFormed = true)
    (hLog : ∀ e ∈ log, ProdLogEntryOk suite params sk e)
    (hCons : ProdLogConsistent suite params sk log)
    (i : Nat) (hi : i < params.numLayers) (cur : List UInt8) (digF : List Nat)
    (hDigF : digF = digs⟪i⟫)
    (hDiff : ∀ e ∈ log, e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) = pos⟪i⟫ →
      cur ≠ prodHonestLayerMsg suite params sk e i)
    (hTsw : checkTargetSum params.w params.ell1 params.targetSum digF = true)
    (hWalk : walkMerkleAuthPath suite sk.pkSeed (UInt32.ofNat i) tree⟪i⟫ .tree params.subtreeHeight
        0
        kp⟪i⟫
        (recoverWotsPkFromSig suite params sk.pkSeed (UInt32.ofNat i) tree⟪i⟫ kp⟪i⟫ digF
          lsig⟪i⟫.wotsChains)
        lsig⟪i⟫.authPath =
      some (computeXmssSubtreeRoot suite params sk (UInt32.ofNat i) tree⟪i⟫)) :
    PSum (ProdTcrWitness suite params sk log msgStar sigStar) (ProdPreimageBreak suite params sk
        log msgStar sigStar) :=
  have hKpLt : kp⟪i⟫ < 2 ^ params.subtreeHeight := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hWalkNode : walkMerkleAuthPath suite sk.pkSeed (UInt32.ofNat i) tree⟪i⟫ .tree
      params.subtreeHeight 0 kp⟪i⟫
      (recoverWotsPkFromSig suite params sk.pkSeed (UInt32.ofNat i) tree⟪i⟫ kp⟪i⟫ digF
        lsig⟪i⟫.wotsChains)
      lsig⟪i⟫.authPath =
      some (computeMerkleNode suite sk.pkSeed (UInt32.ofNat i) tree⟪i⟫ .tree
        (computeWotsPk suite params sk (UInt32.ofNat i) tree⟪i⟫) params.subtreeHeight 0) := by
    rw [← computeXmssSubtreeRoot_eq]; exact hWalk
  match prodWalkMerkleExtract suite sk.pkSeed (UInt32.ofNat i) tree⟪i⟫ .tree
      (computeWotsPk suite params sk (UInt32.ofNat i) tree⟪i⟫) kp⟪i⟫ params.subtreeHeight
      (ProdTcrWitness suite params sk log msgStar sigStar)
      (fun h n a b hH hLo hHi hNe hHash =>
        ⟨.xmssNode i h n, _, ⟨hi, hH, hLo, hHi⟩, ⟨a, b, rfl⟩, hNe, hHash⟩)
      params.subtreeHeight 0 kp⟪i⟫ _ _ (Nat.le_refl _) hKpLt
      (by rw [Nat.zero_mul, Nat.zero_add]) hWalkNode with
  | .inr w => .inl w
  | .inl hPk =>
    have hTlEq :
        thCall suite tagThTl sk.pkSeed ⟨UInt32.ofNat i, tree⟪i⟫, .wotsPk, UInt32.ofNat kp⟪i⟫, 0, 0⟩
          (recoverWotsEndpoints suite params sk.pkSeed (UInt32.ofNat i) tree⟪i⟫ kp⟪i⟫ digF
            lsig⟪i⟫.wotsChains) =
        thCall suite tagThTl sk.pkSeed ⟨UInt32.ofNat i, tree⟪i⟫, .wotsPk, UInt32.ofNat kp⟪i⟫, 0, 0⟩
          ((List.range params.ell1).map fun r =>
            honestChainNode suite sk (UInt32.ofNat i) tree⟪i⟫ kp⟪i⟫ r (params.w - 1)) := by
      rw [recoverWotsPkFromSig_eq, computeWotsPk_eq, thTweakTl_eq, thTweakTl_eq] at hPk
      exact hPk
    match prodThCallSplit suite hTlEq with
    | .inr ⟨hNe, hHash⟩ => .inl ⟨.wotsPk i, _, hi, ⟨_, rfl⟩, hNe, hHash⟩
    | .inl hEnds =>
      match prodAllChainsExtract suite params sk (UInt32.ofNat i) tree⟪i⟫ kp⟪i⟫ digF
          lsig⟪i⟫.wotsChains (ProdTcrWitness suite params sk log msgStar sigStar)
          (fun r s x hr hs hNe hHash => ⟨.chainStep i r s, _, ⟨hi, hr, hs⟩, ⟨x, rfl⟩, hNe, hHash⟩)
          hEnds hTsw params.ell1 (Nat.le_refl _) with
      | .inr w => .inl w
      | .inl hChains =>
        match prodListSearch
            (fun e : List UInt8 × PqHashSig =>
              e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) = pos⟪i⟫)
            (fun e =>
              if h : e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) = pos⟪i⟫ then .inl h
              else .inr h) log with
        | .inr hNoUse =>
          .inr (prod_layer_preimage_unused suite params sk log msgStar sigStar hw hPwf i hi digF
              hTsw hChains hNoUse)
        | .inl ⟨e, ⟨he, hPos⟩⟩ =>
          if hDigEq : digF = prodLogLayerDigits suite params sk e i then
            if hPre : prodLayerPreimage params sigStar.rRand sk.pkSeed PK_ROOT cur i tree⟪i⟫
                (UInt32.ofNat kp⟪i⟫) lsig⟪i⟫.tswCtr =
                ProdTargetIdx.input suite params sk sigStar.leafGlobalIdx (.signedDigest e i) then
              False.elim (by
                simp only [ProdTargetIdx.input] at hPre
                rw [hPos] at hPre
                exact hDiff e he hPos (prodLayerPreimage_cur_inj hPre))
            else
              .inl ⟨.signedDigest e i, _, ⟨he, hi, hPos⟩, ⟨cur, rfl⟩, hPre, by
                have hDE := hDigEq
                rw [hDigF] at hDE
                unfold prodLogLayerDigits at hDE
                have hD := production_digits_inj params hw hPwf
                  (productionLayerDigest_length _ _ _ _ _ _ _ _ _ _)
                  (by
                    unfold prodLogLayerDigest
                    exact productionLayerDigest_length _ _ _ _ _ _ _ _ _ _)
                  hDE
                unfold prodLogLayerDigest at hD
                rw [productionLayerDigest_rawHash, productionLayerDigest_rawHash] at hD
                exact hD⟩
          else
            .inr (prod_layer_preimage_logged suite params sk log msgStar sigStar hCons i hi digF
                hTsw hChains e he
              (hLog e he) hPos hDigEq)

/-! ### The hypertree walk -/

/-- Result of walking the layers from `i` upward with layer message `cur`. -/
inductive ProdWalkOutcome (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8) (sigStar : PqHashSig) (i : Nat)
        (cur : List UInt8) : Type where
  /-- `cur` is the message the logged signature `e` signed at this position. -/
  | honest (e : List UInt8 × PqHashSig) (he : e ∈ log)
      (hPos : e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) = pos⟪i⟫)
      (hEq : cur = prodHonestLayerMsg suite params sk e i)
  | tcr (w : ProdTcrWitness suite params sk log msgStar sigStar)
  | pre (h : ProdPreimageBreak suite params sk log msgStar sigStar)

/-- `prod_hypertree_walk_break` as a function. -/
def prodHypertreeWalkExtract (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hw : params.w = 4 ∨ params.w = 16) (hPwf : params.productionWellFormed = true)
    (hLog : ∀ e ∈ log, ProdLogEntryOk suite params sk e)
    (hCons : ProdLogConsistent suite params sk log) :
    ∀ (sigs : List LayerXmssSig) (i : Nat) (cur : List UInt8),
      sigs ≠ [] →
      (∀ j, sigs.getD j ⟨0, [], []⟩ = sigStar.layerSigs.getD (i + j) ⟨0, [], []⟩) →
      i + sigs.length = params.numLayers →
      verifyProductionHypertreeLayers suite params sk.pkSeed PK_ROOT sigStar.rRand i (pos⟪i⟫) cur
          sigs =
        some TOP_ROOT →
      ProdWalkOutcome suite params sk log msgStar sigStar i cur
  | [], _, _, hNe, _, _, _ => absurd rfl hNe
  | lsig :: rest, i, cur, _, hAlign, hLenEq, hVer =>
    have hi : i < params.numLayers := by
      rw [← hLenEq, List.length_cons]
      omega
    have hLs : lsig = lsig⟪i⟫ := by
      have h := hAlign 0
      rw [List.getD_cons_zero, Nat.add_zero] at h
      exact h
    have hStep : pos⟪i⟫ / 2 ^ params.subtreeHeight =
        sigStar.leafGlobalIdx / 2 ^ ((i + 1) * params.subtreeHeight) := by
      have h := div_pow_mul_pow_mul sigStar.leafGlobalIdx i 1 params.subtreeHeight
      rw [Nat.one_mul] at h
      exact h
    have hInv := verifyProductionHypertreeLayers_cons_inv suite params _ _ _ _ _ _ _ _ _ hVer
    have hTsw : checkTargetSum params.w params.ell1 params.targetSum digs⟪i⟫ = true := by
      rw [← hLs]; exact hInv.2.1
    match hNextW : walkMerkleAuthPath suite sk.pkSeed (UInt32.ofNat i) tree⟪i⟫ .tree
        params.subtreeHeight 0 kp⟪i⟫
        (recoverWotsPkFromSig suite params sk.pkSeed (UInt32.ofNat i) tree⟪i⟫ kp⟪i⟫ digs⟪i⟫
          lsig⟪i⟫.wotsChains)
        lsig⟪i⟫.authPath with
    | none => False.elim (by
        obtain ⟨_, _, n', hW, _⟩ := hInv
        rw [hLs] at hW
        rw [hNextW] at hW
        cases hW)
    | some next =>
      have hRest : verifyProductionHypertreeLayers suite params sk.pkSeed PK_ROOT sigStar.rRand (i
          + 1)
          (sigStar.leafGlobalIdx / 2 ^ ((i + 1) * params.subtreeHeight)) next rest = some TOP_ROOT
              := by
        obtain ⟨_, _, n', hW, hR⟩ := hInv
        rw [hLs] at hW
        rw [hNextW] at hW
        have hn : next = n' := Option.some.inj hW
        rw [← hn, hStep] at hR
        exact hR
      let step : PSum (next = computeXmssSubtreeRoot suite params sk (UInt32.ofNat i) tree⟪i⟫)
          (PSum (ProdTcrWitness suite params sk log msgStar sigStar) (ProdPreimageBreak suite
              params sk log msgStar sigStar)) :=
        match hR : rest with
        | [] => .inl (by
            have hRest' := hRest
            rw [hR, verifyProductionHypertreeLayers_nil] at hRest'
            simp only [Option.some.injEq] at hRest'
            have hD : params.numLayers = i + 1 := by
              rw [← hLenEq, hR, List.length_cons, List.length_nil]
            rw [hD, Nat.add_sub_cancel] at hRest'
            rw [hStep]
            exact hRest')
        | _ :: _ =>
          match prodHypertreeWalkExtract suite params sk log msgStar sigStar hw hPwf hLog hCons
              rest (i + 1) next
              (by rw [hR]; exact List.cons_ne_nil _ _)
              (fun j => by
                have h := hAlign (j + 1)
                rw [List.getD_cons_succ] at h
                rw [h, show i + (j + 1) = i + 1 + j by omega])
              (by rw [← hLenEq, List.length_cons]; omega)
              hRest with
          | .honest e _ hPos hEq => .inl (by
              rw [hEq]
              unfold prodHonestLayerMsg
              simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
              rw [hPos, hStep])
          | .tcr w => .inr (.inl w)
          | .pre h => .inr (.inr h)
      match step with
      | .inr (.inl w) => .tcr w
      | .inr (.inr h) => .pre h
      | .inl hNext =>
        match prodListSearch
            (fun e : List UInt8 × PqHashSig =>
              e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) = pos⟪i⟫ ∧
              cur = prodHonestLayerMsg suite params sk e i)
            (fun e =>
              if h : e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) = pos⟪i⟫ ∧
                  cur = prodHonestLayerMsg suite params sk e i then .inl h
              else .inr h) log with
        | .inl ⟨e, ⟨he, hP⟩⟩ => .honest e he hP.1 hP.2
        | .inr hNone =>
          match prodLayerExtract suite params sk log msgStar sigStar hw hPwf hLog hCons i hi cur
              digs⟪i⟫ rfl
              (fun e he hPos hEq => hNone e he ⟨hPos, hEq⟩) hTsw
              (by rw [← hNext]; exact hNextW) with
          | .inl w => .tcr w
          | .inr h => .pre h

end Qsag
end

#verify_constructive Qsag.prod_layer_preimage_logged Qsag.prod_layer_preimage_unused
#verify_constructive Qsag.production_accept_leaf_lt

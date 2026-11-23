module
/-
# Qsag.Protocol.Signing.HulsingExplicitClassify — Unsealed 3-Way Forgery Classification on `ExecEufCmaIdealPrfGame`

Constructively classifies every winning execution of `ExecEufCmaIdealPrfGame` (`rfMsg` and `rfSec`
idealized) into one of three explicit, unsealed witness types ready for interactive `Spec.Code`
reductions into `Spec.Assumptions`:
1. `ExplicitItsrCover` — FORS subset-cover collision (`statefulJorts = false`, `0 < forsTrees`),
2. `ExplicitTcrWitness` — explicit `Spec.TargetBreak` collision under `suiteTweakHash suite pkSeed`,
3. `ExplicitPreBreak` — explicit unopened FORS secret leaf or WOTS+C chain-step inversion witness.
-/

public import Qsag.Protocol.Signing.HulsingFullOverlay
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-! ## §1. Unsealed Break Structures & Constructive Hypertree Extraction -/

/-- Unsealed ITSR subset-cover break over `prodSigForsLeaves`. -/
structure ExplicitItsrCover (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (log : List (List UInt8 × PqHashSig))
    (msgStar : List UInt8) (sigStar : PqHashSig) : Prop where
  accepted : verifyProductionPqHashSig suite params pk msgStar sigStar = true
  stateless : params.statefulJorts = false
  trees_pos : 0 < params.forsTrees
  fresh : ∀ e ∈ log, e.1 ≠ msgStar
  covered : ∀ a ∈ prodSigForsLeaves suite params pk msgStar sigStar,
    ∃ e ∈ log, a ∈ prodSigForsLeaves suite params pk e.1 e.2

/-- Explicit `TargetBreak` collision witness under `suiteTweakHash suite pkSeed`. -/
structure ExplicitTcrWitness (suite : TweakableHashSuite) (pkSeed : Spec.Bytes) : Type where
  brk : Spec.TargetBreak
  ne : brk.candidate ≠ brk.committed
  collides : suiteTweakHash suite pkSeed brk.tweak brk.candidate =
    suiteTweakHash suite pkSeed brk.tweak brk.committed

/-- Unsealed preimage witness naming a concrete FORS leaf or WOTS chain step. -/
inductive ExplicitPreBreak (suite secOv : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (log : List (List UInt8 × PqHashSig))
    (msgStar : List UInt8) (sigStar : PqHashSig) : Prop where
  | fors (j : Nat) (hj : j < params.forsTrees)
      (stateless : params.statefulJorts = false)
      (leafLt : sigStar.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight))
      (idxLt : (prodSigForsIdxs suite params (derivePublicKey secOv params sk) msgStar
        sigStar).getD j 0 < 2 ^ params.forsHeight)
      (unrevealed : ∀ e ∈ log,
        (sigStar.leafGlobalIdx, j,
          (prodSigForsIdxs suite params (derivePublicKey secOv params sk) msgStar
            sigStar).getD j 0) ∉
          prodSigForsLeaves suite params (derivePublicKey secOv params sk) e.1 e.2)
      (inverts :
        forsIndexedLeafHash suite sk.pkSeed
          (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight))
          (sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight) j
          ((prodSigForsIdxs suite params (derivePublicKey secOv params sk) msgStar
            sigStar).getD j 0)
          (sigStar.forsOpenings.getD j ⟨[], []⟩).secretVal =
        forsIndexedLeafFn secOv sk
          (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight))
          (sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight) j
          ((prodSigForsIdxs suite params (derivePublicKey secOv params sk) msgStar
            sigStar).getD j 0))
  | wots (i : Nat) (hi : i < params.numLayers) (r : Nat) (hr : r < params.ell1)
      (step : Nat) (hstep : step + 1 ≤ params.w - 1)
      (leafLt : sigStar.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight))
      (inverts :
        thChainF suite sk.pkSeed
          ⟨UInt32.ofNat i,
           UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
             2 ^ params.subtreeHeight),
           .wotsHash,
           UInt32.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) %
             2 ^ params.subtreeHeight),
           UInt32.ofNat r, UInt32.ofNat step⟩
          ((sigStar.layerSigs.getD i ⟨0, [], []⟩).wotsChains.getD r []) =
        honestChainNode secOv sk (UInt32.ofNat i)
          (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
            2 ^ params.subtreeHeight))
          (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight)
          r (step + 1))
      (unrevealed : ∀ e ∈ log,
        e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) =
          sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) →
        step < (prodLogLayerDigits secOv params sk e i).getD r 0)

private def mkMultiRoleCollision (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (secFn : Spec.Bytes → Spec.Bytes) (role : List UInt8)
    (adrs : HashAdrs) (argsF argsH : List (List UInt8))
    (hRole : role ≠ tagPrf) (hArgsNe : argsF ≠ argsH)
    (hHash : (secOverlaySuite suite pkSeed secFn).rawHash (thPreimage role pkSeed adrs argsF) =
      (secOverlaySuite suite pkSeed secFn).rawHash (thPreimage role pkSeed adrs argsH)) :
    ExplicitTcrWitness suite pkSeed :=
  have hSecEq : ∀ xs, (secOverlaySuite suite pkSeed secFn).rawHash
      (thPreimage role pkSeed adrs xs) =
      suite.rawHash (thPreimage role pkSeed adrs xs) := fun xs => by
    rw [← thCall_eq, ← thCall_eq]
    exact secOverlaySuite_nonPrf_thCall suite pkSeed secFn hRole pkSeed adrs xs
  ⟨⟨encodeMultiRoleTweak role adrs, encodeMultiFrame argsH, encodeMultiFrame argsF⟩,
    fun hEq => by
      have h1 := congrArg decodeMultiFrameBytes hEq
      rw [decodeMultiFrameBytes_encodeMultiFrame, decodeMultiFrameBytes_encodeMultiFrame] at h1
      exact hArgsNe (Option.some.inj h1),
    by
      rw [suiteTweakHash_multiRole, suiteTweakHash_multiRole, ← hSecEq argsF, ← hSecEq argsH]
      exact hHash⟩

private def mkChainFCollision (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (secFn : Spec.Bytes → Spec.Bytes) (adrs : HashAdrs) (xF xH : List UInt8)
    (hPreNe : thPreimage tagThF pkSeed adrs [xF] ≠ thPreimage tagThF pkSeed adrs [xH])
    (hHash : (secOverlaySuite suite pkSeed secFn).rawHash (thPreimage tagThF pkSeed adrs [xF]) =
      (secOverlaySuite suite pkSeed secFn).rawHash (thPreimage tagThF pkSeed adrs [xH])) :
    ExplicitTcrWitness suite pkSeed :=
  have hSecEq : ∀ x, (secOverlaySuite suite pkSeed secFn).rawHash
      (thPreimage tagThF pkSeed adrs [x]) =
      thChainF suite pkSeed adrs x := fun x => by
    rw [← thCall_eq, thChainF_eq]
    exact secOverlaySuite_nonPrf_thCall suite pkSeed secFn tagThF_ne_tagPrf.1 pkSeed adrs [x]
  ⟨⟨encodeChainFTweak adrs, xH, xF⟩,
    fun hEq => hPreNe (congrArg (fun z => thPreimage tagThF pkSeed adrs [z]) hEq),
    by rw [suiteTweakHash_chainF, suiteTweakHash_chainF, ← hSecEq xF, ← hSecEq xH]; exact hHash⟩

theorem honestChainNode_secOv_succ (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (secFn : Spec.Bytes → Spec.Bytes) (l : UInt32) (t : UInt64) (kp r step : Nat) :
    honestChainNode (secOverlaySuite suite pkSeed secFn) ⟨[], [], pkSeed⟩ l t kp r (step + 1) =
      thChainF suite pkSeed ⟨l, t, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat step⟩
        (honestChainNode (secOverlaySuite suite pkSeed secFn) ⟨[], [], pkSeed⟩ l t kp r step) := by
  rw [← honestChainNode_succ, thChainF_eq, thChainF_eq,
    secOverlaySuite_nonPrf_thCall _ _ _ tagThF_ne_tagPrf.1]

private def explicitLayerExtract (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (secFn : Spec.Bytes → Spec.Bytes)
    (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hw : params.w = 4 ∨ params.w = 16) (hPwf : params.productionWellFormed = true)
    (hLeafLt : sigStar.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight))
    (hLogValid : ∀ e ∈ log, ∀ i < params.numLayers,
      checkTargetSum params.w params.ell1 params.targetSum
        (prodLogLayerDigits (secOverlaySuite suite pkSeed secFn) params ⟨[], [], pkSeed⟩ e i) = true)
    (hCons : ProdLogConsistent (secOverlaySuite suite pkSeed secFn) params ⟨[], [], pkSeed⟩ log)
    (i : Nat) (hi : i < params.numLayers) (cur : List UInt8)
    (hDiff : ∀ e ∈ log,
      e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) =
        sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) →
      cur ≠ prodHonestLayerMsg (secOverlaySuite suite pkSeed secFn) params ⟨[], [], pkSeed⟩ e i)
    (hTsw : checkTargetSum params.w params.ell1 params.targetSum
      (extractBaseWDigits params.w params.ell1
        (productionLayerDigest (secOverlaySuite suite pkSeed secFn) params sigStar.rRand pkSeed
          (derivePublicKey (secOverlaySuite suite pkSeed secFn) params ⟨[], [], pkSeed⟩).pkRoot cur i
          (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
            2 ^ params.subtreeHeight))
          (UInt32.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) %
            2 ^ params.subtreeHeight))
          (sigStar.layerSigs.getD i ⟨0, [], []⟩).tswCtr)) = true)
    (hWalk : walkMerkleAuthPath (secOverlaySuite suite pkSeed secFn) pkSeed (UInt32.ofNat i)
      (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
        2 ^ params.subtreeHeight)) .tree params.subtreeHeight 0
      (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight)
      (recoverWotsPkFromSig (secOverlaySuite suite pkSeed secFn) params pkSeed (UInt32.ofNat i)
        (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
          2 ^ params.subtreeHeight))
        (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight)
        (extractBaseWDigits params.w params.ell1
          (productionLayerDigest (secOverlaySuite suite pkSeed secFn) params sigStar.rRand pkSeed
            (derivePublicKey (secOverlaySuite suite pkSeed secFn) params ⟨[], [], pkSeed⟩).pkRoot
            cur i
            (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
              2 ^ params.subtreeHeight))
            (UInt32.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) %
              2 ^ params.subtreeHeight))
            (sigStar.layerSigs.getD i ⟨0, [], []⟩).tswCtr))
        (sigStar.layerSigs.getD i ⟨0, [], []⟩).wotsChains)
      (sigStar.layerSigs.getD i ⟨0, [], []⟩).authPath =
      some (computeXmssSubtreeRoot (secOverlaySuite suite pkSeed secFn) params ⟨[], [], pkSeed⟩
        (UInt32.ofNat i)
        (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
          2 ^ params.subtreeHeight)))) :
    PSum (ExplicitTcrWitness suite pkSeed)
      (ExplicitPreBreak suite (secOverlaySuite suite pkSeed secFn) params ⟨[], [], pkSeed⟩ log
        msgStar sigStar) :=
  let sov := secOverlaySuite suite pkSeed secFn
  let sk0 : PqSecretKey := ⟨[], [], pkSeed⟩
  let posI := sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)
  let treeI := UInt64.ofNat (posI / 2 ^ params.subtreeHeight)
  let kpI := posI % 2 ^ params.subtreeHeight
  let lsig := sigStar.layerSigs.getD i ⟨0, [], []⟩
  let pkRoot := (derivePublicKey sov params sk0).pkRoot
  let digF := extractBaseWDigits params.w params.ell1
    (productionLayerDigest sov params sigStar.rRand pkSeed pkRoot cur i treeI (UInt32.ofNat kpI)
      lsig.tswCtr)
  have hThHNe : tagThH ≠ tagPrf := by
    simp only [tagThH.public_eqs, tagPrf.public_eqs]; decide +kernel
  have hWalkNode : walkMerkleAuthPath sov pkSeed (UInt32.ofNat i) treeI .tree params.subtreeHeight
      0 kpI (recoverWotsPkFromSig sov params pkSeed (UInt32.ofNat i) treeI kpI digF lsig.wotsChains)
      lsig.authPath =
      some (computeMerkleNode sov pkSeed (UInt32.ofNat i) treeI .tree
        (computeWotsPk sov params sk0 (UInt32.ofNat i) treeI) params.subtreeHeight 0) := by
    change walkMerkleAuthPath sov pkSeed (UInt32.ofNat i) treeI .tree params.subtreeHeight 0 kpI
        (recoverWotsPkFromSig sov params pkSeed (UInt32.ofNat i) treeI kpI digF lsig.wotsChains)
        lsig.authPath =
      some (computeMerkleNode sov sk0.pkSeed (UInt32.ofNat i) treeI .tree
        (computeWotsPk sov params sk0 (UInt32.ofNat i) treeI) params.subtreeHeight 0)
    rw [← computeXmssSubtreeRoot_eq]; exact hWalk
  match prodWalkMerkleExtract sov pkSeed (UInt32.ofNat i) treeI .tree
      (computeWotsPk sov params sk0 (UInt32.ofNat i) treeI) kpI params.subtreeHeight
      (ExplicitTcrWitness suite pkSeed)
      (fun h n a b _ _ _ hNe hHash =>
        mkMultiRoleCollision suite pkSeed secFn tagThH
          ⟨UInt32.ofNat i, treeI, .tree, 0, UInt32.ofNat (h + 1), UInt32.ofNat n⟩ [a, b] _
          hThHNe (fun hEq => hNe (congrArg _ hEq)) hHash)
      params.subtreeHeight 0 kpI _ _ (Nat.le_refl _) (Nat.mod_lt _ (Nat.two_pow_pos _))
      (by rw [Nat.zero_mul, Nat.zero_add]) hWalkNode with
  | .inr w => .inl w
  | .inl hPk =>
    have hTlEq :
        thCall sov tagThTl pkSeed ⟨UInt32.ofNat i, treeI, .wotsPk, UInt32.ofNat kpI, 0, 0⟩
          (recoverWotsEndpoints sov params pkSeed (UInt32.ofNat i) treeI kpI digF lsig.wotsChains) =
        thCall sov tagThTl pkSeed ⟨UInt32.ofNat i, treeI, .wotsPk, UInt32.ofNat kpI, 0, 0⟩
          ((List.range params.ell1).map fun r =>
            honestChainNode sov sk0 (UInt32.ofNat i) treeI kpI r (params.w - 1)) := by
      rw [recoverWotsPkFromSig_eq, computeWotsPk_eq, thTweakTl_eq, thTweakTl_eq] at hPk
      exact hPk
    match prodThCallSplit sov hTlEq with
    | .inr ⟨hNe, hHash⟩ =>
      .inl (mkMultiRoleCollision suite pkSeed secFn tagThTl
        ⟨UInt32.ofNat i, treeI, .wotsPk, UInt32.ofNat kpI, 0, 0⟩ _ _ tagThF_ne_tagPrf.2
        (fun hEq => hNe (congrArg _ hEq)) hHash)
    | .inl hEnds =>
      match prodAllChainsExtract sov params sk0 (UInt32.ofNat i) treeI kpI digF lsig.wotsChains
          (ExplicitTcrWitness suite pkSeed)
          (fun r s x _ _ hNe hHash =>
            mkChainFCollision suite pkSeed secFn
              ⟨UInt32.ofNat i, treeI, .wotsHash, UInt32.ofNat kpI, UInt32.ofNat r, UInt32.ofNat s⟩
              x _ hNe hHash)
          hEnds hTsw params.ell1 (Nat.le_refl _) with
      | .inr w => .inl w
      | .inl hChains =>
        match prodListSearch
            (fun e : List UInt8 × PqHashSig =>
              e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) = posI)
            (fun e =>
              if h : e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) = posI then .inl h
              else .inr h) log with
        | .inr hNoUse =>
          .inr (by
            have hGeom := params.productionWellFormed_geom hPwf hw
            have hStrict : params.targetSum < (params.w - 1) * params.ell1 := by
              rw [PqHashParams.targetSum_eq]
              rcases hGeom with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> decide
            obtain ⟨hLenF, _, hSumF⟩ := (checkTargetSum_iff _ _ _ _).mp hTsw
            cases hFind : findDigitLt (params.w - 1) digF with
            | none =>
              exfalso
              have hGe := prod_sumDigits_ge_mul (params.w - 1) digF
                (prod_findDigitLt_none (params.w - 1) digF hFind)
              change digF.length = params.ell1 at hLenF
              change sumDigits digF = params.targetSum at hSumF
              rw [hLenF, hSumF] at hGe
              omega
            | some r =>
              obtain ⟨hrLen, hrVal⟩ := findDigitLt_sound (params.w - 1) hFind
              change digF.length = params.ell1 at hLenF
              have hr : r < params.ell1 := by rw [← hLenF]; exact hrLen
              have hF : digF.getD r 0 = digF[r] := list_getD_eq_getElem digF 0 hrLen
              exact .wots i hi r hr (digF.getD r 0) (by rw [hF]; exact hrVal) hLeafLt
                (by rw [hChains r hr, honestChainNode_secOv_succ])
                (fun e' he' hP' => absurd hP' (hNoUse e' he')))
        | .inl ⟨e, ⟨he, hPos⟩⟩ =>
          if hDigEq : digF = prodLogLayerDigits sov params sk0 e i then
            .inl (by
              let honCur := prodHonestLayerMsg sov params sk0 e i
              let tw := encodeLayerDigestTweak params i treeI (UInt32.ofNat kpI)
              let mCand := encodeLayerDigestMsg sigStar.rRand pkRoot cur lsig.tswCtr
              let mHon := encodeLayerDigestMsg e.2.rRand pkRoot honCur
                (e.2.layerSigs.getD i ⟨0, [], []⟩).tswCtr
              have hCurNe : cur ≠ honCur := hDiff e he hPos
              have hMsgNe : mCand ≠ mHon := fun hEq => by
                have hDec := congrArg decodeMultiFrameBytes hEq
                dsimp only [mCand, mHon] at hDec
                rw [encodeLayerDigestMsg.public_eqs, encodeLayerDigestMsg.public_eqs,
                  decodeMultiFrameBytes_encodeMultiFrame,
                  decodeMultiFrameBytes_encodeMultiFrame] at hDec
                injection hDec with hL
                simp only [List.cons.injEq] at hL
                exact hCurNe hL.2.2.1
              have hDigEqSuite :
                  productionLayerDigest suite params sigStar.rRand pkSeed pkRoot cur i treeI
                    (UInt32.ofNat kpI) lsig.tswCtr =
                  productionLayerDigest suite params e.2.rRand pkSeed pkRoot honCur i treeI
                    (UInt32.ofNat kpI) (e.2.layerSigs.getD i ⟨0, [], []⟩).tswCtr := by
                have hSecToSuite : ∀ rR c ctr,
                    productionLayerDigest sov params rR pkSeed pkRoot c i treeI (UInt32.ofNat kpI)
                      ctr =
                    productionLayerDigest suite params rR pkSeed pkRoot c i treeI
                      (UInt32.ofNat kpI) ctr := fun rR c ctr => by
                  rw [productionLayerDigest_eq, productionLayerDigest_eq]
                  split
                  · rw [thHashLeafMsg_eq, thHashLeafMsg_eq]
                    exact secOverlaySuite_thCall_cons2 _ _ _ _ _ _ _ _ _
                  · rw [thHashInternalNode_eq, thHashInternalNode_eq]
                    exact secOverlaySuite_thCall_cons2 _ _ _ _ _ _ _ _ _
                have hDE := hDigEq
                unfold prodLogLayerDigits prodLogLayerDigest at hDE
                rw [hPos] at hDE
                have hInj := production_digits_inj params hw hPwf
                  (productionLayerDigest_length _ _ _ _ _ _ _ _ _ _)
                  (productionLayerDigest_length _ _ _ _ _ _ _ _ _ _) hDE
                rw [hSecToSuite, hSecToSuite] at hInj
                exact hInj
              exact ⟨⟨tw, mHon, mCand⟩, hMsgNe, by
                rw [suiteTweakHash_layerDigest, suiteTweakHash_layerDigest]; exact hDigEqSuite⟩)
          else
            .inr (by
              let honDig := prodLogLayerDigits sov params sk0 e i
              have hValidH := hLogValid e he i hi
              obtain ⟨hLenF, _, _⟩ := (checkTargetSum_iff _ _ _ _).mp hTsw
              obtain ⟨_, hBoundH, _⟩ := (checkTargetSum_iff _ _ _ _).mp hValidH
              obtain ⟨r, hr2, hr1, hlt, _⟩ :=
                (tsw_incomparable_no_chain_forgery hValidH hTsw (fun hEq => hDigEq hEq.symm)).2
              change digF.length = params.ell1 at hLenF
              change r < digF.length at hr2
              change r < honDig.length at hr1
              change digF[r] < honDig[r] at hlt
              have hr : r < params.ell1 := by rw [← hLenF]; exact hr2
              have hHonLtW : honDig[r] < params.w := hBoundH _ (List.getElem_mem hr1)
              have hF : digF.getD r 0 = digF[r] := list_getD_eq_getElem digF 0 hr2
              have hH : honDig.getD r 0 = honDig[r] := list_getD_eq_getElem honDig 0 hr1
              have hStepBnd : digF.getD r 0 + 1 ≤ params.w - 1 := by
                rw [hF]; exact Decidable.byContradiction (fun _ => by omega)
              exact .wots i hi r hr (digF.getD r 0) hStepBnd hLeafLt
                (by rw [hChains r hr, honestChainNode_secOv_succ])
                (fun e' he' hP' => by
                  rw [hCons e' he' e he i hi (hP'.trans hPos.symm)]
                  change digF.getD r 0 < honDig.getD r 0
                  rw [hF, hH]; exact hlt))

private inductive ExplicitWalkRes (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (secFn : Spec.Bytes → Spec.Bytes)
    (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8) (sigStar : PqHashSig)
    (i : Nat) (cur : List UInt8) : Type where
  | honest (e : List UInt8 × PqHashSig) (he : e ∈ log)
      (hPos : e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) =
        sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight))
      (hEq : cur = prodHonestLayerMsg (secOverlaySuite suite pkSeed secFn) params ⟨[], [], pkSeed⟩
        e i)
  | tcr (w : ExplicitTcrWitness suite pkSeed)
  | pre (h : ExplicitPreBreak suite (secOverlaySuite suite pkSeed secFn) params ⟨[], [], pkSeed⟩
      log msgStar sigStar)

private def explicitHypertreeWalk (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (secFn : Spec.Bytes → Spec.Bytes)
    (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hw : params.w = 4 ∨ params.w = 16) (hPwf : params.productionWellFormed = true)
    (hLeafLt : sigStar.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight))
    (hLogValid : ∀ e ∈ log, ∀ i < params.numLayers,
      checkTargetSum params.w params.ell1 params.targetSum
        (prodLogLayerDigits (secOverlaySuite suite pkSeed secFn) params ⟨[], [], pkSeed⟩ e i) = true)
    (hCons : ProdLogConsistent (secOverlaySuite suite pkSeed secFn) params ⟨[], [], pkSeed⟩ log) :
    ∀ (sigs : List LayerXmssSig) (i : Nat) (cur : List UInt8),
      sigs ≠ [] →
      (∀ j, sigs.getD j ⟨0, [], []⟩ = sigStar.layerSigs.getD (i + j) ⟨0, [], []⟩) →
      i + sigs.length = params.numLayers →
      verifyProductionHypertreeLayers (secOverlaySuite suite pkSeed secFn) params pkSeed
          (derivePublicKey (secOverlaySuite suite pkSeed secFn) params ⟨[], [], pkSeed⟩).pkRoot
          sigStar.rRand i (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)) cur sigs =
        some (computeXmssSubtreeRoot (secOverlaySuite suite pkSeed secFn) params ⟨[], [], pkSeed⟩
          (UInt32.ofNat (params.numLayers - 1))
          (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (params.numLayers * params.subtreeHeight)))) →
      ExplicitWalkRes suite params pkSeed secFn log msgStar sigStar i cur
  | [], _, _, hNe, _, _, _ => absurd rfl hNe
  | lsig :: rest, i, cur, _, hAlign, hLenEq, hVer =>
    let sov := secOverlaySuite suite pkSeed secFn
    let sk0 : PqSecretKey := ⟨[], [], pkSeed⟩
    have hi : i < params.numLayers :=
      Decidable.byContradiction (fun _ => by
        have hL := hLenEq; rw [List.length_cons] at hL; omega)
    have hLs : lsig = sigStar.layerSigs.getD i ⟨0, [], []⟩ := by
      have h := hAlign 0; rw [List.getD_cons_zero, Nat.add_zero] at h; exact h
    have hStep : sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight =
        sigStar.leafGlobalIdx / 2 ^ ((i + 1) * params.subtreeHeight) := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_add,
        show i * params.subtreeHeight + params.subtreeHeight = (i + 1) * params.subtreeHeight by
          rw [Nat.succ_mul]]
    have hInv := verifyProductionHypertreeLayers_cons_inv sov params _ _ _ _ _ _ _ _ _ hVer
    have hTsw := hLs ▸ hInv.2.1
    match hNextW : walkMerkleAuthPath sov pkSeed (UInt32.ofNat i)
        (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
          2 ^ params.subtreeHeight)) .tree params.subtreeHeight 0
        (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight)
        (recoverWotsPkFromSig sov params pkSeed (UInt32.ofNat i)
          (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
            2 ^ params.subtreeHeight))
          (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight)
          (extractBaseWDigits params.w params.ell1
            (productionLayerDigest sov params sigStar.rRand pkSeed
              (derivePublicKey sov params sk0).pkRoot cur i
              (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
                2 ^ params.subtreeHeight))
              (UInt32.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) %
                2 ^ params.subtreeHeight))
              (sigStar.layerSigs.getD i ⟨0, [], []⟩).tswCtr))
          (sigStar.layerSigs.getD i ⟨0, [], []⟩).wotsChains)
        (sigStar.layerSigs.getD i ⟨0, [], []⟩).authPath with
    | none => False.elim (by
        obtain ⟨_, _, _, hW, _⟩ := hInv; rw [hLs, hNextW] at hW; cases hW)
    | some next =>
      have hRest : verifyProductionHypertreeLayers sov params pkSeed
          (derivePublicKey sov params sk0).pkRoot sigStar.rRand (i + 1)
          (sigStar.leafGlobalIdx / 2 ^ ((i + 1) * params.subtreeHeight)) next rest =
          some (computeXmssSubtreeRoot sov params sk0 (UInt32.ofNat (params.numLayers - 1))
            (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (params.numLayers * params.subtreeHeight)))) := by
        obtain ⟨_, _, n', hW, hR⟩ := hInv
        rw [hLs, hNextW] at hW
        rw [← Option.some.inj hW, hStep] at hR; exact hR
      let upper : PSum
          (next = computeXmssSubtreeRoot sov params sk0 (UInt32.ofNat i)
            (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
              2 ^ params.subtreeHeight)))
          (PSum (ExplicitTcrWitness suite pkSeed)
            (ExplicitPreBreak suite sov params sk0 log msgStar sigStar)) :=
        match hR : rest with
        | [] => .inl (by
            have hR' := hRest
            rw [hR, verifyProductionHypertreeLayers_nil] at hR'
            have hEq := Option.some.inj hR'
            have hD : params.numLayers = i + 1 := by
              rw [← hLenEq, hR, List.length_cons, List.length_nil]
            rw [hD, Nat.add_sub_cancel] at hEq
            rw [hStep]; exact hEq)
        | _ :: _ =>
          match explicitHypertreeWalk suite params pkSeed secFn log msgStar sigStar hw hPwf hLeafLt
              hLogValid hCons rest (i + 1) next (by rw [hR]; exact List.cons_ne_nil _ _)
              (fun j => by
                have h := hAlign (j + 1); rw [List.getD_cons_succ] at h
                rw [h, ← Nat.add_assoc, Nat.add_right_comm i j 1])
              (Decidable.byContradiction (fun _ => by
                have hL := hLenEq; rw [List.length_cons] at hL; omega)) hRest with
          | .honest e _ hPos hEq => .inl (by
              rw [hEq]; unfold prodHonestLayerMsg
              simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
              rw [hPos, hStep])
          | .tcr w => .inr (.inl w)
          | .pre h => .inr (.inr h)
      match upper with
      | .inr (.inl w) => .tcr w
      | .inr (.inr h) => .pre h
      | .inl hNext =>
        match prodListSearch
            (fun e : List UInt8 × PqHashSig =>
              e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) =
                sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) ∧
              cur = prodHonestLayerMsg sov params sk0 e i)
            (fun e =>
              if h : e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) =
                  sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) ∧
                cur = prodHonestLayerMsg sov params sk0 e i then .inl h
              else .inr h) log with
        | .inl ⟨e, ⟨he, hP⟩⟩ => .honest e he hP.1 hP.2
        | .inr hNone =>
          match explicitLayerExtract suite params pkSeed secFn log msgStar sigStar hw hPwf hLeafLt
              hLogValid hCons i hi cur (fun e he hP hEq => hNone e he ⟨hP, hEq⟩) hTsw
              (by rw [← hNext]; exact hNextW) with
          | .inl w => .tcr w
          | .inr h => .pre h

theorem prodSigForsIdxs_secOv_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (secFn : Spec.Bytes → Spec.Bytes) (pk : PqPublicKey)
    (msg : List UInt8) (sig : PqHashSig) :
    prodSigForsIdxs (secOverlaySuite suite pkSeed secFn) params pk msg sig =
      prodSigForsIdxs suite params pk msg sig := by
  let sov := secOverlaySuite suite pkSeed secFn
  have hMu : thPreHash sov pk.pkSeed pk.pkRoot msg = thPreHash suite pk.pkSeed pk.pkRoot msg := by
    rw [thPreHash_eq, thPreHash_eq]; exact secOverlaySuite_thCall_cons2 _ _ _ _ _ _ _ _ _
  have hXof : ∀ first n,
      thXofMsgBlocks sov sig.rRand pk.pkSeed pk.pkRoot (thPreHash suite pk.pkSeed pk.pkRoot msg)
        first n =
      thXofMsgBlocks suite sig.rRand pk.pkSeed pk.pkRoot (thPreHash suite pk.pkSeed pk.pkRoot msg)
        first n := by
    intro first n; induction n generalizing first with
    | zero => rw [thXofMsgBlocks_zero, thXofMsgBlocks_zero]
    | succ n' ih =>
      rw [thXofMsgBlocks_succ, thXofMsgBlocks_succ, secOverlaySuite_thCall_cons2, ih (first + 1)]
  unfold prodSigForsIdxs
  rw [hMu, deriveProductionStatelessInputs_eq, deriveProductionStatelessInputs_eq]
  dsimp only
  rw [thXofMsg_eq, thXofMsg_eq, hXof]

theorem prodSigForsLeaves_secOv_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (secFn : Spec.Bytes → Spec.Bytes) (pk : PqPublicKey)
    (msg : List UInt8) (sig : PqHashSig) :
    prodSigForsLeaves (secOverlaySuite suite pkSeed secFn) params pk msg sig =
      prodSigForsLeaves suite params pk msg sig := by
  unfold prodSigForsLeaves
  rw [prodSigForsIdxs_secOv_eq]

/-! ## §2. Unsealed 3-Way Classification Theorem (`execEufCmaIdealPrf_explicit_classify`) -/

/-- **Computable 3-Way Extractor on `ExecEufCmaIdealPrfGame`
    (`execEufCmaIdealPrf_explicit_extract`).**
    Returns an explicit `ExplicitTcrWitness` in `Type` (`PSum.inl`) or a constructive `Prop`
    classification into `ExplicitItsrCover ∨ ExplicitPreBreak` (`PSum.inr`). -/
def execEufCmaIdealPrf_explicit_extract {n qHash qSign : Nat} (latchOn : Bool) (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams) (hw : params.w = 4 ∨ params.w = 16)
    (pkSeedOf : Fin n → List UInt8) (rfMsg rfSec : Fin n → Spec.Bytes → Spec.Bytes)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) (ω : Fin n)
    (hRf : ∀ x, x.length = 65 → (rfMsg ω x).length = 32)
    (hOneTimeIfSt : params.statefulJorts = true → latchOn = true)
    (hWin : (ExecEufCmaIdealPrfGame latchOn hPos suite params pkSeedOf rfMsg rfSec adv).win ω =
      true) :
    let pkSeed := pkSeedOf ω
    let sov := secOverlaySuite suite pkSeed (rfSec ω)
    let sk0 : PqSecretKey := ⟨[], [], pkSeed⟩
    let pk := derivePublicKeyIdealPrf suite params pkSeed (rfSec ω)
    let signFn := signQueryIdealPrf suite params pkSeed (rfMsg ω) (rfSec ω)
    let run := evalLatchedAdaptiveTree latchOn suite.rawHash signFn
      ((canonicalizeAdvOptRand (adv ω)).run pk) 0
    let log := signLogFromOracle signFn run.2
    PSum (ExplicitTcrWitness suite pkSeed)
      (ExplicitItsrCover suite params pk log run.1.1 run.1.2 ∨
       ExplicitPreBreak suite sov params sk0 log run.1.1 run.1.2) := by
  intro pkSeed sov sk0 pk signFn run log
  let fov := fullIdealOverlaySuite suite pkSeed (rfMsg ω) (rfSec ω)
  rw [ExecEufCmaIdealPrfGame_win] at hWin
  have hAcceptSuite : verifyProductionPqHashSig suite params pk run.1.1 run.1.2 = true :=
    (Bool.and_eq_true_iff.mp hWin).1
  have hFreshDec := (Bool.and_eq_true_iff.mp hWin).2
  have hFresh : ∀ e ∈ log, e.1 ≠ run.1.1 := fun e he hEq =>
    of_decide_eq_true hFreshDec (List.mem_map.mpr ⟨e, he, hEq⟩)
  have hPkFov : derivePublicKey fov params sk0 = pk :=
    fullIdealOverlaySuite_derivePublicKey_eq suite params pkSeed (rfMsg ω) (rfSec ω)
  have hPkSov : derivePublicKey sov params sk0 = pk := by
    dsimp only [sov, sk0, pk]; rw [derivePublicKeyIdealPrf.public_eqs]
  have hOptAll : ∀ q ∈ run.2, q.randomness = [] ∨ q.randomness.length = 32 := by
    intro q hq
    dsimp only [run] at hq
    rw [canonicalizeAdvOptRand_run] at hq
    exact evalLatched_canonicalize_log_optRand latchOn suite.rawHash signFn _ 0 q hq
  have hLogFov : productionSigningLog fov params sk0 run.2 = log :=
    fullIdealOverlaySuite_productionSigningLog_eq suite params pkSeed (rfMsg ω) (rfSec ω)
      hRf run.2 hOptAll
  have hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ run.2 → ∀ q', q' ∈ run.2 → q.epoch = q'.epoch → q = q' := fun hSt => by
    have hL := hOneTimeIfSt hSt
    dsimp only [run]
    rw [hL]
    exact evalLatchedAdaptiveTree_oneTime suite.rawHash signFn _ 0
  have hFovSovMsg : ∀ e i, prodHonestLayerMsg fov params sk0 e i =
      prodHonestLayerMsg sov params sk0 e i := fun e i => by
    unfold prodHonestLayerMsg
    rw [hPkFov, hPkSov]
    split
    · split
      · rw [thPreHash_eq, thPreHash_eq]
        exact fullIdealOverlaySuite_role_ne_thCall _ _ _ _ public_roles_ne_tagPrfMsg.2.2.2.2.1 _ _ _
      · rw [computeProductionForsPk_eq, computeProductionForsPk_eq, thTweakTl_eq, thTweakTl_eq,
          fullIdealOverlaySuite_role_ne_thCall _ _ _ _ public_roles_ne_tagPrfMsg.2.2.1]
        congr 1; apply List.map_congr_left; intro j _
        exact fullIdealOverlaySuite_merkleKp_eq suite pkSeed (rfMsg ω) (rfSec ω) pkSeed 0 _
          .forsTree _ _ _ (fun u => by
            rw [forsIndexedLeafFn_eq, forsIndexedLeafFn_eq, forsIndexedLeafHash_eq,
              forsIndexedLeafHash_eq, forsIndexedSecretLeaf_eq, forsIndexedSecretLeaf_eq,
              thSecretPrf_eq, thSecretPrf_eq,
              fullIdealOverlaySuite_role_ne_thCall _ _ _ _ public_roles_ne_tagPrfMsg.1,
              thChainF_eq, thChainF_eq,
              fullIdealOverlaySuite_role_ne_thCall _ _ _ _ public_roles_ne_tagPrfMsg.2.1]) _ _ _
    · rw [computeXmssSubtreeRoot_eq, computeXmssSubtreeRoot_eq,
        ← computeMerkleNodeKp_zero_eq, ← computeMerkleNodeKp_zero_eq]
      exact fullIdealOverlaySuite_merkleKp_eq suite pkSeed (rfMsg ω) (rfSec ω) pkSeed _ _ .tree 0
        _ _ (fullIdealOverlaySuite_wotsPk_eq suite params pkSeed (rfMsg ω) (rfSec ω) sk0 _ _) _ _ _
  have hFovSovDigits : ∀ e i, prodLogLayerDigits fov params sk0 e i =
      prodLogLayerDigits sov params sk0 e i := fun e i => by
    unfold prodLogLayerDigits prodLogLayerDigest
    rw [hPkFov, hPkSov, hFovSovMsg, productionLayerDigest_eq, productionLayerDigest_eq]
    congr 1
    split
    · rw [thHashLeafMsg_eq, thHashLeafMsg_eq]
      exact fullIdealOverlaySuite_role_ne_thCall _ _ _ _ public_roles_ne_tagPrfMsg.2.2.2.2.2 _ _ _
    · exact fullIdealOverlaySuite_thHashInternalNode _ _ _ _ _ _ _ _ _ _ _
  have hLogValid : ∀ e ∈ log, ∀ i < params.numLayers,
      checkTargetSum params.w params.ell1 params.targetSum
        (prodLogLayerDigits sov params sk0 e i) = true := by
    intro e he i hi
    rw [← hFovSovDigits]
    exact prodLogLayerDigits_valid
      (productionSigningLog_entryOk fov params sk0 run.2 e (hLogFov.symm ▸ he)) i hi
  have hConsSov : ProdLogConsistent sov params sk0 log := by
    intro e he e' he' i hi hP
    have hCFov := productionSigningLog_consistent fov params sk0 run.2 hOneTime
      e (hLogFov.symm ▸ he) e' (hLogFov.symm ▸ he') i hi hP
    rw [hFovSovDigits, hFovSovDigits] at hCFov
    exact hCFov
  have hAcceptSov : verifyProductionPqHashSig sov params (derivePublicKey sov params sk0)
      run.1.1 run.1.2 = true := by
    rw [hPkSov, secOverlaySuite_verify_eq]; exact hAcceptSuite
  cases hSt : params.statefulJorts
  · have hFacts := prod_stateless_accept_facts sov params sk0 run.1.1 run.1.2 hSt hAcceptSov
    have hPwf : params.productionWellFormed = true := hFacts.1
    have hLen : run.1.2.layerSigs.length = params.numLayers := hFacts.2.1
    have hLeafLt : run.1.2.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight) :=
      hFacts.2.2.1
    have hILen : (prodSigForsIdxs sov params (derivePublicKey sov params sk0)
        run.1.1 run.1.2).length = params.forsTrees := hFacts.2.2.2.1
    have hIBnd : ∀ u ∈ prodSigForsIdxs sov params (derivePublicKey sov params sk0)
        run.1.1 run.1.2, u < 2 ^ params.forsHeight := hFacts.2.2.2.2.1
    have hTrees := (params.productionWellFormed_stateless_fors hPwf hSt).1
    have hNe : run.1.2.layerSigs ≠ [] := fun hnil => by
      have hDPos := (params.productionWellFormed_facts hPwf).1
      rw [hnil, List.length_nil] at hLen; omega
    have h0 : run.1.2.leafGlobalIdx / 2 ^ (0 * params.subtreeHeight) = run.1.2.leafGlobalIdx := by
      simp only [Nat.zero_mul, Nat.pow_zero, Nat.div_one]
    have hTop : (derivePublicKey sov params sk0).pkRoot =
        computeXmssSubtreeRoot sov params sk0 (UInt32.ofNat (params.numLayers - 1))
          (UInt64.ofNat (run.1.2.leafGlobalIdx / 2 ^ (params.numLayers * params.subtreeHeight))) := by
      rw [Nat.div_eq_of_lt hLeafLt]; rfl
    cases hFors : recoverProductionForsPk sov params pkSeed
        (UInt64.ofNat (run.1.2.leafGlobalIdx / 2 ^ params.subtreeHeight))
        (run.1.2.leafGlobalIdx % 2 ^ params.subtreeHeight)
        (prodSigForsIdxs sov params (derivePublicKey sov params sk0) run.1.1 run.1.2)
        run.1.2.forsOpenings with
    | none =>
      exact False.elim (by
        obtain ⟨_, _, _, _, _, _, hF0, _⟩ := hFacts
        change recoverProductionForsPk sov params pkSeed _ _ _ _ = _ at hF0
        rw [hFors] at hF0; cases hF0)
    | some forsPkF =>
      have hHt : verifyProductionHypertreeLayers sov params pkSeed
          (derivePublicKey sov params sk0).pkRoot run.1.2.rRand 0 run.1.2.leafGlobalIdx
          forsPkF run.1.2.layerSigs = some (derivePublicKey sov params sk0).pkRoot := by
        obtain ⟨_, _, _, _, _, fp, hF0, hH0⟩ := hFacts
        change recoverProductionForsPk sov params pkSeed _ _ _ _ = some fp at hF0
        rw [hFors] at hF0; injection hF0 with hEqFp; subst hEqFp; exact hH0
      match explicitHypertreeWalk suite params pkSeed (rfSec ω) log run.1.1 run.1.2 hw hPwf hLeafLt
          hLogValid hConsSov run.1.2.layerSigs 0 forsPkF hNe (fun j => by rw [Nat.zero_add])
          (by rw [Nat.zero_add]; exact hLen) (by rw [h0, ← hTop]; exact hHt) with
      | .tcr w => exact .inl w
      | .pre h => exact .inr (.inr h)
      | .honest e _ hPos hEq =>
        have hL : e.2.leafGlobalIdx = run.1.2.leafGlobalIdx := by
          simpa only [Nat.zero_mul, Nat.pow_zero, Nat.div_one] using hPos
        have hForsEq : forsPkF = computeProductionForsPk sov params sk0
            (UInt64.ofNat (run.1.2.leafGlobalIdx / 2 ^ params.subtreeHeight))
            (run.1.2.leafGlobalIdx % 2 ^ params.subtreeHeight) := by
          rw [hEq]; unfold prodHonestLayerMsg
          simp only [hSt, ↓reduceIte, Bool.false_eq_true, hL]; rfl
        cases hRoots : recoverProductionForsTreeRoots sov params pkSeed
            (UInt64.ofNat (run.1.2.leafGlobalIdx / 2 ^ params.subtreeHeight))
            (run.1.2.leafGlobalIdx % 2 ^ params.subtreeHeight)
            (prodSigForsIdxs sov params (derivePublicKey sov params sk0) run.1.1 run.1.2)
            run.1.2.forsOpenings 0 params.forsTrees with
        | none =>
          exact False.elim (by
            rw [hForsEq] at hFors
            obtain ⟨_, hR0, _⟩ :=
              prod_recoverForsPk_some_inv sov params pkSeed _ _ _ run.1.2.forsOpenings _ hFors
            rw [hRoots] at hR0; cases hR0)
        | some rootsF =>
          have hPkTl : computeProductionForsPk sov params sk0
              (UInt64.ofNat (run.1.2.leafGlobalIdx / 2 ^ params.subtreeHeight))
              (run.1.2.leafGlobalIdx % 2 ^ params.subtreeHeight) =
              thTweakTl sov pkSeed
                ⟨0, UInt64.ofNat (run.1.2.leafGlobalIdx / 2 ^ params.subtreeHeight), .forsRoots,
                 UInt32.ofNat (run.1.2.leafGlobalIdx % 2 ^ params.subtreeHeight), 0, 0⟩ rootsF := by
            rw [hForsEq] at hFors
            obtain ⟨r0, hR0, hTl0⟩ :=
              prod_recoverForsPk_some_inv sov params pkSeed _ _ _ run.1.2.forsOpenings _ hFors
            rw [hRoots] at hR0; injection hR0 with hEqR; subst hEqR; exact hTl0
          rw [computeProductionForsPk_eq] at hPkTl; dsimp only at hPkTl
          rw [thTweakTl_eq, thTweakTl_eq] at hPkTl
          match prodThCallSplit sov hPkTl.symm with
          | .inr ⟨hNe', hHash⟩ =>
            exact .inl (mkMultiRoleCollision suite pkSeed (rfSec ω) tagThTl _ _ _
              tagThF_ne_tagPrf.2 (fun hE => hNe' (congrArg _ hE)) hHash)
          | .inl hArgs =>
            let idxsSov := prodSigForsIdxs sov params (derivePublicKey sov params sk0) run.1.1 run.1.2
            have hIdxsBnd : ∀ J, J < params.forsTrees → idxsSov.getD J 0 < 2 ^ params.forsHeight :=
              fun J hJ => by
                have hJL : J < idxsSov.length := by rw [hILen]; exact hJ
                rw [list_getD_eq_getElem idxsSov 0 hJL]
                exact hIBnd _ (List.getElem_mem hJL)
            have hThHNe : tagThH ≠ tagPrf := by
              simp only [tagThH.public_eqs, tagPrf.public_eqs]; decide +kernel
            match prodForsRootsExtract sov params sk0 _ _ _ run.1.2.forsOpenings
                (ExplicitTcrWitness suite pkSeed)
                (fun j h d b x y _ _ _ _ hNe' hHash =>
                  mkMultiRoleCollision suite pkSeed (rfSec ω) tagThH
                    ⟨0, _, .forsTree, _, UInt32.ofNat (h + 1), UInt32.ofNat (j * 2 ^ d + b)⟩
                    [x, y] _ hThHNe (fun hE => hNe' (congrArg _ hE)) hHash)
                hIdxsBnd params.forsTrees 0 rootsF
                (Decidable.byContradiction (fun _ => by omega)) hRoots
                (by rw [hArgs]; apply List.map_congr_left; intro off _; rw [Nat.zero_add]) with
            | .inr w => exact .inl w
            | .inl hAll =>
              refine .inr ?_
              let idxsSuite := prodSigForsIdxs suite params pk run.1.1 run.1.2
              have hIdxsEq : idxsSov = idxsSuite := by
                dsimp only [idxsSov, idxsSuite]
                rw [hPkSov, prodSigForsIdxs_secOv_eq]
              have hSearch := prodBoundedSearch
                (fun j => ∀ e' ∈ log,
                  (run.1.2.leafGlobalIdx, j, idxsSuite.getD j 0) ∉
                    prodSigForsLeaves suite params pk e'.1 e'.2)
                (fun j =>
                  match prodListSearch
                      (fun e' => (run.1.2.leafGlobalIdx, j, idxsSuite.getD j 0) ∈
                        prodSigForsLeaves suite params pk e'.1 e'.2)
                      (fun e' =>
                        if hm : (run.1.2.leafGlobalIdx, j, idxsSuite.getD j 0) ∈
                            prodSigForsLeaves suite params pk e'.1 e'.2 then .inl hm
                        else .inr hm) log with
                  | .inl ⟨e', he', hm⟩ => .inr (fun hAllNot => hAllNot e' he' hm)
                  | .inr hNone => .inl hNone)
                params.forsTrees
              rcases hSearch with ⟨j, hj, hUn⟩ | hEvery
              · refine .inr ?_
                have hLeafJ := hAll j hj
                rw [Nat.zero_add, hIdxsEq] at hLeafJ
                have hIdxLtJ : idxsSuite.getD j 0 < 2 ^ params.forsHeight := by
                  rw [← hIdxsEq]; exact hIdxsBnd j hj
                have hHashSuite : forsIndexedLeafHash sov pkSeed
                    (UInt64.ofNat (run.1.2.leafGlobalIdx / 2 ^ params.subtreeHeight))
                    (run.1.2.leafGlobalIdx % 2 ^ params.subtreeHeight) j (idxsSuite.getD j 0)
                    (run.1.2.forsOpenings.getD j ⟨[], []⟩).secretVal =
                  forsIndexedLeafHash suite pkSeed
                    (UInt64.ofNat (run.1.2.leafGlobalIdx / 2 ^ params.subtreeHeight))
                    (run.1.2.leafGlobalIdx % 2 ^ params.subtreeHeight) j (idxsSuite.getD j 0)
                    (run.1.2.forsOpenings.getD j ⟨[], []⟩).secretVal := by
                  rw [forsIndexedLeafHash_eq, forsIndexedLeafHash_eq, thChainF_eq, thChainF_eq,
                    secOverlaySuite_nonPrf_thCall _ _ _ tagThF_ne_tagPrf.1]
                rw [hHashSuite] at hLeafJ
                refine .fors j hj hSt hLeafLt (by rw [hPkSov]; exact hIdxLtJ)
                  (fun e' he' => by rw [hPkSov]; exact hUn e' he') (by rw [hPkSov]; exact hLeafJ)
              · refine .inl ⟨hAcceptSuite, hSt, hTrees, hFresh, fun a ha => ?_⟩
                unfold prodSigForsLeaves at ha
                obtain ⟨j, hjR, rfl⟩ := List.mem_map.mp ha
                have hj := List.mem_range.mp hjR
                match prodListSearch
                    (fun e' => (run.1.2.leafGlobalIdx, j, idxsSuite.getD j 0) ∈
                      prodSigForsLeaves suite params pk e'.1 e'.2)
                    (fun e' =>
                      if hm : (run.1.2.leafGlobalIdx, j, idxsSuite.getD j 0) ∈
                          prodSigForsLeaves suite params pk e'.1 e'.2 then .inl hm
                      else .inr hm) log with
                | .inl ⟨e', he', hm⟩ => exact ⟨e', he', hm⟩
                | .inr hNone => exact absurd hNone (hEvery j hj)
  · have hInv := verifyProductionPqHashSig_stateful_inv sov params _ run.1.1 run.1.2 hSt hAcceptSov
    have hPwf : params.productionWellFormed = true := hInv.1
    have hLen : run.1.2.layerSigs.length = params.numLayers := hInv.2.1
    have hLeafLt : run.1.2.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight) :=
      hInv.2.2.1
    have hHt := hInv.2.2.2
    have hNe : run.1.2.layerSigs ≠ [] := fun hnil => by
      have hDPos := (params.productionWellFormed_facts hPwf).1
      rw [hnil, List.length_nil] at hLen; omega
    have h0 : run.1.2.leafGlobalIdx / 2 ^ (0 * params.subtreeHeight) = run.1.2.leafGlobalIdx := by
      simp only [Nat.zero_mul, Nat.pow_zero, Nat.div_one]
    have hTop : (derivePublicKey sov params sk0).pkRoot =
        computeXmssSubtreeRoot sov params sk0 (UInt32.ofNat (params.numLayers - 1))
          (UInt64.ofNat (run.1.2.leafGlobalIdx / 2 ^ (params.numLayers * params.subtreeHeight))) := by
      rw [Nat.div_eq_of_lt hLeafLt]; rfl
    match explicitHypertreeWalk suite params pkSeed (rfSec ω) log run.1.1 run.1.2 hw hPwf hLeafLt
        hLogValid hConsSov run.1.2.layerSigs 0
        (thPreHash sov pkSeed (derivePublicKey sov params sk0).pkRoot run.1.1) hNe
        (fun j => by rw [Nat.zero_add]) (by rw [Nat.zero_add]; exact hLen)
        (by rw [h0, ← hTop]; exact hHt) with
    | .tcr w => exact .inl w
    | .pre h => exact .inr (.inr h)
    | .honest e he _ hEq =>
      have hMu : thCall sov tagHPre pkSeed zeroAdrs [(derivePublicKey sov params sk0).pkRoot, run.1.1] =
          thCall sov tagHPre pkSeed zeroAdrs [(derivePublicKey sov params sk0).pkRoot, e.1] := by
        unfold prodHonestLayerMsg at hEq
        simp only [hSt, ↓reduceIte] at hEq
        rw [thPreHash_eq, thPreHash_eq] at hEq; exact hEq
      have hHPreNe : tagHPre ≠ tagPrf := by
        simp only [tagHPre.public_eqs, tagPrf.public_eqs]; decide +kernel
      match prodThCallSplit sov hMu with
      | .inl hArgs =>
        exact False.elim (by
          simp only [List.cons.injEq, and_true] at hArgs
          exact hFresh e he hArgs.2.symm)
      | .inr ⟨hNe', hHash⟩ =>
        exact .inl (mkMultiRoleCollision suite pkSeed (rfSec ω) tagHPre zeroAdrs _ _ hHPreNe
          (fun hE => hNe' (congrArg _ hE)) hHash)

/-- **Unsealed 3-Way Classification on `ExecEufCmaIdealPrfGame`
    (`execEufCmaIdealPrf_explicit_classify`).** -/
theorem execEufCmaIdealPrf_explicit_classify {n qHash qSign : Nat} (latchOn : Bool) (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams) (hw : params.w = 4 ∨ params.w = 16)
    (pkSeedOf : Fin n → List UInt8) (rfMsg rfSec : Fin n → Spec.Bytes → Spec.Bytes)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) (ω : Fin n)
    (hRf : ∀ x, x.length = 65 → (rfMsg ω x).length = 32)
    (hOneTimeIfSt : params.statefulJorts = true → latchOn = true)
    (hWin : (ExecEufCmaIdealPrfGame latchOn hPos suite params pkSeedOf rfMsg rfSec adv).win ω =
      true) :
    let pkSeed := pkSeedOf ω
    let sov := secOverlaySuite suite pkSeed (rfSec ω)
    let sk0 : PqSecretKey := ⟨[], [], pkSeed⟩
    let pk := derivePublicKeyIdealPrf suite params pkSeed (rfSec ω)
    let signFn := signQueryIdealPrf suite params pkSeed (rfMsg ω) (rfSec ω)
    let run := evalLatchedAdaptiveTree latchOn suite.rawHash signFn
      ((canonicalizeAdvOptRand (adv ω)).run pk) 0
    let log := signLogFromOracle signFn run.2
    ExplicitItsrCover suite params pk log run.1.1 run.1.2 ∨
    Nonempty (ExplicitTcrWitness suite pkSeed) ∨
    ExplicitPreBreak suite sov params sk0 log run.1.1 run.1.2 :=
  match execEufCmaIdealPrf_explicit_extract latchOn hPos suite params hw pkSeedOf rfMsg rfSec adv ω
      hRf hOneTimeIfSt hWin with
  | .inl w => .inr (.inl ⟨w⟩)
  | .inr (.inl h) => .inl h
  | .inr (.inr h) => .inr (.inr h)

/-- Total computable `Option (ExplicitTcrWitness suite pkSeed)` extractor on single-instance
    `(pkSeed, rfMsg, secFn, A)` runs of `ExecEufCmaIdealPrfGame`. -/
def extractIdealPrfTcrWitnessOpt {qHash qSign : Nat} (latchOn : Bool)
    (suite : TweakableHashSuite) (params : PqHashParams) (hw : params.w = 4 ∨ params.w = 16)
    (pkSeed : List UInt8) (rfMsg secFn : Spec.Bytes → Spec.Bytes)
    (hRf : ∀ x, x.length = 65 → (rfMsg x).length = 32)
    (hOneTimeIfSt : params.statefulJorts = true → latchOn = true)
    (A : SeedWithheldEufCmaAdv qHash qSign) : Option (ExplicitTcrWitness suite pkSeed) :=
  if hW : (ExecEufCmaIdealPrfGame latchOn Nat.one_pos suite params (fun _ => pkSeed)
      (fun _ => rfMsg) (fun _ => secFn) (fun _ => A)).win ⟨0, Nat.one_pos⟩ = true then
    match execEufCmaIdealPrf_explicit_extract latchOn Nat.one_pos suite params hw
        (fun _ => pkSeed) (fun _ => rfMsg) (fun _ => secFn) (fun _ => A) ⟨0, Nat.one_pos⟩
        hRf hOneTimeIfSt hW with
    | .inl w => some w
    | .inr _ => none
  else none

/-- Every winning coin `ω` of `ExecEufCmaIdealPrfGame` constructively satisfies `ExplicitItsrCover`,
    causes `extractIdealPrfTcrWitnessOpt` to return `some w`, or satisfies `ExplicitPreBreak`. -/
theorem execEufCmaIdealPrf_explicit_classify_opt {n qHash qSign : Nat} (latchOn : Bool)
    (hPos : 0 < n) (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16)
    (pkSeedOf : Fin n → List UInt8) (rfMsg rfSec : Fin n → Spec.Bytes → Spec.Bytes)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) (ω : Fin n)
    (hRf : ∀ x, x.length = 65 → (rfMsg ω x).length = 32)
    (hOneTimeIfSt : params.statefulJorts = true → latchOn = true)
    (hWin : (ExecEufCmaIdealPrfGame latchOn hPos suite params pkSeedOf rfMsg rfSec adv).win ω =
      true) :
    let pkSeed := pkSeedOf ω
    let sov := secOverlaySuite suite pkSeed (rfSec ω)
    let sk0 : PqSecretKey := ⟨[], [], pkSeed⟩
    let pk := derivePublicKeyIdealPrf suite params pkSeed (rfSec ω)
    let signFn := signQueryIdealPrf suite params pkSeed (rfMsg ω) (rfSec ω)
    let run := evalLatchedAdaptiveTree latchOn suite.rawHash signFn
      ((canonicalizeAdvOptRand (adv ω)).run pk) 0
    let log := signLogFromOracle signFn run.2
    ExplicitItsrCover suite params pk log run.1.1 run.1.2 ∨
    (∃ w, extractIdealPrfTcrWitnessOpt latchOn suite params hw pkSeed (rfMsg ω) (rfSec ω)
      hRf hOneTimeIfSt (adv ω) = some w) ∨
    ExplicitPreBreak suite sov params sk0 log run.1.1 run.1.2 := by
  intro pkSeed sov sk0 pk signFn run log
  have hW1 : (ExecEufCmaIdealPrfGame latchOn Nat.one_pos suite params (fun _ => pkSeed)
      (fun _ => rfMsg ω) (fun _ => rfSec ω) (fun _ => adv ω)).win ⟨0, Nat.one_pos⟩ = true := by
    rw [ExecEufCmaIdealPrfGame_win]
    rw [ExecEufCmaIdealPrfGame_win] at hWin
    exact hWin
  unfold extractIdealPrfTcrWitnessOpt
  rw [dite_eq_left hW1]
  match hEx : execEufCmaIdealPrf_explicit_extract latchOn Nat.one_pos suite params hw
      (fun _ => pkSeed) (fun _ => rfMsg ω) (fun _ => rfSec ω) (fun _ => adv ω) ⟨0, Nat.one_pos⟩
      hRf hOneTimeIfSt hW1 with
  | .inl w => exact .inr (.inl ⟨w, rfl⟩)
  | .inr (.inl hI) => exact .inl hI
  | .inr (.inr hP) => exact .inr (.inr hP)

/-- `#tooth` Stateful `Jorts` (`statefulJorts = true`) never admits an `ExplicitItsrCover`. -/
theorem tooth_stateful_no_explicitItsrCover (suite : TweakableHashSuite) (params : PqHashParams)
    (hSt : params.statefulJorts = true) (pk : PqPublicKey)
    (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8) (sigStar : PqHashSig) :
    ¬ ExplicitItsrCover suite params pk log msgStar sigStar :=
  fun h => Bool.noConfusion (h.stateless.symm.trans hSt)

#verify_constructive
  Qsag.honestChainNode_secOv_succ
  Qsag.prodSigForsIdxs_secOv_eq
  Qsag.prodSigForsLeaves_secOv_eq
  Qsag.execEufCmaIdealPrf_explicit_classify
  Qsag.execEufCmaIdealPrf_explicit_classify_opt
  Qsag.tooth_stateful_no_explicitItsrCover

#tooth_pair Qsag.execEufCmaIdealPrf_explicit_classify vs Qsag.tooth_stateful_no_explicitItsrCover

theorem extractIdealPrfTcrWitnessOpt_lost {qHash qSign : Nat} (latchOn : Bool)
    (suite : TweakableHashSuite) (params : PqHashParams) (hw : params.w = 4 ∨ params.w = 16)
    (pkSeed : List UInt8) (rfMsg secFn : Spec.Bytes → Spec.Bytes)
    (hRf : ∀ x, x.length = 65 → (rfMsg x).length = 32)
    (hOneTimeIfSt : params.statefulJorts = true → latchOn = true)
    (A : SeedWithheldEufCmaAdv qHash qSign) (lost : (ExecEufCmaIdealPrfGame latchOn Nat.one_pos suite params (fun _ => pkSeed)
      (fun _ => rfMsg) (fun _ => secFn) (fun _ => A)).win ⟨0, Nat.one_pos⟩ = false) :
    extractIdealPrfTcrWitnessOpt latchOn suite params hw pkSeed rfMsg secFn hRf hOneTimeIfSt A = none := by
  unfold extractIdealPrfTcrWitnessOpt
  exact dite_eq_right (fun won => Bool.noConfusion (lost.symm.trans won))

#verify_constructive extractIdealPrfTcrWitnessOpt_lost

end Qsag
end

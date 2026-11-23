module
/-
# Qsag.Protocol.Signing.HulsingFullOverlay — Full Signer-Idealized Overlay & Unified 3-Arg Tweakable Hash

Provides the constructive overlay and 3-argument tweakable hash adapter connecting Hop 2
(`ExecEufCmaIdealPrfGame`) to Hop 4 (`HulsingMultiHopReduction`) and concrete production parameter
bounds (`ProductionParamRefinement` / `ProductionJortsBaggyBounds`):

1. **Full Signer-Idealized Overlay (`fullIdealOverlaySuite`):**
   Routes signer-internal `tagPrfMsg` (`skPrf = []`) and `tagPrf` (`skSeed = []`) calls to `rfMsg`
   and `secFn` while leaving all public tweakable-hash roles (`tagThF`, `tagThTl`, `tagThH`,
   `tagHPre`, `tagHMsg`, `tagHInternal`, `tagHXof`) and `verifyProductionPqHashSig` identical to
   `suite`, discharging `execEufCmaIdealPrf_extract_complete` from `prodPublicExtract_complete` for
   arbitrary `pkSeed`.
2. **Unified 3-Argument Tweakable Hash Adapter (`suiteTweakHash`):**
   Injectively encodes `tagThF` chain/leaf calls, multi-frame `tagThH`/`tagThTl`/`tagHPre` calls,
   and `productionLayerDigest` calls into `(seed, tweak, msg)` for `Spec.smDtTcrGame`,
   `Spec.smDtPreGame`, and `SmDtUdHard`.
-/

public import Qsag.Protocol.Signing.HulsingPrfUdHops
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-! ## §1. Full Signer-Idealized Overlay Suite (`fullIdealOverlaySuite`) -/

/-- Signer-internal overlay intercepting both `tagPrfMsg` (`seed = []`, `skPrf = []`,
    `adrs = zeroAdrs`, `optRand = [] ∨ optRand.length = 32`, `mu.length = 32`) and `tagPrf`
    (`secOverlaySuite`), delegating all public hash calls to `suite.rawHash`. -/
def fullIdealOverlaySuite (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (rfMsg secFn : Spec.Bytes → Spec.Bytes) : TweakableHashSuite where
  suiteId := suite.suiteId
  rawHash raw :=
    match parseThPreimage raw with
    | some (role, seed, adrs, [a0, optRand, mu]) =>
      if role = tagPrfMsg ∧ seed = [] ∧ adrs = zeroAdrs ∧ a0 = [] ∧
          (optRand = [] ∨ optRand.length = 32) ∧ mu.length = 32 then
        padBytes32 (rfMsg (encodePrfMsg65 optRand mu))
      else (secOverlaySuite suite pkSeed secFn).rawHash raw
    | _ => (secOverlaySuite suite pkSeed secFn).rawHash raw
  rawHash_len raw := by
    split
    · split
      · exact padBytes32_length _
      · exact (secOverlaySuite suite pkSeed secFn).rawHash_len raw
    · exact (secOverlaySuite suite pkSeed secFn).rawHash_len raw

theorem public_roles_ne_tagPrfMsg :
    tagPrf ≠ tagPrfMsg ∧ tagThF ≠ tagPrfMsg ∧ tagThTl ≠ tagPrfMsg ∧
    tagThH ≠ tagPrfMsg ∧ tagHPre ≠ tagPrfMsg ∧ tagHMsg ≠ tagPrfMsg := by
  simp only [tagPrf.public_eqs, tagThF.public_eqs, tagThTl.public_eqs,
    tagThH.public_eqs, tagHPre.public_eqs, tagHMsg.public_eqs, tagPrfMsg.public_eqs]
  decide +kernel

theorem fullIdealOverlaySuite_thPrfMsg_empty (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (rfMsg secFn : Spec.Bytes → Spec.Bytes) {optRand mu : List UInt8}
    (hOpt : optRand = [] ∨ optRand.length = 32) (hMu : mu.length = 32) :
    thPrfMsg (fullIdealOverlaySuite suite pkSeed rfMsg secFn) [] optRand mu =
      padBytes32 (rfMsg (encodePrfMsg65 optRand mu)) := by
  rw [thPrfMsg_eq, thCall_eq]
  unfold fullIdealOverlaySuite
  dsimp only
  rw [parseThPreimage_thPreimage]
  have hc : tagPrfMsg = tagPrfMsg ∧ ([] : List UInt8) = [] ∧ zeroAdrs = zeroAdrs ∧
      ([] : List UInt8) = [] ∧ (optRand = [] ∨ optRand.length = 32) ∧ mu.length = 32 :=
    ⟨rfl, rfl, rfl, rfl, hOpt, hMu⟩
  exact ite_eq_left hc

theorem fullIdealOverlaySuite_role_ne_thCall (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (rfMsg secFn : Spec.Bytes → Spec.Bytes) {role : List UInt8} (hNe : role ≠ tagPrfMsg)
    (seed : List UInt8) (adrs : HashAdrs) (args : List (List UInt8)) :
    thCall (fullIdealOverlaySuite suite pkSeed rfMsg secFn) role seed adrs args =
      thCall (secOverlaySuite suite pkSeed secFn) role seed adrs args := by
  rw [thCall_eq, thCall_eq]
  unfold fullIdealOverlaySuite
  dsimp only
  rw [parseThPreimage_thPreimage]
  rcases args with _ | ⟨a0, _ | ⟨o, _ | ⟨m, _ | ⟨_, _⟩⟩⟩⟩
  · rfl
  · rfl
  · rfl
  · simp only [hNe, false_and, ↓reduceIte]
  · rfl

theorem fullIdealOverlaySuite_thCall_non3 (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (rfMsg secFn : Spec.Bytes → Spec.Bytes) (role seed : List UInt8) (adrs : HashAdrs)
    {args : List (List UInt8)} (hLen : args.length ≠ 3) :
    thCall (fullIdealOverlaySuite suite pkSeed rfMsg secFn) role seed adrs args =
      thCall (secOverlaySuite suite pkSeed secFn) role seed adrs args := by
  rw [thCall_eq, thCall_eq]
  unfold fullIdealOverlaySuite
  dsimp only
  rw [parseThPreimage_thPreimage]
  rcases args with _ | ⟨a0, _ | ⟨o, _ | ⟨m, _ | ⟨_, _⟩⟩⟩⟩
  · rfl
  · rfl
  · rfl
  · exact absurd rfl hLen
  · rfl

theorem fullIdealOverlaySuite_thHashInternalNode (suite : TweakableHashSuite)
    (pkSeed : List UInt8) (rfMsg secFn : Spec.Bytes → Spec.Bytes)
    (s pR cur : List UInt8) (lU : UInt32) (tI : UInt64) (kpI : UInt32) (ctr : Nat) :
    thHashInternalNode (fullIdealOverlaySuite suite pkSeed rfMsg secFn) s pR cur lU tI kpI ctr =
      thHashInternalNode (secOverlaySuite suite pkSeed secFn) s pR cur lU tI kpI ctr := by
  rw [thHashInternalNode_eq, thHashInternalNode_eq, thCall_eq, thCall_eq]
  unfold fullIdealOverlaySuite
  dsimp only
  rw [parseThPreimage_thPreimage]
  have hBe : (be 4 ctr).length ≠ 32 := by rw [length_be]; decide
  simp only [hBe, and_false, ↓reduceIte]

theorem fullIdealOverlaySuite_wotsSteps_eq (suite : TweakableHashSuite)
    (pkSeed : List UInt8) (rfMsg secFn : Spec.Bytes → Spec.Bytes) (s : List UInt8)
    (l : UInt32) (t : UInt64) (kp r : Nat) :
    ∀ k st x,
      wotsChainSteps (fullIdealOverlaySuite suite pkSeed rfMsg secFn) s l t kp r st k x =
      wotsChainSteps (secOverlaySuite suite pkSeed secFn) s l t kp r st k x
  | 0, _, _ => by rw [wotsChainSteps_zero, wotsChainSteps_zero]
  | k + 1, st, x => by
    rw [wotsChainSteps_succ, wotsChainSteps_succ]
    dsimp only
    rw [thChainF_eq, thChainF_eq,
      fullIdealOverlaySuite_role_ne_thCall _ _ _ _ public_roles_ne_tagPrfMsg.2.1]
    exact fullIdealOverlaySuite_wotsSteps_eq suite pkSeed rfMsg secFn s l t kp r k (st + 1) _

theorem fullIdealOverlaySuite_merkleKp_eq (suite : TweakableHashSuite)
    (pkSeed : List UInt8) (rfMsg secFn : Spec.Bytes → Spec.Bytes) (s : List UInt8)
    (l : UInt32) (t : UInt64) (kind : AdrsKind) (kp : UInt32)
    (f g : Nat → List UInt8) (hfg : ∀ i, f i = g i) :
    ∀ ht n loc,
      computeMerkleNodeKp (fullIdealOverlaySuite suite pkSeed rfMsg secFn) s l t kind kp f ht n loc =
      computeMerkleNodeKp (secOverlaySuite suite pkSeed secFn) s l t kind kp g ht n loc
  | 0, _, loc => by rw [computeMerkleNodeKp_zero, computeMerkleNodeKp_zero]; exact hfg loc
  | ht + 1, n, loc => by
    rw [computeMerkleNodeKp_succ, computeMerkleNodeKp_succ, thNodeH_eq, thNodeH_eq,
      fullIdealOverlaySuite_role_ne_thCall _ _ _ _ public_roles_ne_tagPrfMsg.2.2.2.1,
      fullIdealOverlaySuite_merkleKp_eq suite pkSeed rfMsg secFn s l t kind kp f g hfg ht _ _,
      fullIdealOverlaySuite_merkleKp_eq suite pkSeed rfMsg secFn s l t kind kp f g hfg ht _ _]

private theorem fullIdealOverlaySuite_authPathKp_eq (suite : TweakableHashSuite)
    (pkSeed : List UInt8) (rfMsg secFn : Spec.Bytes → Spec.Bytes) (s : List UInt8)
    (l : UInt32) (t : UInt64) (kind : AdrsKind) (kp : UInt32)
    (f g : Nat → List UInt8) (hfg : ∀ i, f i = g i) :
    ∀ ht root locBase locIdx,
      buildMerkleAuthPathKp (fullIdealOverlaySuite suite pkSeed rfMsg secFn) s l t kind kp f ht root
        locBase locIdx =
      buildMerkleAuthPathKp (secOverlaySuite suite pkSeed secFn) s l t kind kp g ht root locBase
        locIdx
  | 0, _, _, _ => by rw [buildMerkleAuthPathKp.public_eq_1, buildMerkleAuthPathKp.public_eq_1]
  | ht + 1, root, locBase, locIdx => by
    rw [buildMerkleAuthPathKp.public_eq_2, buildMerkleAuthPathKp.public_eq_2]
    dsimp only
    split <;>
      rw [fullIdealOverlaySuite_merkleKp_eq suite pkSeed rfMsg secFn s l t kind kp f g hfg ht _ _,
        fullIdealOverlaySuite_authPathKp_eq suite pkSeed rfMsg secFn s l t kind kp f g hfg ht _ _ _]

theorem fullIdealOverlaySuite_wotsPk_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (rfMsg secFn : Spec.Bytes → Spec.Bytes) (sk : PqSecretKey)
    (l : UInt32) (t : UInt64) (kp : Nat) :
    computeWotsPk (fullIdealOverlaySuite suite pkSeed rfMsg secFn) params sk l t kp =
      computeWotsPk (secOverlaySuite suite pkSeed secFn) params sk l t kp := by
  rw [computeWotsPk_eq, computeWotsPk_eq, thTweakTl_eq, thTweakTl_eq,
    fullIdealOverlaySuite_role_ne_thCall _ _ _ _ public_roles_ne_tagPrfMsg.2.2.1]
  congr 1; apply List.map_congr_left; intro r _
  rw [wotsSecretBase_eq, wotsSecretBase_eq, thSecretPrf_eq, thSecretPrf_eq,
    fullIdealOverlaySuite_role_ne_thCall _ _ _ _ public_roles_ne_tagPrfMsg.1,
    fullIdealOverlaySuite_wotsSteps_eq]

theorem fullIdealOverlaySuite_verify_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (rfMsg secFn : Spec.Bytes → Spec.Bytes)
    (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig) :
    verifyProductionPqHashSig (fullIdealOverlaySuite suite pkSeed rfMsg secFn) params pk msg sig =
      verifyProductionPqHashSig suite params pk msg sig := by
  let fov := fullIdealOverlaySuite suite pkSeed rfMsg secFn
  let sov := secOverlaySuite suite pkSeed secFn
  suffices verifyProductionPqHashSig fov params pk msg sig =
      verifyProductionPqHashSig sov params pk msg sig from
    this.trans (secOverlaySuite_verify_eq suite params pkSeed secFn pk msg sig)
  have hWalkKp : ∀ s l t kind kp ht root loc leaf path,
      walkMerkleAuthPathKp fov s l t kind kp ht root loc leaf path =
      walkMerkleAuthPathKp sov s l t kind kp ht root loc leaf path := by
    intro s l t kind kp ht; induction ht with
    | zero => intro root loc leaf path; cases path <;> rfl
    | succ ht' ih =>
      intro root loc leaf path; cases path with
      | nil => rfl
      | cons sib rest =>
        unfold walkMerkleAuthPathKp; dsimp only
        if hHalf : loc < 2 ^ ht' then
          rw [ite_eq_left hHalf, ite_eq_left hHalf, ih]
          cases walkMerkleAuthPathKp sov s l t kind kp ht' (2 * root) loc leaf rest with
          | none => rfl
          | some _ =>
            dsimp only; rw [thNodeH_eq, thNodeH_eq]
            exact congrArg some (fullIdealOverlaySuite_role_ne_thCall _ _ _ _
              public_roles_ne_tagPrfMsg.2.2.2.1 _ _ _)
        else
          rw [ite_eq_right hHalf, ite_eq_right hHalf, ih]
          cases walkMerkleAuthPathKp sov s l t kind kp ht' (2 * root + 1) (loc - 2 ^ ht') leaf rest with
          | none => rfl
          | some _ =>
            dsimp only; rw [thNodeH_eq, thNodeH_eq]
            exact congrArg some (fullIdealOverlaySuite_role_ne_thCall _ _ _ _
              public_roles_ne_tagPrfMsg.2.2.2.1 _ _ _)
  have hRecWots : ∀ s l t kp digs chs,
      recoverWotsPkFromSig fov params s l t kp digs chs =
      recoverWotsPkFromSig sov params s l t kp digs chs := by
    intro s l t kp digs chs
    rw [recoverWotsPkFromSig_eq, recoverWotsPkFromSig_eq, thTweakTl_eq, thTweakTl_eq,
      fullIdealOverlaySuite_role_ne_thCall _ _ _ _ public_roles_ne_tagPrfMsg.2.2.1,
      recoverWotsEndpoints_eq, recoverWotsEndpoints_eq]
    congr 1; apply List.map_congr_left; intro r _
    exact fullIdealOverlaySuite_wotsSteps_eq _ _ _ _ _ _ _ _ _ _ _ _
  have hLayers : ∀ s pR rR lI gI cur ls,
      verifyProductionHypertreeLayers fov params s pR rR lI gI cur ls =
      verifyProductionHypertreeLayers sov params s pR rR lI gI cur ls := by
    intro s pR rR lI gI cur ls; induction ls generalizing lI gI cur with
    | nil => rw [verifyProductionHypertreeLayers_nil, verifyProductionHypertreeLayers_nil]
    | cons lsig rest ih =>
      rw [verifyProductionHypertreeLayers_cons, verifyProductionHypertreeLayers_cons]; dsimp only
      cases (!decide (lsig.tswCtr < 2 ^ 32))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hDig : productionLayerDigest fov params rR s pR cur lI
            (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (gI % 2 ^ params.subtreeHeight)) lsig.tswCtr =
          productionLayerDigest sov params rR s pR cur lI
            (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (gI % 2 ^ params.subtreeHeight)) lsig.tswCtr := by
          rw [productionLayerDigest_eq, productionLayerDigest_eq]
          split
          · rw [thHashLeafMsg_eq, thHashLeafMsg_eq]
            exact fullIdealOverlaySuite_role_ne_thCall _ _ _ _
              public_roles_ne_tagPrfMsg.2.2.2.2.2 _ _ _
          · exact fullIdealOverlaySuite_thHashInternalNode _ _ _ _ _ _ _ _ _ _ _
        rw [hDig]
        cases extractBaseWDigitsChecked params.w params.ell1 _ with
        | none => rfl
        | some digits =>
          dsimp only
          cases (!checkTargetSum params.w params.ell1 params.targetSum digits)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            if hL : lsig.wotsChains.length ≠ params.ell1 then
              rw [ite_eq_left hL, ite_eq_left hL]
            else
              rw [ite_eq_right hL, ite_eq_right hL, hRecWots, hWalkKp]
              cases walkMerkleAuthPathKp sov s _ _ .tree 0 params.subtreeHeight 0 _ _ lsig.authPath with
              | none => rfl
              | some nxt => exact ih _ _ nxt
          · simp only [↓reduceIte]
      · simp only [↓reduceIte]
  have hXof : ∀ rR s pR mu first n,
      thXofMsgBlocks fov rR s pR mu first n = thXofMsgBlocks sov rR s pR mu first n := by
    intro rR s pR mu first n; induction n generalizing first with
    | zero => rw [thXofMsgBlocks_zero, thXofMsgBlocks_zero]
    | succ n' ih =>
      rw [thXofMsgBlocks_succ, thXofMsgBlocks_succ,
        fullIdealOverlaySuite_thCall_non3 _ _ _ _ _ _ _ (by intro h; cases h), ih (first + 1)]
  have hForsRoots : ∀ s t0 kp0 idxs ops j rem,
      recoverProductionForsTreeRoots fov params s t0 kp0 idxs ops j rem =
      recoverProductionForsTreeRoots sov params s t0 kp0 idxs ops j rem := by
    intro s t0 kp0 idxs ops j rem; induction rem generalizing j with
    | zero => rw [recoverProductionForsTreeRoots_zero, recoverProductionForsTreeRoots_zero]
    | succ rem' ih =>
      rw [recoverProductionForsTreeRoots_succ, recoverProductionForsTreeRoots_succ]; dsimp only
      rw [forsIndexedLeafHash_eq, forsIndexedLeafHash_eq, thChainF_eq, thChainF_eq,
        fullIdealOverlaySuite_role_ne_thCall _ _ _ _ public_roles_ne_tagPrfMsg.2.1, hWalkKp]
      cases walkMerkleAuthPathKp sov s 0 t0 .forsTree _ params.forsHeight j _ _ _ with
      | none => rfl
      | some _ => rw [ih (j + 1)]
  rw [verifyProductionPqHashSig_eq, verifyProductionPqHashSig_eq]; dsimp only
  have hMu : thPreHash fov pk.pkSeed pk.pkRoot msg = thPreHash sov pk.pkSeed pk.pkRoot msg := by
    rw [thPreHash_eq, thPreHash_eq]
    exact fullIdealOverlaySuite_role_ne_thCall _ _ _ _ public_roles_ne_tagPrfMsg.2.2.2.2.1 _ _ _
  rw [hMu]
  cases (!params.productionWellFormed || !params.productionLeafIdxInRange sig.leafGlobalIdx)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases (decide (sig.layerSigs.length ≠ params.numLayers) || decide (sig.msgTswCtr ≠ 0))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hSt : params.statefulJorts
      · simp only [Bool.false_eq_true, ↓reduceIte]
        if hFLen : sig.forsOpenings.length ≠ params.forsTrees then
          rw [ite_eq_left hFLen, ite_eq_left hFLen]
        else
          rw [ite_eq_right hFLen, ite_eq_right hFLen]
          have hDer : deriveProductionStatelessInputs fov params sig.rRand pk.pkSeed pk.pkRoot
              (thPreHash sov pk.pkSeed pk.pkRoot msg) =
            deriveProductionStatelessInputs sov params sig.rRand pk.pkSeed pk.pkRoot
              (thPreHash sov pk.pkSeed pk.pkRoot msg) := by
            rw [deriveProductionStatelessInputs_eq, deriveProductionStatelessInputs_eq]
            dsimp only; rw [thXofMsg_eq, thXofMsg_eq, hXof]
          rw [hDer]
          cases deriveProductionStatelessInputs sov params sig.rRand pk.pkSeed pk.pkRoot _ with
          | none => rfl
          | some li =>
            dsimp only
            if hLi : sig.leafGlobalIdx ≠ li.1 then
              rw [ite_eq_left hLi, ite_eq_left hLi]
            else
              rw [ite_eq_right hLi, ite_eq_right hLi]
              have hRecF : recoverProductionForsPk fov params pk.pkSeed
                  (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
                  (sig.leafGlobalIdx % 2 ^ params.subtreeHeight) li.2 sig.forsOpenings =
                recoverProductionForsPk sov params pk.pkSeed
                  (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
                  (sig.leafGlobalIdx % 2 ^ params.subtreeHeight) li.2 sig.forsOpenings := by
                rw [recoverProductionForsPk_eq, recoverProductionForsPk_eq]
                split
                · rfl
                · rw [hForsRoots]
                  cases recoverProductionForsTreeRoots sov params pk.pkSeed _ _ li.2
                      sig.forsOpenings 0 params.forsTrees with
                  | none => rfl
                  | some _ =>
                    dsimp only; rw [thTweakTl_eq, thTweakTl_eq,
                      fullIdealOverlaySuite_role_ne_thCall _ _ _ _ public_roles_ne_tagPrfMsg.2.2.1]
              rw [hRecF]
              cases recoverProductionForsPk sov params pk.pkSeed _ _ li.2 sig.forsOpenings with
              | none => rfl
              | some _ => dsimp only; rw [hLayers]
      · simp only [↓reduceIte]
        cases (!sig.forsOpenings.isEmpty) <;> simp only [Bool.false_eq_true, ↓reduceIte, hLayers]
    · simp only [↓reduceIte]
  · simp only [↓reduceIte]

theorem fullIdealOverlaySuite_derivePublicKey_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (rfMsg secFn : Spec.Bytes → Spec.Bytes) :
    derivePublicKey (fullIdealOverlaySuite suite pkSeed rfMsg secFn) params ⟨[], [], pkSeed⟩ =
      derivePublicKeyIdealPrf suite params pkSeed secFn := by
  rw [derivePublicKeyIdealPrf.public_eqs]
  unfold derivePublicKey; dsimp only
  rw [computeXmssSubtreeRoot_eq, computeXmssSubtreeRoot_eq,
    ← computeMerkleNodeKp_zero_eq, ← computeMerkleNodeKp_zero_eq]
  congr 1
  exact fullIdealOverlaySuite_merkleKp_eq suite pkSeed rfMsg secFn pkSeed _ _ .tree 0 _ _
    (fullIdealOverlaySuite_wotsPk_eq suite params pkSeed rfMsg secFn ⟨[], [], pkSeed⟩ _ _) _ _ _

theorem fullIdealOverlaySuite_prodSignQuery_opt_eq (suite : TweakableHashSuite)
    (params : PqHashParams) (pkSeed : List UInt8) (rfMsg secFn : Spec.Bytes → Spec.Bytes)
    (q : ProdSigningQuery) (hOpt : q.randomness = [] ∨ q.randomness.length = 32)
    (hRf : ∀ x, x.length = 65 → (rfMsg x).length = 32) :
    prodSignQuery (fullIdealOverlaySuite suite pkSeed rfMsg secFn) params ⟨[], [], pkSeed⟩ q =
      signQueryIdealPrf suite params pkSeed rfMsg secFn q := by
  let fov := fullIdealOverlaySuite suite pkSeed rfMsg secFn
  let sov := secOverlaySuite suite pkSeed secFn
  let sk0 : PqSecretKey := ⟨[], [], pkSeed⟩
  have hPk : derivePublicKey (fullIdealOverlaySuite suite pkSeed rfMsg secFn) params ⟨[], [], pkSeed⟩ =
      derivePublicKey (secOverlaySuite suite pkSeed secFn) params ⟨[], [], pkSeed⟩ := by
    rw [fullIdealOverlaySuite_derivePublicKey_eq, derivePublicKeyIdealPrf.public_eqs]
  have hMu : ∀ pR m,
      thPreHash (fullIdealOverlaySuite suite pkSeed rfMsg secFn) pkSeed pR m =
      thPreHash (secOverlaySuite suite pkSeed secFn) pkSeed pR m := fun pR m => by
    rw [thPreHash_eq, thPreHash_eq]
    exact fullIdealOverlaySuite_role_ne_thCall _ _ _ _ public_roles_ne_tagPrfMsg.2.2.2.2.1 _ _ _
  have hForsLeafFn : ∀ t0 kp0 j u,
      forsIndexedLeafFn fov sk0 t0 kp0 j u = forsIndexedLeafFn sov sk0 t0 kp0 j u := by
    intro t0 kp0 j u
    rw [forsIndexedLeafFn_eq, forsIndexedLeafFn_eq, forsIndexedLeafHash_eq, forsIndexedLeafHash_eq,
      forsIndexedSecretLeaf_eq, forsIndexedSecretLeaf_eq, thSecretPrf_eq, thSecretPrf_eq,
      fullIdealOverlaySuite_role_ne_thCall _ _ _ _ public_roles_ne_tagPrfMsg.1,
      thChainF_eq, thChainF_eq,
      fullIdealOverlaySuite_role_ne_thCall _ _ _ _ public_roles_ne_tagPrfMsg.2.1]
  have hGrindL : ∀ rR pR cur tI kpI c rem,
      grindTswLeafCounterAux fov params.w params.ell1 params.targetSum rR pkSeed pR cur tI kpI c rem =
      grindTswLeafCounterAux sov params.w params.ell1 params.targetSum rR pkSeed pR cur tI kpI c rem := by
    intro rR pR cur tI kpI c rem; induction rem generalizing c with
    | zero => rw [grindTswLeafCounterAux_zero, grindTswLeafCounterAux_zero]
    | succ rem' ih =>
      rw [grindTswLeafCounterAux_succ, grindTswLeafCounterAux_succ,
        thHashLeafMsg_eq, thHashLeafMsg_eq,
        fullIdealOverlaySuite_role_ne_thCall _ _ _ _ public_roles_ne_tagPrfMsg.2.2.2.2.2,
        ih (c + 1)]
  have hGrindI : ∀ pR cur lU tI kpI c rem,
      grindTswInternalCounterAux fov params.w params.ell1 params.targetSum pkSeed pR cur lU tI kpI c rem =
      grindTswInternalCounterAux sov params.w params.ell1 params.targetSum pkSeed pR cur lU tI kpI c rem := by
    intro pR cur lU tI kpI c rem; induction rem generalizing c with
    | zero => rw [grindTswInternalCounterAux_zero, grindTswInternalCounterAux_zero]
    | succ rem' ih =>
      rw [grindTswInternalCounterAux_succ, grindTswInternalCounterAux_succ,
        fullIdealOverlaySuite_thHashInternalNode, ih (c + 1)]
  have hSignLayers : ∀ pR rR lI gI cur rem,
      signProductionHypertreeLayers fov params sk0 pR rR q.grindLimit lI gI cur rem =
      signProductionHypertreeLayers sov params sk0 pR rR q.grindLimit lI gI cur rem := by
    intro pR rR lI gI cur rem; induction rem generalizing lI gI cur with
    | zero => rw [signProductionHypertreeLayers_zero, signProductionHypertreeLayers_zero]
    | succ rem' ih =>
      rw [signProductionHypertreeLayers_succ, signProductionHypertreeLayers_succ]; dsimp only
      have hG : (if params.statefulJorts && decide (lI = 0) then
          grindTswLeafCounterAux fov params.w params.ell1 params.targetSum rR pkSeed pR cur
            (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (gI % 2 ^ params.subtreeHeight)) 0 q.grindLimit
        else
          grindTswInternalCounterAux fov params.w params.ell1 params.targetSum pkSeed pR cur
            (UInt32.ofNat lI) (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (gI % 2 ^ params.subtreeHeight)) 0 q.grindLimit) =
        (if params.statefulJorts && decide (lI = 0) then
          grindTswLeafCounterAux sov params.w params.ell1 params.targetSum rR pkSeed pR cur
            (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (gI % 2 ^ params.subtreeHeight)) 0 q.grindLimit
        else
          grindTswInternalCounterAux sov params.w params.ell1 params.targetSum pkSeed pR cur
            (UInt32.ofNat lI) (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (gI % 2 ^ params.subtreeHeight)) 0 q.grindLimit) := by
        split
        · exact hGrindL _ _ _ _ _ _ _
        · exact hGrindI _ _ _ _ _ _ _
      rw [hG]
      cases (if params.statefulJorts && decide (lI = 0) then
          grindTswLeafCounterAux sov params.w params.ell1 params.targetSum rR pkSeed pR cur
            (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (gI % 2 ^ params.subtreeHeight)) 0 q.grindLimit
        else
          grindTswInternalCounterAux sov params.w params.ell1 params.targetSum pkSeed pR cur
            (UInt32.ofNat lI) (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (gI % 2 ^ params.subtreeHeight)) 0 q.grindLimit) with
      | none => rfl
      | some triple =>
        rcases triple with ⟨ctr, digits, _⟩; dsimp only
        have hSub : computeXmssSubtreeRoot fov params sk0 (UInt32.ofNat lI)
            (UInt64.ofNat (gI / 2 ^ params.subtreeHeight)) =
          computeXmssSubtreeRoot sov params sk0 (UInt32.ofNat lI)
            (UInt64.ofNat (gI / 2 ^ params.subtreeHeight)) := by
          rw [computeXmssSubtreeRoot_eq, computeXmssSubtreeRoot_eq,
            ← computeMerkleNodeKp_zero_eq, ← computeMerkleNodeKp_zero_eq]
          exact fullIdealOverlaySuite_merkleKp_eq suite pkSeed rfMsg secFn pkSeed _ _ .tree 0 _ _
            (fullIdealOverlaySuite_wotsPk_eq suite params pkSeed rfMsg secFn sk0 _ _) _ _ _
        have hAp := fullIdealOverlaySuite_authPathKp_eq suite pkSeed rfMsg secFn pkSeed
          (UInt32.ofNat lI) (UInt64.ofNat (gI / 2 ^ params.subtreeHeight)) .tree 0 _ _
          (fullIdealOverlaySuite_wotsPk_eq suite params pkSeed rfMsg secFn sk0
            (UInt32.ofNat lI) (UInt64.ofNat (gI / 2 ^ params.subtreeHeight)))
          params.subtreeHeight 0 0 (gI % 2 ^ params.subtreeHeight)
        have hMap : ((List.range params.ell1).map fun r =>
            wotsChainSteps fov pkSeed (UInt32.ofNat lI)
              (UInt64.ofNat (gI / 2 ^ params.subtreeHeight)) (gI % 2 ^ params.subtreeHeight) r 0
              (digits.getD r 0)
              (wotsSecretBase fov sk0 (UInt32.ofNat lI)
                (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
                (gI % 2 ^ params.subtreeHeight) r)) =
          ((List.range params.ell1).map fun r =>
            wotsChainSteps sov pkSeed (UInt32.ofNat lI)
              (UInt64.ofNat (gI / 2 ^ params.subtreeHeight)) (gI % 2 ^ params.subtreeHeight) r 0
              (digits.getD r 0)
              (wotsSecretBase sov sk0 (UInt32.ofNat lI)
                (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
                (gI % 2 ^ params.subtreeHeight) r)) := by
          apply List.map_congr_left; intro r _
          rw [wotsSecretBase_eq, wotsSecretBase_eq, thSecretPrf_eq, thSecretPrf_eq,
            fullIdealOverlaySuite_role_ne_thCall _ _ _ _ public_roles_ne_tagPrfMsg.1,
            fullIdealOverlaySuite_wotsSteps_eq]
        rw [hMap, hAp, hSub, ih]
  have hCore : ∀ pk mu rR leaf fIdxs,
      signProductionHypertreeCore (fullIdealOverlaySuite suite pkSeed rfMsg secFn) params
        ⟨[], [], pkSeed⟩ pk q.message mu rR leaf fIdxs q.grindLimit =
      signProductionHypertreeCore (secOverlaySuite suite pkSeed secFn) params
        ⟨[], [], pkSeed⟩ pk q.message mu rR leaf fIdxs q.grindLimit := by
    intro pk mu rR leaf fIdxs
    change signProductionHypertreeCore fov params sk0 pk q.message mu rR leaf fIdxs q.grindLimit =
      signProductionHypertreeCore sov params sk0 pk q.message mu rR leaf fIdxs q.grindLimit
    rw [signProductionHypertreeCore_def, signProductionHypertreeCore_def]; dsimp only
    cases hSt : params.statefulJorts
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases fIdxs with
      | none => rfl
      | some idxs =>
        dsimp only
        have hOps : buildProductionForsOpenings fov params sk0
            (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)) (leaf % 2 ^ params.subtreeHeight) idxs =
          buildProductionForsOpenings sov params sk0
            (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)) (leaf % 2 ^ params.subtreeHeight) idxs := by
          rw [buildProductionForsOpenings_def, buildProductionForsOpenings_def]; dsimp only
          apply List.map_congr_left; intro j _
          rw [forsIndexedSecretLeaf_eq, forsIndexedSecretLeaf_eq, thSecretPrf_eq, thSecretPrf_eq,
            fullIdealOverlaySuite_role_ne_thCall _ _ _ _ public_roles_ne_tagPrfMsg.1,
            fullIdealOverlaySuite_authPathKp_eq suite pkSeed rfMsg secFn pkSeed 0 _ .forsTree _ _ _
              (hForsLeafFn _ _ j)]
        have hFpk : computeProductionForsPk fov params sk0
            (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)) (leaf % 2 ^ params.subtreeHeight) =
          computeProductionForsPk sov params sk0
            (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)) (leaf % 2 ^ params.subtreeHeight) := by
          rw [computeProductionForsPk_eq, computeProductionForsPk_eq, thTweakTl_eq, thTweakTl_eq,
            fullIdealOverlaySuite_role_ne_thCall _ _ _ _ public_roles_ne_tagPrfMsg.2.2.1]
          congr 1; apply List.map_congr_left; intro j _
          exact fullIdealOverlaySuite_merkleKp_eq suite pkSeed rfMsg secFn pkSeed 0 _ .forsTree _
            _ _ (hForsLeafFn _ _ j) _ _ _
        rw [hOps, hFpk, hSignLayers]
        cases signProductionHypertreeLayers sov params sk0 pk.pkRoot rR q.grindLimit 0 leaf _
            params.numLayers with
        | none => rfl
        | some _ =>
          dsimp only
          rw [fullIdealOverlaySuite_verify_eq, secOverlaySuite_verify_eq]
    · simp only [↓reduceIte, hSignLayers]
      cases signProductionHypertreeLayers sov params sk0 pk.pkRoot rR q.grindLimit 0 leaf mu
          params.numLayers with
      | none => rfl
      | some _ =>
        dsimp only
        rw [fullIdealOverlaySuite_verify_eq, secOverlaySuite_verify_eq]
  rw [prodSignQuery_eq, signQueryIdealPrf.public_eqs, signQueryWithRandFn.public_eqs,
    signCoreWithRand.public_eqs]
  dsimp only
  have hPkSeed : (derivePublicKey (secOverlaySuite suite pkSeed secFn) params
      ⟨[], [], pkSeed⟩).pkSeed = pkSeed := by
    unfold derivePublicKey; rfl
  have hMuLen : (thPreHash (secOverlaySuite suite pkSeed secFn) pkSeed
      (derivePublicKey (secOverlaySuite suite pkSeed secFn) params ⟨[], [], pkSeed⟩).pkRoot
      q.message).length = 32 := by rw [thPreHash_eq]; exact thCall_length _ _ _ _ _
  have hPrfEq : thPrfMsg (fullIdealOverlaySuite suite pkSeed rfMsg secFn) [] q.randomness
      (thPreHash (secOverlaySuite suite pkSeed secFn) pkSeed
        (derivePublicKey (secOverlaySuite suite pkSeed secFn) params ⟨[], [], pkSeed⟩).pkRoot
        q.message) =
    rfMsg (encodePrfMsg65 q.randomness
      (thPreHash (secOverlaySuite suite pkSeed secFn) pkSeed
        (derivePublicKey (secOverlaySuite suite pkSeed secFn) params ⟨[], [], pkSeed⟩).pkRoot
        q.message)) := by
    rw [fullIdealOverlaySuite_thPrfMsg_empty suite pkSeed rfMsg secFn hOpt hMuLen,
      padBytes32_of_len32 (hRf _ (encodePrfMsg65_length _ _))]
  cases hSt : params.statefulJorts
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [evalProductionStatelessSign_eq]
    simp only [hSt, Bool.false_or]
    cases (!params.productionWellFormed)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hPk, hPkSeed, hMu, hPrfEq]
      have hXof : ∀ rR pR mu first n,
          thXofMsgBlocks (fullIdealOverlaySuite suite pkSeed rfMsg secFn) rR pkSeed pR mu first n =
          thXofMsgBlocks (secOverlaySuite suite pkSeed secFn) rR pkSeed pR mu first n := by
        intro rR pR mu first n; induction n generalizing first with
        | zero => rw [thXofMsgBlocks_zero, thXofMsgBlocks_zero]
        | succ n' ih =>
          rw [thXofMsgBlocks_succ, thXofMsgBlocks_succ,
            fullIdealOverlaySuite_thCall_non3 _ _ _ _ _ _ _ (by intro h; cases h), ih (first + 1)]
      have hDer : ∀ rR pR mu,
          deriveProductionStatelessInputs (fullIdealOverlaySuite suite pkSeed rfMsg secFn) params
            rR pkSeed pR mu =
          deriveProductionStatelessInputs (secOverlaySuite suite pkSeed secFn) params
            rR pkSeed pR mu := by
        intro rR pR mu
        rw [deriveProductionStatelessInputs_eq, deriveProductionStatelessInputs_eq]
        dsimp only; rw [thXofMsg_eq, thXofMsg_eq, hXof]
      rw [hDer]
      cases deriveProductionStatelessInputs (secOverlaySuite suite pkSeed secFn) params _ pkSeed _ _ with
      | none => rfl
      | some val =>
        rcases val with ⟨leafGlobalIdx, forsIdxs⟩
        dsimp only
        exact hCore _ _ _ _ _
    · simp only [↓reduceIte]
  · simp only [↓reduceIte]
    rw [evalProductionStatefulSign_eq]
    simp only [hSt, Bool.not_true, Bool.false_or]
    cases (!params.productionWellFormed || !params.productionLeafIdxInRange q.epoch)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hPk, hPkSeed, hMu, hPrfEq]
      exact hCore _ _ _ _ _
    · simp only [↓reduceIte]

theorem fullIdealOverlaySuite_prodSignQuery_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (rfMsg secFn : Spec.Bytes → Spec.Bytes) (q : ProdSigningQuery)
    (hRf : ∀ x, x.length = 65 → (rfMsg x).length = 32) :
    prodSignQuery (fullIdealOverlaySuite suite pkSeed rfMsg secFn) params ⟨[], [], pkSeed⟩
        (canonicalizeQueryOptRand q) =
      signQueryIdealPrf suite params pkSeed rfMsg secFn (canonicalizeQueryOptRand q) :=
  fullIdealOverlaySuite_prodSignQuery_opt_eq suite params pkSeed rfMsg secFn
    (canonicalizeQueryOptRand q)
    (by rw [canonicalizeQueryOptRand.public_eqs]; exact canonicalOptRand_spec q.randomness) hRf

theorem fullIdealOverlaySuite_productionSigningLog_eq (suite : TweakableHashSuite)
    (params : PqHashParams) (pkSeed : List UInt8) (rfMsg secFn : Spec.Bytes → Spec.Bytes)
    (hRf : ∀ x, x.length = 65 → (rfMsg x).length = 32) :
    ∀ (qs : List ProdSigningQuery),
      (∀ q ∈ qs, q.randomness = [] ∨ q.randomness.length = 32) →
      productionSigningLog (fullIdealOverlaySuite suite pkSeed rfMsg secFn) params
        ⟨[], [], pkSeed⟩ qs =
      signLogFromOracle (signQueryIdealPrf suite params pkSeed rfMsg secFn) qs
  | [], _ => by rw [productionSigningLog_nil, signLogFromOracle.public_eq_1]
  | q :: qs, hAll => by
    rw [productionSigningLog_cons, signLogFromOracle_cons,
      fullIdealOverlaySuite_prodSignQuery_opt_eq suite params pkSeed rfMsg secFn q
        (hAll q List.mem_cons_self) hRf,
      fullIdealOverlaySuite_productionSigningLog_eq suite params pkSeed rfMsg secFn hRf qs
        (fun q' hq' => hAll q' (List.mem_cons_of_mem q hq'))]
    cases signQueryIdealPrf suite params pkSeed rfMsg secFn q <;> rfl

/-- **Public-Extractor Completeness on `ExecEufCmaIdealPrfGame`
    (`execEufCmaIdealPrf_extract_complete`).** -/
theorem execEufCmaIdealPrf_extract_complete {n qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams) (hw : params.w = 4 ∨ params.w = 16)
    (pkSeedOf : Fin n → List UInt8) (rfMsg rfSec : Fin n → Spec.Bytes → Spec.Bytes)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) (ω : Fin n)
    (hRf : ∀ x, x.length = 65 → (rfMsg ω x).length = 32)
    (hWin : (ExecEufCmaIdealPrfGame true hPos suite params pkSeedOf rfMsg rfSec adv).win ω = true) :
    let fov := fullIdealOverlaySuite suite (pkSeedOf ω) (rfMsg ω) (rfSec ω)
    let sk0 : PqSecretKey := ⟨[], [], pkSeedOf ω⟩
    let pk := derivePublicKeyIdealPrf suite params (pkSeedOf ω) (rfSec ω)
    let signFn := signQueryIdealPrf suite params (pkSeedOf ω) (rfMsg ω) (rfSec ω)
    let run := evalLatchedAdaptiveTree true suite.rawHash signFn
      ((canonicalizeAdvOptRand (adv ω)).run pk) 0
    let log := signLogFromOracle signFn run.2
    let cands := prodPublicExtract fov params pk log run.1.1 run.1.2
    cands.subsetCover = true ∨
    (∃ sub ∈ cands.collisions, smDtTcrChallengerCheck fov params sk0 run.2 (some sub) = true) ∨
    (∃ sub ∈ cands.preimages, smDtPreChallengerCheck fov params sk0 run.2 (some sub) = true) := by
  intro fov sk0 pk signFn run log cands
  rw [ExecEufCmaIdealPrfGame_win] at hWin
  have hPkEq : derivePublicKey fov params sk0 = pk :=
    fullIdealOverlaySuite_derivePublicKey_eq suite params (pkSeedOf ω) (rfMsg ω) (rfSec ω)
  have hOptAll : ∀ q ∈ run.2, q.randomness = [] ∨ q.randomness.length = 32 := by
    intro q hq; dsimp only [run] at hq
    rw [canonicalizeAdvOptRand_run] at hq
    exact evalLatched_canonicalize_log_optRand true suite.rawHash signFn _ 0 q hq
  have hLogEq : productionSigningLog fov params sk0 run.2 = log :=
    fullIdealOverlaySuite_productionSigningLog_eq suite params (pkSeedOf ω) (rfMsg ω) (rfSec ω)
      hRf run.2 hOptAll
  have hOneTime : ProdOneTimeLog run.2 :=
    evalLatchedAdaptiveTree_oneTime suite.rawHash signFn _ 0
  let o : ProdEufCmaOutcome := ⟨sk0, run.2, run.1.1, run.1.2⟩
  have hWinO : prodEufCmaWin fov params o = true := by
    rw [prodEufCmaWin_eq]; dsimp only [o]
    rw [hPkEq, hLogEq, fullIdealOverlaySuite_verify_eq]; exact hWin
  have hExt := prodPublicExtract_complete fov params hw o (fun _ => hOneTime) hWinO
  dsimp only [o] at hExt; rw [hPkEq, hLogEq] at hExt; exact hExt

/-! ## §2. Unified 3-Arg Tweakable Hash Adapter (`suiteTweakHash`) -/

/-- Unified 3-argument tweakable hash `th seed tweak msg` over `suite`:
    * `0x00 :: adrsBytes`: 1-argument `tagThF` chain/leaf hash `thChainF suite seed adrs msg`.
    * `0x01 :: adrsBytes ++ role`: fixed-address multi-argument call (`tagThH`, `tagThTl`, `tagHPre`).
    * `0x02 :: modeByte :: baseAdrs`: layer digest call (`tagHMsg` when `modeByte = 0x01`, else
      `tagHInternal`), taking TSW counter step in the message frame so collisions sharing
      `(layer, tree, kp)` map to the identical tweak. -/
def suiteTweakHash (suite : TweakableHashSuite) (seed tweak msg : Spec.Bytes) : Spec.Bytes :=
  match tweak with
  | mode :: rest =>
    if mode = 0x00 then
      match decodeAdrsBytes rest with
      | some adrs => suite.rawHash (thPreimage tagThF seed adrs [msg])
      | none => List.replicate 32 0
    else if mode = 0x01 then
      match decodeAdrsBytes (rest.take 32), decodeMultiFrameBytes msg with
      | some adrs, some args => suite.rawHash (thPreimage (rest.drop 32) seed adrs args)
      | _, _ => List.replicate 32 0
    else if mode = 0x02 then
      match rest with
      | modeByte :: adrsBytes =>
        match decodeAdrsBytes adrsBytes, decodeMultiFrameBytes msg with
        | some baseAdrs, some [rRand, pkRoot, cur, ctrAdrsBytes, ctrBe4] =>
          match decodeAdrsBytes ctrAdrsBytes with
          | some ctrAdrs =>
            let adrs := { baseAdrs with hashStep := ctrAdrs.hashStep }
            if modeByte = 0x01 then
              suite.rawHash (thPreimage tagHMsg seed adrs [rRand, pkRoot, cur, ctrBe4])
            else
              suite.rawHash (thPreimage tagHInternal seed adrs [pkRoot, cur, ctrBe4])
          | none => List.replicate 32 0
        | _, _ => List.replicate 32 0
      | [] => List.replicate 32 0
    else List.replicate 32 0
  | [] => List.replicate 32 0

def encodeChainFTweak (adrs : HashAdrs) : Spec.Bytes :=
  0x00 :: encodeAdrs adrs

def encodeMultiRoleTweak (role : List UInt8) (adrs : HashAdrs) : Spec.Bytes :=
  0x01 :: (encodeAdrs adrs ++ role)

def encodeLayerDigestTweak (params : PqHashParams) (i : Nat) (T : UInt64) (KP : UInt32) :
    Spec.Bytes :=
  0x02 :: (if params.statefulJorts && decide (i = 0) then 0x01 else 0x00) ::
    encodeAdrs ⟨UInt32.ofNat i, T, .wotsHash, KP, 0, 0⟩

def encodeLayerDigestMsg (rRand pkRoot cur : List UInt8) (ctr : Nat) : Spec.Bytes :=
  encodeMultiFrame [rRand, pkRoot, cur, encodeAdrs ⟨0, 0, .wotsHash, 0, 0, UInt32.ofNat ctr⟩,
    be 4 ctr]

theorem suiteTweakHash_chainF (suite : TweakableHashSuite) (seed : Spec.Bytes) (adrs : HashAdrs)
    (x : Spec.Bytes) :
    suiteTweakHash suite seed (encodeChainFTweak adrs) x = thChainF suite seed adrs x := by
  unfold suiteTweakHash encodeChainFTweak
  generalize hA : encodeAdrs adrs = bs
  dsimp only
  rw [ite_eq_left rfl, ← hA, decodeAdrsBytes_encodeAdrs, thChainF_eq, thCall_eq]

theorem suiteTweakHash_multiRole (suite : TweakableHashSuite) (seed role : Spec.Bytes)
    (adrs : HashAdrs) (args : List (List UInt8)) :
    suiteTweakHash suite seed (encodeMultiRoleTweak role adrs) (encodeMultiFrame args) =
      suite.rawHash (thPreimage role seed adrs args) := by
  have hLen : (encodeAdrs adrs).length = 32 := encodeAdrs_length adrs
  unfold suiteTweakHash encodeMultiRoleTweak
  generalize hA : encodeAdrs adrs = bs at hLen ⊢
  generalize hM : encodeMultiFrame args = ms
  dsimp only
  rw [ite_eq_right (by decide : ¬ ((0x01 : UInt8) = 0x00)), ite_eq_left rfl,
    List.take_left' hLen, List.drop_left' hLen, ← hA, ← hM, decodeAdrsBytes_encodeAdrs,
    decodeMultiFrameBytes_encodeMultiFrame]

private theorem suiteTweakHash_mode02 (suite : TweakableHashSuite) (seed : Spec.Bytes)
    (modeByte : UInt8) (ab mb cb : Spec.Bytes) (baseAdrs ctrAdrs : HashAdrs)
    (rRand pkRoot cur ctrBe4 : List UInt8)
    (h1 : decodeAdrsBytes ab = some baseAdrs)
    (h2 : decodeMultiFrameBytes mb = some [rRand, pkRoot, cur, cb, ctrBe4])
    (h3 : decodeAdrsBytes cb = some ctrAdrs) :
    suiteTweakHash suite seed (0x02 :: modeByte :: ab) mb =
      if modeByte = 0x01 then
        suite.rawHash (thPreimage tagHMsg seed
          { baseAdrs with hashStep := ctrAdrs.hashStep } [rRand, pkRoot, cur, ctrBe4])
      else
        suite.rawHash (thPreimage tagHInternal seed
          { baseAdrs with hashStep := ctrAdrs.hashStep } [pkRoot, cur, ctrBe4]) := by
  unfold suiteTweakHash
  have n0 : ¬ ((0x02 : UInt8) = 0x00) := by decide
  have n1 : ¬ ((0x02 : UInt8) = 0x01) := by decide
  simp only [n0, n1, ↓reduceIte, h1, h2, h3]

theorem suiteTweakHash_layerDigest (suite : TweakableHashSuite) (params : PqHashParams)
    (rRand seed pkRoot cur : List UInt8) (i : Nat) (T : UInt64) (KP : UInt32) (ctr : Nat) :
    suiteTweakHash suite seed (encodeLayerDigestTweak params i T KP)
        (encodeLayerDigestMsg rRand pkRoot cur ctr) =
      productionLayerDigest suite params rRand seed pkRoot cur i T KP ctr := by
  unfold encodeLayerDigestTweak encodeLayerDigestMsg
  rw [suiteTweakHash_mode02 suite seed _ _ _ _ _ _ rRand pkRoot cur (be 4 ctr)
    (decodeAdrsBytes_encodeAdrs _) (decodeMultiFrameBytes_encodeMultiFrame _)
    (decodeAdrsBytes_encodeAdrs _)]
  rw [productionLayerDigest_eq]
  cases hc : (params.statefulJorts && decide (i = 0))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [ite_eq_right (by decide : ¬ ((0x00 : UInt8) = 0x01)), thHashInternalNode_eq, thCall_eq]
  · obtain ⟨_, hi0⟩ := Bool.and_eq_true_iff.mp hc
    have hi : i = 0 := of_decide_eq_true hi0
    subst hi
    simp only [↓reduceIte]
    rw [thHashLeafMsg_eq, thCall_eq]; rfl

def forsLeafHashAdrs (tree0 : UInt64) (kp0 j u : Nat) : HashAdrs :=
  ⟨0, tree0, .forsTree, UInt32.ofNat kp0, UInt32.ofNat j, UInt32.ofNat u⟩

theorem forsIndexedLeafHash_eq_chainF_adrs (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (tree0 : UInt64) (kp0 j u : Nat) (x : List UInt8) :
    forsIndexedLeafHash suite pkSeed tree0 kp0 j u x =
      thChainF suite pkSeed (forsLeafHashAdrs tree0 kp0 j u) x := by
  unfold forsLeafHashAdrs
  rw [forsIndexedLeafHash_eq]

#export_eqns encodeChainFTweak encodeMultiRoleTweak encodeLayerDigestTweak encodeLayerDigestMsg
  forsLeafHashAdrs

/-- `#tooth` Outside the domain-separated prefix tags `0x00`/`0x01`/`0x02`, `suiteTweakHash`
    refutes unconditional message injectivity by collapsing `[0xFF]` tweaks. -/
theorem tooth_suiteTweakHash_unknown_prefix_collides (suite : TweakableHashSuite)
    (seed : Spec.Bytes) :
    ¬ (∀ tweak m₁ m₂ : Spec.Bytes, m₁ ≠ m₂ →
        suiteTweakHash suite seed tweak m₁ ≠ suiteTweakHash suite seed tweak m₂) :=
  fun h => h [0xFF] [0x00] [0x01] (by decide) (by unfold suiteTweakHash; rfl)

#verify_constructive
  Qsag.fullIdealOverlaySuite_verify_eq
  Qsag.fullIdealOverlaySuite_derivePublicKey_eq
  Qsag.fullIdealOverlaySuite_prodSignQuery_eq
  Qsag.execEufCmaIdealPrf_extract_complete
  Qsag.suiteTweakHash_chainF
  Qsag.suiteTweakHash_multiRole
  suiteTweakHash_mode02
  Qsag.suiteTweakHash_layerDigest
  Qsag.forsIndexedLeafHash_eq_chainF_adrs
  Qsag.tooth_suiteTweakHash_unknown_prefix_collides

#tooth_pair Qsag.suiteTweakHash_chainF vs Qsag.tooth_suiteTweakHash_unknown_prefix_collides

end Qsag
end

module
/-
# Qsag.Protocol.Signing.HulsingSecOverlay — Signer-Only Secret-PRF Overlay (`secOverlaySuite`)

Constructs the signer-internal secret-PRF overlay `secOverlaySuite suite pkSeed secFn`, which
intercepts ONLY `thPreimage tagPrf pkSeed adrs [[]]` inside key derivation and signing while
leaving every public hash role (`tagThF`, `tagThTl`, `tagThH`, `tagHPre`, `tagHMsg`, `tagHInternal`,
`tagHXof`) and `verifyProductionPqHashSig` **100% identical** to `suite`.
-/

public import Qsag.Protocol.Signing.HulsingPrfMsgHop
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-- Fixed-length `(seedLen + 32 → 32)` PRF wrapper over `thSecretPrf suite pkSeed skSeed adrs`
    matching `Spec.PrfSampleOk`. -/
def suitePrfSec (seedLen : Nat) (suite : TweakableHashSuite) (skSeed inp : Spec.Bytes) :
    Spec.Bytes :=
  if inp.length = seedLen + 32 then
    match decodeAdrsBytes (inp.drop seedLen) with
    | some adrs => thSecretPrf suite (inp.take seedLen) skSeed adrs
    | none => zero32
  else []

theorem suitePrfSec_eq_thSecretPrf {seedLen : Nat} (suite : TweakableHashSuite)
    {pkSeed : Spec.Bytes} (hSeed : pkSeed.length = seedLen)
    (skSeed : Spec.Bytes) (adrs : HashAdrs) :
    suitePrfSec seedLen suite skSeed (pkSeed ++ encodeAdrs adrs) =
      thSecretPrf suite pkSeed skSeed adrs := by
  have hAdrsLen : (encodeAdrs adrs).length = 32 := encodeAdrs_length adrs
  have hTot : (pkSeed ++ encodeAdrs adrs).length = seedLen + 32 := by
    rw [List.length_append, hSeed, hAdrsLen]
  unfold suitePrfSec
  rw [ite_eq_left hTot, List.drop_left' hSeed, List.take_left' hSeed, decodeAdrsBytes_encodeAdrs]

/-- Signer-internal overlay suite routing ONLY `thPreimage tagPrf pkSeed adrs [[]]` to
    `padBytes32 (secFn (pkSeed ++ encodeAdrs adrs))` while delegating EVERY public hash call to
    `suite.rawHash`. -/
def secOverlaySuite (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (secFn : Spec.Bytes → Spec.Bytes) : TweakableHashSuite where
  suiteId := suite.suiteId
  rawHash raw :=
    match parseThPreimage raw with
    | some (role, seed, adrs, [[]]) =>
      if role = tagPrf ∧ seed = pkSeed then padBytes32 (secFn (pkSeed ++ encodeAdrs adrs))
      else suite.rawHash raw
    | _ => suite.rawHash raw
  rawHash_len raw := by
    split
    · split
      · exact padBytes32_length _
      · exact suite.rawHash_len raw
    · exact suite.rawHash_len raw

theorem secOverlaySuite_nonPrf_thCall (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (secFn : Spec.Bytes → Spec.Bytes) {role : List UInt8} (hNe : role ≠ tagPrf)
    (seed : List UInt8) (adrs : HashAdrs) (args : List (List UInt8)) :
    thCall (secOverlaySuite suite pkSeed secFn) role seed adrs args =
      thCall suite role seed adrs args := by
  rw [thCall_eq, thCall_eq]
  unfold secOverlaySuite
  dsimp only
  rw [parseThPreimage_thPreimage]
  cases args with
  | nil => rfl
  | cons a rest =>
    cases a with
    | nil =>
      cases rest with
      | nil => simp [hNe]
      | cons _ _ => rfl
    | cons _ _ => rfl

theorem secOverlaySuite_tagPrf_empty (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (secFn : Spec.Bytes → Spec.Bytes) (adrs : HashAdrs) :
    thSecretPrf (secOverlaySuite suite pkSeed secFn) pkSeed [] adrs =
      padBytes32 (secFn (pkSeed ++ encodeAdrs adrs)) := by
  rw [thSecretPrf_eq, thCall_eq]
  unfold secOverlaySuite
  dsimp only
  rw [parseThPreimage_thPreimage]
  simp

theorem tagThF_ne_tagPrf : tagThF ≠ tagPrf ∧ tagThTl ≠ tagPrf := by
  simp only [tagThF.public_eqs, tagThTl.public_eqs, tagPrf.public_eqs]
  decide +kernel

theorem secOverlaySuite_thCall_cons2 (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (secFn : Spec.Bytes → Spec.Bytes) (role seed : List UInt8) (adrs : HashAdrs)
    (a b : List UInt8) (rest : List (List UInt8)) :
    thCall (secOverlaySuite suite pkSeed secFn) role seed adrs (a :: b :: rest) =
      thCall suite role seed adrs (a :: b :: rest) := by
  rw [thCall_eq, thCall_eq]
  unfold secOverlaySuite
  dsimp only
  rw [parseThPreimage_thPreimage]
  cases a <;> rfl

theorem secOverlaySuite_verify_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (secFn : Spec.Bytes → Spec.Bytes)
    (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig) :
    verifyProductionPqHashSig (secOverlaySuite suite pkSeed secFn) params pk msg sig =
      verifyProductionPqHashSig suite params pk msg sig := by
  let ov := secOverlaySuite suite pkSeed secFn
  have hWotsSteps : ∀ s l t kp r k start x,
      wotsChainSteps ov s l t kp r start k x = wotsChainSteps suite s l t kp r start k x := by
    intro s l t kp r k; induction k with
    | zero => intro start x; rw [wotsChainSteps_zero, wotsChainSteps_zero]
    | succ k' ih =>
      intro start x; rw [wotsChainSteps_succ, wotsChainSteps_succ]; dsimp only
      rw [thChainF_eq, thChainF_eq, secOverlaySuite_nonPrf_thCall _ _ _ tagThF_ne_tagPrf.1]
      exact ih (start + 1) _
  have hWalkKp : ∀ s l t kind kp ht root loc leaf path,
      walkMerkleAuthPathKp ov s l t kind kp ht root loc leaf path =
      walkMerkleAuthPathKp suite s l t kind kp ht root loc leaf path := by
    intro s l t kind kp ht
    induction ht with
    | zero => intro root loc leaf path; cases path <;> rfl
    | succ ht' ih =>
      intro root loc leaf path
      cases path with
      | nil => rfl
      | cons sib rest =>
        unfold walkMerkleAuthPathKp
        dsimp only
        by_cases hHalf : loc < 2 ^ ht'
        · simp only [hHalf, ↓reduceIte, ih]
          cases walkMerkleAuthPathKp suite s l t kind kp ht' (2 * root) loc leaf rest with
          | none => rfl
          | some _ =>
            dsimp only
            rw [thNodeH_eq, thNodeH_eq]
            congr 1
            exact secOverlaySuite_thCall_cons2 _ _ _ _ _ _ _ _ _
        · simp only [hHalf, ↓reduceIte, ih]
          cases walkMerkleAuthPathKp suite s l t kind kp ht' (2 * root + 1) (loc - 2 ^ ht')
              leaf rest with
          | none => rfl
          | some _ =>
            dsimp only
            rw [thNodeH_eq, thNodeH_eq]
            congr 1
            exact secOverlaySuite_thCall_cons2 _ _ _ _ _ _ _ _ _
  have hRecWots : ∀ s l t kp digs chs,
      recoverWotsPkFromSig ov params s l t kp digs chs =
      recoverWotsPkFromSig suite params s l t kp digs chs := by
    intro s l t kp digs chs
    rw [recoverWotsPkFromSig_eq, recoverWotsPkFromSig_eq, thTweakTl_eq, thTweakTl_eq,
      secOverlaySuite_nonPrf_thCall _ _ _ tagThF_ne_tagPrf.2,
      recoverWotsEndpoints_eq, recoverWotsEndpoints_eq]
    congr 1; apply List.map_congr_left; intro r _; exact hWotsSteps _ _ _ _ _ _ _ _
  have hLayers : ∀ s pR rR lI gI cur ls,
      verifyProductionHypertreeLayers ov params s pR rR lI gI cur ls =
      verifyProductionHypertreeLayers suite params s pR rR lI gI cur ls := by
    intro s pR rR lI gI cur ls
    induction ls generalizing lI gI cur with
    | nil => rw [verifyProductionHypertreeLayers_nil, verifyProductionHypertreeLayers_nil]
    | cons lsig rest ih =>
      rw [verifyProductionHypertreeLayers_cons, verifyProductionHypertreeLayers_cons]
      dsimp only
      cases (!decide (lsig.tswCtr < 2 ^ 32))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hDig : productionLayerDigest ov params rR s pR cur lI
            (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (gI % 2 ^ params.subtreeHeight)) lsig.tswCtr =
          productionLayerDigest suite params rR s pR cur lI
            (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (gI % 2 ^ params.subtreeHeight)) lsig.tswCtr := by
          rw [productionLayerDigest_eq, productionLayerDigest_eq]
          split
          · rw [thHashLeafMsg_eq, thHashLeafMsg_eq]
            exact secOverlaySuite_thCall_cons2 _ _ _ _ _ _ _ _ _
          · rw [thHashInternalNode_eq, thHashInternalNode_eq]
            exact secOverlaySuite_thCall_cons2 _ _ _ _ _ _ _ _ _
        rw [hDig]
        cases extractBaseWDigitsChecked params.w params.ell1 _ with
        | none => rfl
        | some digits =>
          dsimp only
          cases (!checkTargetSum params.w params.ell1 params.targetSum digits)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            by_cases hL : lsig.wotsChains.length ≠ params.ell1
            · rw [ite_eq_left hL, ite_eq_left hL]
            · rw [ite_eq_right hL, ite_eq_right hL, hRecWots, hWalkKp]
              cases walkMerkleAuthPathKp suite s (UInt32.ofNat lI)
                  (UInt64.ofNat (gI / 2 ^ params.subtreeHeight)) .tree 0
                  params.subtreeHeight 0 (gI % 2 ^ params.subtreeHeight) _ lsig.authPath with
              | none => rfl
              | some nxt => exact ih _ _ nxt
          · simp only [↓reduceIte]
      · simp only [↓reduceIte]
  have hXof : ∀ rR s pR mu first n,
      thXofMsgBlocks ov rR s pR mu first n = thXofMsgBlocks suite rR s pR mu first n := by
    intro rR s pR mu first n
    induction n generalizing first with
    | zero => rw [thXofMsgBlocks_zero, thXofMsgBlocks_zero]
    | succ n' ih =>
      rw [thXofMsgBlocks_succ, thXofMsgBlocks_succ, secOverlaySuite_thCall_cons2, ih]
  have hForsRoots : ∀ s t0 kp0 idxs ops j rem,
      recoverProductionForsTreeRoots ov params s t0 kp0 idxs ops j rem =
      recoverProductionForsTreeRoots suite params s t0 kp0 idxs ops j rem := by
    intro s t0 kp0 idxs ops j rem
    induction rem generalizing j with
    | zero => rw [recoverProductionForsTreeRoots_zero, recoverProductionForsTreeRoots_zero]
    | succ rem' ih =>
      rw [recoverProductionForsTreeRoots_succ, recoverProductionForsTreeRoots_succ]
      dsimp only
      have hLeafH : forsIndexedLeafHash ov s t0 kp0 j (idxs.getD j 0)
          (ops.getD j ⟨[], []⟩).secretVal =
        forsIndexedLeafHash suite s t0 kp0 j (idxs.getD j 0)
          (ops.getD j ⟨[], []⟩).secretVal := by
        rw [forsIndexedLeafHash_eq, forsIndexedLeafHash_eq, thChainF_eq, thChainF_eq]
        exact secOverlaySuite_nonPrf_thCall _ _ _ tagThF_ne_tagPrf.1 _ _ _
      rw [hLeafH, hWalkKp]
      cases walkMerkleAuthPathKp suite s 0 t0 .forsTree (UInt32.ofNat kp0) params.forsHeight j
          (idxs.getD j 0) _ (ops.getD j ⟨[], []⟩).authPath with
      | none => rfl
      | some rJ => rw [ih (j + 1)]
  rw [verifyProductionPqHashSig_eq, verifyProductionPqHashSig_eq]
  dsimp only
  have hMu : thPreHash ov pk.pkSeed pk.pkRoot msg = thPreHash suite pk.pkSeed pk.pkRoot msg := by
    rw [thPreHash_eq, thPreHash_eq]
    exact secOverlaySuite_thCall_cons2 _ _ _ _ _ _ _ _ _
  rw [hMu]
  cases (!params.productionWellFormed || !params.productionLeafIdxInRange sig.leafGlobalIdx)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases (decide (sig.layerSigs.length ≠ params.numLayers) || decide (sig.msgTswCtr ≠ 0))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hSt : params.statefulJorts
      · simp only [hSt, ↓reduceIte]
        cases (!sig.forsOpenings.isEmpty)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hLayers]
        · simp only [↓reduceIte]
      · simp only [hSt, Bool.false_eq_true, ↓reduceIte]
        by_cases hFLen : sig.forsOpenings.length ≠ params.forsTrees
        · rw [ite_eq_left hFLen, ite_eq_left hFLen]
        · rw [ite_eq_right hFLen, ite_eq_right hFLen]
          have hDer : deriveProductionStatelessInputs ov params sig.rRand pk.pkSeed pk.pkRoot
              (thPreHash suite pk.pkSeed pk.pkRoot msg) =
            deriveProductionStatelessInputs suite params sig.rRand pk.pkSeed pk.pkRoot
              (thPreHash suite pk.pkSeed pk.pkRoot msg) := by
            rw [deriveProductionStatelessInputs_eq, deriveProductionStatelessInputs_eq]
            dsimp only
            rw [thXofMsg_eq, thXofMsg_eq, hXof]
          rw [hDer]
          cases deriveProductionStatelessInputs suite params sig.rRand pk.pkSeed pk.pkRoot
              (thPreHash suite pk.pkSeed pk.pkRoot msg) with
          | none => rfl
          | some li =>
            dsimp only
            by_cases hLi : sig.leafGlobalIdx ≠ li.1
            · rw [ite_eq_left hLi, ite_eq_left hLi]
            · rw [ite_eq_right hLi, ite_eq_right hLi]
              have hRecF : recoverProductionForsPk ov params pk.pkSeed
                  (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
                  (sig.leafGlobalIdx % 2 ^ params.subtreeHeight) li.2 sig.forsOpenings =
                recoverProductionForsPk suite params pk.pkSeed
                  (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
                  (sig.leafGlobalIdx % 2 ^ params.subtreeHeight) li.2 sig.forsOpenings := by
                rw [recoverProductionForsPk_eq, recoverProductionForsPk_eq]
                split
                · rfl
                · rw [hForsRoots]
                  cases recoverProductionForsTreeRoots suite params pk.pkSeed _ _ li.2
                      sig.forsOpenings 0 params.forsTrees with
                  | none => rfl
                  | some rs =>
                    dsimp only
                    rw [thTweakTl_eq, thTweakTl_eq,
                      secOverlaySuite_nonPrf_thCall _ _ _ tagThF_ne_tagPrf.2]
              rw [hRecF]
              cases recoverProductionForsPk suite params pk.pkSeed _ _ li.2 sig.forsOpenings with
              | none => rfl
              | some fpk => dsimp only; rw [hLayers]
    · simp only [↓reduceIte]
  · simp only [↓reduceIte]

/-- Ideal-PRF public key: secret leaves from `secFn`, public hashes from `suite`. -/
def derivePublicKeyIdealPrf (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (secFn : Spec.Bytes → Spec.Bytes) : PqPublicKey :=
  derivePublicKey (secOverlaySuite suite pkSeed secFn) params ⟨[], [], pkSeed⟩

/-- Ideal-PRF signing query: randomizers from `rfMsg`, secret leaves from `secFn`, public hashes
    from `suite`. -/
def signQueryIdealPrf (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (rfMsg secFn : Spec.Bytes → Spec.Bytes)
    (q : ProdSigningQuery) : Option PqHashSig :=
  signQueryWithRandFn (secOverlaySuite suite pkSeed secFn) params pkSeed [] rfMsg q

/-- **Hop-2 Idealized-PRF EUF-CMA Game (`ExecEufCmaIdealPrfGame`).**
    Both `skPrf` and `skSeed` are replaced inside the signer by uniform functions `rfMsg` and
    `rfSec`, while **`suite.rawHash` is 100% untouched** for the adversary and verifier! -/
def ExecEufCmaIdealPrfGame {n qHash qSign : Nat} (latchOn : Bool) (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeedOf : Fin n → List UInt8)
    (rfMsg rfSec : Fin n → Spec.Bytes → Spec.Bytes)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) : Spec.FinGame n where
  samplePos := hPos
  win ω :=
    let pkSeed := pkSeedOf ω
    let pk := derivePublicKeyIdealPrf suite params pkSeed (rfSec ω)
    let signFn := signQueryIdealPrf suite params pkSeed (rfMsg ω) (rfSec ω)
    let run := evalLatchedAdaptiveTree latchOn suite.rawHash signFn
      ((canonicalizeAdvOptRand (adv ω)).run pk) 0
    let msgStar := run.1.1
    let sigStar := run.1.2
    let log := signLogFromOracle signFn run.2
    verifyProductionPqHashSig suite params pk msgStar sigStar &&
      decide (msgStar ∉ log.map Prod.fst)

theorem secOverlaySuite_real_wotsPk {seedLen : Nat} (suite : TweakableHashSuite)
    (params : PqHashParams) (pkSeed skSeed : List UInt8) (hSeed : pkSeed.length = seedLen)
    (l : UInt32) (t : UInt64) (kp : Nat) :
    computeWotsPk (secOverlaySuite suite pkSeed (suitePrfSec seedLen suite skSeed)) params
      ⟨[], [], pkSeed⟩ l t kp =
    computeWotsPk suite params ⟨skSeed, [], pkSeed⟩ l t kp := by
  let ov := secOverlaySuite suite pkSeed (suitePrfSec seedLen suite skSeed)
  have hSteps : ∀ r k start x,
      wotsChainSteps ov pkSeed l t kp r start k x =
      wotsChainSteps suite pkSeed l t kp r start k x := by
    intro r k; induction k with
    | zero => intro start x; rw [wotsChainSteps_zero, wotsChainSteps_zero]
    | succ k' ih =>
      intro start x; rw [wotsChainSteps_succ, wotsChainSteps_succ]; dsimp only
      rw [thChainF_eq, thChainF_eq, secOverlaySuite_nonPrf_thCall _ _ _ tagThF_ne_tagPrf.1]
      exact ih (start + 1) _
  rw [computeWotsPk_eq, computeWotsPk_eq, thTweakTl_eq, thTweakTl_eq,
    secOverlaySuite_nonPrf_thCall _ _ _ tagThF_ne_tagPrf.2]
  congr 1; apply List.map_congr_left; intro r _
  rw [wotsSecretBase_eq, wotsSecretBase_eq, secOverlaySuite_tagPrf_empty,
    suitePrfSec_eq_thSecretPrf suite hSeed,
    padBytes32_of_len32 (by rw [thSecretPrf_eq]; exact thCall_length _ _ _ _ _), hSteps]

theorem secOverlaySuite_real_merkleNodeKp (suite : TweakableHashSuite)
    (pkSeed : List UInt8) (secFn : Spec.Bytes → Spec.Bytes)
    (l : UInt32) (t : UInt64) (kind : AdrsKind) (kp : UInt32)
    (f g : Nat → List UInt8) (hfg : ∀ i, f i = g i) :
    ∀ (ht n loc : Nat),
      computeMerkleNodeKp (secOverlaySuite suite pkSeed secFn) pkSeed l t kind kp f ht n loc =
        computeMerkleNodeKp suite pkSeed l t kind kp g ht n loc
  | 0, _, loc => by rw [computeMerkleNodeKp_zero, computeMerkleNodeKp_zero]; exact hfg loc
  | ht + 1, n, loc => by
    rw [computeMerkleNodeKp_succ, computeMerkleNodeKp_succ, thNodeH_eq, thNodeH_eq,
      secOverlaySuite_thCall_cons2,
      secOverlaySuite_real_merkleNodeKp suite pkSeed secFn l t kind kp f g hfg ht _ _,
      secOverlaySuite_real_merkleNodeKp suite pkSeed secFn l t kind kp f g hfg ht _ _]

theorem secOverlaySuite_real_authPathKp (suite : TweakableHashSuite)
    (pkSeed : List UInt8) (secFn : Spec.Bytes → Spec.Bytes)
    (l : UInt32) (t : UInt64) (kind : AdrsKind) (kp : UInt32)
    (f g : Nat → List UInt8) (hfg : ∀ i, f i = g i) :
    ∀ (ht root locBase locIdx : Nat),
      buildMerkleAuthPathKp (secOverlaySuite suite pkSeed secFn) pkSeed l t kind kp f ht root
        locBase locIdx =
      buildMerkleAuthPathKp suite pkSeed l t kind kp g ht root locBase locIdx
  | 0, _, _, _ => by rw [buildMerkleAuthPathKp.public_eq_1, buildMerkleAuthPathKp.public_eq_1]
  | ht + 1, root, locBase, locIdx => by
    rw [buildMerkleAuthPathKp.public_eq_2, buildMerkleAuthPathKp.public_eq_2]
    dsimp only
    split
    · rw [secOverlaySuite_real_merkleNodeKp suite pkSeed secFn l t kind kp f g hfg ht _ _,
        secOverlaySuite_real_authPathKp suite pkSeed secFn l t kind kp f g hfg ht _ _ _]
    · rw [secOverlaySuite_real_merkleNodeKp suite pkSeed secFn l t kind kp f g hfg ht _ _,
        secOverlaySuite_real_authPathKp suite pkSeed secFn l t kind kp f g hfg ht _ _ _]

theorem derivePublicKeyIdealPrf_real_eq {seedLen : Nat} (suite : TweakableHashSuite)
    (params : PqHashParams) (pkSeed skSeed : List UInt8) (hSeed : pkSeed.length = seedLen) :
    derivePublicKeyIdealPrf suite params pkSeed (suitePrfSec seedLen suite skSeed) =
      derivePublicKey suite params ⟨skSeed, [], pkSeed⟩ := by
  unfold derivePublicKeyIdealPrf derivePublicKey
  dsimp only
  rw [computeXmssSubtreeRoot_eq, computeXmssSubtreeRoot_eq,
    ← computeMerkleNodeKp_zero_eq, ← computeMerkleNodeKp_zero_eq]
  congr 1
  exact secOverlaySuite_real_merkleNodeKp suite pkSeed _ _ _ _ _ _ _
    (secOverlaySuite_real_wotsPk suite params pkSeed skSeed hSeed _ _) _ _ _

theorem signQueryIdealPrf_real_eq {seedLen : Nat} (suite : TweakableHashSuite)
    (params : PqHashParams) (pkSeed skSeed : List UInt8) (hSeed : pkSeed.length = seedLen)
    (rfMsg : Spec.Bytes → Spec.Bytes) (q : ProdSigningQuery) :
    signQueryIdealPrf suite params pkSeed rfMsg (suitePrfSec seedLen suite skSeed) q =
      signQueryWithRandFn suite params pkSeed skSeed rfMsg q := by
  let secFn := suitePrfSec seedLen suite skSeed
  let ov := secOverlaySuite suite pkSeed secFn
  have hPk := derivePublicKeyIdealPrf_real_eq suite params pkSeed skSeed hSeed
  change derivePublicKey ov params ⟨[], [], pkSeed⟩ = _ at hPk
  have hMu : ∀ pR m, thPreHash ov pkSeed pR m = thPreHash suite pkSeed pR m := fun pR m => by
    rw [thPreHash_eq, thPreHash_eq]
    exact secOverlaySuite_thCall_cons2 _ _ _ _ _ _ _ _ _
  have hForsLeafFn : ∀ t0 kp0 j u,
      forsIndexedLeafFn ov ⟨[], [], pkSeed⟩ t0 kp0 j u =
      forsIndexedLeafFn suite ⟨skSeed, [], pkSeed⟩ t0 kp0 j u := by
    intro t0 kp0 j u
    rw [forsIndexedLeafFn_eq, forsIndexedLeafFn_eq, forsIndexedLeafHash_eq, forsIndexedLeafHash_eq,
      forsIndexedSecretLeaf_eq, forsIndexedSecretLeaf_eq,
      secOverlaySuite_tagPrf_empty]
    dsimp only [secFn]
    rw [suitePrfSec_eq_thSecretPrf suite hSeed,
      padBytes32_of_len32 (by rw [thSecretPrf_eq]; exact thCall_length _ _ _ _ _),
      thChainF_eq, thChainF_eq, secOverlaySuite_nonPrf_thCall _ _ _ tagThF_ne_tagPrf.1]
  have hGrindLeaf : ∀ rR pR cur tI kpI c rem,
      grindTswLeafCounterAux ov params.w params.ell1 params.targetSum rR pkSeed pR cur tI kpI c rem =
      grindTswLeafCounterAux suite params.w params.ell1 params.targetSum rR pkSeed pR cur tI kpI c rem := by
    intro rR pR cur tI kpI c rem
    induction rem generalizing c with
    | zero => rw [grindTswLeafCounterAux_zero, grindTswLeafCounterAux_zero]
    | succ rem' ih =>
      rw [grindTswLeafCounterAux_succ, grindTswLeafCounterAux_succ]
      have hHm : thHashLeafMsg ov rR pkSeed pR cur tI kpI c =
          thHashLeafMsg suite rR pkSeed pR cur tI kpI c := by
        rw [thHashLeafMsg_eq, thHashLeafMsg_eq]
        exact secOverlaySuite_thCall_cons2 _ _ _ _ _ _ _ _ _
      rw [hHm, ih (c + 1)]
  have hGrindInt : ∀ pR cur lU tI kpI c rem,
      grindTswInternalCounterAux ov params.w params.ell1 params.targetSum pkSeed pR cur lU tI kpI c rem =
      grindTswInternalCounterAux suite params.w params.ell1 params.targetSum pkSeed pR cur lU tI kpI c rem := by
    intro pR cur lU tI kpI c rem
    induction rem generalizing c with
    | zero => rw [grindTswInternalCounterAux_zero, grindTswInternalCounterAux_zero]
    | succ rem' ih =>
      rw [grindTswInternalCounterAux_succ, grindTswInternalCounterAux_succ]
      have hHi : thHashInternalNode ov pkSeed pR cur lU tI kpI c =
          thHashInternalNode suite pkSeed pR cur lU tI kpI c := by
        rw [thHashInternalNode_eq, thHashInternalNode_eq]
        exact secOverlaySuite_thCall_cons2 _ _ _ _ _ _ _ _ _
      rw [hHi, ih (c + 1)]
  have hSignLayers : ∀ pR rR lI gI cur rem,
      signProductionHypertreeLayers ov params ⟨[], [], pkSeed⟩ pR rR q.grindLimit lI gI cur rem =
      signProductionHypertreeLayers suite params ⟨skSeed, [], pkSeed⟩ pR rR q.grindLimit lI gI cur rem := by
    intro pR rR lI gI cur rem
    induction rem generalizing lI gI cur with
    | zero => rw [signProductionHypertreeLayers_zero, signProductionHypertreeLayers_zero]
    | succ rem' ih =>
      rw [signProductionHypertreeLayers_succ, signProductionHypertreeLayers_succ]
      dsimp only
      have hG : (if params.statefulJorts && decide (lI = 0) then
          grindTswLeafCounterAux ov params.w params.ell1 params.targetSum rR pkSeed pR cur
            (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (gI % 2 ^ params.subtreeHeight)) 0 q.grindLimit
        else
          grindTswInternalCounterAux ov params.w params.ell1 params.targetSum pkSeed pR cur
            (UInt32.ofNat lI) (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (gI % 2 ^ params.subtreeHeight)) 0 q.grindLimit) =
        (if params.statefulJorts && decide (lI = 0) then
          grindTswLeafCounterAux suite params.w params.ell1 params.targetSum rR pkSeed pR cur
            (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (gI % 2 ^ params.subtreeHeight)) 0 q.grindLimit
        else
          grindTswInternalCounterAux suite params.w params.ell1 params.targetSum pkSeed pR cur
            (UInt32.ofNat lI) (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (gI % 2 ^ params.subtreeHeight)) 0 q.grindLimit) := by
        split
        · exact hGrindLeaf _ _ _ _ _ _ _
        · exact hGrindInt _ _ _ _ _ _ _
      rw [hG]
      cases (if params.statefulJorts && decide (lI = 0) then
          grindTswLeafCounterAux suite params.w params.ell1 params.targetSum rR pkSeed pR cur
            (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (gI % 2 ^ params.subtreeHeight)) 0 q.grindLimit
        else
          grindTswInternalCounterAux suite params.w params.ell1 params.targetSum pkSeed pR cur
            (UInt32.ofNat lI) (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (gI % 2 ^ params.subtreeHeight)) 0 q.grindLimit) with
      | none => rfl
      | some triple =>
        rcases triple with ⟨ctr, digits, _⟩
        dsimp only
        have hCh : ∀ r,
            wotsChainSteps ov pkSeed (UInt32.ofNat lI)
              (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
              (gI % 2 ^ params.subtreeHeight) r 0 (digits.getD r 0)
              (wotsSecretBase ov ⟨[], [], pkSeed⟩ (UInt32.ofNat lI)
                (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
                (gI % 2 ^ params.subtreeHeight) r) =
            wotsChainSteps suite pkSeed (UInt32.ofNat lI)
              (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
              (gI % 2 ^ params.subtreeHeight) r 0 (digits.getD r 0)
              (wotsSecretBase suite ⟨skSeed, [], pkSeed⟩ (UInt32.ofNat lI)
                (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
                (gI % 2 ^ params.subtreeHeight) r) := by
          intro r
          rw [wotsSecretBase_eq, wotsSecretBase_eq, secOverlaySuite_tagPrf_empty]
          dsimp only [secFn]
          rw [suitePrfSec_eq_thSecretPrf suite hSeed,
            padBytes32_of_len32 (by rw [thSecretPrf_eq]; exact thCall_length _ _ _ _ _)]
          generalize digits.getD r 0 = d
          generalize thSecretPrf suite pkSeed skSeed _ = x0
          suffices ∀ k st x, wotsChainSteps ov pkSeed (UInt32.ofNat lI)
              (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
              (gI % 2 ^ params.subtreeHeight) r st k x =
            wotsChainSteps suite pkSeed (UInt32.ofNat lI)
              (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
              (gI % 2 ^ params.subtreeHeight) r st k x from this d 0 x0
          intro k; induction k with
          | zero => intro st x; rw [wotsChainSteps_zero, wotsChainSteps_zero]
          | succ k' ihK =>
            intro st x; rw [wotsChainSteps_succ, wotsChainSteps_succ]; dsimp only
            rw [thChainF_eq, thChainF_eq, secOverlaySuite_nonPrf_thCall _ _ _ tagThF_ne_tagPrf.1]
            exact ihK (st + 1) _
        have hSubR : computeXmssSubtreeRoot ov params ⟨[], [], pkSeed⟩ (UInt32.ofNat lI)
            (UInt64.ofNat (gI / 2 ^ params.subtreeHeight)) =
          computeXmssSubtreeRoot suite params ⟨skSeed, [], pkSeed⟩ (UInt32.ofNat lI)
            (UInt64.ofNat (gI / 2 ^ params.subtreeHeight)) := by
          rw [computeXmssSubtreeRoot_eq, computeXmssSubtreeRoot_eq,
            ← computeMerkleNodeKp_zero_eq, ← computeMerkleNodeKp_zero_eq]
          exact secOverlaySuite_real_merkleNodeKp suite pkSeed secFn _ _ _ _ _ _
            (secOverlaySuite_real_wotsPk suite params pkSeed skSeed hSeed _ _) _ _ _
        have hAp := secOverlaySuite_real_authPathKp suite pkSeed secFn (UInt32.ofNat lI)
          (UInt64.ofNat (gI / 2 ^ params.subtreeHeight)) .tree 0 _ _
          (secOverlaySuite_real_wotsPk suite params pkSeed skSeed hSeed
            (UInt32.ofNat lI) (UInt64.ofNat (gI / 2 ^ params.subtreeHeight)))
          params.subtreeHeight 0 0 (gI % 2 ^ params.subtreeHeight)
        have hMapEq : ((List.range params.ell1).map fun r =>
            wotsChainSteps ov pkSeed (UInt32.ofNat lI)
              (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
              (gI % 2 ^ params.subtreeHeight) r 0 (digits.getD r 0)
              (wotsSecretBase ov ⟨[], [], pkSeed⟩ (UInt32.ofNat lI)
                (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
                (gI % 2 ^ params.subtreeHeight) r)) =
          ((List.range params.ell1).map fun r =>
            wotsChainSteps suite pkSeed (UInt32.ofNat lI)
              (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
              (gI % 2 ^ params.subtreeHeight) r 0 (digits.getD r 0)
              (wotsSecretBase suite ⟨skSeed, [], pkSeed⟩ (UInt32.ofNat lI)
                (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
                (gI % 2 ^ params.subtreeHeight) r)) :=
          List.map_congr_left (fun r _ => hCh r)
        rw [hMapEq, hAp, hSubR, ih]
  have hCore : ∀ pk mu rR leaf fIdxs,
      signProductionHypertreeCore ov params ⟨[], [], pkSeed⟩ pk q.message mu rR leaf fIdxs
        q.grindLimit =
      signProductionHypertreeCore suite params ⟨skSeed, [], pkSeed⟩ pk q.message mu rR leaf fIdxs
        q.grindLimit := by
    intro pk mu rR leaf fIdxs
    rw [signProductionHypertreeCore_def, signProductionHypertreeCore_def]
    dsimp only
    by_cases hSt : params.statefulJorts
    · simp only [hSt, ↓reduceIte]
      rw [hSignLayers]
      cases signProductionHypertreeLayers suite params ⟨skSeed, [], pkSeed⟩ pk.pkRoot rR
          q.grindLimit 0 leaf mu params.numLayers with
      | none => rfl
      | some ls => dsimp only; rw [secOverlaySuite_verify_eq]
    · simp only [hSt, Bool.false_eq_true, ↓reduceIte]
      cases fIdxs with
      | none => rfl
      | some idxs =>
        dsimp only
        have hOps : buildProductionForsOpenings ov params ⟨[], [], pkSeed⟩
            (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight))
            (leaf % 2 ^ params.subtreeHeight) idxs =
          buildProductionForsOpenings suite params ⟨skSeed, [], pkSeed⟩
            (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight))
            (leaf % 2 ^ params.subtreeHeight) idxs := by
          rw [buildProductionForsOpenings_def, buildProductionForsOpenings_def]
          dsimp only
          apply List.map_congr_left; intro j _
          have hS : forsIndexedSecretLeaf ov ⟨[], [], pkSeed⟩
              (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight))
              (leaf % 2 ^ params.subtreeHeight) j (idxs.getD j 0) =
            forsIndexedSecretLeaf suite ⟨skSeed, [], pkSeed⟩
              (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight))
              (leaf % 2 ^ params.subtreeHeight) j (idxs.getD j 0) := by
            rw [forsIndexedSecretLeaf_eq, forsIndexedSecretLeaf_eq,
              secOverlaySuite_tagPrf_empty]
            dsimp only [secFn]
            rw [suitePrfSec_eq_thSecretPrf suite hSeed,
              padBytes32_of_len32 (by rw [thSecretPrf_eq]; exact thCall_length _ _ _ _ _)]
          rw [hS, secOverlaySuite_real_authPathKp suite pkSeed secFn 0 _ .forsTree _ _ _
            (hForsLeafFn _ _ j)]
        have hFpk : computeProductionForsPk ov params ⟨[], [], pkSeed⟩
            (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight))
            (leaf % 2 ^ params.subtreeHeight) =
          computeProductionForsPk suite params ⟨skSeed, [], pkSeed⟩
            (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight))
            (leaf % 2 ^ params.subtreeHeight) := by
          rw [computeProductionForsPk_eq, computeProductionForsPk_eq, thTweakTl_eq, thTweakTl_eq,
            secOverlaySuite_nonPrf_thCall _ _ _ tagThF_ne_tagPrf.2]
          congr 1; apply List.map_congr_left; intro j _
          exact secOverlaySuite_real_merkleNodeKp suite pkSeed secFn 0 _ .forsTree _ _ _
            (hForsLeafFn _ _ j) _ _ _
        rw [hOps, hFpk, hSignLayers]
        cases signProductionHypertreeLayers suite params ⟨skSeed, [], pkSeed⟩ pk.pkRoot rR
            q.grindLimit 0 leaf _ params.numLayers with
        | none => rfl
        | some ls => dsimp only; rw [secOverlaySuite_verify_eq]
  unfold signQueryIdealPrf
  rw [signQueryWithRandFn.public_eqs, signQueryWithRandFn.public_eqs,
    signCoreWithRand.public_eqs, signCoreWithRand.public_eqs]
  dsimp only
  have hPkSeed0 : (derivePublicKey suite params ⟨skSeed, [], pkSeed⟩).pkSeed = pkSeed := by
    unfold derivePublicKey; rfl
  rw [hPk, hPkSeed0, hMu]
  by_cases hSt : params.statefulJorts
  · simp only [hSt, ↓reduceIte]
    split
    · rfl
    · exact hCore _ _ _ _ _
  · simp only [hSt, Bool.false_eq_true, ↓reduceIte]
    split
    · rfl
    · have hXof : ∀ rR pR mu first n,
          thXofMsgBlocks ov rR pkSeed pR mu first n =
          thXofMsgBlocks suite rR pkSeed pR mu first n := by
        intro rR pR mu first n; induction n generalizing first with
        | zero => rw [thXofMsgBlocks_zero, thXofMsgBlocks_zero]
        | succ n' ihX =>
          rw [thXofMsgBlocks_succ, thXofMsgBlocks_succ, secOverlaySuite_thCall_cons2, ihX]
      have hDer : ∀ rR pR mu,
          deriveProductionStatelessInputs ov params rR pkSeed pR mu =
          deriveProductionStatelessInputs suite params rR pkSeed pR mu := by
        intro rR pR mu
        rw [deriveProductionStatelessInputs_eq, deriveProductionStatelessInputs_eq]
        dsimp only
        rw [thXofMsg_eq, thXofMsg_eq, hXof]
      rw [hDer]
      cases deriveProductionStatelessInputs suite params _ pkSeed _ _ with
      | none => rfl
      | some li => exact hCore _ _ _ _ _

theorem ExecEufCmaIdealPrfGame_win {n qHash qSign : Nat} (latchOn : Bool) (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeedOf : Fin n → List UInt8)
    (rfMsg rfSec : Fin n → Spec.Bytes → Spec.Bytes)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) (ω : Fin n) :
    (ExecEufCmaIdealPrfGame latchOn hPos suite params pkSeedOf rfMsg rfSec adv).win ω =
      (let pkSeed := pkSeedOf ω
       let pk := derivePublicKeyIdealPrf suite params pkSeed (rfSec ω)
       let signFn := signQueryIdealPrf suite params pkSeed (rfMsg ω) (rfSec ω)
       let run := evalLatchedAdaptiveTree latchOn suite.rawHash signFn
         ((canonicalizeAdvOptRand (adv ω)).run pk) 0
       let log := signLogFromOracle signFn run.2
       verifyProductionPqHashSig suite params pk run.1.1 run.1.2 &&
         decide (run.1.1 ∉ log.map Prod.fst)) := by
  unfold ExecEufCmaIdealPrfGame; rfl

#export_eqns suitePrfSec derivePublicKeyIdealPrf signQueryIdealPrf

#verify_constructive
  Qsag.suitePrfSec_eq_thSecretPrf
  Qsag.secOverlaySuite_verify_eq
  Qsag.derivePublicKeyIdealPrf_real_eq
  Qsag.signQueryIdealPrf_real_eq

end Qsag
end

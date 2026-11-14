module
/-
# Qsag.ThresholdMpc — Distributed Post-Quantum Threshold Signing (`Depth = 1 + w`, RSS & Shamir)

Self-contained Lean 4.35 formalization of the distributed threshold MPC signing engine (`0` Mathlib,
`0` sorry, `0` cleartext secret reconstruction during key generation or signing; malicious MACs,
DKG, resharing, and Simplex quorum safety live in `Qsag.MaliciousSecurity`):
1. **`Depth = 1 + w` Public/Secret Cut (`PqHashMpcOracles`, `evalCutBatchSignMpc_eq_evalSingleSign`,
   `transcript_shape_depends_only_on_public_params`)**.
2. **3-Party `2-of-3 RSS` Word-Level `Keccak-f[1600]`, `SHAKE256` & `cSHAKE256`
   (`reconstructRssKState_mpcKeccakF1600Rss`, `reconstructRssBytes_mpcShake256SharedRss`,
   `rss_thresholdSlhSign_eq_slhSignInternal`, `rss_thresholdPqHashSign_eq_evalSingleSign`)**.
3. **Arbitrary $t$-of-$n$ Shamir `Π_pow7` S-Box & Share-Level `Poseidon2` Threshold Signing
   (`lagrangeCombine_mpcPow7Shares_eq_sbox7`, `evalSharedPow7Binomial_complete`,
   `evalSharedPoseidon2Perm_simulates`, `mkShamirPoseidon2MpcOracles_matchesKey`,
   `shamir_poseidon2_thresholdSign_eq_evalSingleSign`)**.
4. Checked stateless threshold path equal to `evalStatelessCheckedSign`
   (`thresholdStatelessCheckedSign_eq_evalStatelessCheckedSign`).
5. Threshold FIPS 205 output equal to the single-signer output for every correct run
   (`threshold_sig_perfectly_indistinguishable_from_single_signer`): share-level `Keccak`/`SHAKE256`
   for 2-of-3 RSS (`SlhThresholdRun.ofRss`), and quorum-recombination `SlhMpcOracles` interface for
   `(t, n)` Shamir FIPS 205 (`SlhThresholdRun.ofShamir`, while `(t, n)` Shamir share-level `Poseidon2`
   signing is realized end-to-end by `mkShamirPoseidon2MpcOracles` in Section 3).
-/

public import Qsag.Goldilocks
public import Qsag.BinaryTower
public import Qsag.Keccak
public import Qsag.Poseidon2
public import Qsag.UcGames
public import Qsag.HashSigs
public import Qsag.Fips205
public import Qsag.Preprocessing

public import Qsag.Constructive
import all Qsag.Goldilocks
import all Qsag.Poseidon2
import all Qsag.UcGames
import all Qsag.Preprocessing

public section
namespace Qsag

set_option autoImplicit false

/-! ## 1. `Depth = 1 + w` Public/Secret Cut (`PqHashMpcOracles` & `evalCutBatchSignMpc`) -/

/-- Build a length-`rem` WOTS+ / `TSW` chain table `[X^0, X^1, ..., X^{rem-1}]` inside the MPC cut. -/
def buildMpcChainTable (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp chain startStep : Nat) :
    Nat → List UInt8 → List (List UInt8)
  | 0, _ => []
  | rem + 1, cur =>
    let adrs : HashAdrs := ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat chain, UInt32.ofNat startStep⟩
    cur :: buildMpcChainTable suite pkSeed layer tree kp chain (startStep + 1) rem
             (thChainF suite pkSeed adrs cur)

/-- Open ONLY the public target digit step `digit` from a secret-shared chain table. -/
def ramOpenChainStep (table : List (List UInt8)) (digit : Nat) : List UInt8 :=
  table.getD digit []

/-- **`ramOpenChainStep_eq_wotsChainSteps`**: RAM selection at public digit `digit < rem` on the
    `Depth = 1 + w` chain table equals `wotsChainSteps ... startStep digit cur` bit-for-bit. -/
theorem ramOpenChainStep_eq_wotsChainSteps
    (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp chain : Nat) :
    ∀ (rem startStep digit : Nat) (cur : List UInt8),
      digit < rem →
      ramOpenChainStep (buildMpcChainTable suite pkSeed layer tree kp chain startStep rem cur) digit =
        wotsChainSteps suite pkSeed layer tree kp chain startStep digit cur
  | 0, _, _, _, hLt => by omega
  | rem + 1, startStep, 0, cur, _ => by
    rw [wotsChainSteps_zero]
    rfl
  | rem + 1, startStep, d + 1, cur, hLt => by
    rw [wotsChainSteps_succ]
    simp only [buildMpcChainTable, ramOpenChainStep, List.getD_cons_succ]
    exact ramOpenChainStep_eq_wotsChainSteps suite pkSeed layer tree kp chain rem (startStep + 1) d _ (by omega)

/-- Distributed MPC oracle interface for `Corduroy`, `SLH-DSA`, and `Poseidon2` hypertree signing:
    `skSeed` and `skPrf` remain secret-shared across the committee and are NEVER reconstructed;
    only the 4 public outputs at the `Depth = 1 + w` cut boundary are opened. -/
structure PqHashMpcOracles where
  /-- Evaluates `thPrfMsg suite skPrf optRand mu` over shares (`Depth = 1`) and opens ONLY `rRand`. -/
  evalPrfMsg       : List UInt8 → List UInt8 → List UInt8
  /-- Evaluates `wotsChainSteps ... 0 steps (wotsSecretBase ...)` over shares (`Depth = 1 + steps ≤ w`)
      and opens ONLY the selected chain value (`steps = d_r` or public endpoint `w - 1`). -/
  evalWotsChainEnd : UInt32 → UInt64 → Nat → Nat → Nat → List UInt8
  /-- Evaluates `forsSecretLeaf` over shares (`Depth = 1`) and opens ONLY signature-disclosed FORS leaves. -/
  evalForsReveal   : UInt64 → Nat → Nat → List UInt8
  /-- Evaluates `forsLeafFn` over shares (`Depth = 2`) and opens ONLY the public FORS leaf hash. -/
  evalForsLeafHash : UInt64 → Nat → Nat → List UInt8

/-- Soundness predicate stating that `o : PqHashMpcOracles` faithfully evaluates the 4 cut-boundary
    functions of `sk : PqSecretKey` under `suite : TweakableHashSuite`. -/
def PqHashMpcOracles.MatchesKey (o : PqHashMpcOracles) (suite : TweakableHashSuite) (sk : PqSecretKey) : Prop :=
  (∀ optRand mu, o.evalPrfMsg optRand mu = thPrfMsg suite sk.skPrf optRand mu) ∧
  (∀ layer tree kp chain steps,
    o.evalWotsChainEnd layer tree kp chain steps =
      wotsChainSteps suite sk.pkSeed layer tree kp chain 0 steps
        (wotsSecretBase suite sk layer tree kp chain)) ∧
  (∀ tree0 kp0 globalU,
    o.evalForsReveal tree0 kp0 globalU = forsSecretLeaf suite sk tree0 kp0 globalU) ∧
  (∀ tree0 kp0 globalU,
    o.evalForsLeafHash tree0 kp0 globalU = forsLeafFn suite sk tree0 kp0 globalU)

def mpcComputeWotsPk (suite : TweakableHashSuite) (params : PqHashParams)
    (o : PqHashMpcOracles) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp : Nat) : List UInt8 :=
  thTweakTl suite pkSeed ⟨layer, tree, .wotsPk, UInt32.ofNat kp, 0, 0⟩
    ((List.range params.ell1).map fun r => o.evalWotsChainEnd layer tree kp r (params.w - 1))

def mpcComputeXmssSubtreeRoot (suite : TweakableHashSuite) (params : PqHashParams)
    (o : PqHashMpcOracles) (pkSeed : List UInt8) (layer : UInt32) (treeIdx : UInt64) : List UInt8 :=
  computeMerkleNode suite pkSeed layer treeIdx .tree
    (mpcComputeWotsPk suite params o pkSeed layer treeIdx) params.subtreeHeight 0

/-- Distributed key generation deriving `(pkSeed, pkRoot)` solely via `o : PqHashMpcOracles`
    without ever receiving or reconstructing `PqSecretKey`. -/
def derivePublicKeyMpc (suite : TweakableHashSuite) (params : PqHashParams)
    (o : PqHashMpcOracles) (pkSeed : List UInt8) : PqPublicKey :=
  let topLayer := UInt32.ofNat (params.numLayers - 1)
  { pkSeed := pkSeed
    pkRoot := mpcComputeXmssSubtreeRoot suite params o pkSeed topLayer 0 }

def mpcBuildForsOpenings (suite : TweakableHashSuite) (params : PqHashParams)
    (o : PqHashMpcOracles) (pkSeed : List UInt8)
    (tree0 : UInt64) (kp0 : Nat) (hmsg0 : List UInt8) : List ForsTreeOpening :=
  let idxs := deriveForsIndices params.forsTrees params.forsHeight hmsg0
  let leafFn := o.evalForsLeafHash tree0 kp0
  (List.range params.forsTrees).map fun j =>
    let idxJ := idxs.getD j 0
    let globalU := j * (2 ^ params.forsHeight) + idxJ
    { secretVal := o.evalForsReveal tree0 kp0 globalU
      authPath  := buildMerkleAuthPath suite pkSeed 0 tree0 .forsTree leafFn params.forsHeight j idxJ }

def mpcComputeForsPk (suite : TweakableHashSuite) (params : PqHashParams)
    (o : PqHashMpcOracles) (pkSeed : List UInt8) (tree0 : UInt64) (kp0 : Nat) : List UInt8 :=
  let leafFn := o.evalForsLeafHash tree0 kp0
  let roots := (List.range params.forsTrees).map fun j =>
    computeMerkleNode suite pkSeed 0 tree0 .forsTree leafFn params.forsHeight j
  thTweakTl suite pkSeed ⟨0, tree0, .forsRoots, UInt32.ofNat kp0, 0, 0⟩ roots

def mpcSignHypertreeLayers (suite : TweakableHashSuite) (params : PqHashParams)
    (o : PqHashMpcOracles) (pkSeed pkRoot layer0Rand : List UInt8) (maxGrind : Nat) :
    Nat → Nat → List UInt8 → Nat → Option (List LayerXmssSig)
  | _, _, _, 0 => some []
  | layerIdx, globalIdx, curRoot, rem + 1 =>
    let subLeaves := 2 ^ params.subtreeHeight
    let kpIdx := globalIdx % subLeaves
    let kpU32 := UInt32.ofNat kpIdx
    let treeIdxNat := globalIdx / subLeaves
    let treeIdx := UInt64.ofNat treeIdxNat
    let layerU32 := UInt32.ofNat layerIdx
    match grindTswCounterAux suite params.w params.ell1 params.targetSum
            layer0Rand pkSeed pkRoot curRoot layerU32 treeIdx kpU32 0 maxGrind with
    | none => none
    | some (ctr, digits, _) =>
      let wotsChains := (List.range params.ell1).map fun r =>
        o.evalWotsChainEnd layerU32 treeIdx kpIdx r (digits.getD r 0)
      let authPath := buildMerkleAuthPath suite pkSeed layerU32 treeIdx .tree
        (mpcComputeWotsPk suite params o pkSeed layerU32 treeIdx) params.subtreeHeight 0 kpIdx
      let nextRoot := mpcComputeXmssSubtreeRoot suite params o pkSeed layerU32 treeIdx
      match mpcSignHypertreeLayers suite params o pkSeed pkRoot [] maxGrind (layerIdx + 1) treeIdxNat nextRoot rem with
      | none => none
      | some restSigs =>
        some ({ tswCtr := ctr, wotsChains := wotsChains, authPath := authPath } :: restSigs)

/-- **Distributed `Depth = 1 + w` Cut Signer (`evalCutBatchSignMpc`)**:
    Takes ONLY `o : PqHashMpcOracles` and public `pk : PqPublicKey` (`PqSecretKey` never appears!).
    `[P0-02]`/`[P1-04]`: binds `kp0` in `grindTswCounterAux` and signs static `forsPk` + all upper
    XMSS layers deterministically (`layer0Rand = []`). -/
def evalCutBatchSignMpc (suite : TweakableHashSuite) (params : PqHashParams)
    (o : PqHashMpcOracles) (pk : PqPublicKey) (msg optRand : List UInt8)
    (leafGlobalIdx maxGrind : Nat) : Option PqHashSig :=
  if !(params.wellFormed) then none
  else if !(leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight)) then none
  else
    let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
    let rRand := o.evalPrfMsg optRand mu
    if params.statefulJorts then
      match mpcSignHypertreeLayers suite params o pk.pkSeed pk.pkRoot rRand maxGrind 0 leafGlobalIdx mu params.numLayers with
      | none => none
      | some layerSigs =>
        some { rRand := rRand, msgTswCtr := 0, leafGlobalIdx := leafGlobalIdx, forsOpenings := [], layerSigs := layerSigs }
    else
      let subLeaves := 2 ^ params.subtreeHeight
      let kp0 := leafGlobalIdx % subLeaves
      let kp0U32 := UInt32.ofNat kp0
      let tree0 := UInt64.ofNat (leafGlobalIdx / subLeaves)
      match grindTswCounterAux suite params.w params.ell1 params.targetSum
              rRand pk.pkSeed pk.pkRoot mu 0 tree0 kp0U32 0 maxGrind with
      | none => none
      | some (ctr0, _, hmsg0) =>
        let forsOps := mpcBuildForsOpenings suite params o pk.pkSeed tree0 kp0 hmsg0
        let forsPk := mpcComputeForsPk suite params o pk.pkSeed tree0 kp0
        match mpcSignHypertreeLayers suite params o pk.pkSeed pk.pkRoot [] maxGrind 0 leafGlobalIdx forsPk params.numLayers with
        | none => none
        | some layerSigs =>
          some { rRand := rRand, msgTswCtr := ctr0, leafGlobalIdx := leafGlobalIdx, forsOpenings := forsOps, layerSigs := layerSigs }

private theorem computeMerkleNode_congr_leafFn (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind) (f g : Nat → List UInt8)
    (hfg : ∀ u, f u = g u) :
    ∀ (h nodeIdx : Nat),
      computeMerkleNode suite pkSeed layer tree nodeKind f h nodeIdx =
        computeMerkleNode suite pkSeed layer tree nodeKind g h nodeIdx
  | 0, nodeIdx => by rw [computeMerkleNode_zero, computeMerkleNode_zero, hfg]
  | h + 1, nodeIdx => by
    rw [computeMerkleNode_succ, computeMerkleNode_succ,
        computeMerkleNode_congr_leafFn suite pkSeed layer tree nodeKind f g hfg h (2 * nodeIdx),
        computeMerkleNode_congr_leafFn suite pkSeed layer tree nodeKind f g hfg h (2 * nodeIdx + 1)]

private theorem buildMerkleAuthPath_congr_leafFn (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind) (f g : Nat → List UInt8)
    (hfg : ∀ u, f u = g u) :
    ∀ (h nodeIdx localIdx : Nat),
      buildMerkleAuthPath suite pkSeed layer tree nodeKind f h nodeIdx localIdx =
        buildMerkleAuthPath suite pkSeed layer tree nodeKind g h nodeIdx localIdx
  | 0, _, _ => by rw [buildMerkleAuthPath_zero, buildMerkleAuthPath_zero]
  | h + 1, nodeIdx, localIdx => by
    rw [buildMerkleAuthPath_succ, buildMerkleAuthPath_succ]
    split <;> simp only [List.cons.injEq] <;>
      exact ⟨computeMerkleNode_congr_leafFn suite pkSeed layer tree nodeKind f g hfg h _,
             buildMerkleAuthPath_congr_leafFn suite pkSeed layer tree nodeKind f g hfg h _ _⟩

private theorem mpcComputeWotsPk_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (o : PqHashMpcOracles) (sk : PqSecretKey) (hMatch : o.MatchesKey suite sk)
    (layer : UInt32) (tree : UInt64) (kp : Nat) :
    mpcComputeWotsPk suite params o sk.pkSeed layer tree kp = computeWotsPk suite params sk layer tree kp := by
  unfold mpcComputeWotsPk
  rw [computeWotsPk_eq]
  simp [hMatch.2.1]

private theorem mpcComputeXmssSubtreeRoot_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (o : PqHashMpcOracles) (sk : PqSecretKey) (hMatch : o.MatchesKey suite sk)
    (layer : UInt32) (tree : UInt64) :
    mpcComputeXmssSubtreeRoot suite params o sk.pkSeed layer tree =
      computeXmssSubtreeRoot suite params sk layer tree := by
  unfold mpcComputeXmssSubtreeRoot
  rw [computeXmssSubtreeRoot_eq]
  exact computeMerkleNode_congr_leafFn suite sk.pkSeed layer tree .tree _ _
    (mpcComputeWotsPk_eq suite params o sk hMatch layer tree) _ _

private theorem mpcSignHypertreeLayers_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (o : PqHashMpcOracles) (sk : PqSecretKey) (hMatch : o.MatchesKey suite sk)
    (pkRoot : List UInt8) (maxGrind : Nat) :
    ∀ (rem layerIdx globalIdx : Nat) (layer0Rand curRoot : List UInt8),
      mpcSignHypertreeLayers suite params o sk.pkSeed pkRoot layer0Rand maxGrind layerIdx globalIdx curRoot rem =
        signHypertreeLayers suite params sk pkRoot layer0Rand maxGrind layerIdx globalIdx curRoot rem
  | 0, layerIdx, globalIdx, layer0Rand, curRoot => by rw [mpcSignHypertreeLayers, signHypertreeLayers_zero]
  | rem + 1, layerIdx, globalIdx, layer0Rand, curRoot => by
    rw [mpcSignHypertreeLayers, signHypertreeLayers_succ]
    dsimp only
    cases grindTswCounterAux suite params.w params.ell1 params.targetSum layer0Rand sk.pkSeed pkRoot curRoot
        (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
        (UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight)) 0 maxGrind with
    | none => rfl
    | some triple =>
      rcases triple with ⟨ctr, digits, hm⟩
      dsimp only
      let layerU32 := UInt32.ofNat layerIdx
      let treeU64 := UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)
      have hPath := buildMerkleAuthPath_congr_leafFn suite sk.pkSeed layerU32 treeU64 .tree
        (mpcComputeWotsPk suite params o sk.pkSeed layerU32 treeU64)
        (computeWotsPk suite params sk layerU32 treeU64)
        (mpcComputeWotsPk_eq suite params o sk hMatch layerU32 treeU64)
        params.subtreeHeight 0 (globalIdx % 2 ^ params.subtreeHeight)
      have hNext := mpcComputeXmssSubtreeRoot_eq suite params o sk hMatch layerU32 treeU64
      dsimp only [layerU32, treeU64] at hPath hNext
      rw [hPath, hNext,
          mpcSignHypertreeLayers_eq suite params o sk hMatch pkRoot maxGrind rem (layerIdx + 1)
            (globalIdx / 2 ^ params.subtreeHeight) []]
      cases signHypertreeLayers suite params sk pkRoot [] maxGrind (layerIdx + 1)
          (globalIdx / 2 ^ params.subtreeHeight) _ rem with
      | none => rfl
      | some _ => simp [hMatch.2.1]

/-- **Public/Secret Cut Bit-Identity (`evalCutBatchSignMpc_eq_evalSingleSign`)**:
    Whenever `o : PqHashMpcOracles` matches `sk` (`o.MatchesKey suite sk`), distributed keygen
    and signing across `Corduroy`, `SLH-DSA`, and `Poseidon2` hypertree suites emit the **exact same**
    public key and signature as single-party `derivePublicKey` / `evalSingleSign`, and every
    emitted signature passes `verifyPqHashSig`! -/
theorem evalCutBatchSignMpc_eq_evalSingleSign
    (suite : TweakableHashSuite) (params : PqHashParams)
    (o : PqHashMpcOracles) (sk : PqSecretKey)
    (msg optRand : List UInt8) (leafGlobalIdx maxGrind : Nat)
    (hMatch : o.MatchesKey suite sk) :
    derivePublicKeyMpc suite params o sk.pkSeed = derivePublicKey suite params sk ∧
    evalCutBatchSignMpc suite params o (derivePublicKeyMpc suite params o sk.pkSeed)
      msg optRand leafGlobalIdx maxGrind =
      evalSingleSign suite params sk msg optRand leafGlobalIdx maxGrind ∧
    (∀ sig,
      evalCutBatchSignMpc suite params o (derivePublicKeyMpc suite params o sk.pkSeed)
        msg optRand leafGlobalIdx maxGrind = some sig →
      verifyPqHashSig suite params (derivePublicKeyMpc suite params o sk.pkSeed) msg sig = true) := by
  have hPk : derivePublicKeyMpc suite params o sk.pkSeed = derivePublicKey suite params sk := by
    unfold derivePublicKeyMpc derivePublicKey
    simp [mpcComputeXmssSubtreeRoot_eq suite params o sk hMatch]
  have hSign :
      evalCutBatchSignMpc suite params o (derivePublicKey suite params sk) msg optRand leafGlobalIdx maxGrind =
        evalSingleSign suite params sk msg optRand leafGlobalIdx maxGrind := by
    unfold evalCutBatchSignMpc evalSingleSign
    dsimp only [derivePublicKey]
    by_cases hWf : params.wellFormed = true
    · simp only [hWf, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hLeaf : leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight)
      · simp only [hLeaf, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hMatch.1]
        by_cases hMode : params.statefulJorts = true
        · simp only [hMode, ↓reduceIte]
          rw [mpcSignHypertreeLayers_eq suite params o sk hMatch]
          rfl
        · simp only [hMode, Bool.false_eq_true, ↓reduceIte]
          cases grindTswCounterAux suite params.w params.ell1 params.targetSum _ _ _ _ 0 _ _ 0 maxGrind with
          | none => rfl
          | some tr0 =>
            rcases tr0 with ⟨ctr0, _, hmsg0⟩
            dsimp only
            have hForsOps : mpcBuildForsOpenings suite params o sk.pkSeed
                (UInt64.ofNat (leafGlobalIdx / 2 ^ params.subtreeHeight))
                (leafGlobalIdx % 2 ^ params.subtreeHeight) hmsg0 =
                buildForsOpenings suite params sk
                  (UInt64.ofNat (leafGlobalIdx / 2 ^ params.subtreeHeight))
                  (leafGlobalIdx % 2 ^ params.subtreeHeight) hmsg0 := by
              unfold mpcBuildForsOpenings
              rw [buildForsOpenings_eq]
              dsimp only
              apply List.map_congr_left
              intro j _
              simp only [hMatch.2.2.1]
              congr 1
              exact buildMerkleAuthPath_congr_leafFn suite sk.pkSeed 0 _ .forsTree _ _
                (hMatch.2.2.2 _ _) params.forsHeight j _
            have hForsPk : mpcComputeForsPk suite params o sk.pkSeed
                (UInt64.ofNat (leafGlobalIdx / 2 ^ params.subtreeHeight))
                (leafGlobalIdx % 2 ^ params.subtreeHeight) =
                computeForsPk suite params sk
                  (UInt64.ofNat (leafGlobalIdx / 2 ^ params.subtreeHeight))
                  (leafGlobalIdx % 2 ^ params.subtreeHeight) := by
              unfold mpcComputeForsPk
              rw [computeForsPk_eq]
              dsimp only
              congr 1
              apply List.map_congr_left
              intro j _
              exact computeMerkleNode_congr_leafFn suite sk.pkSeed 0 _ .forsTree _ _
                (hMatch.2.2.2 _ _) params.forsHeight j
            rw [hForsOps, hForsPk, mpcSignHypertreeLayers_eq suite params o sk hMatch]
            rfl
      · simp [hLeaf]
    · simp [hWf]
  refine ⟨hPk, by rw [hPk, hSign], ?_⟩
  intro sig hSome
  rw [hPk] at hSome ⊢
  rw [hSign] at hSome
  exact verifyPqHashSig_evalSingleSign suite params sk msg optRand leafGlobalIdx maxGrind sig hSome

/-- Public transcript cost profile at the `Depth = 1 + w` cut boundary. -/
structure MpcCutCostProfile where
  chainRoundDepth   : Nat
  openedRBytes      : Nat
  openedForsLeaves  : Nat
  openedWotsChains  : Nat
  deriving DecidableEq, Repr

def pqHashCutCost (params : PqHashParams) : MpcCutCostProfile :=
  { chainRoundDepth  := 1 + params.w
    openedRBytes     := 32
    openedForsLeaves := if params.statefulJorts then 0 else params.forsTrees
    openedWotsChains := params.numLayers * params.ell1 }

/-- **Secret-Independent Cut Shape (`transcript_shape_depends_only_on_public_params`)**:
    For any well-formed signature emitted by `evalCutBatchSignMpc`, the counts and byte lengths of
    opened values at the `Depth = 1 + w` cut equal `pqHashCutCost params`, leaking zero timing or
    shape information about `skSeed` or `skPrf`. -/
theorem transcript_shape_depends_only_on_public_params
    (suite : TweakableHashSuite) (params : PqHashParams)
    (o₁ o₂ : PqHashMpcOracles) (sk₁ sk₂ : PqSecretKey)
    (hM₁ : o₁.MatchesKey suite sk₁) (hM₂ : o₂.MatchesKey suite sk₂)
    (m₁ r₁ m₂ r₂ : List UInt8) (idx₁ idx₂ maxGrind : Nat)
    (sig₁ sig₂ : PqHashSig)
    (hS₁ : evalCutBatchSignMpc suite params o₁ (derivePublicKeyMpc suite params o₁ sk₁.pkSeed) m₁ r₁ idx₁ maxGrind = some sig₁)
    (hS₂ : evalCutBatchSignMpc suite params o₂ (derivePublicKeyMpc suite params o₂ sk₂.pkSeed) m₂ r₂ idx₂ maxGrind = some sig₂) :
    sig₁.rRand.length = (pqHashCutCost params).openedRBytes ∧
    sig₂.rRand.length = (pqHashCutCost params).openedRBytes ∧
    sig₁.forsOpenings.length = (pqHashCutCost params).openedForsLeaves ∧
    sig₂.forsOpenings.length = (pqHashCutCost params).openedForsLeaves ∧
    sig₁.layerSigs.length = params.numLayers ∧
    sig₂.layerSigs.length = params.numLayers := by
  have hVer₁ := (evalCutBatchSignMpc_eq_evalSingleSign suite params o₁ sk₁ m₁ r₁ idx₁ maxGrind hM₁).2.2 sig₁ hS₁
  have hVer₂ := (evalCutBatchSignMpc_eq_evalSingleSign suite params o₂ sk₂ m₂ r₂ idx₂ maxGrind hM₂).2.2 sig₂ hS₂
  have hEq₁ := (evalCutBatchSignMpc_eq_evalSingleSign suite params o₁ sk₁ m₁ r₁ idx₁ maxGrind hM₁).2.1
  have hEq₂ := (evalCutBatchSignMpc_eq_evalSingleSign suite params o₂ sk₂ m₂ r₂ idx₂ maxGrind hM₂).2.1
  rw [hEq₁] at hS₁; rw [hEq₂] at hS₂
  have hExtract : ∀ (sk : PqSecretKey) (m r : List UInt8) (idx : Nat) (sig : PqHashSig),
      evalSingleSign suite params sk m r idx maxGrind = some sig →
      verifyPqHashSig suite params (derivePublicKey suite params sk) m sig = true →
      sig.rRand.length = 32 ∧
      sig.forsOpenings.length = (if params.statefulJorts then 0 else params.forsTrees) ∧
      sig.layerSigs.length = params.numLayers := by
    intro sk m r idx sig hs hv
    unfold evalSingleSign at hs
    cases hwf : params.wellFormed
    · simp [hwf] at hs
    · simp only [hwf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hs
      by_cases hlt : idx < 2 ^ (params.numLayers * params.subtreeHeight)
      · simp only [hlt, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hs
        have hLayerLen : sig.layerSigs.length = params.numLayers := by
          unfold verifyPqHashSig at hv
          simp only [hwf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hv
          by_cases hne : sig.layerSigs.length ≠ params.numLayers
          · simp [hne] at hv
          · exact Decidable.of_not_not hne
        cases hst : params.statefulJorts
        · simp only [hst, Bool.false_eq_true, ↓reduceIte] at hs ⊢
          cases hG : grindTswCounterAux suite params.w params.ell1 params.targetSum
              (thPrfMsg suite sk.skPrf r (thPreHash suite (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot m))
              (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot
              (thPreHash suite (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot m)
              0 (UInt64.ofNat (idx / 2 ^ params.subtreeHeight)) (UInt32.ofNat (idx % 2 ^ params.subtreeHeight)) 0 maxGrind
          · simp [hG] at hs
          · rcases ‹Nat × List Nat × List UInt8› with ⟨_, _, _⟩
            simp only [hG] at hs
            cases hS : signHypertreeLayers suite params sk (derivePublicKey suite params sk).pkRoot [] maxGrind 0 idx
                (computeForsPk suite params sk (UInt64.ofNat (idx / 2 ^ params.subtreeHeight)) (idx % 2 ^ params.subtreeHeight)) params.numLayers
            · simp [hS] at hs
            · simp only [hS, Option.some.injEq] at hs; subst hs
              refine ⟨?_, ?_, hLayerLen⟩
              · rw [thPrfMsg_eq]; exact thCall_length suite _ _ _ _
              · rw [buildForsOpenings_eq]; simp
        · simp only [hst, ↓reduceIte] at hs ⊢
          cases hS : signHypertreeLayers suite params sk (derivePublicKey suite params sk).pkRoot
              (thPrfMsg suite sk.skPrf r (thPreHash suite (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot m))
              maxGrind 0 idx (thPreHash suite (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot m) params.numLayers
          · simp [hS] at hs
          · simp only [hS, Option.some.injEq] at hs; subst hs
            refine ⟨?_, rfl, hLayerLen⟩
            rw [thPrfMsg_eq]; exact thCall_length suite _ _ _ _
      · simp [hlt] at hs
  have hPk₁ := (evalCutBatchSignMpc_eq_evalSingleSign suite params o₁ sk₁ m₁ r₁ idx₁ maxGrind hM₁).1
  have hPk₂ := (evalCutBatchSignMpc_eq_evalSingleSign suite params o₂ sk₂ m₂ r₂ idx₂ maxGrind hM₂).1
  rw [hPk₁] at hVer₁; rw [hPk₂] at hVer₂
  obtain ⟨hr1, hf1, hl1⟩ := hExtract sk₁ m₁ r₁ idx₁ sig₁ hS₁ hVer₁
  obtain ⟨hr2, hf2, hl2⟩ := hExtract sk₂ m₂ r₂ idx₂ sig₂ hS₂ hVer₂
  dsimp only [pqHashCutCost]
  exact ⟨hr1, hr2, hf1, hf2, hl1, hl2⟩

/-! ## 2. Genuine 3-Party `2-of-3 RSS` Word-Level `Keccak-f[1600]`, `SHAKE256` & `cSHAKE256` -/

/-- 3-way Boolean share triple `(x0, x1, x2)` for 2-of-3 replicated secret sharing:
    Party 0 holds `(x0, x1)`, Party 1 holds `(x1, x2)`, Party 2 holds `(x2, x0)`. -/
structure RssBitShare where
  x0 : Bool
  x1 : Bool
  x2 : Bool
  deriving DecidableEq, Repr

@[expose] def reconstructRss (s : RssBitShare) : Bool :=
  s.x0 ^^ s.x1 ^^ s.x2

/-- Pairwise PRF randomness bits `(r0, r1, r2)` where Party $i$ holds `(r_i, r_{i+1})`. -/
structure RssPrfZeroBitSeeds where
  r0 : Bool
  r1 : Bool
  r2 : Bool
  deriving DecidableEq, Repr

/-- Local 1-party Boolean AND step: uses ONLY Party $i$'s 2-of-3 share view `(ax_i, ax_next)`! -/
def rssBitPartyAndLocal (ax_i ax_next bx_i bx_next r_i r_next : Bool) : Bool :=
  (ax_i && bx_i) ^^ (ax_i && bx_next) ^^ (ax_next && bx_i) ^^ (r_i ^^ r_next)

def rssBitXor (a b : RssBitShare) : RssBitShare :=
  ⟨a.x0 ^^ b.x0, a.x1 ^^ b.x1, a.x2 ^^ b.x2⟩

def rssBitNot (a : RssBitShare) : RssBitShare :=
  ⟨!a.x0, a.x1, a.x2⟩

def rssBitAnd (a b : RssBitShare) (seeds : RssPrfZeroBitSeeds) : RssBitShare :=
  ⟨rssBitPartyAndLocal a.x0 a.x1 b.x0 b.x1 seeds.r0 seeds.r1,
   rssBitPartyAndLocal a.x1 a.x2 b.x1 b.x2 seeds.r1 seeds.r2,
   rssBitPartyAndLocal a.x2 a.x0 b.x2 b.x0 seeds.r2 seeds.r0⟩

def mpcKeccakChiBitRss (a b c : RssBitShare) (seeds : RssPrfZeroBitSeeds) : RssBitShare :=
  rssBitXor a (rssBitAnd (rssBitNot b) c seeds)

private theorem rssBoolAnd_identity (a0 a1 a2 b0 b1 b2 r0 r1 r2 : Bool) :
    (((a0 && b0) ^^ (a0 && b1) ^^ (a1 && b0) ^^ (r0 ^^ r1)) ^^
     ((a1 && b1) ^^ (a1 && b2) ^^ (a2 && b1) ^^ (r1 ^^ r2)) ^^
     ((a2 && b2) ^^ (a2 && b0) ^^ (a0 && b2) ^^ (r2 ^^ r0))) =
    ((a0 ^^ a1 ^^ a2) && (b0 ^^ b1 ^^ b2)) := by
  have hCancel : ∀ (x y z u0 u1 u2 : Bool),
      ((x ^^ (u0 ^^ u1)) ^^ (y ^^ (u1 ^^ u2)) ^^ (z ^^ (u2 ^^ u0))) = (x ^^ y ^^ z) := by
    intros x y z u0 u1 u2
    cases x <;> cases y <;> cases z <;> cases u0 <;> cases u1 <;> cases u2 <;> rfl
  rw [hCancel]
  cases a0 <;> cases a1 <;> cases a2 <;> cases b0 <;> cases b1 <;> cases b2 <;> rfl

theorem reconstructRss_rssBitAnd (a b : RssBitShare) (seeds : RssPrfZeroBitSeeds) :
    reconstructRss (rssBitAnd a b seeds) = (reconstructRss a && reconstructRss b) :=
  rssBoolAnd_identity a.x0 a.x1 a.x2 b.x0 b.x1 b.x2 seeds.r0 seeds.r1 seeds.r2

theorem reconstructRss_mpcKeccakChiBitRss (a b c : RssBitShare) (seeds : RssPrfZeroBitSeeds) :
    reconstructRss (mpcKeccakChiBitRss a b c seeds) =
      keccakChiBit (reconstructRss a) (reconstructRss b) (reconstructRss c) := by
  have hXor : ∀ u v : RssBitShare, reconstructRss (rssBitXor u v) = (reconstructRss u ^^ reconstructRss v) := by
    intro u v; cases u; cases v
    cases ‹Bool› <;> cases ‹Bool› <;> cases ‹Bool› <;> cases ‹Bool› <;> cases ‹Bool› <;> cases ‹Bool› <;> rfl
  have hNot : ∀ u : RssBitShare, reconstructRss (rssBitNot u) = !(reconstructRss u) := by
    intro u; cases u
    cases ‹Bool› <;> cases ‹Bool› <;> cases ‹Bool› <;> rfl
  unfold mpcKeccakChiBitRss keccakChiBit
  rw [hXor, reconstructRss_rssBitAnd, hNot]

/-- 64-bit bitsliced 2-of-3 RSS word share `(x0, x1, x2 : UInt64)`. -/
structure RssWord64 where
  x0 : UInt64
  x1 : UInt64
  x2 : UInt64
  deriving DecidableEq, Repr

@[expose] def reconstructRssWord (w : RssWord64) : UInt64 :=
  w.x0 ^^^ w.x1 ^^^ w.x2

/-- Pairwise 64-bit PRF randomness words `(r0, r1, r2)` where Party $i$ holds `(r_i, r_{i+1})`. -/
structure RssPrfZeroSeeds where
  r0 : UInt64
  r1 : UInt64
  r2 : UInt64
  deriving DecidableEq, Repr

def zeroRssSeeds : RssPrfZeroSeeds := ⟨0, 0, 0⟩

/-- Local 1-party 64-bit bitsliced AND step: accesses ONLY Party $i$'s 2-of-3 view `(ax_i, ax_next)`. -/
@[inline] def rssPartyAndLocal (ax_i ax_next bx_i bx_next r_i r_next : UInt64) : UInt64 :=
  (ax_i &&& bx_i) ^^^ (ax_i &&& bx_next) ^^^ (ax_next &&& bx_i) ^^^ (r_i ^^^ r_next)

@[inline] def rssWordAnd (a b : RssWord64) (seeds : RssPrfZeroSeeds) : RssWord64 :=
  ⟨rssPartyAndLocal a.x0 a.x1 b.x0 b.x1 seeds.r0 seeds.r1,
   rssPartyAndLocal a.x1 a.x2 b.x1 b.x2 seeds.r1 seeds.r2,
   rssPartyAndLocal a.x2 a.x0 b.x2 b.x0 seeds.r2 seeds.r0⟩

theorem reconstructRssWord_rssWordAnd (a b : RssWord64) (seeds : RssPrfZeroSeeds) :
    reconstructRssWord (rssWordAnd a b seeds) = (reconstructRssWord a &&& reconstructRssWord b) := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [reconstructRssWord, rssWordAnd, rssPartyAndLocal,
    UInt64.toBitVec_xor, UInt64.toBitVec_and, BitVec.getLsbD_xor, BitVec.getLsbD_and]
  exact rssBoolAnd_identity _ _ _ _ _ _ _ _ _

/-- Local 1-party Keccak $\chi$ lane computation `a_i ^ (((~b)_i & c_i) ...)` for each of the 3 parties:
    note `(~~~b)` negates `b0` only (`(~~~b0) ^^^ b1 ^^^ b2 = ~~~(b0 ^^^ b1 ^^^ b2)`), so:
    - Party 0 uses `(a0, a1, ~~~b0, b1, c0, c1, r0, r1)`,
    - Party 1 uses `(a1, a2, b1, b2, c1, c2, r1, r2)`,
    - Party 2 uses `(a2, a0, b2, ~~~b0, c2, c0, r2, r0)`. -/
@[inline] def rssChiLane0 (a0 _a1 b0 b1 c0 c1 r0 r1 : UInt64) : UInt64 :=
  a0 ^^^ rssPartyAndLocal (~~~b0) b1 c0 c1 r0 r1

@[inline] def rssChiLane1 (a1 _a2 b1 b2 c1 c2 r1 r2 : UInt64) : UInt64 :=
  a1 ^^^ rssPartyAndLocal b1 b2 c1 c2 r1 r2

@[inline] def rssChiLane2 (a2 _a0 b2 b0 c2 c0 r2 r0 : UInt64) : UInt64 :=
  a2 ^^^ rssPartyAndLocal b2 (~~~b0) c2 c0 r2 r0

private theorem rssChiLane_reconstruct (a0 a1 a2 b0 b1 b2 c0 c1 c2 : UInt64) (s : RssPrfZeroSeeds) :
    (rssChiLane0 a0 a1 b0 b1 c0 c1 s.r0 s.r1 ^^^
     (rssChiLane1 a1 a2 b1 b2 c1 c2 s.r1 s.r2 ^^^
      rssChiLane2 a2 a0 b2 b0 c2 c0 s.r2 s.r0)) =
    ((a0 ^^^ (a1 ^^^ a2)) ^^^ ((~~~(b0 ^^^ (b1 ^^^ b2))) &&& (c0 ^^^ (c1 ^^^ c2)))) := by
  have hAnd := reconstructRssWord_rssWordAnd ⟨~~~b0, b1, b2⟩ ⟨c0, c1, c2⟩ s
  unfold reconstructRssWord rssWordAnd at hAnd
  dsimp only at hAnd
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hAndBit := congrArg (fun w : UInt64 => w.toBitVec.getLsbD i) hAnd
  simp only [UInt64.toBitVec_xor, UInt64.toBitVec_and, UInt64.toBitVec_not,
    BitVec.getLsbD_xor, BitVec.getLsbD_and, Constructive.getLsbD_not, hi, decide_true, Bool.true_and] at hAndBit ⊢
  unfold rssChiLane0 rssChiLane1 rssChiLane2
  simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor]
  have hNotAssoc : ((!b0.toBitVec.getLsbD i) ^^ b1.toBitVec.getLsbD i ^^ b2.toBitVec.getLsbD i) =
      (!(b0.toBitVec.getLsbD i ^^ (b1.toBitVec.getLsbD i ^^ b2.toBitVec.getLsbD i))) := by
    cases b0.toBitVec.getLsbD i <;> cases b1.toBitVec.getLsbD i <;> cases b2.toBitVec.getLsbD i <;> rfl
  have hRearr : ∀ (x0 x1 x2 y0 y1 y2 : Bool),
      ((x0 ^^ y0) ^^ ((x1 ^^ y1) ^^ (x2 ^^ y2))) = ((x0 ^^ (x1 ^^ x2)) ^^ (y0 ^^ y1 ^^ y2)) := by
    intros x0 x1 x2 y0 y1 y2
    cases x0 <;> cases x1 <;> cases x2 <;> cases y0 <;> cases y1 <;> cases y2 <;> rfl
  rw [hRearr, hAndBit, hNotAssoc]
  have hCAssoc : (c0.toBitVec.getLsbD i ^^ c1.toBitVec.getLsbD i ^^ c2.toBitVec.getLsbD i) =
      (c0.toBitVec.getLsbD i ^^ (c1.toBitVec.getLsbD i ^^ c2.toBitVec.getLsbD i)) := by
    cases c0.toBitVec.getLsbD i <;> cases c1.toBitVec.getLsbD i <;> cases c2.toBitVec.getLsbD i <;> rfl
  rw [hCAssoc]

/-- 3-party 2-of-3 RSS 1600-bit Keccak state `(s0, s1, s2 : KState)`:
    Party 0 holds `(s0, s1)`, Party 1 holds `(s1, s2)`, Party 2 holds `(s2, s0)`. -/
structure RssKState where
  s0 : KState
  s1 : KState
  s2 : KState
  deriving DecidableEq, Repr

def zeroRssKState : RssKState := ⟨zeroKState, zeroKState, zeroKState⟩

def reconstructRssKState (st : RssKState) : KState :=
  xorKState st.s0 (xorKState st.s1 st.s2)

private theorem uint64_xor_assoc_comm (a b c d : UInt64) :
    ((a ^^^ b) ^^^ (c ^^^ d)) = ((a ^^^ c) ^^^ (b ^^^ d)) := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor]
  cases a.toBitVec.getLsbD i <;> cases b.toBitVec.getLsbD i <;>
    cases c.toBitVec.getLsbD i <;> cases d.toBitVec.getLsbD i <;> rfl

private theorem rotlK_xor (u v k j : UInt64)
    (hk : k.toNat < 64) (hj : j.toNat < 64) (hSum : k.toNat + j.toNat = 64) :
    rotlK (u ^^^ v) k j = rotlK u k j ^^^ rotlK v k j := by
  rw [rotlK_eq, rotlK_eq, rotlK_eq]
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hkm : (k.toBitVec % 64).toNat = k.toNat := by simp [BitVec.toNat_umod, Nat.mod_eq_of_lt hk]
  have hjm : (j.toBitVec % 64).toNat = j.toNat := by simp [BitVec.toNat_umod, Nat.mod_eq_of_lt hj]
  rw [UInt64.toBitVec_or, UInt64.toBitVec_xor, UInt64.toBitVec_or, UInt64.toBitVec_or,
      UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftLeft,
      BitVec.shiftLeft_eq', BitVec.shiftLeft_eq', BitVec.shiftLeft_eq',
      UInt64.toBitVec_shiftRight, UInt64.toBitVec_shiftRight, UInt64.toBitVec_shiftRight,
      BitVec.ushiftRight_eq', BitVec.ushiftRight_eq', BitVec.ushiftRight_eq',
      hkm, hjm, UInt64.toBitVec_xor]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    hi, decide_true, Bool.true_and]
  if hLow : i < k.toNat then
    simp [hLow]
  else
    have hOut : ∀ (b : BitVec 64), b.getLsbD (j.toNat + i) = false := fun b => by
      have hLt : b.toNat < 2 ^ (j.toNat + i) :=
        Nat.lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by omega) (by omega))
      simp [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hLt]
    simp [hLow, hOut]

private theorem thetaS_xorKState (u v : KState) :
    thetaS (xorKState u v) = xorKState (thetaS u) (thetaS v) := by
  rw [xorKState_eq, thetaS_eq, thetaS_eq, thetaS_eq, xorKState_eq]
  dsimp only
  have h5 : ∀ (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : UInt64),
      ((a0 ^^^ b0) ^^^ (a1 ^^^ b1) ^^^ (a2 ^^^ b2) ^^^ (a3 ^^^ b3) ^^^ (a4 ^^^ b4)) =
      ((a0 ^^^ a1 ^^^ a2 ^^^ a3 ^^^ a4) ^^^ (b0 ^^^ b1 ^^^ b2 ^^^ b3 ^^^ b4)) := by
    intros a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
    apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_getLsbD_eq; intro i _
    simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor]
    cases a0.toBitVec.getLsbD i <;> cases a1.toBitVec.getLsbD i <;> cases a2.toBitVec.getLsbD i <;>
      cases a3.toBitVec.getLsbD i <;> cases a4.toBitVec.getLsbD i <;>
      cases b0.toBitVec.getLsbD i <;> cases b1.toBitVec.getLsbD i <;> cases b2.toBitVec.getLsbD i <;>
      cases b3.toBitVec.getLsbD i <;> cases b4.toBitVec.getLsbD i <;> rfl
  have hLane : ∀ (u0 v0 cA cB rA rB : UInt64),
      ((u0 ^^^ v0) ^^^ ((cA ^^^ cB) ^^^ (rA ^^^ rB))) =
      ((u0 ^^^ (cA ^^^ rA)) ^^^ (v0 ^^^ (cB ^^^ rB))) := by
    intros u0 v0 cA cB rA rB
    apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_getLsbD_eq; intro i _
    simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor]
    cases u0.toBitVec.getLsbD i <;> cases v0.toBitVec.getLsbD i <;>
      cases cA.toBitVec.getLsbD i <;> cases cB.toBitVec.getLsbD i <;>
      cases rA.toBitVec.getLsbD i <;> cases rB.toBitVec.getLsbD i <;> rfl
  have hr1 : ∀ (x y : UInt64), rotlK (x ^^^ y) 1 63 = rotlK x 1 63 ^^^ rotlK y 1 63 :=
    fun x y => rotlK_xor x y 1 63 (by decide) (by decide) (by decide)
  conv =>
    lhs
    simp (config := { singlePass := true }) only [h5]
    simp (config := { singlePass := true }) only [hr1]
    simp (config := { singlePass := true }) only [hLane]

private theorem rhoPiS_xorKState (u v : KState) :
    rhoPiS (xorKState u v) = xorKState (rhoPiS u) (rhoPiS v) := by
  rw [xorKState_eq, rhoPiS_eq, rhoPiS_eq, rhoPiS_eq, xorKState_eq]
  dsimp only
  simp only [
    rotlK_xor _ _ 44 20 (by decide) (by decide) (by decide),
    rotlK_xor _ _ 43 21 (by decide) (by decide) (by decide),
    rotlK_xor _ _ 21 43 (by decide) (by decide) (by decide),
    rotlK_xor _ _ 14 50 (by decide) (by decide) (by decide),
    rotlK_xor _ _ 28 36 (by decide) (by decide) (by decide),
    rotlK_xor _ _ 20 44 (by decide) (by decide) (by decide),
    rotlK_xor _ _ 3 61 (by decide) (by decide) (by decide),
    rotlK_xor _ _ 45 19 (by decide) (by decide) (by decide),
    rotlK_xor _ _ 61 3 (by decide) (by decide) (by decide),
    rotlK_xor _ _ 1 63 (by decide) (by decide) (by decide),
    rotlK_xor _ _ 6 58 (by decide) (by decide) (by decide),
    rotlK_xor _ _ 25 39 (by decide) (by decide) (by decide),
    rotlK_xor _ _ 8 56 (by decide) (by decide) (by decide),
    rotlK_xor _ _ 18 46 (by decide) (by decide) (by decide),
    rotlK_xor _ _ 27 37 (by decide) (by decide) (by decide),
    rotlK_xor _ _ 36 28 (by decide) (by decide) (by decide),
    rotlK_xor _ _ 10 54 (by decide) (by decide) (by decide),
    rotlK_xor _ _ 15 49 (by decide) (by decide) (by decide),
    rotlK_xor _ _ 56 8 (by decide) (by decide) (by decide),
    rotlK_xor _ _ 62 2 (by decide) (by decide) (by decide),
    rotlK_xor _ _ 55 9 (by decide) (by decide) (by decide),
    rotlK_xor _ _ 39 25 (by decide) (by decide) (by decide),
    rotlK_xor _ _ 41 23 (by decide) (by decide) (by decide),
    rotlK_xor _ _ 2 62 (by decide) (by decide) (by decide)]

def mpcThetaRss (st : RssKState) : RssKState :=
  ⟨thetaS st.s0, thetaS st.s1, thetaS st.s2⟩

def mpcRhoPiRss (st : RssKState) : RssKState :=
  ⟨rhoPiS st.s0, rhoPiS st.s1, rhoPiS st.s2⟩

/-- Party 0 local 25-lane $\chi$ share computation from `(s0, s1)` and `(r0, r1)`. -/
def mpcChiParty0 (s0 s1 : KState) (rk : Nat → RssPrfZeroSeeds) : KState :=
  ⟨rssChiLane0 s0.a0 s1.a0 s0.a1 s1.a1 s0.a2 s1.a2 (rk 0).r0 (rk 0).r1,
   rssChiLane0 s0.a1 s1.a1 s0.a2 s1.a2 s0.a3 s1.a3 (rk 1).r0 (rk 1).r1,
   rssChiLane0 s0.a2 s1.a2 s0.a3 s1.a3 s0.a4 s1.a4 (rk 2).r0 (rk 2).r1,
   rssChiLane0 s0.a3 s1.a3 s0.a4 s1.a4 s0.a0 s1.a0 (rk 3).r0 (rk 3).r1,
   rssChiLane0 s0.a4 s1.a4 s0.a0 s1.a0 s0.a1 s1.a1 (rk 4).r0 (rk 4).r1,
   rssChiLane0 s0.a5 s1.a5 s0.a6 s1.a6 s0.a7 s1.a7 (rk 5).r0 (rk 5).r1,
   rssChiLane0 s0.a6 s1.a6 s0.a7 s1.a7 s0.a8 s1.a8 (rk 6).r0 (rk 6).r1,
   rssChiLane0 s0.a7 s1.a7 s0.a8 s1.a8 s0.a9 s1.a9 (rk 7).r0 (rk 7).r1,
   rssChiLane0 s0.a8 s1.a8 s0.a9 s1.a9 s0.a5 s1.a5 (rk 8).r0 (rk 8).r1,
   rssChiLane0 s0.a9 s1.a9 s0.a5 s1.a5 s0.a6 s1.a6 (rk 9).r0 (rk 9).r1,
   rssChiLane0 s0.a10 s1.a10 s0.a11 s1.a11 s0.a12 s1.a12 (rk 10).r0 (rk 10).r1,
   rssChiLane0 s0.a11 s1.a11 s0.a12 s1.a12 s0.a13 s1.a13 (rk 11).r0 (rk 11).r1,
   rssChiLane0 s0.a12 s1.a12 s0.a13 s1.a13 s0.a14 s1.a14 (rk 12).r0 (rk 12).r1,
   rssChiLane0 s0.a13 s1.a13 s0.a14 s1.a14 s0.a10 s1.a10 (rk 13).r0 (rk 13).r1,
   rssChiLane0 s0.a14 s1.a14 s0.a10 s1.a10 s0.a11 s1.a11 (rk 14).r0 (rk 14).r1,
   rssChiLane0 s0.a15 s1.a15 s0.a16 s1.a16 s0.a17 s1.a17 (rk 15).r0 (rk 15).r1,
   rssChiLane0 s0.a16 s1.a16 s0.a17 s1.a17 s0.a18 s1.a18 (rk 16).r0 (rk 16).r1,
   rssChiLane0 s0.a17 s1.a17 s0.a18 s1.a18 s0.a19 s1.a19 (rk 17).r0 (rk 17).r1,
   rssChiLane0 s0.a18 s1.a18 s0.a19 s1.a19 s0.a15 s1.a15 (rk 18).r0 (rk 18).r1,
   rssChiLane0 s0.a19 s1.a19 s0.a15 s1.a15 s0.a16 s1.a16 (rk 19).r0 (rk 19).r1,
   rssChiLane0 s0.a20 s1.a20 s0.a21 s1.a21 s0.a22 s1.a22 (rk 20).r0 (rk 20).r1,
   rssChiLane0 s0.a21 s1.a21 s0.a22 s1.a22 s0.a23 s1.a23 (rk 21).r0 (rk 21).r1,
   rssChiLane0 s0.a22 s1.a22 s0.a23 s1.a23 s0.a24 s1.a24 (rk 22).r0 (rk 22).r1,
   rssChiLane0 s0.a23 s1.a23 s0.a24 s1.a24 s0.a20 s1.a20 (rk 23).r0 (rk 23).r1,
   rssChiLane0 s0.a24 s1.a24 s0.a20 s1.a20 s0.a21 s1.a21 (rk 24).r0 (rk 24).r1⟩

/-- Party 1 local 25-lane $\chi$ share computation from `(s1, s2)` and `(r1, r2)`. -/
def mpcChiParty1 (s1 s2 : KState) (rk : Nat → RssPrfZeroSeeds) : KState :=
  ⟨rssChiLane1 s1.a0 s2.a0 s1.a1 s2.a1 s1.a2 s2.a2 (rk 0).r1 (rk 0).r2,
   rssChiLane1 s1.a1 s2.a1 s1.a2 s2.a2 s1.a3 s2.a3 (rk 1).r1 (rk 1).r2,
   rssChiLane1 s1.a2 s2.a2 s1.a3 s2.a3 s1.a4 s2.a4 (rk 2).r1 (rk 2).r2,
   rssChiLane1 s1.a3 s2.a3 s1.a4 s2.a4 s1.a0 s2.a0 (rk 3).r1 (rk 3).r2,
   rssChiLane1 s1.a4 s2.a4 s1.a0 s2.a0 s1.a1 s2.a1 (rk 4).r1 (rk 4).r2,
   rssChiLane1 s1.a5 s2.a5 s1.a6 s2.a6 s1.a7 s2.a7 (rk 5).r1 (rk 5).r2,
   rssChiLane1 s1.a6 s2.a6 s1.a7 s2.a7 s1.a8 s2.a8 (rk 6).r1 (rk 6).r2,
   rssChiLane1 s1.a7 s2.a7 s1.a8 s2.a8 s1.a9 s2.a9 (rk 7).r1 (rk 7).r2,
   rssChiLane1 s1.a8 s2.a8 s1.a9 s2.a9 s1.a5 s2.a5 (rk 8).r1 (rk 8).r2,
   rssChiLane1 s1.a9 s2.a9 s1.a5 s2.a5 s1.a6 s2.a6 (rk 9).r1 (rk 9).r2,
   rssChiLane1 s1.a10 s2.a10 s1.a11 s2.a11 s1.a12 s2.a12 (rk 10).r1 (rk 10).r2,
   rssChiLane1 s1.a11 s2.a11 s1.a12 s2.a12 s1.a13 s2.a13 (rk 11).r1 (rk 11).r2,
   rssChiLane1 s1.a12 s2.a12 s1.a13 s2.a13 s1.a14 s2.a14 (rk 12).r1 (rk 12).r2,
   rssChiLane1 s1.a13 s2.a13 s1.a14 s2.a14 s1.a10 s2.a10 (rk 13).r1 (rk 13).r2,
   rssChiLane1 s1.a14 s2.a14 s1.a10 s2.a10 s1.a11 s2.a11 (rk 14).r1 (rk 14).r2,
   rssChiLane1 s1.a15 s2.a15 s1.a16 s2.a16 s1.a17 s2.a17 (rk 15).r1 (rk 15).r2,
   rssChiLane1 s1.a16 s2.a16 s1.a17 s2.a17 s1.a18 s2.a18 (rk 16).r1 (rk 16).r2,
   rssChiLane1 s1.a17 s2.a17 s1.a18 s2.a18 s1.a19 s2.a19 (rk 17).r1 (rk 17).r2,
   rssChiLane1 s1.a18 s2.a18 s1.a19 s2.a19 s1.a15 s2.a15 (rk 18).r1 (rk 18).r2,
   rssChiLane1 s1.a19 s2.a19 s1.a15 s2.a15 s1.a16 s2.a16 (rk 19).r1 (rk 19).r2,
   rssChiLane1 s1.a20 s2.a20 s1.a21 s2.a21 s1.a22 s2.a22 (rk 20).r1 (rk 20).r2,
   rssChiLane1 s1.a21 s2.a21 s1.a22 s2.a22 s1.a23 s2.a23 (rk 21).r1 (rk 21).r2,
   rssChiLane1 s1.a22 s2.a22 s1.a23 s2.a23 s1.a24 s2.a24 (rk 22).r1 (rk 22).r2,
   rssChiLane1 s1.a23 s2.a23 s1.a24 s2.a24 s1.a20 s2.a20 (rk 23).r1 (rk 23).r2,
   rssChiLane1 s1.a24 s2.a24 s1.a20 s2.a20 s1.a21 s2.a21 (rk 24).r1 (rk 24).r2⟩

/-- Party 2 local 25-lane $\chi$ share computation from `(s2, s0)` and `(r2, r0)`. -/
def mpcChiParty2 (s2 s0 : KState) (rk : Nat → RssPrfZeroSeeds) : KState :=
  ⟨rssChiLane2 s2.a0 s0.a0 s2.a1 s0.a1 s2.a2 s0.a2 (rk 0).r2 (rk 0).r0,
   rssChiLane2 s2.a1 s0.a1 s2.a2 s0.a2 s2.a3 s0.a3 (rk 1).r2 (rk 1).r0,
   rssChiLane2 s2.a2 s0.a2 s2.a3 s0.a3 s2.a4 s0.a4 (rk 2).r2 (rk 2).r0,
   rssChiLane2 s2.a3 s0.a3 s2.a4 s0.a4 s2.a0 s0.a0 (rk 3).r2 (rk 3).r0,
   rssChiLane2 s2.a4 s0.a4 s2.a0 s0.a0 s2.a1 s0.a1 (rk 4).r2 (rk 4).r0,
   rssChiLane2 s2.a5 s0.a5 s2.a6 s0.a6 s2.a7 s0.a7 (rk 5).r2 (rk 5).r0,
   rssChiLane2 s2.a6 s0.a6 s2.a7 s0.a7 s2.a8 s0.a8 (rk 6).r2 (rk 6).r0,
   rssChiLane2 s2.a7 s0.a7 s2.a8 s0.a8 s2.a9 s0.a9 (rk 7).r2 (rk 7).r0,
   rssChiLane2 s2.a8 s0.a8 s2.a9 s0.a9 s2.a5 s0.a5 (rk 8).r2 (rk 8).r0,
   rssChiLane2 s2.a9 s0.a9 s2.a5 s0.a5 s2.a6 s0.a6 (rk 9).r2 (rk 9).r0,
   rssChiLane2 s2.a10 s0.a10 s2.a11 s0.a11 s2.a12 s0.a12 (rk 10).r2 (rk 10).r0,
   rssChiLane2 s2.a11 s0.a11 s2.a12 s0.a12 s2.a13 s0.a13 (rk 11).r2 (rk 11).r0,
   rssChiLane2 s2.a12 s0.a12 s2.a13 s0.a13 s2.a14 s0.a14 (rk 12).r2 (rk 12).r0,
   rssChiLane2 s2.a13 s0.a13 s2.a14 s0.a14 s2.a10 s0.a10 (rk 13).r2 (rk 13).r0,
   rssChiLane2 s2.a14 s0.a14 s2.a10 s0.a10 s2.a11 s0.a11 (rk 14).r2 (rk 14).r0,
   rssChiLane2 s2.a15 s0.a15 s2.a16 s0.a16 s2.a17 s0.a17 (rk 15).r2 (rk 15).r0,
   rssChiLane2 s2.a16 s0.a16 s2.a17 s0.a17 s2.a18 s0.a18 (rk 16).r2 (rk 16).r0,
   rssChiLane2 s2.a17 s0.a17 s2.a18 s0.a18 s2.a19 s0.a19 (rk 17).r2 (rk 17).r0,
   rssChiLane2 s2.a18 s0.a18 s2.a19 s0.a19 s2.a15 s0.a15 (rk 18).r2 (rk 18).r0,
   rssChiLane2 s2.a19 s0.a19 s2.a15 s0.a15 s2.a16 s0.a16 (rk 19).r2 (rk 19).r0,
   rssChiLane2 s2.a20 s0.a20 s2.a21 s0.a21 s2.a22 s0.a22 (rk 20).r2 (rk 20).r0,
   rssChiLane2 s2.a21 s0.a21 s2.a22 s0.a22 s2.a23 s0.a23 (rk 21).r2 (rk 21).r0,
   rssChiLane2 s2.a22 s0.a22 s2.a23 s0.a23 s2.a24 s0.a24 (rk 22).r2 (rk 22).r0,
   rssChiLane2 s2.a23 s0.a23 s2.a24 s0.a24 s2.a20 s0.a20 (rk 23).r2 (rk 23).r0,
   rssChiLane2 s2.a24 s0.a24 s2.a20 s0.a20 s2.a21 s0.a21 (rk 24).r2 (rk 24).r0⟩

/-- 1-round 2-of-3 RSS $\chi$ step: each party computes `s_i` strictly from its own 2-of-3 view
    and forwards `s_i` to Party `(i - 1) mod 3` (`0` intermediate lanes opened!). -/
def mpcChiRss (st : RssKState) (rk : Nat → RssPrfZeroSeeds) : RssKState :=
  ⟨mpcChiParty0 st.s0 st.s1 rk,
   mpcChiParty1 st.s1 st.s2 rk,
   mpcChiParty2 st.s2 st.s0 rk⟩

def mpcRoundSRss (st : RssKState) (rc : UInt64) (rk : Nat → RssPrfZeroSeeds) : RssKState :=
  let m := mpcChiRss (mpcRhoPiRss (mpcThetaRss st)) rk
  { m with s0 := { m.s0 with a0 := m.s0.a0 ^^^ rc } }

def mpcKeccakRoundsRss : List UInt64 → Nat → RssKState → (Nat → Nat → RssPrfZeroSeeds) → RssKState
  | [], _, st, _ => st
  | rc :: rcs, rIdx, st, tape =>
    mpcKeccakRoundsRss rcs (rIdx + 1) (mpcRoundSRss st rc (tape rIdx)) tape

/-- Full 24-round distributed 2-of-3 RSS `Keccak-f[1600]` (`0` bits opened!). -/
def mpcKeccakF1600Rss (st : RssKState) (tape : Nat → Nat → RssPrfZeroSeeds) : RssKState :=
  mpcKeccakRoundsRss keccakRoundConstants 0 st tape

theorem reconstructRssKState_mpcRoundSRss (st : RssKState) (rc : UInt64) (rk : Nat → RssPrfZeroSeeds) :
    reconstructRssKState (mpcRoundSRss st rc rk) = roundS (reconstructRssKState st) rc := by
  have hTheta : reconstructRssKState (mpcThetaRss st) = thetaS (reconstructRssKState st) := by
    unfold reconstructRssKState mpcThetaRss
    rw [thetaS_xorKState, thetaS_xorKState]
  have hRho : ∀ u : RssKState, reconstructRssKState (mpcRhoPiRss u) = rhoPiS (reconstructRssKState u) := by
    intro u; unfold reconstructRssKState mpcRhoPiRss
    rw [rhoPiS_xorKState, rhoPiS_xorKState]
  have hChi : ∀ u : RssKState, reconstructRssKState (mpcChiRss u rk) = chiS (reconstructRssKState u) := by
    intro u
    unfold reconstructRssKState mpcChiRss mpcChiParty0 mpcChiParty1 mpcChiParty2
    rw [xorKState_eq, xorKState_eq, xorKState_eq, xorKState_eq, chiS_eq]
    dsimp only
    simp only [rssChiLane_reconstruct]
  unfold mpcRoundSRss
  rw [roundS_eq]
  dsimp only
  have hMid := (hChi (mpcRhoPiRss (mpcThetaRss st))).trans
    (congrArg chiS ((hRho (mpcThetaRss st)).trans (congrArg rhoPiS hTheta)))
  let m := mpcChiRss (mpcRhoPiRss (mpcThetaRss st)) rk
  have hIota : ((m.s0.a0 ^^^ rc) ^^^ (m.s1.a0 ^^^ m.s2.a0)) =
      ((m.s0.a0 ^^^ (m.s1.a0 ^^^ m.s2.a0)) ^^^ rc) := by
    apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_getLsbD_eq; intro i _
    simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor]
    cases m.s0.a0.toBitVec.getLsbD i <;> cases m.s1.a0.toBitVec.getLsbD i <;>
      cases m.s2.a0.toBitVec.getLsbD i <;> cases rc.toBitVec.getLsbD i <;> rfl
  change xorKState { m.s0 with a0 := m.s0.a0 ^^^ rc } (xorKState m.s1 m.s2) =
    { chiS (rhoPiS (thetaS (reconstructRssKState st))) with
      a0 := (chiS (rhoPiS (thetaS (reconstructRssKState st)))).a0 ^^^ rc }
  rw [← hMid]
  unfold reconstructRssKState
  dsimp only [m] at hIota ⊢
  rw [xorKState_eq]
  dsimp only
  rw [xorKState_eq, xorKState_eq]
  dsimp only
  rw [hIota]

/-- **2-of-3 RSS `Keccak-f[1600]` Exact Simulation (`reconstructRssKState_mpcKeccakF1600Rss`)**:
    For ANY correlated zero-seed tape `tape`, 24-round distributed RSS `mpcKeccakF1600Rss`
    reconstructs bit-for-bit to single-party `keccakF1600`! -/
theorem reconstructRssKState_mpcKeccakF1600Rss (st : RssKState) (tape : Nat → Nat → RssPrfZeroSeeds) :
    reconstructRssKState (mpcKeccakF1600Rss st tape) = keccakF1600 (reconstructRssKState st) := by
  unfold mpcKeccakF1600Rss
  rw [keccakF1600_eq]
  suffices hLoop : ∀ (rcs : List UInt64) (rIdx : Nat) (cur : RssKState),
      reconstructRssKState (mpcKeccakRoundsRss rcs rIdx cur tape) =
        rcs.foldl roundS (reconstructRssKState cur) from hLoop keccakRoundConstants 0 st
  intro rcs
  induction rcs with
  | nil => intros _ _; rfl
  | cons rc rcs ih =>
    intro rIdx cur
    simp only [mpcKeccakRoundsRss, List.foldl_cons,
      ih (rIdx + 1) (mpcRoundSRss cur rc (tape rIdx)),
      reconstructRssKState_mpcRoundSRss]

/-- 3-way XOR byte-stream sharing `(b0, b1, b2)` where Party 0 holds `(b0, b1)`,
    Party 1 holds `(b1, b2)`, and Party 2 holds `(b2, b0)`. -/
structure RssByteShares where
  b0 : List UInt8
  b1 : List UInt8
  b2 : List UInt8
  deriving DecidableEq, Repr

def RssByteShares.WellFormed (sh : RssByteShares) : Prop :=
  sh.b0.length = sh.b1.length ∧ sh.b1.length = sh.b2.length

@[expose] def reconstructRssBytes (sh : RssByteShares) : List UInt8 :=
  List.zipWith (· ^^^ ·) sh.b0 (List.zipWith (· ^^^ ·) sh.b1 sh.b2)

def rssPublicBytes (pub : List UInt8) : RssByteShares :=
  ⟨pub, List.replicate pub.length 0, List.replicate pub.length 0⟩

def rssAppendShares (x y : RssByteShares) : RssByteShares :=
  ⟨x.b0 ++ y.b0, x.b1 ++ y.b1, x.b2 ++ y.b2⟩

def rssTakeShares (n : Nat) (x : RssByteShares) : RssByteShares :=
  ⟨x.b0.take n, x.b1.take n, x.b2.take n⟩

def rssDropShares (n : Nat) (x : RssByteShares) : RssByteShares :=
  ⟨x.b0.drop n, x.b1.drop n, x.b2.drop n⟩

private theorem zipXor_length_eq : ∀ {xs ys : List UInt8},
    xs.length = ys.length → (List.zipWith (· ^^^ ·) xs ys).length = xs.length
  | [], [], _ => rfl
  | _ :: xs, _ :: ys, h => by simp [zipXor_length_eq (Nat.succ.inj h)]

private theorem zipXor_replicate_zero_right : ∀ (xs : List UInt8),
    List.zipWith (· ^^^ ·) xs (List.replicate xs.length 0) = xs
  | [] => rfl
  | x :: xs => by
    have hx0 : (x ^^^ (0 : UInt8)) = x := by
      apply UInt8.eq_of_toBitVec_eq; simp
    simp [List.replicate_succ, hx0, zipXor_replicate_zero_right xs]

private theorem zipXor_append : ∀ {x1 x2 y1 y2 : List UInt8},
    x1.length = y1.length →
    List.zipWith (· ^^^ ·) (x1 ++ x2) (y1 ++ y2) =
      List.zipWith (· ^^^ ·) x1 y1 ++ List.zipWith (· ^^^ ·) x2 y2
  | [], x2, [], y2, _ => rfl
  | _ :: x1, x2, _ :: y1, y2, h => by
    simp [zipXor_append (Nat.succ.inj h)]

private theorem zipXor_take : ∀ (n : Nat) (xs ys : List UInt8),
    List.zipWith (· ^^^ ·) (xs.take n) (ys.take n) = (List.zipWith (· ^^^ ·) xs ys).take n
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | _ + 1, _ :: _, [] => rfl
  | n + 1, _ :: xs, _ :: ys => by simp [zipXor_take n xs ys]

private theorem zipXor_drop : ∀ (n : Nat) (xs ys : List UInt8),
    List.zipWith (· ^^^ ·) (xs.drop n) (ys.drop n) = (List.zipWith (· ^^^ ·) xs ys).drop n
  | 0, _, _ => rfl
  | _ + 1, [], _ => by simp
  | _ + 1, _ :: _, [] => by simp
  | n + 1, _ :: xs, _ :: ys => by simp [zipXor_drop n xs ys]

theorem rssPublicBytes_wellFormed (pub : List UInt8) : (rssPublicBytes pub).WellFormed := by
  simp [rssPublicBytes, RssByteShares.WellFormed]

theorem reconstructRssBytes_rssPublicBytes (pub : List UInt8) :
    reconstructRssBytes (rssPublicBytes pub) = pub := by
  unfold reconstructRssBytes rssPublicBytes
  dsimp only
  have h1 : List.zipWith (· ^^^ ·) (List.replicate pub.length (0 : UInt8))
      (List.replicate pub.length (0 : UInt8)) = List.replicate pub.length (0 : UInt8) := by
    have h0 := zipXor_replicate_zero_right (List.replicate pub.length (0 : UInt8))
    rw [List.length_replicate] at h0
    exact h0
  rw [h1, zipXor_replicate_zero_right]

theorem reconstructRssBytes_length {sh : RssByteShares} (hWf : sh.WellFormed) :
    (reconstructRssBytes sh).length = sh.b0.length := by
  unfold reconstructRssBytes
  have h12 : (List.zipWith (· ^^^ ·) sh.b1 sh.b2).length = sh.b1.length :=
    zipXor_length_eq hWf.2
  exact zipXor_length_eq (hWf.1.trans h12.symm)

theorem rssAppendShares_wellFormed {x y : RssByteShares}
    (hx : x.WellFormed) (hy : y.WellFormed) : (rssAppendShares x y).WellFormed := by
  refine ⟨?_, ?_⟩
  · simp [rssAppendShares, hx.1, hy.1]
  · simp [rssAppendShares, hx.2, hy.2]

theorem reconstructRssBytes_append {x y : RssByteShares}
    (hx : x.WellFormed) :
    reconstructRssBytes (rssAppendShares x y) = reconstructRssBytes x ++ reconstructRssBytes y := by
  unfold reconstructRssBytes rssAppendShares
  dsimp only
  rw [zipXor_append hx.2, zipXor_append (hx.1.trans (zipXor_length_eq hx.2).symm)]

/-- Pad a 3-way shared byte stream in MPC without reconstructing `sh` (`padTail` depends ONLY on
    public length `sh.b0.length`). -/
def rssPadForRate (sh : RssByteShares) (suffix : UInt8) : RssByteShares :=
  let count := shake256RateBytes - sh.b0.length % shake256RateBytes
  let tail : List UInt8 :=
    if count = 1 then [suffix ^^^ (0x80 : UInt8)]
    else [suffix] ++ List.replicate (count - 2) 0 ++ [0x80]
  rssAppendShares sh (rssPublicBytes tail)

theorem rssPadForRate_wellFormed {sh : RssByteShares} (hWf : sh.WellFormed) (suffix : UInt8) :
    (rssPadForRate sh suffix).WellFormed :=
  rssAppendShares_wellFormed hWf (rssPublicBytes_wellFormed _)

theorem reconstructRssBytes_rssPadForRate {sh : RssByteShares} (hWf : sh.WellFormed) (suffix : UInt8) :
    reconstructRssBytes (rssPadForRate sh suffix) = padForRate (reconstructRssBytes sh) suffix := by
  unfold rssPadForRate
  rw [reconstructRssBytes_append hWf, reconstructRssBytes_rssPublicBytes,
      padForRate_eq, reconstructRssBytes_length hWf]
  dsimp only
  split <;> simp [List.append_assoc]

def mpcXorRate136Rss (st : RssKState) (blk : RssByteShares) : RssKState :=
  ⟨xorRate136 st.s0 blk.b0, xorRate136 st.s1 blk.b1, xorRate136 st.s2 blk.b2⟩

private theorem reconstructRssKState_mpcXorRate136Rss (st : RssKState) {blk : RssByteShares}
    (hWf : blk.WellFormed) :
    reconstructRssKState (mpcXorRate136Rss st blk) =
      xorRate136 (reconstructRssKState st) (reconstructRssBytes blk) := by
  have h12Len : (List.zipWith (· ^^^ ·) blk.b1 blk.b2).length = blk.b1.length := zipXor_length_eq hWf.2
  have hLoad : ∀ lane : Nat,
      loadLe64 (reconstructRssBytes blk) lane =
        (loadLe64 blk.b0 lane ^^^ (loadLe64 blk.b1 lane ^^^ loadLe64 blk.b2 lane)) := by
    intro lane
    unfold reconstructRssBytes
    rw [loadLe64_zipXor _ _ (hWf.1.trans h12Len.symm), loadLe64_zipXor _ _ hWf.2]
  have hLane6 : ∀ (s0 s1 s2 l0 l1 l2 : UInt64),
      ((s0 ^^^ l0) ^^^ ((s1 ^^^ l1) ^^^ (s2 ^^^ l2))) =
      ((s0 ^^^ (s1 ^^^ s2)) ^^^ (l0 ^^^ (l1 ^^^ l2))) := by
    intros s0 s1 s2 l0 l1 l2
    apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_getLsbD_eq; intro i _
    simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor]
    cases s0.toBitVec.getLsbD i <;> cases s1.toBitVec.getLsbD i <;> cases s2.toBitVec.getLsbD i <;>
      cases l0.toBitVec.getLsbD i <;> cases l1.toBitVec.getLsbD i <;> cases l2.toBitVec.getLsbD i <;> rfl
  unfold reconstructRssKState mpcXorRate136Rss
  rw [xorRate136_eq, xorRate136_eq, xorRate136_eq, xorRate136_eq,
      xorKState_eq, xorKState_eq, xorKState_eq, xorKState_eq]
  dsimp only
  simp only [hLoad, hLane6]

def mpcAbsorbBlocksRss : Nat → Nat → RssKState → RssByteShares → (Nat → Nat → Nat → RssPrfZeroSeeds) → RssKState
  | 0, _, st, _, _ => st
  | k + 1, blkIdx, st, rest, blkTape =>
    let absorbed := mpcXorRate136Rss st (rssTakeShares shake256RateBytes rest)
    let permuted := mpcKeccakF1600Rss absorbed (blkTape blkIdx)
    mpcAbsorbBlocksRss k (blkIdx + 1) permuted (rssDropShares shake256RateBytes rest) blkTape

def mpcAbsorbPaddedRss (padded : RssByteShares) (blkTape : Nat → Nat → Nat → RssPrfZeroSeeds) : RssKState :=
  mpcAbsorbBlocksRss (padded.b0.length / shake256RateBytes) 0 zeroRssKState padded blkTape

/-- Squeeze multi-block XOF output **directly into `RssByteShares` without opening a single byte**! -/
def mpcSqueezeFuelSharedRss : Nat → Nat → Nat → RssKState → (Nat → Nat → Nat → RssPrfZeroSeeds) → RssByteShares
  | 0, _, _, _, _ => ⟨[], [], []⟩
  | _ + 1, 0, _, _, _ => ⟨[], [], []⟩
  | fuel + 1, outLen + 1, sqIdx, st, sqTape =>
    let blk : RssByteShares := ⟨rateBlockBytes st.s0, rateBlockBytes st.s1, rateBlockBytes st.s2⟩
    if outLen + 1 ≤ 136 then
      rssTakeShares (outLen + 1) blk
    else
      rssAppendShares blk
        (mpcSqueezeFuelSharedRss fuel (outLen + 1 - 136) (sqIdx + 1)
          (mpcKeccakF1600Rss st (sqTape sqIdx)) sqTape)

/-- **Secret-Shared `SHAKE256` (`mpcShake256SharedRss`)**: maps `RssByteShares` to `RssByteShares`
    (`0` bytes reconstructed during sponge absorption, permutation, or squeeze!). -/
def mpcShake256SharedRss (outLen : Nat) (sh : RssByteShares)
    (tape : Nat → Nat → Nat → RssPrfZeroSeeds) : RssByteShares :=
  let padded := rssPadForRate sh 0x1f
  let absorbed := mpcAbsorbPaddedRss padded (fun b => tape (2 * b))
  mpcSqueezeFuelSharedRss outLen outLen 0 absorbed (fun q => tape (2 * q + 1))

/-- **Secret-Shared `cSHAKE256` (`mpcCshake256SharedRss`)**: maps `RssByteShares` to `RssByteShares`
    (`0` bytes reconstructed!). -/
def mpcCshake256SharedRss (outLen : Nat) (customization : List UInt8) (sh : RssByteShares)
    (tape : Nat → Nat → Nat → RssPrfZeroSeeds) : RssByteShares :=
  let shakeCompatible := customization = []
  let framed := if shakeCompatible then sh else rssAppendShares (rssPublicBytes (customizationPrefix customization)) sh
  let suffix : UInt8 := if shakeCompatible then 0x1f else 0x04
  let padded := rssPadForRate framed suffix
  let absorbed := mpcAbsorbPaddedRss padded (fun b => tape (2 * b))
  mpcSqueezeFuelSharedRss outLen outLen 0 absorbed (fun q => tape (2 * q + 1))

private theorem mpcSqueezeFuelSharedRss_simulates :
    ∀ (fuel outLen sqIdx : Nat) (st : RssKState) (sqTape : Nat → Nat → Nat → RssPrfZeroSeeds),
      (mpcSqueezeFuelSharedRss fuel outLen sqIdx st sqTape).WellFormed ∧
      reconstructRssBytes (mpcSqueezeFuelSharedRss fuel outLen sqIdx st sqTape) =
        squeezeXofFuel fuel outLen (reconstructRssKState st)
  | 0, outLen, _, st, _ => ⟨⟨rfl, rfl⟩, by rw [squeezeXofFuel_zero]; rfl⟩
  | fuel + 1, 0, _, st, _ => ⟨⟨rfl, rfl⟩, by rw [squeezeXofFuel_succ_zero]; rfl⟩
  | fuel + 1, outLen + 1, sqIdx, st, sqTape => by
    simp only [mpcSqueezeFuelSharedRss]
    rw [squeezeXofFuel_succ_succ]
    let blk : RssByteShares := ⟨rateBlockBytes st.s0, rateBlockBytes st.s1, rateBlockBytes st.s2⟩
    have hBlkWf : blk.WellFormed :=
      ⟨(rateBlockBytes_length st.s0).trans (rateBlockBytes_length st.s1).symm,
       (rateBlockBytes_length st.s1).trans (rateBlockBytes_length st.s2).symm⟩
    have hBlkRec : reconstructRssBytes blk = rateBlockBytes (reconstructRssKState st) := by
      unfold reconstructRssKState reconstructRssBytes
      rw [rateBlockBytes_xor, rateBlockBytes_xor]
    if hle : outLen + 1 ≤ 136 then
      simp only [hle, ↓reduceIte]
      refine ⟨⟨by simp [rssTakeShares, rateBlockBytes_length],
               by simp [rssTakeShares, rateBlockBytes_length]⟩, ?_⟩
      unfold reconstructRssBytes rssTakeShares
      dsimp only
      rw [zipXor_take, zipXor_take, ← hBlkRec]; rfl
    else
      simp only [hle, ↓reduceIte]
      obtain ⟨ihWf, ihRec⟩ := mpcSqueezeFuelSharedRss_simulates fuel (outLen + 1 - 136) (sqIdx + 1)
        (mpcKeccakF1600Rss st (sqTape sqIdx)) sqTape
      rw [reconstructRssKState_mpcKeccakF1600Rss] at ihRec
      exact ⟨rssAppendShares_wellFormed hBlkWf ihWf,
             by rw [reconstructRssBytes_append hBlkWf, hBlkRec, ihRec]⟩

private theorem mpcAbsorbBlocksRss_simulates :
    ∀ (k blkIdx : Nat) (st : RssKState) (rest : RssByteShares)
      (blkTape : Nat → Nat → Nat → RssPrfZeroSeeds),
      rest.WellFormed →
      reconstructRssKState (mpcAbsorbBlocksRss k blkIdx st rest blkTape) =
        absorbBlocks k (reconstructRssKState st) (reconstructRssBytes rest)
  | 0, _, st, rest, _, _ => by rw [absorbBlocks_zero]; rfl
  | k + 1, blkIdx, st, rest, blkTape, hWf => by
    simp only [mpcAbsorbBlocksRss]
    rw [absorbBlocks_succ]
    have hTakeWf : (rssTakeShares shake256RateBytes rest).WellFormed :=
      ⟨by simp [rssTakeShares, hWf.1], by simp [rssTakeShares, hWf.2]⟩
    have hDropWf : (rssDropShares shake256RateBytes rest).WellFormed :=
      ⟨by simp [rssDropShares, hWf.1], by simp [rssDropShares, hWf.2]⟩
    have hTakeRec : reconstructRssBytes (rssTakeShares shake256RateBytes rest) =
        (reconstructRssBytes rest).take shake256RateBytes := by
      unfold reconstructRssBytes rssTakeShares; dsimp only; rw [zipXor_take, zipXor_take]
    have hDropRec : reconstructRssBytes (rssDropShares shake256RateBytes rest) =
        (reconstructRssBytes rest).drop shake256RateBytes := by
      unfold reconstructRssBytes rssDropShares; dsimp only; rw [zipXor_drop, zipXor_drop]
    rw [mpcAbsorbBlocksRss_simulates k (blkIdx + 1) _ _ blkTape hDropWf,
        reconstructRssKState_mpcKeccakF1600Rss,
        reconstructRssKState_mpcXorRate136Rss st hTakeWf,
        hTakeRec, hDropRec]

private theorem reconstructRssKState_zero : reconstructRssKState zeroRssKState = zeroKState := by
  unfold reconstructRssKState zeroRssKState
  rw [zeroKState_eq, xorKState_eq, xorKState_eq]
  rfl

/-- **`reconstructRssBytes_mpcShake256SharedRss`**: shared 2-of-3 RSS `SHAKE256` output shares are
    well-formed and reconstruct bit-for-bit to `shake256Xof outLen (reconstructRssBytes sh)`. -/
theorem reconstructRssBytes_mpcShake256SharedRss (outLen : Nat) {sh : RssByteShares}
    (hWf : sh.WellFormed) (tape : Nat → Nat → Nat → RssPrfZeroSeeds) :
    (mpcShake256SharedRss outLen sh tape).WellFormed ∧
    reconstructRssBytes (mpcShake256SharedRss outLen sh tape) =
      shake256Xof outLen (reconstructRssBytes sh) := by
  unfold mpcShake256SharedRss shake256Xof
  have hPadWf := rssPadForRate_wellFormed hWf 0x1f
  have hPadRec := reconstructRssBytes_rssPadForRate hWf 0x1f
  obtain ⟨hSqWf, hSqRec⟩ := mpcSqueezeFuelSharedRss_simulates outLen outLen 0
    (mpcAbsorbPaddedRss (rssPadForRate sh 0x1f) (fun b => tape (2 * b))) (fun q => tape (2 * q + 1))
  refine ⟨hSqWf, ?_⟩
  rw [hSqRec, squeezeXofAux_eq, absorbPadded_eq]
  unfold mpcAbsorbPaddedRss
  have hLenEq : (rssPadForRate sh 0x1f).b0.length = (padForRate (reconstructRssBytes sh) 0x1f).length := by
    rw [← hPadRec, reconstructRssBytes_length hPadWf]
  rw [hLenEq, mpcAbsorbBlocksRss_simulates _ 0 zeroRssKState _ _ hPadWf,
      reconstructRssKState_zero, hPadRec]

/-- **`reconstructRssBytes_mpcCshake256SharedRss`**: shared 2-of-3 RSS `cSHAKE256` output shares are
    well-formed and reconstruct bit-for-bit to `cshake256Xof outLen customization (reconstructRssBytes sh)`. -/
theorem reconstructRssBytes_mpcCshake256SharedRss (outLen : Nat) (customization : List UInt8)
    {sh : RssByteShares} (hWf : sh.WellFormed) (tape : Nat → Nat → Nat → RssPrfZeroSeeds) :
    (mpcCshake256SharedRss outLen customization sh tape).WellFormed ∧
    reconstructRssBytes (mpcCshake256SharedRss outLen customization sh tape) =
      cshake256Xof outLen customization (reconstructRssBytes sh) := by
  unfold mpcCshake256SharedRss cshake256Xof
  dsimp only
  let framed := if customization = [] then sh else rssAppendShares (rssPublicBytes (customizationPrefix customization)) sh
  let suffix : UInt8 := if customization = [] then 0x1f else 0x04
  have hFramedWf : framed.WellFormed := by
    dsimp only [framed]; split
    · exact hWf
    · exact rssAppendShares_wellFormed (rssPublicBytes_wellFormed _) hWf
  have hFramedRec : reconstructRssBytes framed =
      (if customization = [] then reconstructRssBytes sh
       else customizationPrefix customization ++ reconstructRssBytes sh) := by
    dsimp only [framed]; split
    · rfl
    · rw [reconstructRssBytes_append (rssPublicBytes_wellFormed _), reconstructRssBytes_rssPublicBytes]
  have hPadWf := rssPadForRate_wellFormed hFramedWf suffix
  have hPadRec := reconstructRssBytes_rssPadForRate hFramedWf suffix
  obtain ⟨hSqWf, hSqRec⟩ := mpcSqueezeFuelSharedRss_simulates outLen outLen 0
    (mpcAbsorbPaddedRss (rssPadForRate framed suffix) (fun b => tape (2 * b))) (fun q => tape (2 * q + 1))
  refine ⟨hSqWf, ?_⟩
  rw [hSqRec, squeezeXofAux_eq, absorbPadded_eq]
  unfold mpcAbsorbPaddedRss
  have hLenEq : (rssPadForRate framed suffix).b0.length = (padForRate (reconstructRssBytes framed) suffix).length := by
    rw [← hPadRec, reconstructRssBytes_length hPadWf]
  rw [hLenEq, mpcAbsorbBlocksRss_simulates _ 0 zeroRssKState _ _ hPadWf,
      reconstructRssKState_zero, hPadRec, hFramedRec]

/-! ### Cleartext-Free 2-of-3 RSS Oracles for NIST FIPS 205 (`SLH-DSA`) & `Corduroy` -/

def mpcFipsPrfSharedRss (n : Nat) (pkSeed : List UInt8) (skSeedSh : RssByteShares)
    (adrs : Fips205Adrs) (tape : Nat → Nat → Nat → RssPrfZeroSeeds) : RssByteShares :=
  let pre := rssAppendShares (rssPublicBytes (pkSeed ++ encodeFips205Adrs adrs)) skSeedSh
  mpcShake256SharedRss n pre tape

def mpcFipsFSharedRss (n : Nat) (pkSeed : List UInt8) (adrs : Fips205Adrs)
    (m1Sh : RssByteShares) (tape : Nat → Nat → Nat → RssPrfZeroSeeds) : RssByteShares :=
  let pre := rssAppendShares (rssPublicBytes (pkSeed ++ encodeFips205Adrs adrs)) m1Sh
  mpcShake256SharedRss n pre tape

/-- Iterates `mpcFipsFSharedRss` `steps` times on secret-shared `curSh` (`0` intermediate bytes opened!). -/
def mpcFipsChainSharedRss (n : Nat) (pkSeed : List UInt8) (layer tree kp chainIdx : Nat) :
    Nat → Nat → RssByteShares → (Nat → Nat → Nat → Nat → RssPrfZeroSeeds) → RssByteShares
  | _, 0, curSh, _ => curSh
  | startIdx, steps + 1, curSh, stepTape =>
    let adrs := mkFipsAdrs layer tree .wotsHash kp chainIdx startIdx
    let nextSh := mpcFipsFSharedRss n pkSeed adrs curSh (stepTape startIdx)
    mpcFipsChainSharedRss n pkSeed layer tree kp chainIdx (startIdx + 1) steps nextSh stepTape

/-- **Cleartext-Free 2-of-3 RSS Oracle Instance for NIST FIPS 205 (`mkRssSlhMpcOracles`)**:
    `skSeedSh` and `skPrfSh` are NEVER reconstructed; intermediate WOTS+ chain values and unqueried
    FORS secret leaves remain inside `RssByteShares` throughout! -/
@[expose] def mkRssSlhMpcOracles (p : Fips205Params) (skSeedSh skPrfSh : RssByteShares)
    (pkSeed : List UInt8) (tape : Nat → Nat → Nat → Nat → RssPrfZeroSeeds) : SlhMpcOracles where
  evalPrfMsg optRand msgPrime :=
    let pre := rssAppendShares skPrfSh (rssPublicBytes (optRand ++ msgPrime))
    reconstructRssBytes (mpcShake256SharedRss p.n pre (tape 0))
  evalWotsChainEnd layer tree kp chainIdx steps :=
    let baseSh := mpcFipsPrfSharedRss p.n pkSeed skSeedSh (mkFipsAdrs layer tree .wotsPrf kp chainIdx 0) (tape 0)
    let endSh := mpcFipsChainSharedRss p.n pkSeed layer tree kp chainIdx 0 steps baseSh (fun s => tape (s + 1))
    reconstructRssBytes endSh
  evalForsReveal tree idxLeaf globalLeaf :=
    let leafSh := mpcFipsPrfSharedRss p.n pkSeed skSeedSh (mkFipsAdrs 0 tree .forsPrf idxLeaf 0 globalLeaf) (tape 0)
    reconstructRssBytes leafSh
  evalForsLeafHash tree idxLeaf nodeIdx :=
    let secSh := mpcFipsPrfSharedRss p.n pkSeed skSeedSh (mkFipsAdrs 0 tree .forsPrf idxLeaf 0 nodeIdx) (tape 0)
    let hashSh := mpcFipsFSharedRss p.n pkSeed (mkFipsAdrs 0 tree .forsTree idxLeaf 0 nodeIdx) secSh (tape 1)
    reconstructRssBytes hashSh

private theorem mpcFipsChainSharedRss_simulates (n : Nat) (pkSeed : List UInt8)
    (layer tree kp chainIdx : Nat) (stepTape : Nat → Nat → Nat → Nat → RssPrfZeroSeeds) :
    ∀ (steps startIdx : Nat) {curSh : RssByteShares},
      curSh.WellFormed →
      (mpcFipsChainSharedRss n pkSeed layer tree kp chainIdx startIdx steps curSh stepTape).WellFormed ∧
      reconstructRssBytes (mpcFipsChainSharedRss n pkSeed layer tree kp chainIdx startIdx steps curSh stepTape) =
        fipsChain n pkSeed layer tree kp chainIdx startIdx steps (reconstructRssBytes curSh)
  | 0, startIdx, curSh, hWf => ⟨hWf, by simp only [mpcFipsChainSharedRss]; rw [fipsChain_zero]⟩
  | steps + 1, startIdx, curSh, hWf => by
    simp only [mpcFipsChainSharedRss]
    rw [fipsChain_succ]
    dsimp only
    unfold mpcFipsFSharedRss
    let pub := pkSeed ++ encodeFips205Adrs (mkFipsAdrs layer tree .wotsHash kp chainIdx startIdx)
    have hPreWf := rssAppendShares_wellFormed (rssPublicBytes_wellFormed pub) hWf
    obtain ⟨hNextWf, hNextRec⟩ := reconstructRssBytes_mpcShake256SharedRss n hPreWf (stepTape startIdx)
    rw [reconstructRssBytes_append (rssPublicBytes_wellFormed pub), reconstructRssBytes_rssPublicBytes,
        List.append_assoc] at hNextRec
    obtain ⟨ihWf, ihRec⟩ := mpcFipsChainSharedRss_simulates n pkSeed layer tree kp chainIdx stepTape steps (startIdx + 1) hNextWf
    refine ⟨ihWf, ?_⟩
    dsimp only [pub] at hNextRec
    rw [ihRec, hNextRec, fipsF_eq, List.append_assoc]

/-- **`mkRssSlhMpcOracles_matchesKey`**: proves `mkRssSlhMpcOracles` faithfully satisfies
    `SlhMpcOracles.MatchesKey` without ever reconstructing `skSeed` or `skPrf`! -/
theorem mkRssSlhMpcOracles_matchesKey (p : Fips205Params)
    {skSeedSh skPrfSh : RssByteShares} (hSeedWf : skSeedSh.WellFormed) (hPrfWf : skPrfSh.WellFormed)
    (pkSeed : List UInt8) (tape : Nat → Nat → Nat → Nat → RssPrfZeroSeeds) :
    (mkRssSlhMpcOracles p skSeedSh skPrfSh pkSeed tape).MatchesKey p
      (reconstructRssBytes skSeedSh) (reconstructRssBytes skPrfSh) pkSeed := by
  rw [SlhMpcOracles.MatchesKey_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro optRand msgPrime
    dsimp only [mkRssSlhMpcOracles]
    have hPreWf := rssAppendShares_wellFormed hPrfWf (rssPublicBytes_wellFormed (optRand ++ msgPrime))
    rw [(reconstructRssBytes_mpcShake256SharedRss p.n hPreWf (tape 0)).2,
        reconstructRssBytes_append hPrfWf, reconstructRssBytes_rssPublicBytes,
        fipsPrfMsg_eq, List.append_assoc]
  · intro layer tree kp chainIdx steps
    dsimp only [mkRssSlhMpcOracles, mpcFipsPrfSharedRss]
    let pub := pkSeed ++ encodeFips205Adrs (mkFipsAdrs layer tree .wotsPrf kp chainIdx 0)
    have hPreWf := rssAppendShares_wellFormed (rssPublicBytes_wellFormed pub) hSeedWf
    obtain ⟨hBaseWf, hBaseRec⟩ := reconstructRssBytes_mpcShake256SharedRss p.n hPreWf (tape 0)
    rw [(mpcFipsChainSharedRss_simulates p.n pkSeed layer tree kp chainIdx (fun s => tape (s + 1)) steps 0 hBaseWf).2,
        hBaseRec, reconstructRssBytes_append (rssPublicBytes_wellFormed pub),
        reconstructRssBytes_rssPublicBytes, fipsPrf_eq]
  · intro tree idxLeaf globalLeaf
    dsimp only [mkRssSlhMpcOracles, mpcFipsPrfSharedRss]
    let pub := pkSeed ++ encodeFips205Adrs (mkFipsAdrs 0 tree .forsPrf idxLeaf 0 globalLeaf)
    have hPreWf := rssAppendShares_wellFormed (rssPublicBytes_wellFormed pub) hSeedWf
    rw [(reconstructRssBytes_mpcShake256SharedRss p.n hPreWf (tape 0)).2,
        reconstructRssBytes_append (rssPublicBytes_wellFormed pub),
        reconstructRssBytes_rssPublicBytes, fipsPrf_eq]
  · intro tree idxLeaf nodeIdx
    dsimp only [mkRssSlhMpcOracles, mpcFipsPrfSharedRss, mpcFipsFSharedRss]
    let pub1 := pkSeed ++ encodeFips205Adrs (mkFipsAdrs 0 tree .forsPrf idxLeaf 0 nodeIdx)
    let pub2 := pkSeed ++ encodeFips205Adrs (mkFipsAdrs 0 tree .forsTree idxLeaf 0 nodeIdx)
    have hPre1 := rssAppendShares_wellFormed (rssPublicBytes_wellFormed pub1) hSeedWf
    obtain ⟨hSecWf, hSecRec⟩ := reconstructRssBytes_mpcShake256SharedRss p.n hPre1 (tape 0)
    have hPre2 := rssAppendShares_wellFormed (rssPublicBytes_wellFormed pub2) hSecWf
    rw [(reconstructRssBytes_mpcShake256SharedRss p.n hPre2 (tape 1)).2,
        reconstructRssBytes_append (rssPublicBytes_wellFormed pub2), reconstructRssBytes_rssPublicBytes,
        hSecRec, reconstructRssBytes_append (rssPublicBytes_wellFormed pub1),
        reconstructRssBytes_rssPublicBytes, fipsF_eq, fipsPrf_eq]

/-- **End-to-End 2-of-3 RSS Threshold NIST FIPS 205 Bit-Identity (`rss_thresholdSlhSign_eq_slhSignInternal`)**:
    For both `SLH-DSA-SHAKE-128f` (`17,088`B) and `SLH-DSA-SHAKE-128s` (`7,856`B), 3-party RSS
    signing over secret-shared `skSeedSh, skPrfSh` outputs the **bit-identical** public key and
    signature bytes as single-party NIST FIPS 205 `slhSignInternal`! -/
theorem rss_thresholdSlhSign_eq_slhSignInternal (p : Fips205Params) (hWf : p.wellFormed = true)
    {skSeedSh skPrfSh : RssByteShares} (hSeedWf : skSeedSh.WellFormed) (hPrfWf : skPrfSh.WellFormed)
    (pkSeed msgPrime optRand : List UInt8) (tape : Nat → Nat → Nat → Nat → RssPrfZeroSeeds) :
    let o := mkRssSlhMpcOracles p skSeedSh skPrfSh pkSeed tape
    let (sk, pk) := slhKeygenInternal p (reconstructRssBytes skSeedSh) (reconstructRssBytes skPrfSh) pkSeed
    slhKeygenMpc p o pkSeed = pk ∧
    thresholdSlhSignBytes p o msgPrime pk optRand = encodeSlhSig (slhSignInternal p msgPrime sk optRand) ∧
    (thresholdSlhSignBytes p o msgPrime pk optRand).length = p.sigBytes ∧
    slhVerifyInternal p msgPrime (slhSignMpc p o msgPrime pk optRand) pk = true := by
  have hM := mkRssSlhMpcOracles_matchesKey p hSeedWf hPrfWf pkSeed tape
  obtain ⟨h1, _, h3, h4, h5⟩ := thresholdSlhSign_eq_slhSignInternal p hWf _ _ _ pkSeed msgPrime optRand hM
  exact ⟨h1, h3, h4, h5⟩

/-- Frame `thPreimage roleTag pkSeed adrs [secretSh]` as `RssByteShares` without opening `secretSh`. -/
def rssFrameSingleSecretCall (roleTag pkSeed : List UInt8) (adrs : HashAdrs)
    (secretSh : RssByteShares) : RssByteShares :=
  let pubPrefix :=
    leb128 4 ++ encodeListField roleTag ++ encodeListField pkSeed ++
    encodeListField (encodeAdrs adrs) ++ leb128 secretSh.b0.length
  rssAppendShares (rssPublicBytes pubPrefix) secretSh

private theorem reconstructRssBytes_rssFrameSingleSecretCall (roleTag pkSeed : List UInt8)
    (adrs : HashAdrs) {secretSh : RssByteShares} (hWf : secretSh.WellFormed) :
    (rssFrameSingleSecretCall roleTag pkSeed adrs secretSh).WellFormed ∧
    reconstructRssBytes (rssFrameSingleSecretCall roleTag pkSeed adrs secretSh) =
      thPreimage roleTag pkSeed adrs [reconstructRssBytes secretSh] := by
  unfold rssFrameSingleSecretCall
  refine ⟨rssAppendShares_wellFormed (rssPublicBytes_wellFormed _) hWf, ?_⟩
  rw [reconstructRssBytes_append (rssPublicBytes_wellFormed _), reconstructRssBytes_rssPublicBytes,
      thPreimage_eq]
  simp only [List.cons_append, List.nil_append, encodeMultiFrame, List.length_cons, List.length_nil,
    encodeByteFields_cons, encodeByteFields_nil, List.append_nil,
    encodeListField_eq (reconstructRssBytes secretSh), reconstructRssBytes_length hWf,
    List.append_assoc]

def mpcCshakeThChainSharedRss (pkSeed : List UInt8) (layer : UInt32) (tree : UInt64) (kp chain : Nat) :
    Nat → Nat → RssByteShares → (Nat → Nat → Nat → Nat → RssPrfZeroSeeds) → RssByteShares
  | _, 0, curSh, _ => curSh
  | startStep, rem + 1, curSh, stepTape =>
    let adrs : HashAdrs := ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat chain, UInt32.ofNat startStep⟩
    let preSh := rssFrameSingleSecretCall tagThF pkSeed adrs curSh
    let nextSh := mpcCshake256SharedRss 32 pqCshakeSuiteCustom preSh (stepTape startStep)
    mpcCshakeThChainSharedRss pkSeed layer tree kp chain (startStep + 1) rem nextSh stepTape

/-- **Cleartext-Free 2-of-3 RSS Oracle Instance for `cshake256Suite` (`Corduroy` & `SLH-DSA`)**. -/
@[expose] def mkRssCshakePqHashMpcOracles (skSeedSh skPrfSh : RssByteShares)
    (pkSeed : List UInt8) (tape : Nat → Nat → Nat → Nat → RssPrfZeroSeeds) : PqHashMpcOracles where
  evalPrfMsg optRand mu :=
    let pubPrefix :=
      leb128 6 ++ encodeListField tagPrfMsg ++ encodeListField [] ++
      encodeListField (encodeAdrs zeroAdrs) ++ leb128 skPrfSh.b0.length
    let pubSuffix := encodeListField optRand ++ encodeListField mu
    let preSh := rssAppendShares (rssPublicBytes pubPrefix)
                   (rssAppendShares skPrfSh (rssPublicBytes pubSuffix))
    reconstructRssBytes (mpcCshake256SharedRss 32 pqCshakeSuiteCustom preSh (tape 0))
  evalWotsChainEnd layer tree kp chain steps :=
    let baseAdrs : HashAdrs := ⟨layer, tree, .wotsPrf, UInt32.ofNat kp, UInt32.ofNat chain, 0⟩
    let baseSh := mpcCshake256SharedRss 32 pqCshakeSuiteCustom
                    (rssFrameSingleSecretCall tagPrf pkSeed baseAdrs skSeedSh) (tape 0)
    let endSh := mpcCshakeThChainSharedRss pkSeed layer tree kp chain 0 steps baseSh (fun s => tape (s + 1))
    reconstructRssBytes endSh
  evalForsReveal tree0 kp0 globalU :=
    let adrs : HashAdrs := ⟨0, tree0, .forsPrf, UInt32.ofNat kp0, 0, UInt32.ofNat globalU⟩
    let secSh := mpcCshake256SharedRss 32 pqCshakeSuiteCustom
                   (rssFrameSingleSecretCall tagPrf pkSeed adrs skSeedSh) (tape 0)
    reconstructRssBytes secSh
  evalForsLeafHash tree0 kp0 globalU :=
    let prfAdrs : HashAdrs := ⟨0, tree0, .forsPrf, UInt32.ofNat kp0, 0, UInt32.ofNat globalU⟩
    let secSh := mpcCshake256SharedRss 32 pqCshakeSuiteCustom
                   (rssFrameSingleSecretCall tagPrf pkSeed prfAdrs skSeedSh) (tape 0)
    let treeAdrs : HashAdrs := ⟨0, tree0, .forsTree, UInt32.ofNat kp0, 0, UInt32.ofNat globalU⟩
    let hashSh := mpcCshake256SharedRss 32 pqCshakeSuiteCustom
                    (rssFrameSingleSecretCall tagThF pkSeed treeAdrs secSh) (tape 1)
    reconstructRssBytes hashSh

private theorem mpcCshakeThChainSharedRss_simulates (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp chain : Nat)
    (stepTape : Nat → Nat → Nat → Nat → RssPrfZeroSeeds) :
    ∀ (rem startStep : Nat) {curSh : RssByteShares},
      curSh.WellFormed →
      (mpcCshakeThChainSharedRss pkSeed layer tree kp chain startStep rem curSh stepTape).WellFormed ∧
      reconstructRssBytes (mpcCshakeThChainSharedRss pkSeed layer tree kp chain startStep rem curSh stepTape) =
        wotsChainSteps cshake256Suite pkSeed layer tree kp chain startStep rem (reconstructRssBytes curSh)
  | 0, startStep, curSh, hWf => ⟨hWf, by simp only [mpcCshakeThChainSharedRss]; rw [wotsChainSteps_zero]⟩
  | rem + 1, startStep, curSh, hWf => by
    simp only [mpcCshakeThChainSharedRss]
    rw [wotsChainSteps_succ]
    dsimp only
    obtain ⟨hFrameWf, hFrameRec⟩ := reconstructRssBytes_rssFrameSingleSecretCall tagThF pkSeed _ hWf
    obtain ⟨hNextWf, hNextRec⟩ := reconstructRssBytes_mpcCshake256SharedRss 32 pqCshakeSuiteCustom hFrameWf (stepTape startStep)
    obtain ⟨ihWf, ihRec⟩ := mpcCshakeThChainSharedRss_simulates pkSeed layer tree kp chain stepTape rem (startStep + 1) hNextWf
    refine ⟨ihWf, ?_⟩
    rw [ihRec, hNextRec, hFrameRec, thChainF_eq, thCall_eq]; rfl

theorem mkRssCshakePqHashMpcOracles_matchesKey
    {skSeedSh skPrfSh : RssByteShares} (hSeedWf : skSeedSh.WellFormed) (hPrfWf : skPrfSh.WellFormed)
    (pkSeed : List UInt8) (tape : Nat → Nat → Nat → Nat → RssPrfZeroSeeds) :
    (mkRssCshakePqHashMpcOracles skSeedSh skPrfSh pkSeed tape).MatchesKey cshake256Suite
      { skSeed := reconstructRssBytes skSeedSh
        skPrf  := reconstructRssBytes skPrfSh
        pkSeed := pkSeed } := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro optRand mu
    dsimp only [mkRssCshakePqHashMpcOracles]
    let pubPrefix :=
      leb128 6 ++ encodeListField tagPrfMsg ++ encodeListField [] ++
      encodeListField (encodeAdrs zeroAdrs) ++ leb128 skPrfSh.b0.length
    let pubSuffix := encodeListField optRand ++ encodeListField mu
    have hMidWf := rssAppendShares_wellFormed hPrfWf (rssPublicBytes_wellFormed pubSuffix)
    have hPreWf := rssAppendShares_wellFormed (rssPublicBytes_wellFormed pubPrefix) hMidWf
    rw [(reconstructRssBytes_mpcCshake256SharedRss 32 pqCshakeSuiteCustom hPreWf (tape 0)).2,
        reconstructRssBytes_append (rssPublicBytes_wellFormed pubPrefix), reconstructRssBytes_rssPublicBytes,
        reconstructRssBytes_append hPrfWf, reconstructRssBytes_rssPublicBytes,
        thPrfMsg_eq, thCall_eq, thPreimage_eq]
    dsimp only [pubPrefix, pubSuffix]
    simp only [cshake256Suite, cshake256Bytes, List.cons_append, List.nil_append,
      encodeMultiFrame, List.length_cons, List.length_nil, encodeByteFields_cons, encodeByteFields_nil,
      List.append_nil, encodeListField_eq (reconstructRssBytes skPrfSh), reconstructRssBytes_length hPrfWf,
      List.append_assoc]
  · intro layer tree kp chain steps
    dsimp only [mkRssCshakePqHashMpcOracles]
    obtain ⟨hFWf, hFRec⟩ := reconstructRssBytes_rssFrameSingleSecretCall tagPrf pkSeed _ hSeedWf
    obtain ⟨hBaseWf, hBaseRec⟩ := reconstructRssBytes_mpcCshake256SharedRss 32 pqCshakeSuiteCustom hFWf (tape 0)
    rw [(mpcCshakeThChainSharedRss_simulates pkSeed layer tree kp chain (fun s => tape (s + 1)) steps 0 hBaseWf).2,
        hBaseRec, hFRec, wotsSecretBase_eq, thSecretPrf_eq, thCall_eq]; rfl
  · intro tree0 kp0 globalU
    dsimp only [mkRssCshakePqHashMpcOracles]
    obtain ⟨hFWf, hFRec⟩ := reconstructRssBytes_rssFrameSingleSecretCall tagPrf pkSeed _ hSeedWf
    rw [(reconstructRssBytes_mpcCshake256SharedRss 32 pqCshakeSuiteCustom hFWf (tape 0)).2,
        hFRec, forsSecretLeaf_eq, thSecretPrf_eq, thCall_eq]; rfl
  · intro tree0 kp0 globalU
    dsimp only [mkRssCshakePqHashMpcOracles]
    obtain ⟨hF1Wf, hF1Rec⟩ := reconstructRssBytes_rssFrameSingleSecretCall tagPrf pkSeed _ hSeedWf
    obtain ⟨hSecWf, hSecRec⟩ := reconstructRssBytes_mpcCshake256SharedRss 32 pqCshakeSuiteCustom hF1Wf (tape 0)
    obtain ⟨hF2Wf, hF2Rec⟩ := reconstructRssBytes_rssFrameSingleSecretCall tagThF pkSeed _ hSecWf
    rw [(reconstructRssBytes_mpcCshake256SharedRss 32 pqCshakeSuiteCustom hF2Wf (tape 1)).2,
        hF2Rec, hSecRec, hF1Rec, forsLeafFn_eq, forsSecretLeaf_eq, thChainF_eq, thSecretPrf_eq,
        thCall_eq, thCall_eq]; rfl

theorem rss_thresholdPqHashSign_eq_evalSingleSign (params : PqHashParams)
    {skSeedSh skPrfSh : RssByteShares} (hSeedWf : skSeedSh.WellFormed) (hPrfWf : skPrfSh.WellFormed)
    (pkSeed msg optRand : List UInt8) (leafGlobalIdx maxGrind : Nat)
    (tape : Nat → Nat → Nat → Nat → RssPrfZeroSeeds) :
    let o := mkRssCshakePqHashMpcOracles skSeedSh skPrfSh pkSeed tape
    let sk : PqSecretKey := ⟨reconstructRssBytes skSeedSh, reconstructRssBytes skPrfSh, pkSeed⟩
    derivePublicKeyMpc cshake256Suite params o pkSeed = derivePublicKey cshake256Suite params sk ∧
    evalCutBatchSignMpc cshake256Suite params o (derivePublicKeyMpc cshake256Suite params o pkSeed)
      msg optRand leafGlobalIdx maxGrind =
      evalSingleSign cshake256Suite params sk msg optRand leafGlobalIdx maxGrind := by
  have hM := mkRssCshakePqHashMpcOracles_matchesKey hSeedWf hPrfWf pkSeed tape
  obtain ⟨h1, h2, _⟩ := evalCutBatchSignMpc_eq_evalSingleSign cshake256Suite params _ _ msg optRand leafGlobalIdx maxGrind hM
  exact ⟨h1, h2⟩

/-! ## 3. Arbitrary $t$-of-$n$ `BinaryTower` ($\mathcal{T}_3$) & `Goldilocks` Shamir `Poseidon2` -/

/-- Polymorphic Lagrange-at-zero linear combiner $\sum_{p} \lambda_p \cdot s_p$. -/
@[expose] def lagrangeCombine {R : Type} [CommRingOps R] (lambdas shares : List R) : R :=
  ringDot lambdas shares

theorem lagrangeCombine_zipAdd {R : Type} [LawfulCommRing R] :
    ∀ (ls xs ys : List R),
      xs.length = ys.length →
      lagrangeCombine ls (List.zipWith CommRingOps.add xs ys) =
        CommRingOps.add (lagrangeCombine ls xs) (lagrangeCombine ls ys)
  | [], _, _, _ => by simp [lagrangeCombine, ringDot, LawfulCommRing.add_zero]
  | _ :: _, [], [], _ => by simp [lagrangeCombine, ringDot, LawfulCommRing.add_zero]
  | l :: ls, x :: xs, y :: ys, h => by
    have ih := lagrangeCombine_zipAdd ls xs ys (Nat.succ.inj h)
    simp only [lagrangeCombine] at ih
    simp only [List.zipWith_cons_cons, lagrangeCombine, ringDot]
    rw [LawfulCommRing.left_distrib, ih, LawfulCommRing.add_add_add_comm]

theorem lagrangeCombine_zipSub {R : Type} [LawfulCommRing R] :
    ∀ (ls xs ys : List R),
      xs.length = ys.length →
      lagrangeCombine ls (List.zipWith CommRingOps.sub xs ys) =
        CommRingOps.sub (lagrangeCombine ls xs) (lagrangeCombine ls ys)
  | [], _, _, _ => by simp [lagrangeCombine, ringDot, LawfulCommRing.sub_self]
  | _ :: _, [], [], _ => by simp [lagrangeCombine, ringDot, LawfulCommRing.sub_self]
  | l :: ls, x :: xs, y :: ys, h => by
    have hNegAdd : ∀ (a b : R), CommRingOps.neg (CommRingOps.add a b) =
        CommRingOps.add (CommRingOps.neg a) (CommRingOps.neg b) := fun a b => by
      apply LawfulCommRing.add_left_cancel (a := CommRingOps.add a b)
      rw [LawfulCommRing.add_right_neg, LawfulCommRing.add_add_add_comm,
          LawfulCommRing.add_right_neg, LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]
    have ih := lagrangeCombine_zipSub ls xs ys (Nat.succ.inj h)
    simp only [lagrangeCombine] at ih
    simp only [List.zipWith_cons_cons, lagrangeCombine, ringDot]
    rw [LawfulCommRing.mul_sub, ih]
    simp only [LawfulCommRing.sub_eq_add_neg, hNegAdd, LawfulCommRing.add_add_add_comm]

theorem lagrangeCombine_scale {R : Type} [LawfulCommRing R] (c : R) :
    ∀ (ls xs : List R),
      lagrangeCombine ls (xs.map (CommRingOps.mul c)) =
        CommRingOps.mul c (lagrangeCombine ls xs)
  | [], _ => by simp [lagrangeCombine, ringDot, LawfulCommRing.mul_zero]
  | _ :: _, [] => by simp [lagrangeCombine, ringDot, LawfulCommRing.mul_zero]
  | l :: ls, x :: xs => by
    have ih := lagrangeCombine_scale c ls xs
    simp only [lagrangeCombine] at ih
    simp only [List.map_cons, lagrangeCombine, ringDot]
    rw [ih, LawfulCommRing.left_distrib,
        ← LawfulCommRing.mul_assoc, ← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm l c]

/-- Valid Shamir evaluation points: pairwise distinct and strictly nonzero (`x ≠ 0`). -/
def validShamirEvalPoints {R : Type} [CommRingOps R] [DecidableEq R] (pts : List R) : Prop :=
  pts.Nodup ∧ ∀ x ∈ pts, x ≠ CommRingOps.zero

/-- **`#tooth` Shamir Nonzero Evaluation Point Guard (`zero_eval_point_leaks_secret_term`)**:
    Evaluating any polynomial `c₀ :: cs` at `0` directly outputs `c₀` (the secret constant term!),
    proving why `validShamirEvalPoints` must forbid `CommRingOps.zero`. -/
theorem zero_eval_point_leaks_secret_term {R : Type} [LawfulCommRing R] (c₀ : R) (cs : List R) :
    RoundPoly.evalCoeffs (c₀ :: cs) CommRingOps.zero = c₀ := by
  simp [RoundPoly.evalCoeffs, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]

/-- Validity invariant for a dealerless `(t, n)` Shamir `Π_pow7` tuple: all 7 share lists have
    length `lambdas.length` and recombine to `(r, r^2, r^3, r^4, r^5, r^6, r^7)` at `0`. -/
def SharedPow7Tuple.validAt (lambdas : List Goldilocks) (tup : SharedPow7Tuple) : Prop :=
  let r  := lagrangeCombine lambdas tup.rSh
  let r2 := Goldilocks.mul r r
  let r3 := Goldilocks.mul r2 r
  let r4 := Goldilocks.mul r3 r
  let r5 := Goldilocks.mul r4 r
  let r6 := Goldilocks.mul r5 r
  let r7 := Goldilocks.mul r6 r
  tup.rSh.length = lambdas.length ∧
  tup.r2Sh.length = lambdas.length ∧
  tup.r3Sh.length = lambdas.length ∧
  tup.r4Sh.length = lambdas.length ∧
  tup.r5Sh.length = lambdas.length ∧
  tup.r6Sh.length = lambdas.length ∧
  tup.r7Sh.length = lambdas.length ∧
  lagrangeCombine lambdas tup.r2Sh = r2 ∧
  lagrangeCombine lambdas tup.r3Sh = r3 ∧
  lagrangeCombine lambdas tup.r4Sh = r4 ∧
  lagrangeCombine lambdas tup.r5Sh = r5 ∧
  lagrangeCombine lambdas tup.r6Sh = r6 ∧
  lagrangeCombine lambdas tup.r7Sh = r7

/-- **Weld from `Preprocessing.evalSharedPow7Tree` to `SharedPow7Tuple.validAt`**:
    The 3-round dealerless Beaver tree `evalSharedPow7Tree` over `(t, n)` Shamir shares produces a
    `SharedPow7Tuple` satisfying `validAt lambdas` with zero cleartext secret reconstruction. -/
theorem evalSharedPow7Tree_validAt
    (lambdas rSh : List Goldilocks)
    (t2 t3 t4 t5 t6 t7 : SharedBeaverTriple Goldilocks)
    (hSumOne : ringListSum lambdas = Goldilocks.one)
    (hRLen : rSh.length = lambdas.length)
    (h2 : t2.validAt lambdas) (h3 : t3.validAt lambdas) (h4 : t4.validAt lambdas)
    (h5 : t5.validAt lambdas) (h6 : t6.validAt lambdas) (h7 : t7.validAt lambdas) :
    (evalSharedPow7Tree lambdas rSh t2 t3 t4 t5 t6 t7).validAt lambdas := by
  have hTree := evalSharedPow7Tree_correct lambdas rSh t2 t3 t4 t5 t6 t7
    hSumOne hRLen h2 h3 h4 h5 h6 h7
  dsimp only at hTree
  obtain ⟨hRSh, ⟨hL2, hL3, hL4, hL5, hL6, hL7⟩, hE2, hE3, hE4, hE5, hE6, hE7⟩ := hTree
  unfold SharedPow7Tuple.validAt lagrangeCombine
  dsimp only
  rw [hRSh]
  have hR4 : ringDot lambdas (evalSharedPow7Tree lambdas rSh t2 t3 t4 t5 t6 t7).r4Sh =
      Goldilocks.mul (Goldilocks.mul (Goldilocks.mul (ringDot lambdas rSh) (ringDot lambdas rSh)) (ringDot lambdas rSh))
        (ringDot lambdas rSh) := by
    rw [hE4]
    apply Goldilocks.ext
    simp only [Goldilocks.mul_val, Nat.mul_mod_mod, Nat.mod_mul_mod]
    congr 1; ac_rfl
  refine ⟨hRLen, hL2, hL3, hL4, hL5, hL6, hL7, hE2, hE3, hR4, ?_, ?_, ?_⟩
  · rw [hE5, hR4]
  · rw [hE6, hR4, hE2]
    apply Goldilocks.ext
    simp only [Goldilocks.mul_val, Nat.mul_mod_mod, Nat.mod_mul_mod]
    congr 1; ac_rfl
  · rw [hE7]
    unfold sbox7
    apply Goldilocks.ext
    simp only [Goldilocks.mul_val, Nat.mul_mod_mod, Nat.mod_mul_mod]
    congr 1; ac_rfl

/-- Degree-7 binomial expansion $(\delta + r)^7 = \delta^7 + 7\delta^6 r + 21\delta^5 r^2 + 35\delta^4 r^3 + 35\delta^3 r^4 + 21\delta^2 r^5 + 7\delta r^6 + r^7$,
    evaluated as an affine linear combination of `(1, r, r2, r3, r4, r5, r6, r7)`. -/
def power7BinomialEval (d r r2 r3 r4 r5 r6 r7 : Goldilocks) : Goldilocks :=
  let d2 := Goldilocks.mul d d
  let d3 := Goldilocks.mul d2 d
  let d4 := Goldilocks.mul d2 d2
  let d5 := Goldilocks.mul d4 d
  let d6 := Goldilocks.mul d4 d2
  let d7 := Goldilocks.mul d4 d3
  Goldilocks.add
    (Goldilocks.add
      (Goldilocks.add d7 (Goldilocks.mul (Goldilocks.mul (Goldilocks.ofNat 7) d6) r))
      (Goldilocks.add
        (Goldilocks.mul (Goldilocks.mul (Goldilocks.ofNat 21) d5) r2)
        (Goldilocks.mul (Goldilocks.mul (Goldilocks.ofNat 35) d4) r3)))
    (Goldilocks.add
      (Goldilocks.add
        (Goldilocks.mul (Goldilocks.mul (Goldilocks.ofNat 35) d3) r4)
        (Goldilocks.mul (Goldilocks.mul (Goldilocks.ofNat 21) d2) r5))
      (Goldilocks.add
        (Goldilocks.mul (Goldilocks.mul (Goldilocks.ofNat 7) d) r6)
        r7))

private theorem nat_binom7_expand (a b : Nat) :
    (a + b) ^ 7 =
      (((a * a * a * a) * (a * a * a) + ((7 * ((a * a * a * a) * (a * a))) * b)) +
       (((21 * ((a * a * a * a) * a)) * (b * b)) + ((35 * (a * a * a * a)) * (b * b * b)))) +
      ((((35 * (a * a * a)) * (b * b * b * b)) + ((21 * (a * a)) * (b * b * b * b * b))) +
       (((7 * a) * (b * b * b * b * b * b)) + (b * b * b * b * b * b * b))) := by
  have h2 : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.succ_mul, Nat.zero_mul, Nat.zero_add]; ac_rfl
  have h3 : (a + b) * (a * a + 2 * a * b + b * b) =
      a * a * a + 3 * (a * a) * b + 3 * a * (b * b) + b * b * b := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.succ_mul, Nat.zero_mul, Nat.zero_add]; ac_rfl
  have h4 : (a + b) * (a * a * a + 3 * (a * a) * b + 3 * a * (b * b) + b * b * b) =
      a * a * a * a + 4 * (a * a * a) * b + 6 * (a * a) * (b * b) + 4 * a * (b * b * b) + b * b * b * b := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.succ_mul, Nat.zero_mul, Nat.zero_add]; ac_rfl
  have h5 : (a + b) * (a * a * a * a + 4 * (a * a * a) * b + 6 * (a * a) * (b * b) + 4 * a * (b * b * b) + b * b * b * b) =
      a * a * a * a * a + 5 * (a * a * a * a) * b + 10 * (a * a * a) * (b * b) + 10 * (a * a) * (b * b * b) +
      5 * a * (b * b * b * b) + b * b * b * b * b := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.succ_mul, Nat.zero_mul, Nat.zero_add]; ac_rfl
  have h6 : (a + b) * (a * a * a * a * a + 5 * (a * a * a * a) * b + 10 * (a * a * a) * (b * b) + 10 * (a * a) * (b * b * b) +
      5 * a * (b * b * b * b) + b * b * b * b * b) =
      a * a * a * a * a * a + 6 * (a * a * a * a * a) * b + 15 * (a * a * a * a) * (b * b) + 20 * (a * a * a) * (b * b * b) +
      15 * (a * a) * (b * b * b * b) + 6 * a * (b * b * b * b * b) + b * b * b * b * b * b := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.succ_mul, Nat.zero_mul, Nat.zero_add]; ac_rfl
  have h7 : (a + b) * (a * a * a * a * a * a + 6 * (a * a * a * a * a) * b + 15 * (a * a * a * a) * (b * b) + 20 * (a * a * a) * (b * b * b) +
      15 * (a * a) * (b * b * b * b) + 6 * a * (b * b * b * b * b) + b * b * b * b * b * b) =
      (((a * a * a * a) * (a * a * a) + ((7 * ((a * a * a * a) * (a * a))) * b)) +
       (((21 * ((a * a * a * a) * a)) * (b * b)) + ((35 * (a * a * a * a)) * (b * b * b)))) +
      ((((35 * (a * a * a)) * (b * b * b * b)) + ((21 * (a * a)) * (b * b * b * b * b))) +
       (((7 * a) * (b * b * b * b * b * b)) + (b * b * b * b * b * b * b))) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.succ_mul, Nat.zero_mul, Nat.zero_add]; ac_rfl
  calc (a + b) ^ 7
    _ = (a + b) * ((a + b) * ((a + b) * ((a + b) * ((a + b) * ((a + b) * (a + b)))))) := by
      simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]; ac_rfl
    _ = _ := by rw [h2, h3, h4, h5, h6, h7]

/-- **1-Round `Π_pow7` Degree-7 S-Box Identity (`power7BinomialEval_eq_sbox7`)**:
    Opening only $\delta = x - r$ and evaluating `power7BinomialEval` linearly over `(r, r^2, ..., r^7)`
    recovers `sbox7 x = x^7` over `Goldilocks` with zero cleartext secret leakage! -/
theorem power7BinomialEval_eq_sbox7 (x r : Goldilocks) :
    let d  := Goldilocks.sub x r
    let r2 := Goldilocks.mul r r
    let r3 := Goldilocks.mul r2 r
    let r4 := Goldilocks.mul r3 r
    let r5 := Goldilocks.mul r4 r
    let r6 := Goldilocks.mul r5 r
    let r7 := Goldilocks.mul r6 r
    power7BinomialEval d r r2 r3 r4 r5 r6 r7 = sbox7 x := by
  intro d r2 r3 r4 r5 r6 r7
  have hAddDR : Goldilocks.add d r = x := by
    change CommRingOps.add (CommRingOps.sub x r) r = x
    rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
        LawfulCommRing.add_left_neg, LawfulCommRing.add_zero]
  rw [← hAddDR]
  apply Goldilocks.ext
  rw [sbox7_val]
  have hPowMod : ((Goldilocks.add d r).val ^ 7) % goldilocksPrime = ((d.val + r.val) ^ 7) % goldilocksPrime := by
    rw [Goldilocks.add_val]
    have hStep : ∀ k : Nat, (((d.val + r.val) % goldilocksPrime) ^ k) % goldilocksPrime = ((d.val + r.val) ^ k) % goldilocksPrime := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, ih, ← Nat.mul_mod, Nat.mul_mod_mod]
    exact hStep 7
  rw [hPowMod, nat_binom7_expand d.val r.val]
  unfold power7BinomialEval
  dsimp only [r2, r3, r4, r5, r6, r7]
  have hc7  : (Goldilocks.ofNat 7).val = 7 := rfl
  have hc21 : (Goldilocks.ofNat 21).val = 21 := rfl
  have hc35 : (Goldilocks.ofNat 35).val = 35 := rfl
  simp only [Goldilocks.add_val, Goldilocks.mul_val, hc7, hc21, hc35,
    Nat.add_mod_mod, Nat.mod_add_mod, Nat.mul_mod_mod, Nat.mod_mul_mod, Nat.mul_assoc]

/-! ### Share-Level `(t, n)` Shamir `Π_pow7` Evaluation & SPDZ `GoldilocksExt2` MAC Verification -/

/-- Party-local linear combination of `SharedPow7Tuple` shares at opened masked scalar `d = x - r`,
    producing `(t, n)` Shamir shares of `x^7` with zero communication and zero secret reconstruction. -/
def mpcPow7Shares (d : Goldilocks) (tup : SharedPow7Tuple) : List Goldilocks :=
  let d2 := Goldilocks.mul d d
  let d3 := Goldilocks.mul d2 d
  let d4 := Goldilocks.mul d2 d2
  let d5 := Goldilocks.mul d4 d
  let d6 := Goldilocks.mul d4 d2
  let d7 := Goldilocks.mul d4 d3
  let c1 := Goldilocks.mul (Goldilocks.ofNat 7) d6
  let c2 := Goldilocks.mul (Goldilocks.ofNat 21) d5
  let c3 := Goldilocks.mul (Goldilocks.ofNat 35) d4
  let c4 := Goldilocks.mul (Goldilocks.ofNat 35) d3
  let c5 := Goldilocks.mul (Goldilocks.ofNat 21) d2
  let c6 := Goldilocks.mul (Goldilocks.ofNat 7) d
  ringListZipAdd
    (ringListZipAdd
      (shareAddConst d7 (shareScale c1 tup.rSh))
      (ringListZipAdd (shareScale c2 tup.r2Sh) (shareScale c3 tup.r3Sh)))
    (ringListZipAdd
      (ringListZipAdd (shareScale c4 tup.r4Sh) (shareScale c5 tup.r5Sh))
      (ringListZipAdd (shareScale c6 tup.r6Sh) tup.r7Sh))

/-- **Share-Level `Π_pow7` Correctness (`lagrangeCombine_mpcPow7Shares_eq_sbox7`)**:
    When `∑ λ_i = 1` and `tup` satisfies `tup.validAt lambdas`, opening ONLY `d = x - r` and locally
    evaluating `mpcPow7Shares d tup` produces `lambdas.length` Shamir shares recombining to
    `sbox7 (lagrangeCombine lambdas xSh)` without reconstructing `x` or `r`. -/
theorem lagrangeCombine_mpcPow7Shares_eq_sbox7
    (lambdas xSh : List Goldilocks) (tup : SharedPow7Tuple)
    (hSumOne : ringListSum lambdas = Goldilocks.one)
    (hXLen : xSh.length = lambdas.length)
    (hTup : tup.validAt lambdas) :
    let dOpened := lagrangeCombine lambdas (shareZipSub xSh tup.rSh)
    (mpcPow7Shares dOpened tup).length = lambdas.length ∧
    lagrangeCombine lambdas (mpcPow7Shares dOpened tup) =
      sbox7 (lagrangeCombine lambdas xSh) := by
  obtain ⟨hL1, hL2, hL3, hL4, hL5, hL6, hL7, hE2, hE3, hE4, hE5, hE6, hE7⟩ := hTup
  let d := lagrangeCombine lambdas (shareZipSub xSh tup.rSh)
  change (mpcPow7Shares d tup).length = lambdas.length ∧
    lagrangeCombine lambdas (mpcPow7Shares d tup) = sbox7 (lagrangeCombine lambdas xSh)
  unfold mpcPow7Shares
  dsimp only
  let d2 := Goldilocks.mul d d
  let d3 := Goldilocks.mul d2 d
  let d4 := Goldilocks.mul d2 d2
  let d5 := Goldilocks.mul d4 d
  let d6 := Goldilocks.mul d4 d2
  let d7 := Goldilocks.mul d4 d3
  let c1 := Goldilocks.mul (Goldilocks.ofNat 7) d6
  let c2 := Goldilocks.mul (Goldilocks.ofNat 21) d5
  let c3 := Goldilocks.mul (Goldilocks.ofNat 35) d4
  let c4 := Goldilocks.mul (Goldilocks.ofNat 35) d3
  let c5 := Goldilocks.mul (Goldilocks.ofNat 21) d2
  let c6 := Goldilocks.mul (Goldilocks.ofNat 7) d
  have hLenA1 : (shareAddConst d7 (shareScale c1 tup.rSh)).length = lambdas.length := by
    simp [hL1]
  have hLenA2 : (ringListZipAdd (shareScale c2 tup.r2Sh) (shareScale c3 tup.r3Sh)).length = lambdas.length := by
    rw [ringListZipAdd_length_of_eq (by simp [hL2, hL3])]; simp [hL2]
  have hLenL : (ringListZipAdd (shareAddConst d7 (shareScale c1 tup.rSh))
      (ringListZipAdd (shareScale c2 tup.r2Sh) (shareScale c3 tup.r3Sh))).length = lambdas.length := by
    rw [ringListZipAdd_length_of_eq (hLenA1.trans hLenA2.symm), hLenA1]
  have hLenB1 : (ringListZipAdd (shareScale c4 tup.r4Sh) (shareScale c5 tup.r5Sh)).length = lambdas.length := by
    rw [ringListZipAdd_length_of_eq (by simp [hL4, hL5])]; simp [hL4]
  have hLenB2 : (ringListZipAdd (shareScale c6 tup.r6Sh) tup.r7Sh).length = lambdas.length := by
    rw [ringListZipAdd_length_of_eq (by simp [hL6, hL7])]; simp [hL6]
  have hLenR : (ringListZipAdd
      (ringListZipAdd (shareScale c4 tup.r4Sh) (shareScale c5 tup.r5Sh))
      (ringListZipAdd (shareScale c6 tup.r6Sh) tup.r7Sh)).length = lambdas.length := by
    rw [ringListZipAdd_length_of_eq (hLenB1.trans hLenB2.symm), hLenB1]
  have hTotalLen : (ringListZipAdd
      (ringListZipAdd (shareAddConst d7 (shareScale c1 tup.rSh))
        (ringListZipAdd (shareScale c2 tup.r2Sh) (shareScale c3 tup.r3Sh)))
      (ringListZipAdd
        (ringListZipAdd (shareScale c4 tup.r4Sh) (shareScale c5 tup.r5Sh))
        (ringListZipAdd (shareScale c6 tup.r6Sh) tup.r7Sh))).length = lambdas.length := by
    rw [ringListZipAdd_length_of_eq (hLenL.trans hLenR.symm), hLenL]
  refine ⟨hTotalLen, ?_⟩
  unfold lagrangeCombine at hE2 hE3 hE4 hE5 hE6 hE7 ⊢
  have hOneMulD7 : CommRingOps.mul Goldilocks.one d7 = d7 := LawfulCommRing.one_mul d7
  rw [ringDot_zipAdd (hLenL.trans hLenR.symm),
      ringDot_zipAdd (hLenA1.trans hLenA2.symm),
      ringDot_zipAdd (hLenB1.trans hLenB2.symm),
      ringDot_addConst d7 (by simp [hL1]),
      hSumOne, hOneMulD7,
      ringDot_zipAdd (by simp [hL2, hL3]),
      ringDot_zipAdd (by simp [hL4, hL5]),
      ringDot_zipAdd (by simp [hL6, hL7]),
      ringDot_scale, ringDot_scale, ringDot_scale, ringDot_scale, ringDot_scale, ringDot_scale,
      hE2, hE3, hE4, hE5, hE6, hE7]
  have hd : d = Goldilocks.sub (ringDot lambdas xSh) (ringDot lambdas tup.rSh) := by
    dsimp only [d]; unfold lagrangeCombine
    exact ringDot_zipSub (hXLen.trans hL1.symm)
  dsimp only [c1, c2, c3, c4, c5, c6, d7, d6, d5, d4, d3, d2]
  rw [hd]
  exact power7BinomialEval_eq_sbox7 (ringDot lambdas xSh) (ringDot lambdas tup.rSh)

/-- Honest 1-round `Π_pow7` opening & zero-sum SPDZ `GoldilocksExt2` `MacCheck` broadcast generator. -/
def openSharedPow7Input
    (lambdas xSh : List Goldilocks) (tup : SharedPow7Tuple)
    (macX macR alphaShares zeroMasks : List GoldilocksExt2) :
    Goldilocks × List GoldilocksExt2 :=
  let dOpened := lagrangeCombine lambdas (shareZipSub xSh tup.rSh)
  let macD := shareZipSub macX macR
  let sigmas := spdzComputeSigmas (GoldilocksExt2.ofBase dOpened) macD alphaShares zeroMasks
  (dOpened, sigmas)

/-- **Maliciously Authenticated Share-Level `Π_pow7` S-Box (`evalSharedPow7Binomial`)**:
    Verifies the distributed `GoldilocksExt2` zero-sum SPDZ MAC over `dOpened = x - r`
    (`verifySpdzZeroSumMac sigmas`); aborts with `none` on any MAC failure and otherwise outputs
    the party-local Shamir shares `mpcPow7Shares dOpened tup`. -/
def evalSharedPow7Binomial
    (dOpened : Goldilocks) (tup : SharedPow7Tuple)
    (sigmas : List GoldilocksExt2) : Option (List Goldilocks) :=
  if verifySpdzZeroSumMac sigmas then
    some (mpcPow7Shares dOpened tup)
  else
    none

/-- **Authenticated Share-Level `Π_pow7` Completeness (`evalSharedPow7Binomial_complete`)**:
    Under valid `(t, n)` Shamir shares and additive `GoldilocksExt2` SPDZ MAC shares, honest
    `openSharedPow7Input` passes `evalSharedPow7Binomial` (`= some ySh`) with
    `lagrangeCombine lambdas ySh = sbox7 (lagrangeCombine lambdas xSh)`. -/
theorem evalSharedPow7Binomial_complete
    (lambdas xSh : List Goldilocks) (tup : SharedPow7Tuple)
    (macX macR alphaShares zeroMasks : List GoldilocksExt2)
    (hSumOne : ringListSum lambdas = Goldilocks.one)
    (hXLen : xSh.length = lambdas.length)
    (hTup : tup.validAt lambdas)
    (hMacXLen : macX.length = alphaShares.length)
    (hMacRLen : macR.length = alphaShares.length)
    (hMaskLen : zeroMasks.length = alphaShares.length)
    (hMacXSum : ringListSum macX = CommRingOps.mul (ringListSum alphaShares) (GoldilocksExt2.ofBase (lagrangeCombine lambdas xSh)))
    (hMacRSum : ringListSum macR = CommRingOps.mul (ringListSum alphaShares) (GoldilocksExt2.ofBase (lagrangeCombine lambdas tup.rSh)))
    (hZeroMask : ringListSum zeroMasks = CommRingOps.zero) :
    let (dOpened, sigmas) := openSharedPow7Input lambdas xSh tup macX macR alphaShares zeroMasks
    ∃ ySh : List Goldilocks,
      evalSharedPow7Binomial dOpened tup sigmas = some ySh ∧
      ySh.length = lambdas.length ∧
      lagrangeCombine lambdas ySh = sbox7 (lagrangeCombine lambdas xSh) := by
  dsimp only [openSharedPow7Input]
  let dOpened := lagrangeCombine lambdas (shareZipSub xSh tup.rSh)
  have hRLen : tup.rSh.length = lambdas.length := hTup.1
  have hdEq : dOpened = Goldilocks.sub (lagrangeCombine lambdas xSh) (lagrangeCombine lambdas tup.rSh) := by
    dsimp only [dOpened]; unfold lagrangeCombine
    exact ringDot_zipSub (hXLen.trans hRLen.symm)
  have hMacDLen : (shareZipSub macX macR).length = alphaShares.length := by
    rw [shareZipSub_length_of_eq (hMacXLen.trans hMacRLen.symm), hMacXLen]
  have hMacDSum : ringListSum (shareZipSub macX macR) =
      CommRingOps.mul (ringListSum alphaShares) (GoldilocksExt2.ofBase dOpened) := by
    rw [ringListSum_zipSub (hMacXLen.trans hMacRLen.symm), hMacXSum, hMacRSum,
        ← LawfulCommRing.mul_sub, hdEq]
    congr 1
  have hVer := verifySpdzZeroSumMac_complete
    (GoldilocksExt2.ofBase dOpened) (GoldilocksExt2.ofBase dOpened)
    (shareZipSub macX macR) alphaShares zeroMasks hMacDLen hMaskLen hMacDSum hZeroMask rfl
  obtain ⟨hYLen, hYComb⟩ := lagrangeCombine_mpcPow7Shares_eq_sbox7 lambdas xSh tup hSumOne hXLen hTup
  refine ⟨mpcPow7Shares dOpened tup, ?_, hYLen, hYComb⟩
  unfold evalSharedPow7Binomial
  rw [hVer]
  rfl

/-- **Authenticated Share-Level `Π_pow7` Malicious Soundness (`evalSharedPow7Binomial_forged_pins_key`)**:
    Any tampered masked opening `dOpened ≠ x - r` accepted by `evalSharedPow7Binomial` under
    arbitrary adversary broadcast shift `deltaSigma` uniquely pins the global MAC key
    `α ∈ GoldilocksExt2` (`≤ 1` key out of `goldilocksPrime ^ 2 > 2 ^ 127`, soundness `< 2^{-127}`). -/
theorem evalSharedPow7Binomial_forged_pins_key
    (lambdas xSh : List Goldilocks) (tup : SharedPow7Tuple)
    (dOpened : Goldilocks) (alpha deltaSigma : GoldilocksExt2)
    (sigmas : List GoldilocksExt2) (ySh : List Goldilocks)
    (hTamper : dOpened ≠ Goldilocks.sub (lagrangeCombine lambdas xSh) (lagrangeCombine lambdas tup.rSh))
    (hSum : ringListSum sigmas = CommRingOps.sub
      (CommRingOps.add (CommRingOps.mul alpha (GoldilocksExt2.ofBase
        (Goldilocks.sub (lagrangeCombine lambdas xSh) (lagrangeCombine lambdas tup.rSh)))) deltaSigma)
      (CommRingOps.mul alpha (GoldilocksExt2.ofBase dOpened)))
    (hAccept : evalSharedPow7Binomial dOpened tup sigmas = some ySh) :
    alpha = CommRingOps.mul deltaSigma (GoldilocksExt2.inv (CommRingOps.sub
      (GoldilocksExt2.ofBase dOpened)
      (GoldilocksExt2.ofBase (Goldilocks.sub (lagrangeCombine lambdas xSh) (lagrangeCombine lambdas tup.rSh))))) := by
  unfold evalSharedPow7Binomial at hAccept
  cases hVer : verifySpdzZeroSumMac sigmas with
  | false => rw [hVer] at hAccept; cases hAccept
  | true =>
    have hNeK : GoldilocksExt2.ofBase dOpened ≠
        GoldilocksExt2.ofBase (Goldilocks.sub (lagrangeCombine lambdas xSh) (lagrangeCombine lambdas tup.rSh)) :=
      fun hEq => hTamper (GoldilocksExt2.ofBase_injective hEq)
    exact verifySpdzZeroSumMac_forged_pins_key alpha _ _ deltaSigma sigmas hNeK hSum hVer

def demoPow7TupleFor4 : SharedPow7Tuple :=
  -- Genuine non-constant degree-1 2-of-3 Shamir shares at x = [1, 2, 3] for r = 4:
  -- r^1 = 4, r^2 = 16, r^3 = 64, r^4 = 256, r^5 = 1024, r^6 = 4096, r^7 = 16384
  -- Polynomials: r^k + k * X
  { rSh  := [Goldilocks.ofNat 5,     Goldilocks.ofNat 6,     Goldilocks.ofNat 7]
    r2Sh := [Goldilocks.ofNat 18,    Goldilocks.ofNat 20,    Goldilocks.ofNat 22]
    r3Sh := [Goldilocks.ofNat 67,    Goldilocks.ofNat 70,    Goldilocks.ofNat 73]
    r4Sh := [Goldilocks.ofNat 260,   Goldilocks.ofNat 264,   Goldilocks.ofNat 268]
    r5Sh := [Goldilocks.ofNat 1029,  Goldilocks.ofNat 1034,  Goldilocks.ofNat 1039]
    r6Sh := [Goldilocks.ofNat 4102,  Goldilocks.ofNat 4108,  Goldilocks.ofNat 4114]
    r7Sh := [Goldilocks.ofNat 16391, Goldilocks.ofNat 16398, Goldilocks.ofNat 16405] }

/-- **Inhabitedness Witness (`evalSharedPow7Binomial_inhabited`)**:
    Evaluating `evalSharedPow7Binomial` on degree-1 2-of-3 Shamir shares of `x = 9` (`9 + 2X -> [11, 13, 15]`)
    and `demoPow7TupleFor4` (`r = 4`) returns `some ySh` recombining to `sbox7 9 = 4782969`. -/
theorem evalSharedPow7Binomial_inhabited :
    let xSh := [Goldilocks.ofNat 11, Goldilocks.ofNat 13, Goldilocks.ofNat 15]
    let (dOpened, sigmas) := openSharedPow7Input demoLambdas2of3 xSh demoPow7TupleFor4
      (mkDemoMacShares 9) (mkDemoMacShares 4) demoAlphaShares3 demoZeroMasks3
    dOpened = Goldilocks.ofNat 5 ∧
    (match evalSharedPow7Binomial dOpened demoPow7TupleFor4 sigmas with
     | some ySh => lagrangeCombine demoLambdas2of3 ySh == sbox7 (Goldilocks.ofNat 9)
     | none => false) = true := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- **`#tooth` Tampered `Π_pow7` Masked Opening & MAC Refusal (`tooth_evalSharedPow7Binomial_rejects_mac_tamper`)**:
    Corrupting the opened masked scalar from `d = 5` (`9 - 4`) to `d_bad = 6` causes the committee's
    `spdzComputeSigmas` broadcast to fail `verifySpdzZeroSumMac`, so `evalSharedPow7Binomial` aborts (`= none`),
    and corrupting a single party's `σ_0` share likewise aborts (`= none`)! -/
theorem tooth_evalSharedPow7Binomial_rejects_mac_tamper :
    let dBad := Goldilocks.ofNat 6
    let macD := shareZipSub (mkDemoMacShares 9) (mkDemoMacShares 4)
    let sigmasOnBad := spdzComputeSigmas (GoldilocksExt2.ofBase dBad) macD demoAlphaShares3 demoZeroMasks3
    let (_, honestSigmas) := openSharedPow7Input demoLambdas2of3
      [Goldilocks.ofNat 11, Goldilocks.ofNat 13, Goldilocks.ofNat 15] demoPow7TupleFor4
      (mkDemoMacShares 9) (mkDemoMacShares 4) demoAlphaShares3 demoZeroMasks3
    let corruptedSigmas := match honestSigmas with
      | s0 :: rest => CommRingOps.add s0 CommRingOps.one :: rest
      | [] => []
    evalSharedPow7Binomial dBad demoPow7TupleFor4 sigmasOnBad = none ∧
    evalSharedPow7Binomial (Goldilocks.ofNat 5) demoPow7TupleFor4 corruptedSigmas = none := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-! ### Share-Level `(t, n)` Shamir `Poseidon2` Permutation & Sponge Oracles (`mkShamirPoseidon2MpcOracles`) -/

/-- Recombine 4-lane `Goldilocks` share vectors across a Shamir quorum. -/
def lagrangeCombineLane4 : List Goldilocks → List Lane4 → Lane4
  | [], _ => lane4Zero
  | _, [] => lane4Zero
  | l :: ls, b :: bs => lane4Add (lane4Scale l b) (lagrangeCombineLane4 ls bs)

/-- Recombine width-12 `Poseidon2State12` shares across a Shamir quorum. -/
def lagrangeCombineState12 : List Goldilocks → List Poseidon2State12 → Poseidon2State12
  | [], _ => state12Zero
  | _, [] => state12Zero
  | l :: ls, s :: ss => state12Add (state12Scale l s) (lagrangeCombineState12 ls ss)

theorem lagrangeCombineState12_map_applyME :
    ∀ (ls : List Goldilocks) (ss : List Poseidon2State12),
      lagrangeCombineState12 ls (ss.map applyME) = applyME (lagrangeCombineState12 ls ss)
  | [], _ => by simp [lagrangeCombineState12, applyME_zero]
  | _ :: _, [] => by simp [lagrangeCombineState12, applyME_zero]
  | l :: ls, s :: ss => by
    simp only [List.map_cons, lagrangeCombineState12,
      lagrangeCombineState12_map_applyME ls ss, applyME_add, applyME_scale]


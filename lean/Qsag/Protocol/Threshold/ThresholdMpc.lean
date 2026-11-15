module
/-
# Qsag.Protocol.Threshold.ThresholdMpc — Distributed Post-Quantum Threshold Signing (`Depth = 1 + w`, RSS & Shamir)

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
4. Checked stateless & production Rust-exact threshold paths (`HashSigs` Section 6 weld:
   `thresholdStatelessCheckedSign_eq_evalStatelessCheckedSign`,
   `thresholdProductionStatelessSign_eq_evalProductionStatelessSign`,
   `thresholdProductionStatefulSign_eq_evalProductionStatefulSign`) covering
   `H_INTERNAL` vs `H_MSG`, XOF-derived FORS indices, `(j, u)` FORS ADRS, `kp0` FORS Merkle
   `keyPair`. Separately, `execActiveSharedPow7Round_sound_or_pins_key` checks an active SPDZ
   gate; `execActiveSharedPoseidon2Perm_sound_or_pins_key` composes all 118 gates of the
   30-round permutation, propagates additive MAC shares, and preserves authentication on
   correct output. Zero-opening-deviation accepted runs refine the frozen passive permutation
   API at the party-share level. `execActiveShamirAbsorbRate8Block` additionally handles one
   rate-8 block with authenticated message limbs. `execActiveShamirBlocks` composes arbitrary
   block streams with bounded gate fault witnesses and refines `shamirAbsorbLimbStream`.
   The authenticated `decomp8`, chain,
   and oracle bundle are not yet threaded through this authenticated state; whole-signer active Shamir composition remains open.
5. Threshold FIPS 205 output equal to the single-signer output for every correct run
   (`threshold_sig_deterministic_and_matches_single_signer`; a functional-correctness and
   determinism statement about runs that carry a proof of oracle correctness, with no adversary
   and no probability space): share-level `Keccak`/`SHAKE256`
   for 2-of-3 RSS (`SlhThresholdRun.ofRss`), and quorum-recombination `SlhMpcOracles` interface for
   `(t, n)` Shamir FIPS 205 (`SlhThresholdRun.ofShamir`, while `(t, n)` Shamir share-level `Poseidon2`
   honest signing is realized by `mkShamirPoseidon2MpcOracles`).
6. One actively corrupt party in a hedged signing run
   (`active_malicious_threshold_sig_abort_or_exact_hedged_dist`): every run aborts, releases the
   exact single-signer signature on hedge `honestCoin ⊕ corruptCoin`, or is a counted tag forgery;
   the released law is the single-signer hedged law restricted to the corrupt party's release
   set, and the abort pattern is independent of the key in that game. The strategy-to-interactive
   transcript refinement is a separate obligation, not proved by this abstract game.
-/

public import Qsag.Math.Goldilocks
public import Qsag.Math.BinaryTower
public import Qsag.Oracle.Keccak
public import Qsag.Oracle.Poseidon2
public import Qsag.Oracle.UcGames
public import Qsag.Protocol.Signing.HashSigs
public import Qsag.Protocol.Signing.Fips205
public import Qsag.Protocol.Threshold.Preprocessing

public import Qsag.Math.Constructive
import all Qsag.Math.Goldilocks
import all Qsag.Oracle.Poseidon2
import all Qsag.Oracle.UcGames
import all Qsag.Protocol.Signing.HashSigs
import all Qsag.Protocol.Threshold.Preprocessing

import Qsag.Tactic.AssuranceKit

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

/-- Pairwise 64-bit PRF randomness words `(r0, r1, r2)` where Party $i$ holds `(r_i, r_{i+1})`.

    "PrfZero" names the zero-sharing the parties derive from these words, not a constraint on the
    words: party `i` masks its product share with `r_i ^^^ r_{i+1}` (`mask0`, `mask1`, `mask2`),
    and those three masks XOR to zero for every value of `(r0, r1, r2)`
    (`RssPrfZeroSeeds.masks_xor_eq_zero`). The words themselves carry no invariant, and the
    predicate `r0 ^^^ r1 ^^^ r2 = 0` (`SeedsXorZero`) must not be imposed on them: under it each
    party could compute the word it does not hold
    (`tooth_rssPrfZeroSeeds_seedsXorZero_reveals_third_word`).

    How the words are produced (pairwise PRF keys, their expansion, the preprocessing that
    distributes them) is not modelled. Every theorem over this structure, and over the tapes
    `Nat → Nat → Nat → Nat → RssPrfZeroSeeds`, quantifies over arbitrary values; such theorems are
    correctness statements and say nothing about the distribution of the words. -/
structure RssPrfZeroSeeds where
  r0 : UInt64
  r1 : UInt64
  r2 : UInt64
  deriving DecidableEq, Repr

def zeroRssSeeds : RssPrfZeroSeeds := ⟨0, 0, 0⟩

/-- Party 0's zero-share word `r0 ^^^ r1`. -/
def RssPrfZeroSeeds.mask0 (s : RssPrfZeroSeeds) : UInt64 := s.r0 ^^^ s.r1

/-- Party 1's zero-share word `r1 ^^^ r2`. -/
def RssPrfZeroSeeds.mask1 (s : RssPrfZeroSeeds) : UInt64 := s.r1 ^^^ s.r2

/-- Party 2's zero-share word `r2 ^^^ r0`. -/
def RssPrfZeroSeeds.mask2 (s : RssPrfZeroSeeds) : UInt64 := s.r2 ^^^ s.r0

/-- The predicate `r0 ^^^ r1 ^^^ r2 = 0` on the words themselves. It is not an invariant of
    `RssPrfZeroSeeds` and no theorem in this module assumes it; it is named so that the teeth
    below can state why. -/
def RssPrfZeroSeeds.SeedsXorZero (s : RssPrfZeroSeeds) : Prop := s.r0 ^^^ s.r1 ^^^ s.r2 = 0

/-- **Zero-sum invariant of the derived masks.** For every `(r0, r1, r2)` the three per-party
    masks XOR to zero. This is the zero-sharing the name refers to; it holds by construction and
    needs no hypothesis on the words. -/
theorem RssPrfZeroSeeds.masks_xor_eq_zero (s : RssPrfZeroSeeds) :
    s.mask0 ^^^ s.mask1 ^^^ s.mask2 = 0 := by
  unfold RssPrfZeroSeeds.mask0 RssPrfZeroSeeds.mask1 RssPrfZeroSeeds.mask2
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor, UInt64.toBitVec_zero, BitVec.getLsbD_zero]
  cases s.r0.toBitVec.getLsbD i <;> cases s.r1.toBitVec.getLsbD i <;>
    cases s.r2.toBitVec.getLsbD i <;> rfl

/-- **`#tooth` (`tooth_rssPrfZeroSeeds_seedsXorZero_reveals_third_word`)**: if the words
    themselves XORed to zero, party 0, which holds `(r0, r1)`, could compute `r2`. The pairwise
    words are therefore left unconstrained. -/
theorem tooth_rssPrfZeroSeeds_seedsXorZero_reveals_third_word (s : RssPrfZeroSeeds)
    (h : s.SeedsXorZero) : s.r2 = s.r0 ^^^ s.r1 :=
  (UInt64.xor_eq_zero_iff.mp h).symm

/-- **`#tooth` (`tooth_rssPrfZeroSeeds_masks_zero_without_seedsXorZero`)**: the words `(1, 0, 0)`
    violate `SeedsXorZero`, and their masks still XOR to zero. The mask invariant does not depend
    on the word-level predicate. -/
theorem tooth_rssPrfZeroSeeds_masks_zero_without_seedsXorZero :
    ¬ (⟨1, 0, 0⟩ : RssPrfZeroSeeds).SeedsXorZero ∧
    (⟨1, 0, 0⟩ : RssPrfZeroSeeds).mask0 ^^^ (⟨1, 0, 0⟩ : RssPrfZeroSeeds).mask1 ^^^
      (⟨1, 0, 0⟩ : RssPrfZeroSeeds).mask2 = 0 := by
  refine ⟨?_, RssPrfZeroSeeds.masks_xor_eq_zero _⟩
  show ¬ ((1 : UInt64) ^^^ 0 ^^^ 0 = 0)
  decide

/-- Local 1-party 64-bit bitsliced AND step: accesses ONLY Party $i$'s 2-of-3 view `(ax_i, ax_next)`. -/
@[inline] def rssPartyAndLocal (ax_i ax_next bx_i bx_next r_i r_next : UInt64) : UInt64 :=
  (ax_i &&& bx_i) ^^^ (ax_i &&& bx_next) ^^^ (ax_next &&& bx_i) ^^^ (r_i ^^^ r_next)

@[inline] def rssWordAnd (a b : RssWord64) (seeds : RssPrfZeroSeeds) : RssWord64 :=
  ⟨rssPartyAndLocal a.x0 a.x1 b.x0 b.x1 seeds.r0 seeds.r1,
   rssPartyAndLocal a.x1 a.x2 b.x1 b.x2 seeds.r1 seeds.r2,
   rssPartyAndLocal a.x2 a.x0 b.x2 b.x0 seeds.r2 seeds.r0⟩

/-- The three output shares of `rssWordAnd` are the local product terms masked by `mask0`,
    `mask1`, `mask2`: the masks of `RssPrfZeroSeeds.masks_xor_eq_zero` are the ones the protocol
    step applies. -/
theorem rssWordAnd_eq_masked_products (a b : RssWord64) (seeds : RssPrfZeroSeeds) :
    rssWordAnd a b seeds =
      ⟨(a.x0 &&& b.x0) ^^^ (a.x0 &&& b.x1) ^^^ (a.x1 &&& b.x0) ^^^ seeds.mask0,
       (a.x1 &&& b.x1) ^^^ (a.x1 &&& b.x2) ^^^ (a.x2 &&& b.x1) ^^^ seeds.mask1,
       (a.x2 &&& b.x2) ^^^ (a.x2 &&& b.x0) ^^^ (a.x0 &&& b.x2) ^^^ seeds.mask2⟩ := by
  simp only [rssWordAnd, rssPartyAndLocal, RssPrfZeroSeeds.mask0, RssPrfZeroSeeds.mask1,
    RssPrfZeroSeeds.mask2]

theorem reconstructRssWord_rssWordAnd (a b : RssWord64) (seeds : RssPrfZeroSeeds) :
    reconstructRssWord (rssWordAnd a b seeds) = (reconstructRssWord a &&& reconstructRssWord b) := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [reconstructRssWord, rssWordAnd, rssPartyAndLocal,
    UInt64.toBitVec_xor, UInt64.toBitVec_and, BitVec.getLsbD_xor, BitVec.getLsbD_and]
  exact rssBoolAnd_identity _ _ _ _ _ _ _ _ _


/-- Every pair of mask words occurs: zero-sum constrains only the third mask, not the first two.
    This algebraic range statement does not assume or assert a randomness distribution. -/
theorem RssPrfZeroSeeds.masks_pair_surjective (m0 m1 : UInt64) :
    ∃ s : RssPrfZeroSeeds, s.mask0 = m0 ∧ s.mask1 = m1 ∧ s.mask2 = m0 ^^^ m1 := by
  refine ⟨⟨0, m0, m0 ^^^ m1⟩, ?_, ?_, ?_⟩ <;>
    simp [RssPrfZeroSeeds.mask0, RssPrfZeroSeeds.mask1, RssPrfZeroSeeds.mask2,
      ← UInt64.xor_assoc]

/-- Changing the masking tape changes shares but never the reconstructed AND result. -/
theorem rssWordAnd_reconstruction_seed_independent (a b : RssWord64)
    (s t : RssPrfZeroSeeds) :
    reconstructRssWord (rssWordAnd a b s) = reconstructRssWord (rssWordAnd a b t) := by
  rw [reconstructRssWord_rssWordAnd, reconstructRssWord_rssWordAnd]

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

set_option maxHeartbeats 800000 in
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

/-- **Share-Grounded Active `Π_pow7` Round Execution (`execActiveSharedPow7Round`)**:
    Computes the masked opening `dOpened = ⟨λ, x - r⟩ + deltaD` and the committee's SPDZ
    `GoldilocksExt2` `MacCheck` broadcast `spdzComputeSigmas(dOpened, macX - macR, α, z) + sigmaDevs`
    directly from the authenticated party shares `(xSh, tup, macX, macR, alphaShares, zeroMasks)`
    under active opening shift `deltaD` and active MAC broadcast shifts `sigmaDevs`, then runs
    `evalSharedPow7Binomial` (aborting with `none` on any MAC mismatch). -/
def execActiveSharedPow7Round
    (lambdas xSh : List Goldilocks) (tup : SharedPow7Tuple)
    (macX macR alphaShares zeroMasks : List GoldilocksExt2)
    (deltaD : Goldilocks) (sigmaDevs : List GoldilocksExt2) : Option (List Goldilocks) :=
  let dTrue := lagrangeCombine lambdas (shareZipSub xSh tup.rSh)
  let dOpened := Goldilocks.add dTrue deltaD
  let macD := shareZipSub macX macR
  let honestSigmas := spdzComputeSigmas (GoldilocksExt2.ofBase dOpened) macD alphaShares zeroMasks
  let sigmas := ringListZipAdd honestSigmas sigmaDevs
  evalSharedPow7Binomial dOpened tup sigmas

/-- **Share-Grounded Active `Π_pow7` Soundness Without External `hSum`
    (`execActiveSharedPow7Round_sound_or_pins_key`)**:
    Derives the SPDZ residual identity directly from the authenticated shares `(macX, macR, zeroMasks)`
    with **zero** assumed `hSum` premise: whenever `execActiveSharedPow7Round` accepts (`= some ySh`),
    either `deltaD = 0` and `ySh` recombines to the exact `sbox7 (lagrangeCombine lambdas xSh)`, or
    `deltaD ≠ 0` and the global MAC key `∑ α_i ∈ GoldilocksExt2` is uniquely pinned to
    `(∑ sigmaDevs) · (ofBase deltaD)⁻¹` (`≤ 1` key out of `goldilocksPrime ^ 2 > 2 ^ 127`). -/
theorem execActiveSharedPow7Round_sound_or_pins_key
    (lambdas xSh : List Goldilocks) (tup : SharedPow7Tuple)
    (macX macR alphaShares zeroMasks : List GoldilocksExt2)
    (deltaD : Goldilocks) (sigmaDevs : List GoldilocksExt2)
    (ySh : List Goldilocks)
    (hSumOne : ringListSum lambdas = Goldilocks.one)
    (hXLen : xSh.length = lambdas.length)
    (hTup : tup.validAt lambdas)
    (hMacXLen : macX.length = alphaShares.length)
    (hMacRLen : macR.length = alphaShares.length)
    (hMaskLen : zeroMasks.length = alphaShares.length)
    (hMacXSum : ringListSum macX =
      CommRingOps.mul (ringListSum alphaShares) (GoldilocksExt2.ofBase (lagrangeCombine lambdas xSh)))
    (hMacRSum : ringListSum macR =
      CommRingOps.mul (ringListSum alphaShares) (GoldilocksExt2.ofBase (lagrangeCombine lambdas tup.rSh)))
    (hZeroMask : ringListSum zeroMasks = CommRingOps.zero)
    (hAccept : execActiveSharedPow7Round lambdas xSh tup macX macR alphaShares zeroMasks deltaD sigmaDevs = some ySh) :
    (deltaD = Goldilocks.zero ∧ ySh.length = lambdas.length ∧
      lagrangeCombine lambdas ySh = sbox7 (lagrangeCombine lambdas xSh)) ∨
    (deltaD ≠ Goldilocks.zero ∧
      ringListSum alphaShares =
        CommRingOps.mul (ringListSum sigmaDevs) (GoldilocksExt2.inv (GoldilocksExt2.ofBase deltaD))) := by
  let dTrue := lagrangeCombine lambdas (shareZipSub xSh tup.rSh)
  let dOpened := Goldilocks.add dTrue deltaD
  have hdTrueEq : dTrue = Goldilocks.sub (lagrangeCombine lambdas xSh) (lagrangeCombine lambdas tup.rSh) := by
    dsimp only [dTrue]; unfold lagrangeCombine
    exact ringDot_zipSub (hXLen.trans hTup.1.symm)
  by_cases hZeroD : deltaD = Goldilocks.zero
  · left
    have hdOpenEq : dOpened = dTrue := by
      dsimp only [dOpened]; rw [hZeroD]; exact LawfulCommRing.add_zero dTrue
    unfold execActiveSharedPow7Round evalSharedPow7Binomial at hAccept
    dsimp only at hAccept
    cases hVer : verifySpdzZeroSumMac (ringListZipAdd
        (spdzComputeSigmas (GoldilocksExt2.ofBase dOpened) (shareZipSub macX macR) alphaShares zeroMasks) sigmaDevs) with
    | false =>
      change (if verifySpdzZeroSumMac _ then _ else none) = some ySh at hAccept
      rw [hVer] at hAccept; cases hAccept
    | true =>
      change (if verifySpdzZeroSumMac _ then some (mpcPow7Shares dOpened tup) else none) = some ySh at hAccept
      rw [hVer] at hAccept
      simp only [↓reduceIte, Option.some.injEq] at hAccept
      subst hAccept
      rw [hdOpenEq]
      obtain ⟨hYLen, hYComb⟩ := lagrangeCombine_mpcPow7Shares_eq_sbox7 lambdas xSh tup hSumOne hXLen hTup
      exact ⟨hZeroD, hYLen, hYComb⟩
  · right
    have hTamper : dOpened ≠ Goldilocks.sub (lagrangeCombine lambdas xSh) (lagrangeCombine lambdas tup.rSh) := by
      rw [← hdTrueEq]
      intro hEq
      have hEq' : CommRingOps.add dTrue deltaD = CommRingOps.add dTrue Goldilocks.zero := by
        change CommRingOps.add dTrue deltaD = CommRingOps.add dTrue CommRingOps.zero
        rw [LawfulCommRing.add_zero]; exact hEq
      exact hZeroD (LawfulCommRing.add_left_cancel hEq')
    have hMacDLen : (shareZipSub macX macR).length = alphaShares.length := by
      rw [shareZipSub_length_of_eq (hMacXLen.trans hMacRLen.symm), hMacXLen]
    have hMacDSum : ringListSum (shareZipSub macX macR) =
        CommRingOps.mul (ringListSum alphaShares)
          (GoldilocksExt2.ofBase (Goldilocks.sub (lagrangeCombine lambdas xSh) (lagrangeCombine lambdas tup.rSh))) := by
      rw [ringListSum_zipSub (hMacXLen.trans hMacRLen.symm), hMacXSum, hMacRSum,
          ← LawfulCommRing.mul_sub, ← GoldilocksExt2.ofBase_sub]
      rfl
    have hSubAddComm : ∀ (A B C : GoldilocksExt2),
        CommRingOps.add (CommRingOps.sub A B) C = CommRingOps.sub (CommRingOps.add A C) B := fun A B C => by
      rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.sub_eq_add_neg,
          LawfulCommRing.add_assoc, LawfulCommRing.add_comm (CommRingOps.neg B) C, ← LawfulCommRing.add_assoc]
    have hSumDerived :
        ringListSum (ringListZipAdd
          (spdzComputeSigmas (GoldilocksExt2.ofBase dOpened) (shareZipSub macX macR) alphaShares zeroMasks)
          sigmaDevs) =
        CommRingOps.sub
          (CommRingOps.add
            (CommRingOps.mul (ringListSum alphaShares)
              (GoldilocksExt2.ofBase (Goldilocks.sub (lagrangeCombine lambdas xSh) (lagrangeCombine lambdas tup.rSh))))
            (ringListSum sigmaDevs))
          (CommRingOps.mul (ringListSum alphaShares) (GoldilocksExt2.ofBase dOpened)) := by
      rw [ringListSum_zipAdd, ringListSum_spdzComputeSigmas _ hMacDLen hMaskLen,
          hZeroMask, LawfulCommRing.add_zero, hMacDSum, hSubAddComm]
    have hPin := evalSharedPow7Binomial_forged_pins_key lambdas xSh tup dOpened
      (ringListSum alphaShares) (ringListSum sigmaDevs) _ ySh hTamper hSumDerived hAccept
    have hDiffEq :
        CommRingOps.sub (GoldilocksExt2.ofBase dOpened)
          (GoldilocksExt2.ofBase (Goldilocks.sub (lagrangeCombine lambdas xSh) (lagrangeCombine lambdas tup.rSh))) =
        GoldilocksExt2.ofBase deltaD := by
      rw [← hdTrueEq, ← GoldilocksExt2.ofBase_sub]
      congr 1
      change CommRingOps.sub (CommRingOps.add dTrue deltaD) dTrue = deltaD
      rw [LawfulCommRing.add_comm dTrue deltaD, LawfulCommRing.sub_eq_add_neg,
          LawfulCommRing.add_assoc, LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]
    rw [hDiffEq] at hPin
    exact ⟨hZeroD, hPin⟩

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

/-- **`#tooth` Share-Grounded Active `Π_pow7` Rejects Unpinned Tampering
    (`tooth_execActiveSharedPow7Round_rejects_unpinned_tamper`)**:
    On authenticated 2-of-3 shares of `x = 9` and `r = 4`, honest execution (`deltaD = 0`, `sigmaDevs = 0`)
    succeeds and recombines to `sbox7 9`, whereas shifting the opened scalar by `deltaD = 1` without
    knowing `∑ α_i` aborts (`= none`), and shifting a MAC share by `1` while keeping `deltaD = 0`
    also aborts (`= none`). -/
theorem tooth_execActiveSharedPow7Round_rejects_unpinned_tamper :
    let xSh := [Goldilocks.ofNat 11, Goldilocks.ofNat 13, Goldilocks.ofNat 15]
    let zeroDevs : List GoldilocksExt2 := [CommRingOps.zero, CommRingOps.zero, CommRingOps.zero]
    let oneDevs  : List GoldilocksExt2 := [CommRingOps.one, CommRingOps.zero, CommRingOps.zero]
    (match execActiveSharedPow7Round demoLambdas2of3 xSh demoPow7TupleFor4
        (mkDemoMacShares 9) (mkDemoMacShares 4) demoAlphaShares3 demoZeroMasks3
        Goldilocks.zero zeroDevs with
     | some ySh => lagrangeCombine demoLambdas2of3 ySh == sbox7 (Goldilocks.ofNat 9)
     | none => false) = true ∧
    execActiveSharedPow7Round demoLambdas2of3 xSh demoPow7TupleFor4
      (mkDemoMacShares 9) (mkDemoMacShares 4) demoAlphaShares3 demoZeroMasks3
      Goldilocks.one zeroDevs = none ∧
    execActiveSharedPow7Round demoLambdas2of3 xSh demoPow7TupleFor4
      (mkDemoMacShares 9) (mkDemoMacShares 4) demoAlphaShares3 demoZeroMasks3
      Goldilocks.zero oneDevs = none := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

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

theorem lagrangeCombineState12_map_applyMI :
    ∀ (ls : List Goldilocks) (ss : List Poseidon2State12),
      lagrangeCombineState12 ls (ss.map applyMI) = applyMI (lagrangeCombineState12 ls ss)
  | [], _ => by simp [lagrangeCombineState12, applyMI_zero]
  | _ :: _, [] => by simp [lagrangeCombineState12, applyMI_zero]
  | l :: ls, s :: ss => by
    simp only [List.map_cons, lagrangeCombineState12,
      lagrangeCombineState12_map_applyMI ls ss, applyMI_add, applyMI_scale]

def zipLane4Shares : List Goldilocks → List Goldilocks → List Goldilocks → List Goldilocks → List Lane4
  | x0 :: xs0, x1 :: xs1, x2 :: xs2, x3 :: xs3 =>
    ⟨x0, x1, x2, x3⟩ :: zipLane4Shares xs0 xs1 xs2 xs3
  | _, _, _, _ => []

def zipState12Shares : List Lane4 → List Lane4 → List Lane4 → List Poseidon2State12
  | b0 :: bs0, b1 :: bs1, b2 :: bs2 =>
    ⟨b0, b1, b2⟩ :: zipState12Shares bs0 bs1 bs2
  | _, _, _ => []

private theorem zipLane4Shares_length :
    ∀ {xs0 xs1 xs2 xs3 : List Goldilocks} {n : Nat},
      xs0.length = n → xs1.length = n → xs2.length = n → xs3.length = n →
      (zipLane4Shares xs0 xs1 xs2 xs3).length = n
  | [], [], [], [], 0, _, _, _, _ => rfl
  | _ :: xs0, _ :: xs1, _ :: xs2, _ :: xs3, n + 1, h0, h1, h2, h3 => by
    simp only [zipLane4Shares, List.length_cons,
      zipLane4Shares_length (Nat.succ.inj h0) (Nat.succ.inj h1) (Nat.succ.inj h2) (Nat.succ.inj h3)]

private theorem zipState12Shares_length :
    ∀ {bs0 bs1 bs2 : List Lane4} {n : Nat},
      bs0.length = n → bs1.length = n → bs2.length = n →
      (zipState12Shares bs0 bs1 bs2).length = n
  | [], [], [], 0, _, _, _ => rfl
  | _ :: bs0, _ :: bs1, _ :: bs2, n + 1, h0, h1, h2 => by
    simp only [zipState12Shares, List.length_cons,
      zipState12Shares_length (Nat.succ.inj h0) (Nat.succ.inj h1) (Nat.succ.inj h2)]

private theorem lagrangeCombineLane4_zip :
    ∀ (ls xs0 xs1 xs2 xs3 : List Goldilocks),
      xs0.length = ls.length → xs1.length = ls.length →
      xs2.length = ls.length → xs3.length = ls.length →
      lagrangeCombineLane4 ls (zipLane4Shares xs0 xs1 xs2 xs3) =
        ⟨lagrangeCombine ls xs0, lagrangeCombine ls xs1,
         lagrangeCombine ls xs2, lagrangeCombine ls xs3⟩
  | [], [], [], [], [], _, _, _, _ => by
    simp [lagrangeCombineLane4, lagrangeCombine, ringDot, lane4Zero_eq]; rfl
  | l :: ls, x0 :: xs0, x1 :: xs1, x2 :: xs2, x3 :: xs3, h0, h1, h2, h3 => by
    simp only [zipLane4Shares, lagrangeCombineLane4,
      lagrangeCombineLane4_zip ls xs0 xs1 xs2 xs3
        (Nat.succ.inj h0) (Nat.succ.inj h1) (Nat.succ.inj h2) (Nat.succ.inj h3),
      lane4Scale_eq, lane4Add_eq, lagrangeCombine, ringDot]; rfl

private theorem lagrangeCombineState12_zip :
    ∀ (ls : List Goldilocks) (bs0 bs1 bs2 : List Lane4),
      bs0.length = ls.length → bs1.length = ls.length → bs2.length = ls.length →
      lagrangeCombineState12 ls (zipState12Shares bs0 bs1 bs2) =
        ⟨lagrangeCombineLane4 ls bs0, lagrangeCombineLane4 ls bs1, lagrangeCombineLane4 ls bs2⟩
  | [], [], [], [], _, _, _ => by simp [lagrangeCombineState12, state12Zero_eq]; rfl
  | l :: ls, b0 :: bs0, b1 :: bs1, b2 :: bs2, h0, h1, h2 => by
    simp only [zipState12Shares, lagrangeCombineState12,
      lagrangeCombineState12_zip ls bs0 bs1 bs2
        (Nat.succ.inj h0) (Nat.succ.inj h1) (Nat.succ.inj h2),
      state12Scale_eq, state12Add_eq]; rfl

private theorem lagrangeCombineLane4_proj :
    ∀ (ls : List Goldilocks) (bs : List Lane4),
      lagrangeCombineLane4 ls bs =
        ⟨lagrangeCombine ls (bs.map (·.x0)), lagrangeCombine ls (bs.map (·.x1)),
         lagrangeCombine ls (bs.map (·.x2)), lagrangeCombine ls (bs.map (·.x3))⟩
  | [], _ => by simp [lagrangeCombineLane4, lagrangeCombine, ringDot, lane4Zero_eq]; rfl
  | _ :: _, [] => by simp [lagrangeCombineLane4, lagrangeCombine, ringDot, lane4Zero_eq]; rfl
  | l :: ls, b :: bs => by
    simp only [List.map_cons, lagrangeCombineLane4, lagrangeCombineLane4_proj ls bs,
      lane4Scale_eq, lane4Add_eq, lagrangeCombine, ringDot]; rfl

private theorem lagrangeCombineState12_proj :
    ∀ (ls : List Goldilocks) (ss : List Poseidon2State12),
      lagrangeCombineState12 ls ss =
        ⟨lagrangeCombineLane4 ls (ss.map (·.b0)),
         lagrangeCombineLane4 ls (ss.map (·.b1)),
         lagrangeCombineLane4 ls (ss.map (·.b2))⟩
  | [], _ => by simp [lagrangeCombineState12, lagrangeCombineLane4, state12Zero_eq]
  | _ :: _, [] => by simp [lagrangeCombineState12, lagrangeCombineLane4, state12Zero_eq]
  | l :: ls, s :: ss => by
    simp only [List.map_cons, lagrangeCombineState12, lagrangeCombineState12_proj ls ss,
      state12Scale_eq, state12Add_eq]; rfl

private theorem ringDot_replicate_right {R : Type} [LawfulCommRing R] :
    ∀ (ls : List R) (c : R),
      ringDot ls (List.replicate ls.length c) = CommRingOps.mul (ringListSum ls) c
  | [], _ => by simp [ringDot, ringListSum, LawfulCommRing.zero_mul]
  | l :: ls, c => by
    simp only [List.length_cons, List.replicate_succ, ringDot, ringListSum,
      ringDot_replicate_right ls c, LawfulCommRing.right_distrib]

private theorem lagrangeCombine_add_public
    (ls xs : List Goldilocks) (rc : Goldilocks)
    (hSumOne : ringListSum ls = Goldilocks.one)
    (hLen : xs.length = ls.length) :
    lagrangeCombine ls (xs.map (fun x => Goldilocks.add x rc)) =
      Goldilocks.add (lagrangeCombine ls xs) rc := by
  have hComm : xs.map (fun x => Goldilocks.add x rc) = shareAddConst rc xs := by
    apply List.map_congr_left
    intro x _
    exact LawfulCommRing.add_comm x rc
  have hOneMul : CommRingOps.mul Goldilocks.one rc = rc := LawfulCommRing.one_mul rc
  rw [hComm]
  unfold lagrangeCombine
  rw [ringDot_addConst rc (by omega), hSumOne, hOneMul]
  exact LawfulCommRing.add_comm rc _

private theorem lagrangeCombine_map_add_public {α : Type}
    (ls : List Goldilocks) (ss : List α) (f : α → Goldilocks) (rc : Goldilocks)
    (hSumOne : ringListSum ls = Goldilocks.one)
    (hLen : ss.length = ls.length) :
    lagrangeCombine ls (ss.map (fun s => Goldilocks.add (f s) rc)) =
      Goldilocks.add (lagrangeCombine ls (ss.map f)) rc := by
  have hMap : ss.map (fun s => Goldilocks.add (f s) rc) = (ss.map f).map (fun x => Goldilocks.add x rc) := by
    rw [List.map_map]; rfl
  rw [hMap]
  exact lagrangeCombine_add_public ls (ss.map f) rc hSumOne (by rw [List.length_map, hLen])

private theorem lagrangeCombineState12_add_public
    (ls : List Goldilocks) (ss : List Poseidon2State12) (rc : Poseidon2State12)
    (hSumOne : ringListSum ls = Goldilocks.one)
    (hLen : ss.length = ls.length) :
    lagrangeCombineState12 ls (ss.map (fun s => state12Add s rc)) =
      state12Add (lagrangeCombineState12 ls ss) rc := by
  rw [lagrangeCombineState12_proj, lagrangeCombineState12_proj,
      lagrangeCombineLane4_proj, lagrangeCombineLane4_proj, lagrangeCombineLane4_proj,
      lagrangeCombineLane4_proj, lagrangeCombineLane4_proj, lagrangeCombineLane4_proj,
      state12Add_eq, lane4Add_eq, lane4Add_eq, lane4Add_eq]
  simp only [List.map_map]
  refine Poseidon2State12.ext (Lane4.ext ?_ ?_ ?_ ?_) (Lane4.ext ?_ ?_ ?_ ?_) (Lane4.ext ?_ ?_ ?_ ?_)
  · exact lagrangeCombine_map_add_public ls ss (fun s => s.b0.x0) rc.b0.x0 hSumOne hLen
  · exact lagrangeCombine_map_add_public ls ss (fun s => s.b0.x1) rc.b0.x1 hSumOne hLen
  · exact lagrangeCombine_map_add_public ls ss (fun s => s.b0.x2) rc.b0.x2 hSumOne hLen
  · exact lagrangeCombine_map_add_public ls ss (fun s => s.b0.x3) rc.b0.x3 hSumOne hLen
  · exact lagrangeCombine_map_add_public ls ss (fun s => s.b1.x0) rc.b1.x0 hSumOne hLen
  · exact lagrangeCombine_map_add_public ls ss (fun s => s.b1.x1) rc.b1.x1 hSumOne hLen
  · exact lagrangeCombine_map_add_public ls ss (fun s => s.b1.x2) rc.b1.x2 hSumOne hLen
  · exact lagrangeCombine_map_add_public ls ss (fun s => s.b1.x3) rc.b1.x3 hSumOne hLen
  · exact lagrangeCombine_map_add_public ls ss (fun s => s.b2.x0) rc.b2.x0 hSumOne hLen
  · exact lagrangeCombine_map_add_public ls ss (fun s => s.b2.x1) rc.b2.x1 hSumOne hLen
  · exact lagrangeCombine_map_add_public ls ss (fun s => s.b2.x2) rc.b2.x2 hSumOne hLen
  · exact lagrangeCombine_map_add_public ls ss (fun s => s.b2.x3) rc.b2.x3 hSumOne hLen

/-- Authenticated online S-box gate data `(dOpened, tup, sigmas)`. -/
structure AuthPow7Gate where
  dOpened : Goldilocks
  tup     : SharedPow7Tuple
  sigmas  : List GoldilocksExt2
  deriving DecidableEq, Repr

def AuthPow7Gate.validFor (lambdas xSh : List Goldilocks) (g : AuthPow7Gate) : Prop :=
  g.tup.validAt lambdas ∧
  g.dOpened = lagrangeCombine lambdas (shareZipSub xSh g.tup.rSh) ∧
  verifySpdzZeroSumMac g.sigmas = true

theorem evalSharedPow7Gate_simulates
    (lambdas xSh : List Goldilocks) (g : AuthPow7Gate)
    (hSumOne : ringListSum lambdas = Goldilocks.one)
    (hXLen : xSh.length = lambdas.length)
    (hValid : g.validFor lambdas xSh) :
    ∃ ySh : List Goldilocks,
      evalSharedPow7Binomial g.dOpened g.tup g.sigmas = some ySh ∧
      ySh.length = lambdas.length ∧
      lagrangeCombine lambdas ySh = sbox7 (lagrangeCombine lambdas xSh) := by
  obtain ⟨hTup, hdEq, hMac⟩ := hValid
  obtain ⟨hYLen, hYComb⟩ := lagrangeCombine_mpcPow7Shares_eq_sbox7 lambdas xSh g.tup hSumOne hXLen hTup
  refine ⟨mpcPow7Shares g.dOpened g.tup, ?_, ?_, ?_⟩
  · unfold evalSharedPow7Binomial; rw [hMac]; rfl
  · rwa [hdEq]
  · rwa [hdEq]

/-- 12 authenticated S-box gates for a full width-12 external `Poseidon2` round. -/
structure ExtRoundAuthGates where
  g00 : AuthPow7Gate
  g01 : AuthPow7Gate
  g02 : AuthPow7Gate
  g03 : AuthPow7Gate
  g10 : AuthPow7Gate
  g11 : AuthPow7Gate
  g12 : AuthPow7Gate
  g13 : AuthPow7Gate
  g20 : AuthPow7Gate
  g21 : AuthPow7Gate
  g22 : AuthPow7Gate
  g23 : AuthPow7Gate
  deriving DecidableEq, Repr

def ExtRoundAuthGates.validFor
    (lambdas : List Goldilocks) (ssRc : List Poseidon2State12) (gs : ExtRoundAuthGates) : Prop :=
  gs.g00.validFor lambdas (ssRc.map (·.b0.x0)) ∧
  gs.g01.validFor lambdas (ssRc.map (·.b0.x1)) ∧
  gs.g02.validFor lambdas (ssRc.map (·.b0.x2)) ∧
  gs.g03.validFor lambdas (ssRc.map (·.b0.x3)) ∧
  gs.g10.validFor lambdas (ssRc.map (·.b1.x0)) ∧
  gs.g11.validFor lambdas (ssRc.map (·.b1.x1)) ∧
  gs.g12.validFor lambdas (ssRc.map (·.b1.x2)) ∧
  gs.g13.validFor lambdas (ssRc.map (·.b1.x3)) ∧
  gs.g20.validFor lambdas (ssRc.map (·.b2.x0)) ∧
  gs.g21.validFor lambdas (ssRc.map (·.b2.x1)) ∧
  gs.g22.validFor lambdas (ssRc.map (·.b2.x2)) ∧
  gs.g23.validFor lambdas (ssRc.map (·.b2.x3))

private def evalSharedLane4Sbox
    (g0 g1 g2 g3 : AuthPow7Gate) : Option (List Lane4) :=
  match evalSharedPow7Binomial g0.dOpened g0.tup g0.sigmas,
        evalSharedPow7Binomial g1.dOpened g1.tup g1.sigmas,
        evalSharedPow7Binomial g2.dOpened g2.tup g2.sigmas,
        evalSharedPow7Binomial g3.dOpened g3.tup g3.sigmas with
  | some y0, some y1, some y2, some y3 => some (zipLane4Shares y0 y1 y2 y3)
  | _, _, _, _ => none

/-- Share-level external `Poseidon2` round (`+ rc`, 12 authenticated `Π_pow7` gates, local `applyME`). -/
def evalSharedPoseidon2ExternalRound
    (_rc : Poseidon2State12) (ss : List Poseidon2State12) (gs : ExtRoundAuthGates) :
    Option (List Poseidon2State12) :=
  match evalSharedLane4Sbox gs.g00 gs.g01 gs.g02 gs.g03,
        evalSharedLane4Sbox gs.g10 gs.g11 gs.g12 gs.g13,
        evalSharedLane4Sbox gs.g20 gs.g21 gs.g22 gs.g23 with
  | some bs0, some bs1, some bs2 =>
    if ss.length == bs0.length then
      some ((zipState12Shares bs0 bs1 bs2).map applyME)
    else
      none
  | _, _, _ => none

/-- Share-level internal `Poseidon2` round (`b0.x0 + rc`, 1 authenticated `Π_pow7` gate, local `applyMI`). -/
def evalSharedPoseidon2InternalRound
    (_rc : Goldilocks) (ss : List Poseidon2State12) (g : AuthPow7Gate) :
    Option (List Poseidon2State12) :=
  match evalSharedPow7Binomial g.dOpened g.tup g.sigmas with
  | none => none
  | some y0 =>
    if ss.length == y0.length then
      let bs0 := zipLane4Shares y0 (ss.map (·.b0.x1)) (ss.map (·.b0.x2)) (ss.map (·.b0.x3))
      some ((zipState12Shares bs0 (ss.map (·.b1)) (ss.map (·.b2))).map applyMI)
    else
      none

theorem evalSharedPoseidon2ExternalRound_simulates
    (lambdas : List Goldilocks) (rc : Poseidon2State12)
    (ss : List Poseidon2State12) (gs : ExtRoundAuthGates)
    (hSumOne : ringListSum lambdas = Goldilocks.one)
    (hLen : ss.length = lambdas.length)
    (hValid : gs.validFor lambdas (ss.map (fun s => state12Add s rc))) :
    ∃ ssOut : List Poseidon2State12,
      evalSharedPoseidon2ExternalRound rc ss gs = some ssOut ∧
      ssOut.length = lambdas.length ∧
      lagrangeCombineState12 lambdas ssOut = externalRound rc (lagrangeCombineState12 lambdas ss) := by
  let ssRc := ss.map (fun s => state12Add s rc)
  obtain ⟨v00, v01, v02, v03, v10, v11, v12, v13, v20, v21, v22, v23⟩ := hValid
  obtain ⟨y00, e00, l00, c00⟩ := evalSharedPow7Gate_simulates lambdas (ssRc.map (·.b0.x0)) gs.g00 hSumOne (by simp [ssRc, hLen]) v00
  obtain ⟨y01, e01, l01, c01⟩ := evalSharedPow7Gate_simulates lambdas (ssRc.map (·.b0.x1)) gs.g01 hSumOne (by simp [ssRc, hLen]) v01
  obtain ⟨y02, e02, l02, c02⟩ := evalSharedPow7Gate_simulates lambdas (ssRc.map (·.b0.x2)) gs.g02 hSumOne (by simp [ssRc, hLen]) v02
  obtain ⟨y03, e03, l03, c03⟩ := evalSharedPow7Gate_simulates lambdas (ssRc.map (·.b0.x3)) gs.g03 hSumOne (by simp [ssRc, hLen]) v03
  obtain ⟨y10, e10, l10, c10⟩ := evalSharedPow7Gate_simulates lambdas (ssRc.map (·.b1.x0)) gs.g10 hSumOne (by simp [ssRc, hLen]) v10
  obtain ⟨y11, e11, l11, c11⟩ := evalSharedPow7Gate_simulates lambdas (ssRc.map (·.b1.x1)) gs.g11 hSumOne (by simp [ssRc, hLen]) v11
  obtain ⟨y12, e12, l12, c12⟩ := evalSharedPow7Gate_simulates lambdas (ssRc.map (·.b1.x2)) gs.g12 hSumOne (by simp [ssRc, hLen]) v12
  obtain ⟨y13, e13, l13, c13⟩ := evalSharedPow7Gate_simulates lambdas (ssRc.map (·.b1.x3)) gs.g13 hSumOne (by simp [ssRc, hLen]) v13
  obtain ⟨y20, e20, l20, c20⟩ := evalSharedPow7Gate_simulates lambdas (ssRc.map (·.b2.x0)) gs.g20 hSumOne (by simp [ssRc, hLen]) v20
  obtain ⟨y21, e21, l21, c21⟩ := evalSharedPow7Gate_simulates lambdas (ssRc.map (·.b2.x1)) gs.g21 hSumOne (by simp [ssRc, hLen]) v21
  obtain ⟨y22, e22, l22, c22⟩ := evalSharedPow7Gate_simulates lambdas (ssRc.map (·.b2.x2)) gs.g22 hSumOne (by simp [ssRc, hLen]) v22
  obtain ⟨y23, e23, l23, c23⟩ := evalSharedPow7Gate_simulates lambdas (ssRc.map (·.b2.x3)) gs.g23 hSumOne (by simp [ssRc, hLen]) v23
  have hBs0Len : (zipLane4Shares y00 y01 y02 y03).length = lambdas.length := zipLane4Shares_length l00 l01 l02 l03
  have hBs1Len : (zipLane4Shares y10 y11 y12 y13).length = lambdas.length := zipLane4Shares_length l10 l11 l12 l13
  have hBs2Len : (zipLane4Shares y20 y21 y22 y23).length = lambdas.length := zipLane4Shares_length l20 l21 l22 l23
  let preMe := zipState12Shares (zipLane4Shares y00 y01 y02 y03) (zipLane4Shares y10 y11 y12 y13) (zipLane4Shares y20 y21 y22 y23)
  have hPreLen : preMe.length = lambdas.length := zipState12Shares_length hBs0Len hBs1Len hBs2Len
  have hEqB : (ss.length == (zipLane4Shares y00 y01 y02 y03).length) = true := by
    rw [beq_iff_eq, hLen, hBs0Len]
  refine ⟨preMe.map applyME, ?_, by simp [hPreLen], ?_⟩
  · unfold evalSharedPoseidon2ExternalRound evalSharedLane4Sbox
    rw [e00, e01, e02, e03, e10, e11, e12, e13, e20, e21, e22, e23]
    dsimp only
    rw [hEqB]
    rfl
  · rw [lagrangeCombineState12_map_applyME,
        lagrangeCombineState12_zip lambdas _ _ _ hBs0Len hBs1Len hBs2Len,
        lagrangeCombineLane4_zip lambdas _ _ _ _ l00 l01 l02 l03,
        lagrangeCombineLane4_zip lambdas _ _ _ _ l10 l11 l12 l13,
        lagrangeCombineLane4_zip lambdas _ _ _ _ l20 l21 l22 l23,
        c00, c01, c02, c03, c10, c11, c12, c13, c20, c21, c22, c23]
    have hAddRc := lagrangeCombineState12_add_public lambdas ss rc hSumOne hLen
    have hProjRc := lagrangeCombineState12_proj lambdas ssRc
    rw [lagrangeCombineLane4_proj, lagrangeCombineLane4_proj, lagrangeCombineLane4_proj] at hProjRc
    simp only [List.map_map] at hProjRc
    dsimp only [ssRc] at hProjRc
    rw [hAddRc] at hProjRc
    let stRc := state12Add (lagrangeCombineState12 lambdas ss) rc
    have hStRcEq : stRc =
        ⟨⟨lagrangeCombine lambdas (ssRc.map (·.b0.x0)), lagrangeCombine lambdas (ssRc.map (·.b0.x1)),
          lagrangeCombine lambdas (ssRc.map (·.b0.x2)), lagrangeCombine lambdas (ssRc.map (·.b0.x3))⟩,
         ⟨lagrangeCombine lambdas (ssRc.map (·.b1.x0)), lagrangeCombine lambdas (ssRc.map (·.b1.x1)),
          lagrangeCombine lambdas (ssRc.map (·.b1.x2)), lagrangeCombine lambdas (ssRc.map (·.b1.x3))⟩,
         ⟨lagrangeCombine lambdas (ssRc.map (·.b2.x0)), lagrangeCombine lambdas (ssRc.map (·.b2.x1)),
          lagrangeCombine lambdas (ssRc.map (·.b2.x2)), lagrangeCombine lambdas (ssRc.map (·.b2.x3))⟩⟩ := hProjRc
    rw [externalRound_eq]
    change _ = applyME (sboxState12 stRc)
    rw [hStRcEq, sboxState12_eq]

theorem evalSharedPoseidon2InternalRound_simulates
    (lambdas : List Goldilocks) (rc : Goldilocks)
    (ss : List Poseidon2State12) (g : AuthPow7Gate)
    (hSumOne : ringListSum lambdas = Goldilocks.one)
    (hLen : ss.length = lambdas.length)
    (hValid : g.validFor lambdas (ss.map (fun s => Goldilocks.add s.b0.x0 rc))) :
    ∃ ssOut : List Poseidon2State12,
      evalSharedPoseidon2InternalRound rc ss g = some ssOut ∧
      ssOut.length = lambdas.length ∧
      lagrangeCombineState12 lambdas ssOut = internalRound rc (lagrangeCombineState12 lambdas ss) := by
  let x0RcSh := ss.map (fun s => Goldilocks.add s.b0.x0 rc)
  obtain ⟨y0, e0, l0, c0⟩ := evalSharedPow7Gate_simulates lambdas x0RcSh g hSumOne (by simp [x0RcSh, hLen]) hValid
  have hBs0Len : (zipLane4Shares y0 (ss.map (·.b0.x1)) (ss.map (·.b0.x2)) (ss.map (·.b0.x3))).length = lambdas.length :=
    zipLane4Shares_length l0 (by simp [hLen]) (by simp [hLen]) (by simp [hLen])
  let preMi := zipState12Shares
    (zipLane4Shares y0 (ss.map (·.b0.x1)) (ss.map (·.b0.x2)) (ss.map (·.b0.x3)))
    (ss.map (·.b1)) (ss.map (·.b2))
  have hPreLen : preMi.length = lambdas.length :=
    zipState12Shares_length hBs0Len (by simp [hLen]) (by simp [hLen])
  have hEqY : (ss.length == y0.length) = true := by rw [beq_iff_eq, hLen, l0]
  refine ⟨preMi.map applyMI, ?_, by simp [hPreLen], ?_⟩
  · unfold evalSharedPoseidon2InternalRound
    rw [e0]
    dsimp only
    rw [hEqY]
    rfl
  · rw [lagrangeCombineState12_map_applyMI,
        lagrangeCombineState12_zip lambdas _ _ _ hBs0Len (by simp [hLen]) (by simp [hLen]),
        lagrangeCombineLane4_zip lambdas _ _ _ _ l0 (by simp [hLen]) (by simp [hLen]) (by simp [hLen]),
        c0]
    have hx0Add : lagrangeCombine lambdas x0RcSh =
        Goldilocks.add (lagrangeCombine lambdas (ss.map (·.b0.x0))) rc := by
      have hMap : x0RcSh = (ss.map (·.b0.x0)).map (fun x => Goldilocks.add x rc) := by
        rw [List.map_map]; rfl
      rw [hMap]
      exact lagrangeCombine_add_public lambdas (ss.map (·.b0.x0)) rc hSumOne (by simp [hLen])
    rw [hx0Add]
    have hProj := lagrangeCombineState12_proj lambdas ss
    rw [lagrangeCombineLane4_proj] at hProj
    simp only [List.map_map] at hProj
    rw [internalRound_eq, hProj]
    rfl

def evalSharedRounds {α ω : Type}
    (step : α → List Poseidon2State12 → ω → Option (List Poseidon2State12)) :
    List α → List Poseidon2State12 → List ω → Option (List Poseidon2State12)
  | [], ss, _ => some ss
  | _, _, [] => none
  | c :: cs, ss, w :: ws =>
    match step c ss w with
    | none => none
    | some ss' => evalSharedRounds step cs ss' ws

/-- Full 30-round (`4 + 22 + 4`) authenticated gate witness for `evalSharedPoseidon2Perm`. -/
structure Poseidon2PermAuthGates where
  initExt : List ExtRoundAuthGates
  inter   : List AuthPow7Gate
  termExt : List ExtRoundAuthGates
  deriving DecidableEq, Repr

/-- **Maliciously Authenticated Share-Level `(t, n)` Shamir `Poseidon2` Permutation (`evalSharedPoseidon2Perm`)**:
    Executes initial `applyME`, 4 external rounds, 22 internal rounds, and 4 terminal external rounds
    directly on party shares `ss : List Poseidon2State12`, aborting (`= none`) if any SPDZ MAC fails. -/
def evalSharedPoseidon2Perm
    (ss : List Poseidon2State12) (wit : Poseidon2PermAuthGates) :
    Option (List Poseidon2State12) :=
  let s0 := ss.map applyME
  match evalSharedRounds evalSharedPoseidon2ExternalRound poseidon2InitialExtConsts s0 wit.initExt with
  | none => none
  | some s1 =>
    match evalSharedRounds evalSharedPoseidon2InternalRound poseidon2InternalConsts s1 wit.inter with
    | none => none
    | some s2 =>
      evalSharedRounds evalSharedPoseidon2ExternalRound poseidon2TerminalExtConsts s2 wit.termExt

/-- Online gate-opening step: committee opens `d = ⟨λ, x - r⟩` and checks SPDZ `sigmas`. -/
def mkOnlineAuthGate
    (lambdas xSh : List Goldilocks)
    (gatePrep : SharedPow7Tuple × List GoldilocksExt2) : AuthPow7Gate :=
  { dOpened := lagrangeCombine lambdas (shareZipSub xSh gatePrep.1.rSh)
    tup     := gatePrep.1
    sigmas  := gatePrep.2 }

def mkOnlineExtRoundGates
    (lambdas : List Goldilocks) (rc : Poseidon2State12) (ss : List Poseidon2State12)
    (prepAt : Nat → SharedPow7Tuple × List GoldilocksExt2) : ExtRoundAuthGates :=
  let ssRc := ss.map (fun s => state12Add s rc)
  { g00 := mkOnlineAuthGate lambdas (ssRc.map (·.b0.x0)) (prepAt 0)
    g01 := mkOnlineAuthGate lambdas (ssRc.map (·.b0.x1)) (prepAt 1)
    g02 := mkOnlineAuthGate lambdas (ssRc.map (·.b0.x2)) (prepAt 2)
    g03 := mkOnlineAuthGate lambdas (ssRc.map (·.b0.x3)) (prepAt 3)
    g10 := mkOnlineAuthGate lambdas (ssRc.map (·.b1.x0)) (prepAt 4)
    g11 := mkOnlineAuthGate lambdas (ssRc.map (·.b1.x1)) (prepAt 5)
    g12 := mkOnlineAuthGate lambdas (ssRc.map (·.b1.x2)) (prepAt 6)
    g13 := mkOnlineAuthGate lambdas (ssRc.map (·.b1.x3)) (prepAt 7)
    g20 := mkOnlineAuthGate lambdas (ssRc.map (·.b2.x0)) (prepAt 8)
    g21 := mkOnlineAuthGate lambdas (ssRc.map (·.b2.x1)) (prepAt 9)
    g22 := mkOnlineAuthGate lambdas (ssRc.map (·.b2.x2)) (prepAt 10)
    g23 := mkOnlineAuthGate lambdas (ssRc.map (·.b2.x3)) (prepAt 11) }

def runOnlineExtRounds
    (lambdas : List Goldilocks) :
    List Poseidon2State12 → List Poseidon2State12 →
    (Nat → Nat → SharedPow7Tuple × List GoldilocksExt2) → Nat → Option (List Poseidon2State12)
  | [], ss, _, _ => some ss
  | rc :: rcs, ss, rPrep, idx =>
    let gs := mkOnlineExtRoundGates lambdas rc ss (rPrep idx)
    match evalSharedPoseidon2ExternalRound rc ss gs with
    | none => none
    | some ss' => runOnlineExtRounds lambdas rcs ss' rPrep (idx + 1)

def runOnlineIntRounds
    (lambdas : List Goldilocks) :
    List Goldilocks → List Poseidon2State12 →
    (Nat → SharedPow7Tuple × List GoldilocksExt2) → Nat → Option (List Poseidon2State12)
  | [], ss, _, _ => some ss
  | rc :: rcs, ss, rPrep, idx =>
    let g := mkOnlineAuthGate lambdas (ss.map (fun s => Goldilocks.add s.b0.x0 rc)) (rPrep idx)
    match evalSharedPoseidon2InternalRound rc ss g with
    | none => none
    | some ss' => runOnlineIntRounds lambdas rcs ss' rPrep (idx + 1)

/-- Full online `(t, n)` Shamir `Poseidon2` permutation executing `evalSharedPoseidon2ExternalRound`
    and `evalSharedPoseidon2InternalRound` across all 30 rounds (`4` ext + `22` int + `4` ext). -/
def runSharedPoseidon2PermOnline
    (lambdas : List Goldilocks) (ss : List Poseidon2State12)
    (extInitPrep : Nat → Nat → SharedPow7Tuple × List GoldilocksExt2)
    (intPrep     : Nat → SharedPow7Tuple × List GoldilocksExt2)
    (extTermPrep : Nat → Nat → SharedPow7Tuple × List GoldilocksExt2) :
    Option (List Poseidon2State12) :=
  let s0 := ss.map applyME
  match runOnlineExtRounds lambdas poseidon2InitialExtConsts s0 extInitPrep 0 with
  | none => none
  | some s1 =>
    match runOnlineIntRounds lambdas poseidon2InternalConsts s1 intPrep 0 with
    | none => none
    | some s2 =>
      runOnlineExtRounds lambdas poseidon2TerminalExtConsts s2 extTermPrep 0

private theorem runOnlineExtRounds_simulates
    (lambdas : List Goldilocks)
    (rPrep : Nat → Nat → SharedPow7Tuple × List GoldilocksExt2)
    (hSumOne : ringListSum lambdas = Goldilocks.one)
    (hPrep : ∀ r l, (rPrep r l).1.validAt lambdas ∧ verifySpdzZeroSumMac (rPrep r l).2 = true) :
    ∀ (rcs : List Poseidon2State12) (ss : List Poseidon2State12) (idx : Nat),
      ss.length = lambdas.length →
      ∃ ssOut : List Poseidon2State12,
        runOnlineExtRounds lambdas rcs ss rPrep idx = some ssOut ∧
        ssOut.length = lambdas.length ∧
        lagrangeCombineState12 lambdas ssOut = runRounds externalRound rcs (lagrangeCombineState12 lambdas ss)
  | [], ss, _, hLen => ⟨ss, rfl, hLen, by rw [runRounds_nil]⟩
  | rc :: rcs, ss, idx, hLen => by
    have hGsValid : (mkOnlineExtRoundGates lambdas rc ss (rPrep idx)).validFor
        lambdas (ss.map (fun s => state12Add s rc)) := by
      unfold ExtRoundAuthGates.validFor mkOnlineExtRoundGates mkOnlineAuthGate AuthPow7Gate.validFor
      exact ⟨⟨(hPrep idx 0).1, rfl, (hPrep idx 0).2⟩,
             ⟨(hPrep idx 1).1, rfl, (hPrep idx 1).2⟩,
             ⟨(hPrep idx 2).1, rfl, (hPrep idx 2).2⟩,
             ⟨(hPrep idx 3).1, rfl, (hPrep idx 3).2⟩,
             ⟨(hPrep idx 4).1, rfl, (hPrep idx 4).2⟩,
             ⟨(hPrep idx 5).1, rfl, (hPrep idx 5).2⟩,
             ⟨(hPrep idx 6).1, rfl, (hPrep idx 6).2⟩,
             ⟨(hPrep idx 7).1, rfl, (hPrep idx 7).2⟩,
             ⟨(hPrep idx 8).1, rfl, (hPrep idx 8).2⟩,
             ⟨(hPrep idx 9).1, rfl, (hPrep idx 9).2⟩,
             ⟨(hPrep idx 10).1, rfl, (hPrep idx 10).2⟩,
             ⟨(hPrep idx 11).1, rfl, (hPrep idx 11).2⟩⟩
    obtain ⟨ss1, hStep, hLen1, hComb1⟩ :=
      evalSharedPoseidon2ExternalRound_simulates lambdas rc ss _ hSumOne hLen hGsValid
    obtain ⟨ssOut, hRest, hLenOut, hCombOut⟩ :=
      runOnlineExtRounds_simulates lambdas rPrep hSumOne hPrep rcs ss1 (idx + 1) hLen1
    refine ⟨ssOut, ?_, hLenOut, ?_⟩
    · simp only [runOnlineExtRounds, hStep, hRest]
    · rw [runRounds_cons, ← hComb1, hCombOut]

private theorem runOnlineIntRounds_simulates
    (lambdas : List Goldilocks)
    (rPrep : Nat → SharedPow7Tuple × List GoldilocksExt2)
    (hSumOne : ringListSum lambdas = Goldilocks.one)
    (hPrep : ∀ r, (rPrep r).1.validAt lambdas ∧ verifySpdzZeroSumMac (rPrep r).2 = true) :
    ∀ (rcs : List Goldilocks) (ss : List Poseidon2State12) (idx : Nat),
      ss.length = lambdas.length →
      ∃ ssOut : List Poseidon2State12,
        runOnlineIntRounds lambdas rcs ss rPrep idx = some ssOut ∧
        ssOut.length = lambdas.length ∧
        lagrangeCombineState12 lambdas ssOut = runRounds internalRound rcs (lagrangeCombineState12 lambdas ss)
  | [], ss, _, hLen => ⟨ss, rfl, hLen, by rw [runRounds_nil]⟩
  | rc :: rcs, ss, idx, hLen => by
    have hGValid : (mkOnlineAuthGate lambdas (ss.map (fun s => Goldilocks.add s.b0.x0 rc)) (rPrep idx)).validFor
        lambdas (ss.map (fun s => Goldilocks.add s.b0.x0 rc)) :=
      ⟨(hPrep idx).1, rfl, (hPrep idx).2⟩
    obtain ⟨ss1, hStep, hLen1, hComb1⟩ :=
      evalSharedPoseidon2InternalRound_simulates lambdas rc ss _ hSumOne hLen hGValid
    obtain ⟨ssOut, hRest, hLenOut, hCombOut⟩ :=
      runOnlineIntRounds_simulates lambdas rPrep hSumOne hPrep rcs ss1 (idx + 1) hLen1
    refine ⟨ssOut, ?_, hLenOut, ?_⟩
    · simp only [runOnlineIntRounds, hStep, hRest]
    · rw [runRounds_cons, ← hComb1, hCombOut]

/-- **Share-Level `(t, n)` Shamir `Poseidon2` Permutation Simulation (`evalSharedPoseidon2Perm_simulates`)**:
    Across all 30 rounds (`4` initial external + `22` internal + `4` terminal external), online
    share-level evaluation with valid `SharedPow7Tuple`s and zero-sum SPDZ MACs outputs `some ssOut`
    whose Lagrange recombination equals `poseidon2Perm12 (lagrangeCombineState12 lambdas ss)`! -/
theorem evalSharedPoseidon2Perm_simulates
    (lambdas : List Goldilocks) (ss : List Poseidon2State12)
    (extInitPrep : Nat → Nat → SharedPow7Tuple × List GoldilocksExt2)
    (intPrep     : Nat → SharedPow7Tuple × List GoldilocksExt2)
    (extTermPrep : Nat → Nat → SharedPow7Tuple × List GoldilocksExt2)
    (hSumOne : ringListSum lambdas = Goldilocks.one)
    (hLen : ss.length = lambdas.length)
    (hInit : ∀ r l, (extInitPrep r l).1.validAt lambdas ∧ verifySpdzZeroSumMac (extInitPrep r l).2 = true)
    (hInt  : ∀ r, (intPrep r).1.validAt lambdas ∧ verifySpdzZeroSumMac (intPrep r).2 = true)
    (hTerm : ∀ r l, (extTermPrep r l).1.validAt lambdas ∧ verifySpdzZeroSumMac (extTermPrep r l).2 = true) :
    ∃ ssOut : List Poseidon2State12,
      runSharedPoseidon2PermOnline lambdas ss extInitPrep intPrep extTermPrep = some ssOut ∧
      ssOut.length = lambdas.length ∧
      lagrangeCombineState12 lambdas ssOut = poseidon2Perm12 (lagrangeCombineState12 lambdas ss) := by
  have hLen0 : (ss.map applyME).length = lambdas.length := by simp [hLen]
  obtain ⟨s1, hE1, hL1, hC1⟩ :=
    runOnlineExtRounds_simulates lambdas extInitPrep hSumOne hInit poseidon2InitialExtConsts (ss.map applyME) 0 hLen0
  obtain ⟨s2, hE2, hL2, hC2⟩ :=
    runOnlineIntRounds_simulates lambdas intPrep hSumOne hInt poseidon2InternalConsts s1 0 hL1
  obtain ⟨s3, hE3, hL3, hC3⟩ :=
    runOnlineExtRounds_simulates lambdas extTermPrep hSumOne hTerm poseidon2TerminalExtConsts s2 0 hL2
  refine ⟨s3, ?_, hL3, ?_⟩
  · unfold runSharedPoseidon2PermOnline
    dsimp only
    rw [hE1]
    dsimp only
    rw [hE2]
    dsimp only
    exact hE3
  · unfold poseidon2Perm12
    dsimp only
    rw [hC3, hC2, hC1, lagrangeCombineState12_map_applyME]

/-- **`#tooth` Corrupted SPDZ MAC Aborts Share-Level `Poseidon2` (`tooth_evalSharedPoseidon2Perm_aborts_on_forged_gate`)**:
    Corrupting a single SPDZ MAC broadcast share in the internal round causes
    `runSharedPoseidon2PermOnline` to abort cleanly (`= none`)! -/
theorem tooth_evalSharedPoseidon2Perm_aborts_on_forged_gate :
    let initSs := List.replicate 3 poseidon2InitState
    let goodPair : SharedPow7Tuple × List GoldilocksExt2 := (demoPow7TupleFor4, demoZeroMasks3)
    let badSigmas : List GoldilocksExt2 := [⟨Goldilocks.one, Goldilocks.zero⟩, CommRingOps.zero, CommRingOps.zero]
    let badIntPrep : Nat → SharedPow7Tuple × List GoldilocksExt2 :=
      fun r => if r == 0 then (demoPow7TupleFor4, badSigmas) else goodPair
    runSharedPoseidon2PermOnline demoLambdas2of3 initSs
      (fun _ _ => goodPair) badIntPrep (fun _ _ => goodPair) = none := by
  decide +kernel

/-- Shamir byte-share validity: each byte of `bs` is shared across `lambdas.length` parties. -/
def ShamirByteSharesValid (lambdas : List Goldilocks) :
    List (List Goldilocks) → List UInt8 → Prop
  | [], [] => True
  | row :: rows, b :: bs =>
    row.length = lambdas.length ∧
    lagrangeCombine lambdas row = Goldilocks.ofNat b.toNat ∧
    ShamirByteSharesValid lambdas rows bs
  | _, _ => False

theorem ShamirByteSharesValid.length_eq {lambdas : List Goldilocks} :
    ∀ {rows : List (List Goldilocks)} {bs : List UInt8},
      ShamirByteSharesValid lambdas rows bs → rows.length = bs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, _, hRest⟩ => congrArg Nat.succ hRest.length_eq

theorem ShamirByteSharesValid.append {lambdas : List Goldilocks} :
    ∀ {r1 r2 : List (List Goldilocks)} {b1 b2 : List UInt8},
      ShamirByteSharesValid lambdas r1 b1 →
      ShamirByteSharesValid lambdas r2 b2 →
      ShamirByteSharesValid lambdas (r1 ++ r2) (b1 ++ b2)
  | [], _, [], _, _, h2 => h2
  | _ :: _, _, _ :: _, _, ⟨hL, hC, h1⟩, h2 => ⟨hL, hC, h1.append h2⟩

def shamirPublicByteShares (nParties : Nat) (bs : List UInt8) : List (List Goldilocks) :=
  bs.map (fun b => List.replicate nParties (Goldilocks.ofNat b.toNat))

theorem shamirPublicByteShares_valid
    (lambdas : List Goldilocks) (hSumOne : ringListSum lambdas = Goldilocks.one) :
    ∀ (bs : List UInt8),
      ShamirByteSharesValid lambdas (shamirPublicByteShares lambdas.length bs) bs
  | [] => trivial
  | b :: bs => by
    refine ⟨List.length_replicate, ?_, shamirPublicByteShares_valid lambdas hSumOne bs⟩
    unfold lagrangeCombine
    rw [ringDot_replicate_right, hSumOne]
    exact LawfulCommRing.one_mul (Goldilocks.ofNat b.toNat)

private theorem goldilocks_ofNat_add (a b : Nat) :
    Goldilocks.add (Goldilocks.ofNat a) (Goldilocks.ofNat b) = Goldilocks.ofNat (a + b) := by
  apply Goldilocks.ext
  simp [Goldilocks.add_val, Goldilocks.ofNat, Nat.mod_add_mod]

private theorem goldilocks_ofNat_mul (a b : Nat) :
    Goldilocks.mul (Goldilocks.ofNat a) (Goldilocks.ofNat b) = Goldilocks.ofNat (a * b) := by
  apply Goldilocks.ext
  simp [Goldilocks.mul_val, Goldilocks.ofNat, Nat.mul_mod]

def horner256StepShares (accSh bSh : List Goldilocks) : List Goldilocks :=
  ringListZipAdd (shareScale (Goldilocks.ofNat 256) accSh) bSh

def shamirFoldHorner256 (accSh : List Goldilocks) : List (List Goldilocks) → List Goldilocks
  | [] => accSh
  | bSh :: rest => shamirFoldHorner256 (horner256StepShares accSh bSh) rest

private theorem shamirFoldHorner256_correct (lambdas : List Goldilocks) :
    ∀ {rows : List (List Goldilocks)} {bs : List UInt8} (accSh : List Goldilocks) (acc : Nat),
      ShamirByteSharesValid lambdas rows bs →
      accSh.length = lambdas.length →
      lagrangeCombine lambdas accSh = Goldilocks.ofNat acc →
      (shamirFoldHorner256 accSh rows).length = lambdas.length ∧
      lagrangeCombine lambdas (shamirFoldHorner256 accSh rows) =
        Goldilocks.ofNat (bs.foldl (fun a b => a * 256 + b.toNat) acc)
  | [], [], accSh, acc, _, hAccLen, hAccVal => ⟨hAccLen, hAccVal⟩
  | row :: rows, b :: bs, accSh, acc, ⟨hRLen, hRVal, hRest⟩, hAccLen, hAccVal => by
    have hNextLen : (horner256StepShares accSh row).length = lambdas.length := by
      unfold horner256StepShares
      rw [ringListZipAdd_length_of_eq (by simp [hAccLen, hRLen])]
      simp [hAccLen]
    have hNextVal : lagrangeCombine lambdas (horner256StepShares accSh row) =
        Goldilocks.ofNat (acc * 256 + b.toNat) := by
      unfold lagrangeCombine horner256StepShares
      rw [ringDot_zipAdd (by simp [hAccLen, hRLen]), ringDot_scale]
      change Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 256) (lagrangeCombine lambdas accSh))
        (lagrangeCombine lambdas row) = _
      rw [hAccVal, hRVal, goldilocks_ofNat_mul, goldilocks_ofNat_add, Nat.mul_comm 256 acc]
    exact shamirFoldHorner256_correct lambdas (horner256StepShares accSh row) (acc * 256 + b.toNat)
      hRest hNextLen hNextVal

/-- Pack 7 Shamir-shared bytes linearly into a `< 2^56` `Goldilocks` limb share vector. -/
def shamirPack7ByteShares (nParties : Nat) (rows7 : List (List Goldilocks)) : List Goldilocks :=
  shamirFoldHorner256 (List.replicate nParties Goldilocks.zero) rows7

def shamirChunk7Exact (nParties : Nat) : List (List Goldilocks) → List (List Goldilocks)
  | s0 :: s1 :: s2 :: s3 :: s4 :: s5 :: s6 :: rest =>
    shamirPack7ByteShares nParties [s0, s1, s2, s3, s4, s5, s6] :: shamirChunk7Exact nParties rest
  | _ => []

def ShamirLimbSharesValid (lambdas : List Goldilocks) :
    List (List Goldilocks) → List Goldilocks → Prop
  | [], [] => True
  | row :: rows, x :: xs =>
    row.length = lambdas.length ∧
    lagrangeCombine lambdas row = x ∧
    ShamirLimbSharesValid lambdas rows xs
  | _, _ => False

theorem ShamirLimbSharesValid.length_eq {lambdas : List Goldilocks} :
    ∀ {rows : List (List Goldilocks)} {xs : List Goldilocks},
      ShamirLimbSharesValid lambdas rows xs → rows.length = xs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, _, hRest⟩ => congrArg Nat.succ hRest.length_eq

theorem ShamirLimbSharesValid.append {lambdas : List Goldilocks} :
    ∀ {r1 r2 : List (List Goldilocks)} {x1 x2 : List Goldilocks},
      ShamirLimbSharesValid lambdas r1 x1 →
      ShamirLimbSharesValid lambdas r2 x2 →
      ShamirLimbSharesValid lambdas (r1 ++ r2) (x1 ++ x2)
  | [], _, [], _, _, h2 => h2
  | _ :: _, _, _ :: _, _, ⟨hL, hC, h1⟩, h2 => ⟨hL, hC, h1.append h2⟩

private theorem shamirChunk7Exact_valid (lambdas : List Goldilocks) :
    ∀ {rows : List (List Goldilocks)} {bs : List UInt8},
      ShamirByteSharesValid lambdas rows bs →
      ShamirLimbSharesValid lambdas (shamirChunk7Exact lambdas.length rows) (chunk7Exact bs)
  | s0 :: s1 :: s2 :: s3 :: s4 :: s5 :: s6 :: restR,
    b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: restB,
    ⟨l0, c0, l1, c1, l2, c2, l3, c3, l4, c4, l5, c5, l6, c6, hRest⟩ => by
    have h7 : ShamirByteSharesValid lambdas [s0, s1, s2, s3, s4, s5, s6] [b0, b1, b2, b3, b4, b5, b6] :=
      ⟨l0, c0, l1, c1, l2, c2, l3, c3, l4, c4, l5, c5, l6, c6, trivial⟩
    have hZVal : lagrangeCombine lambdas (List.replicate lambdas.length Goldilocks.zero) = Goldilocks.ofNat 0 := by
      unfold lagrangeCombine
      rw [ringDot_replicate_right]
      exact LawfulCommRing.mul_zero (ringListSum lambdas)
    obtain ⟨hPackLen, hPackVal⟩ := shamirFoldHorner256_correct lambdas
      (List.replicate lambdas.length Goldilocks.zero) 0 h7 List.length_replicate hZVal
    have hEqLimb : Goldilocks.ofNat ([b0, b1, b2, b3, b4, b5, b6].foldl (fun a b => a * 256 + b.toNat) 0) =
        pack7BytesLimb [b0, b1, b2, b3, b4, b5, b6] := by
      apply Goldilocks.ext
      unfold pack7BytesLimb ofBE
      dsimp only
      have hTake : (([b0, b1, b2, b3, b4, b5, b6] ++ List.replicate (7 - [b0, b1, b2, b3, b4, b5, b6].length) 0).take 7) =
          [b0, b1, b2, b3, b4, b5, b6] := rfl
      have hLtP : ([b0, b1, b2, b3, b4, b5, b6].foldl (fun a b => a * 256 + b.toNat) 0) < goldilocksPrime := by
        have h56 := pack7BytesLimb_lt_two_pow_56 [b0, b1, b2, b3, b4, b5, b6]
        unfold pack7BytesLimb ofBE at h56
        dsimp only at h56
        rw [hTake] at h56
        exact Nat.lt_trans h56 (by unfold goldilocksPrime; decide)
      simp only [Goldilocks.ofNat, hTake, Nat.mod_eq_of_lt hLtP]
    refine ⟨hPackLen, hPackVal.trans hEqLimb, shamirChunk7Exact_valid lambdas hRest⟩
  | [], [], _ => trivial
  | [_], [_], _ | [_, _], [_, _], _ | [_, _, _], [_, _, _], _
  | [_, _, _, _], [_, _, _, _], _ | [_, _, _, _, _], [_, _, _, _, _], _
  | [_, _, _, _, _, _], [_, _, _, _, _, _], _ => trivial

def shamirPoseidon2PadBytes (nParties : Nat) (msgSh : List (List Goldilocks)) : List (List Goldilocks) :=
  let markedSh := msgSh ++ shamirPublicByteShares nParties [(0x01 : UInt8)]
  let padLen := (7 - markedSh.length % 7) % 7
  let limbsSh := shamirChunk7Exact nParties
    (markedSh ++ shamirPublicByteShares nParties (List.replicate padLen (0x00 : UInt8)))
  let z := (8 - (limbsSh.length + 1) % 8) % 8
  limbsSh ++ (pad101Suffix z).map (fun c => List.replicate nParties c)

private theorem shamirPublicLimbs_valid
    (lambdas : List Goldilocks) (hSumOne : ringListSum lambdas = Goldilocks.one) :
    ∀ (xs : List Goldilocks),
      ShamirLimbSharesValid lambdas (xs.map (fun c => List.replicate lambdas.length c)) xs
  | [] => trivial
  | c :: cs => by
    refine ⟨List.length_replicate, ?_, shamirPublicLimbs_valid lambdas hSumOne cs⟩
    unfold lagrangeCombine
    rw [ringDot_replicate_right, hSumOne]
    exact LawfulCommRing.one_mul c

private theorem shamirPoseidon2PadBytes_valid
    (lambdas : List Goldilocks) (hSumOne : ringListSum lambdas = Goldilocks.one)
    {msgSh : List (List Goldilocks)} {msg : List UInt8}
    (hValid : ShamirByteSharesValid lambdas msgSh msg) :
    ShamirLimbSharesValid lambdas (shamirPoseidon2PadBytes lambdas.length msgSh) (poseidon2PadBytes msg) := by
  unfold shamirPoseidon2PadBytes poseidon2PadBytes poseidon2Pad bytesToLimbs56
  have hMarkValid : ShamirByteSharesValid lambdas
      (msgSh ++ shamirPublicByteShares lambdas.length [(0x01 : UInt8)]) (msg ++ [(0x01 : UInt8)]) :=
    hValid.append (shamirPublicByteShares_valid lambdas hSumOne [(0x01 : UInt8)])
  have hMarkLen : (msgSh ++ shamirPublicByteShares lambdas.length [(0x01 : UInt8)]).length =
      (msg ++ [(0x01 : UInt8)]).length := hMarkValid.length_eq
  let padLen := (7 - (msg ++ [(0x01 : UInt8)]).length % 7) % 7
  have hPaddedBytesValid : ShamirByteSharesValid lambdas
      ((msgSh ++ shamirPublicByteShares lambdas.length [(0x01 : UInt8)]) ++
        shamirPublicByteShares lambdas.length (List.replicate padLen (0x00 : UInt8)))
      ((msg ++ [(0x01 : UInt8)]) ++ List.replicate padLen (0x00 : UInt8)) :=
    hMarkValid.append (shamirPublicByteShares_valid lambdas hSumOne _)
  have hChunkValid := shamirChunk7Exact_valid lambdas hPaddedBytesValid
  have hChunkLen := hChunkValid.length_eq
  dsimp only
  rw [hMarkLen]
  dsimp only [padLen] at hChunkValid hChunkLen ⊢
  rw [hChunkLen]
  exact hChunkValid.append (shamirPublicLimbs_valid lambdas hSumOne _)

/-- Preprocessing bundle for a single 30-round `Poseidon2` permutation call. -/
structure Poseidon2CallPrep where
  extInit : Nat → Nat → SharedPow7Tuple × List GoldilocksExt2
  inter   : Nat → SharedPow7Tuple × List GoldilocksExt2
  extTerm : Nat → Nat → SharedPow7Tuple × List GoldilocksExt2

def Poseidon2CallPrep.validAt (lambdas : List Goldilocks) (p : Poseidon2CallPrep) : Prop :=
  (∀ r l, (p.extInit r l).1.validAt lambdas ∧ verifySpdzZeroSumMac (p.extInit r l).2 = true) ∧
  (∀ r, (p.inter r).1.validAt lambdas ∧ verifySpdzZeroSumMac (p.inter r).2 = true) ∧
  (∀ r l, (p.extTerm r l).1.validAt lambdas ∧ verifySpdzZeroSumMac (p.extTerm r l).2 = true)

def shamirAbsorbRate8Block
    (lambdas : List Goldilocks) (ss : List Poseidon2State12)
    (m0 m1 m2 m3 m4 m5 m6 m7 : List Goldilocks)
    (callPrep : Poseidon2CallPrep) : Option (List Poseidon2State12) :=
  let bs0 := zipLane4Shares
    (ringListZipAdd (ss.map (·.b0.x0)) m0)
    (ringListZipAdd (ss.map (·.b0.x1)) m1)
    (ringListZipAdd (ss.map (·.b0.x2)) m2)
    (ringListZipAdd (ss.map (·.b0.x3)) m3)
  let bs1 := zipLane4Shares
    (ringListZipAdd (ss.map (·.b1.x0)) m4)
    (ringListZipAdd (ss.map (·.b1.x1)) m5)
    (ringListZipAdd (ss.map (·.b1.x2)) m6)
    (ringListZipAdd (ss.map (·.b1.x3)) m7)
  let absorbed := zipState12Shares bs0 bs1 (ss.map (·.b2))
  runSharedPoseidon2PermOnline lambdas absorbed callPrep.extInit callPrep.inter callPrep.extTerm

def shamirAbsorbLimbStream
    (lambdas : List Goldilocks) (ss : List Poseidon2State12)
    (blockPrep : Nat → Poseidon2CallPrep) :
    Nat → List (List Goldilocks) → Option (List Poseidon2State12)
  | blk, m0 :: m1 :: m2 :: m3 :: m4 :: m5 :: m6 :: m7 :: rest =>
    match shamirAbsorbRate8Block lambdas ss m0 m1 m2 m3 m4 m5 m6 m7 (blockPrep blk) with
    | none => none
    | some ss' => shamirAbsorbLimbStream lambdas ss' blockPrep (blk + 1) rest
  | _, _ => some ss

private theorem shamirAbsorbLimbStream_simulates
    (lambdas : List Goldilocks)
    (blockPrep : Nat → Poseidon2CallPrep)
    (hSumOne : ringListSum lambdas = Goldilocks.one)
    (hPrep : ∀ blk, (blockPrep blk).validAt lambdas) :
    ∀ {limbShs : List (List Goldilocks)} {limbs : List Goldilocks}
      (ss : List Poseidon2State12) (blk : Nat),
      ShamirLimbSharesValid lambdas limbShs limbs →
      ss.length = lambdas.length →
      ∃ ssOut : List Poseidon2State12,
        shamirAbsorbLimbStream lambdas ss blockPrep blk limbShs = some ssOut ∧
        ssOut.length = lambdas.length ∧
        lagrangeCombineState12 lambdas ssOut =
          absorbLimbStream (lagrangeCombineState12 lambdas ss) limbs
  | m0Sh :: m1Sh :: m2Sh :: m3Sh :: m4Sh :: m5Sh :: m6Sh :: m7Sh :: restSh,
    m0 :: m1 :: m2 :: m3 :: m4 :: m5 :: m6 :: m7 :: restL,
    ss, blk,
    ⟨l0, c0, l1, c1, l2, c2, l3, c3, l4, c4, l5, c5, l6, c6, l7, c7, hRest⟩,
    hSsLen => by
    have zL0 : (ringListZipAdd (ss.map (·.b0.x0)) m0Sh).length = lambdas.length := by
      rw [ringListZipAdd_length_of_eq (by simp [hSsLen, l0])]; simp [hSsLen]
    have zL1 : (ringListZipAdd (ss.map (·.b0.x1)) m1Sh).length = lambdas.length := by
      rw [ringListZipAdd_length_of_eq (by simp [hSsLen, l1])]; simp [hSsLen]
    have zL2 : (ringListZipAdd (ss.map (·.b0.x2)) m2Sh).length = lambdas.length := by
      rw [ringListZipAdd_length_of_eq (by simp [hSsLen, l2])]; simp [hSsLen]
    have zL3 : (ringListZipAdd (ss.map (·.b0.x3)) m3Sh).length = lambdas.length := by
      rw [ringListZipAdd_length_of_eq (by simp [hSsLen, l3])]; simp [hSsLen]
    have zL4 : (ringListZipAdd (ss.map (·.b1.x0)) m4Sh).length = lambdas.length := by
      rw [ringListZipAdd_length_of_eq (by simp [hSsLen, l4])]; simp [hSsLen]
    have zL5 : (ringListZipAdd (ss.map (·.b1.x1)) m5Sh).length = lambdas.length := by
      rw [ringListZipAdd_length_of_eq (by simp [hSsLen, l5])]; simp [hSsLen]
    have zL6 : (ringListZipAdd (ss.map (·.b1.x2)) m6Sh).length = lambdas.length := by
      rw [ringListZipAdd_length_of_eq (by simp [hSsLen, l6])]; simp [hSsLen]
    have zL7 : (ringListZipAdd (ss.map (·.b1.x3)) m7Sh).length = lambdas.length := by
      rw [ringListZipAdd_length_of_eq (by simp [hSsLen, l7])]; simp [hSsLen]
    let bs0 := zipLane4Shares
      (ringListZipAdd (ss.map (·.b0.x0)) m0Sh) (ringListZipAdd (ss.map (·.b0.x1)) m1Sh)
      (ringListZipAdd (ss.map (·.b0.x2)) m2Sh) (ringListZipAdd (ss.map (·.b0.x3)) m3Sh)
    let bs1 := zipLane4Shares
      (ringListZipAdd (ss.map (·.b1.x0)) m4Sh) (ringListZipAdd (ss.map (·.b1.x1)) m5Sh)
      (ringListZipAdd (ss.map (·.b1.x2)) m6Sh) (ringListZipAdd (ss.map (·.b1.x3)) m7Sh)
    have hBs0Len : bs0.length = lambdas.length := zipLane4Shares_length zL0 zL1 zL2 zL3
    have hBs1Len : bs1.length = lambdas.length := zipLane4Shares_length zL4 zL5 zL6 zL7
    let absorbed := zipState12Shares bs0 bs1 (ss.map (·.b2))
    have hAbsLen : absorbed.length = lambdas.length :=
      zipState12Shares_length hBs0Len hBs1Len (by simp [hSsLen])
    obtain ⟨hPInit, hPInt, hPTerm⟩ := hPrep blk
    obtain ⟨ss1, hPerm, hLen1, hComb1⟩ :=
      evalSharedPoseidon2Perm_simulates lambdas absorbed _ _ _ hSumOne hAbsLen hPInit hPInt hPTerm
    have hAbsComb : lagrangeCombineState12 lambdas absorbed =
        ⟨lane4Add (lagrangeCombineState12 lambdas ss).b0 ⟨m0, m1, m2, m3⟩,
         lane4Add (lagrangeCombineState12 lambdas ss).b1 ⟨m4, m5, m6, m7⟩,
         (lagrangeCombineState12 lambdas ss).b2⟩ := by
      rw [lagrangeCombineState12_zip lambdas _ _ _ hBs0Len hBs1Len (by simp [hSsLen]),
          lagrangeCombineLane4_zip lambdas _ _ _ _ zL0 zL1 zL2 zL3,
          lagrangeCombineLane4_zip lambdas _ _ _ _ zL4 zL5 zL6 zL7]
      have hProj := lagrangeCombineState12_proj lambdas ss
      have hB0 : (lagrangeCombineState12 lambdas ss).b0 = lagrangeCombineLane4 lambdas (ss.map (·.b0)) := by
        rw [hProj]
      have hB1 : (lagrangeCombineState12 lambdas ss).b1 = lagrangeCombineLane4 lambdas (ss.map (·.b1)) := by
        rw [hProj]
      have hB2 : (lagrangeCombineState12 lambdas ss).b2 = lagrangeCombineLane4 lambdas (ss.map (·.b2)) := by
        rw [hProj]
      rw [hB0, hB1, hB2, lagrangeCombineLane4_proj, lagrangeCombineLane4_proj, lagrangeCombineLane4_proj,
          lane4Add_eq, lane4Add_eq]
      simp only [List.map_map]
      unfold lagrangeCombine at c0 c1 c2 c3 c4 c5 c6 c7 ⊢
      rw [ringDot_zipAdd (by simp [hSsLen, l0]), ringDot_zipAdd (by simp [hSsLen, l1]),
          ringDot_zipAdd (by simp [hSsLen, l2]), ringDot_zipAdd (by simp [hSsLen, l3]),
          ringDot_zipAdd (by simp [hSsLen, l4]), ringDot_zipAdd (by simp [hSsLen, l5]),
          ringDot_zipAdd (by simp [hSsLen, l6]), ringDot_zipAdd (by simp [hSsLen, l7]),
          c0, c1, c2, c3, c4, c5, c6, c7]
      rfl
    obtain ⟨ssOut, hRestStep, hLenOut, hCombOut⟩ :=
      shamirAbsorbLimbStream_simulates lambdas blockPrep hSumOne hPrep ss1 (blk + 1) hRest hLen1
    refine ⟨ssOut, ?_, hLenOut, ?_⟩
    · simp only [shamirAbsorbLimbStream, shamirAbsorbRate8Block]
      change (match runSharedPoseidon2PermOnline lambdas absorbed
                (blockPrep blk).extInit (blockPrep blk).inter (blockPrep blk).extTerm with
              | none => none
              | some ss' => shamirAbsorbLimbStream lambdas ss' blockPrep (blk + 1) restSh) = some ssOut
      rw [hPerm]
      exact hRestStep
    · simp only [absorbLimbStream, absorbRate8Block]
      rw [hCombOut, hComb1, hAbsComb]
  | [], [], ss, _, _, hSsLen => ⟨ss, rfl, hSsLen, rfl⟩
  | [_], [_], ss, _, _, hSsLen | [_, _], [_, _], ss, _, _, hSsLen
  | [_, _, _], [_, _, _], ss, _, _, hSsLen | [_, _, _, _], [_, _, _, _], ss, _, _, hSsLen
  | [_, _, _, _, _], [_, _, _, _, _], ss, _, _, hSsLen
  | [_, _, _, _, _, _], [_, _, _, _, _, _], ss, _, _, hSsLen
  | [_, _, _, _, _, _, _], [_, _, _, _, _, _, _], ss, _, _, hSsLen => ⟨ss, rfl, hSsLen, rfl⟩

/-- Execute the full `(t, n)` Shamir `Poseidon2` sponge over Shamir-shared message bytes `msgSh`,
    keeping the entire width-12 sponge state shared across the committee. -/
def mpcPoseidon2SpongeShared
    (lambdas : List Goldilocks) (msgSh : List (List Goldilocks))
    (blockPrep : Nat → Poseidon2CallPrep) : Option (List Poseidon2State12) :=
  let initSs := List.replicate lambdas.length poseidon2InitState
  let paddedLimbShs := shamirPoseidon2PadBytes lambdas.length msgSh
  shamirAbsorbLimbStream lambdas initSs blockPrep 0 paddedLimbShs

/-- Open ONLY the 4 squeezed rate limbs (`32` digest bytes) at the public cut boundary. -/
def shamirOpenSqueeze32 (lambdas : List Goldilocks) (ss : List Poseidon2State12) : List UInt8 :=
  let x0 := lagrangeCombine lambdas (ss.map (·.b0.x0))
  let x1 := lagrangeCombine lambdas (ss.map (·.b0.x1))
  let x2 := lagrangeCombine lambdas (ss.map (·.b0.x2))
  let x3 := lagrangeCombine lambdas (ss.map (·.b0.x3))
  be 8 x0.val ++ be 8 x1.val ++ be 8 x2.val ++ be 8 x3.val

/-- Evaluate `poseidon2Hash32` over `(t, n)` Shamir-shared message bytes and open ONLY the 32-byte digest. -/
def mpcPoseidon2Hash32Shared
    (lambdas : List Goldilocks) (msgSh : List (List Goldilocks))
    (blockPrep : Nat → Poseidon2CallPrep) : List UInt8 :=
  match mpcPoseidon2SpongeShared lambdas msgSh blockPrep with
  | some finalSs => shamirOpenSqueeze32 lambdas finalSs
  | none => []

private theorem lagrangeCombineState12_replicate
    (lambdas : List Goldilocks) (st : Poseidon2State12)
    (hSumOne : ringListSum lambdas = Goldilocks.one) :
    lagrangeCombineState12 lambdas (List.replicate lambdas.length st) = st := by
  have hLane : ∀ (c : Goldilocks),
      lagrangeCombine lambdas (List.replicate lambdas.length c) = c := by
    intro c
    unfold lagrangeCombine
    rw [ringDot_replicate_right, hSumOne]
    exact LawfulCommRing.one_mul c
  rw [lagrangeCombineState12_proj, lagrangeCombineLane4_proj,
      lagrangeCombineLane4_proj, lagrangeCombineLane4_proj]
  simp only [List.map_replicate, hLane]

/-- **Share-Level `(t, n)` Shamir `poseidon2Hash32` Simulation (`mpcPoseidon2SpongeShared_simulates`)**:
    On any Shamir-shared byte input `msgSh` (`ShamirByteSharesValid lambdas msgSh msg`),
    `mpcPoseidon2SpongeShared` outputs `some finalSs` recombining to the exact sponge state of
    `poseidon2Hash32 msg`, and `mpcPoseidon2Hash32Shared` equals `poseidon2Hash32 msg` bit-for-bit! -/
theorem mpcPoseidon2SpongeShared_simulates
    (lambdas : List Goldilocks) (hSumOne : ringListSum lambdas = Goldilocks.one)
    {msgSh : List (List Goldilocks)} {msg : List UInt8}
    (hMsg : ShamirByteSharesValid lambdas msgSh msg)
    (blockPrep : Nat → Poseidon2CallPrep)
    (hPrep : ∀ blk, (blockPrep blk).validAt lambdas) :
    (∃ finalSs : List Poseidon2State12,
      mpcPoseidon2SpongeShared lambdas msgSh blockPrep = some finalSs ∧
      finalSs.length = lambdas.length ∧
      lagrangeCombineState12 lambdas finalSs =
        absorbLimbStream poseidon2InitState (poseidon2PadBytes msg)) ∧
    mpcPoseidon2Hash32Shared lambdas msgSh blockPrep = poseidon2Hash32 msg := by
  have hPadValid := shamirPoseidon2PadBytes_valid lambdas hSumOne hMsg
  obtain ⟨finalSs, hSp, hLen, hComb⟩ :=
    shamirAbsorbLimbStream_simulates lambdas blockPrep hSumOne hPrep
      (List.replicate lambdas.length poseidon2InitState) 0 hPadValid List.length_replicate
  rw [lagrangeCombineState12_replicate lambdas poseidon2InitState hSumOne] at hComb
  have hSpEq : mpcPoseidon2SpongeShared lambdas msgSh blockPrep = some finalSs := hSp
  refine ⟨⟨finalSs, hSpEq, hLen, hComb⟩, ?_⟩
  unfold mpcPoseidon2Hash32Shared
  rw [hSpEq]
  unfold shamirOpenSqueeze32 poseidon2Hash32 squeeze32Bytes
  have hProj := lagrangeCombineState12_proj lambdas finalSs
  rw [lagrangeCombineLane4_proj] at hProj
  simp only [List.map_map] at hProj
  rw [← hComb, hProj]
  rfl

/-- `Π_bitdecomp` limb-to-bytes share conversion oracle for multi-step secret chaining inside the cut:
    converts a shared `Goldilocks` limb `limbSh` into 8 Shamir-shared big-endian bytes without opening it. -/
def ValidShamirLimbDecomp8
    (lambdas : List Goldilocks) (decomp8 : List Goldilocks → List (List Goldilocks)) : Prop :=
  ∀ limbSh : List Goldilocks,
    limbSh.length = lambdas.length →
    ShamirByteSharesValid lambdas (decomp8 limbSh) (be 8 (lagrangeCombine lambdas limbSh).val)

def shamirSqueezeShared32
    (decomp8 : List Goldilocks → List (List Goldilocks))
    (ss : List Poseidon2State12) : List (List Goldilocks) :=
  decomp8 (ss.map (·.b0.x0)) ++ decomp8 (ss.map (·.b0.x1)) ++
  decomp8 (ss.map (·.b0.x2)) ++ decomp8 (ss.map (·.b0.x3))

def shamirFrameSingleSecretCall
    (nParties : Nat) (roleTag pkSeed : List UInt8) (adrs : HashAdrs)
    (secretSh : List (List Goldilocks)) : List (List Goldilocks) :=
  let pubPrefix :=
    leb128 4 ++ encodeListField roleTag ++ encodeListField pkSeed ++
    encodeListField (encodeAdrs adrs) ++ leb128 secretSh.length
  shamirPublicByteShares nParties pubPrefix ++ secretSh

private theorem shamirFrameSingleSecretCall_valid
    (lambdas : List Goldilocks) (hSumOne : ringListSum lambdas = Goldilocks.one)
    (roleTag pkSeed : List UInt8) (adrs : HashAdrs)
    {secretSh : List (List Goldilocks)} {secret : List UInt8}
    (hSec : ShamirByteSharesValid lambdas secretSh secret) :
    ShamirByteSharesValid lambdas
      (shamirFrameSingleSecretCall lambdas.length roleTag pkSeed adrs secretSh)
      (thPreimage roleTag pkSeed adrs [secret]) := by
  unfold shamirFrameSingleSecretCall
  have hEqPre :
      (leb128 4 ++ encodeListField roleTag ++ encodeListField pkSeed ++
        encodeListField (encodeAdrs adrs) ++ leb128 secretSh.length) ++ secret =
      thPreimage roleTag pkSeed adrs [secret] := by
    rw [thPreimage_eq, hSec.length_eq]
    simp only [List.cons_append, List.nil_append, encodeMultiFrame, List.length_cons,
      List.length_nil, encodeByteFields_cons, encodeByteFields_nil, List.append_nil,
      encodeListField_eq secret, List.append_assoc]
  rw [← hEqPre]
  exact (shamirPublicByteShares_valid lambdas hSumOne _).append hSec

def mpcPoseidon2SqueezeSecret32
    (lambdas : List Goldilocks)
    (decomp8 : List Goldilocks → List (List Goldilocks))
    (msgSh : List (List Goldilocks))
    (blockPrep : Nat → Poseidon2CallPrep) : Option (List (List Goldilocks)) :=
  match mpcPoseidon2SpongeShared lambdas msgSh blockPrep with
  | some finalSs => some (shamirSqueezeShared32 decomp8 finalSs)
  | none => none

private theorem mpcPoseidon2SqueezeSecret32_valid
    (lambdas : List Goldilocks) (hSumOne : ringListSum lambdas = Goldilocks.one)
    {decomp8 : List Goldilocks → List (List Goldilocks)}
    (hDecomp : ValidShamirLimbDecomp8 lambdas decomp8)
    {msgSh : List (List Goldilocks)} {msg : List UInt8}
    (hMsg : ShamirByteSharesValid lambdas msgSh msg)
    (blockPrep : Nat → Poseidon2CallPrep)
    (hPrep : ∀ blk, (blockPrep blk).validAt lambdas) :
    ∃ outSh : List (List Goldilocks),
      mpcPoseidon2SqueezeSecret32 lambdas decomp8 msgSh blockPrep = some outSh ∧
      ShamirByteSharesValid lambdas outSh (poseidon2Hash32 msg) := by
  obtain ⟨⟨finalSs, hSp, hLen, hComb⟩, _⟩ :=
    mpcPoseidon2SpongeShared_simulates lambdas hSumOne hMsg blockPrep hPrep
  refine ⟨shamirSqueezeShared32 decomp8 finalSs, ?_, ?_⟩
  · unfold mpcPoseidon2SqueezeSecret32; rw [hSp]
  · unfold shamirSqueezeShared32 poseidon2Hash32 squeeze32Bytes
    have hProj := lagrangeCombineState12_proj lambdas finalSs
    rw [lagrangeCombineLane4_proj] at hProj
    simp only [List.map_map] at hProj
    rw [← hComb, hProj]
    exact (((hDecomp _ (by simp [hLen])).append (hDecomp _ (by simp [hLen]))).append
      (hDecomp _ (by simp [hLen]))).append (hDecomp _ (by simp [hLen]))

def mpcPoseidon2ThChainShared
    (lambdas : List Goldilocks)
    (decomp8 : List Goldilocks → List (List Goldilocks))
    (pkSeed : List UInt8) (layer : UInt32) (tree : UInt64) (kp chain : Nat) :
    Nat → Nat → List (List Goldilocks) → (Nat → Nat → Poseidon2CallPrep) → Option (List (List Goldilocks))
  | _, 0, curSh, _ => some curSh
  | startStep, rem + 1, curSh, stepPrep =>
    let adrs : HashAdrs := ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat chain, UInt32.ofNat startStep⟩
    let preSh := shamirFrameSingleSecretCall lambdas.length tagThF pkSeed adrs curSh
    match mpcPoseidon2SqueezeSecret32 lambdas decomp8 preSh (stepPrep startStep) with
    | none => none
    | some nextSh =>
      mpcPoseidon2ThChainShared lambdas decomp8 pkSeed layer tree kp chain (startStep + 1) rem nextSh stepPrep

private theorem mpcPoseidon2ThChainShared_simulates
    (lambdas : List Goldilocks) (hSumOne : ringListSum lambdas = Goldilocks.one)
    {decomp8 : List Goldilocks → List (List Goldilocks)}
    (hDecomp : ValidShamirLimbDecomp8 lambdas decomp8)
    (pkSeed : List UInt8) (layer : UInt32) (tree : UInt64) (kp chain : Nat)
    (stepPrep : Nat → Nat → Poseidon2CallPrep)
    (hPrep : ∀ s blk, (stepPrep s blk).validAt lambdas) :
    ∀ (rem startStep : Nat) {curSh : List (List Goldilocks)} {cur : List UInt8},
      ShamirByteSharesValid lambdas curSh cur →
      ∃ outSh : List (List Goldilocks),
        mpcPoseidon2ThChainShared lambdas decomp8 pkSeed layer tree kp chain startStep rem curSh stepPrep = some outSh ∧
        ShamirByteSharesValid lambdas outSh
          (wotsChainSteps poseidon2Suite pkSeed layer tree kp chain startStep rem cur)
  | 0, _, curSh, _, hCur =>
    ⟨curSh, rfl, by rw [wotsChainSteps_zero]; exact hCur⟩
  | rem + 1, startStep, curSh, cur, hCur => by
    let adrs : HashAdrs := ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat chain, UInt32.ofNat startStep⟩
    have hFrame := shamirFrameSingleSecretCall_valid lambdas hSumOne tagThF pkSeed adrs hCur
    obtain ⟨nextSh, hSq, hNextValid⟩ :=
      mpcPoseidon2SqueezeSecret32_valid lambdas hSumOne hDecomp hFrame (stepPrep startStep) (hPrep startStep)
    have hNextEq : poseidon2Hash32 (thPreimage tagThF pkSeed adrs [cur]) =
        thChainF poseidon2Suite pkSeed adrs cur := by
      rw [thChainF_eq, thCall_eq]; rfl
    rw [hNextEq] at hNextValid
    obtain ⟨outSh, hRest, hOutValid⟩ :=
      mpcPoseidon2ThChainShared_simulates lambdas hSumOne hDecomp pkSeed layer tree kp chain stepPrep hPrep
        rem (startStep + 1) hNextValid
    refine ⟨outSh, ?_, ?_⟩
    · simp only [mpcPoseidon2ThChainShared]
      change (match mpcPoseidon2SqueezeSecret32 lambdas decomp8
                (shamirFrameSingleSecretCall lambdas.length tagThF pkSeed adrs curSh) (stepPrep startStep) with
              | none => none
              | some nextSh => mpcPoseidon2ThChainShared lambdas decomp8 pkSeed layer tree kp chain
                  (startStep + 1) rem nextSh stepPrep) = some outSh
      rw [hSq]
      exact hRest
    · rw [wotsChainSteps_succ]; exact hOutValid

def shamirReconstructOpenBytes (lambdas : List Goldilocks) (rows : List (List Goldilocks)) : List UInt8 :=
  rows.map (fun row => UInt8.ofNat (lagrangeCombine lambdas row).val)

private theorem shamirReconstructOpenBytes_eq (lambdas : List Goldilocks) :
    ∀ {rows : List (List Goldilocks)} {bs : List UInt8},
      ShamirByteSharesValid lambdas rows bs →
      shamirReconstructOpenBytes lambdas rows = bs
  | [], [], _ => rfl
  | row :: rows, b :: bs, ⟨_, hC, hRest⟩ => by
    simp only [shamirReconstructOpenBytes, List.map_cons, hC]
    have hbLt : b.toNat < goldilocksPrime :=
      Nat.lt_trans b.toNat_lt (by unfold goldilocksPrime; decide)
    have hByte : UInt8.ofNat (Goldilocks.ofNat b.toNat).val = b := by
      simp [Goldilocks.ofNat, Nat.mod_eq_of_lt hbLt]
    rw [hByte]
    change b :: shamirReconstructOpenBytes lambdas rows = b :: bs
    rw [shamirReconstructOpenBytes_eq lambdas hRest]

/-- **Cleartext-Free `(t, n)` Shamir `Poseidon2` Cut-Boundary Oracles (`mkShamirPoseidon2MpcOracles`)**:
    Evaluates all 4 `poseidon2Suite` cut functions (`evalPrfMsg`, `evalWotsChainEnd`, `evalForsReveal`,
    `evalForsLeafHash`) over Shamir-shared secret bytes `skSeedSh, skPrfSh` using share-level
    `runSharedPoseidon2PermOnline` (`evalSharedPow7Binomial` + SPDZ `GoldilocksExt2` `MacCheck`);
    `skSeed` and `skPrf` are NEVER reconstructed in cleartext! -/
def mkShamirPoseidon2MpcOracles
    (lambdas : List Goldilocks)
    (skSeedSh skPrfSh : List (List Goldilocks))
    (pkSeed : List UInt8)
    (decomp8 : List Goldilocks → List (List Goldilocks))
    (callPrep : Nat → Nat → Poseidon2CallPrep) : PqHashMpcOracles where
  evalPrfMsg optRand mu :=
    let pubPrefix :=
      leb128 6 ++ encodeListField tagPrfMsg ++ encodeListField [] ++
      encodeListField (encodeAdrs zeroAdrs) ++ leb128 skPrfSh.length
    let pubSuffix := encodeListField optRand ++ encodeListField mu
    let preSh := shamirPublicByteShares lambdas.length pubPrefix ++
                 (skPrfSh ++ shamirPublicByteShares lambdas.length pubSuffix)
    mpcPoseidon2Hash32Shared lambdas preSh (callPrep 0)
  evalWotsChainEnd layer tree kp chain steps :=
    let baseAdrs : HashAdrs := ⟨layer, tree, .wotsPrf, UInt32.ofNat kp, UInt32.ofNat chain, 0⟩
    let preBase := shamirFrameSingleSecretCall lambdas.length tagPrf pkSeed baseAdrs skSeedSh
    match steps with
    | 0 => mpcPoseidon2Hash32Shared lambdas preBase (callPrep 0)
    | steps' + 1 =>
      match mpcPoseidon2SqueezeSecret32 lambdas decomp8 preBase (callPrep 0) with
      | none => []
      | some baseSh =>
        match mpcPoseidon2ThChainShared lambdas decomp8 pkSeed layer tree kp chain 0 (steps' + 1) baseSh
                (fun s => callPrep (s + 1)) with
        | none => []
        | some endSh => shamirReconstructOpenBytes lambdas endSh
  evalForsReveal tree0 kp0 globalU :=
    let adrs : HashAdrs := ⟨0, tree0, .forsPrf, UInt32.ofNat kp0, 0, UInt32.ofNat globalU⟩
    mpcPoseidon2Hash32Shared lambdas
      (shamirFrameSingleSecretCall lambdas.length tagPrf pkSeed adrs skSeedSh) (callPrep 0)
  evalForsLeafHash tree0 kp0 globalU :=
    let prfAdrs : HashAdrs := ⟨0, tree0, .forsPrf, UInt32.ofNat kp0, 0, UInt32.ofNat globalU⟩
    match mpcPoseidon2SqueezeSecret32 lambdas decomp8
            (shamirFrameSingleSecretCall lambdas.length tagPrf pkSeed prfAdrs skSeedSh) (callPrep 0) with
    | none => []
    | some secSh =>
      let treeAdrs : HashAdrs := ⟨0, tree0, .forsTree, UInt32.ofNat kp0, 0, UInt32.ofNat globalU⟩
      mpcPoseidon2Hash32Shared lambdas
        (shamirFrameSingleSecretCall lambdas.length tagThF pkSeed treeAdrs secSh) (callPrep 1)

/-- **Constructive `(t, n)` Shamir `Poseidon2` `MatchesKey` Theorem (`mkShamirPoseidon2MpcOracles_matchesKey`)**:
    Discharges `PqHashMpcOracles.MatchesKey poseidon2Suite sk` end-to-end from share-level Shamir
    `Poseidon2` (`evalSharedPoseidon2Perm` + `evalSharedPow7Binomial`) with `0` cleartext key reconstruction! -/
theorem mkShamirPoseidon2MpcOracles_matchesKey
    (lambdas : List Goldilocks) (hSumOne : ringListSum lambdas = Goldilocks.one)
    {skSeedSh skPrfSh : List (List Goldilocks)} {skSeed skPrf : List UInt8}
    (hSeed : ShamirByteSharesValid lambdas skSeedSh skSeed)
    (hPrf  : ShamirByteSharesValid lambdas skPrfSh skPrf)
    (pkSeed : List UInt8)
    {decomp8 : List Goldilocks → List (List Goldilocks)}
    (hDecomp : ValidShamirLimbDecomp8 lambdas decomp8)
    (callPrep : Nat → Nat → Poseidon2CallPrep)
    (hPrep : ∀ step blk, (callPrep step blk).validAt lambdas) :
    (mkShamirPoseidon2MpcOracles lambdas skSeedSh skPrfSh pkSeed decomp8 callPrep).MatchesKey
      poseidon2Suite { skSeed := skSeed, skPrf := skPrf, pkSeed := pkSeed } := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro optRand mu
    dsimp only [mkShamirPoseidon2MpcOracles]
    let pubPrefix :=
      leb128 6 ++ encodeListField tagPrfMsg ++ encodeListField [] ++
      encodeListField (encodeAdrs zeroAdrs) ++ leb128 skPrfSh.length
    let pubSuffix := encodeListField optRand ++ encodeListField mu
    have hPreValid : ShamirByteSharesValid lambdas
        (shamirPublicByteShares lambdas.length pubPrefix ++
          (skPrfSh ++ shamirPublicByteShares lambdas.length pubSuffix))
        (pubPrefix ++ (skPrf ++ pubSuffix)) :=
      (shamirPublicByteShares_valid lambdas hSumOne pubPrefix).append
        (hPrf.append (shamirPublicByteShares_valid lambdas hSumOne pubSuffix))
    rw [(mpcPoseidon2SpongeShared_simulates lambdas hSumOne hPreValid (callPrep 0) (hPrep 0)).2,
        thPrfMsg_eq, thCall_eq, thPreimage_eq]
    dsimp only [pubPrefix, pubSuffix]
    rw [hPrf.length_eq]
    simp only [poseidon2Suite, List.cons_append, List.nil_append,
      encodeMultiFrame, List.length_cons, List.length_nil, encodeByteFields_cons, encodeByteFields_nil,
      List.append_nil, encodeListField_eq skPrf, List.append_assoc]
  · intro layer tree kp chain steps
    dsimp only [mkShamirPoseidon2MpcOracles]
    have hBaseFrame := shamirFrameSingleSecretCall_valid lambdas hSumOne tagPrf pkSeed
      ⟨layer, tree, .wotsPrf, UInt32.ofNat kp, UInt32.ofNat chain, 0⟩ hSeed
    cases steps with
    | zero =>
      rw [wotsChainSteps_zero,
          (mpcPoseidon2SpongeShared_simulates lambdas hSumOne hBaseFrame (callPrep 0) (hPrep 0)).2,
          wotsSecretBase_eq, thSecretPrf_eq, thCall_eq]
      rfl
    | succ steps' =>
      obtain ⟨baseSh, hSqBase, hBaseValid⟩ :=
        mpcPoseidon2SqueezeSecret32_valid lambdas hSumOne hDecomp hBaseFrame (callPrep 0) (hPrep 0)
      have hBaseEq : poseidon2Hash32 (thPreimage tagPrf pkSeed
          ⟨layer, tree, .wotsPrf, UInt32.ofNat kp, UInt32.ofNat chain, 0⟩ [skSeed]) =
          wotsSecretBase poseidon2Suite { skSeed := skSeed, skPrf := skPrf, pkSeed := pkSeed }
            layer tree kp chain := by
        rw [wotsSecretBase_eq, thSecretPrf_eq, thCall_eq]; rfl
      rw [hBaseEq] at hBaseValid
      obtain ⟨endSh, hChain, hEndValid⟩ :=
        mpcPoseidon2ThChainShared_simulates lambdas hSumOne hDecomp pkSeed layer tree kp chain
          (fun s => callPrep (s + 1)) (fun s blk => hPrep (s + 1) blk) (steps' + 1) 0 hBaseValid
      rw [hSqBase]
      dsimp only
      rw [hChain]
      exact shamirReconstructOpenBytes_eq lambdas hEndValid
  · intro tree0 kp0 globalU
    dsimp only [mkShamirPoseidon2MpcOracles]
    have hFrame := shamirFrameSingleSecretCall_valid lambdas hSumOne tagPrf pkSeed
      ⟨0, tree0, .forsPrf, UInt32.ofNat kp0, 0, UInt32.ofNat globalU⟩ hSeed
    rw [(mpcPoseidon2SpongeShared_simulates lambdas hSumOne hFrame (callPrep 0) (hPrep 0)).2,
        forsSecretLeaf_eq, thSecretPrf_eq, thCall_eq]
    rfl
  · intro tree0 kp0 globalU
    dsimp only [mkShamirPoseidon2MpcOracles]
    have hF1 := shamirFrameSingleSecretCall_valid lambdas hSumOne tagPrf pkSeed
      ⟨0, tree0, .forsPrf, UInt32.ofNat kp0, 0, UInt32.ofNat globalU⟩ hSeed
    obtain ⟨secSh, hSqSec, hSecValid⟩ :=
      mpcPoseidon2SqueezeSecret32_valid lambdas hSumOne hDecomp hF1 (callPrep 0) (hPrep 0)
    have hF2 := shamirFrameSingleSecretCall_valid lambdas hSumOne tagThF pkSeed
      ⟨0, tree0, .forsTree, UInt32.ofNat kp0, 0, UInt32.ofNat globalU⟩ hSecValid
    rw [hSqSec]
    dsimp only
    rw [(mpcPoseidon2SpongeShared_simulates lambdas hSumOne hF2 (callPrep 1) (hPrep 1)).2,
        forsLeafFn_eq, forsSecretLeaf_eq, thChainF_eq, thSecretPrf_eq, thCall_eq, thCall_eq]
    rfl

/-- **Arbitrary $t$-of-$n$ Shamir `Poseidon2` Threshold Signing Bit-Identity
    (`shamir_poseidon2_thresholdSign_eq_evalSingleSign`)**:
    Whenever Shamir-shared `Poseidon2` cut-boundary oracles `o` satisfy `o.MatchesKey poseidon2Suite sk`
    (discharged constructively by `mkShamirPoseidon2MpcOracles_matchesKey`), distributed key generation
    and signing emit the **exact same** public key and signature as single-party `evalSingleSign`,
    and every emitted signature passes `verifyPqHashSig`. -/
theorem shamir_poseidon2_thresholdSign_eq_evalSingleSign
    (params : PqHashParams) (o : PqHashMpcOracles) (sk : PqSecretKey)
    (msg optRand : List UInt8) (leafGlobalIdx maxGrind : Nat)
    (hMatch : o.MatchesKey poseidon2Suite sk) :
    derivePublicKeyMpc poseidon2Suite params o sk.pkSeed = derivePublicKey poseidon2Suite params sk ∧
    evalCutBatchSignMpc poseidon2Suite params o (derivePublicKeyMpc poseidon2Suite params o sk.pkSeed)
      msg optRand leafGlobalIdx maxGrind =
      evalSingleSign poseidon2Suite params sk msg optRand leafGlobalIdx maxGrind ∧
    (∀ sig,
      evalCutBatchSignMpc poseidon2Suite params o (derivePublicKeyMpc poseidon2Suite params o sk.pkSeed)
        msg optRand leafGlobalIdx maxGrind = some sig →
      verifyPqHashSig poseidon2Suite params (derivePublicKeyMpc poseidon2Suite params o sk.pkSeed) msg sig = true) :=
  evalCutBatchSignMpc_eq_evalSingleSign poseidon2Suite params o sk msg optRand leafGlobalIdx maxGrind hMatch

/-- **End-to-End Share-Level `(t, n)` Shamir `Poseidon2` Threshold Signing (`shamir_poseidon2_shared_thresholdSign_eq_evalSingleSign`)**:
    Wires `mkShamirPoseidon2MpcOracles` (`evalSharedPoseidon2Perm` + `evalSharedPow7Binomial`) directly into
    `shamir_poseidon2_thresholdSign_eq_evalSingleSign` with `0` cleartext secret reconstruction! -/
theorem shamir_poseidon2_shared_thresholdSign_eq_evalSingleSign
    (params : PqHashParams)
    (lambdas : List Goldilocks) (hSumOne : ringListSum lambdas = Goldilocks.one)
    {skSeedSh skPrfSh : List (List Goldilocks)} {skSeed skPrf : List UInt8}
    (hSeed : ShamirByteSharesValid lambdas skSeedSh skSeed)
    (hPrf  : ShamirByteSharesValid lambdas skPrfSh skPrf)
    (pkSeed msg optRand : List UInt8) (leafGlobalIdx maxGrind : Nat)
    {decomp8 : List Goldilocks → List (List Goldilocks)}
    (hDecomp : ValidShamirLimbDecomp8 lambdas decomp8)
    (callPrep : Nat → Nat → Poseidon2CallPrep)
    (hPrep : ∀ step blk, (callPrep step blk).validAt lambdas) :
    let o := mkShamirPoseidon2MpcOracles lambdas skSeedSh skPrfSh pkSeed decomp8 callPrep
    let sk : PqSecretKey := { skSeed := skSeed, skPrf := skPrf, pkSeed := pkSeed }
    derivePublicKeyMpc poseidon2Suite params o pkSeed = derivePublicKey poseidon2Suite params sk ∧
    evalCutBatchSignMpc poseidon2Suite params o (derivePublicKeyMpc poseidon2Suite params o pkSeed)
      msg optRand leafGlobalIdx maxGrind =
      evalSingleSign poseidon2Suite params sk msg optRand leafGlobalIdx maxGrind ∧
    (∀ sig,
      evalCutBatchSignMpc poseidon2Suite params o (derivePublicKeyMpc poseidon2Suite params o pkSeed)
        msg optRand leafGlobalIdx maxGrind = some sig →
      verifyPqHashSig poseidon2Suite params (derivePublicKeyMpc poseidon2Suite params o pkSeed) msg sig = true) :=
  shamir_poseidon2_thresholdSign_eq_evalSingleSign params _ _ msg optRand leafGlobalIdx maxGrind
    (mkShamirPoseidon2MpcOracles_matchesKey lambdas hSumOne hSeed hPrf pkSeed hDecomp callPrep hPrep)

/-! ## 4. Checked stateless threshold path (`HashSigs` weld) -/

/-- Threshold counterpart of `evalStatelessCheckedSign`: the leaf is the HXOF-derived index of
    `deriveStatelessInputs` on the opened randomizer, and the digit geometry must pass
    `PqHashParams.checkedDigitGeometry`. Only cut-boundary oracles are consulted. -/
def thresholdStatelessCheckedSign (suite : TweakableHashSuite) (params : PqHashParams)
    (o : PqHashMpcOracles) (pk : PqPublicKey) (msg optRand : List UInt8)
    (maxGrind : Nat) : Option PqHashSig :=
  if !params.checkedDigitGeometry then none
  else
    match deriveStatelessInputs suite params
        (o.evalPrfMsg optRand (thPreHash suite pk.pkSeed pk.pkRoot msg))
        pk.pkSeed pk.pkRoot (thPreHash suite pk.pkSeed pk.pkRoot msg) with
    | none => none
    | some (leaf, _) => evalCutBatchSignMpc suite params o pk msg optRand leaf maxGrind

/-- The threshold checked path is the checked single-signer path, output for output. -/
theorem thresholdStatelessCheckedSign_eq_evalStatelessCheckedSign
    (suite : TweakableHashSuite) (params : PqHashParams)
    (o : PqHashMpcOracles) (sk : PqSecretKey) (msg optRand : List UInt8) (maxGrind : Nat)
    (hMatch : o.MatchesKey suite sk) :
    thresholdStatelessCheckedSign suite params o (derivePublicKeyMpc suite params o sk.pkSeed)
      msg optRand maxGrind =
      evalStatelessCheckedSign suite params sk msg optRand maxGrind := by
  have hPk := (evalCutBatchSignMpc_eq_evalSingleSign suite params o sk msg optRand 0 maxGrind hMatch).1
  have hSeed : (derivePublicKey suite params sk).pkSeed = sk.pkSeed := rfl
  have key : ∀ leaf, evalCutBatchSignMpc suite params o (derivePublicKey suite params sk)
      msg optRand leaf maxGrind = evalSingleSign suite params sk msg optRand leaf maxGrind := by
    intro leaf
    have h := (evalCutBatchSignMpc_eq_evalSingleSign suite params o sk msg optRand leaf maxGrind hMatch).2.1
    rwa [hPk] at h
  unfold thresholdStatelessCheckedSign
  rw [evalStatelessCheckedSign_eq, hPk]
  simp only [hSeed, hMatch.1, key]
  rfl

/-- Every signature emitted by the threshold checked path passes the checked verifier, and its
    digits at the message layer are the successful output of `extractBaseWDigitsChecked`. -/
theorem thresholdStatelessCheckedSign_accepted
    (suite : TweakableHashSuite) (params : PqHashParams)
    (o : PqHashMpcOracles) (sk : PqSecretKey) (msg optRand : List UInt8) (maxGrind : Nat)
    (hMatch : o.MatchesKey suite sk) (sig : PqHashSig)
    (hSign : thresholdStatelessCheckedSign suite params o
      (derivePublicKeyMpc suite params o sk.pkSeed) msg optRand maxGrind = some sig) :
    verifyStatelessChecked suite params (derivePublicKeyMpc suite params o sk.pkSeed) msg sig = true ∧
    ∃ digits hmsg0,
      grindTswCounterAux suite params.w params.ell1 params.targetSum sig.rRand sk.pkSeed
        (derivePublicKey suite params sk).pkRoot
        (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msg)
        0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
        (UInt32.ofNat (sig.leafGlobalIdx % 2 ^ params.subtreeHeight)) 0 maxGrind =
          some (sig.msgTswCtr, digits, hmsg0) ∧
      extractBaseWDigitsChecked params.w params.ell1 hmsg0 = some digits := by
  have hPk := (evalCutBatchSignMpc_eq_evalSingleSign suite params o sk msg optRand 0 maxGrind hMatch).1
  rw [thresholdStatelessCheckedSign_eq_evalStatelessCheckedSign suite params o sk msg optRand maxGrind hMatch] at hSign
  have hVer := verifyStatelessChecked_evalStatelessCheckedSign suite params sk msg optRand maxGrind sig hSign
  obtain ⟨hGeom, hSt, _, _⟩ := verifyStatelessChecked_sound suite params _ msg sig hVer
  refine ⟨by rw [hPk]; exact hVer, ?_⟩
  rw [evalStatelessCheckedSign_eq] at hSign
  simp only [hGeom, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hSign
  split at hSign
  · cases hSign
  · rename_i leaf idxs hD
    obtain ⟨_, _, hR, hL, ⟨dg, hmsg0, hG, _⟩, _⟩ :=
      evalSingleSign_stateless_inv suite params sk msg optRand leaf maxGrind sig hSt hSign
    rw [← hR, ← hL] at hG
    exact ⟨dg, hmsg0, hG, grindTswCounterAux_checked hGeom hG⟩

/-- Concrete 2-of-3 RSS instance of the checked weld for `cshake256Suite`. -/
theorem rss_thresholdStatelessCheckedSign_eq_evalStatelessCheckedSign (params : PqHashParams)
    {skSeedSh skPrfSh : RssByteShares} (hSeedWf : skSeedSh.WellFormed) (hPrfWf : skPrfSh.WellFormed)
    (pkSeed msg optRand : List UInt8) (maxGrind : Nat)
    (tape : Nat → Nat → Nat → Nat → RssPrfZeroSeeds) :
    thresholdStatelessCheckedSign cshake256Suite params
      (mkRssCshakePqHashMpcOracles skSeedSh skPrfSh pkSeed tape)
      (derivePublicKeyMpc cshake256Suite params
        (mkRssCshakePqHashMpcOracles skSeedSh skPrfSh pkSeed tape) pkSeed)
      msg optRand maxGrind =
      evalStatelessCheckedSign cshake256Suite params
        ⟨reconstructRssBytes skSeedSh, reconstructRssBytes skPrfSh, pkSeed⟩ msg optRand maxGrind :=
  thresholdStatelessCheckedSign_eq_evalStatelessCheckedSign cshake256Suite params _
    ⟨reconstructRssBytes skSeedSh, reconstructRssBytes skPrfSh, pkSeed⟩ msg optRand maxGrind
    (mkRssCshakePqHashMpcOracles_matchesKey hSeedWf hPrfWf pkSeed tape)

/-- Share-level evaluation of the production `(j, u)`-addressed FORS secret. -/
def mpcForsIndexedSecretRss (skSeedSh : RssByteShares) (pkSeed : List UInt8)
    (tree : UInt64) (kp j u : Nat) (tape : Nat → Nat → Nat → RssPrfZeroSeeds) : RssByteShares :=
  mpcCshake256SharedRss 32 pqCshakeSuiteCustom
    (rssFrameSingleSecretCall tagPrf pkSeed
      ⟨0, tree, .forsPrf, UInt32.ofNat kp, UInt32.ofNat j, UInt32.ofNat u⟩ skSeedSh) tape

/-- Share-level evaluation of the production `(j, u)`-addressed FORS leaf hash. -/
def mpcForsIndexedLeafHashRss (skSeedSh : RssByteShares) (pkSeed : List UInt8)
    (tree : UInt64) (kp j u : Nat) (tape : Nat → Nat → Nat → Nat → RssPrfZeroSeeds) : RssByteShares :=
  mpcCshake256SharedRss 32 pqCshakeSuiteCustom
    (rssFrameSingleSecretCall tagThF pkSeed
      ⟨0, tree, .forsTree, UInt32.ofNat kp, UInt32.ofNat j, UInt32.ofNat u⟩
      (mpcForsIndexedSecretRss skSeedSh pkSeed tree kp j u (tape 0))) (tape 1)

/-- The RSS cut evaluates the production FORS address format `(j, u)` exactly. -/
theorem reconstructRssBytes_mpcForsIndexedRss
    {skSeedSh : RssByteShares} (hSeedWf : skSeedSh.WellFormed) (skPrf pkSeed : List UInt8)
    (tree : UInt64) (kp j u : Nat) (tape : Nat → Nat → Nat → Nat → RssPrfZeroSeeds) :
    reconstructRssBytes (mpcForsIndexedSecretRss skSeedSh pkSeed tree kp j u (tape 0)) =
      forsIndexedSecretLeaf cshake256Suite ⟨reconstructRssBytes skSeedSh, skPrf, pkSeed⟩ tree kp j u ∧
    reconstructRssBytes (mpcForsIndexedLeafHashRss skSeedSh pkSeed tree kp j u tape) =
      forsIndexedLeafHash cshake256Suite pkSeed tree kp j u
        (forsIndexedSecretLeaf cshake256Suite ⟨reconstructRssBytes skSeedSh, skPrf, pkSeed⟩ tree kp j u) := by
  unfold mpcForsIndexedLeafHashRss mpcForsIndexedSecretRss
  obtain ⟨hF1Wf, hF1Rec⟩ := reconstructRssBytes_rssFrameSingleSecretCall tagPrf pkSeed
    ⟨0, tree, .forsPrf, UInt32.ofNat kp, UInt32.ofNat j, UInt32.ofNat u⟩ hSeedWf
  obtain ⟨hSecWf, hSecRec⟩ := reconstructRssBytes_mpcCshake256SharedRss 32 pqCshakeSuiteCustom hF1Wf (tape 0)
  obtain ⟨hF2Wf, hF2Rec⟩ := reconstructRssBytes_rssFrameSingleSecretCall tagThF pkSeed
    ⟨0, tree, .forsTree, UInt32.ofNat kp, UInt32.ofNat j, UInt32.ofNat u⟩ hSecWf
  have hSec : reconstructRssBytes (mpcCshake256SharedRss 32 pqCshakeSuiteCustom
      (rssFrameSingleSecretCall tagPrf pkSeed
        ⟨0, tree, .forsPrf, UInt32.ofNat kp, UInt32.ofNat j, UInt32.ofNat u⟩ skSeedSh) (tape 0)) =
      forsIndexedSecretLeaf cshake256Suite ⟨reconstructRssBytes skSeedSh, skPrf, pkSeed⟩ tree kp j u := by
    rw [hSecRec, hF1Rec, forsIndexedSecretLeaf_eq, thSecretPrf_eq, thCall_eq]; rfl
  refine ⟨hSec, ?_⟩
  rw [(reconstructRssBytes_mpcCshake256SharedRss 32 pqCshakeSuiteCustom hF2Wf (tape 1)).2,
      hF2Rec, hSec, forsIndexedLeafHash_eq, thChainF_eq, thCall_eq]; rfl

/-! ## 5. Threshold output equals single-signer FIPS 205 & `Poseidon2` output

Sharing models covered, and at which level:
* **2-of-3 replicated (XOR) sharing (`SHAKE256` / `cSHAKE256`)**: the concrete share-level `Keccak`
  protocol `mkRssSlhMpcOracles` (and `mkRssCshakePqHashMpcOracles`), for every two-party quorum,
  every well-formed sharing, and every zero-sharing tape.
* **Arbitrary `(t, n)` Shamir sharing (`Poseidon2` suite, Section 3)**: the concrete share-level
  `Poseidon2` protocol `mkShamirPoseidon2MpcOracles` (`evalSharedPoseidon2Perm` +
  `evalSharedPow7Binomial` + SPDZ `GoldilocksExt2` `MacCheck`), with `MatchesKey` proved
  constructively in `mkShamirPoseidon2MpcOracles_matchesKey` and zero cleartext secret reconstruction.
* **Arbitrary `(t, n)` Shamir quorum-recombination (`SlhThresholdRun.ofShamir`)**: `ShamirQuorum`
  packages Lagrange-at-zero recombination (`shamirReconstructBytes_quorum`) for FIPS 205
  `SlhMpcOracles`, paired below with `shamir_single_share_privacy_bijection` and the pure-Shamir
  `shamir_poseidon2_threshold_sig_witness`. -/

/-- The three two-party quorums of 2-of-3 replicated sharing. -/
inductive RssQuorum where
  | p01 | p12 | p20
  deriving DecidableEq, Repr

/-- The two parties' local views (each party holds two of the three components). -/
def RssQuorum.views (q : RssQuorum) (sh : RssByteShares) :
    (List UInt8 × List UInt8) × (List UInt8 × List UInt8) :=
  match q with
  | .p01 => ((sh.b0, sh.b1), (sh.b1, sh.b2))
  | .p12 => ((sh.b1, sh.b2), (sh.b2, sh.b0))
  | .p20 => ((sh.b2, sh.b0), (sh.b0, sh.b1))

/-- Reassemble the share triple from the two quorum members' views alone. -/
def RssQuorum.assemble (q : RssQuorum)
    (v : (List UInt8 × List UInt8) × (List UInt8 × List UInt8)) : RssByteShares :=
  match q with
  | .p01 => ⟨v.1.1, v.1.2, v.2.2⟩
  | .p12 => ⟨v.2.2, v.1.1, v.1.2⟩
  | .p20 => ⟨v.1.2, v.2.2, v.1.1⟩

theorem RssQuorum.assemble_views (q : RssQuorum) (sh : RssByteShares) :
    q.assemble (q.views sh) = sh := by
  cases q <;> rfl

/-- Regression: one party's view does not determine the triple; two sharings of different secrets
    can agree on party 0's whole view. -/
theorem rss_single_view_does_not_determine_secret :
    (RssQuorum.p01.views ⟨[1], [2], [3]⟩).1 = (RssQuorum.p01.views ⟨[1], [2], [4]⟩).1 ∧
    reconstructRssBytes ⟨[1], [2], [3]⟩ ≠ reconstructRssBytes ⟨[1], [2], [4]⟩ := by
  decide +kernel

/-- FIPS 205 signature bytes produced by a two-party quorum running the share-level RSS protocol
    on the triples it reassembles from its own views. -/
def rssQuorumSlhSignBytes (p : Fips205Params) (q : RssQuorum)
    (seedViews prfViews : (List UInt8 × List UInt8) × (List UInt8 × List UInt8))
    (pkSeed : List UInt8) (tape : Nat → Nat → Nat → Nat → RssPrfZeroSeeds)
    (msgPrime optRand : List UInt8) : List UInt8 :=
  thresholdSlhSignBytes p
    (mkRssSlhMpcOracles p (q.assemble seedViews) (q.assemble prfViews) pkSeed tape) msgPrime
    (slhKeygenMpc p
      (mkRssSlhMpcOracles p (q.assemble seedViews) (q.assemble prfViews) pkSeed tape) pkSeed)
    optRand

/-- Lagrange-at-zero data of a Shamir quorum at threshold `t`: evaluation points and
    recombination coefficients satisfying the Vandermonde conditions up to degree `t - 1`. -/
structure ShamirQuorum (R : Type) [CommRingOps R] (t : Nat) where
  pts : List R
  lambdas : List R
  sum_one : ringDot lambdas (pts.map (fun _ => CommRingOps.one)) = CommRingOps.one
  kills_higher : ∀ d, 1 ≤ d → d < t →
    ringDot lambdas (pts.map (fun x => ringPow x d)) = CommRingOps.zero

/-- Share matrix seen by a quorum: one row per secret byte, one column per quorum member. -/
def shamirQuorumShares {R : Type} [CommRingOps R] (pts : List R) (polys : List (List R)) :
    List (List R) :=
  polys.map (fun c => pts.map (fun x => RoundPoly.evalCoeffs c x))

/-- Quorum-side recombination of every secret byte. -/
def shamirReconstructBytes {R : Type} [CommRingOps R] (decode : R → UInt8) (lambdas : List R)
    (shares : List (List R)) : List UInt8 :=
  shares.map (fun row => decode (ringDot lambdas row))

/-- The shared byte string: the decoded constant terms. -/
def shamirSecretBytes {R : Type} [CommRingOps R] (decode : R → UInt8) (polys : List (List R)) :
    List UInt8 :=
  polys.map (fun c => decode (RoundPoly.evalCoeffs c CommRingOps.zero))

/-- Any quorum recombines any degree-`< t` sharing to the same secret bytes. -/
theorem shamirReconstructBytes_quorum {R : Type} [LawfulCommRing R] (decode : R → UInt8)
    (t : Nat) (Q : ShamirQuorum R t) (polys : List (List R))
    (hDeg : ∀ c ∈ polys, c.length ≤ t) :
    shamirReconstructBytes decode Q.lambdas (shamirQuorumShares Q.pts polys) =
      shamirSecretBytes decode polys := by
  unfold shamirReconstructBytes shamirQuorumShares shamirSecretBytes
  rw [List.map_map]
  apply List.map_congr_left
  intro c hc
  simp only [Function.comp]
  rw [lagrangeAtZero_evalCoeffs Q.lambdas Q.pts c t (hDeg c hc) Q.sum_one Q.kills_higher]

/-- A correct threshold signing run for the key `(skSeed, skPrf, pkSeed)`: cut-boundary oracles
    together with the proof that they evaluate that key. Constructors below build runs from the
    RSS share-level protocol and from a Shamir quorum.

    The field `matchesKey` is a correctness proof carried inside the run. A value of this type is
    therefore an honest run by construction: theorems quantified over `SlhThresholdRun` range over
    correct executions only, and say nothing about parties that deviate, about aborts, or about
    any distribution over runs. -/
structure SlhThresholdRun (p : Fips205Params) (skSeed skPrf pkSeed : List UInt8) where
  oracles : SlhMpcOracles
  matchesKey : oracles.MatchesKey p skSeed skPrf pkSeed

/-- Signature bytes output by a run. -/
def SlhThresholdRun.signBytes {p : Fips205Params} {skSeed skPrf pkSeed : List UInt8}
    (r : SlhThresholdRun p skSeed skPrf pkSeed) (msgPrime optRand : List UInt8) : List UInt8 :=
  thresholdSlhSignBytes p r.oracles msgPrime (slhKeygenMpc p r.oracles pkSeed) optRand

/-- Run of the concrete RSS protocol by quorum `q` on its own views. -/
def SlhThresholdRun.ofRss (p : Fips205Params) (q : RssQuorum)
    {skSeedSh skPrfSh : RssByteShares} (hSeedWf : skSeedSh.WellFormed) (hPrfWf : skPrfSh.WellFormed)
    (pkSeed : List UInt8) (tape : Nat → Nat → Nat → Nat → RssPrfZeroSeeds) :
    SlhThresholdRun p (reconstructRssBytes skSeedSh) (reconstructRssBytes skPrfSh) pkSeed where
  oracles := mkRssSlhMpcOracles p (q.assemble (q.views skSeedSh)) (q.assemble (q.views skPrfSh)) pkSeed tape
  matchesKey := by
    rw [RssQuorum.assemble_views, RssQuorum.assemble_views]
    exact mkRssSlhMpcOracles_matchesKey p hSeedWf hPrfWf pkSeed tape

/-- Run by a Shamir quorum: the oracles are assumed correct on the key the quorum recombines
    from its own shares; the run is then a run for the shared secret itself. -/
def SlhThresholdRun.ofShamir {R : Type} [LawfulCommRing R] (p : Fips205Params)
    (decode : R → UInt8) (t : Nat) (Q : ShamirQuorum R t)
    (seedPolys prfPolys : List (List R))
    (hSeedDeg : ∀ c ∈ seedPolys, c.length ≤ t) (hPrfDeg : ∀ c ∈ prfPolys, c.length ≤ t)
    (pkSeed : List UInt8) (o : SlhMpcOracles)
    (hO : o.MatchesKey p
      (shamirReconstructBytes decode Q.lambdas (shamirQuorumShares Q.pts seedPolys))
      (shamirReconstructBytes decode Q.lambdas (shamirQuorumShares Q.pts prfPolys)) pkSeed) :
    SlhThresholdRun p (shamirSecretBytes decode seedPolys) (shamirSecretBytes decode prfPolys) pkSeed where
  oracles := o
  matchesKey := by
    rw [← shamirReconstructBytes_quorum decode t Q seedPolys hSeedDeg,
        ← shamirReconstructBytes_quorum decode t Q prfPolys hPrfDeg]
    exact hO

/-- **Threshold output is the single-signer FIPS 205 output
    (`threshold_sig_deterministic_and_matches_single_signer`).** For any two correct runs for the
    same key (arbitrary and possibly different thresholds, party counts, quorums, share values and
    protocol randomness, all hidden inside the runs), the signature bytes on `(msgPrime, optRand)`
    are bit-identical to each other and to `slh_sign_internal` under that key, and verify.
    `optRand := pkSeed` is the deterministic variant; any other value is the hedged variant.

    This is functional correctness plus determinism of correct runs. Both runs carry
    `matchesKey`, so no adversary, abort event or probability distribution appears in the
    statement, and it is not an indistinguishability result about an execution with corrupted
    parties. -/
theorem threshold_sig_deterministic_and_matches_single_signer
    (p : Fips205Params) (hWf : p.wellFormed = true) {skSeed skPrf pkSeed : List UInt8}
    (r₁ r₂ : SlhThresholdRun p skSeed skPrf pkSeed) (msgPrime optRand : List UInt8) :
    r₁.signBytes msgPrime optRand =
      encodeSlhSig (slhSignInternal p msgPrime (slhKeygenInternal p skSeed skPrf pkSeed).1 optRand) ∧
    r₁.signBytes msgPrime optRand = r₂.signBytes msgPrime optRand ∧
    slhKeygenMpc p r₁.oracles pkSeed = (slhKeygenInternal p skSeed skPrf pkSeed).2 ∧
    slhVerifyInternal p msgPrime
      (slhSignMpc p r₁.oracles msgPrime (slhKeygenMpc p r₁.oracles pkSeed) optRand)
      (slhKeygenInternal p skSeed skPrf pkSeed).2 = true := by
  obtain ⟨hPk₁, _, hB₁, _, hV₁⟩ :=
    thresholdSlhSign_eq_slhSignInternal p hWf r₁.oracles skSeed skPrf pkSeed msgPrime optRand r₁.matchesKey
  obtain ⟨hPk₂, _, hB₂, _, _⟩ :=
    thresholdSlhSign_eq_slhSignInternal p hWf r₂.oracles skSeed skPrf pkSeed msgPrime optRand r₂.matchesKey
  have e₁ : r₁.signBytes msgPrime optRand =
      encodeSlhSig (slhSignInternal p msgPrime (slhKeygenInternal p skSeed skPrf pkSeed).1 optRand) := by
    unfold SlhThresholdRun.signBytes
    rw [hPk₁]
    exact hB₁
  have e₂ : r₂.signBytes msgPrime optRand =
      encodeSlhSig (slhSignInternal p msgPrime (slhKeygenInternal p skSeed skPrf pkSeed).1 optRand) := by
    unfold SlhThresholdRun.signBytes
    rw [hPk₂]
    exact hB₂
  refine ⟨e₁, e₁.trans e₂.symm, hPk₁, ?_⟩
  rw [hPk₁]
  exact hV₁

/-- Earlier name of `threshold_sig_deterministic_and_matches_single_signer`, kept because the
    challenge roster refers to it. The statement is the same determinism-and-correctness
    statement about correct runs; despite the name it is not an indistinguishability result. -/
theorem threshold_sig_perfectly_indistinguishable_from_single_signer
    (p : Fips205Params) (hWf : p.wellFormed = true) {skSeed skPrf pkSeed : List UInt8}
    (r₁ r₂ : SlhThresholdRun p skSeed skPrf pkSeed) (msgPrime optRand : List UInt8) :
    r₁.signBytes msgPrime optRand =
      encodeSlhSig (slhSignInternal p msgPrime (slhKeygenInternal p skSeed skPrf pkSeed).1 optRand) ∧
    r₁.signBytes msgPrime optRand = r₂.signBytes msgPrime optRand ∧
    slhKeygenMpc p r₁.oracles pkSeed = (slhKeygenInternal p skSeed skPrf pkSeed).2 ∧
    slhVerifyInternal p msgPrime
      (slhSignMpc p r₁.oracles msgPrime (slhKeygenMpc p r₁.oracles pkSeed) optRand)
      (slhKeygenInternal p skSeed skPrf pkSeed).2 = true :=
  threshold_sig_deterministic_and_matches_single_signer p hWf r₁ r₂ msgPrime optRand

/-- **Hedged variant, output equality (`threshold_sig_hedged_output_equality`).** Index the
    joint randomness (sharing randomness, quorum choice, protocol tapes and the shared hedging
    value) by `Fin N`. For every Boolean test on signature bytes, the number of indices on which
    the threshold output is accepted equals the number on which the single-signer output with the
    same hedging value is accepted.

    The two counted quantities are pointwise equal (each run's bytes equal the single-signer
    bytes by `threshold_sig_deterministic_and_matches_single_signer`), so the difference is zero
    for every `hedge : Fin N → List UInt8`, including constant ones. `hedge` is a parameter, not a
    sampled value: the theorem does not compare two output laws and is not a statistical-distance
    bound for a hedging distribution. -/
theorem threshold_sig_hedged_output_equality
    (p : Fips205Params) (hWf : p.wellFormed = true) {skSeed skPrf pkSeed : List UInt8}
    (N : Nat) (run : Fin N → SlhThresholdRun p skSeed skPrf pkSeed)
    (hedge : Fin N → List UInt8) (msgPrime : List UInt8) (D : List UInt8 → Bool) :
    natAbsDiff
      (finSum N (fun i => if D ((run i).signBytes msgPrime (hedge i)) then 1 else 0))
      (finSum N (fun i => if D (encodeSlhSig (slhSignInternal p msgPrime
        (slhKeygenInternal p skSeed skPrf pkSeed).1 (hedge i))) then 1 else 0)) = 0 := by
  have hLe := finSum_indicator_diff_le
    (fun i => D ((run i).signBytes msgPrime (hedge i)))
    (fun i => D (encodeSlhSig (slhSignInternal p msgPrime
      (slhKeygenInternal p skSeed skPrf pkSeed).1 (hedge i))))
    (fun _ => false)
    (fun i _ => by
      rw [(threshold_sig_deterministic_and_matches_single_signer p hWf (run i) (run i)
        msgPrime (hedge i)).1])
  have hZero : finSum N (fun _ : Fin N => if (false : Bool) = true then 1 else 0) = 0 := by
    have h := finSum_const N 0
    rw [Nat.mul_zero] at h
    exact h
  rw [hZero] at hLe
  exact Nat.eq_zero_of_le_zero hLe

/-- Earlier name of `threshold_sig_hedged_output_equality`, kept because the challenge roster
    refers to it. The statement is the same pointwise output equality; despite the name it does
    not bound a statistical distance between output distributions. -/
theorem threshold_sig_hedged_statistical_distance_zero
    (p : Fips205Params) (hWf : p.wellFormed = true) {skSeed skPrf pkSeed : List UInt8}
    (N : Nat) (run : Fin N → SlhThresholdRun p skSeed skPrf pkSeed)
    (hedge : Fin N → List UInt8) (msgPrime : List UInt8) (D : List UInt8 → Bool) :
    natAbsDiff
      (finSum N (fun i => if D ((run i).signBytes msgPrime (hedge i)) then 1 else 0))
      (finSum N (fun i => if D (encodeSlhSig (slhSignInternal p msgPrime
        (slhKeygenInternal p skSeed skPrf pkSeed).1 (hedge i))) then 1 else 0)) = 0 :=
  threshold_sig_hedged_output_equality p hWf N run hedge msgPrime D

/-- **2-of-3 RSS, concrete protocol.** Any two-party quorum, any well-formed sharing and any
    word tape (an arbitrary function into `RssPrfZeroSeeds`; its PRF expansion is not modelled)
    give the single-signer signature; two runs that share only the reconstructed key give
    identical bytes. -/
theorem rss_threshold_sig_independent_of_quorum_and_sharing
    (p : Fips205Params) (hWf : p.wellFormed = true) (q₁ q₂ : RssQuorum)
    {seed₁ prf₁ seed₂ prf₂ : RssByteShares}
    (hS₁ : seed₁.WellFormed) (hP₁ : prf₁.WellFormed) (hS₂ : seed₂.WellFormed) (hP₂ : prf₂.WellFormed)
    (hSeed : reconstructRssBytes seed₁ = reconstructRssBytes seed₂)
    (hPrf : reconstructRssBytes prf₁ = reconstructRssBytes prf₂)
    (pkSeed : List UInt8) (tape₁ tape₂ : Nat → Nat → Nat → Nat → RssPrfZeroSeeds)
    (msgPrime optRand : List UInt8) :
    rssQuorumSlhSignBytes p q₁ (q₁.views seed₁) (q₁.views prf₁) pkSeed tape₁ msgPrime optRand =
      encodeSlhSig (slhSignInternal p msgPrime
        (slhKeygenInternal p (reconstructRssBytes seed₁) (reconstructRssBytes prf₁) pkSeed).1 optRand) ∧
    rssQuorumSlhSignBytes p q₁ (q₁.views seed₁) (q₁.views prf₁) pkSeed tape₁ msgPrime optRand =
      rssQuorumSlhSignBytes p q₂ (q₂.views seed₂) (q₂.views prf₂) pkSeed tape₂ msgPrime optRand := by
  have h₁ := (threshold_sig_deterministic_and_matches_single_signer p hWf
    (SlhThresholdRun.ofRss p q₁ hS₁ hP₁ pkSeed tape₁) (SlhThresholdRun.ofRss p q₁ hS₁ hP₁ pkSeed tape₁)
    msgPrime optRand).1
  have h₂ := (threshold_sig_deterministic_and_matches_single_signer p hWf
    (SlhThresholdRun.ofRss p q₂ hS₂ hP₂ pkSeed tape₂) (SlhThresholdRun.ofRss p q₂ hS₂ hP₂ pkSeed tape₂)
    msgPrime optRand).1
  have e : encodeSlhSig (slhSignInternal p msgPrime
      (slhKeygenInternal p (reconstructRssBytes seed₁) (reconstructRssBytes prf₁) pkSeed).1 optRand) =
      encodeSlhSig (slhSignInternal p msgPrime
      (slhKeygenInternal p (reconstructRssBytes seed₂) (reconstructRssBytes prf₂) pkSeed).1 optRand) := by
    rw [hSeed, hPrf]
  exact ⟨h₁, h₁.trans (e.trans h₂.symm)⟩

/-- **Shamir `(t, n)`, reconstruction level.** Two Shamir presentations (possibly different rings,
    thresholds, quorums and polynomials) of the same key bytes, each with cut oracles that are
    correct on the key its quorum recombines, give identical signature bytes, equal to the
    single-signer output. -/
theorem shamir_threshold_sig_independent_of_threshold_quorum_and_sharing
    {R₁ R₂ : Type} [LawfulCommRing R₁] [LawfulCommRing R₂]
    (p : Fips205Params) (hWf : p.wellFormed = true)
    (decode₁ : R₁ → UInt8) (t₁ : Nat) (Q₁ : ShamirQuorum R₁ t₁) (seedPolys₁ prfPolys₁ : List (List R₁))
    (hSD₁ : ∀ c ∈ seedPolys₁, c.length ≤ t₁) (hPD₁ : ∀ c ∈ prfPolys₁, c.length ≤ t₁)
    (decode₂ : R₂ → UInt8) (t₂ : Nat) (Q₂ : ShamirQuorum R₂ t₂) (seedPolys₂ prfPolys₂ : List (List R₂))
    (hSD₂ : ∀ c ∈ seedPolys₂, c.length ≤ t₂) (hPD₂ : ∀ c ∈ prfPolys₂, c.length ≤ t₂)
    (hSeed : shamirSecretBytes decode₁ seedPolys₁ = shamirSecretBytes decode₂ seedPolys₂)
    (hPrf : shamirSecretBytes decode₁ prfPolys₁ = shamirSecretBytes decode₂ prfPolys₂)
    (pkSeed : List UInt8) (o₁ o₂ : SlhMpcOracles)
    (hO₁ : o₁.MatchesKey p
      (shamirReconstructBytes decode₁ Q₁.lambdas (shamirQuorumShares Q₁.pts seedPolys₁))
      (shamirReconstructBytes decode₁ Q₁.lambdas (shamirQuorumShares Q₁.pts prfPolys₁)) pkSeed)
    (hO₂ : o₂.MatchesKey p
      (shamirReconstructBytes decode₂ Q₂.lambdas (shamirQuorumShares Q₂.pts seedPolys₂))
      (shamirReconstructBytes decode₂ Q₂.lambdas (shamirQuorumShares Q₂.pts prfPolys₂)) pkSeed)
    (msgPrime optRand : List UInt8) :
    thresholdSlhSignBytes p o₁ msgPrime (slhKeygenMpc p o₁ pkSeed) optRand =
      encodeSlhSig (slhSignInternal p msgPrime
        (slhKeygenInternal p (shamirSecretBytes decode₁ seedPolys₁)
          (shamirSecretBytes decode₁ prfPolys₁) pkSeed).1 optRand) ∧
    thresholdSlhSignBytes p o₁ msgPrime (slhKeygenMpc p o₁ pkSeed) optRand =
      thresholdSlhSignBytes p o₂ msgPrime (slhKeygenMpc p o₂ pkSeed) optRand := by
  have h₁ := (threshold_sig_deterministic_and_matches_single_signer p hWf
    (SlhThresholdRun.ofShamir p decode₁ t₁ Q₁ seedPolys₁ prfPolys₁ hSD₁ hPD₁ pkSeed o₁ hO₁)
    (SlhThresholdRun.ofShamir p decode₁ t₁ Q₁ seedPolys₁ prfPolys₁ hSD₁ hPD₁ pkSeed o₁ hO₁)
    msgPrime optRand).1
  have h₂ := (threshold_sig_deterministic_and_matches_single_signer p hWf
    (SlhThresholdRun.ofShamir p decode₂ t₂ Q₂ seedPolys₂ prfPolys₂ hSD₂ hPD₂ pkSeed o₂ hO₂)
    (SlhThresholdRun.ofShamir p decode₂ t₂ Q₂ seedPolys₂ prfPolys₂ hSD₂ hPD₂ pkSeed o₂ hO₂)
    msgPrime optRand).1
  have e : encodeSlhSig (slhSignInternal p msgPrime
      (slhKeygenInternal p (shamirSecretBytes decode₁ seedPolys₁)
        (shamirSecretBytes decode₁ prfPolys₁) pkSeed).1 optRand) =
      encodeSlhSig (slhSignInternal p msgPrime
      (slhKeygenInternal p (shamirSecretBytes decode₂ seedPolys₂)
        (shamirSecretBytes decode₂ prfPolys₂) pkSeed).1 optRand) := by
    rw [hSeed, hPrf]
  exact ⟨h₁, h₁.trans (e.trans h₂.symm)⟩

/-! ### Satisfiability witnesses -/

/-- Two distinct well-formed sharings of the same seed, used with two distinct quorums. -/
theorem rss_threshold_sig_witness (pkSeed msgPrime optRand : List UInt8)
    (tape₁ tape₂ : Nat → Nat → Nat → Nat → RssPrfZeroSeeds) :
    (⟨[1], [2], [3]⟩ : RssByteShares) ≠ ⟨[7], [7], [0]⟩ ∧
    rssQuorumSlhSignBytes slhDsaShake128f .p01
      (RssQuorum.p01.views ⟨[1], [2], [3]⟩) (RssQuorum.p01.views ⟨[5], [0], [0]⟩)
      pkSeed tape₁ msgPrime optRand =
    rssQuorumSlhSignBytes slhDsaShake128f .p12
      (RssQuorum.p12.views ⟨[7], [7], [0]⟩) (RssQuorum.p12.views ⟨[0], [5], [0]⟩)
      pkSeed tape₂ msgPrime optRand :=
  ⟨by decide +kernel,
   (rss_threshold_sig_independent_of_quorum_and_sharing slhDsaShake128f slhDsaShake128f_wellFormed
    .p01 .p12 ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (by decide +kernel) (by decide +kernel)
    pkSeed tape₁ tape₂ msgPrime optRand).2⟩

/-- Quorum `{1, 2}` of a threshold-2 Goldilocks sharing: `2·f(1) − f(2) = f(0)`. -/
def shamirGoldilocksQuorum12 : ShamirQuorum Goldilocks 2 where
  pts := [Goldilocks.ofNat 1, Goldilocks.ofNat 2]
  lambdas := [Goldilocks.ofNat 2, Goldilocks.ofNat (goldilocksPrime - 1)]
  sum_one := by decide +kernel
  kills_higher := by
    intro d h1 h2
    have hd : d = 1 := by omega
    subst hd
    decide +kernel

/-- Quorum `{2, 3}` of a threshold-2 Goldilocks sharing: `3·f(2) − 2·f(3) = f(0)`. -/
def shamirGoldilocksQuorum23 : ShamirQuorum Goldilocks 2 where
  pts := [Goldilocks.ofNat 2, Goldilocks.ofNat 3]
  lambdas := [Goldilocks.ofNat 3, Goldilocks.ofNat (goldilocksPrime - 2)]
  sum_one := by decide +kernel
  kills_higher := by
    intro d h1 h2
    have hd : d = 1 := by omega
    subst hd
    decide +kernel

/-- Two different quorums of a 2-of-3 Goldilocks sharing hold different non-zero degree-1 shares
    of the byte `5` and recombine it identically; pairing each quorum with distinct non-zero
    masked 3-party sharings shows the FIPS 205 `SlhThresholdRun.ofShamir` hypotheses are
    jointly satisfiable without `rssPublicBytes`. (See `shamir_poseidon2_threshold_sig_witness`
    below for the pure-Shamir `Poseidon2` share-level protocol witness with zero RSS.) -/
theorem shamir_threshold_sig_witness (pkSeed msgPrime optRand : List UInt8)
    (tape : Nat → Nat → Nat → Nat → RssPrfZeroSeeds) :
    shamirQuorumShares shamirGoldilocksQuorum12.pts [[Goldilocks.ofNat 5, Goldilocks.ofNat 7]] ≠
      shamirQuorumShares shamirGoldilocksQuorum23.pts [[Goldilocks.ofNat 5, Goldilocks.ofNat 7]] ∧
    ∃ o₁ o₂ : SlhMpcOracles,
      thresholdSlhSignBytes slhDsaShake128f o₁ msgPrime (slhKeygenMpc slhDsaShake128f o₁ pkSeed) optRand =
        thresholdSlhSignBytes slhDsaShake128f o₂ msgPrime (slhKeygenMpc slhDsaShake128f o₂ pkSeed) optRand ∧
      thresholdSlhSignBytes slhDsaShake128f o₁ msgPrime (slhKeygenMpc slhDsaShake128f o₁ pkSeed) optRand =
        encodeSlhSig (slhSignInternal slhDsaShake128f msgPrime
          (slhKeygenInternal slhDsaShake128f [5] [5] pkSeed).1 optRand) := by
  refine ⟨by decide +kernel, ?_⟩
  let dec : Goldilocks → UInt8 := fun g => UInt8.ofNat g.val
  let polys : List (List Goldilocks) := [[Goldilocks.ofNat 5, Goldilocks.ofNat 7]]
  have hDeg : ∀ c ∈ polys, c.length ≤ 2 := by
    intro c hc
    rcases List.mem_singleton.mp hc with rfl
    exact Nat.le_refl 2
  let sh₁ : RssByteShares := ⟨[0xA0], [0xA0], [0x05]⟩
  let sh₂ : RssByteShares := ⟨[0x39], [0x30], [0x0C]⟩
  have hKey₁ : shamirReconstructBytes dec shamirGoldilocksQuorum12.lambdas
      (shamirQuorumShares shamirGoldilocksQuorum12.pts polys) = reconstructRssBytes sh₁ := by
    decide +kernel
  have hKey₂ : shamirReconstructBytes dec shamirGoldilocksQuorum23.lambdas
      (shamirQuorumShares shamirGoldilocksQuorum23.pts polys) = reconstructRssBytes sh₂ := by
    decide +kernel
  have hM₁ := mkRssSlhMpcOracles_matchesKey slhDsaShake128f
    (skSeedSh := sh₁) (skPrfSh := sh₁) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ pkSeed tape
  have hM₂ := mkRssSlhMpcOracles_matchesKey slhDsaShake128f
    (skSeedSh := sh₂) (skPrfSh := sh₂) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ pkSeed tape
  rw [← hKey₁] at hM₁
  rw [← hKey₂] at hM₂
  have hSecret : shamirSecretBytes dec polys = [5] := by decide +kernel
  have h := shamir_threshold_sig_independent_of_threshold_quorum_and_sharing
    slhDsaShake128f slhDsaShake128f_wellFormed
    dec 2 shamirGoldilocksQuorum12 polys polys hDeg hDeg
    dec 2 shamirGoldilocksQuorum23 polys polys hDeg hDeg rfl rfl pkSeed _ _ hM₁ hM₂ msgPrime optRand
  rw [hSecret] at h
  exact ⟨_, _, h.2, h.1⟩

/-- **`(t, n)` Shamir Sub-Threshold View Privacy Bijection (`shamir_single_share_privacy_bijection`)**:
    For any `< t` corrupt evaluation points `corruptPts` (`corruptPts.length + 1 ≤ t`, `∀ c ∈ corruptPts, c ≠ 0`)
    and any two secrets `s₁ s₂ : Goldilocks`, `shamir_rebalanceEquiv` exhibits an explicit `SimpleEquiv`
    bijection on degree-`< t` Shamir polynomials mapping secret `s₁` to secret `s₂` while keeping
    every corrupt party's share identical (`RoundPoly.evalCoeffs Q.1 xc = RoundPoly.evalCoeffs P.1 xc`). -/
theorem shamir_single_share_privacy_bijection
    (t : Nat) (corruptPts : List Goldilocks) (s₁ s₂ : Goldilocks)
    (hCard : corruptPts.length + 1 ≤ t)
    (hNonZero : ∀ c ∈ corruptPts, c ≠ Goldilocks.zero)
    (P : ShamirPadPoly Goldilocks t)
    (hSec₁ : RoundPoly.evalCoeffs P.1 Goldilocks.zero = s₁) :
    let eqv := shamir_rebalanceEquiv Goldilocks.inv t corruptPts (Goldilocks.sub s₂ s₁) hCard
    let Q := eqv.toFun P
    eqv.invFun Q = P ∧
    RoundPoly.evalCoeffs Q.1 Goldilocks.zero = s₂ ∧
    (∀ xc ∈ corruptPts, RoundPoly.evalCoeffs Q.1 xc = RoundPoly.evalCoeffs P.1 xc) := by
  intro eqv Q
  obtain ⟨hAt0, hCorr⟩ := pad_bijection_masked_openings_uniform
    Goldilocks.inv (fun _ hx => Goldilocks.mul_inv_cancel hx)
    t corruptPts (Goldilocks.sub s₂ s₁) hCard hNonZero P
  have hQ0 : RoundPoly.evalCoeffs Q.1 Goldilocks.zero = s₂ := by
    change RoundPoly.evalCoeffs ((shamir_rebalanceEquiv Goldilocks.inv t corruptPts (Goldilocks.sub s₂ s₁) hCard).toFun P).1
      CommRingOps.zero = s₂
    rw [← LawfulCommRing.zero_add (RoundPoly.evalCoeffs _ CommRingOps.zero), hAt0]
    change CommRingOps.add (CommRingOps.sub s₂ s₁) (RoundPoly.evalCoeffs P.1 Goldilocks.zero) = s₂
    rw [hSec₁, LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
        LawfulCommRing.add_left_neg, LawfulCommRing.add_zero]
  exact ⟨eqv.left_inv P, hQ0, hCorr⟩

/-- Concrete 1-of-3 view witness for threshold `t = 2`: party `x = 1` observes identical share `12`
    under degree-1 sharings of secret `5` (`5 + 7X`) and secret `42` (`42 + (p - 30)X`). -/
theorem shamir_single_share_does_not_determine_secret :
    let p₁ : List Goldilocks := [Goldilocks.ofNat 5, Goldilocks.ofNat 7]
    let p₂ : List Goldilocks := [Goldilocks.ofNat 42, Goldilocks.sub (Goldilocks.ofNat 12) (Goldilocks.ofNat 42)]
    RoundPoly.evalCoeffs p₁ (Goldilocks.ofNat 1) = RoundPoly.evalCoeffs p₂ (Goldilocks.ofNat 1) ∧
    RoundPoly.evalCoeffs p₁ Goldilocks.zero ≠ RoundPoly.evalCoeffs p₂ Goldilocks.zero := by
  decide +kernel

def demoPow7TupleQuorum12 : SharedPow7Tuple :=
  { rSh  := demoPow7TupleFor4.rSh.take 2
    r2Sh := demoPow7TupleFor4.r2Sh.take 2
    r3Sh := demoPow7TupleFor4.r3Sh.take 2
    r4Sh := demoPow7TupleFor4.r4Sh.take 2
    r5Sh := demoPow7TupleFor4.r5Sh.take 2
    r6Sh := demoPow7TupleFor4.r6Sh.take 2
    r7Sh := demoPow7TupleFor4.r7Sh.take 2 }

def demoPow7TupleQuorum23 : SharedPow7Tuple :=
  { rSh  := demoPow7TupleFor4.rSh.drop 1
    r2Sh := demoPow7TupleFor4.r2Sh.drop 1
    r3Sh := demoPow7TupleFor4.r3Sh.drop 1
    r4Sh := demoPow7TupleFor4.r4Sh.drop 1
    r5Sh := demoPow7TupleFor4.r5Sh.drop 1
    r6Sh := demoPow7TupleFor4.r6Sh.drop 1
    r7Sh := demoPow7TupleFor4.r7Sh.drop 1 }

def demoZeroMasks2 : List GoldilocksExt2 :=
  [⟨Goldilocks.ofNat 19, Goldilocks.ofNat 23⟩,
   GoldilocksExt2.neg ⟨Goldilocks.ofNat 19, Goldilocks.ofNat 23⟩]

def demoCallPrep12 : Poseidon2CallPrep :=
  { extInit := fun _ _ => (demoPow7TupleQuorum12, demoZeroMasks2)
    inter   := fun _   => (demoPow7TupleQuorum12, demoZeroMasks2)
    extTerm := fun _ _ => (demoPow7TupleQuorum12, demoZeroMasks2) }

def demoCallPrep23 : Poseidon2CallPrep :=
  { extInit := fun _ _ => (demoPow7TupleQuorum23, demoZeroMasks2)
    inter   := fun _   => (demoPow7TupleQuorum23, demoZeroMasks2)
    extTerm := fun _ _ => (demoPow7TupleQuorum23, demoZeroMasks2) }

/-- Ideal `ℱ_bitdecomp` masked byte-share reference specification for `ShamirQuorum Goldilocks 2`:
    deals non-constant degree-1 Shamir shares `[b, maskSlope]` across `Q.pts` to witness
    `ValidShamirLimbDecomp8` satisfiability without any RSS scaffolding. -/
def idealShamirBitDecompRef (Q : ShamirQuorum Goldilocks 2) (maskSlope : Goldilocks)
    (limbSh : List Goldilocks) : List (List Goldilocks) :=
  (be 8 (lagrangeCombine Q.lambdas limbSh).val).map (fun b =>
    Q.pts.map (fun pt => RoundPoly.evalCoeffs [Goldilocks.ofNat b.toNat, maskSlope] pt))

private theorem idealShamirBitDecompRef_valid
    (Q : ShamirQuorum Goldilocks 2) (hPtsLen : Q.pts.length = Q.lambdas.length)
    (maskSlope : Goldilocks) :
    ValidShamirLimbDecomp8 Q.lambdas (idealShamirBitDecompRef Q maskSlope) := by
  intro limbSh _
  unfold idealShamirBitDecompRef
  suffices hAll : ∀ (bs : List UInt8),
      ShamirByteSharesValid Q.lambdas
        (bs.map (fun b => Q.pts.map (fun pt => RoundPoly.evalCoeffs [Goldilocks.ofNat b.toNat, maskSlope] pt))) bs by
    exact hAll _
  intro bs
  induction bs with
  | nil => trivial
  | cons b rest ih =>
    refine ⟨by simp [hPtsLen], ?_, ih⟩
    unfold lagrangeCombine
    rw [lagrangeAtZero_evalCoeffs Q.lambdas Q.pts [Goldilocks.ofNat b.toNat, maskSlope] 2
          (Nat.le_refl 2) Q.sum_one Q.kills_higher]
    simp [RoundPoly.evalCoeffs, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]

/-- **Pure-Shamir Share-Level `Poseidon2` Threshold Signing Witness (`shamir_poseidon2_threshold_sig_witness`)**:
    Two distinct 2-of-3 `Goldilocks` Shamir quorums (`{1, 2}` and `{2, 3}`) holding distinct
    non-zero degree-1 shares of `skSeed = [5]` (`5 + 7X`) and `skPrf = [9]` (`9 + 11X`),
    distinct non-zero `SharedPow7Tuple` shares (`demoPow7TupleQuorum12`, `demoPow7TupleQuorum23`),
    and non-zero `GoldilocksExt2` SPDZ MAC masks (`demoZeroMasks2`) execute `mkShamirPoseidon2MpcOracles`
    (with **zero** `RssByteShares` or `rssPublicBytes`) and derive the exact same `Poseidon2`
    public key and `evalCutBatchSignMpc` output as single-party `evalSingleSign poseidon2Suite`! -/
theorem shamir_poseidon2_threshold_sig_witness
    (params : PqHashParams) (pkSeed msg optRand : List UInt8) (leafGlobalIdx maxGrind : Nat) :
    let seedPolys := [[Goldilocks.ofNat 5, Goldilocks.ofNat 7]]
    let prfPolys  := [[Goldilocks.ofNat 9, Goldilocks.ofNat 11]]
    let seedSh₁ := shamirQuorumShares shamirGoldilocksQuorum12.pts seedPolys
    let seedSh₂ := shamirQuorumShares shamirGoldilocksQuorum23.pts seedPolys
    let prfSh₁  := shamirQuorumShares shamirGoldilocksQuorum12.pts prfPolys
    let prfSh₂  := shamirQuorumShares shamirGoldilocksQuorum23.pts prfPolys
    let o₁ := mkShamirPoseidon2MpcOracles shamirGoldilocksQuorum12.lambdas seedSh₁ prfSh₁ pkSeed
                (idealShamirBitDecompRef shamirGoldilocksQuorum12 (Goldilocks.ofNat 13))
                (fun _ _ => demoCallPrep12)
    let o₂ := mkShamirPoseidon2MpcOracles shamirGoldilocksQuorum23.lambdas seedSh₂ prfSh₂ pkSeed
                (idealShamirBitDecompRef shamirGoldilocksQuorum23 (Goldilocks.ofNat 17))
                (fun _ _ => demoCallPrep23)
    let sk : PqSecretKey := { skSeed := [5], skPrf := [9], pkSeed := pkSeed }
    seedSh₁ ≠ seedSh₂ ∧
    prfSh₁ ≠ prfSh₂ ∧
    derivePublicKeyMpc poseidon2Suite params o₁ pkSeed = derivePublicKey poseidon2Suite params sk ∧
    derivePublicKeyMpc poseidon2Suite params o₂ pkSeed = derivePublicKey poseidon2Suite params sk ∧
    evalCutBatchSignMpc poseidon2Suite params o₁ (derivePublicKeyMpc poseidon2Suite params o₁ pkSeed)
      msg optRand leafGlobalIdx maxGrind =
      evalCutBatchSignMpc poseidon2Suite params o₂ (derivePublicKeyMpc poseidon2Suite params o₂ pkSeed)
        msg optRand leafGlobalIdx maxGrind ∧
    evalCutBatchSignMpc poseidon2Suite params o₁ (derivePublicKeyMpc poseidon2Suite params o₁ pkSeed)
      msg optRand leafGlobalIdx maxGrind =
      evalSingleSign poseidon2Suite params sk msg optRand leafGlobalIdx maxGrind := by
  intro seedPolys prfPolys seedSh₁ seedSh₂ prfSh₁ prfSh₂ o₁ o₂ sk
  have hSum₁ : ringListSum shamirGoldilocksQuorum12.lambdas = Goldilocks.one := by decide +kernel
  have hSum₂ : ringListSum shamirGoldilocksQuorum23.lambdas = Goldilocks.one := by decide +kernel
  have hSeed₁ : ShamirByteSharesValid shamirGoldilocksQuorum12.lambdas seedSh₁ [5] :=
    ⟨by decide +kernel, by decide +kernel, trivial⟩
  have hSeed₂ : ShamirByteSharesValid shamirGoldilocksQuorum23.lambdas seedSh₂ [5] :=
    ⟨by decide +kernel, by decide +kernel, trivial⟩
  have hPrf₁ : ShamirByteSharesValid shamirGoldilocksQuorum12.lambdas prfSh₁ [9] :=
    ⟨by decide +kernel, by decide +kernel, trivial⟩
  have hPrf₂ : ShamirByteSharesValid shamirGoldilocksQuorum23.lambdas prfSh₂ [9] :=
    ⟨by decide +kernel, by decide +kernel, trivial⟩
  have hTup12 : demoPow7TupleQuorum12.validAt shamirGoldilocksQuorum12.lambdas := by
    unfold SharedPow7Tuple.validAt; decide +kernel
  have hTup23 : demoPow7TupleQuorum23.validAt shamirGoldilocksQuorum23.lambdas := by
    unfold SharedPow7Tuple.validAt; decide +kernel
  have hMac2 : verifySpdzZeroSumMac demoZeroMasks2 = true := by decide +kernel
  have hPrep₁ : ∀ _ _ : Nat, demoCallPrep12.validAt shamirGoldilocksQuorum12.lambdas :=
    fun _ _ => ⟨fun _ _ => ⟨hTup12, hMac2⟩, fun _ => ⟨hTup12, hMac2⟩, fun _ _ => ⟨hTup12, hMac2⟩⟩
  have hPrep₂ : ∀ _ _ : Nat, demoCallPrep23.validAt shamirGoldilocksQuorum23.lambdas :=
    fun _ _ => ⟨fun _ _ => ⟨hTup23, hMac2⟩, fun _ => ⟨hTup23, hMac2⟩, fun _ _ => ⟨hTup23, hMac2⟩⟩
  have hRun₁ := shamir_poseidon2_shared_thresholdSign_eq_evalSingleSign
    params shamirGoldilocksQuorum12.lambdas hSum₁ hSeed₁ hPrf₁ pkSeed msg optRand leafGlobalIdx maxGrind
    (idealShamirBitDecompRef_valid shamirGoldilocksQuorum12 rfl (Goldilocks.ofNat 13))
    (fun _ _ => demoCallPrep12) hPrep₁
  have hRun₂ := shamir_poseidon2_shared_thresholdSign_eq_evalSingleSign
    params shamirGoldilocksQuorum23.lambdas hSum₂ hSeed₂ hPrf₂ pkSeed msg optRand leafGlobalIdx maxGrind
    (idealShamirBitDecompRef_valid shamirGoldilocksQuorum23 rfl (Goldilocks.ofNat 17))
    (fun _ _ => demoCallPrep23) hPrep₂
  exact ⟨by decide +kernel, by decide +kernel, hRun₁.1, hRun₂.1, hRun₁.2.1.trans hRun₂.2.1.symm, hRun₁.2.1⟩

/-- XOR with a corrupt coin fixed before the independent uniform honest coin preserves the
    single-signer hedged output law, for every encoding and every signature distinguisher.
    This is a counting statement about the joint coin before selective abort. Applying it to
    a commitment protocol additionally requires a hiding/independence argument; a deterministic
    commitment hash alone does not supply that premise. -/
theorem threshold_joint_coin_output_law
    (p : Fips205Params) (sk : SlhSecretKey) (msg : List UInt8)
    (width : Nat) (encode : BitVec width → List UInt8) (corruptCoin : BitVec width)
    (D : List UInt8 → Bool) :
    finSum (2 ^ width) (fun i => if D (encodeSlhSig
      (slhSignInternal p msg sk (encode (BitVec.ofFin i ^^^ corruptCoin)))) then 1 else 0) =
    finSum (2 ^ width) (fun i => if D (encodeSlhSig
      (slhSignInternal p msg sk (encode (BitVec.ofFin i)))) then 1 else 0) := by
  let flip : Fin (2 ^ width) → Fin (2 ^ width) :=
    fun i => (BitVec.ofFin i ^^^ corruptCoin).toFin
  have hInv : ∀ i, flip (flip i) = i := by
    intro i
    apply Fin.ext
    have h : (BitVec.ofFin i ^^^ corruptCoin) ^^^ corruptCoin = BitVec.ofFin i := by
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    exact congrArg BitVec.toNat h
  exact finSum_perm_invariant flip flip hInv hInv
    (fun i => if D (encodeSlhSig (slhSignInternal p msg sk (encode (BitVec.ofFin i)))) then 1 else 0)

/-- A corrupt party can commit to zero, observe the honest coin, and open only when the
    joint coin is one. Even an ideal hiding commitment cannot stop this selective abort.
    Of two equally likely honest coins there is one accepted execution, and its coin is
    always one; the unconditioned uniform coin is one on only one of two executions.
    Thus output laws conditioned on success cannot in general use the original uniform
    hedge law. Security with abort must give the ideal adversary the same abort capability. -/
theorem tooth_selective_abort_biases_committed_joint_coin :
    let honest : Fin 2 → Bool := fun i => i.val == 1
    let accepted : Fin 2 → Option Bool := fun i =>
      if honest i ^^ false then some (honest i ^^ false) else none
    finSum 2 (fun i => if (accepted i).isSome then 1 else 0) = 1 ∧
    finSum 2 (fun i => if accepted i == some true then 1 else 0) = 1 ∧
    (∀ i, accepted i ≠ some false) ∧
    finSum 2 (fun i => if honest i then 1 else 0) = 1 := by
  decide +kernel

/-! ### Active-malicious hedged signing: abort, exact single-signer output, or counted tag forgery

One corrupt party, one hedged signing run. The order of play is the order of the fields below:
the corrupt coin share is fixed before the honest coin share is opened (that is what a hiding
commitment buys, and the binding side is that the opened value is the committed one); the
corrupt party then sees the honest coin and chooses its share modification; the consistency
challenge is sampled after the modification is fixed; finally the corrupt party may refuse to
finish. The statements below hold for every tag scheme. The number of accepted non-zero
deviations is left as an explicit term; `Qsag.RssSlhFullSecurity` bounds it by `deg / 2^128`
for the `GF(2^128)` Horner tag. -/

/-- A consistency-tag check as the honest parties see it: which deviations are the zero
    deviation, and which `(deviation, challenge)` pairs are accepted. Completeness is the only
    law: an unmodified execution is never rejected. Soundness is not a field; the theorems below
    count the accepted non-zero deviations instead of assuming there are none. -/
structure ConsistencyTagScheme (Dev : Type) (nChal : Nat) where
  isHonest : Dev → Bool
  accepts : Dev → Fin nChal → Bool
  complete : ∀ d c, isHonest d = true → accepts d c = true

/-- Strategy of the corrupt party in one hedged signing run.
    * `corruptCoin` is committed before the honest coin share is visible.
    * `deviation` is the share modification, chosen knowing the honest coin share and before the
      consistency challenge.
    * `tamperedOutput` is what the honest parties would release if the modification passed the
      tag check.
    * `aborts` is the decision to stop the run, taken with the honest coin share and the
      challenge in view. -/
structure ActiveSlhAdversary (width nChal : Nat) (Dev : Type) where
  corruptCoin : BitVec width
  deviation : BitVec width → Dev
  tamperedOutput : BitVec width → Fin nChal → List UInt8
  aborts : BitVec width → Fin nChal → Bool

/-- Output of the honest parties in one run against `adv`: `none` on abort (the corrupt party
    stopped, or the tag check rejected), otherwise the released signature bytes. The hedging
    value is `encode (honestCoin ⊕ corruptCoin)`. -/
def activeMaliciousThresholdSign {p : Fips205Params} {skSeed skPrf pkSeed : List UInt8}
    (run : SlhThresholdRun p skSeed skPrf pkSeed) {width nChal : Nat} {Dev : Type}
    (tags : ConsistencyTagScheme Dev nChal) (adv : ActiveSlhAdversary width nChal Dev)
    (encode : BitVec width → List UInt8) (msgPrime : List UInt8)
    (honestCoin : Fin (2 ^ width)) (chal : Fin nChal) : Option (List UInt8) :=
  if adv.aborts (BitVec.ofFin honestCoin) chal then none
  else if !(tags.accepts (adv.deviation (BitVec.ofFin honestCoin)) chal) then none
  else if tags.isHonest (adv.deviation (BitVec.ofFin honestCoin)) then
    some (run.signBytes msgPrime (encode (BitVec.ofFin honestCoin ^^^ adv.corruptCoin)))
  else some (adv.tamperedOutput (BitVec.ofFin honestCoin) chal)

/-- The failure event: a non-zero deviation that the tag check accepts in a run the corrupt
    party lets finish. -/
def activeTagForgery {width nChal : Nat} {Dev : Type}
    (tags : ConsistencyTagScheme Dev nChal) (adv : ActiveSlhAdversary width nChal Dev)
    (honestCoin : Fin (2 ^ width)) (chal : Fin nChal) : Bool :=
  !(adv.aborts (BitVec.ofFin honestCoin) chal) &&
    tags.accepts (adv.deviation (BitVec.ofFin honestCoin)) chal &&
    !(tags.isHonest (adv.deviation (BitVec.ofFin honestCoin)))

/-- The runs in which the ideal functionality with abort releases a signature: the corrupt party
    does not stop and did not modify its shares. -/
def activeReleased {width nChal : Nat} {Dev : Type}
    (tags : ConsistencyTagScheme Dev nChal) (adv : ActiveSlhAdversary width nChal Dev)
    (honestCoin : Fin (2 ^ width)) (chal : Fin nChal) : Bool :=
  !(adv.aborts (BitVec.ofFin honestCoin) chal) &&
    tags.isHonest (adv.deviation (BitVec.ofFin honestCoin))

private theorem finSum_natAbsDiff_le : ∀ (n : Nat) (f g b : Fin n → Nat),
    (∀ i, natAbsDiff (f i) (g i) ≤ b i) →
    natAbsDiff (finSum n f) (finSum n g) ≤ finSum n b
  | 0, _, _, _, _ => by simp [finSum, natAbsDiff]
  | n + 1, f, g, b, h => by
    simp only [finSum]
    have ih := finSum_natAbsDiff_le n
      (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
      (fun i => g ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
      (fun i => b ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
      (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    exact Nat.le_trans (natAbsDiff_add_le _ _ _ _)
      (Nat.add_le_add (h ⟨0, Nat.zero_lt_succ n⟩) ih)

/-- In every run, the honest parties abort, or release exactly the single-signer signature on
    the hedge `encode (honestCoin ⊕ corruptCoin)`, or the run is a tag forgery. -/
theorem activeMaliciousThresholdSign_cases
    (p : Fips205Params) (hWf : p.wellFormed = true) {skSeed skPrf pkSeed : List UInt8}
    (run : SlhThresholdRun p skSeed skPrf pkSeed) {width nChal : Nat} {Dev : Type}
    (tags : ConsistencyTagScheme Dev nChal) (adv : ActiveSlhAdversary width nChal Dev)
    (encode : BitVec width → List UInt8) (msgPrime : List UInt8)
    (honestCoin : Fin (2 ^ width)) (chal : Fin nChal) :
    (activeTagForgery tags adv honestCoin chal = false →
      activeMaliciousThresholdSign run tags adv encode msgPrime honestCoin chal =
        if activeReleased tags adv honestCoin chal then
          some (encodeSlhSig (slhSignInternal p msgPrime
            (slhKeygenInternal p skSeed skPrf pkSeed).1
            (encode (BitVec.ofFin honestCoin ^^^ adv.corruptCoin))))
        else none) ∧
    (activeTagForgery tags adv honestCoin chal = true →
      activeMaliciousThresholdSign run tags adv encode msgPrime honestCoin chal =
        some (adv.tamperedOutput (BitVec.ofFin honestCoin) chal)) := by
  have hSig := (threshold_sig_deterministic_and_matches_single_signer p hWf run run msgPrime
    (encode (BitVec.ofFin honestCoin ^^^ adv.corruptCoin))).1
  unfold activeMaliciousThresholdSign activeTagForgery activeReleased
  cases hA : adv.aborts (BitVec.ofFin honestCoin) chal
  · cases hH : tags.isHonest (adv.deviation (BitVec.ofFin honestCoin))
    · cases hT : tags.accepts (adv.deviation (BitVec.ofFin honestCoin)) chal
      · exact ⟨fun _ => rfl, fun h => Bool.noConfusion h⟩
      · exact ⟨fun h => Bool.noConfusion h, fun _ => rfl⟩
    · have hT := tags.complete (adv.deviation (BitVec.ofFin honestCoin)) chal hH
      rw [hT]
      exact ⟨fun _ => congrArg some hSig, fun h => Bool.noConfusion h⟩
  · exact ⟨fun _ => rfl, fun h => Bool.noConfusion h⟩

/-- **Active-malicious hedged threshold signing
    (`active_malicious_threshold_sig_abort_or_exact_hedged_dist`).** For one corrupt party with
    an arbitrary strategy `adv`, any tag scheme, a uniform honest coin share and a uniform
    consistency challenge:

    1. Every run aborts, or releases exactly `slh_sign_internal` under the shared key with
       hedge `encode (honestCoin ⊕ corruptCoin)`, or is a tag forgery
       (`activeTagForgery`: a modified share accepted by the check).
    2. For every test `D` on signature bytes, the number of runs whose released bytes pass `D`
       differs from the number of runs in which the ideal functionality with abort releases a
       single-signer signature passing `D` by at most the number of tag forgeries. The ideal
       count uses the same release set `activeReleased`, which the corrupt party controls:
       this is security with abort, and the released law is the single-signer hedged law
       restricted to that set, not the unconditioned one
       (`tooth_selective_abort_biases_committed_joint_coin`).
    3. The abort pattern does not depend on the key: for a run of any other key, with the same
       strategy, exactly the same `(honestCoin, challenge)` pairs abort.

    The statement makes no claim that tag forgeries are rare; that is a property of the tag
    scheme and is proved for the `GF(2^128)` Horner tag in `Qsag.RssSlhFullSecurity`
    (`rss_active_tag_forgery_count_le`). The independence of `corruptCoin` and of `deviation`
    from later values is built into `ActiveSlhAdversary`; deriving it from a concrete commitment
    needs a hiding assumption that is not discharged here. -/
theorem active_malicious_threshold_sig_abort_or_exact_hedged_dist
    (p : Fips205Params) (hWf : p.wellFormed = true) {skSeed skPrf pkSeed : List UInt8}
    (run : SlhThresholdRun p skSeed skPrf pkSeed) {width nChal : Nat} {Dev : Type}
    (tags : ConsistencyTagScheme Dev nChal) (adv : ActiveSlhAdversary width nChal Dev)
    (encode : BitVec width → List UInt8) (msgPrime : List UInt8) :
    (∀ (honestCoin : Fin (2 ^ width)) (chal : Fin nChal),
      activeMaliciousThresholdSign run tags adv encode msgPrime honestCoin chal = none ∨
      activeMaliciousThresholdSign run tags adv encode msgPrime honestCoin chal =
        some (encodeSlhSig (slhSignInternal p msgPrime
          (slhKeygenInternal p skSeed skPrf pkSeed).1
          (encode (BitVec.ofFin honestCoin ^^^ adv.corruptCoin)))) ∨
      activeTagForgery tags adv honestCoin chal = true) ∧
    (∀ D : List UInt8 → Bool,
      natAbsDiff
        (finSum (2 ^ width) (fun h => finSum nChal (fun c =>
          if (match activeMaliciousThresholdSign run tags adv encode msgPrime h c with
              | some s => D s
              | none => false) then 1 else 0)))
        (finSum (2 ^ width) (fun h => finSum nChal (fun c =>
          if (activeReleased tags adv h c &&
              D (encodeSlhSig (slhSignInternal p msgPrime
                (slhKeygenInternal p skSeed skPrf pkSeed).1
                (encode (BitVec.ofFin h ^^^ adv.corruptCoin))))) then 1 else 0))) ≤
      finSum (2 ^ width) (fun h => finSum nChal (fun c =>
        if activeTagForgery tags adv h c then 1 else 0))) ∧
    (∀ {skSeed' skPrf' pkSeed' : List UInt8} (run' : SlhThresholdRun p skSeed' skPrf' pkSeed')
       (msgPrime' : List UInt8) (honestCoin : Fin (2 ^ width)) (chal : Fin nChal),
      (activeMaliciousThresholdSign run tags adv encode msgPrime honestCoin chal).isSome =
      (activeMaliciousThresholdSign run' tags adv encode msgPrime' honestCoin chal).isSome) := by
  refine ⟨?_, ?_, ?_⟩
  · intro honestCoin chal
    have hC := activeMaliciousThresholdSign_cases p hWf run tags adv encode msgPrime honestCoin chal
    cases hF : activeTagForgery tags adv honestCoin chal
    · have h := hC.1 hF
      cases hR : activeReleased tags adv honestCoin chal
      · rw [hR] at h; exact Or.inl h
      · rw [hR] at h; exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr rfl)
  · intro D
    apply finSum_natAbsDiff_le
    intro h
    apply finSum_indicator_diff_le
      (fun c => match activeMaliciousThresholdSign run tags adv encode msgPrime h c with
                | some s => D s
                | none => false)
      (fun c => activeReleased tags adv h c &&
                D (encodeSlhSig (slhSignInternal p msgPrime
                  (slhKeygenInternal p skSeed skPrf pkSeed).1
                  (encode (BitVec.ofFin h ^^^ adv.corruptCoin)))))
      (fun c => activeTagForgery tags adv h c)
    intro c hF
    have hEq := (activeMaliciousThresholdSign_cases p hWf run tags adv encode msgPrime h c).1 hF
    rw [hEq]
    cases activeReleased tags adv h c <;> rfl
  · intro skSeed' skPrf' pkSeed' run' msgPrime' honestCoin chal
    unfold activeMaliciousThresholdSign
    cases adv.aborts (BitVec.ofFin honestCoin) chal
    · cases tags.accepts (adv.deviation (BitVec.ofFin honestCoin)) chal
      · rfl
      · cases tags.isHonest (adv.deviation (BitVec.ofFin honestCoin)) <;> rfl
    · rfl

/-- **Exact hedged law without abort.** If the corrupt party neither modifies its shares nor
    stops, then for every test `D` the count of accepted released signatures over the uniform
    honest coin share and challenge equals `nChal` times the count of accepted single-signer
    signatures over a uniform hedge: the released law is the single-signer hedged law, whatever
    coin share the corrupt party committed to. -/
theorem active_threshold_sig_no_abort_exact_single_signer_law
    (p : Fips205Params) (hWf : p.wellFormed = true) {skSeed skPrf pkSeed : List UInt8}
    (run : SlhThresholdRun p skSeed skPrf pkSeed) {width nChal : Nat} {Dev : Type}
    (tags : ConsistencyTagScheme Dev nChal) (adv : ActiveSlhAdversary width nChal Dev)
    (encode : BitVec width → List UInt8) (msgPrime : List UInt8)
    (hNoAbort : ∀ h c, adv.aborts h c = false)
    (hNoDeviation : ∀ h, tags.isHonest (adv.deviation h) = true)
    (D : List UInt8 → Bool) :
    finSum (2 ^ width) (fun h => finSum nChal (fun c =>
      if (match activeMaliciousThresholdSign run tags adv encode msgPrime h c with
          | some s => D s
          | none => false) then 1 else 0)) =
    nChal * finSum (2 ^ width) (fun u =>
      if D (encodeSlhSig (slhSignInternal p msgPrime
        (slhKeygenInternal p skSeed skPrf pkSeed).1 (encode (BitVec.ofFin u)))) then 1 else 0) := by
  rw [← threshold_joint_coin_output_law p (slhKeygenInternal p skSeed skPrf pkSeed).1 msgPrime
        width encode adv.corruptCoin D,
      ← finSum_mul_left]
  apply finSum_congr
  intro h
  have hInner : ∀ c : Fin nChal,
      (if (match activeMaliciousThresholdSign run tags adv encode msgPrime h c with
           | some s => D s
           | none => false) then 1 else 0) =
      (if D (encodeSlhSig (slhSignInternal p msgPrime
        (slhKeygenInternal p skSeed skPrf pkSeed).1
        (encode (BitVec.ofFin h ^^^ adv.corruptCoin)))) then 1 else 0) := by
    intro c
    have hF : activeTagForgery tags adv h c = false := by
      unfold activeTagForgery
      rw [hNoDeviation]
      exact Bool.and_false _
    have hR : activeReleased tags adv h c = true := by
      unfold activeReleased
      rw [hNoAbort, hNoDeviation]
      rfl
    rw [(activeMaliciousThresholdSign_cases p hWf run tags adv encode msgPrime h c).1 hF, hR]
    rfl
  rw [finSum_congr hInner, finSum_const]

/-- The forgery term of `active_malicious_threshold_sig_abort_or_exact_hedged_dist` cannot be
    dropped: with a tag check that accepts one modified execution, the honest parties release
    the corrupt party's bytes in that run, for any key and any bytes. -/
theorem tooth_active_tag_forgery_releases_tampered_output
    {p : Fips205Params} {skSeed skPrf pkSeed : List UInt8}
    (run : SlhThresholdRun p skSeed skPrf pkSeed) (encode : BitVec 1 → List UInt8)
    (msgPrime bogus : List UInt8) :
    let tags : ConsistencyTagScheme Bool 2 :=
      { isHonest := fun d => !d
        accepts := fun d c => !d || c.val == 0
        complete := fun d c h => by cases d <;> simp_all }
    let adv : ActiveSlhAdversary 1 2 Bool :=
      { corruptCoin := 0#1
        deviation := fun _ => true
        tamperedOutput := fun _ _ => bogus
        aborts := fun _ _ => false }
    activeMaliciousThresholdSign run tags adv encode msgPrime
      ⟨0, by decide⟩ ⟨0, by decide⟩ = some bogus ∧
    activeMaliciousThresholdSign run tags adv encode msgPrime
      ⟨0, by decide⟩ ⟨1, by decide⟩ = none ∧
    finSum (2 ^ 1) (fun h => finSum 2 (fun c =>
      if activeTagForgery tags adv h c then 1 else 0)) = 2 := by
  exact ⟨rfl, rfl, rfl⟩

/-- The share view of the party outside quorum `q` (the corrupt party when `q` is honest). -/
def RssQuorum.outsiderView (q : RssQuorum) (sh : RssByteShares) : List UInt8 × List UInt8 :=
  match q with
  | .p01 => (sh.b2, sh.b0)
  | .p12 => (sh.b0, sh.b1)
  | .p20 => (sh.b1, sh.b2)

/-- **Abort leaks nothing beyond the corrupt party's own share view (2-of-3 RSS).** Let the
    corrupt strategy be any function of the corrupt party's views of the two key sharings.
    For two sharings, of possibly different keys, that give the corrupt party the same views,
    the honest quorum aborts on exactly the same `(honestCoin, challenge)` pairs. Sharings of
    different secrets with a common single-party view exist
    (`rss_single_view_does_not_determine_secret`). -/
theorem rss_active_abort_pattern_depends_only_on_corrupt_view
    (p : Fips205Params) (q : RssQuorum)
    {seed₁ prf₁ seed₂ prf₂ : RssByteShares}
    (hS₁ : seed₁.WellFormed) (hP₁ : prf₁.WellFormed) (hS₂ : seed₂.WellFormed) (hP₂ : prf₂.WellFormed)
    (hSeedView : q.outsiderView seed₁ = q.outsiderView seed₂)
    (hPrfView : q.outsiderView prf₁ = q.outsiderView prf₂)
    (pkSeed₁ pkSeed₂ : List UInt8) (tape₁ tape₂ : Nat → Nat → Nat → Nat → RssPrfZeroSeeds)
    {width nChal : Nat} {Dev : Type} (tags : ConsistencyTagScheme Dev nChal)
    (strategy : List UInt8 × List UInt8 → List UInt8 × List UInt8 → ActiveSlhAdversary width nChal Dev)
    (encode : BitVec width → List UInt8) (msg₁ msg₂ : List UInt8)
    (honestCoin : Fin (2 ^ width)) (chal : Fin nChal) :
    (activeMaliciousThresholdSign (SlhThresholdRun.ofRss p q hS₁ hP₁ pkSeed₁ tape₁) tags
      (strategy (q.outsiderView seed₁) (q.outsiderView prf₁)) encode msg₁ honestCoin chal).isSome =
    (activeMaliciousThresholdSign (SlhThresholdRun.ofRss p q hS₂ hP₂ pkSeed₂ tape₂) tags
      (strategy (q.outsiderView seed₂) (q.outsiderView prf₂)) encode msg₂ honestCoin chal).isSome := by
  rw [hSeedView, hPrfView]
  unfold activeMaliciousThresholdSign
  cases (strategy (q.outsiderView seed₂) (q.outsiderView prf₂)).aborts (BitVec.ofFin honestCoin) chal
  · cases tags.accepts
      ((strategy (q.outsiderView seed₂) (q.outsiderView prf₂)).deviation (BitVec.ofFin honestCoin)) chal
    · rfl
    · cases tags.isHonest
        ((strategy (q.outsiderView seed₂) (q.outsiderView prf₂)).deviation (BitVec.ofFin honestCoin)) <;> rfl
  · rfl


/-! ## Production HashSigs cut interface

The extra FORS coordinate is essential: flattening `(j,u)` into one legacy
coordinate changes the PRF domain. These routines consume only public data and
cut outputs; a secret key appears only in their refinement propositions.
-/
structure ProductionPqHashMpcOracles extends PqHashMpcOracles where
  evalIndexedForsReveal : UInt64 → Nat → Nat → Nat → List UInt8
  evalIndexedForsLeafHash : UInt64 → Nat → Nat → Nat → List UInt8

def ProductionPqHashMpcOracles.MatchesKey (o : ProductionPqHashMpcOracles)
    (suite : TweakableHashSuite) (sk : PqSecretKey) : Prop :=
  o.toPqHashMpcOracles.MatchesKey suite sk ∧
  (∀ tree kp j u, o.evalIndexedForsReveal tree kp j u = forsIndexedSecretLeaf suite sk tree kp j u) ∧
  (∀ tree kp j u, o.evalIndexedForsLeafHash tree kp j u = forsIndexedLeafFn suite sk tree kp j u)

def mpcComputeProductionForsPk (suite : TweakableHashSuite) (params : PqHashParams)
    (o : ProductionPqHashMpcOracles) (pkSeed : List UInt8) (tree0 : UInt64) (kp0 : Nat) : List UInt8 :=
  let kpU32 := UInt32.ofNat kp0
  let roots := (List.range params.forsTrees).map fun j =>
    computeMerkleNodeKp suite pkSeed 0 tree0 .forsTree kpU32
      (o.evalIndexedForsLeafHash tree0 kp0 j) params.forsHeight j 0
  thTweakTl suite pkSeed ⟨0, tree0, .forsRoots, kpU32, 0, 0⟩ roots

def mpcBuildProductionForsOpenings (suite : TweakableHashSuite) (params : PqHashParams)
    (o : ProductionPqHashMpcOracles) (pkSeed : List UInt8) (tree0 : UInt64) (kp0 : Nat) (idxs : List Nat) : List ForsTreeOpening :=
  let kpU32 := UInt32.ofNat kp0
  (List.range params.forsTrees).map fun j =>
    let idxJ := idxs.getD j 0
    { secretVal := o.evalIndexedForsReveal tree0 kp0 j idxJ
      authPath  := buildMerkleAuthPathKp suite pkSeed 0 tree0 .forsTree kpU32
                     (o.evalIndexedForsLeafHash tree0 kp0 j) params.forsHeight j 0 idxJ }

def mpcSignProductionHypertreeLayers (suite : TweakableHashSuite) (params : PqHashParams)
    (o : ProductionPqHashMpcOracles) (pkSeed : List UInt8) (pkRoot rRand : List UInt8) (maxGrind : Nat) :
    Nat → Nat → List UInt8 → Nat → Option (List LayerXmssSig)
  | _, _, _, 0 => some []
  | layerIdx, globalIdx, curRoot, rem + 1 =>
    let subLeaves := 2 ^ params.subtreeHeight
    let kpIdx := globalIdx % subLeaves
    let kpU32 := UInt32.ofNat kpIdx
    let treeIdxNat := globalIdx / subLeaves
    let treeIdx := UInt64.ofNat treeIdxNat
    let layerU32 := UInt32.ofNat layerIdx
    let grindRes :=
      if params.statefulJorts && decide (layerIdx = 0) then
        grindTswLeafCounterAux suite params.w params.ell1 params.targetSum
          rRand pkSeed pkRoot curRoot treeIdx kpU32 0 maxGrind
      else
        grindTswInternalCounterAux suite params.w params.ell1 params.targetSum
          pkSeed pkRoot curRoot layerU32 treeIdx kpU32 0 maxGrind
    match grindRes with
    | none => none
    | some (ctr, digits, _) =>
      let wotsChains := (List.range params.ell1).map fun r =>
        let dr := digits.getD r 0
        o.evalWotsChainEnd layerU32 treeIdx kpIdx r dr
      let authPath := buildMerkleAuthPathKp suite pkSeed layerU32 treeIdx .tree 0
        (mpcComputeWotsPk suite params o.toPqHashMpcOracles pkSeed layerU32 treeIdx) params.subtreeHeight 0 0 kpIdx
      let nextRoot := mpcComputeXmssSubtreeRoot suite params o.toPqHashMpcOracles pkSeed layerU32 treeIdx
      match mpcSignProductionHypertreeLayers suite params o pkSeed pkRoot rRand maxGrind (layerIdx + 1) treeIdxNat nextRoot rem with
      | none => none
      | some restSigs =>
        some ({ tswCtr := ctr, wotsChains := wotsChains, authPath := authPath } :: restSigs)

def mpcSignProductionHypertreeCore (suite : TweakableHashSuite) (params : PqHashParams)
    (o : ProductionPqHashMpcOracles) (pkSeed : List UInt8) (pk : PqPublicKey) (msg mu rRand : List UInt8)
    (leafGlobalIdx : Nat) (forsIdxs : Option (List Nat)) (maxGrind : Nat) : Option PqHashSig :=
  let subLeaves := 2 ^ params.subtreeHeight
  match (if params.statefulJorts then some ([], mu)
         else
           match forsIdxs with
           | none => none
           | some idxs =>
             let kp0 := leafGlobalIdx % subLeaves
             let tree0 := UInt64.ofNat (leafGlobalIdx / subLeaves)
             some (mpcBuildProductionForsOpenings suite params o pkSeed tree0 kp0 idxs,
                   mpcComputeProductionForsPk suite params o pkSeed tree0 kp0)) with
  | none => none
  | some (forsOpenings, curRoot) =>
    match mpcSignProductionHypertreeLayers suite params o pkSeed pk.pkRoot rRand maxGrind 0 leafGlobalIdx curRoot params.numLayers with
    | none => none
    | some layerSigs =>
      let sig : PqHashSig :=
        { rRand := rRand
          msgTswCtr := 0
          leafGlobalIdx := leafGlobalIdx
          forsOpenings := forsOpenings
          layerSigs := layerSigs }
      if verifyProductionPqHashSig suite params pk msg sig then some sig else none

def mpcEvalProductionStatelessSign (suite : TweakableHashSuite) (params : PqHashParams)
    (o : ProductionPqHashMpcOracles) (pkSeed : List UInt8) (msg optRand : List UInt8) (maxGrind : Nat) : Option PqHashSig :=
  if params.statefulJorts || !params.productionWellFormed then none
  else
    let pk := derivePublicKeyMpc suite params o.toPqHashMpcOracles pkSeed
    let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
    let rRand := o.evalPrfMsg optRand mu
    match deriveProductionStatelessInputs suite params rRand pk.pkSeed pk.pkRoot mu with
    | none => none
    | some (leafGlobalIdx, forsIdxs) =>
      mpcSignProductionHypertreeCore suite params o pkSeed pk msg mu rRand leafGlobalIdx (some forsIdxs) maxGrind

def mpcEvalProductionStatefulSign (suite : TweakableHashSuite) (params : PqHashParams)
    (o : ProductionPqHashMpcOracles) (pkSeed : List UInt8) (msg optRand : List UInt8) (epoch maxGrind : Nat) : Option PqHashSig :=
  if !params.statefulJorts || !params.productionWellFormed || !params.productionLeafIdxInRange epoch then none
  else
    let pk := derivePublicKeyMpc suite params o.toPqHashMpcOracles pkSeed
    let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
    let rRand := o.evalPrfMsg optRand mu
    mpcSignProductionHypertreeCore suite params o pkSeed pk msg mu rRand epoch none maxGrind

private theorem production_mpc_fors_refines
    (suite : TweakableHashSuite) (params : PqHashParams)
    (o : ProductionPqHashMpcOracles) (sk : PqSecretKey)
    (hm : o.MatchesKey suite sk) (tree : UInt64) (kp : Nat) (idxs : List Nat) :
    mpcComputeProductionForsPk suite params o sk.pkSeed tree kp =
      computeProductionForsPk suite params sk tree kp ∧
    mpcBuildProductionForsOpenings suite params o sk.pkSeed tree kp idxs =
      buildProductionForsOpenings suite params sk tree kp idxs := by
  have hl : o.evalIndexedForsLeafHash tree kp = forsIndexedLeafFn suite sk tree kp :=
    funext fun j => funext fun u => hm.2.2 tree kp j u
  have hs : o.evalIndexedForsReveal tree kp = forsIndexedSecretLeaf suite sk tree kp :=
    funext fun j => funext fun u => hm.2.1 tree kp j u
  constructor
  · simp only [mpcComputeProductionForsPk, computeProductionForsPk, hl]
  · simp only [mpcBuildProductionForsOpenings, buildProductionForsOpenings, hl, hs]

private theorem production_mpc_layers_refines
    (suite : TweakableHashSuite) (params : PqHashParams)
    (o : ProductionPqHashMpcOracles) (sk : PqSecretKey)
    (hm : o.MatchesKey suite sk) (pkRoot rRand : List UInt8) (maxGrind : Nat) :
    ∀ rem layer idx root,
    mpcSignProductionHypertreeLayers suite params o sk.pkSeed pkRoot rRand maxGrind layer idx root rem =
      signProductionHypertreeLayers suite params sk pkRoot rRand maxGrind layer idx root rem := by
  intro rem
  induction rem with
  | zero => intros; rfl
  | succ rem ih =>
    intro layer idx root
    have hw : mpcComputeWotsPk suite params o.toPqHashMpcOracles sk.pkSeed =
        computeWotsPk suite params sk :=
      funext fun l => funext fun t => funext fun k =>
        mpcComputeWotsPk_eq suite params o.toPqHashMpcOracles sk hm.1 l t k
    simp only [mpcSignProductionHypertreeLayers, signProductionHypertreeLayers,
      hm.1.2.1, hw, mpcComputeXmssSubtreeRoot_eq suite params o.toPqHashMpcOracles sk hm.1, ih]
    rfl

private theorem production_mpc_core_refines
    (suite : TweakableHashSuite) (params : PqHashParams)
    (o : ProductionPqHashMpcOracles) (sk : PqSecretKey)
    (hm : o.MatchesKey suite sk) (pk : PqPublicKey) (msg mu rRand : List UInt8)
    (leaf : Nat) (idxs : Option (List Nat)) (maxGrind : Nat) :
    mpcSignProductionHypertreeCore suite params o sk.pkSeed pk msg mu rRand leaf idxs maxGrind =
      signProductionHypertreeCore suite params sk pk msg mu rRand leaf idxs maxGrind := by
  have hf := production_mpc_fors_refines suite params o sk hm
  simp only [mpcSignProductionHypertreeCore, signProductionHypertreeCore,
    (fun tree kp => (hf tree kp []).1), (hf _ _ _).2, production_mpc_layers_refines suite params o sk hm]
  rfl

theorem thresholdProductionStatelessSign_eq_evalProductionStatelessSign
    (suite : TweakableHashSuite) (params : PqHashParams)
    (o : ProductionPqHashMpcOracles) (sk : PqSecretKey)
    (hm : o.MatchesKey suite sk) (msg optRand : List UInt8) (maxGrind : Nat) :
    mpcEvalProductionStatelessSign suite params o sk.pkSeed msg optRand maxGrind =
      evalProductionStatelessSign suite params sk msg optRand maxGrind := by
  have hp : derivePublicKeyMpc suite params o.toPqHashMpcOracles sk.pkSeed =
      derivePublicKey suite params sk := by
    unfold derivePublicKeyMpc
    dsimp only
    rw [mpcComputeXmssSubtreeRoot_eq suite params o.toPqHashMpcOracles sk hm.1]
    rfl
  simp only [mpcEvalProductionStatelessSign, evalProductionStatelessSign, hp, hm.1.1,
    production_mpc_core_refines suite params o sk hm]
  rfl

theorem thresholdProductionStatefulSign_eq_evalProductionStatefulSign
    (suite : TweakableHashSuite) (params : PqHashParams)
    (o : ProductionPqHashMpcOracles) (sk : PqSecretKey)
    (hm : o.MatchesKey suite sk) (msg optRand : List UInt8) (epoch maxGrind : Nat) :
    mpcEvalProductionStatefulSign suite params o sk.pkSeed msg optRand epoch maxGrind =
      evalProductionStatefulSign suite params sk msg optRand epoch maxGrind := by
  have hp : derivePublicKeyMpc suite params o.toPqHashMpcOracles sk.pkSeed =
      derivePublicKey suite params sk := by
    unfold derivePublicKeyMpc
    dsimp only
    rw [mpcComputeXmssSubtreeRoot_eq suite params o.toPqHashMpcOracles sk hm.1]
    rfl
  simp only [mpcEvalProductionStatefulSign, evalProductionStatefulSign, hp, hm.1.1,
    production_mpc_core_refines suite params o sk hm]


/-- RSS implementation of the production FORS addresses. Only cut outputs are reconstructed. -/
def mkRssProductionPqHashMpcOracles (skSeedSh skPrfSh : RssByteShares)
    (pkSeed : List UInt8) (tape : Nat → Nat → Nat → Nat → RssPrfZeroSeeds) :
    ProductionPqHashMpcOracles where
  toPqHashMpcOracles := mkRssCshakePqHashMpcOracles skSeedSh skPrfSh pkSeed tape
  evalIndexedForsReveal tree0 kp0 j u :=
    let adrs : HashAdrs := ⟨0, tree0, .forsPrf, UInt32.ofNat kp0, UInt32.ofNat j, UInt32.ofNat u⟩
    let secSh := mpcCshake256SharedRss 32 pqCshakeSuiteCustom
                   (rssFrameSingleSecretCall tagPrf pkSeed adrs skSeedSh) (tape 0)
    reconstructRssBytes secSh
  evalIndexedForsLeafHash tree0 kp0 j u :=
    let prfAdrs : HashAdrs := ⟨0, tree0, .forsPrf, UInt32.ofNat kp0, UInt32.ofNat j, UInt32.ofNat u⟩
    let secSh := mpcCshake256SharedRss 32 pqCshakeSuiteCustom
                   (rssFrameSingleSecretCall tagPrf pkSeed prfAdrs skSeedSh) (tape 0)
    let treeAdrs : HashAdrs := ⟨0, tree0, .forsTree, UInt32.ofNat kp0, UInt32.ofNat j, UInt32.ofNat u⟩
    let hashSh := mpcCshake256SharedRss 32 pqCshakeSuiteCustom
                    (rssFrameSingleSecretCall tagThF pkSeed treeAdrs secSh) (tape 1)
    reconstructRssBytes hashSh

set_option maxHeartbeats 800000 in
 theorem mkRssProductionPqHashMpcOracles_matchesKey
    {skSeedSh skPrfSh : RssByteShares} (hSeedWf : skSeedSh.WellFormed) (hPrfWf : skPrfSh.WellFormed)
    (pkSeed : List UInt8) (tape : Nat → Nat → Nat → Nat → RssPrfZeroSeeds) :
    (mkRssProductionPqHashMpcOracles skSeedSh skPrfSh pkSeed tape).MatchesKey cshake256Suite
      ⟨reconstructRssBytes skSeedSh, reconstructRssBytes skPrfSh, pkSeed⟩ := by
  refine ⟨mkRssCshakePqHashMpcOracles_matchesKey hSeedWf hPrfWf pkSeed tape, ?_, ?_⟩
  · intro tree0 kp0 j u
    dsimp only [mkRssProductionPqHashMpcOracles]
    obtain ⟨hFWf, hFRec⟩ := reconstructRssBytes_rssFrameSingleSecretCall tagPrf pkSeed _ hSeedWf
    rw [(reconstructRssBytes_mpcCshake256SharedRss 32 pqCshakeSuiteCustom hFWf (tape 0)).2,
        hFRec]
    rfl
  · intro tree0 kp0 j u
    dsimp only [mkRssProductionPqHashMpcOracles]
    obtain ⟨hF1Wf, hF1Rec⟩ := reconstructRssBytes_rssFrameSingleSecretCall tagPrf pkSeed _ hSeedWf
    obtain ⟨hSecWf, hSecRec⟩ := reconstructRssBytes_mpcCshake256SharedRss 32 pqCshakeSuiteCustom hF1Wf (tape 0)
    obtain ⟨hF2Wf, hF2Rec⟩ := reconstructRssBytes_rssFrameSingleSecretCall tagThF pkSeed _ hSecWf
    rw [(reconstructRssBytes_mpcCshake256SharedRss 32 pqCshakeSuiteCustom hF2Wf (tape 1)).2,
        hF2Rec, hSecRec, hF1Rec]
    rfl

theorem rss_production_stateless_sign_refines
    (params : PqHashParams) {seed prf : RssByteShares}
    (hs : seed.WellFormed) (hp : prf.WellFormed)
    (pkSeed msg rand : List UInt8) (maxGrind : Nat)
    (tape : Nat → Nat → Nat → Nat → RssPrfZeroSeeds) :
    mpcEvalProductionStatelessSign cshake256Suite params
      (mkRssProductionPqHashMpcOracles seed prf pkSeed tape) pkSeed msg rand maxGrind =
      evalProductionStatelessSign cshake256Suite params
        ⟨reconstructRssBytes seed, reconstructRssBytes prf, pkSeed⟩ msg rand maxGrind :=
  thresholdProductionStatelessSign_eq_evalProductionStatelessSign _ _ _ _
    (mkRssProductionPqHashMpcOracles_matchesKey hs hp pkSeed tape) _ _ _

/-! ### Authenticated Shamir wires and local MAC propagation -/

/-- A Shamir wire with additive extension-field MAC shares. -/
structure AuthShamirWire where
  shares : List Goldilocks
  macs : List GoldilocksExt2
  deriving DecidableEq, Repr

/-- Authentication refers only to the wire's actual shares and the global key. -/
def AuthShamirWire.Valid (ls : List Goldilocks) (keys : List GoldilocksExt2)
    (w : AuthShamirWire) : Prop :=
  w.shares.length = ls.length ∧ w.macs.length = keys.length ∧
  ringListSum w.macs = CommRingOps.mul (ringListSum keys)
    (GoldilocksExt2.ofBase (lagrangeCombine ls w.shares))

def AuthShamirWire.add (x y : AuthShamirWire) : AuthShamirWire :=
  ⟨ringListZipAdd x.shares y.shares, ringListZipAdd x.macs y.macs⟩

def AuthShamirWire.scale (c : Goldilocks) (x : AuthShamirWire) : AuthShamirWire :=
  ⟨shareScale c x.shares, shareScale (GoldilocksExt2.ofBase c) x.macs⟩

/-- Public offsets use the party's key share, not a reconstructed key. -/
def AuthShamirWire.addPublic (keys : List GoldilocksExt2)
    (c : Goldilocks) (x : AuthShamirWire) : AuthShamirWire :=
  ⟨shareAddConst c x.shares,
    ringListZipAdd (shareScale (GoldilocksExt2.ofBase c) keys) x.macs⟩

theorem AuthShamirWire.Valid.add {ls keys x y}
    (hx : AuthShamirWire.Valid ls keys x) (hy : AuthShamirWire.Valid ls keys y) :
    AuthShamirWire.Valid ls keys (x.add y) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (ringListZipAdd_length_of_eq (hx.1.trans hy.1.symm)).trans hx.1
  · exact (ringListZipAdd_length_of_eq (hx.2.1.trans hy.2.1.symm)).trans hx.2.1
  · change ringListSum (ringListZipAdd x.macs y.macs) = _
    rw [ringListSum_zipAdd, hx.2.2, hy.2.2]
    change _ = CommRingOps.mul _ (GoldilocksExt2.ofBase (ringDot ls (ringListZipAdd x.shares y.shares)))
    rw [ringDot_zipAdd (hx.1.trans hy.1.symm), GoldilocksExt2.ofBase_add,
      LawfulCommRing.left_distrib]
    rfl

theorem AuthShamirWire.Valid.scale {ls keys x} (c : Goldilocks)
    (hx : AuthShamirWire.Valid ls keys x) :
    AuthShamirWire.Valid ls keys (x.scale c) := by
  refine ⟨by simpa [AuthShamirWire.scale] using hx.1,
    by simpa [AuthShamirWire.scale] using hx.2.1, ?_⟩
  change ringListSum (shareScale (GoldilocksExt2.ofBase c) x.macs) =
    CommRingOps.mul _ (GoldilocksExt2.ofBase (ringDot ls (shareScale c x.shares)))
  rw [ringListSum_scale, hx.2.2, ringDot_scale, GoldilocksExt2.ofBase_mul,
    ← LawfulCommRing.mul_assoc, ← LawfulCommRing.mul_assoc,
    LawfulCommRing.mul_comm (GoldilocksExt2.ofBase c) (ringListSum keys)]
  rfl

theorem AuthShamirWire.Valid.addPublic {ls keys x} (c : Goldilocks)
    (hOne : ringListSum ls = Goldilocks.one) (hx : AuthShamirWire.Valid ls keys x) :
    AuthShamirWire.Valid ls keys (x.addPublic keys c) := by
  refine ⟨by simpa [AuthShamirWire.addPublic] using hx.1, ?_, ?_⟩
  · change (ringListZipAdd (shareScale _ keys) x.macs).length = keys.length
    rw [ringListZipAdd_length_of_eq (by simpa using hx.2.1.symm), shareScale_length]
  · change ringListSum (ringListZipAdd (shareScale _ keys) x.macs) =
      CommRingOps.mul _ (GoldilocksExt2.ofBase (ringDot ls (shareAddConst c x.shares)))
    have hOneMul : CommRingOps.mul Goldilocks.one c = c := LawfulCommRing.one_mul c
    rw [ringListSum_zipAdd, ringListSum_scale, hx.2.2,
      ringDot_addConst c (Nat.le_of_eq hx.1.symm), hOne,
      hOneMul,
      GoldilocksExt2.ofBase_add, LawfulCommRing.left_distrib,
      LawfulCommRing.mul_comm (GoldilocksExt2.ofBase c) (ringListSum keys)]
    rfl

/-- Each of the seven preprocessed powers carries its own additive MAC shares. -/
structure AuthSharedPow7Tuple where
  r : AuthShamirWire
  r2 : AuthShamirWire
  r3 : AuthShamirWire
  r4 : AuthShamirWire
  r5 : AuthShamirWire
  r6 : AuthShamirWire
  r7 : AuthShamirWire
  deriving DecidableEq, Repr

def AuthSharedPow7Tuple.toTuple (t : AuthSharedPow7Tuple) : SharedPow7Tuple :=
  ⟨t.r.shares, t.r2.shares, t.r3.shares, t.r4.shares,
   t.r5.shares, t.r6.shares, t.r7.shares⟩

def AuthSharedPow7Tuple.Valid (ls : List Goldilocks) (keys : List GoldilocksExt2)
    (t : AuthSharedPow7Tuple) : Prop :=
  t.toTuple.validAt ls ∧ t.r.Valid ls keys ∧ t.r2.Valid ls keys ∧
  t.r3.Valid ls keys ∧ t.r4.Valid ls keys ∧ t.r5.Valid ls keys ∧
  t.r6.Valid ls keys ∧ t.r7.Valid ls keys

/-- The same binomial linear combination as `mpcPow7Shares`, including all seven MACs. -/
def authPow7Output (keys : List GoldilocksExt2) (d : Goldilocks)
    (t : AuthSharedPow7Tuple) : AuthShamirWire :=
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
  (((t.r.scale c1).addPublic keys d7).add ((t.r2.scale c2).add (t.r3.scale c3))).add
    (((t.r4.scale c4).add (t.r5.scale c5)).add ((t.r6.scale c6).add t.r7))

theorem authPow7Output_shares (keys d t) :
    (authPow7Output keys d t).shares = mpcPow7Shares d t.toTuple := by
  simp only [authPow7Output, mpcPow7Shares, AuthSharedPow7Tuple.toTuple,
    AuthShamirWire.add, AuthShamirWire.scale, AuthShamirWire.addPublic]

/-- MAC propagation holds for every opened value, even before its MAC check is considered. -/
theorem authPow7Output_valid {ls keys t} (d : Goldilocks)
    (hOne : ringListSum ls = Goldilocks.one) (ht : AuthSharedPow7Tuple.Valid ls keys t) :
    (authPow7Output keys d t).Valid ls keys := by
  obtain ⟨_, h1, h2, h3, h4, h5, h6, h7⟩ := ht
  exact ((h1.scale _).addPublic _ hOne |>.add ((h2.scale _).add (h3.scale _))).add
    (((h4.scale _).add (h5.scale _)).add ((h6.scale _).add h7))

/-- Active opening and MAC check followed by party-local propagation of all output MACs. -/
def execAuthShamirPow7 (ls : List Goldilocks) (keys masks : List GoldilocksExt2)
    (x : AuthShamirWire) (t : AuthSharedPow7Tuple)
    (delta : Goldilocks) (devs : List GoldilocksExt2) : Option AuthShamirWire :=
  let d := Goldilocks.add (lagrangeCombine ls (shareZipSub x.shares t.r.shares)) delta
  (execActiveSharedPow7Round ls x.shares t.toTuple x.macs t.r.macs keys masks delta devs).map
    (fun ys => ⟨ys, (authPow7Output keys d t).macs⟩)

/-- The active gate's returned shares are the binomial expression at its actual opening. -/
private theorem execActiveSharedPow7Round_output {ls xs t mx mr keys masks delta devs ys}
    (h : execActiveSharedPow7Round ls xs t mx mr keys masks delta devs = some ys) :
    ys = mpcPow7Shares (Goldilocks.add (lagrangeCombine ls (shareZipSub xs t.rSh)) delta) t := by
  unfold execActiveSharedPow7Round evalSharedPow7Binomial at h
  dsimp only at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

theorem execAuthShamirPow7_sound_or_pins_key {ls keys masks x t delta devs out}
    (hOne : ringListSum ls = Goldilocks.one)
    (hx : AuthShamirWire.Valid ls keys x) (ht : AuthSharedPow7Tuple.Valid ls keys t)
    (hm : masks.length = keys.length) (hz : ringListSum masks = CommRingOps.zero)
    (h : execAuthShamirPow7 ls keys masks x t delta devs = some out) :
    out.Valid ls keys ∧
    ((delta = Goldilocks.zero ∧ lagrangeCombine ls out.shares = sbox7 (lagrangeCombine ls x.shares)) ∨
     (delta ≠ Goldilocks.zero ∧ ringListSum keys =
       CommRingOps.mul (ringListSum devs) (GoldilocksExt2.inv (GoldilocksExt2.ofBase delta)))) := by
  unfold execAuthShamirPow7 at h
  cases he : execActiveSharedPow7Round ls x.shares t.toTuple x.macs t.r.macs keys masks delta devs with
  | none => simp only [he, Option.map_none] at h; cases h
  | some ys =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst out
    have hy := execActiveSharedPow7Round_output he
    have hv := authPow7Output_valid
      (Goldilocks.add (lagrangeCombine ls (shareZipSub x.shares t.r.shares)) delta) hOne ht
    refine ⟨?_, ?_⟩
    · rw [hy]
      exact hv
    · obtain hok | hpin := execActiveSharedPow7Round_sound_or_pins_key
        ls x.shares t.toTuple x.macs t.r.macs keys masks delta devs ys
        hOne hx.1 ht.1 hx.2.1 ht.2.1.2.1 hm hx.2.2 ht.2.1.2.2 hz he
      · exact .inl ⟨hok.1, hok.2.2⟩
      · exact .inr hpin


/-- Four authenticated Shamir wires, stored by lane. -/
structure AuthShamirLane4 where
  x0 : AuthShamirWire
  x1 : AuthShamirWire
  x2 : AuthShamirWire
  x3 : AuthShamirWire

/-- A width-12 authenticated state. Transposing its wire shares gives the party states. -/
structure AuthShamirState12 where
  b0 : AuthShamirLane4
  b1 : AuthShamirLane4
  b2 : AuthShamirLane4

def AuthShamirWire.value (ls : List Goldilocks) (x : AuthShamirWire) : Goldilocks :=
  lagrangeCombine ls x.shares

theorem AuthShamirWire.value_add {ls keys x y}
    (hx : AuthShamirWire.Valid ls keys x) (hy : AuthShamirWire.Valid ls keys y) :
    (x.add y).value ls = Goldilocks.add (x.value ls) (y.value ls) := by
  exact ringDot_zipAdd (hx.1.trans hy.1.symm)

theorem AuthShamirWire.value_scale (ls c x) :
    (AuthShamirWire.scale c x).value ls = Goldilocks.mul c (x.value ls) := by
  exact ringDot_scale c ls x.shares

theorem AuthShamirWire.value_addPublic {ls keys x} (c : Goldilocks)
    (hOne : ringListSum ls = Goldilocks.one) (hx : AuthShamirWire.Valid ls keys x) :
    (x.addPublic keys c).value ls = Goldilocks.add c (x.value ls) := by
  change ringDot ls (shareAddConst c x.shares) = _
  have hOneMul : CommRingOps.mul Goldilocks.one c = c := LawfulCommRing.one_mul c
  rw [ringDot_addConst c (Nat.le_of_eq hx.1.symm), hOne, hOneMul]
  rfl

def AuthShamirLane4.Valid (ls : List Goldilocks) (keys : List GoldilocksExt2)
    (s : AuthShamirLane4) : Prop :=
  s.x0.Valid ls keys ∧ s.x1.Valid ls keys ∧ s.x2.Valid ls keys ∧ s.x3.Valid ls keys

def AuthShamirLane4.value (ls : List Goldilocks) (s : AuthShamirLane4) : Lane4 :=
  ⟨s.x0.value ls, s.x1.value ls, s.x2.value ls, s.x3.value ls⟩

def AuthShamirLane4.shares (s : AuthShamirLane4) : List Lane4 :=
  zipLane4Shares s.x0.shares s.x1.shares s.x2.shares s.x3.shares

def AuthShamirLane4.add (a b : AuthShamirLane4) : AuthShamirLane4 :=
  ⟨a.x0.add b.x0, a.x1.add b.x1, a.x2.add b.x2, a.x3.add b.x3⟩

def AuthShamirLane4.sum (a : AuthShamirLane4) : AuthShamirWire :=
  (a.x0.add a.x1).add (a.x2.add a.x3)

def AuthShamirLane4.applyM4 (a : AuthShamirLane4) : AuthShamirLane4 :=
  let s := a.sum
  ⟨s.add (a.x0.add (a.x1.scale (Goldilocks.ofNat 2))),
   s.add (a.x1.add (a.x2.scale (Goldilocks.ofNat 2))),
   s.add (a.x2.add (a.x3.scale (Goldilocks.ofNat 2))),
   s.add (a.x3.add (a.x0.scale (Goldilocks.ofNat 2)))⟩

theorem AuthShamirLane4.Valid.add {ls keys a b}
    (ha : AuthShamirLane4.Valid ls keys a) (hb : AuthShamirLane4.Valid ls keys b) :
    (a.add b).Valid ls keys :=
  ⟨ha.1.add hb.1, ha.2.1.add hb.2.1, ha.2.2.1.add hb.2.2.1, ha.2.2.2.add hb.2.2.2⟩

theorem AuthShamirLane4.Valid.sum {ls keys a} (ha : AuthShamirLane4.Valid ls keys a) :
    a.sum.Valid ls keys :=
  (ha.1.add ha.2.1).add (ha.2.2.1.add ha.2.2.2)

theorem AuthShamirLane4.Valid.applyM4 {ls keys a} (ha : AuthShamirLane4.Valid ls keys a) :
    a.applyM4.Valid ls keys :=
  ⟨ha.sum.add (ha.1.add (ha.2.1.scale _)), ha.sum.add (ha.2.1.add (ha.2.2.1.scale _)),
   ha.sum.add (ha.2.2.1.add (ha.2.2.2.scale _)), ha.sum.add (ha.2.2.2.add (ha.1.scale _))⟩

theorem AuthShamirLane4.value_add {ls keys a b}
    (ha : AuthShamirLane4.Valid ls keys a) (hb : AuthShamirLane4.Valid ls keys b) :
    (a.add b).value ls = lane4Add (a.value ls) (b.value ls) := by
  exact Lane4.ext (AuthShamirWire.value_add ha.1 hb.1)
    (AuthShamirWire.value_add ha.2.1 hb.2.1)
    (AuthShamirWire.value_add ha.2.2.1 hb.2.2.1)
    (AuthShamirWire.value_add ha.2.2.2 hb.2.2.2)

theorem AuthShamirLane4.value_sum {ls keys a} (ha : AuthShamirLane4.Valid ls keys a) :
    a.sum.value ls = lane4Sum (a.value ls) := by
  simp only [AuthShamirLane4.sum,
    AuthShamirWire.value_add (ha.1.add ha.2.1) (ha.2.2.1.add ha.2.2.2),
    AuthShamirWire.value_add ha.1 ha.2.1, AuthShamirWire.value_add ha.2.2.1 ha.2.2.2]
  rfl

theorem AuthShamirLane4.value_applyM4 {ls keys a} (ha : AuthShamirLane4.Valid ls keys a) :
    a.applyM4.value ls = Qsag.applyM4 (a.value ls) := by
  apply Lane4.ext
  · change (a.sum.add (a.x0.add (a.x1.scale _))).value ls = _
    rw [AuthShamirWire.value_add ha.sum (ha.1.add (ha.2.1.scale _)),
      AuthShamirWire.value_add ha.1 (ha.2.1.scale _),
      AuthShamirWire.value_scale, AuthShamirLane4.value_sum ha]
    rfl
  · change (a.sum.add (a.x1.add (a.x2.scale _))).value ls = _
    rw [AuthShamirWire.value_add ha.sum (ha.2.1.add (ha.2.2.1.scale _)),
      AuthShamirWire.value_add ha.2.1 (ha.2.2.1.scale _),
      AuthShamirWire.value_scale, AuthShamirLane4.value_sum ha]
    rfl
  · change (a.sum.add (a.x2.add (a.x3.scale _))).value ls = _
    rw [AuthShamirWire.value_add ha.sum (ha.2.2.1.add (ha.2.2.2.scale _)),
      AuthShamirWire.value_add ha.2.2.1 (ha.2.2.2.scale _),
      AuthShamirWire.value_scale, AuthShamirLane4.value_sum ha]
    rfl
  · change (a.sum.add (a.x3.add (a.x0.scale _))).value ls = _
    rw [AuthShamirWire.value_add ha.sum (ha.2.2.2.add (ha.1.scale _)),
      AuthShamirWire.value_add ha.2.2.2 (ha.1.scale _),
      AuthShamirWire.value_scale, AuthShamirLane4.value_sum ha]
    rfl

def AuthShamirState12.Valid (ls : List Goldilocks) (keys : List GoldilocksExt2)
    (s : AuthShamirState12) : Prop :=
  s.b0.Valid ls keys ∧ s.b1.Valid ls keys ∧ s.b2.Valid ls keys

def AuthShamirState12.value (ls : List Goldilocks) (s : AuthShamirState12) : Poseidon2State12 :=
  ⟨s.b0.value ls, s.b1.value ls, s.b2.value ls⟩

def AuthShamirState12.shares (s : AuthShamirState12) : List Poseidon2State12 :=
  zipState12Shares s.b0.shares s.b1.shares s.b2.shares

theorem AuthShamirLane4.shares_length {ls keys s} (hs : AuthShamirLane4.Valid ls keys s) :
    s.shares.length = ls.length :=
  zipLane4Shares_length hs.1.1 hs.2.1.1 hs.2.2.1.1 hs.2.2.2.1

theorem AuthShamirState12.shares_length {ls keys s} (hs : AuthShamirState12.Valid ls keys s) :
    s.shares.length = ls.length :=
  zipState12Shares_length (AuthShamirLane4.shares_length hs.1)
    (AuthShamirLane4.shares_length hs.2.1) (AuthShamirLane4.shares_length hs.2.2)

theorem AuthShamirState12.combine_shares {ls keys s} (hs : AuthShamirState12.Valid ls keys s) :
    lagrangeCombineState12 ls s.shares = s.value ls := by
  rw [AuthShamirState12.shares, lagrangeCombineState12_zip ls _ _ _
    (AuthShamirLane4.shares_length hs.1) (AuthShamirLane4.shares_length hs.2.1)
    (AuthShamirLane4.shares_length hs.2.2)]
  apply Poseidon2State12.ext
  · exact lagrangeCombineLane4_zip ls _ _ _ _ hs.1.1.1 hs.1.2.1.1 hs.1.2.2.1.1 hs.1.2.2.2.1
  · exact lagrangeCombineLane4_zip ls _ _ _ _ hs.2.1.1.1 hs.2.1.2.1.1 hs.2.1.2.2.1.1 hs.2.1.2.2.2.1
  · exact lagrangeCombineLane4_zip ls _ _ _ _ hs.2.2.1.1 hs.2.2.2.1.1 hs.2.2.2.2.1.1 hs.2.2.2.2.2.1

def AuthShamirState12.applyME (s : AuthShamirState12) : AuthShamirState12 :=
  let y0 := s.b0.applyM4
  let y1 := s.b1.applyM4
  let y2 := s.b2.applyM4
  let total := (y0.add y1).add y2
  ⟨y0.add total, y1.add total, y2.add total⟩

theorem AuthShamirState12.Valid.applyME {ls keys s} (hs : AuthShamirState12.Valid ls keys s) :
    s.applyME.Valid ls keys := by
  have h0 := hs.1.applyM4
  have h1 := hs.2.1.applyM4
  have h2 := hs.2.2.applyM4
  have ht := (h0.add h1).add h2
  exact ⟨h0.add ht, h1.add ht, h2.add ht⟩

theorem AuthShamirState12.value_applyME {ls keys s} (hs : AuthShamirState12.Valid ls keys s) :
    s.applyME.value ls = Qsag.applyME (s.value ls) := by
  have h0 := hs.1.applyM4
  have h1 := hs.2.1.applyM4
  have h2 := hs.2.2.applyM4
  have ht := (h0.add h1).add h2
  simp only [AuthShamirState12.applyME, AuthShamirState12.value,
    AuthShamirLane4.value_add h0 ht, AuthShamirLane4.value_add h1 ht,
    AuthShamirLane4.value_add h2 ht, AuthShamirLane4.value_add (h0.add h1) h2,
    AuthShamirLane4.value_add h0 h1, AuthShamirLane4.value_applyM4 hs.1,
    AuthShamirLane4.value_applyM4 hs.2.1, AuthShamirLane4.value_applyM4 hs.2.2, Qsag.applyME]

def AuthShamirState12.sum (s : AuthShamirState12) : AuthShamirWire :=
  (s.b0.sum.add s.b1.sum).add s.b2.sum

def AuthShamirState12.applyMI (s : AuthShamirState12) : AuthShamirState12 :=
  let total := s.sum
  ⟨⟨(s.b0.x0.scale (goldOfInt (-2))).add total, s.b0.x1.add total, (s.b0.x2.scale (goldOfInt (2))).add total, (s.b0.x3.scale (goldOfInt (4))).add total⟩,
   ⟨(s.b1.x0.scale (goldOfInt (8))).add total, (s.b1.x1.scale (goldOfInt (16))).add total, (s.b1.x2.scale (goldOfInt (32))).add total, (s.b1.x3.scale (goldOfInt (64))).add total⟩,
   ⟨(s.b2.x0.scale (goldOfInt (128))).add total, (s.b2.x1.scale (goldOfInt (256))).add total, (s.b2.x2.scale (goldOfInt (512))).add total, (s.b2.x3.scale (goldOfInt (1024))).add total⟩⟩

theorem AuthShamirState12.Valid.sum {ls keys s} (hs : AuthShamirState12.Valid ls keys s) :
    s.sum.Valid ls keys := (hs.1.sum.add hs.2.1.sum).add hs.2.2.sum

theorem AuthShamirState12.Valid.applyMI {ls keys s} (hs : AuthShamirState12.Valid ls keys s) :
    s.applyMI.Valid ls keys := by
  have ht := hs.sum
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · exact (hs.1.1.scale _).add ht
  · exact hs.1.2.1.add ht
  · exact (hs.1.2.2.1.scale _).add ht
  · exact (hs.1.2.2.2.scale _).add ht
  · exact (hs.2.1.1.scale _).add ht
  · exact (hs.2.1.2.1.scale _).add ht
  · exact (hs.2.1.2.2.1.scale _).add ht
  · exact (hs.2.1.2.2.2.scale _).add ht
  · exact (hs.2.2.1.scale _).add ht
  · exact (hs.2.2.2.1.scale _).add ht
  · exact (hs.2.2.2.2.1.scale _).add ht
  · exact (hs.2.2.2.2.2.scale _).add ht

theorem AuthShamirState12.value_sum {ls keys s} (hs : AuthShamirState12.Valid ls keys s) :
    s.sum.value ls = state12Sum (s.value ls) := by
  simp only [AuthShamirState12.sum,
    AuthShamirWire.value_add (hs.1.sum.add hs.2.1.sum) hs.2.2.sum,
    AuthShamirWire.value_add hs.1.sum hs.2.1.sum,
    AuthShamirLane4.value_sum hs.1, AuthShamirLane4.value_sum hs.2.1,
    AuthShamirLane4.value_sum hs.2.2]
  rfl

theorem AuthShamirState12.value_applyMI {ls keys s} (hs : AuthShamirState12.Valid ls keys s) :
    s.applyMI.value ls = Qsag.applyMI (s.value ls) := by
  apply Poseidon2State12.ext <;> apply Lane4.ext
  · change ((s.b0.x0.scale (goldOfInt (-2))).add s.sum).value ls = _
    rw [AuthShamirWire.value_add (hs.1.1.scale _) hs.sum, AuthShamirWire.value_scale, AuthShamirState12.value_sum hs]
    rfl
  · change (s.b0.x1.add s.sum).value ls = _
    rw [AuthShamirWire.value_add hs.1.2.1 hs.sum, AuthShamirState12.value_sum hs]
    rfl
  · change ((s.b0.x2.scale (goldOfInt (2))).add s.sum).value ls = _
    rw [AuthShamirWire.value_add (hs.1.2.2.1.scale _) hs.sum, AuthShamirWire.value_scale, AuthShamirState12.value_sum hs]
    rfl
  · change ((s.b0.x3.scale (goldOfInt (4))).add s.sum).value ls = _
    rw [AuthShamirWire.value_add (hs.1.2.2.2.scale _) hs.sum, AuthShamirWire.value_scale, AuthShamirState12.value_sum hs]
    rfl
  · change ((s.b1.x0.scale (goldOfInt (8))).add s.sum).value ls = _
    rw [AuthShamirWire.value_add (hs.2.1.1.scale _) hs.sum, AuthShamirWire.value_scale, AuthShamirState12.value_sum hs]
    rfl
  · change ((s.b1.x1.scale (goldOfInt (16))).add s.sum).value ls = _
    rw [AuthShamirWire.value_add (hs.2.1.2.1.scale _) hs.sum, AuthShamirWire.value_scale, AuthShamirState12.value_sum hs]
    rfl
  · change ((s.b1.x2.scale (goldOfInt (32))).add s.sum).value ls = _
    rw [AuthShamirWire.value_add (hs.2.1.2.2.1.scale _) hs.sum, AuthShamirWire.value_scale, AuthShamirState12.value_sum hs]
    rfl
  · change ((s.b1.x3.scale (goldOfInt (64))).add s.sum).value ls = _
    rw [AuthShamirWire.value_add (hs.2.1.2.2.2.scale _) hs.sum, AuthShamirWire.value_scale, AuthShamirState12.value_sum hs]
    rfl
  · change ((s.b2.x0.scale (goldOfInt (128))).add s.sum).value ls = _
    rw [AuthShamirWire.value_add (hs.2.2.1.scale _) hs.sum, AuthShamirWire.value_scale, AuthShamirState12.value_sum hs]
    rfl
  · change ((s.b2.x1.scale (goldOfInt (256))).add s.sum).value ls = _
    rw [AuthShamirWire.value_add (hs.2.2.2.1.scale _) hs.sum, AuthShamirWire.value_scale, AuthShamirState12.value_sum hs]
    rfl
  · change ((s.b2.x2.scale (goldOfInt (512))).add s.sum).value ls = _
    rw [AuthShamirWire.value_add (hs.2.2.2.2.1.scale _) hs.sum, AuthShamirWire.value_scale, AuthShamirState12.value_sum hs]
    rfl
  · change ((s.b2.x3.scale (goldOfInt (1024))).add s.sum).value ls = _
    rw [AuthShamirWire.value_add (hs.2.2.2.2.2.scale _) hs.sum, AuthShamirWire.value_scale, AuthShamirState12.value_sum hs]
    rfl


def AuthShamirLane4.addPublic (keys : List GoldilocksExt2) (rc : Lane4)
    (s : AuthShamirLane4) : AuthShamirLane4 :=
  ⟨s.x0.addPublic keys rc.x0, s.x1.addPublic keys rc.x1,
   s.x2.addPublic keys rc.x2, s.x3.addPublic keys rc.x3⟩

theorem AuthShamirLane4.Valid.addPublic {ls keys s} (rc : Lane4)
    (hOne : ringListSum ls = Goldilocks.one) (hs : AuthShamirLane4.Valid ls keys s) :
    (s.addPublic keys rc).Valid ls keys :=
  ⟨hs.1.addPublic _ hOne, hs.2.1.addPublic _ hOne,
   hs.2.2.1.addPublic _ hOne, hs.2.2.2.addPublic _ hOne⟩

theorem AuthShamirLane4.value_addPublic {ls keys s} (rc : Lane4)
    (hOne : ringListSum ls = Goldilocks.one) (hs : AuthShamirLane4.Valid ls keys s) :
    (s.addPublic keys rc).value ls = lane4Add (s.value ls) rc := by
  apply Lane4.ext
  · change (s.x0.addPublic keys rc.x0).value ls = _
    rw [AuthShamirWire.value_addPublic _ hOne hs.1]
    exact LawfulCommRing.add_comm _ _
  · change (s.x1.addPublic keys rc.x1).value ls = _
    rw [AuthShamirWire.value_addPublic _ hOne hs.2.1]
    exact LawfulCommRing.add_comm _ _
  · change (s.x2.addPublic keys rc.x2).value ls = _
    rw [AuthShamirWire.value_addPublic _ hOne hs.2.2.1]
    exact LawfulCommRing.add_comm _ _
  · change (s.x3.addPublic keys rc.x3).value ls = _
    rw [AuthShamirWire.value_addPublic _ hOne hs.2.2.2]
    exact LawfulCommRing.add_comm _ _

def AuthShamirState12.addPublic (keys : List GoldilocksExt2) (rc : Poseidon2State12)
    (s : AuthShamirState12) : AuthShamirState12 :=
  ⟨s.b0.addPublic keys rc.b0, s.b1.addPublic keys rc.b1, s.b2.addPublic keys rc.b2⟩

theorem AuthShamirState12.Valid.addPublic {ls keys s} (rc : Poseidon2State12)
    (hOne : ringListSum ls = Goldilocks.one) (hs : AuthShamirState12.Valid ls keys s) :
    (s.addPublic keys rc).Valid ls keys :=
  ⟨hs.1.addPublic _ hOne, hs.2.1.addPublic _ hOne, hs.2.2.addPublic _ hOne⟩

theorem AuthShamirState12.value_addPublic {ls keys s} (rc : Poseidon2State12)
    (hOne : ringListSum ls = Goldilocks.one) (hs : AuthShamirState12.Valid ls keys s) :
    (s.addPublic keys rc).value ls = state12Add (s.value ls) rc := by
  exact Poseidon2State12.ext (AuthShamirLane4.value_addPublic _ hOne hs.1)
    (AuthShamirLane4.value_addPublic _ hOne hs.2.1)
    (AuthShamirLane4.value_addPublic _ hOne hs.2.2)

/-- One gate's authenticated preprocessing and active deviations. -/
structure ActiveShamirPow7Prep where
  tuple : AuthSharedPow7Tuple
  zeroMasks : List GoldilocksExt2
  deltaD : Goldilocks
  sigmaDevs : List GoldilocksExt2

def ActiveShamirPow7Prep.Valid (ls : List Goldilocks) (keys : List GoldilocksExt2)
    (p : ActiveShamirPow7Prep) : Prop :=
  p.tuple.Valid ls keys ∧ p.zeroMasks.length = keys.length ∧
  ringListSum p.zeroMasks = CommRingOps.zero

@[expose] def ActiveShamirPow7Prep.Pins (keys : List GoldilocksExt2) (p : ActiveShamirPow7Prep) : Prop :=
  p.deltaD ≠ Goldilocks.zero ∧ ringListSum keys =
    CommRingOps.mul (ringListSum p.sigmaDevs) (GoldilocksExt2.inv (GoldilocksExt2.ofBase p.deltaD))

instance (keys : List GoldilocksExt2) (p : ActiveShamirPow7Prep) : Decidable (p.Pins keys) :=
  by unfold ActiveShamirPow7Prep.Pins; infer_instance

/-- Gate order is 0–47 initial external, 48–69 internal, 70–117 terminal external. -/
abbrev ActiveShamirPermPrep := Fin 118 → ActiveShamirPow7Prep

private def activeShamirGateIndex (i : Nat) : Fin 118 := ⟨i % 118, Nat.mod_lt _ (by decide)⟩

def execAuthShamirGateAt (ls : List Goldilocks) (keys : List GoldilocksExt2)
    (prep : ActiveShamirPermPrep) (i : Nat) (x : AuthShamirWire) : Option AuthShamirWire :=
  let p := prep (activeShamirGateIndex i)
  execAuthShamirPow7 ls keys p.zeroMasks x p.tuple p.deltaD p.sigmaDevs

private theorem execAuthShamirGateAt_exact {ls keys prep i x out}
    (hOne : ringListSum ls = Goldilocks.one) (hx : AuthShamirWire.Valid ls keys x)
    (hp : ∀ j, ActiveShamirPow7Prep.Valid ls keys (prep j))
    (hn : ∀ j, ¬ ActiveShamirPow7Prep.Pins keys (prep j))
    (h : execAuthShamirGateAt ls keys prep i x = some out) :
    out.Valid ls keys ∧ out.value ls = sbox7 (x.value ls) := by
  have ht := hp (activeShamirGateIndex i)
  obtain ⟨hv, he | he⟩ := execAuthShamirPow7_sound_or_pins_key hOne hx ht.1 ht.2.1 ht.2.2 h
  · exact ⟨hv, he.2⟩
  · exact False.elim (hn (activeShamirGateIndex i) he)

def execAuthShamirLane4 (ls : List Goldilocks) (keys : List GoldilocksExt2)
    (prep : ActiveShamirPermPrep) (i : Nat) (s : AuthShamirLane4) : Option AuthShamirLane4 := do
  let x0 ← execAuthShamirGateAt ls keys prep i s.x0
  let x1 ← execAuthShamirGateAt ls keys prep (i + 1) s.x1
  let x2 ← execAuthShamirGateAt ls keys prep (i + 2) s.x2
  let x3 ← execAuthShamirGateAt ls keys prep (i + 3) s.x3
  pure ⟨x0, x1, x2, x3⟩

private theorem execAuthShamirLane4_exact {ls keys prep i s out}
    (hOne : ringListSum ls = Goldilocks.one) (hs : AuthShamirLane4.Valid ls keys s)
    (hp : ∀ j, ActiveShamirPow7Prep.Valid ls keys (prep j))
    (hn : ∀ j, ¬ ActiveShamirPow7Prep.Pins keys (prep j))
    (h : execAuthShamirLane4 ls keys prep i s = some out) :
    out.Valid ls keys ∧ out.value ls = sboxLane4 (s.value ls) := by
  simp only [execAuthShamirLane4, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨x0, h0, x1, h1, x2, h2, x3, h3, rfl⟩ := h
  obtain ⟨v0, e0⟩ := execAuthShamirGateAt_exact hOne hs.1 hp hn h0
  obtain ⟨v1, e1⟩ := execAuthShamirGateAt_exact hOne hs.2.1 hp hn h1
  obtain ⟨v2, e2⟩ := execAuthShamirGateAt_exact hOne hs.2.2.1 hp hn h2
  obtain ⟨v3, e3⟩ := execAuthShamirGateAt_exact hOne hs.2.2.2 hp hn h3
  exact ⟨⟨v0, v1, v2, v3⟩, Lane4.ext e0 e1 e2 e3⟩

def execAuthShamirExternalRound (ls : List Goldilocks) (keys : List GoldilocksExt2)
    (prep : ActiveShamirPermPrep) (rc : Poseidon2State12)
    (i : Nat) (s : AuthShamirState12) : Option AuthShamirState12 := do
  let a := s.addPublic keys rc
  let b0 ← execAuthShamirLane4 ls keys prep i a.b0
  let b1 ← execAuthShamirLane4 ls keys prep (i + 4) a.b1
  let b2 ← execAuthShamirLane4 ls keys prep (i + 8) a.b2
  pure (AuthShamirState12.mk b0 b1 b2).applyME

private theorem execAuthShamirExternalRound_exact {ls keys prep rc i s out}
    (hOne : ringListSum ls = Goldilocks.one) (hs : AuthShamirState12.Valid ls keys s)
    (hp : ∀ j, ActiveShamirPow7Prep.Valid ls keys (prep j))
    (hn : ∀ j, ¬ ActiveShamirPow7Prep.Pins keys (prep j))
    (h : execAuthShamirExternalRound ls keys prep rc i s = some out) :
    out.Valid ls keys ∧ out.value ls = externalRound rc (s.value ls) := by
  simp only [execAuthShamirExternalRound, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨b0, h0, b1, h1, b2, h2, rfl⟩ := h
  have ha := hs.addPublic rc hOne
  obtain ⟨v0, e0⟩ := execAuthShamirLane4_exact hOne ha.1 hp hn h0
  obtain ⟨v1, e1⟩ := execAuthShamirLane4_exact hOne ha.2.1 hp hn h1
  obtain ⟨v2, e2⟩ := execAuthShamirLane4_exact hOne ha.2.2 hp hn h2
  have hv : (AuthShamirState12.mk b0 b1 b2).Valid ls keys := ⟨v0, v1, v2⟩
  refine ⟨hv.applyME, ?_⟩
  rw [AuthShamirState12.value_applyME hv]
  have he : (AuthShamirState12.mk b0 b1 b2).value ls =
      sboxState12 ((s.addPublic keys rc).value ls) := Poseidon2State12.ext e0 e1 e2
  rw [he, AuthShamirState12.value_addPublic rc hOne hs]
  rfl

def execAuthShamirInternalRound (ls : List Goldilocks) (keys : List GoldilocksExt2)
    (prep : ActiveShamirPermPrep) (rc : Goldilocks)
    (i : Nat) (s : AuthShamirState12) : Option AuthShamirState12 := do
  let x0 ← execAuthShamirGateAt ls keys prep i (s.b0.x0.addPublic keys rc)
  pure (AuthShamirState12.mk ⟨x0, s.b0.x1, s.b0.x2, s.b0.x3⟩ s.b1 s.b2).applyMI

private theorem execAuthShamirInternalRound_exact {ls keys prep rc i s out}
    (hOne : ringListSum ls = Goldilocks.one) (hs : AuthShamirState12.Valid ls keys s)
    (hp : ∀ j, ActiveShamirPow7Prep.Valid ls keys (prep j))
    (hn : ∀ j, ¬ ActiveShamirPow7Prep.Pins keys (prep j))
    (h : execAuthShamirInternalRound ls keys prep rc i s = some out) :
    out.Valid ls keys ∧ out.value ls = internalRound rc (s.value ls) := by
  simp only [execAuthShamirInternalRound, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨x0, h0, rfl⟩ := h
  obtain ⟨v0, e0⟩ := execAuthShamirGateAt_exact hOne (hs.1.1.addPublic rc hOne) hp hn h0
  have hv : (AuthShamirState12.mk ⟨x0, s.b0.x1, s.b0.x2, s.b0.x3⟩ s.b1 s.b2).Valid ls keys :=
    ⟨⟨v0, hs.1.2⟩, hs.2⟩
  refine ⟨hv.applyMI, ?_⟩
  rw [AuthShamirState12.value_applyMI hv]
  rw [AuthShamirWire.value_addPublic _ hOne hs.1.1] at e0
  change applyMI ⟨⟨x0.value ls, _, _, _⟩, _, _⟩ = _
  rw [e0]
  have hc : Goldilocks.add rc (s.b0.x0.value ls) = Goldilocks.add (s.b0.x0.value ls) rc :=
    LawfulCommRing.add_comm _ _
  rw [hc]
  rfl

/-- Execute a round list, carrying the authenticated state between rounds. -/
def execAuthShamirRounds {RC : Type}
    (step : RC → Nat → AuthShamirState12 → Option AuthShamirState12) (stride : Nat) :
    List RC → Nat → AuthShamirState12 → Option AuthShamirState12
  | [], _, s => some s
  | rc :: rcs, i, s => (step rc i s).bind (execAuthShamirRounds step stride rcs (i + stride))

private theorem execAuthShamirRounds_exact {RC : Type} {ls keys}
    (step : RC → Nat → AuthShamirState12 → Option AuthShamirState12)
    (plain : RC → Poseidon2State12 → Poseidon2State12) (stride : Nat)
    (hstep : ∀ rc i s out, AuthShamirState12.Valid ls keys s → step rc i s = some out →
      out.Valid ls keys ∧ out.value ls = plain rc (s.value ls)) :
    ∀ rcs i s out, AuthShamirState12.Valid ls keys s →
      execAuthShamirRounds step stride rcs i s = some out →
      out.Valid ls keys ∧ out.value ls = runRounds plain rcs (s.value ls)
  | [], _, _, _, hs, h => by
    simp only [execAuthShamirRounds, Option.some.injEq] at h
    subst h
    exact ⟨hs, rfl⟩
  | rc :: rcs, i, s, out, hs, h => by
    simp only [execAuthShamirRounds, Option.bind_eq_some_iff] at h
    obtain ⟨mid, hm, ho⟩ := h
    obtain ⟨vm, em⟩ := hstep rc i s mid hs hm
    obtain ⟨vo, eo⟩ := execAuthShamirRounds_exact step plain stride hstep rcs (i + stride) mid out vm ho
    exact ⟨vo, by rw [eo, em]; rfl⟩

/-- The full 30-round permutation: 48 + 22 + 48 share-grounded active pow7 gates.
Every gate computes its MAC residual from the propagated MAC shares. -/
def execActiveSharedPoseidon2Perm (ls : List Goldilocks) (keys : List GoldilocksExt2)
    (prep : ActiveShamirPermPrep) (s : AuthShamirState12) : Option AuthShamirState12 := do
  let a ← execAuthShamirRounds (execAuthShamirExternalRound ls keys prep) 12
    poseidon2InitialExtConsts 0 s.applyME
  let b ← execAuthShamirRounds (execAuthShamirInternalRound ls keys prep) 1
    poseidon2InternalConsts 48 a
  execAuthShamirRounds (execAuthShamirExternalRound ls keys prep) 12
    poseidon2TerminalExtConsts 70 b

/-- Accepted full permutations are correct with authenticated output, or one of the 118
active openings pins the global key. Only the initial state and preprocessing are assumed valid. -/
theorem execActiveSharedPoseidon2Perm_sound_or_pins_key {ls keys prep s out}
    (hOne : ringListSum ls = Goldilocks.one) (hs : AuthShamirState12.Valid ls keys s)
    (hp : ∀ j, ActiveShamirPow7Prep.Valid ls keys (prep j))
    (h : execActiveSharedPoseidon2Perm ls keys prep s = some out) :
    (out.Valid ls keys ∧ lagrangeCombineState12 ls out.shares =
      poseidon2Perm12 (lagrangeCombineState12 ls s.shares)) ∨
    (∃ j : Fin 118, (prep j).Pins keys) := by
  by_cases hn : ∃ j : Fin 118, (prep j).Pins keys
  · exact .inr hn
  · have hnone : ∀ j, ¬ (prep j).Pins keys := fun j hj => hn ⟨j, hj⟩
    simp only [execActiveSharedPoseidon2Perm, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, ho⟩ := h
    have he := fun rc i s out hs h => execAuthShamirExternalRound_exact
      (rc := rc) (i := i) (s := s) (out := out) hOne hs hp hnone h
    have hi := fun rc i s out hs h => execAuthShamirInternalRound_exact
      (rc := rc) (i := i) (s := s) (out := out) hOne hs hp hnone h
    obtain ⟨va, ea⟩ := execAuthShamirRounds_exact _ externalRound 12 he _ _ _ _ hs.applyME ha
    obtain ⟨vb, eb⟩ := execAuthShamirRounds_exact _ internalRound 1 hi _ _ _ _ va hb
    obtain ⟨vo, eo⟩ := execAuthShamirRounds_exact _ externalRound 12 he _ _ _ _ vb ho
    left
    refine ⟨vo, ?_⟩
    rw [AuthShamirState12.combine_shares vo, AuthShamirState12.combine_shares hs,
      eo, eb, ea, AuthShamirState12.value_applyME hs]
    rfl


private theorem zipLane4Shares_projections :
    ∀ (a b c d : List Goldilocks), a.length = b.length → a.length = c.length → a.length = d.length →
      (zipLane4Shares a b c d).map (·.x0) = a ∧
      (zipLane4Shares a b c d).map (·.x1) = b ∧
      (zipLane4Shares a b c d).map (·.x2) = c ∧
      (zipLane4Shares a b c d).map (·.x3) = d
  | [], [], [], [], _, _, _ => by simp [zipLane4Shares]
  | _ :: a, _ :: b, _ :: c, _ :: d, hb, hc, hd => by
    obtain ⟨h0, h1, h2, h3⟩ := zipLane4Shares_projections a b c d
      (Nat.succ.inj hb) (Nat.succ.inj hc) (Nat.succ.inj hd)
    simp only [zipLane4Shares, List.map_cons, h0, h1, h2, h3, and_self]

private theorem zipState12Shares_projections :
    ∀ (a b c : List Lane4), a.length = b.length → a.length = c.length →
      (zipState12Shares a b c).map (·.b0) = a ∧
      (zipState12Shares a b c).map (·.b1) = b ∧
      (zipState12Shares a b c).map (·.b2) = c
  | [], [], [], _, _ => by simp [zipState12Shares]
  | _ :: a, _ :: b, _ :: c, hb, hc => by
    obtain ⟨h0, h1, h2⟩ := zipState12Shares_projections a b c (Nat.succ.inj hb) (Nat.succ.inj hc)
    simp only [zipState12Shares, List.map_cons, h0, h1, h2, and_self]

private theorem ringListZipAdd_maps {A : Type} (f g : A → Goldilocks) :
    ∀ (xs : List A), ringListZipAdd (xs.map f) (xs.map g) = xs.map (fun x => Goldilocks.add (f x) (g x))
  | [] => rfl
  | _ :: xs => by simp only [List.map_cons, ringListZipAdd, ringListZipAdd_maps f g xs]; rfl

private theorem zipLane4Shares_maps {A : Type} (f0 f1 f2 f3 : A → Goldilocks) :
    ∀ (xs : List A), zipLane4Shares (xs.map f0) (xs.map f1) (xs.map f2) (xs.map f3) =
      xs.map (fun x => ⟨f0 x, f1 x, f2 x, f3 x⟩)
  | [] => rfl
  | _ :: xs => by simp only [List.map_cons, zipLane4Shares, zipLane4Shares_maps f0 f1 f2 f3 xs]

private theorem zipState12Shares_maps {A : Type} (f0 f1 f2 : A → Lane4) :
    ∀ (xs : List A), zipState12Shares (xs.map f0) (xs.map f1) (xs.map f2) =
      xs.map (fun x => ⟨f0 x, f1 x, f2 x⟩)
  | [] => rfl
  | _ :: xs => by simp only [List.map_cons, zipState12Shares, zipState12Shares_maps f0 f1 f2 xs]

private theorem AuthShamirLane4.projections {ls keys s} (hs : AuthShamirLane4.Valid ls keys s) :
    s.shares.map (·.x0) = s.x0.shares ∧ s.shares.map (·.x1) = s.x1.shares ∧
    s.shares.map (·.x2) = s.x2.shares ∧ s.shares.map (·.x3) = s.x3.shares :=
  zipLane4Shares_projections _ _ _ _ (hs.1.1.trans hs.2.1.1.symm)
    (hs.1.1.trans hs.2.2.1.1.symm) (hs.1.1.trans hs.2.2.2.1.symm)

private theorem AuthShamirState12.projections {ls keys s} (hs : AuthShamirState12.Valid ls keys s) :
    s.shares.map (·.b0) = s.b0.shares ∧ s.shares.map (·.b1) = s.b1.shares ∧
    s.shares.map (·.b2) = s.b2.shares :=
  zipState12Shares_projections _ _ _
    ((AuthShamirLane4.shares_length hs.1).trans (AuthShamirLane4.shares_length hs.2.1).symm)
    ((AuthShamirLane4.shares_length hs.1).trans (AuthShamirLane4.shares_length hs.2.2).symm)

theorem AuthShamirState12.shares_applyME {ls keys s}
    (hs : AuthShamirState12.Valid ls keys s) :
    (s.applyME).shares = s.shares.map Qsag.applyME := by
  obtain ⟨hb0, hb1, hb2⟩ := AuthShamirState12.projections hs
  obtain ⟨h00, h01, h02, h03⟩ := AuthShamirLane4.projections hs.1
  obtain ⟨h10, h11, h12, h13⟩ := AuthShamirLane4.projections hs.2.1
  obtain ⟨h20, h21, h22, h23⟩ := AuthShamirLane4.projections hs.2.2
  simp only [AuthShamirState12.applyME, AuthShamirState12.shares,
    AuthShamirLane4.shares, AuthShamirLane4.applyM4,
    AuthShamirLane4.sum, AuthShamirLane4.add, AuthShamirWire.add, AuthShamirWire.scale]
  rw [← h00, ← h01, ← h02, ← h03, ← h10, ← h11, ← h12, ← h13, ← h20, ← h21, ← h22, ← h23, ← hb0, ← hb1, ← hb2]
  simp only [shareScale, List.map_map, ringListZipAdd_maps,
    zipLane4Shares_maps, zipState12Shares_maps]
  rfl
theorem AuthShamirState12.shares_applyMI {ls keys s}
    (hs : AuthShamirState12.Valid ls keys s) :
    (s.applyMI).shares = s.shares.map Qsag.applyMI := by
  obtain ⟨hb0, hb1, hb2⟩ := AuthShamirState12.projections hs
  obtain ⟨h00, h01, h02, h03⟩ := AuthShamirLane4.projections hs.1
  obtain ⟨h10, h11, h12, h13⟩ := AuthShamirLane4.projections hs.2.1
  obtain ⟨h20, h21, h22, h23⟩ := AuthShamirLane4.projections hs.2.2
  simp only [AuthShamirState12.applyMI, AuthShamirState12.shares, AuthShamirState12.sum,
    AuthShamirLane4.shares, AuthShamirLane4.sum, AuthShamirWire.add, AuthShamirWire.scale]
  rw [← h00, ← h01, ← h02, ← h03, ← h10, ← h11, ← h12, ← h13, ← h20, ← h21, ← h22, ← h23, ← hb0, ← hb1, ← hb2]
  simp only [shareScale, List.map_map, ringListZipAdd_maps,
    zipLane4Shares_maps, zipState12Shares_maps]
  rfl
theorem AuthShamirState12.shares_addPublic {ls keys s} (rc : Poseidon2State12)
    (hs : AuthShamirState12.Valid ls keys s) :
    (s.addPublic keys rc).shares = s.shares.map (fun x => state12Add x rc) := by
  obtain ⟨hb0, hb1, hb2⟩ := AuthShamirState12.projections hs
  obtain ⟨h00, h01, h02, h03⟩ := AuthShamirLane4.projections hs.1
  obtain ⟨h10, h11, h12, h13⟩ := AuthShamirLane4.projections hs.2.1
  obtain ⟨h20, h21, h22, h23⟩ := AuthShamirLane4.projections hs.2.2
  simp only [AuthShamirState12.addPublic, AuthShamirState12.shares,
    AuthShamirLane4.shares, AuthShamirLane4.addPublic, AuthShamirWire.addPublic]
  rw [← h00, ← h01, ← h02, ← h03, ← h10, ← h11, ← h12, ← h13, ← h20, ← h21, ← h22, ← h23, ← hb0, ← hb1, ← hb2]
  simp only [shareAddConst, List.map_map, zipLane4Shares_maps, zipState12Shares_maps]
  apply List.map_congr_left
  intro x _
  apply Poseidon2State12.ext <;> apply Lane4.ext <;>
    exact LawfulCommRing.add_comm _ _


/-- Normalize the passive MAC transcript to the empty zero-sum list. The tuple is unchanged.
This API stores a ready-made transcript rather than authenticated wires. -/
def activeShamirPassivePrep (prep : ActiveShamirPermPrep) (i : Nat) :
    SharedPow7Tuple × List GoldilocksExt2 := ((prep (activeShamirGateIndex i)).tuple.toTuple, [])

/-- The corresponding frozen call-prep bundle, retaining all preprocessed Shamir powers. -/
def activeShamirPassiveCallPrep (prep : ActiveShamirPermPrep) : Poseidon2CallPrep :=
  ⟨(fun r k => activeShamirPassivePrep prep (12 * r + k)),
   (fun r => activeShamirPassivePrep prep (48 + r)),
   (fun r k => activeShamirPassivePrep prep (70 + 12 * r + k))⟩

theorem activeShamirPassiveCallPrep_valid {ls keys prep}
    (hp : ∀ j, ActiveShamirPow7Prep.Valid ls keys (prep j)) :
    (activeShamirPassiveCallPrep prep).validAt ls := by
  refine ⟨?_, ?_, ?_⟩
  · intro r k
    exact ⟨(hp _).1.1, rfl⟩
  · intro r
    exact ⟨(hp _).1.1, rfl⟩
  · intro r k
    exact ⟨(hp _).1.1, rfl⟩

private theorem activeShamirNoPins {keys : List GoldilocksExt2} {prep : ActiveShamirPermPrep}
    (hz : ∀ j : Fin 118, (prep j : ActiveShamirPow7Prep).deltaD = Goldilocks.zero) :
    ∀ j, ¬ ActiveShamirPow7Prep.Pins keys (prep j) :=
  fun j h => h.1 (hz j)

private theorem execAuthShamirGateAt_refines {ls keys prep i x out}
    (hz : ∀ j : Fin 118, (prep j : ActiveShamirPow7Prep).deltaD = Goldilocks.zero)
    (h : execAuthShamirGateAt ls keys prep i x = some out) :
    evalSharedPow7Binomial (lagrangeCombine ls (shareZipSub x.shares
      (activeShamirPassivePrep prep i).1.rSh)) (activeShamirPassivePrep prep i).1
      (activeShamirPassivePrep prep i).2 = some out.shares := by
  let p := prep (activeShamirGateIndex i)
  change execAuthShamirPow7 ls keys p.zeroMasks x p.tuple p.deltaD p.sigmaDevs = some out at h
  unfold execAuthShamirPow7 at h
  cases he : execActiveSharedPow7Round ls x.shares p.tuple.toTuple x.macs p.tuple.r.macs
      keys p.zeroMasks p.deltaD p.sigmaDevs with
  | none => simp only [he, Option.map_none] at h; cases h
  | some ys =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst out
    have hy := execActiveSharedPow7Round_output he
    have hz' : p.deltaD = Goldilocks.zero := hz _
    rw [hz'] at hy
    have hadd : ∀ a : Goldilocks, Goldilocks.add a Goldilocks.zero = a := LawfulCommRing.add_zero
    rw [hadd] at hy
    change evalSharedPow7Binomial _ p.tuple.toTuple [] = some ys
    rw [hy]
    rfl

private theorem execAuthShamirLane4_refines {ls keys prep i s out}
    (hz : ∀ j : Fin 118, (prep j : ActiveShamirPow7Prep).deltaD = Goldilocks.zero)
    (h : execAuthShamirLane4 ls keys prep i s = some out) :
    evalSharedLane4Sbox
      (mkOnlineAuthGate ls s.x0.shares (activeShamirPassivePrep prep i))
      (mkOnlineAuthGate ls s.x1.shares (activeShamirPassivePrep prep (i + 1)))
      (mkOnlineAuthGate ls s.x2.shares (activeShamirPassivePrep prep (i + 2)))
      (mkOnlineAuthGate ls s.x3.shares (activeShamirPassivePrep prep (i + 3))) = some out.shares := by
  simp only [execAuthShamirLane4, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨x0, h0, x1, h1, x2, h2, x3, h3, rfl⟩ := h
  have e0 := execAuthShamirGateAt_refines hz h0
  have e1 := execAuthShamirGateAt_refines hz h1
  have e2 := execAuthShamirGateAt_refines hz h2
  have e3 := execAuthShamirGateAt_refines hz h3
  simp only [evalSharedLane4Sbox, mkOnlineAuthGate, e0, e1, e2, e3, AuthShamirLane4.shares]

private theorem execAuthShamirExternalRound_refines {ls keys prep rc i s out}
    (hOne : ringListSum ls = Goldilocks.one) (hs : AuthShamirState12.Valid ls keys s)
    (hp : ∀ j, ActiveShamirPow7Prep.Valid ls keys (prep j))
    (hz : ∀ j : Fin 118, (prep j).deltaD = Goldilocks.zero)
    (h : execAuthShamirExternalRound ls keys prep rc i s = some out) :
    evalSharedPoseidon2ExternalRound rc s.shares
      (mkOnlineExtRoundGates ls rc s.shares (fun k => activeShamirPassivePrep prep (i + k))) =
      some out.shares := by
  simp only [execAuthShamirExternalRound, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨b0, h0, b1, h1, b2, h2, rfl⟩ := h
  have ha := hs.addPublic rc hOne
  have hn := activeShamirNoPins (keys := keys) hz
  obtain ⟨v0, _⟩ := execAuthShamirLane4_exact hOne ha.1 hp hn h0
  obtain ⟨v1, _⟩ := execAuthShamirLane4_exact hOne ha.2.1 hp hn h1
  obtain ⟨v2, _⟩ := execAuthShamirLane4_exact hOne ha.2.2 hp hn h2
  have hv : (AuthShamirState12.mk b0 b1 b2).Valid ls keys := ⟨v0, v1, v2⟩
  have e0 := execAuthShamirLane4_refines hz h0
  have e1 := execAuthShamirLane4_refines hz h1
  have e2 := execAuthShamirLane4_refines hz h2
  obtain ⟨hb0, hb1, hb2⟩ := AuthShamirState12.projections ha
  obtain ⟨h00, h01, h02, h03⟩ := AuthShamirLane4.projections ha.1
  obtain ⟨h10, h11, h12, h13⟩ := AuthShamirLane4.projections ha.2.1
  obtain ⟨h20, h21, h22, h23⟩ := AuthShamirLane4.projections ha.2.2
  have hadd := AuthShamirState12.shares_addPublic rc hs
  rw [AuthShamirState12.shares_applyME hv]
  unfold mkOnlineExtRoundGates
  rw [← hadd]
  rw [← hb0, List.map_map] at h00 h01 h02 h03
  rw [← hb1, List.map_map] at h10 h11 h12 h13
  rw [← hb2, List.map_map] at h20 h21 h22 h23
  simp only [Function.comp_def] at h00 h01 h02 h03 h10 h11 h12 h13 h20 h21 h22 h23
  simp only [Nat.add_assoc, Nat.reduceAdd] at e1 e2
  simp only [evalSharedPoseidon2ExternalRound, h00, h01, h02, h03, h10, h11, h12, h13,
    h20, h21, h22, h23, Nat.add_zero]
  rw [e0, e1, e2]
  simp only [AuthShamirState12.shares_length hs, AuthShamirLane4.shares_length v0,
    beq_self_eq_true, ↓reduceIte]
  rfl


private theorem execAuthShamirInternalRound_refines {ls keys prep rc i s out}
    (hOne : ringListSum ls = Goldilocks.one) (hs : AuthShamirState12.Valid ls keys s)
    (hp : ∀ j, ActiveShamirPow7Prep.Valid ls keys (prep j))
    (hz : ∀ j : Fin 118, (prep j).deltaD = Goldilocks.zero)
    (h : execAuthShamirInternalRound ls keys prep rc i s = some out) :
    evalSharedPoseidon2InternalRound rc s.shares
      (mkOnlineAuthGate ls (s.shares.map (fun x => Goldilocks.add x.b0.x0 rc))
        (activeShamirPassivePrep prep i)) = some out.shares := by
  simp only [execAuthShamirInternalRound, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨x0, h0, rfl⟩ := h
  obtain ⟨v0, _⟩ := execAuthShamirGateAt_exact hOne (hs.1.1.addPublic rc hOne) hp
    (activeShamirNoPins hz) h0
  have hv : (AuthShamirState12.mk ⟨x0, s.b0.x1, s.b0.x2, s.b0.x3⟩ s.b1 s.b2).Valid ls keys :=
    ⟨⟨v0, hs.1.2⟩, hs.2⟩
  have e0 := execAuthShamirGateAt_refines hz h0
  obtain ⟨hb0, hb1, hb2⟩ := AuthShamirState12.projections hs
  obtain ⟨h00, h01, h02, h03⟩ := AuthShamirLane4.projections hs.1
  rw [← hb0, List.map_map] at h00 h01 h02 h03
  have hadd : (s.b0.x0.addPublic keys rc).shares =
      s.shares.map (fun x => Goldilocks.add x.b0.x0 rc) := by
    change shareAddConst rc s.b0.x0.shares = _
    rw [← h00]
    simp only [shareAddConst, List.map_map]
    apply List.map_congr_left
    intro x _
    exact LawfulCommRing.add_comm _ _
  rw [hadd] at e0
  rw [AuthShamirState12.shares_applyMI hv]
  simp only [Function.comp_def] at h01 h02 h03
  simp only [evalSharedPoseidon2InternalRound, mkOnlineAuthGate]
  rw [e0]
  simp only [AuthShamirState12.shares_length hs, v0.1, beq_self_eq_true, ↓reduceIte,
    h01, h02, h03, hb1, hb2]
  rfl

private theorem execAuthShamirExtRounds_refines {ls keys prep}
    (hOne : ringListSum ls = Goldilocks.one)
    (hp : ∀ j, ActiveShamirPow7Prep.Valid ls keys (prep j))
    (hz : ∀ j : Fin 118, (prep j).deltaD = Goldilocks.zero) (offset : Nat) :
    ∀ rcs idx s out, AuthShamirState12.Valid ls keys s →
      execAuthShamirRounds (execAuthShamirExternalRound ls keys prep) 12 rcs (offset + 12 * idx) s = some out →
      runOnlineExtRounds ls rcs s.shares
        (fun r k => activeShamirPassivePrep prep (offset + 12 * r + k)) idx = some out.shares
  | [], _, _, _, _, h => by
    simp only [execAuthShamirRounds, Option.some.injEq] at h
    subst h
    rfl
  | rc :: rcs, idx, s, out, hs, h => by
    simp only [execAuthShamirRounds, Option.bind_eq_some_iff] at h
    obtain ⟨mid, hm, ho⟩ := h
    have he := execAuthShamirExternalRound_refines hOne hs hp hz hm
    have vm := (execAuthShamirExternalRound_exact hOne hs hp (activeShamirNoPins hz) hm).1
    have hidx : offset + 12 * idx + 12 = offset + 12 * (idx + 1) := by omega
    rw [hidx] at ho
    have ih := execAuthShamirExtRounds_refines hOne hp hz offset rcs (idx + 1) mid out vm ho
    simp only [runOnlineExtRounds, he]
    exact ih

private theorem execAuthShamirIntRounds_refines {ls keys prep}
    (hOne : ringListSum ls = Goldilocks.one)
    (hp : ∀ j, ActiveShamirPow7Prep.Valid ls keys (prep j))
    (hz : ∀ j : Fin 118, (prep j).deltaD = Goldilocks.zero) :
    ∀ rcs idx s out, AuthShamirState12.Valid ls keys s →
      execAuthShamirRounds (execAuthShamirInternalRound ls keys prep) 1 rcs (48 + idx) s = some out →
      runOnlineIntRounds ls rcs s.shares (fun r => activeShamirPassivePrep prep (48 + r)) idx = some out.shares
  | [], _, _, _, _, h => by
    simp only [execAuthShamirRounds, Option.some.injEq] at h
    subst h
    rfl
  | rc :: rcs, idx, s, out, hs, h => by
    simp only [execAuthShamirRounds, Option.bind_eq_some_iff] at h
    obtain ⟨mid, hm, ho⟩ := h
    have he := execAuthShamirInternalRound_refines hOne hs hp hz hm
    have vm := (execAuthShamirInternalRound_exact hOne hs hp (activeShamirNoPins hz) hm).1
    have hidx : 48 + idx + 1 = 48 + (idx + 1) := by omega
    rw [hidx] at ho
    have ih := execAuthShamirIntRounds_refines hOne hp hz rcs (idx + 1) mid out vm ho
    simp only [runOnlineIntRounds, he]
    exact ih

/-- An accepted zero-opening-deviation run has exactly the frozen passive API's party shares.
This is stronger than requiring all deviations zero: arbitrary accepted sigma deviations are allowed.
The corresponding passive prep retains every tuple and normalizes each zero-sum transcript to `[]`. -/
theorem execActiveSharedPoseidon2Perm_refines_online {ls keys prep s out}
    (hOne : ringListSum ls = Goldilocks.one) (hs : AuthShamirState12.Valid ls keys s)
    (hp : ∀ j, ActiveShamirPow7Prep.Valid ls keys (prep j))
    (hz : ∀ j : Fin 118, (prep j).deltaD = Goldilocks.zero)
    (h : execActiveSharedPoseidon2Perm ls keys prep s = some out) :
    runSharedPoseidon2PermOnline ls s.shares
      (fun r k => activeShamirPassivePrep prep (12 * r + k))
      (fun r => activeShamirPassivePrep prep (48 + r))
      (fun r k => activeShamirPassivePrep prep (70 + 12 * r + k)) = some out.shares := by
  simp only [execActiveSharedPoseidon2Perm, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, b, hb, ho⟩ := h
  have he := fun rc i s out hs h => execAuthShamirExternalRound_exact
    (rc := rc) (i := i) (s := s) (out := out) hOne hs hp (activeShamirNoPins hz) h
  have hi := fun rc i s out hs h => execAuthShamirInternalRound_exact
    (rc := rc) (i := i) (s := s) (out := out) hOne hs hp (activeShamirNoPins hz) h
  have va := (execAuthShamirRounds_exact _ externalRound 12 he _ _ _ _ hs.applyME ha).1
  have vb := (execAuthShamirRounds_exact _ internalRound 1 hi _ _ _ _ va hb).1
  have ea := execAuthShamirExtRounds_refines hOne hp hz 0 _ 0 _ _ hs.applyME ha
  have eb := execAuthShamirIntRounds_refines hOne hp hz _ 0 _ _ va hb
  have eo := execAuthShamirExtRounds_refines hOne hp hz 70 _ 0 _ _ vb ho
  rw [AuthShamirState12.shares_applyME hs] at ea
  simp only [Nat.zero_add] at ea
  simp only [runSharedPoseidon2PermOnline, ea, eb, eo]


private theorem execAuthShamirGateAt_complete {ls keys prep i x}
    (hOne : ringListSum ls = Goldilocks.one) (hx : AuthShamirWire.Valid ls keys x)
    (hp : ∀ j, ActiveShamirPow7Prep.Valid ls keys (prep j))
    (hz : ∀ j : Fin 118, (prep j).deltaD = Goldilocks.zero)
    (hd : ∀ j : Fin 118, ringListSum (prep j).sigmaDevs = CommRingOps.zero) :
    ∃ out, execAuthShamirGateAt ls keys prep i x = some out ∧ out.Valid ls keys := by
  let p := prep (activeShamirGateIndex i)
  have ht : p.Valid ls keys := hp _
  let d := lagrangeCombine ls (shareZipSub x.shares p.tuple.r.shares)
  have hdl : (shareZipSub x.macs p.tuple.r.macs).length = keys.length :=
    (shareZipSub_length_of_eq (hx.2.1.trans ht.1.2.1.2.1.symm)).trans hx.2.1
  have hds : ringListSum (shareZipSub x.macs p.tuple.r.macs) =
      CommRingOps.mul (ringListSum keys) (GoldilocksExt2.ofBase d) := by
    rw [ringListSum_zipSub (hx.2.1.trans ht.1.2.1.2.1.symm), hx.2.2, ht.1.2.1.2.2,
      ← LawfulCommRing.mul_sub, ← GoldilocksExt2.ofBase_sub]
    congr 2
    exact (ringDot_zipSub (hx.1.trans ht.1.2.1.1.symm)).symm
  have hc : verifySpdzZeroSumMac (ringListZipAdd
      (spdzComputeSigmas (GoldilocksExt2.ofBase d) (shareZipSub x.macs p.tuple.r.macs) keys p.zeroMasks)
      p.sigmaDevs) = true := by
    unfold verifySpdzZeroSumMac
    rw [decide_eq_true_iff, ringListSum_zipAdd, ringListSum_spdzComputeSigmas _ hdl ht.2.1,
      hds, ht.2.2, hd (activeShamirGateIndex i), LawfulCommRing.sub_self,
      LawfulCommRing.add_zero, LawfulCommRing.add_zero]
  have hz' : p.deltaD = Goldilocks.zero := hz _
  have hadd : ∀ a : Goldilocks, Goldilocks.add a Goldilocks.zero = a := LawfulCommRing.add_zero
  refine ⟨authPow7Output keys d p.tuple, ?_, authPow7Output_valid d hOne ht.1⟩
  change execAuthShamirPow7 ls keys p.zeroMasks x p.tuple p.deltaD p.sigmaDevs = _
  simp only [execAuthShamirPow7, execActiveSharedPow7Round, evalSharedPow7Binomial,
    hz', hadd]
  change (if verifySpdzZeroSumMac (ringListZipAdd
    (spdzComputeSigmas (GoldilocksExt2.ofBase d) (shareZipSub x.macs p.tuple.r.macs) keys p.zeroMasks)
    p.sigmaDevs) then some (mpcPow7Shares d p.tuple.toTuple) else none).map
      (fun ys => ⟨ys, (authPow7Output keys d p.tuple).macs⟩) = some (authPow7Output keys d p.tuple)
  rw [hc]
  simp only [↓reduceIte, Option.map_some]
  rw [← authPow7Output_shares keys d p.tuple]

private theorem execAuthShamirLane4_complete {ls keys prep i s}
    (hOne : ringListSum ls = Goldilocks.one) (hs : AuthShamirLane4.Valid ls keys s)
    (hp : ∀ j, ActiveShamirPow7Prep.Valid ls keys (prep j))
    (hz : ∀ j : Fin 118, (prep j).deltaD = Goldilocks.zero)
    (hd : ∀ j : Fin 118, ringListSum (prep j).sigmaDevs = CommRingOps.zero) :
    ∃ out, execAuthShamirLane4 ls keys prep i s = some out ∧ out.Valid ls keys := by
  obtain ⟨x0, h0, v0⟩ := execAuthShamirGateAt_complete (i := i) hOne hs.1 hp hz hd
  obtain ⟨x1, h1, v1⟩ := execAuthShamirGateAt_complete (i := i + 1) hOne hs.2.1 hp hz hd
  obtain ⟨x2, h2, v2⟩ := execAuthShamirGateAt_complete (i := i + 2) hOne hs.2.2.1 hp hz hd
  obtain ⟨x3, h3, v3⟩ := execAuthShamirGateAt_complete (i := i + 3) hOne hs.2.2.2 hp hz hd
  refine ⟨⟨x0, x1, x2, x3⟩, ?_, ⟨v0, v1, v2, v3⟩⟩
  simp only [execAuthShamirLane4, h0, h1, h2, h3, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

private theorem execAuthShamirExternalRound_complete {ls keys prep rc i s}
    (hOne : ringListSum ls = Goldilocks.one) (hs : AuthShamirState12.Valid ls keys s)
    (hp : ∀ j, ActiveShamirPow7Prep.Valid ls keys (prep j))
    (hz : ∀ j : Fin 118, (prep j).deltaD = Goldilocks.zero)
    (hd : ∀ j : Fin 118, ringListSum (prep j).sigmaDevs = CommRingOps.zero) :
    ∃ out, execAuthShamirExternalRound ls keys prep rc i s = some out ∧ out.Valid ls keys := by
  have ha := hs.addPublic rc hOne
  obtain ⟨b0, h0, v0⟩ := execAuthShamirLane4_complete (i := i) hOne ha.1 hp hz hd
  obtain ⟨b1, h1, v1⟩ := execAuthShamirLane4_complete (i := i + 4) hOne ha.2.1 hp hz hd
  obtain ⟨b2, h2, v2⟩ := execAuthShamirLane4_complete (i := i + 8) hOne ha.2.2 hp hz hd
  have hv : (AuthShamirState12.mk b0 b1 b2).Valid ls keys := ⟨v0, v1, v2⟩
  refine ⟨_, ?_, hv.applyME⟩
  simp only [execAuthShamirExternalRound, h0, h1, h2, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

private theorem execAuthShamirInternalRound_complete {ls keys prep rc i s}
    (hOne : ringListSum ls = Goldilocks.one) (hs : AuthShamirState12.Valid ls keys s)
    (hp : ∀ j, ActiveShamirPow7Prep.Valid ls keys (prep j))
    (hz : ∀ j : Fin 118, (prep j).deltaD = Goldilocks.zero)
    (hd : ∀ j : Fin 118, ringListSum (prep j).sigmaDevs = CommRingOps.zero) :
    ∃ out, execAuthShamirInternalRound ls keys prep rc i s = some out ∧ out.Valid ls keys := by
  obtain ⟨x0, h0, v0⟩ := execAuthShamirGateAt_complete (i := i) hOne
    (hs.1.1.addPublic rc hOne) hp hz hd
  have hv : (AuthShamirState12.mk ⟨x0, s.b0.x1, s.b0.x2, s.b0.x3⟩ s.b1 s.b2).Valid ls keys :=
    ⟨⟨v0, hs.1.2⟩, hs.2⟩
  refine ⟨_, ?_, hv.applyMI⟩
  simp only [execAuthShamirInternalRound, h0, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

private theorem execAuthShamirRounds_complete {RC : Type} {ls keys}
    (step : RC → Nat → AuthShamirState12 → Option AuthShamirState12) (stride : Nat)
    (hc : ∀ rc i s, AuthShamirState12.Valid ls keys s →
      ∃ out, step rc i s = some out ∧ out.Valid ls keys) :
    ∀ rcs i s, AuthShamirState12.Valid ls keys s →
      ∃ out, execAuthShamirRounds step stride rcs i s = some out ∧ out.Valid ls keys
  | [], _, s, hs => ⟨s, rfl, hs⟩
  | rc :: rcs, i, s, hs => by
    obtain ⟨mid, hm, vm⟩ := hc rc i s hs
    obtain ⟨out, ho, vo⟩ := execAuthShamirRounds_complete step stride hc rcs (i + stride) mid vm
    exact ⟨out, by simp only [execAuthShamirRounds, hm, Option.bind_some, ho], vo⟩

/-- Honest openings and zero-sum broadcast deviations never abort on valid authenticated input. -/
theorem execActiveSharedPoseidon2Perm_complete {ls keys prep s}
    (hOne : ringListSum ls = Goldilocks.one) (hs : AuthShamirState12.Valid ls keys s)
    (hp : ∀ j, ActiveShamirPow7Prep.Valid ls keys (prep j))
    (hz : ∀ j : Fin 118, (prep j).deltaD = Goldilocks.zero)
    (hd : ∀ j : Fin 118, ringListSum (prep j).sigmaDevs = CommRingOps.zero) :
    ∃ out, execActiveSharedPoseidon2Perm ls keys prep s = some out ∧ out.Valid ls keys := by
  have he := fun rc i s hs => execAuthShamirExternalRound_complete
    (rc := rc) (i := i) (s := s) hOne hs hp hz hd
  have hi := fun rc i s hs => execAuthShamirInternalRound_complete
    (rc := rc) (i := i) (s := s) hOne hs hp hz hd
  obtain ⟨a, ha, va⟩ := execAuthShamirRounds_complete _ 12 he poseidon2InitialExtConsts 0 _ hs.applyME
  obtain ⟨b, hb, vb⟩ := execAuthShamirRounds_complete _ 1 hi poseidon2InternalConsts 48 a va
  obtain ⟨out, ho, vo⟩ := execAuthShamirRounds_complete _ 12 he poseidon2TerminalExtConsts 70 b vb
  exact ⟨out, by simp only [execActiveSharedPoseidon2Perm, ha, hb, ho,
    Option.bind_eq_bind, Option.bind_some], vo⟩

/-- Equality of the active and frozen passive share outputs, without an acceptance premise. -/
theorem execActiveSharedPoseidon2Perm_honest_eq_online {ls keys prep s}
    (hOne : ringListSum ls = Goldilocks.one) (hs : AuthShamirState12.Valid ls keys s)
    (hp : ∀ j, ActiveShamirPow7Prep.Valid ls keys (prep j))
    (hz : ∀ j : Fin 118, (prep j).deltaD = Goldilocks.zero)
    (hd : ∀ j : Fin 118, ringListSum (prep j).sigmaDevs = CommRingOps.zero) :
    (execActiveSharedPoseidon2Perm ls keys prep s).map AuthShamirState12.shares =
      runSharedPoseidon2PermOnline ls s.shares
        (fun r k => activeShamirPassivePrep prep (12 * r + k))
        (fun r => activeShamirPassivePrep prep (48 + r))
        (fun r k => activeShamirPassivePrep prep (70 + 12 * r + k)) := by
  obtain ⟨out, he, _⟩ := execActiveSharedPoseidon2Perm_complete hOne hs hp hz hd
  rw [he, execActiveSharedPoseidon2Perm_refines_online hOne hs hp hz he]
  rfl


/-- Absorb eight authenticated message limbs, preserving the four capacity lanes. -/
def authShamirAbsorbRate8 (s : AuthShamirState12) (m0 m1 : AuthShamirLane4) : AuthShamirState12 :=
  ⟨s.b0.add m0, s.b1.add m1, s.b2⟩

theorem authShamirAbsorbRate8_valid {ls keys s m0 m1}
    (hs : AuthShamirState12.Valid ls keys s)
    (h0 : AuthShamirLane4.Valid ls keys m0) (h1 : AuthShamirLane4.Valid ls keys m1) :
    (authShamirAbsorbRate8 s m0 m1).Valid ls keys :=
  ⟨hs.1.add h0, hs.2.1.add h1, hs.2.2⟩

def execActiveShamirAbsorbRate8Block (ls : List Goldilocks) (keys : List GoldilocksExt2)
    (prep : ActiveShamirPermPrep) (s : AuthShamirState12) (m0 m1 : AuthShamirLane4) :
    Option AuthShamirState12 :=
  execActiveSharedPoseidon2Perm ls keys prep (authShamirAbsorbRate8 s m0 m1)

/-- Single-block active sponge composition, with authenticated message limbs. -/
theorem execActiveShamirAbsorbRate8Block_sound_or_pins_key {ls keys prep s m0 m1 out}
    (hOne : ringListSum ls = Goldilocks.one) (hs : AuthShamirState12.Valid ls keys s)
    (h0 : AuthShamirLane4.Valid ls keys m0) (h1 : AuthShamirLane4.Valid ls keys m1)
    (hp : ∀ j, ActiveShamirPow7Prep.Valid ls keys (prep j))
    (h : execActiveShamirAbsorbRate8Block ls keys prep s m0 m1 = some out) :
    (out.Valid ls keys ∧ lagrangeCombineState12 ls out.shares =
      poseidon2Perm12 ⟨lane4Add (s.value ls).b0 (m0.value ls),
        lane4Add (s.value ls).b1 (m1.value ls), (s.value ls).b2⟩) ∨
    (∃ j : Fin 118, (prep j).Pins keys) := by
  have ha := authShamirAbsorbRate8_valid hs h0 h1
  obtain hok | hpin := execActiveSharedPoseidon2Perm_sound_or_pins_key hOne ha hp h
  · left
    refine ⟨hok.1, ?_⟩
    rw [hok.2, AuthShamirState12.combine_shares ha]
    have he : (authShamirAbsorbRate8 s m0 m1).value ls =
        ⟨lane4Add (s.value ls).b0 (m0.value ls),
          lane4Add (s.value ls).b1 (m1.value ls), (s.value ls).b2⟩ :=
      Poseidon2State12.ext (AuthShamirLane4.value_add hs.1 h0)
        (AuthShamirLane4.value_add hs.2.1 h1) rfl
    rw [he]
  · exact .inr hpin

/-- The active authenticated absorb block refines the existing passive block at the share level. -/
theorem execActiveShamirAbsorbRate8Block_honest_eq {ls keys prep s m0 m1}
    (hOne : ringListSum ls = Goldilocks.one) (hs : AuthShamirState12.Valid ls keys s)
    (h0 : AuthShamirLane4.Valid ls keys m0) (h1 : AuthShamirLane4.Valid ls keys m1)
    (hp : ∀ j, ActiveShamirPow7Prep.Valid ls keys (prep j))
    (hz : ∀ j : Fin 118, (prep j).deltaD = Goldilocks.zero)
    (hd : ∀ j : Fin 118, ringListSum (prep j).sigmaDevs = CommRingOps.zero) :
    (execActiveShamirAbsorbRate8Block ls keys prep s m0 m1).map AuthShamirState12.shares =
      shamirAbsorbRate8Block ls s.shares m0.x0.shares m0.x1.shares m0.x2.shares m0.x3.shares
        m1.x0.shares m1.x1.shares m1.x2.shares m1.x3.shares (activeShamirPassiveCallPrep prep) := by
  unfold execActiveShamirAbsorbRate8Block
  rw [execActiveSharedPoseidon2Perm_honest_eq_online hOne (authShamirAbsorbRate8_valid hs h0 h1) hp hz hd]
  obtain ⟨hb0, hb1, hb2⟩ := AuthShamirState12.projections hs
  obtain ⟨h00, h01, h02, h03⟩ := AuthShamirLane4.projections hs.1
  obtain ⟨h10, h11, h12, h13⟩ := AuthShamirLane4.projections hs.2.1
  rw [← hb0, List.map_map] at h00 h01 h02 h03
  rw [← hb1, List.map_map] at h10 h11 h12 h13
  simp only [Function.comp_def] at h00 h01 h02 h03 h10 h11 h12 h13
  unfold shamirAbsorbRate8Block
  rw [h00, h01, h02, h03, h10, h11, h12, h13, hb2]
  rfl

/-- Small one-party authenticated zero state, for executable permutation witnesses. -/
def demoAuthShamirZeroWire : AuthShamirWire := ⟨[Goldilocks.zero], [GoldilocksExt2.zero]⟩

def demoAuthShamirZeroState : AuthShamirState12 :=
  let b : AuthShamirLane4 := ⟨demoAuthShamirZeroWire, demoAuthShamirZeroWire,
    demoAuthShamirZeroWire, demoAuthShamirZeroWire⟩
  ⟨b, b, b⟩

def demoAuthShamirZeroTuple : AuthSharedPow7Tuple :=
  ⟨demoAuthShamirZeroWire, demoAuthShamirZeroWire, demoAuthShamirZeroWire,
   demoAuthShamirZeroWire, demoAuthShamirZeroWire, demoAuthShamirZeroWire, demoAuthShamirZeroWire⟩

def demoActiveShamirPermPrep : ActiveShamirPermPrep := fun _ =>
  ⟨demoAuthShamirZeroTuple, [GoldilocksExt2.zero], Goldilocks.zero, [GoldilocksExt2.zero]⟩

theorem demoActiveShamirPerm_valid :
    demoAuthShamirZeroState.Valid [Goldilocks.one] [GoldilocksExt2.one] ∧
    ∀ j, (demoActiveShamirPermPrep j).Valid [Goldilocks.one] [GoldilocksExt2.one] := by
  constructor
  · unfold AuthShamirState12.Valid AuthShamirLane4.Valid AuthShamirWire.Valid
    decide +kernel
  · intro j
    change ActiveShamirPow7Prep.Valid _ _ ⟨demoAuthShamirZeroTuple, _, _, _⟩
    unfold ActiveShamirPow7Prep.Valid AuthSharedPow7Tuple.Valid AuthShamirWire.Valid SharedPow7Tuple.validAt
    decide +kernel

theorem execActiveSharedPoseidon2Perm_inhabited :
    (execActiveSharedPoseidon2Perm [Goldilocks.one] [GoldilocksExt2.one]
      demoActiveShamirPermPrep demoAuthShamirZeroState).isSome = true := by
  obtain ⟨out, he, _⟩ := execActiveSharedPoseidon2Perm_complete (by rfl)
    demoActiveShamirPerm_valid.1 demoActiveShamirPerm_valid.2
    (fun _ => rfl) (fun _ => rfl)
  rw [he]
  rfl

/-- A nonzero first opening deviation, with honest sigma broadcasts, aborts the full permutation. -/
theorem tooth_execActiveSharedPoseidon2Perm_aborts_on_forged_gate :
    (execActiveSharedPoseidon2Perm [Goldilocks.one] [GoldilocksExt2.one]
      (fun j => if j.val = 0 then { demoActiveShamirPermPrep j with deltaD := Goldilocks.one }
        else demoActiveShamirPermPrep j) demoAuthShamirZeroState).isNone = true := by
  decide +kernel

/-- Compose an active authenticated Shamir gate with its online continuation.
Failure is propagated before the continuation can release anything. -/
def continueActiveShamirGate {Output : Type}
    (lambdas xSh : List Goldilocks) (tup : SharedPow7Tuple)
    (macX macR alphaShares zeroMasks : List GoldilocksExt2)
    (deltaD : Goldilocks) (sigmaDevs : List GoldilocksExt2)
    (finish : List Goldilocks → Option Output) : Option Output :=
  (execActiveSharedPow7Round lambdas xSh tup macX macR alphaShares zeroMasks deltaD sigmaDevs).bind finish

theorem continueActiveShamirGate_abort {Output : Type}
    (lambdas xSh : List Goldilocks) (tup : SharedPow7Tuple)
    (macX macR alphaShares zeroMasks : List GoldilocksExt2)
    (deltaD : Goldilocks) (sigmaDevs : List GoldilocksExt2)
    (finish : List Goldilocks → Option Output)
    (h : execActiveSharedPow7Round lambdas xSh tup macX macR alphaShares zeroMasks deltaD sigmaDevs = none) :
    continueActiveShamirGate lambdas xSh tup macX macR alphaShares zeroMasks deltaD sigmaDevs finish = none := by
  simp only [continueActiveShamirGate, h, Option.bind_none]

/-- Any online continuation receives a correct Shamir result, or the active
opening pins the global MAC key. The MAC residual is computed from party shares
by `execActiveSharedPow7Round`, not supplied as an `hSum` assumption. This local
composition theorem does not assume that the continuation is an honest signer. -/
theorem continueActiveShamirGate_sound_or_pins_key {Output : Type}
    (lambdas xSh : List Goldilocks) (tup : SharedPow7Tuple)
    (macX macR alphaShares zeroMasks : List GoldilocksExt2)
    (deltaD : Goldilocks) (sigmaDevs : List GoldilocksExt2)
    (finish : List Goldilocks → Option Output) (out : Output)
    (hSumOne : ringListSum lambdas = Goldilocks.one)
    (hXLen : xSh.length = lambdas.length) (hTup : tup.validAt lambdas)
    (hMacXLen : macX.length = alphaShares.length)
    (hMacRLen : macR.length = alphaShares.length)
    (hMaskLen : zeroMasks.length = alphaShares.length)
    (hMacXSum : ringListSum macX = CommRingOps.mul (ringListSum alphaShares)
      (GoldilocksExt2.ofBase (lagrangeCombine lambdas xSh)))
    (hMacRSum : ringListSum macR = CommRingOps.mul (ringListSum alphaShares)
      (GoldilocksExt2.ofBase (lagrangeCombine lambdas tup.rSh)))
    (hZeroMask : ringListSum zeroMasks = CommRingOps.zero)
    (hAccept : continueActiveShamirGate lambdas xSh tup macX macR alphaShares zeroMasks
      deltaD sigmaDevs finish = some out) :
    (∃ ySh, finish ySh = some out ∧ ySh.length = lambdas.length ∧
      lagrangeCombine lambdas ySh = sbox7 (lagrangeCombine lambdas xSh)) ∨
    (deltaD ≠ Goldilocks.zero ∧ ringListSum alphaShares =
      CommRingOps.mul (ringListSum sigmaDevs) (GoldilocksExt2.inv (GoldilocksExt2.ofBase deltaD))) := by
  unfold continueActiveShamirGate at hAccept
  cases he : execActiveSharedPow7Round lambdas xSh tup macX macR alphaShares zeroMasks deltaD sigmaDevs with
  | none => rw [he] at hAccept; cases hAccept
  | some y =>
    rw [he] at hAccept
    obtain hok | hpin := execActiveSharedPow7Round_sound_or_pins_key
      lambdas xSh tup macX macR alphaShares zeroMasks deltaD sigmaDevs y
      hSumOne hXLen hTup hMacXLen hMacRLen hMaskLen hMacXSum hMacRSum hZeroMask he
    · exact .inl ⟨y, hAccept, hok.2⟩
    · exact .inr hpin


/-- A valid complete permutation execution supplies every premise of share refinement. -/
theorem witness_active_shamir_permutation :
    ∃ (ls : List Goldilocks) (keys : List GoldilocksExt2) (prep : ActiveShamirPermPrep)
      (s out : AuthShamirState12),
      ringListSum ls = Goldilocks.one ∧ s.Valid ls keys ∧
      (∀ j, ActiveShamirPow7Prep.Valid ls keys (prep j)) ∧
      (∀ j : Fin 118, (prep j).deltaD = Goldilocks.zero) ∧
      execActiveSharedPoseidon2Perm ls keys prep s = some out := by
  obtain ⟨out, he, _⟩ := execActiveSharedPoseidon2Perm_complete (by rfl)
    demoActiveShamirPerm_valid.1 demoActiveShamirPerm_valid.2
    (fun _ => rfl) (fun _ => rfl)
  exact ⟨[Goldilocks.one], [GoldilocksExt2.one], demoActiveShamirPermPrep,
    demoAuthShamirZeroState, out, rfl, demoActiveShamirPerm_valid.1,
    demoActiveShamirPerm_valid.2, (fun _ => rfl), he⟩

theorem tooth_active_shamir_no_forged_output (out : AuthShamirState12) :
    execActiveSharedPoseidon2Perm [Goldilocks.one] [GoldilocksExt2.one]
      (fun j => if j.val = 0 then { demoActiveShamirPermPrep j with deltaD := Goldilocks.one }
        else demoActiveShamirPermPrep j) demoAuthShamirZeroState ≠ some out := by
  intro h
  have hn := tooth_execActiveSharedPoseidon2Perm_aborts_on_forged_gate
  rw [h] at hn
  cases hn

#tooth_pair Qsag.execActiveSharedPoseidon2Perm_sound_or_pins_key vs Qsag.tooth_active_shamir_no_forged_output
#verify_inhabited Qsag.execActiveSharedPoseidon2Perm_refines_online Qsag.witness_active_shamir_permutation

/-- An authenticated rate-8 block contains eight authenticated message limbs. -/
abbrev AuthShamirBlock := AuthShamirLane4 × AuthShamirLane4

def AuthShamirBlock.Valid (ls : List Goldilocks) (keys : List GoldilocksExt2)
    (b : AuthShamirBlock) : Prop := b.1.Valid ls keys ∧ b.2.Valid ls keys

/-- Sequential active sponge execution. Each block consumes its own 118-gate preparation. -/
def execActiveShamirBlocks (ls : List Goldilocks) (keys : List GoldilocksExt2)
    (prep : Nat → ActiveShamirPermPrep) :
    Nat → AuthShamirState12 → List AuthShamirBlock → Option AuthShamirState12
  | _, s, [] => some s
  | i, s, b :: bs =>
    (execActiveShamirAbsorbRate8Block ls keys (prep i) s b.1 b.2).bind
      (fun next => execActiveShamirBlocks ls keys prep (i + 1) next bs)

/-- Clear permutation semantics used only in the proof, never by the executor. -/
def activeShamirBlocksValue (ls : List Goldilocks) :
    Poseidon2State12 → List AuthShamirBlock → Poseidon2State12
  | s, [] => s
  | s, b :: bs => activeShamirBlocksValue ls
      (poseidon2Perm12 ⟨lane4Add s.b0 (b.1.value ls),
        lane4Add s.b1 (b.2.value ls), s.b2⟩) bs

/-- An accepted multi-block computation either preserves authentication and the exact
sponge value, or identifies a gate in a consumed block that pins the MAC key. -/
theorem execActiveShamirBlocks_sound_or_pins_key
    {ls keys prep} (hOne : ringListSum ls = Goldilocks.one)
    (hp : ∀ i j, ActiveShamirPow7Prep.Valid ls keys (prep i j)) :
    ∀ (bs : List AuthShamirBlock) (i : Nat) (s out : AuthShamirState12),
      s.Valid ls keys → (∀ b ∈ bs, b.Valid ls keys) →
      execActiveShamirBlocks ls keys prep i s bs = some out →
      (out.Valid ls keys ∧ out.value ls = activeShamirBlocksValue ls (s.value ls) bs) ∨
      (∃ k j, i ≤ k ∧ k < i + bs.length ∧ (prep k j).Pins keys) := by
  intro bs
  induction bs with
  | nil =>
    intro i s out hs _ he
    simp only [execActiveShamirBlocks, Option.some.injEq] at he
    subst out
    exact .inl ⟨hs, rfl⟩
  | cons b bs ih =>
    intro i s out hs hb he
    have vb := hb b (by simp)
    have vr : ∀ c ∈ bs, c.Valid ls keys := fun c hc => hb c (List.mem_cons_of_mem b hc)
    unfold execActiveShamirBlocks at he
    cases hm : execActiveShamirAbsorbRate8Block ls keys (prep i) s b.1 b.2 with
    | none => simp only [hm, Option.bind_none] at he; cases he
    | some mid =>
      simp only [hm, Option.bind_some] at he
      obtain good | bad := execActiveShamirAbsorbRate8Block_sound_or_pins_key
        hOne hs vb.1 vb.2 (hp i) hm
      · have hv : mid.value ls = poseidon2Perm12
            ⟨lane4Add (s.value ls).b0 (b.1.value ls),
             lane4Add (s.value ls).b1 (b.2.value ls), (s.value ls).b2⟩ := by
          exact (AuthShamirState12.combine_shares good.1).symm.trans good.2
        obtain tailGood | tailBad := ih (i + 1) mid out good.1 vr he
        · have stepEq := congrArg (fun v => activeShamirBlocksValue ls v bs) hv
          have result := tailGood.2.trans stepEq
          left
          refine ⟨tailGood.1, ?_⟩
          rw [activeShamirBlocksValue]
          exact result
        · obtain ⟨k, j, hlo, hhi, hpin⟩ := tailBad
          exact .inr ⟨k, j, by omega, by simp only [List.length_cons]; omega, hpin⟩
      · obtain ⟨j, hpin⟩ := bad
        exact .inr ⟨i, j, Nat.le_refl _, by simp [List.length_cons], hpin⟩

/-- Continuations receive the authenticated final state only after every block accepts. -/
def continueActiveShamirBlocks {Output : Type}
    (ls : List Goldilocks) (keys : List GoldilocksExt2) (prep : Nat → ActiveShamirPermPrep)
    (i : Nat) (s : AuthShamirState12) (bs : List AuthShamirBlock)
    (finish : AuthShamirState12 → Option Output) : Option Output :=
  (execActiveShamirBlocks ls keys prep i s bs).bind finish

theorem continueActiveShamirBlocks_sound_or_pins_key {Output : Type}
    {ls keys prep i s bs} (finish : AuthShamirState12 → Option Output) (out : Output)
    (hOne : ringListSum ls = Goldilocks.one)
    (hp : ∀ i j, ActiveShamirPow7Prep.Valid ls keys (prep i j))
    (hs : AuthShamirState12.Valid ls keys s) (hb : ∀ b ∈ bs, AuthShamirBlock.Valid ls keys b)
    (he : continueActiveShamirBlocks ls keys prep i s bs finish = some out) :
    (∃ final, final.Valid ls keys ∧
      final.value ls = activeShamirBlocksValue ls (s.value ls) bs ∧ finish final = some out) ∨
    (∃ k j, i ≤ k ∧ k < i + bs.length ∧ (prep k j).Pins keys) := by
  unfold continueActiveShamirBlocks at he
  cases hx : execActiveShamirBlocks ls keys prep i s bs with
  | none => simp only [hx, Option.bind_none] at he; cases he
  | some final =>
    simp only [hx, Option.bind_some] at he
    obtain good | bad := execActiveShamirBlocks_sound_or_pins_key hOne hp bs i s final hs hb hx
    · exact .inl ⟨final, good.1, good.2, he⟩
    · exact .inr bad

/-- Honest openings complete every block; no acceptance assumption is needed. -/
theorem execActiveShamirBlocks_complete {ls keys prep}
    (hOne : ringListSum ls = Goldilocks.one)
    (hp : ∀ i j, ActiveShamirPow7Prep.Valid ls keys (prep i j))
    (hz : ∀ i j, (prep i j).deltaD = Goldilocks.zero)
    (hd : ∀ i j, ringListSum (prep i j).sigmaDevs = CommRingOps.zero) :
    ∀ (bs : List AuthShamirBlock) (i : Nat) (s : AuthShamirState12),
      s.Valid ls keys → (∀ b ∈ bs, b.Valid ls keys) →
      ∃ out, execActiveShamirBlocks ls keys prep i s bs = some out ∧ out.Valid ls keys := by
  intro bs
  induction bs with
  | nil => intro i s hs _; exact ⟨s, rfl, hs⟩
  | cons b bs ih =>
    intro i s hs hb
    have vb := hb b (by simp)
    obtain ⟨mid, hm, vm⟩ := execActiveSharedPoseidon2Perm_complete hOne
      (authShamirAbsorbRate8_valid hs vb.1 vb.2) (hp i) (hz i) (hd i)
    obtain ⟨out, ho, vo⟩ := ih (i + 1) mid vm (fun c hc => hb c (List.mem_cons_of_mem b hc))
    exact ⟨out, by simp only [execActiveShamirBlocks, execActiveShamirAbsorbRate8Block,
      hm, Option.bind_some, ho], vo⟩

/-- Flatten authenticated blocks to the existing passive sponge's limb-share format. -/
def authShamirBlocksLimbs : List AuthShamirBlock → List (List Goldilocks)
  | [] => []
  | b :: bs => b.1.x0.shares :: b.1.x1.shares :: b.1.x2.shares :: b.1.x3.shares ::
      b.2.x0.shares :: b.2.x1.shares :: b.2.x2.shares :: b.2.x3.shares :: authShamirBlocksLimbs bs

/-- Whole-stream share refinement to the sponge used by the threshold hash oracles. -/
theorem execActiveShamirBlocks_honest_eq {ls keys prep}
    (hOne : ringListSum ls = Goldilocks.one)
    (hp : ∀ i j, ActiveShamirPow7Prep.Valid ls keys (prep i j))
    (hz : ∀ i j, (prep i j).deltaD = Goldilocks.zero)
    (hd : ∀ i j, ringListSum (prep i j).sigmaDevs = CommRingOps.zero) :
    ∀ (bs : List AuthShamirBlock) (i : Nat) (s : AuthShamirState12),
      s.Valid ls keys → (∀ b ∈ bs, b.Valid ls keys) →
      (execActiveShamirBlocks ls keys prep i s bs).map AuthShamirState12.shares =
        shamirAbsorbLimbStream ls s.shares (fun k => activeShamirPassiveCallPrep (prep k))
          i (authShamirBlocksLimbs bs) := by
  intro bs
  induction bs with
  | nil => intro i s _ _; rfl
  | cons b bs ih =>
    intro i s hs hb
    have vb := hb b (by simp)
    obtain ⟨mid, hm, vm⟩ := execActiveSharedPoseidon2Perm_complete hOne
      (authShamirAbsorbRate8_valid hs vb.1 vb.2) (hp i) (hz i) (hd i)
    have hm' : execActiveShamirAbsorbRate8Block ls keys (prep i) s b.1 b.2 = some mid := hm
    have heq := execActiveShamirAbsorbRate8Block_honest_eq hOne hs vb.1 vb.2 (hp i) (hz i) (hd i)
    rw [hm'] at heq
    simp only [Option.map_some] at heq
    simp only [execActiveShamirBlocks, hm', Option.bind_some,
      authShamirBlocksLimbs, shamirAbsorbLimbStream, ← heq]
    exact ih (i + 1) mid vm (fun c hc => hb c (List.mem_cons_of_mem b hc))

/-! ### Constructive `GoldilocksExt2` Enumeration, Degree-`< t` Sacrificial Consistency & Active MAC Pin Bounds -/

theorem goldilocksPrime_pos : 0 < goldilocksPrime := by decide

def goldilocksExt2Card : Nat := goldilocksPrime * goldilocksPrime

theorem goldilocksExt2Card_pos : 0 < goldilocksExt2Card := by
  unfold goldilocksExt2Card
  exact Nat.mul_pos goldilocksPrime_pos goldilocksPrime_pos

theorem goldilocksExt2Card_gt_two_pow_126 : 2 ^ 126 < goldilocksExt2Card := by
  unfold goldilocksExt2Card goldilocksPrime
  decide

/-- Constructive `0 Classical.choice` bijection `Fin goldilocksPrime ≃ Goldilocks`. -/
def enumGoldilocks : SimpleEquiv (Fin goldilocksPrime) Goldilocks :=
  { toFun := fun i => ⟨i.val, i.isLt⟩
    invFun := fun x => ⟨x.val, x.isLt⟩
    left_inv := fun ⟨_, _⟩ => rfl
    right_inv := fun ⟨_, _⟩ => rfl }

/-- Constructive `0 Classical.choice` bijection `Fin (goldilocksPrime^2) ≃ GoldilocksExt2`. -/
def enumGoldilocksExt2 : SimpleEquiv (Fin goldilocksExt2Card) GoldilocksExt2 :=
  { toFun := fun idx =>
      ⟨enumGoldilocks.toFun (ucSplitLeft goldilocksPrime_pos idx),
       enumGoldilocks.toFun (ucSplitRight goldilocksPrime_pos idx)⟩
    invFun := fun x =>
      ucPairFin (enumGoldilocks.invFun x.c0) (enumGoldilocks.invFun x.c1)
    left_inv := fun idx => by
      change ucPairFin (ucSplitLeft goldilocksPrime_pos idx)
          (ucSplitRight goldilocksPrime_pos idx) = idx
      exact ucPair_split goldilocksPrime_pos idx
    right_inv := fun ⟨c0, c1⟩ => by
      apply GoldilocksExt2.ext
      · change (ucSplitLeft goldilocksPrime_pos
            (ucPairFin (enumGoldilocks.invFun c0) (enumGoldilocks.invFun c1)) |> enumGoldilocks.toFun) = c0
        rw [ucSplitLeft_pair goldilocksPrime_pos]
        rfl
      · change (ucSplitRight goldilocksPrime_pos
            (ucPairFin (enumGoldilocks.invFun c0) (enumGoldilocks.invFun c1)) |> enumGoldilocks.toFun) = c1
        rw [ucSplitRight_pair goldilocksPrime_pos]
        rfl }

/-- Constructive `0 Classical.choice` bijection `Fin (ucPow goldilocksPrime t) ≃ ShamirPadPoly Goldilocks t`. -/
def enumShamirPadPolyGoldilocks :
    (t : Nat) → SimpleEquiv (Fin (ucPow goldilocksPrime t)) (ShamirPadPoly Goldilocks t)
  | 0 =>
    { toFun := fun _ => ⟨[], rfl⟩
      invFun := fun _ => ⟨0, Nat.zero_lt_one⟩
      left_inv := fun ⟨v, hv⟩ => by
        have hv1 : v < 1 := hv
        have hv0 : v = 0 := by omega
        subst hv0; rfl
      right_inv := fun ⟨l, hl⟩ => Subtype.ext (List.eq_nil_of_length_eq_zero hl).symm }
  | k + 1 =>
    let prev := enumShamirPadPolyGoldilocks k
    { toFun := fun idx =>
        let p := prev.toFun (ucSplitLeft goldilocksPrime_pos idx)
        let c := enumGoldilocks.toFun (ucSplitRight goldilocksPrime_pos idx)
        ⟨c :: p.1, by simp [p.2]⟩
      invFun := fun ⟨l, hl⟩ =>
        let hd := l.headD Goldilocks.zero
        let tl : ShamirPadPoly Goldilocks k := ⟨l.tail, by rw [List.length_tail, hl]; omega⟩
        ucPairFin (prev.invFun tl) (enumGoldilocks.invFun hd)
      left_inv := fun idx => by
        change ucPairFin
            (prev.invFun ⟨(prev.toFun (ucSplitLeft goldilocksPrime_pos idx)).1, _⟩)
            (enumGoldilocks.invFun (enumGoldilocks.toFun (ucSplitRight goldilocksPrime_pos idx))) = idx
        have hSub : (⟨(prev.toFun (ucSplitLeft goldilocksPrime_pos idx)).1,
            (prev.toFun (ucSplitLeft goldilocksPrime_pos idx)).2⟩ : ShamirPadPoly Goldilocks k) =
            prev.toFun (ucSplitLeft goldilocksPrime_pos idx) := by
          cases prev.toFun (ucSplitLeft goldilocksPrime_pos idx); rfl
        rw [hSub, prev.left_inv, enumGoldilocks.left_inv]
        exact ucPair_split goldilocksPrime_pos idx
      right_inv := fun ⟨l, hl⟩ => by
        apply Subtype.ext
        cases l with
        | nil => cases hl
        | cons x xs =>
          have hxs : xs.length = k := Nat.succ.inj hl
          change enumGoldilocks.toFun
              (ucSplitRight goldilocksPrime_pos
                (ucPairFin (prev.invFun ⟨xs, hxs⟩) (enumGoldilocks.invFun x))) ::
            (prev.toFun
              (ucSplitLeft goldilocksPrime_pos
                (ucPairFin (prev.invFun ⟨xs, hxs⟩) (enumGoldilocks.invFun x)))).1 = x :: xs
          rw [ucSplitRight_pair goldilocksPrime_pos, ucSplitLeft_pair goldilocksPrime_pos,
              enumGoldilocks.right_inv, prev.right_inv] }

/-- Degree-`< t` Shamir sacrificial / polynomial consistency check over evaluation points `pts`. -/
def verifyShamirPolyConsistent (t : Nat) (polyCoeffs : List Goldilocks)
    (pts shares : List Goldilocks) : Bool :=
  decide (polyCoeffs.length = t) &&
  decide (pts.length = shares.length) &&
  (List.zip pts shares).all (fun xy => decide (RoundPoly.evalCoeffs polyCoeffs xy.1 = xy.2))

/-- **Degree-`< t` Shamir Consistency Uniqueness (`shamirPolyConsistent_unique_at_zero`)**:
    Any two length-`t` (degree `< t`) polynomials certified by `verifyShamirPolyConsistent` against
    the same share vector `shares` on `≥ t` duplicate-free evaluation points `pts` have **identical**
    reconstructed secret `evalCoeffs P 0 = evalCoeffs Q 0`. -/
theorem shamirPolyConsistent_unique_at_zero (t : Nat)
    (P Q : List Goldilocks) (pts shares : List Goldilocks)
    (hNodup : pts.Nodup) (hQuorum : t ≤ pts.length)
    (hP : verifyShamirPolyConsistent t P pts shares = true)
    (hQ : verifyShamirPolyConsistent t Q pts shares = true) :
    RoundPoly.evalCoeffs P Goldilocks.zero = RoundPoly.evalCoeffs Q Goldilocks.zero := by
  unfold verifyShamirPolyConsistent at hP hQ
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hP hQ
  rcases hP with ⟨⟨hPLen, hPtsLen⟩, hPZip⟩
  rcases hQ with ⟨⟨hQLen, _⟩, hQZip⟩
  cases t with
  | zero =>
    rw [List.eq_nil_of_length_eq_zero hPLen, List.eq_nil_of_length_eq_zero hQLen]
  | succ d =>
    by_cases hEq0 : RoundPoly.evalCoeffs P Goldilocks.zero = RoundPoly.evalCoeffs Q Goldilocks.zero
    · exact hEq0
    · exfalso
      let diff := polySubFixed P Q
      have hDiffLen : diff.length ≤ d + 1 := by
        rw [polySubFixed_length P Q (hPLen.trans hQLen.symm), hPLen]
        exact Nat.le_refl (d + 1)
      have hNz0 : RoundPoly.evalCoeffs diff Goldilocks.zero ≠ CommRingOps.zero := by
        rw [evalCoeffs_subFixed P Q Goldilocks.zero (hPLen.trans hQLen.symm)]
        intro hSub0
        exact hEq0 (LawfulCommRing.sub_eq_zero_iff.mp hSub0)
      have hAgreePts : ∀ x ∈ pts, RoundPoly.evalCoeffs P x = RoundPoly.evalCoeffs Q x := by
        have hZipAll : ∀ (xs ys : List Goldilocks) (x : Goldilocks),
            xs.length = ys.length → x ∈ xs → ∃ y, (x, y) ∈ List.zip xs ys := by
          intro xs
          induction xs with
          | nil =>
            intro _ _ _ hx
            cases hx
          | cons a as ih =>
            intro ys x hLen hx
            cases ys with
            | nil => cases hLen
            | cons b bs =>
              rcases List.mem_cons.mp hx with rfl | hRest
              · exact ⟨b, .head _⟩
              · obtain ⟨y, hy⟩ := ih bs x (Nat.succ.inj hLen) hRest
                exact ⟨y, .tail _ hy⟩
        intro x hx
        obtain ⟨y, hy⟩ := hZipAll pts shares x hPtsLen hx
        exact (hPZip (x, y) hy).trans (hQZip (x, y) hy).symm
      have hFiltAll :
          pts.filter (fun r => decide (RoundPoly.evalCoeffs diff r = CommRingOps.zero)) = pts := by
        apply List.filter_eq_self.mpr
        intro x hx
        rw [decide_eq_true_eq, evalCoeffs_subFixed P Q x (hPLen.trans hQLen.symm),
            hAgreePts x hx, LawfulCommRing.sub_self]
      have hRoots := RoundPoly.roots_nodup_length_le d diff pts hNodup hDiffLen ⟨Goldilocks.zero, hNz0⟩
      rw [hFiltAll] at hRoots
      omega

/-- `#tooth`: Without enforcing the `< t` degree check (`P.length ≤ t`), a degree-`t` polynomial
    (`length = t + 1`) agrees with an honest constant sharing on `t = 1` evaluation point (`x = 1`)
    while forging a distinct reconstructed secret at `x = 0`! -/
theorem tooth_shamir_unbounded_degree_forges_secret_at_zero :
    ∃ (P Q : List Goldilocks) (pt : Goldilocks),
      pt ≠ Goldilocks.zero ∧
      P.length = 1 ∧
      Q.length = 2 ∧
      RoundPoly.evalCoeffs P pt = RoundPoly.evalCoeffs Q pt ∧
      RoundPoly.evalCoeffs P Goldilocks.zero ≠ RoundPoly.evalCoeffs Q Goldilocks.zero := by
  refine ⟨[Goldilocks.one], [Goldilocks.zero, Goldilocks.one], Goldilocks.one, ?_, rfl, rfl, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- Boolean test for whether global SPDZ MAC key `alpha : GoldilocksExt2` is pinned by a gate
    opening deviation `(deltaD, sigmaSum)`. -/
def spdzGatePinsAlpha (alpha : GoldilocksExt2) (deltaD : Goldilocks)
    (sigmaSum : GoldilocksExt2) : Bool :=
  decide (deltaD ≠ Goldilocks.zero ∧
    alpha = CommRingOps.mul sigmaSum (GoldilocksExt2.inv (GoldilocksExt2.ofBase deltaD)))

/-- For any fixed gate deviation `(deltaD, sigmaSum)`, at most `1` of the `p^2` global MAC keys
    in `GoldilocksExt2` satisfies `spdzGatePinsAlpha`. -/
theorem spdzGatePinsAlpha_count_le_one (deltaD : Goldilocks) (sigmaSum : GoldilocksExt2) :
    finSum goldilocksExt2Card
      (fun idx => if spdzGatePinsAlpha (enumGoldilocksExt2.toFun idx) deltaD sigmaSum then 1 else 0) ≤ 1 := by
  apply finSum_indicator_le_one_of_unique
  intro i j hi hj
  unfold spdzGatePinsAlpha at hi hj
  rcases of_decide_eq_true hi with ⟨_, hEqI⟩
  rcases of_decide_eq_true hj with ⟨_, hEqJ⟩
  have hSame : enumGoldilocksExt2.toFun i = enumGoldilocksExt2.toFun j := hEqI.trans hEqJ.symm
  have hInv := congrArg enumGoldilocksExt2.invFun hSame
  rw [enumGoldilocksExt2.left_inv, enumGoldilocksExt2.left_inv] at hInv
  exact hInv

/-- Boolean test for whether any gate in `gates` pins global MAC key `alpha`. -/
def anyGatePinsAlpha (alpha : GoldilocksExt2) (gates : List (Goldilocks × GoldilocksExt2)) : Bool :=
  gates.any (fun g => spdzGatePinsAlpha alpha g.1 g.2)

theorem anyGatePinsAlpha_nil (alpha : GoldilocksExt2) : anyGatePinsAlpha alpha [] = false := by
  rfl

/-- Across `gates.length` active SPDZ gates, at most `gates.length` out of `goldilocksExt2Card`
    global `GoldilocksExt2` MAC keys are pinned. -/
theorem spdzGateStream_pin_count_le :
    ∀ (gates : List (Goldilocks × GoldilocksExt2)),
      finSum goldilocksExt2Card
        (fun idx => if anyGatePinsAlpha (enumGoldilocksExt2.toFun idx) gates then 1 else 0) ≤
        gates.length
  | [] => by
    have hZ : finSum goldilocksExt2Card
        (fun idx => if anyGatePinsAlpha (enumGoldilocksExt2.toFun idx) [] then 1 else 0) =
        finSum goldilocksExt2Card (fun _ => 0) :=
      finSum_congr (fun _ => rfl)
    rw [hZ, finSum_const]
    omega
  | g :: gs => by
    have hOr := finSum_indicator_or_le
      (fun idx => spdzGatePinsAlpha (enumGoldilocksExt2.toFun idx) g.1 g.2)
      (fun idx => anyGatePinsAlpha (enumGoldilocksExt2.toFun idx) gs)
    have hHead := spdzGatePinsAlpha_count_le_one g.1 g.2
    have hTail := spdzGateStream_pin_count_le gs
    have hStep :
        finSum goldilocksExt2Card
          (fun idx => if anyGatePinsAlpha (enumGoldilocksExt2.toFun idx) (g :: gs) then 1 else 0) =
        finSum goldilocksExt2Card
          (fun i => if (spdzGatePinsAlpha (enumGoldilocksExt2.toFun i) g.1 g.2 ||
                        anyGatePinsAlpha (enumGoldilocksExt2.toFun i) gs) then 1 else 0) :=
      finSum_congr (fun _ => rfl)
    rw [hStep]
    exact Nat.le_trans hOr
      (by rw [List.length_cons, Nat.add_comm gs.length 1]; exact Nat.add_le_add hHead hTail)

theorem witness_shamirPolyConsistent_inhabited :
    ∃ (t : Nat) (P Q : List Goldilocks) (pts shares : List Goldilocks),
      pts.Nodup ∧ t ≤ pts.length ∧
      verifyShamirPolyConsistent t P pts shares = true ∧
      verifyShamirPolyConsistent t Q pts shares = true := by
  refine ⟨1, [Goldilocks.one], [Goldilocks.one], [Goldilocks.one], [Goldilocks.one],
    by decide, by decide, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

#tooth_pair Qsag.shamirPolyConsistent_unique_at_zero vs Qsag.tooth_shamir_unbounded_degree_forges_secret_at_zero
#verify_inhabited Qsag.shamirPolyConsistent_unique_at_zero Qsag.witness_shamirPolyConsistent_inhabited

end Qsag
end

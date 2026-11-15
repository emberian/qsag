module
public import Qsag.Exec.RssSigningProgram
import all Qsag.Exec.RssSigningProgram
import all Qsag.Protocol.Threshold.ThresholdMpc
import all Qsag.Protocol.Signing.HashSigs
import Qsag.Tactic.AssuranceKit

/-! Complete resumable production signing control, including both stateful Jorts
and stateless indexed-FORS branches. Only reached cut operations are requested.
Invalid parameters/leaf indices fail before a query; failed grinding stops before
requesting the selected WOTS values. No signing key is captured by the program.
The interpreter equality covers arbitrary oracle answers and both success and
failure, rather than requiring a successful-signature or MatchesKey premise. -/
public section
namespace Qsag.RssSigning
set_option autoImplicit false

def forsPk (suite : TweakableHashSuite) (params : PqHashParams) (pkSeed : Bytes)
    (tree : UInt64) (kp : Nat) : Program Bytes := do
  let roots ← mapProgram (fun j => merkleKp suite pkSeed 0 tree .forsTree (UInt32.ofNat kp)
    (fun u => ask (.forsLeaf tree kp j u)) params.forsHeight j 0) (List.range params.forsTrees)
  pure (thTweakTl suite pkSeed ⟨0, tree, .forsRoots, UInt32.ofNat kp, 0, 0⟩ roots)

@[simp] theorem evaluate_forsPk (o : ProductionPqHashMpcOracles) (suite : TweakableHashSuite)
    (params : PqHashParams) (pkSeed : Bytes) (tree : UInt64) (kp : Nat) :
    evaluate o (forsPk suite params pkSeed tree kp) =
      mpcComputeProductionForsPk suite params o pkSeed tree kp := by
  simp only [forsPk, evaluate_bind, evaluate_mapProgram, evaluate_merkleKp,
    evaluate_ask, answer, evaluate_pure, mpcComputeProductionForsPk]

def forsOpenings (suite : TweakableHashSuite) (params : PqHashParams) (pkSeed : Bytes)
    (tree : UInt64) (kp : Nat) (indices : List Nat) : Program (List ForsTreeOpening) :=
  mapProgram (fun j => do
    let secret ← ask (.forsReveal tree kp j (indices.getD j 0))
    let path ← authPath suite pkSeed 0 tree .forsTree (UInt32.ofNat kp)
      (fun u => ask (.forsLeaf tree kp j u)) params.forsHeight j 0 (indices.getD j 0)
    pure ⟨secret, path⟩) (List.range params.forsTrees)

@[simp] theorem evaluate_forsOpenings (o : ProductionPqHashMpcOracles)
    (suite : TweakableHashSuite) (params : PqHashParams) (pkSeed : Bytes)
    (tree : UInt64) (kp : Nat) (indices : List Nat) :
    evaluate o (forsOpenings suite params pkSeed tree kp indices) =
      mpcBuildProductionForsOpenings suite params o pkSeed tree kp indices := by
  simp only [forsOpenings, evaluate_mapProgram, evaluate_bind, evaluate_ask,
    evaluate_authPath, answer, evaluate_pure, mpcBuildProductionForsOpenings]

def layers (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed pkRoot rRand : Bytes) (maxGrind : Nat) :
    Nat → Nat → Bytes → Nat → Program (Option (List LayerXmssSig))
  | _, _, _, 0 => pure (some [])
  | layerIndex, globalIndex, currentRoot, remaining + 1 =>
    let subLeaves := 2 ^ params.subtreeHeight
    let kp := globalIndex % subLeaves
    let treeIndex := globalIndex / subLeaves
    let tree := UInt64.ofNat treeIndex
    let layer := UInt32.ofNat layerIndex
    let grind :=
      if params.statefulJorts && decide (layerIndex = 0) then
        grindTswLeafCounterAux suite params.w params.ell1 params.targetSum
          rRand pkSeed pkRoot currentRoot tree (UInt32.ofNat kp) 0 maxGrind
      else
        grindTswInternalCounterAux suite params.w params.ell1 params.targetSum
          pkSeed pkRoot currentRoot layer tree (UInt32.ofNat kp) 0 maxGrind
    match grind with
    | none => pure none
    | some (counter, digits, _) => do
      let chains ← mapProgram (fun r => ask (.wotsChain layer tree kp r (digits.getD r 0)))
        (List.range params.ell1)
      let path ← authPath suite pkSeed layer tree .tree 0
        (wotsPk suite params pkSeed layer tree) params.subtreeHeight 0 0 kp
      let nextRoot ← xmssRoot suite params pkSeed layer tree
      let rest ← layers suite params pkSeed pkRoot rRand maxGrind (layerIndex + 1)
        treeIndex nextRoot remaining
      pure (rest.map (fun signatures => ⟨counter, chains, path⟩ :: signatures))

@[simp] theorem evaluate_layers (o : ProductionPqHashMpcOracles) (suite : TweakableHashSuite)
    (params : PqHashParams) (pkSeed pkRoot rRand : Bytes) (maxGrind : Nat)
    (layerIndex globalIndex : Nat) (currentRoot : Bytes) (remaining : Nat) :
    evaluate o (layers suite params pkSeed pkRoot rRand maxGrind layerIndex globalIndex currentRoot remaining) =
      mpcSignProductionHypertreeLayers suite params o pkSeed pkRoot rRand maxGrind
        layerIndex globalIndex currentRoot remaining := by
  induction remaining generalizing layerIndex globalIndex currentRoot with
  | zero => rfl
  | succ remaining ih =>
      simp only [layers, mpcSignProductionHypertreeLayers]
      split <;> simp_all only [evaluate_bind, evaluate_mapProgram, evaluate_ask, answer,
        evaluate_authPath, evaluate_wotsPk, evaluate_xmssRoot, evaluate_pure]
      split <;> simp_all only [Option.map]

def core (suite : TweakableHashSuite) (params : PqHashParams) (pkSeed : Bytes)
    (pk : PqPublicKey) (msg mu rRand : Bytes) (leafIndex : Nat)
    (forsIndices : Option (List Nat)) (maxGrind : Nat) : Program (Option PqHashSig) := do
  let openingAndRoot ←
    if params.statefulJorts then pure (some ([], mu))
    else match forsIndices with
      | none => pure none
      | some indices => do
        let kp := leafIndex % 2 ^ params.subtreeHeight
        let tree := UInt64.ofNat (leafIndex / 2 ^ params.subtreeHeight)
        let openings ← forsOpenings suite params pkSeed tree kp indices
        let root ← forsPk suite params pkSeed tree kp
        pure (some (openings, root))
  match openingAndRoot with
  | none => pure none
  | some (openings, root) => do
    let signatures ← layers suite params pkSeed pk.pkRoot rRand maxGrind 0 leafIndex root params.numLayers
    match signatures with
    | none => pure none
    | some signatures =>
      let sig : PqHashSig := ⟨rRand, 0, leafIndex, openings, signatures⟩
      pure (if verifyProductionPqHashSig suite params pk msg sig then some sig else none)

@[simp] theorem evaluate_core (o : ProductionPqHashMpcOracles) (suite : TweakableHashSuite)
    (params : PqHashParams) (pkSeed : Bytes) (pk : PqPublicKey) (msg mu rRand : Bytes)
    (leafIndex : Nat) (forsIndices : Option (List Nat)) (maxGrind : Nat) :
    evaluate o (core suite params pkSeed pk msg mu rRand leafIndex forsIndices maxGrind) =
      mpcSignProductionHypertreeCore suite params o pkSeed pk msg mu rRand leafIndex forsIndices maxGrind := by
  cases hp : params.statefulJorts <;> cases hi : forsIndices <;>
    simp only [core, mpcSignProductionHypertreeCore, hp, Bool.false_eq_true, ↓reduceIte, evaluate_bind, evaluate_pure, evaluate_forsOpenings,
      evaluate_forsPk, evaluate_layers]
  all_goals split <;> simp_all only [evaluate_pure]

def stateful (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed msg optRand : Bytes) (epoch maxGrind : Nat) : Program (Option PqHashSig) :=
  if !params.statefulJorts || !params.productionWellFormed || !params.productionLeafIdxInRange epoch then
    pure none
  else do
    let pk ← publicKey suite params pkSeed
    let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
    let rRand ← ask (.prfMsg optRand mu)
    core suite params pkSeed pk msg mu rRand epoch none maxGrind

def stateless (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed msg optRand : Bytes) (maxGrind : Nat) : Program (Option PqHashSig) :=
  if params.statefulJorts || !params.productionWellFormed then pure none
  else do
    let pk ← publicKey suite params pkSeed
    let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
    let rRand ← ask (.prfMsg optRand mu)
    match deriveProductionStatelessInputs suite params rRand pk.pkSeed pk.pkRoot mu with
    | none => pure none
    | some (leafIndex, indices) =>
      core suite params pkSeed pk msg mu rRand leafIndex (some indices) maxGrind

theorem evaluate_stateful (o : ProductionPqHashMpcOracles) (suite : TweakableHashSuite)
    (params : PqHashParams) (pkSeed msg optRand : Bytes) (epoch maxGrind : Nat) :
    evaluate o (stateful suite params pkSeed msg optRand epoch maxGrind) =
      mpcEvalProductionStatefulSign suite params o pkSeed msg optRand epoch maxGrind := by
  simp only [stateful, mpcEvalProductionStatefulSign]
  split
  · rfl
  · simp only [evaluate_bind, evaluate_publicKey, evaluate_ask, answer, evaluate_core]

theorem evaluate_stateless (o : ProductionPqHashMpcOracles) (suite : TweakableHashSuite)
    (params : PqHashParams) (pkSeed msg optRand : Bytes) (maxGrind : Nat) :
    evaluate o (stateless suite params pkSeed msg optRand maxGrind) =
      mpcEvalProductionStatelessSign suite params o pkSeed msg optRand maxGrind := by
  simp only [stateless, mpcEvalProductionStatelessSign]
  split
  · rfl
  · simp only [evaluate_bind, evaluate_publicKey, evaluate_ask, answer]
    split <;> simp_all only [evaluate_pure, evaluate_core]

#verify_constructive evaluate_forsPk evaluate_forsOpenings evaluate_layers evaluate_core
  evaluate_stateful evaluate_stateless
end Qsag.RssSigning

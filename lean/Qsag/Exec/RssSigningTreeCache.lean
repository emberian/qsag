module
public import Qsag.Exec.RssSigningBatches
import all Qsag.Exec.RssSigningBatches
import all Qsag.Exec.RssSigningProgram
import all Qsag.Exec.RssProductionProfile
import all Qsag.Protocol.Threshold.ThresholdMpc
import all Qsag.Protocol.Signing.HashSigs
import Qsag.Tactic.AssuranceKit

/-! One grouped WOTS subtree producer followed by public-only root/path work.
Balanced shape is structural, so malformed or missing rows cannot be filled by
secret fallback queries. Public observation below is correctness instrumentation;
active group opening still requires the actual verifier/commit-open protocol. -/
public section
namespace Qsag.RssSigning
set_option autoImplicit false

inductive LeafTree (α : Type) : Nat → Type where
  | leaf (value : α) : LeafTree α 0
  | node {height : Nat} (left right : LeafTree α height) : LeafTree α (height + 1)

def buildLeafTree {α : Type} (f : Nat → α) : (height : Nat) → Nat → LeafTree α height
  | 0, base => .leaf (f base)
  | height + 1, base => .node (buildLeafTree f height (2 * base))
      (buildLeafTree f height (2 * base + 1))

def mapLeafTree {α β : Type} (f : α → β) : {height : Nat} → LeafTree α height → LeafTree β height
  | 0, .leaf value => .leaf (f value)
  | _ + 1, .node left right => .node (mapLeafTree f left) (mapLeafTree f right)

def mapIndexedTree {α β : Type} (f : Nat → α → β) :
    {height : Nat} → Nat → LeafTree α height → LeafTree β height
  | 0, base, .leaf value => .leaf (f base value)
  | _ + 1, base, .node left right => .node (mapIndexedTree f (2 * base) left)
      (mapIndexedTree f (2 * base + 1) right)

theorem mapLeafTree_build {α β : Type} (f : α → β) (g : Nat → α) (height base : Nat) :
    mapLeafTree f (buildLeafTree g height base) = buildLeafTree (fun i => f (g i)) height base := by
  induction height generalizing base with
  | zero => rfl
  | succ height ih => simp only [buildLeafTree, mapLeafTree, ih]

theorem mapIndexedTree_build {α β : Type} (f : Nat → α → β) (g : Nat → α) (height base : Nat) :
    mapIndexedTree f base (buildLeafTree g height base) =
      buildLeafTree (fun i => f i (g i)) height base := by
  induction height generalizing base with
  | zero => rfl
  | succ height ih => simp only [buildLeafTree, mapIndexedTree, ih]

structure UnverifiedTree (height : Nat) where
  nextInvocation : Nat
  batches : LeafTree UnverifiedBatch height

/-- A single grouped workload, with monotonically threaded internal invocation
coordinates and no intermediate answer reconstruction. -/
def produceTree (prepared : Prepared) (material : RssProduction.Material) (tape : ParticipantTape) :
    {height : Nat} → Nat → LeafTree (List Query) height → UnverifiedTree height
  | 0, first, .leaf queries =>
    let batch := produceBatch prepared material tape first queries
    ⟨batch.nextInvocation, .leaf batch⟩
  | _ + 1, first, .node left right =>
    let lhs := produceTree prepared material tape first left
    let rhs := produceTree prepared material tape lhs.nextInvocation right
    ⟨rhs.nextInvocation, .node lhs.batches rhs.batches⟩

def treeQueryCount : {height : Nat} → LeafTree (List Query) height → Nat
  | 0, .leaf queries => queries.length
  | _ + 1, .node left right => treeQueryCount left + treeQueryCount right

theorem produceTree_counter (prepared : Prepared) (material : RssProduction.Material)
    (tape : ParticipantTape) {height : Nat} (plan : LeafTree (List Query) height) (first : Nat) :
    (produceTree prepared material tape first plan).nextInvocation = first + treeQueryCount plan := by
  induction plan generalizing first with
  | leaf queries => exact produceBatch_counter prepared material tape first queries
  | node left right ihl ihr =>
    simp only [produceTree, treeQueryCount, ihr, ihl, Nat.add_assoc]

/-- Observation only after the complete grouped computation; this is not an
unchecked active protocol port. -/
def candidateTree {height : Nat} (tree : UnverifiedTree height) : LeafTree (List Bytes) height :=
  mapLeafTree candidateBatch tree.batches

theorem produceTree_correct (profile : RssProduction.Profile) (request : SessionScheduleReq)
    (tape : ParticipantTape) {height : Nat} (plan : LeafTree (List Query) height) (first : Nat) :
    candidateTree (produceTree (preparePublic profile request) profile.material tape first plan) =
      mapLeafTree (fun queries => queries.map (answer (RssProduction.sharedOracle profile))) plan := by
  induction plan generalizing first with
  | leaf queries =>
    simp only [candidateTree, produceTree, mapLeafTree, produceBatch_correct]
  | node left right ihl ihr =>
    simp only [candidateTree, produceTree, mapLeafTree] at *
    rw [ihl, ihr]

/-- Both routines below receive only public completed leaf bytes. -/
def cacheRoot (pkSeed : Bytes) (layer : UInt32) (tree : UInt64) :
    {height : Nat} → LeafTree Bytes height → Nat → Bytes
  | 0, .leaf value, _ => value
  | height + 1, .node left right, index =>
    thNodeH cshake256Suite pkSeed ⟨layer, tree, .tree, 0, UInt32.ofNat (height + 1), UInt32.ofNat index⟩
      (cacheRoot pkSeed layer tree left (2 * index))
      (cacheRoot pkSeed layer tree right (2 * index + 1))

def cachePath (pkSeed : Bytes) (layer : UInt32) (tree : UInt64) :
    {height : Nat} → LeafTree Bytes height → Nat → Nat → List Bytes
  | 0, .leaf _, _, _ => []
  | height + 1, .node left right, index, localIndex =>
    if localIndex < 2 ^ height then
      cacheRoot pkSeed layer tree right (2 * index + 1) ::
        cachePath pkSeed layer tree left (2 * index) localIndex
    else cacheRoot pkSeed layer tree left (2 * index) ::
      cachePath pkSeed layer tree right (2 * index + 1) (localIndex - 2 ^ height)

theorem cacheRoot_build (pkSeed : Bytes) (layer : UInt32) (tree : UInt64)
    (leaf : Nat → Bytes) (height index base : Nat) :
    cacheRoot pkSeed layer tree (buildLeafTree leaf height base) index =
      computeMerkleNodeKp cshake256Suite pkSeed layer tree .tree 0 leaf height index base := by
  induction height generalizing index base with
  | zero => rfl
  | succ height ih => simp only [buildLeafTree, cacheRoot, computeMerkleNodeKp, ih]

theorem cachePath_build (pkSeed : Bytes) (layer : UInt32) (tree : UInt64)
    (leaf : Nat → Bytes) (height index base selected : Nat) :
    cachePath pkSeed layer tree (buildLeafTree leaf height base) index selected =
      buildMerkleAuthPathKp cshake256Suite pkSeed layer tree .tree 0 leaf height index base selected := by
  induction height generalizing index base selected with
  | zero => rfl
  | succ height ih =>
    simp only [buildLeafTree, cachePath, buildMerkleAuthPathKp, cacheRoot_build, ih]

def wotsTreePlan (params : PqHashParams) (layer : UInt32) (tree : UInt64)
    (selected : Nat) (digits : List Nat) : LeafTree (List Query) params.subtreeHeight :=
  buildLeafTree (wotsRowQueries params layer tree selected digits) params.subtreeHeight 0

def completeWotsCache (params : PqHashParams) (pkSeed : Bytes) (layer : UInt32) (tree : UInt64)
    (selected : Nat) (digits : List Nat) (rows : LeafTree (List Bytes) params.subtreeHeight) :
    LeafTree Bytes params.subtreeHeight :=
  mapIndexedTree (completeWotsRow params pkSeed layer tree selected digits) 0 rows

theorem actual_wots_cache (profile : RssProduction.Profile) (request : SessionScheduleReq)
    (tape : ParticipantTape) (first : Nat) (layer : UInt32) (tree : UInt64) (selected : Nat)
    (digits : List Nat)
    (hCheck : checkTargetSum profile.params.w profile.params.ell1 profile.params.targetSum digits = true) :
    completeWotsCache profile.params profile.material.pkSeed layer tree selected digits
      (candidateTree (produceTree (preparePublic profile request) profile.material tape first
        (wotsTreePlan profile.params layer tree selected digits))) =
      buildLeafTree
        (mpcComputeWotsPk cshake256Suite profile.params (RssProduction.sharedOracle profile).toPqHashMpcOracles
          profile.material.pkSeed layer tree) profile.params.subtreeHeight 0 := by
  rw [produceTree_correct]
  simp only [wotsTreePlan, completeWotsCache, mapLeafTree_build, mapIndexedTree_build]
  have hf := funext (fun kp => completeWotsRow_correct profile layer tree selected kp digits hCheck)
  rw [hf]

theorem actual_wots_cache_root_and_path (profile : RssProduction.Profile) (request : SessionScheduleReq)
    (tape : ParticipantTape) (first : Nat) (layer : UInt32) (tree : UInt64) (selected : Nat)
    (digits : List Nat)
    (hCheck : checkTargetSum profile.params.w profile.params.ell1 profile.params.targetSum digits = true) :
    let cache := completeWotsCache profile.params profile.material.pkSeed layer tree selected digits
      (candidateTree (produceTree (preparePublic profile request) profile.material tape first
        (wotsTreePlan profile.params layer tree selected digits)))
    cacheRoot profile.material.pkSeed layer tree cache 0 =
      mpcComputeXmssSubtreeRoot cshake256Suite profile.params (RssProduction.sharedOracle profile).toPqHashMpcOracles
        profile.material.pkSeed layer tree ∧
    cachePath profile.material.pkSeed layer tree cache 0 selected =
      buildMerkleAuthPathKp cshake256Suite profile.material.pkSeed layer tree .tree 0
        (mpcComputeWotsPk cshake256Suite profile.params (RssProduction.sharedOracle profile).toPqHashMpcOracles
          profile.material.pkSeed layer tree) profile.params.subtreeHeight 0 0 selected := by
  dsimp only
  rw [actual_wots_cache profile request tape first layer tree selected digits hCheck]
  constructor
  · rw [cacheRoot_build, computeMerkleNodeKp_zero_eq]
    rfl
  · exact cachePath_build _ _ _ _ _ _ _ _

#verify_constructive mapLeafTree_build mapIndexedTree_build produceTree_counter produceTree_correct
  cacheRoot_build cachePath_build actual_wots_cache actual_wots_cache_root_and_path
end Qsag.RssSigning

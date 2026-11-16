module
public import Qsag.Exec.RssSigningPublicCompletion
public import Qsag.Exec.RssSigningBackend
public import Qsag.Exec.RssSigningProgram
public import Qsag.Exec.RssProductionProfile
public import Qsag.Protocol.Threshold.ThresholdMpc
public import Qsag.Protocol.Signing.HashSigs
import Qsag.Tactic.AssuranceKit

/-!
The unverified grouped WOTS workload used by the Rust subtree operation:
selected chains stop at their digits; other leaves stop at full endpoints.
The producer accumulates shared answers/evidence without reconstructing any
answer. Public completion is a distinct consumer of the eventual opened rows.
This is not a checked opening capability, packed64 implementation, or a claim
that arbitrary active executions pass the BBCGGI19 verifier.
-/
public section
namespace Qsag.RssSigning
set_option autoImplicit false

structure UnverifiedBatch where
  nextInvocation : Nat
  computations : List UnverifiedAnswer

/-- All query coordinates are already public. Internal invocation identifiers
advance across the group; no answer is reconstructed by this producer. -/
@[expose] def produceBatch (prepared : Prepared) (material : RssProduction.Material)
    (tape : ParticipantTape) : Nat → List Query → UnverifiedBatch
  | first, [] => ⟨first, []⟩
  | first, query :: queries =>
    let computation := queryRun prepared material first query tape
    let rest := produceBatch prepared material tape (first + 1) queries
    ⟨rest.nextInvocation, computation :: rest.computations⟩

/-- External correctness observation, not an executable active release port. -/
@[expose] def candidateBatch (batch : UnverifiedBatch) : List Bytes :=
  batch.computations.map (fun computation => reconstructRssBytes computation.shares)

theorem produceBatch_counter (prepared : Prepared) (material : RssProduction.Material)
    (tape : ParticipantTape) (first : Nat) (queries : List Query) :
    (produceBatch prepared material tape first queries).nextInvocation = first + queries.length := by
  induction queries generalizing first with
  | nil => rfl
  | cons query queries ih =>
    simp only [produceBatch, ih, List.length_cons]
    omega

theorem produceBatch_length (prepared : Prepared) (material : RssProduction.Material)
    (tape : ParticipantTape) (first : Nat) (queries : List Query) :
    (produceBatch prepared material tape first queries).computations.length = queries.length := by
  induction queries generalizing first with
  | nil => rfl
  | cons query queries ih => simp only [produceBatch, List.length_cons, ih]

theorem produceBatch_correct (profile : RssProduction.Profile) (request : SessionScheduleReq)
    (tape : ParticipantTape) (first : Nat) (queries : List Query) :
    candidateBatch (produceBatch (preparePublic profile request) profile.material tape first queries) =
      queries.map (answer (RssProduction.sharedOracle profile)) := by
  induction queries generalizing first with
  | nil => rfl
  | cons query queries ih =>
    simp only [candidateBatch, produceBatch, List.map_cons] at *
    rw [(queryRun_correct profile request first query tape).2, ih]

/-- Every retained hash record names its actual public query and unique internal
invocation; subcall numbering restarts only in the next invocation namespace. -/
@[expose] def BatchNumbered : Nat → List Query → List UnverifiedAnswer → Prop
  | _, [], [] => True
  | first, query :: queries, computation :: computations =>
    HashesFrom first query 0 computation.evidence ∧ BatchNumbered (first + 1) queries computations
  | _, _, _ => False

theorem produceBatch_numbered (prepared : Prepared) (material : RssProduction.Material)
    (tape : ParticipantTape) (first : Nat) (queries : List Query) :
    BatchNumbered first queries (produceBatch prepared material tape first queries).computations := by
  induction queries generalizing first with
  | nil => trivial
  | cons query queries ih =>
    exact ⟨(queryRun_numbered prepared material first query tape).1, ih (first + 1)⟩

/-- The exact public coordinate selection of eval_tsw_wots_subtree_rss.
A row consists of ell1 chain outputs for one leaf. -/
@[expose] def wotsRowQueries (params : PqHashParams) (layer : UInt32) (tree : UInt64)
    (selected : Nat) (digits : List Nat) (kp : Nat) : List Query :=
  (List.range params.ell1).map fun chain =>
    .wotsChain layer tree kp chain (if kp = selected then digits.getD chain 0 else params.w - 1)

@[expose] def wotsSubtreeQueries (params : PqHashParams) (layer : UInt32) (tree : UInt64)
    (selected : Nat) (digits : List Nat) : List Query :=
  ((List.range (2 ^ params.subtreeHeight)).map
    (wotsRowQueries params layer tree selected digits)).flatten

/-- Public-only row completion, after a separately checked grouped opening. -/
@[expose] def completeWotsRow (params : PqHashParams) (pkSeed : Bytes) (layer : UInt32) (tree : UInt64)
    (selected : Nat) (digits : List Nat) (kp : Nat) (values : List Bytes) : Bytes :=
  if kp = selected then completeSelectedLeaf params pkSeed layer tree kp digits values
  else thTweakTl cshake256Suite pkSeed ⟨layer, tree, .wotsPk, UInt32.ofNat kp, 0, 0⟩ values

theorem completeWotsRow_correct (profile : RssProduction.Profile)
    (layer : UInt32) (tree : UInt64) (selected kp : Nat) (digits : List Nat)
    (hCheck : checkTargetSum profile.params.w profile.params.ell1 profile.params.targetSum digits = true) :
    completeWotsRow profile.params profile.material.pkSeed layer tree selected digits kp
      ((wotsRowQueries profile.params layer tree selected digits kp).map
        (answer (RssProduction.sharedOracle profile))) =
      mpcComputeWotsPk cshake256Suite profile.params (RssProduction.sharedOracle profile).toPqHashMpcOracles
        profile.material.pkSeed layer tree kp := by
  by_cases h : kp = selected
  · rw [completeWotsRow, ite_eq_left h]
    have hValues : (wotsRowQueries profile.params layer tree selected digits kp).map
        (answer (RssProduction.sharedOracle profile)) = selectedValues profile layer tree kp digits := by
      simp only [wotsRowQueries, List.map_map, selectedValues]
      apply List.map_congr_left
      intro chain _
      simp only [Function.comp_def, ite_eq_left h, answer]
    rw [hValues]
    exact selectedLeaf_from_actual_cut profile layer tree kp digits hCheck
  · rw [completeWotsRow, ite_eq_right h]
    rw [mpcComputeWotsPk.public_eq_1]
    congr 1
    simp only [wotsRowQueries, List.map_map]
    apply List.map_congr_left
    intro chain _
    simp only [Function.comp_def, ite_eq_right h, answer]

theorem actual_wotsRow_public_completion (profile : RssProduction.Profile)
    (request : SessionScheduleReq) (tape : ParticipantTape) (first : Nat)
    (layer : UInt32) (tree : UInt64) (selected kp : Nat) (digits : List Nat)
    (hCheck : checkTargetSum profile.params.w profile.params.ell1 profile.params.targetSum digits = true) :
    completeWotsRow profile.params profile.material.pkSeed layer tree selected digits kp
      (candidateBatch (produceBatch (preparePublic profile request) profile.material tape first
        (wotsRowQueries profile.params layer tree selected digits kp))) =
      mpcComputeWotsPk cshake256Suite profile.params (RssProduction.sharedOracle profile).toPqHashMpcOracles
        profile.material.pkSeed layer tree kp := by
  rw [produceBatch_correct]
  exact completeWotsRow_correct profile layer tree selected kp digits hCheck

#verify_constructive produceBatch_counter produceBatch_length produceBatch_correct produceBatch_numbered
  completeWotsRow_correct actual_wotsRow_public_completion
end Qsag.RssSigning

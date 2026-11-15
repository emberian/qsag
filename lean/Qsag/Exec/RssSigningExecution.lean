module
public import Qsag.Exec.RssSigningBackend
public import Qsag.Exec.RssSigningMachine
import all Qsag.Exec.RssSigningBackend
import all Qsag.Exec.RssSigningMachine
import all Qsag.Exec.RssSigningControl
import all Qsag.Exec.RssSigningProgram
import all Qsag.Exec.RssProductionProfile
import all Qsag.Protocol.Aggregation.UcGames
import Qsag.Tactic.AssuranceKit

/-!
Full honest participant computation of the demand-driven production program.
Each reached query executes the concrete participant hash backend and retains
all local gate evidence; no table of unused secret PRFs is precomputed. The
external correctness interpreter reconstructs only the requested final cut,
never intermediate WOTS/FORS states. This honest interpreter is NOT the active
release protocol: its replies still require the actual gate-check/commit-open
phase before being wired to the public controller's reply port.
-/
public section
namespace Qsag.RssSigning
set_option autoImplicit false

structure CutEvidence where
  index : Nat
  query : Query
  computation : UnverifiedAnswer

structure Execution (α : Type) where
  nextCut : Nat
  cuts : List CutEvidence
  result : α

def runPrepared {α : Type} (prepared : Prepared) (material : RssProduction.Material)
    (tape : ParticipantTape) : Nat → Program α → Execution α
  | cut, .pure result => ⟨cut, [], result⟩
  | cut, .query query next =>
      let computation := queryRun prepared material cut query tape
      let response := reconstructRssBytes computation.shares
      let rest := runPrepared prepared material tape (cut + 1) (next response)
      ⟨rest.nextCut, ⟨cut, query, computation⟩ :: rest.cuts, rest.result⟩

def CutsFrom : Nat → List CutEvidence → Prop
  | _, [] => True
  | index, cut :: cuts => cut.index = index ∧
      HashesFrom index cut.query 0 cut.computation.evidence ∧ CutsFrom (index + 1) cuts

theorem runPrepared_numbered {α : Type} (prepared : Prepared) (material : RssProduction.Material)
    (tape : ParticipantTape) (first : Nat) (program : Program α) :
    CutsFrom first (runPrepared prepared material tape first program).cuts ∧
    (runPrepared prepared material tape first program).nextCut =
      first + (runPrepared prepared material tape first program).cuts.length := by
  induction program generalizing first with
  | pure result => exact ⟨trivial, (Nat.add_zero first).symm⟩
  | query query next ih =>
      have h := ih (reconstructRssBytes (queryRun prepared material first query tape).shares) (first + 1)
      refine ⟨⟨rfl, (queryRun_numbered prepared material first query tape).1, h.1⟩, ?_⟩
      change (runPrepared prepared material tape (first + 1)
        (next (reconstructRssBytes (queryRun prepared material first query tape).shares))).nextCut = _
      rw [h.2]
      simp only [runPrepared, List.length_cons]
      omega

theorem runPrepared_result {α : Type} (profile : RssProduction.Profile)
    (request : SessionScheduleReq) (tape : ParticipantTape) (first : Nat) (program : Program α) :
    (runPrepared (preparePublic profile request) profile.material tape first program).result =
      evaluate (RssProduction.sharedOracle profile) program := by
  induction program generalizing first with
  | pure result => rfl
  | query query next ih =>
      change (runPrepared (preparePublic profile request) profile.material tape (first + 1)
        (next (reconstructRssBytes
          (queryRun (preparePublic profile request) profile.material first query tape).shares))).result = _
      rw [(queryRun_correct profile request first query tape).2, ih]
      rfl

/-- The retained cut trace is exactly the original production program's reached
oracle-query log, not a caller-supplied or larger precomputed query set. -/
theorem runPrepared_query_log {α : Type} (profile : RssProduction.Profile)
    (request : SessionScheduleReq) (tape : ParticipantTape) (first : Nat) (program : Program α) :
    (runPrepared (preparePublic profile request) profile.material tape first program).cuts.map
      CutEvidence.query = queryLog (answer (RssProduction.sharedOracle profile)) program := by
  induction program generalizing first with
  | pure result => rfl
  | query query next ih =>
      simp only [runPrepared, List.map_cons, queryLog]
      rw [(queryRun_correct profile request first query tape).2, ih]

def signingProgram (profile : RssProduction.Profile) (request : SessionScheduleReq) :
    Program (Option PqHashSig) :=
  if profile.params.statefulJorts then
    stateful cshake256Suite profile.params profile.material.pkSeed (RssProduction.payload profile request)
      request.optRand request.reqEpoch profile.grindLimit
  else
    stateless cshake256Suite profile.params profile.material.pkSeed (RssProduction.payload profile request)
      request.optRand profile.grindLimit

theorem signingProgram_refines (profile : RssProduction.Profile) (request : SessionScheduleReq) :
    evaluate (RssProduction.sharedOracle profile) (signingProgram profile request) =
      RssProduction.sharedSign profile request := by
  simp only [signingProgram, RssProduction.sharedSign]
  split <;> simp only [evaluate_stateful, evaluate_stateless]

def honestSigningExecution (profile : RssProduction.Profile) (request : SessionScheduleReq)
    (tape : ParticipantTape) (first : Nat := 0) : Execution (Option PqHashSig) :=
  runPrepared (preparePublic profile request) profile.material tape first (signingProgram profile request)

theorem honestSigningExecution_refines (profile : RssProduction.Profile) (request : SessionScheduleReq)
    (tape : ParticipantTape) (first : Nat) :
    (honestSigningExecution profile request tape first).result = RssProduction.sharedSign profile request := by
  exact (runPrepared_result profile request tape first (signingProgram profile request)).trans
    (signingProgram_refines profile request)

/-- Actual wire serialization and genuine signing failure are preserved by the
participant-backed honest computation; no signature-success premise is assumed. -/
theorem honestSigningExecution_wire_refines (profile : RssProduction.Profile) (request : SessionScheduleReq)
    (tape : ParticipantTape) (first : Nat) :
    RssProduction.encodeResult profile.params (honestSigningExecution profile request tape first).result =
      RssProduction.partialOutput profile request := by
  rw [honestSigningExecution_refines]
  rfl

/-- Once the honest computation's final cut is supplied, the resumable controller
preserves its reference meaning. Active acceptance of that cut is not assumed or
claimed by this computation lemma. -/
theorem participant_reply_refines {α : Type} (profile : RssProduction.Profile)
    (request : SessionScheduleReq) (tape : ParticipantTape) (state : State α) (cut : Nat)
    (query : Query) (next : Bytes → Program α) (h : state.phase = .waiting cut query next) :
    meaning (RssProduction.sharedOracle profile)
      (step state (.reply cut (reconstructRssBytes
        (queryRun (preparePublic profile request) profile.material cut query tape).shares))).1 =
      meaning (RssProduction.sharedOracle profile) state := by
  rw [(queryRun_correct profile request cut query tape).2]
  exact honest_reply_refines _ _ _ _ _ h

#verify_constructive runPrepared_numbered runPrepared_result runPrepared_query_log signingProgram_refines
  honestSigningExecution_refines honestSigningExecution_wire_refines participant_reply_refines
end Qsag.RssSigning

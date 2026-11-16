module
public import Qsag.Spec.Algebra
public import Qsag.Spec.Refines
/-
# Qsag.Tests.DistributedCustodyChecks — 2-of-3 runs of the distributed custody machine

Kernel-evaluated executions of `Qsag.DistCustody.step` over `ZMod 257` for deployment `7`, with the
dealer polynomial `42 + 7 X`, evaluation points `p ↦ p + 1`, the identity share commitment and the
transparent digest:

* the honest run (two approvals, then `execute`) releases a signature under the dealt key `42`,
  reconstructed from the two buffered shares, and a retry replays it from the WAL;
* approvals for deployment `8` are refused by the custodian and ignored by the coordinator;
* a corrupted custodian with its real share and one honest custodian form a quorum, exactly as in
  the ideal functionality; a forged share does not;
* once the approval messages are dropped, the coordinator rejects an `execute` that the ideal
  functionality accepts: the refinement carries no liveness;
* teeth: a constant (non-binding) commitment, duplicate evaluation points, and the evaluation
  point `0` each break the property that `Deployment.WellFormed` is there to give.
-/

public import Qsag.Custody.DistributedThresholdCustodyRefinement
import all Qsag.Custody.DistributedThresholdCustodyRefinement
import all Qsag.Protocol.Threshold.ParametricThresholdAndUnlinkableQsa
import all Qsag.Spec.IdealCustody
import all Qsag.Math.Primality
import Qsag.Tactic.AssuranceKit

namespace Qsag.DistCustody.Checks

open Qsag Qsag.Spec Qsag.DistCustody

set_option autoImplicit false
set_option maxRecDepth 1000000

abbrev F257 : Type := ZMod 257
abbrev ToyDigest : Type := Nat × CustodyIntent
abbrev ToySig : Type := F257 × ToyDigest

def toyQuorum : CustodyQuorumProfile where
  numParties := 3
  threshold := 2
  spendCap := 100
  h_pos := by decide
  h_le := by decide

def toyPoly : List F257 := [ZMod.ofNat 257 42, ZMod.ofNat 257 7]

def toyPoint (p : Nat) : F257 := ZMod.ofNat 257 (p + 1)

/-- Deployment `7`: identity commitment, commitments to the dealt shares. -/
def toyDep : Deployment F257 F257 Unit ToyDigest ToySig where
  deploymentId := 7
  pk := ()
  quorum := toyQuorum
  point := toyPoint
  poly := toyPoly
  commit := fun s => s
  shareCommitment := fun p => RoundPoly.evalCoeffs toyPoly (toyPoint p)
  digests := CustodyDigestScheme.transparent
  signWith := fun k d => (k, d)

/-- The same deployment with a constant commitment: every share opens every commitment. -/
def toyDepNonBinding : Deployment F257 F257 Unit ToyDigest ToySig :=
  { toyDep with commit := fun _ => ZMod.ofNat 257 0, shareCommitment := fun _ => ZMod.ofNat 257 0 }

/-- The same deployment with all custodians at the evaluation point `1`. -/
def toyDepDuplicatePoints : Deployment F257 F257 Unit ToyDigest ToySig :=
  { toyDep with
    point := fun _ => ZMod.ofNat 257 1
    shareCommitment := fun _ => RoundPoly.evalCoeffs toyPoly (ZMod.ofNat 257 1) }

theorem toyPoints_nodup : ((List.range 3).map toyPoint).Nodup := by
  decide +kernel

theorem toyPoints_nonzero : ∀ p, p < 3 → ¬ (toyPoint p = CommRingOps.zero) := by
  decide +kernel

theorem toyDep_wellFormed : toyDep.WellFormed where
  points_nodup := toyPoints_nodup
  points_nonzero := toyPoints_nonzero
  degree := by decide
  commitments_dealt _ _ := rfl
  commit_binding _ _ h := h

/-- Outputs of a schedule (`none` marks a rejected turn). -/
def runOutputs (dep : Deployment F257 F257 Unit ToyDigest ToySig) :
    State F257 Unit ToyDigest ToySig → List (Turn F257) → List (Option (Event F257 ToySig))
  | _, [] => []
  | st, turn :: rest =>
    match step dep st turn with
    | some (st', ev) => some ev :: runOutputs dep st' rest
    | none => none :: runOutputs dep st rest

/-- Outputs of the ideal functionality for deployment `7` on a list of inputs. -/
def idealOutputs (oracle : ToyDigest → ToySig) :
    IdealCustodyState Unit ToyDigest ToySig → List CustodyInput →
      List (Option (CustodyOutcome ToySig))
  | _, [] => []
  | st, inp :: rest =>
    match idealCustodyStep CustodyDigestScheme.transparent oracle st inp with
    | some (st', out) => some out :: idealOutputs oracle st' rest
    | none => none :: idealOutputs oracle st rest

def toyIntent : CustodyIntent where
  sessionId := 1
  round := 0
  epoch := 0
  spend := 10
  payload := [1, 2, 3]

/-- The dealt share of custodian `2`: `42 + 7 * 3 = 63`. -/
def share2 : F257 := ZMod.ofNat 257 63

def realShareMsg : Approval F257 where
  sender := 2
  deploymentId := 7
  intent := toyIntent
  share := share2

def forgedShareMsg : Approval F257 := { realShareMsg with share := ZMod.ofNat 257 99 }

/-- Honest 2-of-3 run: the released signature is the dealt key `42` on `digest 7 toyIntent`, and a
    retry of the committed epoch after a crash replays it from the WAL. -/
theorem honest_run_releases_under_dealt_key :
    runOutputs toyDep (State.init toyDep)
        [.approve 0 7 toyIntent, .approve 1 7 toyIntent, .execute 7 [0, 1] toyIntent false,
         .crash 0, .execute 7 [] toyIntent false] =
      [some .approved, some .approved,
       some (.custody (.released (ZMod.ofNat 257 42, (7, toyIntent)))),
       some .recovered,
       some (.custody (.replayedFromWal (ZMod.ofNat 257 42, (7, toyIntent))))] := by
  decide +kernel

/-- The custodian's latch refuses a second intent at a latched epoch. -/
theorem latched_epoch_is_not_reapproved :
    runOutputs toyDep (State.init toyDep)
        [.approve 0 7 toyIntent,
         .approve 0 7 { toyIntent with sessionId := 2, payload := [9] }] =
      [some .approved, none] := by
  decide +kernel

/-- Deployment binding at the custodian: a request for deployment `8` is not approved, and an
    `execute` naming deployment `8` is rejected. -/
theorem other_deployment_is_refused :
    runOutputs toyDep (State.init toyDep)
        [.approve 0 8 toyIntent, .approve 0 7 toyIntent, .approve 1 7 toyIntent,
         .execute 8 [0, 1] toyIntent false] =
      [none, some .approved, some .approved, none] := by
  decide +kernel

/-- Deployment binding at the coordinator: a corrupted custodian's real share in a message for
    deployment `8` does not count towards a quorum of deployment `7`; the same share in a message
    for deployment `7` does. -/
theorem injected_other_deployment_message_is_not_counted :
    runOutputs toyDep (State.init toyDep)
        [.corrupt 2, .approve 0 7 toyIntent, .inject { realShareMsg with deploymentId := 8 },
         .execute 7 [0, 2] toyIntent false, .inject realShareMsg,
         .execute 7 [0, 2] toyIntent false] =
      [some (.corrupted share2 []), some .approved, some .injected, none, some .injected,
       some (.custody (.released (ZMod.ofNat 257 42, (7, toyIntent))))] := by
  decide +kernel

/-- A forged share from the corrupted custodian does not form a quorum. -/
theorem forged_share_is_rejected :
    runOutputs toyDep (State.init toyDep)
        [.corrupt 2, .approve 0 7 toyIntent, .inject forgedShareMsg,
         .execute 7 [0, 2] toyIntent false] =
      [some (.corrupted share2 []), some .approved, some .injected, none] := by
  decide +kernel

/-- An honest sender's approval cannot be injected, and a second corruption is over budget. -/
theorem honest_sender_cannot_be_injected :
    runOutputs toyDep (State.init toyDep)
        [.inject { realShareMsg with sender := 1 }, .corrupt 2, .corrupt 1] =
      [none, some (.corrupted share2 []), none] := by
  decide +kernel

/-- Corruption reveals the custodian's durable approval log, which is what the ideal
    functionality reveals. -/
theorem corruption_reveals_latched_intents :
    runOutputs toyDep (State.init toyDep) [.approve 2 7 toyIntent, .corrupt 2] =
      [some .approved, some (.corrupted share2 [toyIntent])] ∧
    idealOutputs toyDep.idealOracle (IdealCustodyState.init 7 () toyQuorum)
        [.approve 2 7 toyIntent, .corrupt 2] =
      [some .approvalRecorded, some (.corrupted [toyIntent])] := by
  decide +kernel

/-- No liveness: after both approval messages are dropped the coordinator rejects the `execute`,
    while the ideal functionality, which recorded both permits, releases. -/
theorem dropped_approvals_block_release_that_ideal_accepts :
    runOutputs toyDep (State.init toyDep)
        [.approve 0 7 toyIntent, .approve 1 7 toyIntent, .dropMsg 0, .dropMsg 0,
         .execute 7 [0, 1] toyIntent false] =
      [some .approved, some .approved, some .dropped, some .dropped, none] ∧
    idealOutputs toyDep.idealOracle (IdealCustodyState.init 7 () toyQuorum)
        [.approve 0 7 toyIntent, .approve 1 7 toyIntent, .sign 7 toyIntent false] =
      [some .approvalRecorded, some .approvalRecorded,
       some (.released (ZMod.ofNat 257 42, (7, toyIntent)))] := by
  decide +kernel

/-- The refinement theorem applies to `toyDep`: its hypotheses are inhabited. -/
theorem toyDep_trace_inclusion {tr : List (Turn F257 × Event F257 ToySig)}
    (h : (distMachine toyDep).AdmitsTrace tr) :
    (idealCustodyMachine toyDep.digests toyDep.idealOracle 7 () toyQuorum).AdmitsTrace
      (projectTrace (visIn toyDep) visOut tr) :=
  distCustody_trace_inclusion toyDep toyDep_wellFormed h

/-- Lagrange completeness on `toyDep`: every pair of distinct custodians reconstructs `42`. -/
theorem toyDep_every_pair_reconstructs :
    ∀ ps ∈ [[0, 1], [0, 2], [1, 2], [2, 0], [0, 1, 2]],
      reconstruct (ps.map toyDep.point) (ps.map toyDep.trueShare) = ZMod.ofNat 257 42 := by
  decide +kernel

/-! ## Teeth -/

/-- Tooth for `commit_binding`: with a constant commitment the forged share passes the check and
    the same schedule releases under the key `24`. -/
theorem tooth_nonbinding_commitment_releases_under_wrong_key :
    runOutputs toyDepNonBinding (State.init toyDepNonBinding)
        [.corrupt 2, .approve 0 7 toyIntent, .inject forgedShareMsg,
         .execute 7 [0, 2] toyIntent false] =
      [some (.corrupted share2 []), some .approved, some .injected,
       some (.custody (.released (ZMod.ofNat 257 24, (7, toyIntent))))] := by
  decide +kernel

/-- Tooth for `verifyShare_sound`: under the constant commitment a share that passes the public
    check is not the dealt share. -/
theorem tooth_nonbinding_commitment_accepts_wrong_share :
    ¬ (toyDepNonBinding.verifyShare 2 (ZMod.ofNat 257 99) = true →
        ZMod.ofNat 257 99 = toyDepNonBinding.trueShare 2) := by
  decide +kernel

/-- Tooth for `distCustody_trace_inclusion`: the ideal functionality for the non-binding
    deployment never outputs the signature that the concrete run released. -/
theorem tooth_nonbinding_release_is_not_ideal :
    ¬ (idealOutputs toyDepNonBinding.idealOracle (IdealCustodyState.init 7 () toyQuorum)
        [.corrupt 2, .approve 0 7 toyIntent, .advApprove 2 7 toyIntent,
         .sign 7 toyIntent false] =
      [some (.corrupted []), some .approvalRecorded, some .approvalRecorded,
       some (.released (ZMod.ofNat 257 24, (7, toyIntent)))]) := by
  decide +kernel

/-- Tooth for `points_nodup`: with duplicate evaluation points two dealt shares do not
    reconstruct the dealt key. -/
theorem tooth_duplicate_points_do_not_reconstruct :
    ¬ (reconstruct ([0, 1].map toyDepDuplicatePoints.point)
          ([0, 1].map toyDepDuplicatePoints.trueShare) = toyDepDuplicatePoints.secret) := by
  decide +kernel

/-- Tooth for `points_nonzero`: at the evaluation point `0` the share is the constant term, so no
    choice of the other coefficients makes the keys `42` and `43` give the same share. -/
theorem tooth_zero_point_share_is_the_key (tail tail' : List F257) :
    ¬ (RoundPoly.evalCoeffs (ZMod.ofNat 257 43 :: tail') (CommRingOps.zero : F257) =
        RoundPoly.evalCoeffs (ZMod.ofNat 257 42 :: tail) (CommRingOps.zero : F257)) := by
  rw [RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_cons, LawfulCommRing.zero_mul,
    LawfulCommRing.zero_mul, LawfulCommRing.add_zero, LawfulCommRing.add_zero]
  decide +kernel

#verify_constructive
  Qsag.DistCustody.Checks.toyDep_wellFormed
  Qsag.DistCustody.Checks.honest_run_releases_under_dealt_key
  Qsag.DistCustody.Checks.latched_epoch_is_not_reapproved
  Qsag.DistCustody.Checks.other_deployment_is_refused
  Qsag.DistCustody.Checks.injected_other_deployment_message_is_not_counted
  Qsag.DistCustody.Checks.forged_share_is_rejected
  Qsag.DistCustody.Checks.honest_sender_cannot_be_injected
  Qsag.DistCustody.Checks.corruption_reveals_latched_intents
  Qsag.DistCustody.Checks.dropped_approvals_block_release_that_ideal_accepts
  Qsag.DistCustody.Checks.toyDep_trace_inclusion
  Qsag.DistCustody.Checks.toyDep_every_pair_reconstructs
  Qsag.DistCustody.Checks.tooth_nonbinding_commitment_releases_under_wrong_key
  Qsag.DistCustody.Checks.tooth_nonbinding_commitment_accepts_wrong_share
  Qsag.DistCustody.Checks.tooth_nonbinding_release_is_not_ideal
  Qsag.DistCustody.Checks.tooth_duplicate_points_do_not_reconstruct
  Qsag.DistCustody.Checks.tooth_zero_point_share_is_the_key

#tooth_pair Qsag.DistCustody.verifyShare_sound vs
  Qsag.DistCustody.Checks.tooth_nonbinding_commitment_accepts_wrong_share
#tooth_pair Qsag.DistCustody.reconstruct_dealt_shares vs
  Qsag.DistCustody.Checks.tooth_duplicate_points_do_not_reconstruct

end Qsag.DistCustody.Checks

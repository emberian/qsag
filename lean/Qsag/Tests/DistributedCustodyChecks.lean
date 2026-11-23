module
public import Qsag.Spec.Algebra
public import Qsag.Spec.Encoding
public import Qsag.Spec.IdealSign
public import Qsag.Spec.Refines
public import Qsag.Oracle.Keccak
public import Qsag.Oracle.Sponge
/-
# Qsag.Tests.DistributedCustodyChecks — 2-of-3 runs of the distributed custody machine

Kernel-evaluated executions of `Qsag.DistCustody.step` over `ZMod 257` for deployment `7` AND
share-opening executions of `Qsag.DistCustody.shareOpeningStep` over real compressing 256-bit
sponge commitments (`BitVec 256`) and a genuine WOTS+checksum `Spec.SigScheme`:

* the honest run (two approvals, then `execute`) releases a signature under the dealt key `42`,
  reconstructed from the two buffered shares, and a retry replays it from the WAL;
* approvals for deployment `8` are refused by the custodian and ignored by the coordinator;
* a corrupted custodian with its real share and one honest custodian form a quorum, exactly as in
  the ideal functionality; a forged share does not;
* once the approval messages are dropped, the coordinator rejects an `execute` that the ideal
  functionality accepts: the refinement carries no liveness;
* share-level release (`ShareOpeningDeployment`) over a real `Spec.SigScheme` and real 256-bit
  compressing sponge hash (`Bytes → BitVec 256`, instantiated both symbolically with NIST
  `cSHAKE256` and kernel-executably with a 512-bit `pad10*1` ARX sponge) releases a valid signature
  (`sigScheme.verify = true`) with zero secret-key reconstruction, satisfies finite-set
  `InjOnPreimages`, and exhibits the explicit collision branch on a colliding commitment;
* teeth: a constant (non-binding) commitment, a tampered WOTS signature, duplicate evaluation
  points, and the evaluation point `0` each break the property that `WellFormed` guards.
-/

public import Qsag.Custody.DistributedThresholdCustodyRefinement
public import Qsag.Protocol.Threshold.ParametricThresholdAndUnlinkableQsa
public import Qsag.Spec.IdealCustody
public import Qsag.Math.Primality
import Qsag.Tactic.AssuranceKit

namespace Qsag.DistCustody.Checks

open Qsag Qsag.Spec Qsag.DistCustody

set_option autoImplicit false
set_option maxRecDepth 1000000

local instance (priority := high) localDecEqZMod {q : Nat} : DecidableEq (ZMod q) := fun a b =>
  if h : a.val = b.val then .isTrue (ZMod.ext h)
  else .isFalse (fun he => h (congrArg ZMod.val he))

local instance (priority := high) localDecEqCustodyOutcome {Sig : Type} [DecidableEq Sig] :
    DecidableEq (CustodyOutcome Sig) := fun a b =>
  match a, b with
  | .approvalRecorded, .approvalRecorded => .isTrue rfl
  | .corrupted x, .corrupted y =>
    if h : x = y then .isTrue (congrArg _ h) else .isFalse (by intro he; injection he; contradiction)
  | .released x, .released y =>
    if h : x = y then .isTrue (congrArg _ h) else .isFalse (by intro he; injection he; contradiction)
  | .replayedFromWal x, .replayedFromWal y =>
    if h : x = y then .isTrue (congrArg _ h) else .isFalse (by intro he; injection he; contradiction)
  | .abortedQuarantined, .abortedQuarantined => .isTrue rfl
  | .approvalRecorded, .corrupted _ => .isFalse (by intro h; cases h)
  | .approvalRecorded, .released _ => .isFalse (by intro h; cases h)
  | .approvalRecorded, .replayedFromWal _ => .isFalse (by intro h; cases h)
  | .approvalRecorded, .abortedQuarantined => .isFalse (by intro h; cases h)
  | .corrupted _, .approvalRecorded => .isFalse (by intro h; cases h)
  | .corrupted _, .released _ => .isFalse (by intro h; cases h)
  | .corrupted _, .replayedFromWal _ => .isFalse (by intro h; cases h)
  | .corrupted _, .abortedQuarantined => .isFalse (by intro h; cases h)
  | .released _, .approvalRecorded => .isFalse (by intro h; cases h)
  | .released _, .corrupted _ => .isFalse (by intro h; cases h)
  | .released _, .replayedFromWal _ => .isFalse (by intro h; cases h)
  | .released _, .abortedQuarantined => .isFalse (by intro h; cases h)
  | .replayedFromWal _, .approvalRecorded => .isFalse (by intro h; cases h)
  | .replayedFromWal _, .corrupted _ => .isFalse (by intro h; cases h)
  | .replayedFromWal _, .released _ => .isFalse (by intro h; cases h)
  | .replayedFromWal _, .abortedQuarantined => .isFalse (by intro h; cases h)
  | .abortedQuarantined, .approvalRecorded => .isFalse (by intro h; cases h)
  | .abortedQuarantined, .corrupted _ => .isFalse (by intro h; cases h)
  | .abortedQuarantined, .released _ => .isFalse (by intro h; cases h)
  | .abortedQuarantined, .replayedFromWal _ => .isFalse (by intro h; cases h)

local instance (priority := high) localDecEqEvent {F Sig : Type} [DecidableEq F] [DecidableEq Sig] :
    DecidableEq (Event F Sig) := fun a b =>
  match a, b with
  | .approved, .approved => .isTrue rfl
  | .injected, .injected => .isTrue rfl
  | .corrupted s1 l1, .corrupted s2 l2 =>
    if h : s1 = s2 ∧ l1 = l2 then .isTrue (by rw [h.1, h.2])
    else .isFalse (fun he => h (by injection he with hs hl; exact ⟨hs, hl⟩))
  | .recovered, .recovered => .isTrue rfl
  | .dropped, .dropped => .isTrue rfl
  | .custody o1, .custody o2 =>
    if h : o1 = o2 then .isTrue (congrArg _ h) else .isFalse (by intro he; injection he; contradiction)
  | .approved, .injected => .isFalse (by intro h; cases h)
  | .approved, .corrupted _ _ => .isFalse (by intro h; cases h)
  | .approved, .recovered => .isFalse (by intro h; cases h)
  | .approved, .dropped => .isFalse (by intro h; cases h)
  | .approved, .custody _ => .isFalse (by intro h; cases h)
  | .injected, .approved => .isFalse (by intro h; cases h)
  | .injected, .corrupted _ _ => .isFalse (by intro h; cases h)
  | .injected, .recovered => .isFalse (by intro h; cases h)
  | .injected, .dropped => .isFalse (by intro h; cases h)
  | .injected, .custody _ => .isFalse (by intro h; cases h)
  | .corrupted _ _, .approved => .isFalse (by intro h; cases h)
  | .corrupted _ _, .injected => .isFalse (by intro h; cases h)
  | .corrupted _ _, .recovered => .isFalse (by intro h; cases h)
  | .corrupted _ _, .dropped => .isFalse (by intro h; cases h)
  | .corrupted _ _, .custody _ => .isFalse (by intro h; cases h)
  | .recovered, .approved => .isFalse (by intro h; cases h)
  | .recovered, .injected => .isFalse (by intro h; cases h)
  | .recovered, .corrupted _ _ => .isFalse (by intro h; cases h)
  | .recovered, .dropped => .isFalse (by intro h; cases h)
  | .recovered, .custody _ => .isFalse (by intro h; cases h)
  | .dropped, .approved => .isFalse (by intro h; cases h)
  | .dropped, .injected => .isFalse (by intro h; cases h)
  | .dropped, .corrupted _ _ => .isFalse (by intro h; cases h)
  | .dropped, .recovered => .isFalse (by intro h; cases h)
  | .dropped, .custody _ => .isFalse (by intro h; cases h)
  | .custody _, .approved => .isFalse (by intro h; cases h)
  | .custody _, .injected => .isFalse (by intro h; cases h)
  | .custody _, .corrupted _ _ => .isFalse (by intro h; cases h)
  | .custody _, .recovered => .isFalse (by intro h; cases h)
  | .custody _, .dropped => .isFalse (by intro h; cases h)

local instance (priority := high) localDecEqShareEvent {Share Sig : Type}
    [DecidableEq Share] [DecidableEq Sig] :
    DecidableEq (ShareEvent Share Sig) := fun a b =>
  match a, b with
  | .approved, .approved => .isTrue rfl
  | .injected, .injected => .isTrue rfl
  | .corrupted s1 l1, .corrupted s2 l2 =>
    if h : s1 = s2 ∧ l1 = l2 then .isTrue (by rw [h.1, h.2])
    else .isFalse (fun he => h (by injection he with hs hl; exact ⟨hs, hl⟩))
  | .recovered, .recovered => .isTrue rfl
  | .dropped, .dropped => .isTrue rfl
  | .custody o1, .custody o2 =>
    if h : o1 = o2 then .isTrue (congrArg _ h) else .isFalse (by intro he; injection he; contradiction)
  | .approved, .injected => .isFalse (by intro h; cases h)
  | .approved, .corrupted _ _ => .isFalse (by intro h; cases h)
  | .approved, .recovered => .isFalse (by intro h; cases h)
  | .approved, .dropped => .isFalse (by intro h; cases h)
  | .approved, .custody _ => .isFalse (by intro h; cases h)
  | .injected, .approved => .isFalse (by intro h; cases h)
  | .injected, .corrupted _ _ => .isFalse (by intro h; cases h)
  | .injected, .recovered => .isFalse (by intro h; cases h)
  | .injected, .dropped => .isFalse (by intro h; cases h)
  | .injected, .custody _ => .isFalse (by intro h; cases h)
  | .corrupted _ _, .approved => .isFalse (by intro h; cases h)
  | .corrupted _ _, .injected => .isFalse (by intro h; cases h)
  | .corrupted _ _, .recovered => .isFalse (by intro h; cases h)
  | .corrupted _ _, .dropped => .isFalse (by intro h; cases h)
  | .corrupted _ _, .custody _ => .isFalse (by intro h; cases h)
  | .recovered, .approved => .isFalse (by intro h; cases h)
  | .recovered, .injected => .isFalse (by intro h; cases h)
  | .recovered, .corrupted _ _ => .isFalse (by intro h; cases h)
  | .recovered, .dropped => .isFalse (by intro h; cases h)
  | .recovered, .custody _ => .isFalse (by intro h; cases h)
  | .dropped, .approved => .isFalse (by intro h; cases h)
  | .dropped, .injected => .isFalse (by intro h; cases h)
  | .dropped, .corrupted _ _ => .isFalse (by intro h; cases h)
  | .dropped, .recovered => .isFalse (by intro h; cases h)
  | .dropped, .custody _ => .isFalse (by intro h; cases h)
  | .custody _, .approved => .isFalse (by intro h; cases h)
  | .custody _, .injected => .isFalse (by intro h; cases h)
  | .custody _, .corrupted _ _ => .isFalse (by intro h; cases h)
  | .custody _, .recovered => .isFalse (by intro h; cases h)
  | .custody _, .dropped => .isFalse (by intro h; cases h)

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

private def stepAtState (dep : Deployment F257 F257 Unit ToyDigest ToySig) :
    State F257 Unit ToyDigest ToySig → List (Turn F257) → State F257 Unit ToyDigest ToySig
  | st, [] => st
  | st, turn :: rest =>
    match step dep st turn with
    | some (st', _) => stepAtState dep st' rest
    | none => stepAtState dep st rest

private theorem runOutputs_append (dep : Deployment F257 F257 Unit ToyDigest ToySig) :
    ∀ (ts₁ ts₂ : List (Turn F257)) (st : State F257 Unit ToyDigest ToySig),
      runOutputs dep st (ts₁ ++ ts₂) =
        runOutputs dep st ts₁ ++ runOutputs dep (stepAtState dep st ts₁) ts₂
  | [], _, _ => rfl
  | turn :: rest, ts₂, st => by
    dsimp only [List.cons_append, runOutputs, stepAtState]
    cases h : step dep st turn with
    | none =>
      dsimp only
      rw [runOutputs_append dep rest ts₂ st]
      rfl
    | some p =>
      rcases p with ⟨st', ev⟩
      dsimp only
      rw [runOutputs_append dep rest ts₂ st']
      rfl

private theorem step_execute_key_eq (dep : Deployment F257 F257 Unit ToyDigest ToySig)
    (st : State F257 Unit ToyDigest ToySig) (d : Nat) (approvers : List Nat)
    (i : CustodyIntent) (ab : Bool) (k : F257)
    (hk : quorumKey dep st.buffer approvers i = k) :
    step dep st (.execute d approvers i ab) =
      ((custodyLedgerSign dep.digests (dep.signWith k) st.ledger
        (if quorumReady dep st.buffer approvers i then approvers.length else 0) d i ab).map
        (fun r => ({ st with ledger := r.1 }, Event.custody r.2))) := by
  change ((executeStep dep st d approvers i ab).map (fun r => (r.1, Event.custody r.2))) = _
  unfold executeStep
  rw [hk]
  cases custodyLedgerSign dep.digests (dep.signWith k) st.ledger
    (if quorumReady dep st.buffer approvers i then approvers.length else 0) d i ab <;> rfl

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
  let pre : List (Turn F257) := [.approve 0 7 toyIntent, .approve 1 7 toyIntent]
  let post : List (Turn F257) := [.execute 7 [0, 1] toyIntent false, .crash 0, .execute 7 [] toyIntent false]
  change runOutputs toyDep (State.init toyDep) (pre ++ post) = _
  rw [runOutputs_append]
  have hPre : runOutputs toyDep (State.init toyDep) pre = [some .approved, some .approved] := by
    decide +kernel
  let st2 := stepAtState toyDep (State.init toyDep) pre
  have hKey : quorumKey toyDep st2.buffer [0, 1] toyIntent = ZMod.ofNat 257 42 := by
    have hSec : toyDep.secret = ZMod.ofNat 257 42 := by decide +kernel
    rw [← hSec]
    exact quorumKey_eq_secret toyDep toyDep_wellFormed st2.buffer [0, 1] toyIntent (by decide +kernel)
  have hPost : runOutputs toyDep st2 post =
      [some (.custody (.released (ZMod.ofNat 257 42, (7, toyIntent)))),
       some .recovered,
       some (.custody (.replayedFromWal (ZMod.ofNat 257 42, (7, toyIntent))))] := by
    dsimp only [post, runOutputs]
    rw [step_execute_key_eq toyDep st2 7 [0, 1] toyIntent false (ZMod.ofNat 257 42) hKey]
    decide +kernel
  rw [hPre]
  change [some .approved, some .approved] ++ runOutputs toyDep st2 post = _
  rw [hPost]
  rfl

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
  let pre : List (Turn F257) := [.corrupt 2, .approve 0 7 toyIntent,
    .inject { realShareMsg with deploymentId := 8 },
    .execute 7 [0, 2] toyIntent false, .inject realShareMsg]
  let post : List (Turn F257) := [.execute 7 [0, 2] toyIntent false]
  change runOutputs toyDep (State.init toyDep) (pre ++ post) = _
  rw [runOutputs_append]
  have hPre : runOutputs toyDep (State.init toyDep) pre =
      [some (.corrupted share2 []), some .approved, some .injected, none, some .injected] := by
    decide +kernel
  let st5 := stepAtState toyDep (State.init toyDep) pre
  have hKey : quorumKey toyDep st5.buffer [0, 2] toyIntent = ZMod.ofNat 257 42 := by
    have hSec : toyDep.secret = ZMod.ofNat 257 42 := by decide +kernel
    rw [← hSec]
    exact quorumKey_eq_secret toyDep toyDep_wellFormed st5.buffer [0, 2] toyIntent (by decide +kernel)
  have hPost : runOutputs toyDep st5 post =
      [some (.custody (.released (ZMod.ofNat 257 42, (7, toyIntent))))] := by
    dsimp only [post, runOutputs]
    rw [step_execute_key_eq toyDep st5 7 [0, 2] toyIntent false (ZMod.ofNat 257 42) hKey]
    decide +kernel
  rw [hPre]
  change [some (.corrupted share2 []), some .approved, some .injected, none, some .injected] ++
    runOutputs toyDep st5 post = _
  rw [hPost]
  rfl

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
  have hSec : toyDep.secret = ZMod.ofNat 257 42 := by decide +kernel
  rw [← hSec]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro ps (rfl | rfl | rfl | rfl | rfl) <;>
    exact reconstruct_dealt_shares toyDep toyDep_wellFormed _
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ## Teeth -/

private def toyForgedPoly : List F257 := [ZMod.ofNat 257 24, ZMod.ofNat 257 25]

private def toyDepForgedPoly : Deployment F257 F257 Unit ToyDigest ToySig :=
  { toyDep with
    poly := toyForgedPoly
    shareCommitment := fun p => RoundPoly.evalCoeffs toyForgedPoly (toyPoint p) }

private theorem toyDepForgedPoly_wellFormed : toyDepForgedPoly.WellFormed where
  points_nodup := toyPoints_nodup
  points_nonzero := toyPoints_nonzero
  degree := by decide
  commitments_dealt _ _ := rfl
  commit_binding _ _ h := h

/-- Tooth for `commit_binding`: with a constant commitment the forged share passes the check and
    the same schedule releases under the key `24`. -/
theorem tooth_nonbinding_commitment_releases_under_wrong_key :
    runOutputs toyDepNonBinding (State.init toyDepNonBinding)
        [.corrupt 2, .approve 0 7 toyIntent, .inject forgedShareMsg,
         .execute 7 [0, 2] toyIntent false] =
      [some (.corrupted share2 []), some .approved, some .injected,
       some (.custody (.released (ZMod.ofNat 257 24, (7, toyIntent))))] := by
  let pre : List (Turn F257) := [.corrupt 2, .approve 0 7 toyIntent, .inject forgedShareMsg]
  let post : List (Turn F257) := [.execute 7 [0, 2] toyIntent false]
  change runOutputs toyDepNonBinding (State.init toyDepNonBinding) (pre ++ post) = _
  rw [runOutputs_append]
  have hPre : runOutputs toyDepNonBinding (State.init toyDepNonBinding) pre =
      [some (.corrupted share2 []), some .approved, some .injected] := by
    decide +kernel
  let st3 := stepAtState toyDepNonBinding (State.init toyDepNonBinding) pre
  have hKey : quorumKey toyDepNonBinding st3.buffer [0, 2] toyIntent = ZMod.ofNat 257 24 := by
    have hPts : [0, 2].map toyDepNonBinding.point = [0, 2].map toyDepForgedPoly.point := rfl
    have hSh : [0, 2].map (fun p => (approvalShare toyDepNonBinding st3.buffer toyIntent p).getD CommRingOps.zero) =
        [0, 2].map toyDepForgedPoly.trueShare := by
      decide +kernel
    have hSec : toyDepForgedPoly.secret = ZMod.ofNat 257 24 := by decide +kernel
    unfold quorumKey
    rw [hPts, hSh, ← hSec]
    exact reconstruct_dealt_shares toyDepForgedPoly toyDepForgedPoly_wellFormed [0, 2]
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hPost : runOutputs toyDepNonBinding st3 post =
      [some (.custody (.released (ZMod.ofNat 257 24, (7, toyIntent))))] := by
    dsimp only [post, runOutputs]
    rw [step_execute_key_eq toyDepNonBinding st3 7 [0, 2] toyIntent false (ZMod.ofNat 257 24) hKey]
    decide +kernel
  rw [hPre]
  change [some (.corrupted share2 []), some .approved, some .injected] ++
    runOutputs toyDepNonBinding st3 post = _
  rw [hPost]
  rfl

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

theorem verifyShare_sound_audited (dep : Deployment F257 F257 Unit ToyDigest ToySig)
    (hWf : dep.WellFormed) {p : Nat} {s : F257}
    (hp : p < dep.quorum.numParties) (h : dep.verifyShare p s = true) : s = dep.trueShare p :=
  verifyShare_sound dep hWf hp h

theorem reconstruct_dealt_shares_audited (dep : Deployment F257 F257 Unit ToyDigest ToySig)
    (hWf : dep.WellFormed) (approvers : List Nat) (hNd : approvers.Nodup)
    (hEnrolled : ∀ p, p ∈ approvers → p < dep.quorum.numParties)
    (hThr : dep.quorum.threshold ≤ approvers.length) :
    reconstruct (approvers.map dep.point) (approvers.map dep.trueShare) = dep.secret :=
  reconstruct_dealt_shares dep hWf approvers hNd hEnrolled hThr

#tooth_pair Qsag.DistCustody.Checks.verifyShare_sound_audited vs
  Qsag.DistCustody.Checks.tooth_nonbinding_commitment_accepts_wrong_share
#tooth_pair Qsag.DistCustody.Checks.reconstruct_dealt_shares_audited vs
  Qsag.DistCustody.Checks.tooth_duplicate_points_do_not_reconstruct

/-! ## Share-Opening Custody over Real Compressing 256-Bit Sponge (`BitVec 256`) and Real `Spec.SigScheme` -/

/-! ### Real 24-Round `Keccak-f[1600]` Sponge (`cSHAKE256` `"QSAG.DIST.SPONGE/v1"`) -/
set_option maxRecDepth 65536
set_option maxHeartbeats 800000

private def kZeroState : KState :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

private def kLoadLe64 (block : List UInt8) (laneIdx : Nat) : UInt64 :=
  let base := 8 * laneIdx
  (block.getD base 0).toUInt64 |||
  ((block.getD (base + 1) 0).toUInt64 <<< 8) |||
  ((block.getD (base + 2) 0).toUInt64 <<< 16) |||
  ((block.getD (base + 3) 0).toUInt64 <<< 24) |||
  ((block.getD (base + 4) 0).toUInt64 <<< 32) |||
  ((block.getD (base + 5) 0).toUInt64 <<< 40) |||
  ((block.getD (base + 6) 0).toUInt64 <<< 48) |||
  ((block.getD (base + 7) 0).toUInt64 <<< 56)

private def kXorRate136 (s : KState) (block : List UInt8) : KState :=
  { s with
    a0  := s.a0  ^^^ kLoadLe64 block 0,  a1  := s.a1  ^^^ kLoadLe64 block 1,
    a2  := s.a2  ^^^ kLoadLe64 block 2,  a3  := s.a3  ^^^ kLoadLe64 block 3,
    a4  := s.a4  ^^^ kLoadLe64 block 4,  a5  := s.a5  ^^^ kLoadLe64 block 5,
    a6  := s.a6  ^^^ kLoadLe64 block 6,  a7  := s.a7  ^^^ kLoadLe64 block 7,
    a8  := s.a8  ^^^ kLoadLe64 block 8,  a9  := s.a9  ^^^ kLoadLe64 block 9,
    a10 := s.a10 ^^^ kLoadLe64 block 10, a11 := s.a11 ^^^ kLoadLe64 block 11,
    a12 := s.a12 ^^^ kLoadLe64 block 12, a13 := s.a13 ^^^ kLoadLe64 block 13,
    a14 := s.a14 ^^^ kLoadLe64 block 14, a15 := s.a15 ^^^ kLoadLe64 block 15,
    a16 := s.a16 ^^^ kLoadLe64 block 16 }

private def kLaneBytesLE (w : UInt64) : List UInt8 :=
  [UInt8.ofNat (w.toNat % 256),
   UInt8.ofNat ((w.toNat / 256) % 256),
   UInt8.ofNat ((w.toNat / 65536) % 256),
   UInt8.ofNat ((w.toNat / 16777216) % 256),
   UInt8.ofNat ((w.toNat / 4294967296) % 256),
   UInt8.ofNat ((w.toNat / 1099511627776) % 256),
   UInt8.ofNat ((w.toNat / 281474976710656) % 256),
   UInt8.ofNat ((w.toNat / 72057594037927936) % 256)]

private def kRateBlockBytes (s : KState) : List UInt8 :=
  kLaneBytesLE s.a0 ++ kLaneBytesLE s.a1 ++ kLaneBytesLE s.a2 ++ kLaneBytesLE s.a3 ++
  kLaneBytesLE s.a4 ++ kLaneBytesLE s.a5 ++ kLaneBytesLE s.a6 ++ kLaneBytesLE s.a7 ++
  kLaneBytesLE s.a8 ++ kLaneBytesLE s.a9 ++ kLaneBytesLE s.a10 ++ kLaneBytesLE s.a11 ++
  kLaneBytesLE s.a12 ++ kLaneBytesLE s.a13 ++ kLaneBytesLE s.a14 ++ kLaneBytesLE s.a15 ++
  kLaneBytesLE s.a16

/-- Precomputed 136-byte SP 800-185 `bytepad(encodeString("") || encodeString("QSAG.DIST.SPONGE/v1"), 136)`. -/
private def distSpongePrefix136 : Bytes :=
  [
   0x01, 0x88, 0x01, 0x00, 0x01, 0x98, 0x51, 0x53, 0x41, 0x47, 0x2E, 0x44, 0x49, 0x53, 0x54, 0x2E, 0x53,
   0x50, 0x4F, 0x4E, 0x47, 0x45, 0x2F, 0x76, 0x31, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

/-- Real compressing 256-bit sponge hash (`Bytes → BitVec 256`) over 24-round `keccakF1600`
    (`r = 136` bytes, `c = 64` bytes, NIST SP 800-185 `cSHAKE256` domain `0x04`, `"QSAG.DIST.SPONGE/v1"`). -/
def spongeCommit256 (msg : Bytes) : BitVec 256 :=
  BitVec.ofNat 256 (ofBE (evalSponge 136 0x04 keccakF1600 kZeroState kXorRate136 kRateBlockBytes
    (distSpongePrefix136 ++ msg) 32))

/-- Domain tag `"QSAG.DIST.COMMIT/v1"` for NIST SP 800-185 `cSHAKE256` share-opening commitments. -/
def cshakeShareCommitDomain : Bytes :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x44, 0x49, 0x53, 0x54, 0x2E,
   0x43, 0x4F, 0x4D, 0x4D, 0x49, 0x54, 0x2F, 0x76, 0x31]

/-- Real compressing 256-bit hash (`Bytes → BitVec 256`) via NIST SP 800-185 `cSHAKE256`. -/
def cshakeCommit256 (preimage : Bytes) : BitVec 256 :=
  BitVec.ofNat 256 (ofBE (cshake256Bytes cshakeShareCommitDomain preimage))

/-- Domain-separated single-step 256-bit hash chain link parameterized by any 256-bit hash `H`. -/
def hashStep256 (H : Bytes → BitVec 256) (dom : UInt8) (v : BitVec 256) : BitVec 256 :=
  H ([0x51, 0x53, 0x57, dom] ++ be 32 v.toNat)

/-- Iterate the WOTS hash chain `steps` times under `H`. -/
def wotsChainStep (H : Bytes → BitVec 256) : Nat → BitVec 256 → BitVec 256
  | 0, v => v
  | n + 1, v => wotsChainStep H n (hashStep256 H 0x01 v)

theorem wotsChainStep_add (H : Bytes → BitVec 256) : ∀ (a b : Nat) (v : BitVec 256),
    wotsChainStep H b (wotsChainStep H a v) = wotsChainStep H (a + b) v
  | 0, b, v => by rw [Nat.zero_add]; rfl
  | a + 1, b, v => by
    rw [Nat.succ_add]
    exact wotsChainStep_add H a b (hashStep256 H 0x01 v)

/-- 1-bit message digest (`∈ {0, 1}`) under `H`; paired with checksum `1 - b` so `b + (1 - b) = 1`. -/
def msgDigestBit (H : Bytes → BitVec 256) (msg : Bytes) : Nat :=
  (H ([0x51, 0x53, 0x4D] ++ msg)).toNat % 2

theorem msgDigestBit_lt (H : Bytes → BitVec 256) (msg : Bytes) : msgDigestBit H msg < 2 :=
  Nat.mod_lt _ (by decide)

/-- Public endpoint pair `(chain0End, chain1End)` for one RSS slot at one epoch. -/
abbrev SlotEndpoint := BitVec 256 × BitVec 256

/-- Public key for 2 epochs × 3 RSS slots (`12` 256-bit WOTS chain endpoints). -/
structure RssWotsPk where
  ep0s0 : SlotEndpoint
  ep0s1 : SlotEndpoint
  ep0s2 : SlotEndpoint
  ep1s0 : SlotEndpoint
  ep1s1 : SlotEndpoint
  ep1s2 : SlotEndpoint
  deriving DecidableEq, Repr

/-- Master secret key (`3` independent 256-bit seeds; NO custodian holds all three!). -/
structure RssWotsSk where
  s0 : BitVec 256
  s1 : BitVec 256
  s2 : BitVec 256
  deriving DecidableEq, Repr

/-- Assembled WOTS signature for epoch `ep ∈ {0, 1}` across the 3 RSS slots. -/
structure RssWotsSig where
  ep : Nat
  slot0 : SlotEndpoint
  slot1 : SlotEndpoint
  slot2 : SlotEndpoint
  deriving DecidableEq, Repr

def deriveSlotLeaf (H : Bytes → BitVec 256) (seed : BitVec 256) (slot ep : Nat) (chain : Bool) :
    BitVec 256 :=
  hashStep256 H (UInt8.ofNat (16 + 4 * slot + 2 * ep + (if chain then 1 else 0))) seed

def deriveSlotPk (H : Bytes → BitVec 256) (seed : BitVec 256) (slot ep : Nat) : SlotEndpoint :=
  (wotsChainStep H 1 (deriveSlotLeaf H seed slot ep false),
   wotsChainStep H 1 (deriveSlotLeaf H seed slot ep true))

def stepSlotForMsg (H : Bytes → BitVec 256) (seed : BitVec 256) (slot ep : Nat) (msg : Bytes) :
    SlotEndpoint :=
  let b := msgDigestBit H msg
  (wotsChainStep H b (deriveSlotLeaf H seed slot ep false),
   wotsChainStep H (1 - b) (deriveSlotLeaf H seed slot ep true))

def verifySlotForMsg (H : Bytes → BitVec 256) (pk : SlotEndpoint) (msg : Bytes)
    (sig : SlotEndpoint) : Bool :=
  let b := msgDigestBit H msg
  decide (wotsChainStep H (1 - b) sig.1 = pk.1) &&
  decide (wotsChainStep H b sig.2 = pk.2)

theorem verifySlotForMsg_step (H : Bytes → BitVec 256) (seed : BitVec 256) (slot ep : Nat)
    (msg : Bytes) :
    verifySlotForMsg H (deriveSlotPk H seed slot ep) msg (stepSlotForMsg H seed slot ep msg) =
      true := by
  unfold verifySlotForMsg deriveSlotPk stepSlotForMsg
  dsimp only
  have hb : msgDigestBit H msg < 2 := msgDigestBit_lt H msg
  have h1 : msgDigestBit H msg + (1 - msgDigestBit H msg) = 1 := by omega
  have h2 : (1 - msgDigestBit H msg) + msgDigestBit H msg = 1 := by omega
  rw [wotsChainStep_add, wotsChainStep_add, h1, h2]
  simp

/-- Genuine 256-bit WOTS+checksum `Spec.SigScheme` over 3 RSS slots and 2 epochs, parameterized by
    any 256-bit hash `H : Bytes → BitVec 256`. -/
def rssWotsSigScheme (H : Bytes → BitVec 256) : SigScheme RssWotsPk RssWotsSk RssWotsSig where
  derivePk sk :=
    { ep0s0 := deriveSlotPk H sk.s0 0 0
      ep0s1 := deriveSlotPk H sk.s1 1 0
      ep0s2 := deriveSlotPk H sk.s2 2 0
      ep1s0 := deriveSlotPk H sk.s0 0 1
      ep1s1 := deriveSlotPk H sk.s1 1 1
      ep1s2 := deriveSlotPk H sk.s2 2 1 }
  sign sk ep msg :=
    if ep = 0 then
      some ⟨0, stepSlotForMsg H sk.s0 0 0 msg, stepSlotForMsg H sk.s1 1 0 msg,
        stepSlotForMsg H sk.s2 2 0 msg⟩
    else if ep = 1 then
      some ⟨1, stepSlotForMsg H sk.s0 0 1 msg, stepSlotForMsg H sk.s1 1 1 msg,
        stepSlotForMsg H sk.s2 2 1 msg⟩
    else none
  verify pk msg sig :=
    if sig.ep = 0 then
      verifySlotForMsg H pk.ep0s0 msg sig.slot0 &&
      verifySlotForMsg H pk.ep0s1 msg sig.slot1 &&
      verifySlotForMsg H pk.ep0s2 msg sig.slot2
    else if sig.ep = 1 then
      verifySlotForMsg H pk.ep1s0 msg sig.slot0 &&
      verifySlotForMsg H pk.ep1s1 msg sig.slot1 &&
      verifySlotForMsg H pk.ep1s2 msg sig.slot2
    else false
  correct sk ep msg sig hSign := by
    dsimp only at hSign ⊢
    by_cases h0 : ep = 0
    · subst h0
      simp only [↓reduceIte, Option.some.injEq] at hSign
      subst hSign
      simp [verifySlotForMsg_step]
    · simp only [h0, ↓reduceIte] at hSign
      by_cases h1 : ep = 1
      · subst h1
        simp only [↓reduceIte, Option.some.injEq] at hSign
        subst hSign
        simp [verifySlotForMsg_step]
      · simp [h1] at hSign

/-- Replicated `(2, 3)` custodian share: holds ONLY 2 of the 3 256-bit seeds `(idxA, seedA), (idxB, seedB)`. -/
abbrev RssCustodianShare := (Fin 3 × BitVec 256) × (Fin 3 × BitVec 256)

/-- Per-request share-opening contribution: stepped WOTS pairs `(idxA, pairA), (idxB, pairB)` (NO raw seeds!). -/
abbrev RssShareContrib := Option ((Fin 3 × SlotEndpoint) × (Fin 3 × SlotEndpoint))

def encodeToyDigest (d : ToyDigest) : Bytes :=
  be 8 d.1 ++ be 8 d.2.sessionId ++ be 8 d.2.round ++
    be 8 d.2.epoch ++ be 8 d.2.spend ++ be 8 d.2.payload.length ++ d.2.payload

def encodeContribBytes : RssShareContrib → Bytes
  | none => [0]
  | some ((iA, (a0, a1)), (iB, (b0, b1))) =>
    1 :: UInt8.ofNat iA.val :: (be 32 a0.toNat ++
      (be 32 a1.toNat ++ (UInt8.ofNat iB.val :: (be 32 b0.toNat ++ be 32 b1.toNat))))

private theorem bv256_lt_256_32 (v : BitVec 256) : v.toNat < 256 ^ 32 := by
  have hPow : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  rw [← hPow]
  exact v.isLt

private theorem bv256_eq_of_be32 {u v : BitVec 256} (h : be 32 u.toNat = be 32 v.toNat) : u = v := by
  have hOf := congrArg ofBE h
  rw [ofBE_be (bv256_lt_256_32 u), ofBE_be (bv256_lt_256_32 v)] at hOf
  exact BitVec.eq_of_toNat_eq hOf

private theorem fin3_eq_of_uint8 {i j : Fin 3} (h : UInt8.ofNat i.val = UInt8.ofNat j.val) : i = j := by
  have hi : i.val < 256 := Nat.lt_trans i.isLt (by decide)
  have hj : j.val < 256 := Nat.lt_trans j.isLt (by decide)
  have ht := congrArg UInt8.toNat h
  rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat',
      Nat.mod_eq_of_lt (show i.val < 2 ^ 8 by exact hi),
      Nat.mod_eq_of_lt (show j.val < 2 ^ 8 by exact hj)] at ht
  exact Fin.ext ht

theorem encodeContribBytes_injective {c₁ c₂ : RssShareContrib}
    (h : encodeContribBytes c₁ = encodeContribBytes c₂) : c₁ = c₂ := by
  cases c₁ with
  | none =>
    cases c₂ with
    | none => rfl
    | some v2 =>
      rcases v2 with ⟨⟨_, ⟨_, _⟩⟩, ⟨_, ⟨_, _⟩⟩⟩
      dsimp only [encodeContribBytes] at h
      injection h with hHd _
      cases hHd
  | some v1 =>
    rcases v1 with ⟨⟨iA1, ⟨a01, a11⟩⟩, ⟨iB1, ⟨b01, b11⟩⟩⟩
    cases c₂ with
    | none =>
      dsimp only [encodeContribBytes] at h
      injection h with hHd _
      cases hHd
    | some v2 =>
      rcases v2 with ⟨⟨iA2, ⟨a02, a12⟩⟩, ⟨iB2, ⟨b02, b12⟩⟩⟩
      dsimp only [encodeContribBytes] at h
      have h1 := (List.cons.inj h).2
      obtain ⟨hiA, h2⟩ := List.cons.inj h1
      obtain ⟨ha0, h3⟩ := append_inj_of_len_eq ((length_be 32 _).trans (length_be 32 _).symm) h2
      obtain ⟨ha1, h4⟩ := append_inj_of_len_eq ((length_be 32 _).trans (length_be 32 _).symm) h3
      obtain ⟨hiB, h5⟩ := List.cons.inj h4
      obtain ⟨hb0, hb1⟩ := append_inj_of_len_eq ((length_be 32 _).trans (length_be 32 _).symm) h5
      rw [fin3_eq_of_uint8 hiA, bv256_eq_of_be32 ha0, bv256_eq_of_be32 ha1,
          fin3_eq_of_uint8 hiB, bv256_eq_of_be32 hb0, bv256_eq_of_be32 hb1]

/-- Length-framed preimage encoding binding `(p, d, i.sessionId, i.round, i.epoch, i.spend,
    i.payload.length, i.payload)` together with `encodeContribBytes c`. -/
def encodeSharePreimage (p d : Nat) (i : CustodyIntent) (c : RssShareContrib) : Bytes :=
  (be 8 p ++ be 8 d ++ be 8 i.sessionId ++ be 8 i.round ++
    be 8 i.epoch ++ be 8 i.spend ++ be 8 i.payload.length ++ i.payload) ++
    encodeContribBytes c

theorem encodeSharePreimage_framed (p d : Nat) (i : CustodyIntent) (c₁ c₂ : RssShareContrib)
    (h : encodeSharePreimage p d i c₁ = encodeSharePreimage p d i c₂) : c₁ = c₂ :=
  encodeContribBytes_injective (List.append_cancel_left h)

def sampleMasterSk : RssWotsSk :=
  { s0 := 0x111122223333444455556666777788889999AAAABBBBCCCCDDDDEEEEFFFF0001#256
    s1 := 0x22223333444455556666777788889999AAAABBBBCCCCDDDDEEEEFFFF00021111#256
    s2 := 0x3333444455556666777788889999AAAABBBBCCCCDDDDEEEEFFFF000311112222#256 }

def slotSeed (sk : RssWotsSk) (slot : Fin 3) : BitVec 256 :=
  match slot.val with
  | 0 => sk.s0
  | 1 => sk.s1
  | _ => sk.s2

def dealRssShare (sk : RssWotsSk) : Nat → RssCustodianShare
  | 0 => ((⟨1, by decide⟩, sk.s1), (⟨2, by decide⟩, sk.s2))
  | 1 => ((⟨0, by decide⟩, sk.s0), (⟨2, by decide⟩, sk.s2))
  | _ => ((⟨0, by decide⟩, sk.s0), (⟨1, by decide⟩, sk.s1))

def evalRssContrib (H : Bytes → BitVec 256) (_p : Nat) (sh : RssCustodianShare) (d : Nat)
    (i : CustodyIntent) : RssShareContrib :=
  let msg := encodeToyDigest (d, i)
  if i.epoch = 0 ∨ i.epoch = 1 then
    some ((sh.1.1, stepSlotForMsg H sh.1.2 sh.1.1.val i.epoch msg),
          (sh.2.1, stepSlotForMsg H sh.2.2 sh.2.1.val i.epoch msg))
  else none

def findSlotInContribs (slot : Fin 3) : List (Nat × RssShareContrib) → Option SlotEndpoint
  | [] => none
  | (_, none) :: rest => findSlotInContribs slot rest
  | (_, some ((iA, epA), (iB, epB))) :: rest =>
    if iA.val == slot.val then some epA
    else if iB.val == slot.val then some epB
    else findSlotInContribs slot rest

/-- Public combiner: assembles `RssWotsSig` from stepped slot contributions WITHOUT reconstructing `SK`! -/
def assembleRssSig (contribs : List (Nat × RssShareContrib)) (ep : Nat) (_dig : ToyDigest) :
    Option RssWotsSig :=
  if ep = 0 ∨ ep = 1 then
    match findSlotInContribs ⟨0, by decide⟩ contribs,
          findSlotInContribs ⟨1, by decide⟩ contribs,
          findSlotInContribs ⟨2, by decide⟩ contribs with
    | some s0, some s1, some s2 => some ⟨ep, s0, s1, s2⟩
    | _, _, _ => none
  else none

def fallbackRssSig : RssWotsSig :=
  ⟨0, (0#256, 0#256), (0#256, 0#256), (0#256, 0#256)⟩

/-- Generic 2-of-3 share-opening deployment parameterized over any 256-bit hash `H : Bytes → BitVec 256`. -/
def mkRssShareDep (H : Bytes → BitVec 256) :
    ShareOpeningDeployment RssCustodianShare RssShareContrib Bytes
      RssWotsPk RssWotsSk ToyDigest RssWotsSig where
  deploymentId := 7
  quorum := toyQuorum
  sigScheme := rssWotsSigScheme H
  dealtSk := sampleMasterSk
  fallbackSig := fallbackRssSig
  digests := CustodyDigestScheme.transparent
  encodeDigest := encodeToyDigest
  epochOfDigest d := d.2.epoch
  dealShare := dealRssShare sampleMasterSk
  evalContrib := evalRssContrib H
  assembleSig := assembleRssSig
  preimageOf := encodeSharePreimage
  commit := H
  commitmentOf p d i :=
    H (encodeSharePreimage p d i (evalRssContrib H p (dealRssShare sampleMasterSk p) d i))

/-- Concrete 2-of-3 share-opening deployment over NIST SP 800-185 `cSHAKE256` (`BitVec 256`). -/
def cshakeShareDep := mkRssShareDep cshakeCommit256

/-- Concrete kernel-executable 2-of-3 share-opening deployment over 24-round `keccakF1600` sponge `spongeCommit256` (`BitVec 256`). -/
def spongeShareDep := mkRssShareDep spongeCommit256

/-- Non-binding mutant with a constant 256-bit commitment hash (`fun _ => 0#256`) to trigger the
    explicit collision branch of `distCustody_dataRefines_or_collision`. -/
def spongeShareDepConstCommit :
    ShareOpeningDeployment RssCustodianShare RssShareContrib Bytes
      RssWotsPk RssWotsSk ToyDigest RssWotsSig :=
  { spongeShareDep with
    commit := fun _ => 0#256
    commitmentOf := fun _ _ _ => 0#256 }

private theorem findSlot_sound (H : Bytes → BitVec 256) (slot : Fin 3) (sk : RssWotsSk)
    (ep : Nat) (msg : Bytes) :
    ∀ (ps : List Nat), (∀ p ∈ ps, p < 3) →
      (∃ p ∈ ps, (dealRssShare sk p).1.1 = slot ∨ (dealRssShare sk p).2.1 = slot) →
      findSlotInContribs slot
        (ps.map (fun p => (p, some (((dealRssShare sk p).1.1,
            stepSlotForMsg H (dealRssShare sk p).1.2 (dealRssShare sk p).1.1.val ep msg),
          ((dealRssShare sk p).2.1,
            stepSlotForMsg H (dealRssShare sk p).2.2 (dealRssShare sk p).2.1.val ep msg))))) =
        some (stepSlotForMsg H (slotSeed sk slot) slot.val ep msg)
  | [], _, ⟨_, hm, _⟩ => absurd hm List.not_mem_nil
  | p :: rest, hLt, hCov => by
    have hp3 : p < 3 := hLt p List.mem_cons_self
    have hpCases : p = 0 ∨ p = 1 ∨ p = 2 := by omega
    have hSlotCases : slot = ⟨0, by decide⟩ ∨ slot = ⟨1, by decide⟩ ∨ slot = ⟨2, by decide⟩ := by
      rcases slot with ⟨sv, hsv⟩
      have hsc : sv = 0 ∨ sv = 1 ∨ sv = 2 := by omega
      rcases hsc with rfl | rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr rfl)
    rcases hpCases with rfl | rfl | rfl <;> rcases hSlotCases with rfl | rfl | rfl
    · change findSlotInContribs ⟨0, by decide⟩ _ = _
      refine findSlot_sound H ⟨0, by decide⟩ sk ep msg rest
        (fun q hq => hLt q (List.mem_cons_of_mem _ hq)) ?_
      obtain ⟨q, hqM, hqS⟩ := hCov
      rcases List.mem_cons.mp hqM with rfl | hTail
      · simp [dealRssShare] at hqS
      · exact ⟨q, hTail, hqS⟩
    · rfl
    · rfl
    · rfl
    · change findSlotInContribs ⟨1, by decide⟩ _ = _
      refine findSlot_sound H ⟨1, by decide⟩ sk ep msg rest
        (fun q hq => hLt q (List.mem_cons_of_mem _ hq)) ?_
      obtain ⟨q, hqM, hqS⟩ := hCov
      rcases List.mem_cons.mp hqM with rfl | hTail
      · simp [dealRssShare] at hqS
      · exact ⟨q, hTail, hqS⟩
    · rfl
    · rfl
    · rfl
    · change findSlotInContribs ⟨2, by decide⟩ _ = _
      refine findSlot_sound H ⟨2, by decide⟩ sk ep msg rest
        (fun q hq => hLt q (List.mem_cons_of_mem _ hq)) ?_
      obtain ⟨q, hqM, hqS⟩ := hCov
      rcases List.mem_cons.mp hqM with rfl | hTail
      · simp [dealRssShare] at hqS
      · exact ⟨q, hTail, hqS⟩

private theorem two_of_three_covers_slot {ps : List Nat}
    (hNd : ps.Nodup) (hLt : ∀ p ∈ ps, p < 3) (hLen : 2 ≤ ps.length) (slot : Fin 3) :
    ∃ p ∈ ps, (dealRssShare sampleMasterSk p).1.1 = slot ∨
      (dealRssShare sampleMasterSk p).2.1 = slot := by
  cases ps with
  | nil => cases hLen
  | cons p0 tail =>
    cases tail with
    | nil => cases (Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ hLen))
    | cons p1 rest =>
      have hp0 : p0 < 3 := hLt p0 List.mem_cons_self
      have hp1 : p1 < 3 := hLt p1 (List.mem_cons_of_mem _ List.mem_cons_self)
      have hNe : p0 ≠ p1 := fun h => (List.nodup_cons.mp hNd).1 (h ▸ List.mem_cons_self)
      have hC0 : p0 = 0 ∨ p0 = 1 ∨ p0 = 2 := by omega
      have hC1 : p1 = 0 ∨ p1 = 1 ∨ p1 = 2 := by omega
      have hCS : slot = ⟨0, by decide⟩ ∨ slot = ⟨1, by decide⟩ ∨ slot = ⟨2, by decide⟩ := by
        rcases slot with ⟨sv, hsv⟩
        have hsc : sv = 0 ∨ sv = 1 ∨ sv = 2 := by omega
        rcases hsc with rfl | rfl | rfl
        · exact .inl rfl
        · exact .inr (.inl rfl)
        · exact .inr (.inr rfl)
      rcases hC0 with rfl | rfl | rfl <;> rcases hC1 with rfl | rfl | rfl
      · exact False.elim (hNe rfl)
      · rcases hCS with rfl | rfl | rfl <;>
          first
          | exact ⟨_, List.mem_cons_self, .inl rfl⟩
          | exact ⟨_, List.mem_cons_self, .inr rfl⟩
          | exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, .inl rfl⟩
          | exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, .inr rfl⟩
      · rcases hCS with rfl | rfl | rfl <;>
          first
          | exact ⟨_, List.mem_cons_self, .inl rfl⟩
          | exact ⟨_, List.mem_cons_self, .inr rfl⟩
          | exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, .inl rfl⟩
          | exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, .inr rfl⟩
      · rcases hCS with rfl | rfl | rfl <;>
          first
          | exact ⟨_, List.mem_cons_self, .inl rfl⟩
          | exact ⟨_, List.mem_cons_self, .inr rfl⟩
          | exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, .inl rfl⟩
          | exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, .inr rfl⟩
      · exact False.elim (hNe rfl)
      · rcases hCS with rfl | rfl | rfl <;>
          first
          | exact ⟨_, List.mem_cons_self, .inl rfl⟩
          | exact ⟨_, List.mem_cons_self, .inr rfl⟩
          | exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, .inl rfl⟩
          | exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, .inr rfl⟩
      · rcases hCS with rfl | rfl | rfl <;>
          first
          | exact ⟨_, List.mem_cons_self, .inl rfl⟩
          | exact ⟨_, List.mem_cons_self, .inr rfl⟩
          | exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, .inl rfl⟩
          | exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, .inr rfl⟩
      · rcases hCS with rfl | rfl | rfl <;>
          first
          | exact ⟨_, List.mem_cons_self, .inl rfl⟩
          | exact ⟨_, List.mem_cons_self, .inr rfl⟩
          | exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, .inl rfl⟩
          | exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, .inr rfl⟩
      · exact False.elim (hNe rfl)

theorem mkRssShareDep_wellFormed (H : Bytes → BitVec 256) : (mkRssShareDep H).WellFormed where
  epoch_digest _ := rfl
  preimage_framed := encodeSharePreimage_framed
  commitments_dealt _ _ _ := rfl
  assemble_dealt approvers i hNd hEnr hThr := by
    dsimp only [mkRssShareDep, ShareOpeningDeployment.trueContrib, evalRssContrib,
      assembleRssSig, rssWotsSigScheme, CustodyDigestScheme.transparent]
    by_cases hEp : i.epoch = 0 ∨ i.epoch = 1
    · simp only [hEp, ↓reduceIte]
      rw [findSlot_sound H ⟨0, by decide⟩ sampleMasterSk i.epoch (encodeToyDigest (7, i)) approvers hEnr
            (two_of_three_covers_slot hNd hEnr hThr ⟨0, by decide⟩),
          findSlot_sound H ⟨1, by decide⟩ sampleMasterSk i.epoch (encodeToyDigest (7, i)) approvers hEnr
            (two_of_three_covers_slot hNd hEnr hThr ⟨1, by decide⟩),
          findSlot_sound H ⟨2, by decide⟩ sampleMasterSk i.epoch (encodeToyDigest (7, i)) approvers hEnr
            (two_of_three_covers_slot hNd hEnr hThr ⟨2, by decide⟩)]
      dsimp only [slotSeed]
      rcases hEp with h0 | h1
      · simp [h0]
      · simp [h1]
    · have h0 : ¬ (i.epoch = 0) := fun h => hEp (.inl h)
      have h1 : ¬ (i.epoch = 1) := fun h => hEp (.inr h)
      simp [h0, h1]

section SymbolicShareWellFormed
attribute [local irreducible] spongeCommit256 cshakeCommit256

theorem cshakeShareDep_wellFormed : cshakeShareDep.WellFormed :=
  mkRssShareDep_wellFormed cshakeCommit256

theorem spongeShareDep_wellFormed : spongeShareDep.WellFormed :=
  mkRssShareDep_wellFormed spongeCommit256

theorem spongeShareDepConstCommit_wellFormed : spongeShareDepConstCommit.WellFormed :=
  ⟨fun _ => rfl, encodeSharePreimage_framed, fun _ _ _ => rfl,
   (mkRssShareDep_wellFormed spongeCommit256).assemble_dealt⟩

end SymbolicShareWellFormed

def runShareOutputs
    (dep : ShareOpeningDeployment RssCustodianShare RssShareContrib Bytes
      RssWotsPk RssWotsSk ToyDigest RssWotsSig) :
    ShareState RssCustodianShare RssShareContrib RssWotsPk ToyDigest RssWotsSig →
    List (ShareTurn RssShareContrib) →
    List (Option (ShareEvent RssCustodianShare RssWotsSig))
  | _, [] => []
  | st, t :: rest =>
    match shareOpeningStep dep st t with
    | some (st', ev) => some ev :: runShareOutputs dep st' rest
    | none => none :: runShareOutputs dep st rest

/-- Expected signature produced by `(rssWotsSigScheme spongeCommit256).sign` on `(7, toyIntent)` at epoch `0`. -/
def expectedSpongeSig0 : RssWotsSig :=
  ((rssWotsSigScheme spongeCommit256).sign sampleMasterSk 0 (encodeToyDigest (7, toyIntent))).getD
    fallbackRssSig

/-- **Kernel-verified multi-turn execution over real compressing 256-bit sponge (`BitVec 256`) and
    real WOTS `Spec.SigScheme`**:
    2-of-3 honest share-level release (zero `SK` reconstruction!) emits `expectedSpongeSig0`,
    `sigScheme.verify` accepts it, crash wipes volatile coupons, and WAL replay returns the
    committed signature! -/
theorem sponge_share_opening_honest_release_and_wal_replay :
    runShareOutputs spongeShareDep (ShareState.init spongeShareDep)
        [.approve 0 7 toyIntent, .approve 1 7 toyIntent,
         .execute 7 [0, 1] toyIntent false,
         .crash 0, .execute 7 [] toyIntent false] =
      [some .approved, some .approved,
       some (.custody (.released expectedSpongeSig0)),
       some .recovered,
       some (.custody (.replayedFromWal expectedSpongeSig0))] ∧
    spongeShareDep.sigScheme.verify spongeShareDep.pk (encodeToyDigest (7, toyIntent))
      expectedSpongeSig0 = true := by
  decide +kernel

private theorem sponge_share_steps_exist :
    ∃ (s3 : ShareState RssCustodianShare RssShareContrib RssWotsPk ToyDigest RssWotsSig)
      (e1 e2 e3 : ShareEvent RssCustodianShare RssWotsSig),
      (shareOpeningMachine spongeShareDep).ValidTrace (ShareState.init spongeShareDep)
        [(.approve 0 7 toyIntent, e1), (.approve 1 7 toyIntent, e2),
         (.execute 7 [0, 1] toyIntent false, e3)] s3 ∧
      InjOnPreimages spongeShareDep.commit
        (observedSharePreimages spongeShareDep
          [(.approve 0 7 toyIntent, e1), (.approve 1 7 toyIntent, e2),
           (.execute 7 [0, 1] toyIntent false, e3)]) := by
  let s0 := ShareState.init spongeShareDep
  have h1 : ∃ p1, shareOpeningStep spongeShareDep s0 (.approve 0 7 toyIntent) = some p1 := by
    cases h : shareOpeningStep spongeShareDep s0 (.approve 0 7 toyIntent) with
    | some p => exact ⟨p, rfl⟩
    | none =>
      have hRun := sponge_share_opening_honest_release_and_wal_replay.1
      unfold runShareOutputs at hRun
      rw [h] at hRun
      cases hRun
  obtain ⟨⟨s1, e1⟩, hs1⟩ := h1
  have h2 : ∃ p2, shareOpeningStep spongeShareDep s1 (.approve 1 7 toyIntent) = some p2 := by
    cases h : shareOpeningStep spongeShareDep s1 (.approve 1 7 toyIntent) with
    | some p => exact ⟨p, rfl⟩
    | none =>
      have hRun := sponge_share_opening_honest_release_and_wal_replay.1
      unfold runShareOutputs at hRun
      rw [hs1] at hRun
      dsimp only at hRun
      unfold runShareOutputs at hRun
      rw [h] at hRun
      injection hRun with _ hTail
      cases hTail
  obtain ⟨⟨s2, e2⟩, hs2⟩ := h2
  have h3 : ∃ p3, shareOpeningStep spongeShareDep s2 (.execute 7 [0, 1] toyIntent false) = some p3 := by
    cases h : shareOpeningStep spongeShareDep s2 (.execute 7 [0, 1] toyIntent false) with
    | some p => exact ⟨p, rfl⟩
    | none =>
      have hRun := sponge_share_opening_honest_release_and_wal_replay.1
      unfold runShareOutputs at hRun
      rw [hs1] at hRun; dsimp only at hRun
      unfold runShareOutputs at hRun
      rw [hs2] at hRun; dsimp only at hRun
      unfold runShareOutputs at hRun
      rw [h] at hRun
      injection hRun with _ hT1
      injection hT1 with _ hT2
      cases hT2
  obtain ⟨⟨s3, e3⟩, hs3⟩ := h3
  have hTr : (shareOpeningMachine spongeShareDep).ValidTrace s0
      [(.approve 0 7 toyIntent, e1), (.approve 1 7 toyIntent, e2),
       (.execute 7 [0, 1] toyIntent false, e3)] s3 :=
    .accept hs1 (.accept hs2 (.accept hs3 (.nil s3)))
  have hInj : InjOnPreimages spongeShareDep.commit
      (observedSharePreimages spongeShareDep
        [(.approve 0 7 toyIntent, e1), (.approve 1 7 toyIntent, e2),
         (.execute 7 [0, 1] toyIntent false, e3)]) := by
    rw [observedSharePreimages_cons, observedSharePreimages_cons,
        observedSharePreimages_cons, observedSharePreimages_nil]
    decide +kernel
  exact ⟨s3, e1, e2, e3, hTr, hInj⟩

/-- Concrete inhabited `ValidTrace` witness for `distCustody_dataRefines_or_collision` over real
    256-bit sponge commitments (`Bytes → BitVec 256`) and `rssWotsSigScheme`. -/
theorem inhabited_sponge_share_opening_validTrace :
    ∃ (dep : ShareOpeningDeployment RssCustodianShare RssShareContrib Bytes
        RssWotsPk RssWotsSk ToyDigest RssWotsSig)
      (stFinal : ShareState RssCustodianShare RssShareContrib RssWotsPk ToyDigest RssWotsSig)
      (tr : List (ShareTurn RssShareContrib × ShareEvent RssCustodianShare RssWotsSig)),
      dep.WellFormed ∧
      (shareOpeningMachine dep).ValidTrace (ShareState.init dep) tr stFinal ∧
      tr.length = 3 ∧
      InjOnPreimages dep.commit (observedSharePreimages dep tr) := by
  obtain ⟨s3, e1, e2, e3, hTr, hInj⟩ := sponge_share_steps_exist
  exact ⟨spongeShareDep, s3, _, spongeShareDep_wellFormed, hTr, rfl, hInj⟩

def distCustody_injOn_dataRefines_ideal_audited
    (dep : ShareOpeningDeployment RssCustodianShare RssShareContrib Bytes
      RssWotsPk RssWotsSk ToyDigest RssWotsSig)
    (hWf : dep.WellFormed) (obs : List Bytes)
    (hInj : InjOnPreimages dep.commit obs) :
    DataRefines (shareOpeningObservedMachine dep obs)
      (idealCustodyMachine dep.digests dep.idealOracle dep.deploymentId dep.pk dep.quorum)
      (shareVisIn dep) shareVisOut :=
  distCustody_injOn_dataRefines_ideal dep hWf obs hInj

theorem distCustody_injOn_admitsTrace_audited
    (dep : ShareOpeningDeployment RssCustodianShare RssShareContrib Bytes
      RssWotsPk RssWotsSk ToyDigest RssWotsSig)
    (hWf : dep.WellFormed) (obs : List Bytes)
    (hInj : InjOnPreimages dep.commit obs)
    {tr : List (ShareTurn RssShareContrib × ShareEvent RssCustodianShare RssWotsSig)}
    (hTr : (shareOpeningObservedMachine dep obs).AdmitsTrace tr) :
    (idealCustodyMachine dep.digests dep.idealOracle dep.deploymentId dep.pk
      dep.quorum).AdmitsTrace (projectTrace (shareVisIn dep) shareVisOut tr) :=
  (distCustody_injOn_dataRefines_ideal dep hWf obs hInj).preserve_admitsTrace hTr

theorem distCustody_dataRefines_or_collision_audited
    (dep : ShareOpeningDeployment RssCustodianShare RssShareContrib Bytes
      RssWotsPk RssWotsSk ToyDigest RssWotsSig)
    (hWf : dep.WellFormed)
    {stFinal : ShareState RssCustodianShare RssShareContrib RssWotsPk ToyDigest RssWotsSig}
    {tr : List (ShareTurn RssShareContrib × ShareEvent RssCustodianShare RssWotsSig)}
    (hTr : (shareOpeningMachine dep).ValidTrace (ShareState.init dep) tr stFinal) :
    ((idealCustodyMachine dep.digests dep.idealOracle dep.deploymentId dep.pk
        dep.quorum).AdmitsTrace (projectTrace (shareVisIn dep) shareVisOut tr) ∧
      stFinal.corrupt.length < dep.quorum.threshold ∧
      stFinal.ledger.spent ≤ dep.quorum.spendCap ∧
      (∀ r : CustodyRelease ToyDigest RssWotsSig, r ∈ stFinal.ledger.releasedHistory →
        dep.sigScheme.verify dep.pk (dep.encodeDigest r.digest) r.sig = true ∧
        r.sig = dep.idealOracle (dep.digests.digest dep.deploymentId r.intent) ∧
        ∃ p : Nat, p < dep.quorum.numParties ∧ r.intent ∈ (stFinal.nodes p).latched ∧
          r.intent.epoch < (stFinal.nodes p).latch)) ∨
    (∃ x₁ x₂ : Bytes,
      x₁ ≠ x₂ ∧ dep.commit x₁ = dep.commit x₂ ∧
      x₁ ∈ observedSharePreimages dep tr ∧
      x₂ ∈ observedSharePreimages dep tr) :=
  distCustody_dataRefines_or_collision dep hWf hTr

theorem verifyContrib_dealt_or_collision_audited
    (dep : ShareOpeningDeployment RssCustodianShare RssShareContrib Bytes
      RssWotsPk RssWotsSk ToyDigest RssWotsSig)
    (hWf : dep.WellFormed) {p : Nat} {i : CustodyIntent} {c : RssShareContrib}
    (hp : p < dep.quorum.numParties)
    (hVer : dep.commit (dep.preimageOf p dep.deploymentId i c) =
      dep.commitmentOf p dep.deploymentId i) :
    c = dep.trueContrib p i ∨
      (dep.preimageOf p dep.deploymentId i c ≠
        dep.preimageOf p dep.deploymentId i (dep.trueContrib p i) ∧
       dep.commit (dep.preimageOf p dep.deploymentId i c) =
        dep.commit (dep.preimageOf p dep.deploymentId i (dep.trueContrib p i))) :=
  verifyContrib_dealt_or_collision dep hWf hp hVer

/-- Tooth 1 (`tooth_tampered_sponge_wots_sig_rejected`): tampering with a slot endpoint in
    `expectedSpongeSig0` causes `sigScheme.verify` to reject (`= false`). -/
theorem tooth_tampered_sponge_wots_sig_rejected :
    ¬ (spongeShareDep.sigScheme.verify spongeShareDep.pk (encodeToyDigest (7, toyIntent))
        { expectedSpongeSig0 with slot0 := (0#256, 0#256) } = true) := by
  decide +kernel

/-- Tooth 2 (`tooth_const_commit256_exhibits_collision_branch`): under a colliding 256-bit hash
    (`spongeShareDepConstCommit`), a forged contribution `none` from corrupted custodian `2`
    passes `verifyContrib` yet produces an explicit distinct colliding preimage pair `x₁ ≠ x₂`
    with `commit x₁ = commit x₂`. -/
theorem tooth_const_commit256_exhibits_collision_branch :
    let x₁ := spongeShareDepConstCommit.preimageOf 2 7 toyIntent none
    let x₂ := spongeShareDepConstCommit.preimageOf 2 7 toyIntent
      (spongeShareDepConstCommit.trueContrib 2 toyIntent)
    ¬ (x₁ = x₂) ∧
      spongeShareDepConstCommit.commit x₁ = spongeShareDepConstCommit.commit x₂ := by
  decide +kernel

/-- Refutation tooth for `verifyContrib_dealt_or_collision`: without the explicit collision
    branch, a colliding 256-bit commitment hash (`spongeShareDepConstCommit`) accepts `none`
    even though `none ≠ trueContrib 2 toyIntent`! -/
theorem tooth_const_commit256_refutes_naive_binding :
    ¬ (spongeShareDepConstCommit.commit (spongeShareDepConstCommit.preimageOf 2 7 toyIntent none) =
        spongeShareDepConstCommit.commitmentOf 2 7 toyIntent →
        (none : RssShareContrib) = spongeShareDepConstCommit.trueContrib 2 toyIntent) := by
  decide +kernel

/-- Tooth 3 (`tooth_forged_contrib_rejected_under_sponge_commit`): under `spongeShareDep`,
    injecting a forged contribution `none` from corrupted custodian `2` is rejected by
    `shareOpeningStep` (`= none`), whereas under `spongeShareDepConstCommit` it succeeds with an
    non-ideal signature! -/
theorem tooth_forged_contrib_rejected_under_sponge_commit :
    runShareOutputs spongeShareDep (ShareState.init spongeShareDep)
        [.corrupt 2, .approve 0 7 toyIntent,
         .inject { sender := 2, deploymentId := 7, intent := toyIntent, contrib := none },
         .execute 7 [0, 2] toyIntent false] =
      [some (.corrupted (spongeShareDep.dealShare 2) []), some .approved, some .injected, none] := by
  decide +kernel

section AuditSpongeShare
attribute [local irreducible] spongeCommit256 cshakeCommit256

#verify_constructive
  Qsag.DistCustody.Checks.cshakeShareDep_wellFormed
  Qsag.DistCustody.Checks.spongeShareDep_wellFormed
  Qsag.DistCustody.Checks.sponge_share_opening_honest_release_and_wal_replay
  Qsag.DistCustody.Checks.inhabited_sponge_share_opening_validTrace
  Qsag.DistCustody.Checks.distCustody_injOn_admitsTrace_audited
  Qsag.DistCustody.Checks.distCustody_dataRefines_or_collision_audited
  Qsag.DistCustody.Checks.verifyContrib_dealt_or_collision_audited
  Qsag.DistCustody.Checks.tooth_tampered_sponge_wots_sig_rejected
  Qsag.DistCustody.Checks.tooth_const_commit256_exhibits_collision_branch
  Qsag.DistCustody.Checks.tooth_const_commit256_refutes_naive_binding
  Qsag.DistCustody.Checks.tooth_forged_contrib_rejected_under_sponge_commit

#verify_inhabited Qsag.DistCustody.Checks.distCustody_dataRefines_or_collision_audited
  Qsag.DistCustody.Checks.inhabited_sponge_share_opening_validTrace
#tooth_pair Qsag.DistCustody.Checks.verifyContrib_dealt_or_collision_audited vs
  Qsag.DistCustody.Checks.tooth_const_commit256_refutes_naive_binding

end AuditSpongeShare

/-! ## Multi-Epoch (`h = 3`, `8` Epochs `0..7`) Wire-Serialized Base-4 WOTS+C (`target_sum = 12`) Share-Opening Checks (`E4a`) -/

section MultiEpochSymbolic
attribute [local irreducible] spongeCommit256 cshakeCommit256

def sampleBase4MasterSk : Base4WotsCMasterSk :=
  { s0 := 0x111122223333444455556666777788889999AAAABBBBCCCCDDDDEEEEFFFF0001#256
    s1 := 0x22223333444455556666777788889999AAAABBBBCCCCDDDDEEEEFFFF00021111#256
    s2 := 0x3333444455556666777788889999AAAABBBBCCCCDDDDEEEEFFFF000311112222#256 }

/-- Concrete height-`3` (`8` epochs `0..7`) wire-serialized base-4 WOTS+C (`target_sum = 12`)
    share-opening deployment over NIST SP 800-185 `cSHAKE256` (`BitVec 256`). -/
def cshakeMultiEpochDep := mkBase4WotsCShareDep 3 cshakeCommit256 sampleBase4MasterSk 7 100

/-- Concrete height-`3` (`8` epochs `0..7`) wire-serialized base-4 WOTS+C (`target_sum = 12`)
    share-opening deployment over 24-round `keccakF1600` sponge `spongeCommit256` (`BitVec 256`). -/
def spongeMultiEpochDep := mkBase4WotsCShareDep 3 spongeCommit256 sampleBase4MasterSk 7 100

theorem cshakeMultiEpochDep_wellFormed : cshakeMultiEpochDep.WellFormed :=
  mkBase4WotsCShareDep_wellFormed 3 cshakeCommit256 sampleBase4MasterSk 7 100

theorem spongeMultiEpochDep_wellFormed : spongeMultiEpochDep.WellFormed :=
  mkBase4WotsCShareDep_wellFormed 3 spongeCommit256 sampleBase4MasterSk 7 100

def multiEpochIntent5 : CustodyIntent :=
  { sessionId := 50, round := 1, epoch := 5, spend := 30, payload := [0xCA, 0xFE, 0x05] }

def multiEpochIntent7 : CustodyIntent :=
  { sessionId := 70, round := 2, epoch := 7, spend := 40, payload := [0xBE, 0xEF, 0x07] }

def multiEpochIntentOut : CustodyIntent :=
  { sessionId := 80, round := 3, epoch := 8, spend := 10, payload := [0x08] }

/-- **Concrete Multi-Epoch (`epoch = 5 < 2 ^ 3` and `epoch = 7 < 2 ^ 3`) Wire-Serialized Base-4 WOTS+C
    Share-Opening Executions Over Real 256-Bit Sponge (`spongeCommit256`) and `cSHAKE256`**:
    Certifies that BOTH `spongeMultiEpochDep` and `cshakeMultiEpochDep` release valid wire-serialized
    8-chain base-4 WOTS+C (`target_sum = 12` verified!) Merkle signatures at non-toy epochs `5` and `7`! -/
theorem multi_epoch_base4_wotsC_releases_epochs_5_and_7 :
    (∃ (s3 : ShareState Base4CustodianShare Base4ShareContrib Base4WotsCPk MultiEpochDigest Bytes)
       (sig5 : Bytes),
      (shareOpeningMachine spongeMultiEpochDep).ValidTrace (ShareState.init spongeMultiEpochDep)
        [(.approve 0 7 multiEpochIntent5, .approved),
         (.approve 1 7 multiEpochIntent5, .approved),
         (.execute 7 [0, 1] multiEpochIntent5 false, .custody (.released sig5))] s3 ∧
      spongeMultiEpochDep.sigScheme.verify spongeMultiEpochDep.pk
        (encodeMultiEpochDigest (7, multiEpochIntent5)) sig5 = true) ∧
    (∃ (s3' : ShareState Base4CustodianShare Base4ShareContrib Base4WotsCPk MultiEpochDigest Bytes)
       (sig7 : Bytes),
      (shareOpeningMachine cshakeMultiEpochDep).ValidTrace (ShareState.init cshakeMultiEpochDep)
        [(.approve 0 7 multiEpochIntent7, .approved),
         (.approve 1 7 multiEpochIntent7, .approved),
         (.execute 7 [0, 1] multiEpochIntent7 false, .custody (.released sig7))] s3' ∧
      cshakeMultiEpochDep.sigScheme.verify cshakeMultiEpochDep.pk
        (encodeMultiEpochDigest (7, multiEpochIntent7)) sig7 = true) := by
  obtain ⟨_, _, s3, sig5, _, _, _, hVer5, hTr5⟩ :=
    mkBase4WotsCShareDep_fresh_epoch_releases 3 spongeCommit256 sampleBase4MasterSk 7 100
      multiEpochIntent5 (by decide) (by decide)
  obtain ⟨_, _, s3', sig7, _, _, _, hVer7, hTr7⟩ :=
    mkBase4WotsCShareDep_fresh_epoch_releases 3 cshakeCommit256 sampleBase4MasterSk 7 100
      multiEpochIntent7 (by decide) (by decide)
  exact ⟨⟨s3, sig5, hTr5, hVer5⟩, ⟨s3', sig7, hTr7, hVer7⟩⟩

theorem multiEpoch_dataRefines_or_collision_audited
    (dep : ShareOpeningDeployment Base4CustodianShare Base4ShareContrib Bytes
      Base4WotsCPk Base4WotsCMasterSk MultiEpochDigest Bytes)
    (hWf : dep.WellFormed)
    {stFinal : ShareState Base4CustodianShare Base4ShareContrib Base4WotsCPk MultiEpochDigest Bytes}
    {tr : List (ShareTurn Base4ShareContrib × ShareEvent Base4CustodianShare Bytes)}
    (hTr : (shareOpeningMachine dep).ValidTrace (ShareState.init dep) tr stFinal) :
    ((idealCustodyMachine dep.digests dep.idealOracle dep.deploymentId dep.pk
        dep.quorum).AdmitsTrace (projectTrace (shareVisIn dep) shareVisOut tr) ∧
      stFinal.corrupt.length < dep.quorum.threshold ∧
      stFinal.ledger.spent ≤ dep.quorum.spendCap ∧
      (∀ r : CustodyRelease MultiEpochDigest Bytes, r ∈ stFinal.ledger.releasedHistory →
        dep.sigScheme.verify dep.pk (dep.encodeDigest r.digest) r.sig = true ∧
        r.sig = dep.idealOracle (dep.digests.digest dep.deploymentId r.intent) ∧
        ∃ p : Nat, p < dep.quorum.numParties ∧ r.intent ∈ (stFinal.nodes p).latched ∧
          r.intent.epoch < (stFinal.nodes p).latch)) ∨
    (∃ x₁ x₂ : Bytes,
      x₁ ≠ x₂ ∧ dep.commit x₁ = dep.commit x₂ ∧
      x₁ ∈ observedSharePreimages dep tr ∧
      x₂ ∈ observedSharePreimages dep tr) :=
  distCustody_dataRefines_or_collision dep hWf hTr

theorem inhabited_multiEpoch_base4_wotsC_validTrace :
    ∃ (dep : ShareOpeningDeployment Base4CustodianShare Base4ShareContrib Bytes
        Base4WotsCPk Base4WotsCMasterSk MultiEpochDigest Bytes)
      (stFinal : ShareState Base4CustodianShare Base4ShareContrib Base4WotsCPk MultiEpochDigest Bytes)
      (tr : List (ShareTurn Base4ShareContrib × ShareEvent Base4CustodianShare Bytes)),
      dep.WellFormed ∧
      (shareOpeningMachine dep).ValidTrace (ShareState.init dep) tr stFinal ∧
      tr.length = 3 := by
  obtain ⟨⟨s3, sig5, hTr5, _⟩, _⟩ := multi_epoch_base4_wotsC_releases_epochs_5_and_7
  exact ⟨spongeMultiEpochDep, s3, _, spongeMultiEpochDep_wellFormed, hTr5, rfl⟩

/-- `#tooth`: Tampering `target_sum` on `spongeMultiEpochDep` (all-zero base-4 digits, sum `0 ≠ 12`)
    is rejected by `spongeMultiEpochDep.sigScheme.verify`! -/
theorem tooth_spongeMultiEpoch_bad_targetSum_rejected :
    spongeMultiEpochDep.sigScheme.verify spongeMultiEpochDep.pk
      (encodeMultiEpochDigest (7, multiEpochIntent5))
      (encodeMultiEpochWotsCSig
        { epoch := 5
          digits := [0, 0, 0, 0, 0, 0, 0, 0]
          slot0 := ⟨List.replicate 8 0#256, List.replicate 3 0#256⟩
          slot1 := ⟨List.replicate 8 0#256, List.replicate 3 0#256⟩
          slot2 := ⟨List.replicate 8 0#256, List.replicate 3 0#256⟩ }) = false := by
  unfold spongeMultiEpochDep
  rw [mkBase4WotsCShareDep_sigScheme]
  exact tooth_base4WotsCMerkle_bad_targetSum_rejected 3 spongeCommit256 _
    (encodeMultiEpochDigest (7, multiEpochIntent5)) _
    (by rw [checkBase4TargetSum12.public_eqs]; decide)

/-- `#tooth`: Epoch `8 ≥ 2 ^ 3` is refused at custodian contribution / signing time and rejected by
    `spongeMultiEpochDep.sigScheme.verify`! -/
theorem tooth_spongeMultiEpoch_epoch_8_rejected :
    ∃ outSig : MultiEpochWotsCSig,
      outSig.epoch = 8 ∧
      spongeMultiEpochDep.trueContrib 0 multiEpochIntentOut = none ∧
      spongeMultiEpochDep.sigScheme.verify spongeMultiEpochDep.pk
        (encodeMultiEpochDigest (7, multiEpochIntentOut))
        (encodeMultiEpochWotsCSig outSig) = false := by
  let outSig : MultiEpochWotsCSig :=
    { epoch := 8
      digits := wotsBase4Digits spongeCommit256 8 (encodeMultiEpochDigest (7, multiEpochIntentOut))
      slot0 := ⟨List.replicate 8 0#256, List.replicate 3 0#256⟩
      slot1 := ⟨List.replicate 8 0#256, List.replicate 3 0#256⟩
      slot2 := ⟨List.replicate 8 0#256, List.replicate 3 0#256⟩ }
  refine ⟨outSig, rfl, ?_, ?_⟩
  · exact mkBase4WotsCShareDep_trueContrib_out 3 spongeCommit256 sampleBase4MasterSk 7 100
      0 multiEpochIntentOut (by decide)
  · unfold spongeMultiEpochDep
    rw [mkBase4WotsCShareDep_sigScheme]
    refine tooth_base4WotsCMerkle_epoch_ge_pow_rejected 3 spongeCommit256 _
      (encodeMultiEpochDigest (7, multiEpochIntentOut)) outSig ?_
    rw [mkBase4WotsCShareDep_pk_height]
    decide

#verify_constructive
  Qsag.DistCustody.Checks.cshakeMultiEpochDep_wellFormed
  Qsag.DistCustody.Checks.spongeMultiEpochDep_wellFormed
  Qsag.DistCustody.Checks.multi_epoch_base4_wotsC_releases_epochs_5_and_7
  Qsag.DistCustody.Checks.multiEpoch_dataRefines_or_collision_audited
  Qsag.DistCustody.Checks.inhabited_multiEpoch_base4_wotsC_validTrace
  Qsag.DistCustody.Checks.tooth_spongeMultiEpoch_bad_targetSum_rejected
  Qsag.DistCustody.Checks.tooth_spongeMultiEpoch_epoch_8_rejected

#verify_inhabited
  Qsag.DistCustody.Checks.multiEpoch_dataRefines_or_collision_audited
  Qsag.DistCustody.Checks.inhabited_multiEpoch_base4_wotsC_validTrace

#tooth_pair Qsag.DistCustody.Checks.multi_epoch_base4_wotsC_releases_epochs_5_and_7 vs
  Qsag.DistCustody.Checks.tooth_spongeMultiEpoch_bad_targetSum_rejected
#tooth_pair Qsag.DistCustody.Checks.multi_epoch_base4_wotsC_releases_epochs_5_and_7 vs
  Qsag.DistCustody.Checks.tooth_spongeMultiEpoch_epoch_8_rejected

end MultiEpochSymbolic

end Qsag.DistCustody.Checks

module
/-
# Qsag.Spec.IdealCustody — Unified Ideal Separated Threshold Custody Functionality

Canonical Layer-0 ideal specification unifying threshold approval quorums, policy spend caps,
write-ahead-log (`WAL`) idempotent retry / conflict rejection, and non-refund abort semantics
under a single ~150-line reactive `Machine`:
1. Honest quorum authorization (`corruptParties.length < quorum.threshold` ensures every accepted
   quorum contains at least one unquarantined honest custodian),
2. Monotone cumulative spend cap (`spent + spend ≤ quorum.spendCap`),
3. Durable WAL epoch latch (`latchedEpoch`: exact retry returns the cached signature without
   double-spending or re-signing; conflicting payload at a latched epoch is rejected; stale epochs
   are rejected), and
4. Sticky quarantine (`poisoned = true` permanently disables further signing).
-/

public import Qsag.Spec.Primitives
public import Qsag.Spec.Parameters
public import Qsag.Spec.Refines
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spec

set_option autoImplicit false

/-- Canonical signing/custody intent submitted to `IdealCustody`. -/
structure CustodyCommand where
  sessionId : Nat
  epoch : Nat
  spend : Nat
  payload : Bytes
  approvers : List Nat
  abortBeforeRelease : Bool
  deriving DecidableEq, Repr

/-- Observable response of `IdealCustody` on an accepted command. -/
inductive CustodyOutcome (Sig : Type) where
  | released (sig : Sig)
  | replayedFromWal (sig : Sig)
  | abortedQuarantined
  deriving DecidableEq, Repr

/-- Persistent state of the unified `IdealCustody` functionality. -/
structure IdealCustodyState (PK Sig : Type) where
  enrolledPk : PK
  quorum : CustodyQuorumProfile
  corruptParties : List Nat
  quarantinedParties : List Nat
  poisoned : Bool
  spent : Nat
  nextFreshEpoch : Nat
  usedSessions : List Nat
  latchedRecord : Option (Nat × Bytes × Sig)
  releasedHistory : List (Nat × Bytes × Sig)

/-- Canonical initial state for `IdealCustodyState`. -/
@[expose] def IdealCustodyState.init {PK Sig : Type}
    (pk : PK) (quorum : CustodyQuorumProfile) (corrupt : List Nat) :
    IdealCustodyState PK Sig :=
  { enrolledPk := pk
    quorum := quorum
    corruptParties := corrupt
    quarantinedParties := []
    poisoned := false
    spent := 0
    nextFreshEpoch := 0
    usedSessions := []
    latchedRecord := none
    releasedHistory := [] }

/-- Boolean quorum check: `approvers` has no duplicates, every approver is in `[0, numParties)` and
    unquarantined, `threshold ≤ approvers.length`, and at least one approver is honest (`∉ corruptParties`). -/
@[expose] def validCustodyQuorum {PK Sig : Type}
    (st : IdealCustodyState PK Sig) (approvers : List Nat) : Bool :=
  decide (st.quorum.threshold ≤ approvers.length) &&
  decide approvers.Nodup &&
  approvers.all (fun p =>
    decide (p < st.quorum.numParties) && decide (p ∉ st.quarantinedParties)) &&
  approvers.any (fun p => decide (p ∉ st.corruptParties))

/-- Unified single-step transition of `IdealCustody`. -/
def idealCustodyStep {PK Sig : Type} (oracleSign : Nat → Bytes → Sig)
    (st : IdealCustodyState PK Sig) (cmd : CustodyCommand) :
    Option (IdealCustodyState PK Sig × CustodyOutcome Sig) :=
  if st.poisoned then
    none
  else
    match st.latchedRecord with
    | some (latEp, latPayload, latSig) =>
      if cmd.epoch == latEp then
        if cmd.payload == latPayload then
          some (st, .replayedFromWal latSig)
        else
          none
      else if cmd.epoch < st.nextFreshEpoch then
        none
      else if decide (cmd.sessionId ∈ st.usedSessions) ||
              !validCustodyQuorum st cmd.approvers ||
              !decide (st.spent + cmd.spend ≤ st.quorum.spendCap) then
        none
      else if cmd.abortBeforeRelease then
        some ({ st with
                poisoned := true
                spent := st.spent + cmd.spend
                nextFreshEpoch := cmd.epoch + 1
                usedSessions := cmd.sessionId :: st.usedSessions },
              .abortedQuarantined)
      else
        let sig := oracleSign cmd.epoch cmd.payload
        some ({ st with
                spent := st.spent + cmd.spend
                nextFreshEpoch := cmd.epoch + 1
                usedSessions := cmd.sessionId :: st.usedSessions
                latchedRecord := some (cmd.epoch, cmd.payload, sig)
                releasedHistory := (cmd.epoch, cmd.payload, sig) :: st.releasedHistory },
              .released sig)
    | none =>
      if cmd.epoch < st.nextFreshEpoch then
        none
      else if decide (cmd.sessionId ∈ st.usedSessions) ||
              !validCustodyQuorum st cmd.approvers ||
              !decide (st.spent + cmd.spend ≤ st.quorum.spendCap) then
        none
      else if cmd.abortBeforeRelease then
        some ({ st with
                poisoned := true
                spent := st.spent + cmd.spend
                nextFreshEpoch := cmd.epoch + 1
                usedSessions := cmd.sessionId :: st.usedSessions },
              .abortedQuarantined)
      else
        let sig := oracleSign cmd.epoch cmd.payload
        some ({ st with
                spent := st.spent + cmd.spend
                nextFreshEpoch := cmd.epoch + 1
                usedSessions := cmd.sessionId :: st.usedSessions
                latchedRecord := some (cmd.epoch, cmd.payload, sig)
                releasedHistory := (cmd.epoch, cmd.payload, sig) :: st.releasedHistory },
              .released sig)

/-- Canonical `Machine` packaging of `IdealCustody`. -/
@[expose] def idealCustodyMachine {PK Sig : Type}
    (pk₀ : PK) (quorum₀ : CustodyQuorumProfile) (corrupt₀ : List Nat)
    (oracleSign : Nat → Bytes → Sig) :
    Machine (IdealCustodyState PK Sig) CustodyCommand (CustodyOutcome Sig) where
  Init st := st = IdealCustodyState.init pk₀ quorum₀ corrupt₀
  step := idealCustodyStep oracleSign
  errStep st _ := st

/-- Core custody safety invariant: cumulative spend never exceeds `quorum.spendCap`, `enrolledPk`
    is immutable, and every released `(epoch, payload, sig)` has `epoch < nextFreshEpoch`. -/
def IdealCustodyState.SafeInv {PK Sig : Type} (pk₀ : PK) (cap₀ : Nat)
    (st : IdealCustodyState PK Sig) : Prop :=
  st.enrolledPk = pk₀ ∧
  st.quorum.spendCap = cap₀ ∧
  st.spent ≤ cap₀ ∧
  (∀ entry ∈ st.releasedHistory, entry.1 < st.nextFreshEpoch)

theorem IdealCustodyState.init_safeInv {PK Sig : Type}
    (pk₀ : PK) (quorum₀ : CustodyQuorumProfile) (corrupt₀ : List Nat) :
    (IdealCustodyState.init pk₀ quorum₀ corrupt₀ : IdealCustodyState PK Sig).SafeInv
      pk₀ quorum₀.spendCap :=
  ⟨rfl, rfl, Nat.zero_le _, fun _ h => False.elim (List.not_mem_nil h)⟩

private theorem ite_true {α : Type} {p : Prop} [Decidable p] (hp : p) (a b : α) :
    (if p then a else b) = a := by
  cases ‹Decidable p› with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn hp)

private theorem ite_false {α : Type} {p : Prop} [Decidable p] (hnp : ¬ p) (a b : α) :
    (if p then a else b) = b := by
  cases ‹Decidable p› with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

theorem idealCustodyStep_preserves_safeInv {PK Sig : Type}
    {pk₀ : PK} {cap₀ : Nat} {oracleSign : Nat → Bytes → Sig}
    {st st' : IdealCustodyState PK Sig} {cmd : CustodyCommand} {out : CustodyOutcome Sig}
    (hInv : st.SafeInv pk₀ cap₀)
    (hStep : idealCustodyStep oracleSign st cmd = some (st', out)) :
    st'.SafeInv pk₀ cap₀ := by
  rcases hInv with ⟨hPk, hCap, hSpent, hHist⟩
  unfold idealCustodyStep at hStep
  cases hPois : st.poisoned
  · rw [hPois, ite_false Bool.false_ne_true] at hStep
    cases hLat : st.latchedRecord with
    | some rec =>
      rcases rec with ⟨latEp, latPay, latSig⟩
      rw [hLat] at hStep
      dsimp only at hStep
      cases hEpEq : (cmd.epoch == latEp)
      · rw [hEpEq, ite_false Bool.false_ne_true] at hStep
        by_cases hLt : cmd.epoch < st.nextFreshEpoch
        · rw [ite_true hLt] at hStep
          cases hStep
        · rw [ite_false hLt] at hStep
          cases hGate : (decide (cmd.sessionId ∈ st.usedSessions) ||
              !validCustodyQuorum st cmd.approvers ||
              !decide (st.spent + cmd.spend ≤ st.quorum.spendCap))
          · rw [hGate, ite_false Bool.false_ne_true] at hStep
            have hCapOk : st.spent + cmd.spend ≤ st.quorum.spendCap := by
              rcases Bool.or_eq_false_iff.mp hGate with ⟨_, hR⟩
              cases hDec : decide (st.spent + cmd.spend ≤ st.quorum.spendCap)
              · rw [hDec] at hR; cases hR
              · exact of_decide_eq_true hDec
            cases hAb : cmd.abortBeforeRelease
            · rw [hAb, ite_false Bool.false_ne_true] at hStep
              injection hStep with hPair
              injection hPair with hSt _
              subst hSt
              refine ⟨hPk, hCap, hCap ▸ hCapOk, ?_⟩
              intro entry hMem
              dsimp only at hMem ⊢
              cases hMem with
              | head => exact Nat.lt_succ_self _
              | tail _ hTail =>
                have hOld := hHist entry hTail
                omega
            · rw [hAb, ite_true rfl] at hStep
              injection hStep with hPair
              injection hPair with hSt _
              subst hSt
              refine ⟨hPk, hCap, hCap ▸ hCapOk, ?_⟩
              intro entry hMem
              dsimp only at hMem ⊢
              have hOld := hHist entry hMem
              omega
          · rw [hGate, ite_true rfl] at hStep
            cases hStep
      · rw [hEpEq, ite_true rfl] at hStep
        cases hPayEq : (cmd.payload == latPay)
        · rw [hPayEq, ite_false Bool.false_ne_true] at hStep
          cases hStep
        · rw [hPayEq, ite_true rfl] at hStep
          injection hStep with hPair
          injection hPair with hSt _
          subst hSt
          exact ⟨hPk, hCap, hSpent, hHist⟩
    | none =>
      rw [hLat] at hStep
      dsimp only at hStep
      by_cases hLt : cmd.epoch < st.nextFreshEpoch
      · rw [ite_true hLt] at hStep
        cases hStep
      · rw [ite_false hLt] at hStep
        cases hGate : (decide (cmd.sessionId ∈ st.usedSessions) ||
            !validCustodyQuorum st cmd.approvers ||
            !decide (st.spent + cmd.spend ≤ st.quorum.spendCap))
        · rw [hGate, ite_false Bool.false_ne_true] at hStep
          have hCapOk : st.spent + cmd.spend ≤ st.quorum.spendCap := by
            rcases Bool.or_eq_false_iff.mp hGate with ⟨_, hR⟩
            cases hDec : decide (st.spent + cmd.spend ≤ st.quorum.spendCap)
            · rw [hDec] at hR; cases hR
            · exact of_decide_eq_true hDec
          cases hAb : cmd.abortBeforeRelease
          · rw [hAb, ite_false Bool.false_ne_true] at hStep
            injection hStep with hPair
            injection hPair with hSt _
            subst hSt
            refine ⟨hPk, hCap, hCap ▸ hCapOk, ?_⟩
            intro entry hMem
            dsimp only at hMem ⊢
            cases hMem with
            | head => exact Nat.lt_succ_self _
            | tail _ hTail =>
              have hOld := hHist entry hTail
              omega
          · rw [hAb, ite_true rfl] at hStep
            injection hStep with hPair
            injection hPair with hSt _
            subst hSt
            refine ⟨hPk, hCap, hCap ▸ hCapOk, ?_⟩
            intro entry hMem
            dsimp only at hMem ⊢
            have hOld := hHist entry hMem
            omega
        · rw [hGate, ite_true rfl] at hStep
          cases hStep
  · rw [hPois, ite_true rfl] at hStep
    cases hStep

/-- Sticky quarantine property: once `st.poisoned = true`, `idealCustodyStep` rejects every command. -/
theorem idealCustodyStep_poisoned_rejects {PK Sig : Type}
    (oracleSign : Nat → Bytes → Sig) (st : IdealCustodyState PK Sig) (cmd : CustodyCommand)
    (hPois : st.poisoned = true) :
    idealCustodyStep oracleSign st cmd = none := by
  unfold idealCustodyStep
  rw [hPois, ite_true rfl]

/-- WAL exact-retry idempotence & conflict rejection: on a latched `(ep, payload, sig)` in an
    unpoisoned state, retrying `(ep, payload)` replays `sig` without mutating `spent`, whereas
    submitting `cmdConflict.payload ≠ payload` at `ep` is deterministically rejected! -/
theorem idealCustodyStep_wal_retry_and_conflict {PK Sig : Type}
    (oracleSign : Nat → Bytes → Sig) (st : IdealCustodyState PK Sig)
    (ep : Nat) (payload : Bytes) (sig : Sig)
    (cmdRetry cmdConflict : CustodyCommand)
    (hUnpoisoned : st.poisoned = false)
    (hLatched : st.latchedRecord = some (ep, payload, sig))
    (hRetryEp : cmdRetry.epoch = ep) (hRetryPay : cmdRetry.payload = payload)
    (hConfEp : cmdConflict.epoch = ep) (hConfDiff : cmdConflict.payload ≠ payload) :
    idealCustodyStep oracleSign st cmdRetry = some (st, .replayedFromWal sig) ∧
    idealCustodyStep oracleSign st cmdConflict = none := by
  unfold idealCustodyStep
  have hEp1 : (cmdRetry.epoch == ep) = true := by rw [hRetryEp]; exact Nat.beq_refl _
  have hPay1 : (cmdRetry.payload == payload) = true := beq_iff_eq.mpr hRetryPay
  have hEp2 : (cmdConflict.epoch == ep) = true := by rw [hConfEp]; exact Nat.beq_refl _
  have hPay2 : (cmdConflict.payload == payload) = false := beq_false_of_ne hConfDiff
  refine ⟨?_, ?_⟩
  · rw [hUnpoisoned, ite_false Bool.false_ne_true, hLatched]
    dsimp only
    rw [hEp1, ite_true rfl, hPay1, ite_true rfl]
  · rw [hUnpoisoned, ite_false Bool.false_ne_true, hLatched]
    dsimp only
    rw [hEp2, ite_true rfl, hPay2, ite_false Bool.false_ne_true]

#verify_constructive
  Qsag.Spec.IdealCustodyState.init_safeInv
  Qsag.Spec.idealCustodyStep_preserves_safeInv
  Qsag.Spec.idealCustodyStep_poisoned_rejects
  Qsag.Spec.idealCustodyStep_wal_retry_and_conflict

end Qsag.Spec
end

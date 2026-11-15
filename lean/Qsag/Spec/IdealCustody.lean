module
/-
# Qsag.Spec.IdealCustody — Unified Ideal Separated Threshold Custody Functionality

Canonical Layer-0 ideal specification unifying threshold approval quorums, policy spend caps,
write-ahead-log (`WAL`) multi-epoch idempotent retry / conflict rejection, and non-refund abort
semantics under a single reactive `Machine`:
1. Honest quorum authorization (`corruptParties.length < quorum.threshold` ensures every accepted
   quorum contains at least one unquarantined honest custodian),
2. Monotone cumulative spend cap (`spent + spend ≤ quorum.spendCap`),
3. Durable WAL epoch history lookup (`findReleasedEpoch st.releasedHistory cmd.epoch`: retrying
   **any** previously committed `(epoch, payload)` replays its cached signature without
   double-spending or re-signing; conflicting payload at any committed epoch is deterministically
   rejected; uncommitted stale epochs `< nextFreshEpoch` are rejected), and
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

/-- Persistent state of the unified `IdealCustody` functionality (multi-epoch `releasedHistory`
    serves directly as the durable WAL replay table without single-slot truncation). -/
structure IdealCustodyState (PK Sig : Type) where
  enrolledPk : PK
  quorum : CustodyQuorumProfile
  corruptParties : List Nat
  quarantinedParties : List Nat
  poisoned : Bool
  spent : Nat
  nextFreshEpoch : Nat
  usedSessions : List Nat
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
    releasedHistory := [] }

/-- Look up a committed `(payload, sig)` record for `ep` across the full durable WAL history. -/
@[expose] def findReleasedEpoch {Sig : Type}
    (hist : List (Nat × Bytes × Sig)) (ep : Nat) : Option (Bytes × Sig) :=
  match hist with
  | [] => none
  | (e, pay, sig) :: rest =>
    if ep == e then some (pay, sig) else findReleasedEpoch rest ep

/-- Boolean quorum check: `approvers` has no duplicates, every approver is in `[0, numParties)` and
    unquarantined, `threshold ≤ approvers.length`, and at least one approver is honest (`∉ corruptParties`). -/
@[expose] def validCustodyQuorum {PK Sig : Type}
    (st : IdealCustodyState PK Sig) (approvers : List Nat) : Bool :=
  decide (st.quorum.threshold ≤ approvers.length) &&
  decide approvers.Nodup &&
  approvers.all (fun p =>
    decide (p < st.quorum.numParties) && decide (p ∉ st.quarantinedParties)) &&
  approvers.any (fun p => decide (p ∉ st.corruptParties))

/-- Unified single-step transition of `IdealCustody` with full historical epoch WAL lookup. -/
def idealCustodyStep {PK Sig : Type} (oracleSign : Nat → Bytes → Sig)
    (st : IdealCustodyState PK Sig) (cmd : CustodyCommand) :
    Option (IdealCustodyState PK Sig × CustodyOutcome Sig) :=
  if st.poisoned then
    none
  else
    match findReleasedEpoch st.releasedHistory cmd.epoch with
    | some (latPayload, latSig) =>
      if cmd.payload == latPayload then
        some (st, .replayedFromWal latSig)
      else
        none
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
    is immutable, every committed `(epoch, payload, sig)` has `epoch < nextFreshEpoch`, and
    committed epochs in `releasedHistory` are pairwise distinct (`Nodup` on `Prod.fst`). -/
def IdealCustodyState.SafeInv {PK Sig : Type} (pk₀ : PK) (cap₀ : Nat)
    (st : IdealCustodyState PK Sig) : Prop :=
  st.enrolledPk = pk₀ ∧
  st.quorum.spendCap = cap₀ ∧
  st.spent ≤ cap₀ ∧
  (∀ entry ∈ st.releasedHistory, entry.1 < st.nextFreshEpoch) ∧
  (st.releasedHistory.map Prod.fst).Nodup

theorem IdealCustodyState.init_safeInv {PK Sig : Type}
    (pk₀ : PK) (quorum₀ : CustodyQuorumProfile) (corrupt₀ : List Nat) :
    (IdealCustodyState.init pk₀ quorum₀ corrupt₀ : IdealCustodyState PK Sig).SafeInv
      pk₀ quorum₀.spendCap :=
  ⟨rfl, rfl, Nat.zero_le _, fun _ h => False.elim (List.not_mem_nil h), List.Pairwise.nil⟩

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

/-- If `(ep, pay, sig) ∈ hist` and committed epochs in `hist` are pairwise distinct, then
    `findReleasedEpoch hist ep = some (pay, sig)` (regardless of how many newer epochs were committed after `ep`!). -/
theorem findReleasedEpoch_of_mem_nodup {Sig : Type}
    {hist : List (Nat × Bytes × Sig)} {ep : Nat} {pay : Bytes} {sig : Sig}
    (hMem : (ep, pay, sig) ∈ hist)
    (hNd : (hist.map Prod.fst).Nodup) :
    findReleasedEpoch hist ep = some (pay, sig) := by
  induction hist with
  | nil => cases hMem
  | cons hd tl ih =>
    rcases hd with ⟨eHd, payHd, sigHd⟩
    simp only [List.map_cons, List.nodup_cons] at hNd
    rcases hNd with ⟨hNotInTl, hNdTl⟩
    unfold findReleasedEpoch
    cases hMem with
    | head =>
      rw [beq_self_eq_true, ite_true rfl]
    | tail _ hInTl =>
      have hNe : ep ≠ eHd := by
        intro hEq
        subst hEq
        exact hNotInTl (List.mem_map_of_mem (f := Prod.fst) hInTl)
      have hBeqF : (ep == eHd) = false := beq_false_of_ne hNe
      rw [hBeqF, ite_false Bool.false_ne_true]
      exact ih hInTl hNdTl

theorem idealCustodyStep_preserves_safeInv {PK Sig : Type}
    {pk₀ : PK} {cap₀ : Nat} {oracleSign : Nat → Bytes → Sig}
    {st st' : IdealCustodyState PK Sig} {cmd : CustodyCommand} {out : CustodyOutcome Sig}
    (hInv : st.SafeInv pk₀ cap₀)
    (hStep : idealCustodyStep oracleSign st cmd = some (st', out)) :
    st'.SafeInv pk₀ cap₀ := by
  rcases hInv with ⟨hPk, hCap, hSpent, hHist, hNd⟩
  unfold idealCustodyStep at hStep
  cases hPois : st.poisoned
  · rw [hPois, ite_false Bool.false_ne_true] at hStep
    cases hFind : findReleasedEpoch st.releasedHistory cmd.epoch with
    | some rec =>
      rcases rec with ⟨latPay, latSig⟩
      rw [hFind] at hStep
      dsimp only at hStep
      cases hPayEq : (cmd.payload == latPay)
      · rw [hPayEq, ite_false Bool.false_ne_true] at hStep
        cases hStep
      · rw [hPayEq, ite_true rfl] at hStep
        injection hStep with hPair
        injection hPair with hSt _
        subst hSt
        exact ⟨hPk, hCap, hSpent, hHist, hNd⟩
    | none =>
      rw [hFind] at hStep
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
            refine ⟨hPk, hCap, hCap ▸ hCapOk, ?_, ?_⟩
            · intro entry hMem
              dsimp only at hMem ⊢
              cases hMem with
              | head => exact Nat.lt_succ_self _
              | tail _ hTail =>
                have hOld := hHist entry hTail
                omega
            · dsimp only
              rw [List.map_cons, List.nodup_cons]
              refine ⟨?_, hNd⟩
              intro hMemMap
              rcases List.mem_map.mp hMemMap with ⟨entry, hEntryMem, hFstEq⟩
              have hEntryLt := hHist entry hEntryMem
              omega
          · rw [hAb, ite_true rfl] at hStep
            injection hStep with hPair
            injection hPair with hSt _
            subst hSt
            refine ⟨hPk, hCap, hCap ▸ hCapOk, ?_, hNd⟩
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

/-- Multi-epoch historical WAL idempotent retry & conflict rejection: for **any** committed record
    `(ep, payload, sig) ∈ st.releasedHistory` (including earlier epochs after newer epochs have
    advanced `nextFreshEpoch`!), retrying `(ep, payload)` replays `sig` without mutating `spent`,
    whereas submitting `cmdConflict.payload ≠ payload` at `ep` is deterministically rejected! -/
theorem idealCustodyStep_wal_retry_and_conflict {PK Sig : Type}
    {pk₀ : PK} {cap₀ : Nat}
    (oracleSign : Nat → Bytes → Sig) (st : IdealCustodyState PK Sig)
    (ep : Nat) (payload : Bytes) (sig : Sig)
    (cmdRetry cmdConflict : CustodyCommand)
    (hInv : st.SafeInv pk₀ cap₀)
    (hUnpoisoned : st.poisoned = false)
    (hCommitted : (ep, payload, sig) ∈ st.releasedHistory)
    (hRetryEp : cmdRetry.epoch = ep) (hRetryPay : cmdRetry.payload = payload)
    (hConfEp : cmdConflict.epoch = ep) (hConfDiff : cmdConflict.payload ≠ payload) :
    idealCustodyStep oracleSign st cmdRetry = some (st, .replayedFromWal sig) ∧
    idealCustodyStep oracleSign st cmdConflict = none := by
  have hLookup := findReleasedEpoch_of_mem_nodup hCommitted hInv.2.2.2.2
  have hPay1 : (cmdRetry.payload == payload) = true := beq_iff_eq.mpr hRetryPay
  have hPay2 : (cmdConflict.payload == payload) = false := beq_false_of_ne hConfDiff
  unfold idealCustodyStep
  refine ⟨?_, ?_⟩
  · rw [hUnpoisoned, ite_false Bool.false_ne_true, hRetryEp, hLookup]
    dsimp only
    rw [hPay1, ite_true rfl]
  · rw [hUnpoisoned, ite_false Bool.false_ne_true, hConfEp, hLookup]
    dsimp only
    rw [hPay2, ite_false Bool.false_ne_true]

#verify_constructive
  Qsag.Spec.IdealCustodyState.init_safeInv
  Qsag.Spec.findReleasedEpoch_of_mem_nodup
  Qsag.Spec.idealCustodyStep_preserves_safeInv
  Qsag.Spec.idealCustodyStep_poisoned_rejects
  Qsag.Spec.idealCustodyStep_wal_retry_and_conflict

end Qsag.Spec
end

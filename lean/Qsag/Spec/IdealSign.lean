module
/-
# Qsag.Spec.IdealSign — Ideal Standalone and Epoch-Stateful Signing Specification

Layer-0 ideal specification for standalone and one-time-epoch-stateful digital signatures:
1. `SigScheme` interface (`derivePk`, `sign`, `verify`, correctness),
2. Reactive `idealSignMachine S pk₀ stateful₀ maxWindow oracleSign`. A candidate signature
   proposed by `oracleSign` is emitted only if `S.verify enrolledPk` accepts it. In stateful mode
   an epoch is admissible when `nextEpoch ≤ epoch ≤ nextEpoch + maxWindow` (the bounded jump
   window of `BeltLatch`), and an admitted request moves `nextEpoch` to `epoch + 1`.
3. Failure semantics: **burn**. A request with an inadmissible epoch is rejected and leaves the
   state unchanged. A request with an admissible epoch whose signing fails (no candidate, or a
   candidate the verifier rejects) is rejected and still consumes the epoch; the machine stays
   live for later epochs. This is the order of `BeltLatch`, which persists `nextEpoch` before a
   signature exists. Quarantine after a storage failure is a property of the latch's write-ahead
   log and is not part of this functionality.
4. Safety: every emitted signature verifies under the enrolled key; in stateful mode the epochs
   of the accepted requests of a trace are strictly increasing, so no epoch signs twice.
5. `latchedSignerMachine`, the signer that runs `S.sign` behind the same epoch latch, refines the
   ideal machine (`latchedSigner_refines_ideal`).
6. Existential (`EufCmaForgery`) and strong (`SufCmaForgery`) unforgeability predicates.
-/

public import Qsag.Spec.Primitives
public import Qsag.Spec.Parameters
public import Qsag.Spec.Refines
public import Qsag.Spec.GameBound
public import Qsag.Spec.Assumptions
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spec

set_option autoImplicit false

/-- Abstract signature scheme interface parameterized by public key `PK`, secret key `SK`,
    and signature `Sig`. -/
structure SigScheme (PK SK Sig : Type) where
  derivePk : SK → PK
  sign : SK → Nat → Bytes → Option Sig
  verify : PK → Bytes → Sig → Bool
  correct : ∀ (sk : SK) (ep : Nat) (msg : Bytes) (sig : Sig),
    sign sk ep msg = some sig → verify (derivePk sk) msg sig = true

private theorem signAndSplit {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h

private theorem signIteSome {α : Type} {c : Bool} {x : Option α} {y : α}
    (h : (if c = true then x else none) = some y) : c = true ∧ x = some y := by
  cases c with
  | false =>
    have h2 : (none : Option α) = some y := h
    cases h2
  | true => exact ⟨rfl, h⟩

private theorem signMapSome {α β : Type} {x : Option α} {f : α → β} {y : β}
    (h : x.map f = some y) : ∃ s, x = some s ∧ f s = y := by
  cases x with
  | none =>
    have h2 : (none : Option β) = some y := h
    cases h2
  | some s => exact ⟨s, rfl, Option.some.inj h⟩

/-- Signing request: target epoch and message bytes. -/
structure SignRequest where
  epoch : Nat
  message : Bytes
  deriving DecidableEq, Repr

/-- Epoch admissibility. Stateless schemes admit every epoch. A stateful scheme admits the
    epochs of the window `nextEpoch ≤ epoch ≤ nextEpoch + maxWindow`. -/
@[expose] def epochAdmissible (stateful : Bool) (maxWindow nextEpoch epoch : Nat) : Bool :=
  !stateful || (decide (nextEpoch ≤ epoch) && decide (epoch ≤ nextEpoch + maxWindow))

theorem epochAdmissible_stateful {maxWindow nextEpoch epoch : Nat}
    (h : epochAdmissible true maxWindow nextEpoch epoch = true) :
    nextEpoch ≤ epoch ∧ epoch ≤ nextEpoch + maxWindow := by
  have h' : (decide (nextEpoch ≤ epoch) && decide (epoch ≤ nextEpoch + maxWindow)) = true := h
  exact ⟨of_decide_eq_true (signAndSplit h').1, of_decide_eq_true (signAndSplit h').2⟩

/-- A stateful latch does not admit an epoch below `nextEpoch`. -/
theorem epochAdmissible_consumed {maxWindow nextEpoch epoch : Nat} (h : epoch < nextEpoch) :
    epochAdmissible true maxWindow nextEpoch epoch = false := by
  cases hA : epochAdmissible true maxWindow nextEpoch epoch with
  | false => rfl
  | true => exact absurd (epochAdmissible_stateful hA).1 (Nat.not_le_of_lt h)

/-- Persistent state of the ideal signing functionality. `nextEpoch` is the least epoch a
    stateful scheme still admits, `usedEpochs` the consumed epochs (signed or burned), newest
    first, and `signedLog` the emitted `(epoch, message, signature)` triples, newest first. -/
structure IdealSignState (PK Sig : Type) where
  enrolledPk : PK
  statefulEpochs : Bool
  nextEpoch : Nat
  usedEpochs : List Nat
  signedLog : List (Nat × Bytes × Sig)

/-- Initial state: nothing consumed, nothing signed. -/
@[expose] def IdealSignState.empty {PK Sig : Type} (pk : PK) (stateful : Bool) :
    IdealSignState PK Sig :=
  { enrolledPk := pk
    statefulEpochs := stateful
    nextEpoch := 0
    usedEpochs := []
    signedLog := [] }

/-- Consume epoch `ep`: it and every lower epoch are no longer admissible. -/
@[expose] def IdealSignState.consume {PK Sig : Type} (st : IdealSignState PK Sig) (ep : Nat) :
    IdealSignState PK Sig :=
  { st with nextEpoch := ep + 1, usedEpochs := ep :: st.usedEpochs }

/-- Consume the request's epoch and log the emitted signature. -/
@[expose] def IdealSignState.record {PK Sig : Type} (st : IdealSignState PK Sig)
    (req : SignRequest) (sig : Sig) : IdealSignState PK Sig :=
  { st.consume req.epoch with signedLog := (req.epoch, req.message, sig) :: st.signedLog }

/-- The candidate proposed by `oracleSign`, kept only if `S.verify pk` accepts it. -/
@[expose] def verifiedCandidate {PK SK Sig : Type} (S : SigScheme PK SK Sig) (pk : PK)
    (oracleSign : SignRequest → Option Sig) (req : SignRequest) : Option Sig :=
  match oracleSign req with
  | some sig => if S.verify pk req.message sig = true then some sig else none
  | none => none

theorem verifiedCandidate_some {PK SK Sig : Type} {S : SigScheme PK SK Sig} {pk : PK}
    {oracleSign : SignRequest → Option Sig} {req : SignRequest} {sig : Sig}
    (h : verifiedCandidate S pk oracleSign req = some sig) :
    oracleSign req = some sig ∧ S.verify pk req.message sig = true := by
  unfold verifiedCandidate at h
  cases hO : oracleSign req with
  | none =>
    rw [hO] at h
    cases h
  | some s =>
    rw [hO] at h
    have h' : (if S.verify pk req.message s = true then some s else none) = some sig := h
    obtain ⟨hV, hEq⟩ := signIteSome h'
    have hs : s = sig := Option.some.inj hEq
    exact ⟨congrArg some hs, hs ▸ hV⟩

theorem verifiedCandidate_of_valid {PK SK Sig : Type} {S : SigScheme PK SK Sig} {pk : PK}
    {oracleSign : SignRequest → Option Sig} {req : SignRequest} {sig : Sig}
    (hO : oracleSign req = some sig) (hV : S.verify pk req.message sig = true) :
    verifiedCandidate S pk oracleSign req = some sig := by
  unfold verifiedCandidate
  rw [hO]
  show (if S.verify pk req.message sig = true then some sig else none) = some sig
  rw [hV]
  rfl

theorem verifiedCandidate_of_none {PK SK Sig : Type} {S : SigScheme PK SK Sig} {pk : PK}
    {oracleSign : SignRequest → Option Sig} {req : SignRequest}
    (hO : oracleSign req = none) : verifiedCandidate S pk oracleSign req = none := by
  unfold verifiedCandidate
  rw [hO]

/-- **Ideal signing machine** for the scheme `S` and enrolled key `pk₀`.

    `step`: if the request's epoch is admissible and the candidate `oracleSign req` is accepted
    by `S.verify enrolledPk`, emit it, consume the epoch and log the triple; otherwise reject.
    `errStep` (the state after a rejection): an inadmissible epoch leaves the state unchanged;
    an admissible epoch whose signing failed is consumed. -/
@[expose] def idealSignMachine {PK SK Sig : Type} (S : SigScheme PK SK Sig)
    (pk₀ : PK) (stateful₀ : Bool) (maxWindow : Nat) (oracleSign : SignRequest → Option Sig) :
    Machine (IdealSignState PK Sig) SignRequest Sig where
  Init st := st = IdealSignState.empty pk₀ stateful₀
  step st req :=
    if epochAdmissible st.statefulEpochs maxWindow st.nextEpoch req.epoch = true then
      (verifiedCandidate S st.enrolledPk oracleSign req).map (fun sig => (st.record req sig, sig))
    else none
  errStep st req :=
    if epochAdmissible st.statefulEpochs maxWindow st.nextEpoch req.epoch = true then
      st.consume req.epoch
    else st

section Machine
variable {PK SK Sig : Type} {S : SigScheme PK SK Sig} {pk₀ : PK} {stateful₀ : Bool}
  {maxWindow : Nat} {oracleSign : SignRequest → Option Sig}

/-- An accepted request has an admissible epoch, its output is the oracle's candidate, the
    candidate verifies under the enrolled key, and the new state records it. -/
theorem idealSignMachine_step_some {st st' : IdealSignState PK Sig} {req : SignRequest}
    {sig : Sig}
    (h : (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).step st req = some (st', sig)) :
    epochAdmissible st.statefulEpochs maxWindow st.nextEpoch req.epoch = true ∧
    oracleSign req = some sig ∧
    S.verify st.enrolledPk req.message sig = true ∧
    st' = st.record req sig := by
  have h' : (if epochAdmissible st.statefulEpochs maxWindow st.nextEpoch req.epoch = true then
      (verifiedCandidate S st.enrolledPk oracleSign req).map (fun sig => (st.record req sig, sig))
      else none) = some (st', sig) := h
  obtain ⟨hA, hMap⟩ := signIteSome h'
  obtain ⟨s, hC, hPair⟩ := signMapSome hMap
  have hs : s = sig := congrArg Prod.snd hPair
  have hSt : st.record req s = st' := congrArg Prod.fst hPair
  obtain ⟨hO, hV⟩ := verifiedCandidate_some hC
  exact ⟨hA, hs ▸ hO, hs ▸ hV, hs ▸ hSt.symm⟩

/-- **Emitted signatures verify.** -/
theorem idealSignMachine_step_emits_verified {st st' : IdealSignState PK Sig}
    {req : SignRequest} {sig : Sig}
    (h : (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).step st req = some (st', sig)) :
    S.verify st.enrolledPk req.message sig = true :=
  (idealSignMachine_step_some h).2.2.1

theorem idealSignMachine_step_of_valid {st : IdealSignState PK Sig} {req : SignRequest}
    {sig : Sig}
    (hA : epochAdmissible st.statefulEpochs maxWindow st.nextEpoch req.epoch = true)
    (hO : oracleSign req = some sig) (hV : S.verify st.enrolledPk req.message sig = true) :
    (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).step st req =
      some (st.record req sig, sig) := by
  show (if epochAdmissible st.statefulEpochs maxWindow st.nextEpoch req.epoch = true then
      (verifiedCandidate S st.enrolledPk oracleSign req).map (fun sig => (st.record req sig, sig))
      else none) = some (st.record req sig, sig)
  rw [hA, verifiedCandidate_of_valid hO hV]
  rfl

theorem idealSignMachine_step_of_inadmissible {st : IdealSignState PK Sig} {req : SignRequest}
    (hA : epochAdmissible st.statefulEpochs maxWindow st.nextEpoch req.epoch = false) :
    (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).step st req = none := by
  show (if epochAdmissible st.statefulEpochs maxWindow st.nextEpoch req.epoch = true then
      (verifiedCandidate S st.enrolledPk oracleSign req).map (fun sig => (st.record req sig, sig))
      else none) = none
  rw [hA]
  rfl

theorem idealSignMachine_step_of_no_candidate {st : IdealSignState PK Sig} {req : SignRequest}
    (hO : oracleSign req = none) :
    (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).step st req = none := by
  show (if epochAdmissible st.statefulEpochs maxWindow st.nextEpoch req.epoch = true then
      (verifiedCandidate S st.enrolledPk oracleSign req).map (fun sig => (st.record req sig, sig))
      else none) = none
  rw [verifiedCandidate_of_none hO]
  cases epochAdmissible st.statefulEpochs maxWindow st.nextEpoch req.epoch <;> rfl

theorem idealSignMachine_errStep_of_admissible {st : IdealSignState PK Sig} {req : SignRequest}
    (hA : epochAdmissible st.statefulEpochs maxWindow st.nextEpoch req.epoch = true) :
    (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).errStep st req =
      st.consume req.epoch := by
  show (if epochAdmissible st.statefulEpochs maxWindow st.nextEpoch req.epoch = true then
      st.consume req.epoch else st) = st.consume req.epoch
  rw [hA]
  rfl

theorem idealSignMachine_errStep_of_inadmissible {st : IdealSignState PK Sig}
    {req : SignRequest}
    (hA : epochAdmissible st.statefulEpochs maxWindow st.nextEpoch req.epoch = false) :
    (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).errStep st req = st := by
  show (if epochAdmissible st.statefulEpochs maxWindow st.nextEpoch req.epoch = true then
      st.consume req.epoch else st) = st
  rw [hA]
  rfl

/-- **A stateful machine rejects every epoch below `nextEpoch`.** -/
theorem idealSignMachine_rejects_consumed_epoch {st : IdealSignState PK Sig} {req : SignRequest}
    (hStateful : st.statefulEpochs = true) (hLt : req.epoch < st.nextEpoch) :
    (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).step st req = none := by
  apply idealSignMachine_step_of_inadmissible
  rw [hStateful]
  exact epochAdmissible_consumed hLt

/-- **Burn.** In stateful mode, after a rejected request with an admissible epoch, that epoch
    and every lower one are rejected: a failed signing consumes its epoch. -/
theorem idealSignMachine_failed_sign_burns_epoch {st : IdealSignState PK Sig}
    {req req' : SignRequest}
    (hStateful : st.statefulEpochs = true)
    (hA : epochAdmissible st.statefulEpochs maxWindow st.nextEpoch req.epoch = true)
    (hLe : req'.epoch ≤ req.epoch) :
    (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).step
      ((idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).errStep st req) req' = none := by
  rw [idealSignMachine_errStep_of_admissible hA]
  exact idealSignMachine_rejects_consumed_epoch (st := st.consume req.epoch) hStateful
    (Nat.lt_succ_of_le hLe)

/-- State invariant: every logged signature verifies under the enrolled key and its epoch is
    consumed; in stateful mode the consumed epochs are strictly decreasing (newest first) and
    below `nextEpoch`, and the logged epochs are strictly decreasing. -/
def IdealSignState.Inv (S : SigScheme PK SK Sig) (st : IdealSignState PK Sig) : Prop :=
  (∀ e ∈ st.signedLog, S.verify st.enrolledPk e.2.1 e.2.2 = true ∧ e.1 ∈ st.usedEpochs) ∧
  (st.statefulEpochs = true →
    st.usedEpochs.Pairwise (fun a b => b < a) ∧
    (∀ ep ∈ st.usedEpochs, ep < st.nextEpoch) ∧
    st.signedLog.Pairwise (fun a b => b.1 < a.1))

theorem IdealSignState.empty_inv (S : SigScheme PK SK Sig) (pk : PK) (stateful : Bool) :
    (IdealSignState.empty pk stateful : IdealSignState PK Sig).Inv S :=
  ⟨fun _ h => (nomatch h), fun _ => ⟨.nil, fun _ h => (nomatch h), .nil⟩⟩

theorem IdealSignState.Inv.consume {st : IdealSignState PK Sig} (hInv : st.Inv S) (ep : Nat)
    (hAdm : st.statefulEpochs = true → st.nextEpoch ≤ ep) : (st.consume ep).Inv S := by
  obtain ⟨hLog, hSt⟩ := hInv
  refine ⟨fun e he => ⟨(hLog e he).1, List.mem_cons_of_mem _ (hLog e he).2⟩, fun hS => ?_⟩
  obtain ⟨hPw, hLt, hLogPw⟩ := hSt hS
  have hNext := hAdm hS
  refine ⟨.cons (fun b hb => Nat.lt_of_lt_of_le (hLt b hb) hNext) hPw, fun x hx => ?_, hLogPw⟩
  show x < ep + 1
  rcases List.mem_cons.mp hx with hEq | hOld
  · rw [hEq]
    exact Nat.lt_succ_self ep
  · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (hLt x hOld) hNext)

theorem IdealSignState.Inv.record {st : IdealSignState PK Sig} (hInv : st.Inv S)
    (req : SignRequest) (sig : Sig)
    (hAdm : st.statefulEpochs = true → st.nextEpoch ≤ req.epoch)
    (hV : S.verify st.enrolledPk req.message sig = true) : (st.record req sig).Inv S := by
  have hC := hInv.consume req.epoch hAdm
  obtain ⟨hLogC, hStC⟩ := hC
  refine ⟨fun e he => ?_, fun hS => ?_⟩
  · rcases List.mem_cons.mp he with hEq | hOld
    · rw [hEq]
      exact ⟨hV, List.Mem.head _⟩
    · exact hLogC e hOld
  · obtain ⟨hPw, hLt, hLogPw⟩ := hStC hS
    refine ⟨hPw, hLt, .cons (fun b hb => ?_) hLogPw⟩
    obtain ⟨_, hLtOld, _⟩ := hInv.2 hS
    exact Nat.lt_of_lt_of_le (hLtOld b.1 (hInv.1 b hb).2) (hAdm hS)

private theorem admissible_next_le {stateful : Bool} {nextEpoch epoch : Nat}
    (h : epochAdmissible stateful maxWindow nextEpoch epoch = true) (hS : stateful = true) :
    nextEpoch ≤ epoch := by
  subst hS
  exact (epochAdmissible_stateful h).1

theorem idealSignMachine_step_preserves_inv
    {st st' : IdealSignState PK Sig} {req : SignRequest} {sig : Sig}
    (hInv : st.Inv S)
    (hStep : (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).step st req =
      some (st', sig)) :
    st'.Inv S := by
  obtain ⟨hA, _, hV, hEq⟩ := idealSignMachine_step_some hStep
  rw [hEq]
  exact hInv.record req sig (admissible_next_le hA) hV

theorem idealSignMachine_errStep_preserves_inv
    {st : IdealSignState PK Sig} (req : SignRequest) (hInv : st.Inv S) :
    ((idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).errStep st req).Inv S := by
  cases hA : epochAdmissible st.statefulEpochs maxWindow st.nextEpoch req.epoch with
  | false =>
    rw [idealSignMachine_errStep_of_inadmissible hA]
    exact hInv
  | true =>
    rw [idealSignMachine_errStep_of_admissible hA]
    exact hInv.consume req.epoch (admissible_next_le hA)

theorem idealSignMachine_trace_preserves_inv :
    ∀ {s₀ s_final : IdealSignState PK Sig} {tr : List (SignRequest × Sig)},
      s₀.Inv S →
      (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace s₀ tr s_final →
      s_final.Inv S
  | _, _, _, hInv, .nil _ => hInv
  | _, _, _, hInv, .accept hStep hRest =>
    idealSignMachine_trace_preserves_inv
      (idealSignMachine_step_preserves_inv hInv hStep) hRest
  | _, _, _, hInv, .reject inp _ hRest =>
    idealSignMachine_trace_preserves_inv
      (idealSignMachine_errStep_preserves_inv inp hInv) hRest

/-- Every reachable state satisfies the invariant. -/
theorem idealSignMachine_reachable_inv
    (S : SigScheme PK SK Sig) (pk₀ : PK) (stateful₀ : Bool) (maxWindow : Nat)
    (oracleSign : SignRequest → Option Sig)
    {st : IdealSignState PK Sig}
    (hReach : (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).Reachable st) :
    st.Inv S := by
  rcases hReach with ⟨s₀, tr, hInit, hTrace⟩
  have hInit' : s₀ = IdealSignState.empty pk₀ stateful₀ := hInit
  rw [hInit'] at hTrace
  exact idealSignMachine_trace_preserves_inv (IdealSignState.empty_inv S pk₀ stateful₀) hTrace

/-- In stateful mode two log entries with the same epoch are the same entry: no epoch signs
    two messages. -/
theorem IdealSignState.Inv.signedLog_oneTime {st : IdealSignState PK Sig} (hInv : st.Inv S)
    (hS : st.statefulEpochs = true) :
    ∀ a ∈ st.signedLog, ∀ b ∈ st.signedLog, a.1 = b.1 → a = b := by
  have hPw := (hInv.2 hS).2.2
  generalize st.signedLog = l at hPw
  induction l with
  | nil => exact fun _ h => nomatch h
  | cons x l ih =>
    obtain ⟨hHead, hTail⟩ := List.pairwise_cons.mp hPw
    intro a ha b hb hEq
    rcases List.mem_cons.mp ha with h1 | h1
    · rcases List.mem_cons.mp hb with h2 | h2
      · rw [h1, h2]
      · rw [h1] at hEq
        exact absurd hEq.symm (Nat.ne_of_lt (hHead b h2))
    · rcases List.mem_cons.mp hb with h2 | h2
      · rw [h2] at hEq
        exact absurd hEq (Nat.ne_of_lt (hHead a h1))
      · exact ih hTail a h1 b h2 hEq

/-- The enrolled key and the mode never change along a trace. -/
theorem idealSignMachine_trace_key_mode :
    ∀ {s₀ s_final : IdealSignState PK Sig} {tr : List (SignRequest × Sig)},
      (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace s₀ tr s_final →
      s_final.enrolledPk = s₀.enrolledPk ∧ s_final.statefulEpochs = s₀.statefulEpochs
  | _, _, _, .nil _ => ⟨rfl, rfl⟩
  | _, _, _, .accept hStep hRest => by
    have hEq := (idealSignMachine_step_some hStep).2.2.2
    have ih := idealSignMachine_trace_key_mode hRest
    rw [hEq] at ih
    exact ih
  | s₀, _, _, .reject inp _ hRest => by
    have ih := idealSignMachine_trace_key_mode hRest
    cases hA : epochAdmissible s₀.statefulEpochs maxWindow s₀.nextEpoch inp.epoch with
    | false =>
      rw [idealSignMachine_errStep_of_inadmissible hA] at ih
      exact ih
    | true =>
      rw [idealSignMachine_errStep_of_admissible hA] at ih
      exact ih

/-- **Every output of a trace verifies under the key of its starting state.** -/
theorem idealSignMachine_trace_outputs_verified :
    ∀ {s₀ s_final : IdealSignState PK Sig} {tr : List (SignRequest × Sig)},
      (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace s₀ tr s_final →
      ∀ p ∈ tr, S.verify s₀.enrolledPk p.1.message p.2 = true
  | _, _, _, .nil _ => fun _ h => (nomatch h)
  | s₀, _, _, .accept hStep hRest => fun p hp => by
    obtain ⟨_, _, hV, hEq⟩ := idealSignMachine_step_some hStep
    rcases List.mem_cons.mp hp with hHead | hTail
    · rw [hHead]
      exact hV
    · have ih := idealSignMachine_trace_outputs_verified hRest p hTail
      rw [hEq] at ih
      exact ih
  | s₀, _, _, .reject inp _ hRest => fun p hp => by
    have ih := idealSignMachine_trace_outputs_verified hRest p hp
    cases hA : epochAdmissible s₀.statefulEpochs maxWindow s₀.nextEpoch inp.epoch with
    | false =>
      rw [idealSignMachine_errStep_of_inadmissible hA] at ih
      exact ih
    | true =>
      rw [idealSignMachine_errStep_of_admissible hA] at ih
      exact ih

/-- A rejection keeps the enrolled key and the mode, and never lowers `nextEpoch`. -/
theorem idealSignMachine_errStep_facts (st : IdealSignState PK Sig) (req : SignRequest) :
    ((idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).errStep st req).enrolledPk =
      st.enrolledPk ∧
    ((idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).errStep st req).statefulEpochs =
      st.statefulEpochs ∧
    (st.statefulEpochs = true → st.nextEpoch ≤
      ((idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).errStep st req).nextEpoch) := by
  cases hA : epochAdmissible st.statefulEpochs maxWindow st.nextEpoch req.epoch with
  | false =>
    rw [idealSignMachine_errStep_of_inadmissible hA]
    exact ⟨rfl, rfl, fun _ => Nat.le_refl _⟩
  | true =>
    rw [idealSignMachine_errStep_of_admissible hA]
    exact ⟨rfl, rfl, fun hS => Nat.le_trans (admissible_next_le hA hS) (Nat.le_succ _)⟩

/-- **Strictly monotone epochs.** Along a trace of a stateful machine the accepted requests
    have epochs at or above the starting `nextEpoch` and strictly increasing in order. -/
theorem idealSignMachine_trace_epochs_increasing :
    ∀ {s₀ s_final : IdealSignState PK Sig} {tr : List (SignRequest × Sig)},
      s₀.statefulEpochs = true →
      (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace s₀ tr s_final →
      (∀ p ∈ tr, s₀.nextEpoch ≤ p.1.epoch) ∧ tr.Pairwise (fun a b => a.1.epoch < b.1.epoch)
  | _, _, _, _, .nil _ => ⟨fun _ h => (nomatch h), .nil⟩
  | s₀, _, _, hS, .accept (s' := s') (inp := inp) hStep hRest => by
    obtain ⟨hA, _, _, hEq⟩ := idealSignMachine_step_some hStep
    have hNext := admissible_next_le hA hS
    have hS' : s'.statefulEpochs = true := by
      rw [hEq]
      exact hS
    have hN' : s'.nextEpoch = inp.epoch + 1 := by
      rw [hEq]
      rfl
    obtain ⟨ihLo, ihPw⟩ := idealSignMachine_trace_epochs_increasing hS' hRest
    rw [hN'] at ihLo
    refine ⟨fun p hp => ?_, .cons (fun p hp => ihLo p hp) ihPw⟩
    rcases List.mem_cons.mp hp with hHead | hTail
    · rw [hHead]
      exact hNext
    · exact Nat.le_trans (Nat.le_trans hNext (Nat.le_succ _)) (ihLo p hTail)
  | s₀, _, _, hS, .reject inp _ hRest => by
    obtain ⟨_, hSt, hGe⟩ := idealSignMachine_errStep_facts (S := S) (pk₀ := pk₀)
      (stateful₀ := stateful₀) (maxWindow := maxWindow) (oracleSign := oracleSign) s₀ inp
    obtain ⟨ihLo, ihPw⟩ := idealSignMachine_trace_epochs_increasing (hSt.trans hS) hRest
    exact ⟨fun p hp => Nat.le_trans (hGe hS) (ihLo p hp), ihPw⟩

/-- Every initialized trace of a stateful machine has verified outputs under `pk₀` and strictly
    increasing epochs. -/
theorem idealSignMachine_admitted_trace_safe
    (S : SigScheme PK SK Sig) (pk₀ : PK) (maxWindow : Nat)
    (oracleSign : SignRequest → Option Sig) {tr : List (SignRequest × Sig)}
    (hAdmits : (idealSignMachine S pk₀ true maxWindow oracleSign).AdmitsTrace tr) :
    (∀ p ∈ tr, S.verify pk₀ p.1.message p.2 = true) ∧
    tr.Pairwise (fun a b => a.1.epoch < b.1.epoch) := by
  rcases hAdmits with ⟨s₀, s_final, hInit, hTrace⟩
  have hInit' : s₀ = IdealSignState.empty pk₀ true := hInit
  rw [hInit'] at hTrace
  exact ⟨idealSignMachine_trace_outputs_verified hTrace,
    (idealSignMachine_trace_epochs_increasing rfl hTrace).2⟩

end Machine

/-! ## The latched signer refines the ideal machine -/

/-- State of the latched signer: the least epoch still admissible. -/
structure LatchedSignerState where
  nextEpoch : Nat
  deriving DecidableEq, Repr

/-- The signer that runs `S.sign sk` behind the epoch latch. An admissible request moves the
    latch to `epoch + 1` whether or not `S.sign` returns a signature. -/
@[expose] def latchedSignerMachine {PK SK Sig : Type} (S : SigScheme PK SK Sig) (sk : SK)
    (stateful₀ : Bool) (maxWindow : Nat) : Machine LatchedSignerState SignRequest Sig where
  Init c := c = ⟨0⟩
  step c req :=
    if epochAdmissible stateful₀ maxWindow c.nextEpoch req.epoch = true then
      (S.sign sk req.epoch req.message).map (fun sig => (⟨req.epoch + 1⟩, sig))
    else none
  errStep c req :=
    if epochAdmissible stateful₀ maxWindow c.nextEpoch req.epoch = true then ⟨req.epoch + 1⟩
    else c

/-- **The latched signer refines the ideal signing machine** for its own public key, with the
    signer's algorithm as the candidate oracle: equal accept/reject behaviour, equal outputs,
    and the same epoch consumption on failure. -/
def latchedSigner_refines_ideal {PK SK Sig : Type} (S : SigScheme PK SK Sig) (sk : SK)
    (stateful₀ : Bool) (maxWindow : Nat) :
    latchedSignerMachine S sk stateful₀ maxWindow ⊑
      idealSignMachine S (S.derivePk sk) stateful₀ maxWindow
        (fun req => S.sign sk req.epoch req.message) where
  Rel c a := a.nextEpoch = c.nextEpoch ∧ a.statefulEpochs = stateful₀ ∧
    a.enrolledPk = S.derivePk sk
  absInit _ := IdealSignState.empty (S.derivePk sk) stateful₀
  init_ok {c₀} hInit := by
    have hC : c₀ = ⟨0⟩ := hInit
    rw [hC]
    exact ⟨rfl, rfl, rfl, rfl⟩
  sim_ok {c c' a req sig} hRel hStepC := by
    obtain ⟨hN, hS, hPk⟩ := hRel
    have hStepC' : (if epochAdmissible stateful₀ maxWindow c.nextEpoch req.epoch = true then
        (S.sign sk req.epoch req.message).map
          (fun sig => ((⟨req.epoch + 1⟩ : LatchedSignerState), sig))
        else none) = some (c', sig) := hStepC
    obtain ⟨hA, hMap⟩ := signIteSome hStepC'
    obtain ⟨s, hSign, hPair⟩ := signMapSome hMap
    have hs : s = sig := congrArg Prod.snd hPair
    have hc : (⟨req.epoch + 1⟩ : LatchedSignerState) = c' := congrArg Prod.fst hPair
    rw [hs] at hSign
    have hA' : epochAdmissible a.statefulEpochs maxWindow a.nextEpoch req.epoch = true := by
      rw [hS, hN]
      exact hA
    have hV : S.verify a.enrolledPk req.message sig = true := by
      rw [hPk]
      exact S.correct sk req.epoch req.message sig hSign
    rw [idealSignMachine_step_of_valid hA' hSign hV]
    exact ⟨rfl, hc ▸ rfl, hS, hPk⟩
  sim_err {c a req} hRel hNoneC := by
    obtain ⟨hN, hS, hPk⟩ := hRel
    have hNoneC' : (if epochAdmissible stateful₀ maxWindow c.nextEpoch req.epoch = true then
        (S.sign sk req.epoch req.message).map
          (fun sig => ((⟨req.epoch + 1⟩ : LatchedSignerState), sig))
        else none) = none := hNoneC
    cases hA : epochAdmissible stateful₀ maxWindow c.nextEpoch req.epoch with
    | false =>
      have hA' : epochAdmissible a.statefulEpochs maxWindow a.nextEpoch req.epoch = false := by
        rw [hS, hN]
        exact hA
      have hErrC : (latchedSignerMachine S sk stateful₀ maxWindow).errStep c req = c := by
        show (if epochAdmissible stateful₀ maxWindow c.nextEpoch req.epoch = true then
          (⟨req.epoch + 1⟩ : LatchedSignerState) else c) = c
        rw [hA]
        rfl
      rw [hErrC, idealSignMachine_errStep_of_inadmissible hA']
      exact ⟨idealSignMachine_step_of_inadmissible hA', hN, hS, hPk⟩
    | true =>
      have hA' : epochAdmissible a.statefulEpochs maxWindow a.nextEpoch req.epoch = true := by
        rw [hS, hN]
        exact hA
      rw [hA] at hNoneC'
      have hSign : S.sign sk req.epoch req.message = none := by
        cases hSg : S.sign sk req.epoch req.message with
        | none => rfl
        | some s =>
          rw [hSg] at hNoneC'
          cases hNoneC'
      have hErrC : (latchedSignerMachine S sk stateful₀ maxWindow).errStep c req =
          ⟨req.epoch + 1⟩ := by
        show (if epochAdmissible stateful₀ maxWindow c.nextEpoch req.epoch = true then
          (⟨req.epoch + 1⟩ : LatchedSignerState) else c) = ⟨req.epoch + 1⟩
        rw [hA]
        rfl
      rw [hErrC, idealSignMachine_errStep_of_admissible hA']
      exact ⟨idealSignMachine_step_of_no_candidate hSign, rfl, hS, hPk⟩

/-- Every initialized trace of a stateful latched signer consists of signatures that verify
    under the signer's public key, at strictly increasing epochs. -/
theorem latchedSigner_trace_safe {PK SK Sig : Type} (S : SigScheme PK SK Sig) (sk : SK)
    (maxWindow : Nat) {tr : List (SignRequest × Sig)}
    (hAdmits : (latchedSignerMachine S sk true maxWindow).AdmitsTrace tr) :
    (∀ p ∈ tr, S.verify (S.derivePk sk) p.1.message p.2 = true) ∧
    tr.Pairwise (fun a b => a.1.epoch < b.1.epoch) :=
  idealSignMachine_admitted_trace_safe S (S.derivePk sk) maxWindow
    (fun req => S.sign sk req.epoch req.message)
    ((latchedSigner_refines_ideal S sk true maxWindow).preserve_admitsTrace hAdmits)

/-! ## Rejected behaviours -/

/-- Scheme over `Unit` whose signer always signs and whose verifier accepts everything. -/
def acceptAllSigScheme : SigScheme Unit Unit Unit where
  derivePk _ := ()
  sign _ _ _ := some ()
  verify _ _ _ := true
  correct _ _ _ _ _ := rfl

/-- Scheme over `Unit` whose signer never signs and whose verifier rejects everything. -/
def rejectAllSigScheme : SigScheme Unit Unit Unit where
  derivePk _ := ()
  sign _ _ _ := none
  verify _ _ _ := false
  correct _ _ _ _ h := nomatch h

/-- Epochs `2, 1`: after epoch `2` signs, a request for epoch `1` is rejected. -/
theorem idealSign_rejects_epoch_one_after_two :
    ¬ (((idealSignMachine acceptAllSigScheme () true 8 (fun _ => some ())).step
      ((idealSignMachine acceptAllSigScheme () true 8 (fun _ => some ())).runStep
        (IdealSignState.empty () true) ⟨2, []⟩).1 ⟨1, []⟩).isSome = true) := by
  decide

/-- A candidate oracle unrelated to the scheme does not sign: against a verifier that rejects
    everything, the oracle's candidate is never emitted. -/
theorem idealSign_rejects_unverified_candidate :
    ¬ (((idealSignMachine rejectAllSigScheme () false 0 (fun _ => some ())).step
      (IdealSignState.empty () false) ⟨0, []⟩).isSome = true) := by
  decide

/-- A failed signing burns its epoch: after the oracle fails at epoch `3`, another request for
    epoch `3` is rejected although the oracle has a candidate for it. -/
theorem idealSign_failed_epoch_not_reusable :
    ¬ (((idealSignMachine acceptAllSigScheme () true 8
        (fun req => if req.message = [] then none else some ())).step
      ((idealSignMachine acceptAllSigScheme () true 8
        (fun req => if req.message = [] then none else some ())).runStep
        (IdealSignState.empty () true) ⟨3, []⟩).1 ⟨3, [1]⟩).isSome = true) := by
  decide

/-- An epoch beyond the jump window is rejected. -/
theorem idealSign_rejects_epoch_beyond_window :
    ¬ (((idealSignMachine acceptAllSigScheme () true 8 (fun _ => some ())).step
      (IdealSignState.empty () true) ⟨9, []⟩).isSome = true) := by
  decide

#tooth_pair idealSignMachine_trace_epochs_increasing vs idealSign_rejects_epoch_one_after_two
#tooth_pair idealSignMachine_step_emits_verified vs idealSign_rejects_unverified_candidate
#tooth_pair idealSignMachine_failed_sign_burns_epoch vs idealSign_failed_epoch_not_reusable
#tooth_pair idealSignMachine_step_some vs idealSign_rejects_epoch_beyond_window

/-- Existential unforgeability under chosen-message attack (`EUF-CMA`) forgery predicate:
    `verify pk msgStar sigStar = true` on a fresh message `msgStar` absent from `signedLog`. -/
def EufCmaForgery {PK SK Sig : Type}
    (S : SigScheme PK SK Sig) (st : IdealSignState PK Sig)
    (msgStar : Bytes) (sigStar : Sig) : Prop :=
  (∀ entry ∈ st.signedLog, entry.2.1 ≠ msgStar) ∧
  S.verify st.enrolledPk msgStar sigStar = true

/-- Strong unforgeability (`SUF-CMA`) forgery predicate: `(msgStar, sigStar)` is fresh as a pair. -/
def SufCmaForgery {PK SK Sig : Type} [DecidableEq Sig]
    (S : SigScheme PK SK Sig) (st : IdealSignState PK Sig)
    (msgStar : Bytes) (sigStar : Sig) : Prop :=
  (∀ entry ∈ st.signedLog, (entry.2.1, entry.2.2) ≠ (msgStar, sigStar)) ∧
  S.verify st.enrolledPk msgStar sigStar = true

theorem EufCmaForgery.toSufCma {PK SK Sig : Type} [DecidableEq Sig]
    {S : SigScheme PK SK Sig} {st : IdealSignState PK Sig} {msgStar : Bytes} {sigStar : Sig}
    (h : EufCmaForgery S st msgStar sigStar) :
    SufCmaForgery S st msgStar sigStar := by
  refine ⟨fun entry hMem hEq => ?_, h.2⟩
  injection hEq with hMsg _
  exact h.1 entry hMem hMsg

#verify_constructive
  Qsag.Spec.epochAdmissible_stateful
  Qsag.Spec.epochAdmissible_consumed
  Qsag.Spec.verifiedCandidate_some
  Qsag.Spec.verifiedCandidate_of_valid
  Qsag.Spec.idealSignMachine_step_some
  Qsag.Spec.idealSignMachine_step_emits_verified
  Qsag.Spec.idealSignMachine_step_of_valid
  Qsag.Spec.idealSignMachine_rejects_consumed_epoch
  Qsag.Spec.idealSignMachine_failed_sign_burns_epoch
  Qsag.Spec.IdealSignState.empty_inv
  Qsag.Spec.IdealSignState.Inv.consume
  Qsag.Spec.IdealSignState.Inv.record
  Qsag.Spec.idealSignMachine_step_preserves_inv
  Qsag.Spec.idealSignMachine_errStep_preserves_inv
  Qsag.Spec.idealSignMachine_trace_preserves_inv
  Qsag.Spec.idealSignMachine_reachable_inv
  Qsag.Spec.IdealSignState.Inv.signedLog_oneTime
  Qsag.Spec.idealSignMachine_trace_key_mode
  Qsag.Spec.idealSignMachine_trace_outputs_verified
  Qsag.Spec.idealSignMachine_errStep_facts
  Qsag.Spec.idealSignMachine_trace_epochs_increasing
  Qsag.Spec.idealSignMachine_admitted_trace_safe
  Qsag.Spec.latchedSigner_trace_safe
  Qsag.Spec.idealSign_rejects_epoch_one_after_two
  Qsag.Spec.idealSign_rejects_unverified_candidate
  Qsag.Spec.idealSign_failed_epoch_not_reusable
  Qsag.Spec.idealSign_rejects_epoch_beyond_window
  Qsag.Spec.EufCmaForgery.toSufCma

end Qsag.Spec
end

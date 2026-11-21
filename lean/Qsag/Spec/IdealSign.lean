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
6. Forgery events against the signed log (`EufCmaForgery`, `SufCmaForgery`) and their
   characterisation over traces: the log of a run is exactly its outputs, so a forgery against
   the final state is a verifying pair the interface never emitted
   (`idealSignMachine_eufCmaForgery_iff`, `idealSignMachine_sufCmaForgery_iff`), and no emitted
   signature is one (`idealSignMachine_trace_outputs_not_forgeries`). The machine does not
   claim that forgeries are improbable: that is a property of `S`. For the production scheme
   `Protocol.Signing.ExecEufCmaClosedGame` bounds the forgery probability by the probabilities
   of three extractor events on the same run; those event probabilities are not bounded by
   anything proved in this library.
7. Corruption. `idealSignMachine` has one signer and no corruption or key-exposure input.
   `idealSignCorruptibleMachine` is the functionality with adaptive key exposure: the same
   state plus a `corrupted` flag and an injected log, with inputs `.sign` (the transition of
   `idealSignMachine` on the inner state, in every state), `.corrupt` (always accepted, sets
   the flag, which nothing clears) and `.inject req sig` (accepted exactly when the flag is
   set and `S.verify enrolledPk req.message sig` holds; the epoch latch is not consulted).
   - `idealSignMachine` is its corruption-free fragment: a run that ends uncorrupted accepted
     only `.sign` events and is, event for event, a run of `idealSignMachine`
     (`idealSignCorruptibleMachine_uncorrupted_trace_is_ideal`), every run of
     `idealSignMachine` is such a run (`idealSignMachine_trace_lifts_corruptible`), and the
     two machines admit the same honest traces (`idealSignCorruptibleMachine_admits_honest_iff`).
   - In every run the inner state follows `idealSignMachine` on the `.sign` events
     (`idealSignCorruptibleMachine_trace_inner`), the flag is monotone
     (`idealSignCorruptibleMachine_trace_corrupted_mono`), the key and mode are fixed, and
     every emitted signature, signed or injected, verifies under the enrolled key
     (`idealSignCorruptibleMachine_trace_emitted_verified`).
   - A run that ends uncorrupted has the guarantees of item 4 and a signed log equal to its
     outputs (`idealSignCorruptibleMachine_uncorrupted_trace_safe`). A corrupted run does
     not: an injected signature may reuse a consumed epoch
     (`idealSignCorruptible_corrupted_run_reuses_epoch`).
   - Forgery is measured against both logs (`CorruptibleEufCmaForgery`,
     `CorruptibleSufCmaForgery`): a forgery is a verifying pair never emitted, signed or
     injected (`idealSignCorruptibleMachine_eufCmaForgery_iff`). After corruption every
     verifying pair can be emitted by one `.inject`
     (`idealSignCorruptibleMachine_corrupted_absorbs_forgery`), so the functionality promises
     nothing about unforgeability from that point on.
   Neither ideal state has a secret-key component and no output carries key material. In the
   refinement the secret key is a parameter of `latchedSignerMachine`, and every value that
   machine returns is the output of `S.sign sk` on the admitted request
   (`latchedSigner_output_is_sign`); what `S.sign` itself reveals about `sk` is a property of
   the scheme. Gap: only the corruption-free fragment is refined by a real machine
   (`latchedSigner_refines_ideal`). No machine with a key-reveal output is shown to refine the
   behaviour after `.corrupt`; `Refines` demands equal outputs on equal inputs and cannot
   express a simulator that turns a revealed key into `.inject` inputs.
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

/-! ## Forgery events and the signed log -/

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

section Forgery
variable {PK SK Sig : Type} {S : SigScheme PK SK Sig} {pk₀ : PK} {stateful₀ : Bool}
  {maxWindow : Nat} {oracleSign : SignRequest → Option Sig}

private theorem idealSign_errStep_signedLog (st : IdealSignState PK Sig) (req : SignRequest) :
    ((idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).errStep st req).signedLog =
      st.signedLog := by
  cases hA : epochAdmissible st.statefulEpochs maxWindow st.nextEpoch req.epoch with
  | false => rw [idealSignMachine_errStep_of_inadmissible hA]
  | true => rw [idealSignMachine_errStep_of_admissible hA]; rfl

/-- Every output of a trace, and every entry already logged, is in the final signed log. -/
theorem idealSignMachine_trace_log_complete :
    ∀ {s₀ s_final : IdealSignState PK Sig} {tr : List (SignRequest × Sig)},
      (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace s₀ tr s_final →
      (∀ e ∈ s₀.signedLog, e ∈ s_final.signedLog) ∧
      ∀ p ∈ tr, (p.1.epoch, p.1.message, p.2) ∈ s_final.signedLog
  | _, _, _, .nil _ => ⟨fun _ h => h, fun _ h => (nomatch h)⟩
  | s₀, _, _, .accept hStep hRest => by
    obtain ⟨_, _, _, hEq⟩ := idealSignMachine_step_some hStep
    obtain ⟨ihOld, ihTr⟩ := idealSignMachine_trace_log_complete hRest
    rw [hEq] at ihOld
    refine ⟨fun e he => ihOld e (List.mem_cons_of_mem _ he), fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with hHead | hTail
    · rw [hHead]
      exact ihOld _ (List.mem_cons.mpr (.inl rfl))
    · exact ihTr p hTail
  | s₀, _, _, .reject inp _ hRest => by
    obtain ⟨ihOld, ihTr⟩ := idealSignMachine_trace_log_complete hRest
    rw [idealSign_errStep_signedLog] at ihOld
    exact ⟨ihOld, ihTr⟩

/-- Every entry of the final signed log was already logged or is an output of the trace. -/
theorem idealSignMachine_trace_log_sound :
    ∀ {s₀ s_final : IdealSignState PK Sig} {tr : List (SignRequest × Sig)},
      (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace s₀ tr s_final →
      ∀ e ∈ s_final.signedLog,
        e ∈ s₀.signedLog ∨ ∃ p ∈ tr, e = (p.1.epoch, p.1.message, p.2)
  | _, _, _, .nil _ => fun _ h => .inl h
  | s₀, _, _, .accept hStep hRest => fun e he => by
    obtain ⟨_, _, _, hEq⟩ := idealSignMachine_step_some hStep
    have ih := idealSignMachine_trace_log_sound hRest e he
    rw [hEq] at ih
    rcases ih with hOld | ⟨p, hp, hpe⟩
    · rcases List.mem_cons.mp hOld with hHead | hTail
      · exact .inr ⟨_, List.mem_cons.mpr (.inl rfl), hHead⟩
      · exact .inl hTail
    · exact .inr ⟨p, List.mem_cons_of_mem _ hp, hpe⟩
  | s₀, _, _, .reject inp _ hRest => fun e he => by
    have ih := idealSignMachine_trace_log_sound hRest e he
    rw [idealSign_errStep_signedLog] at ih
    exact ih

/-- **`EUF-CMA` forgery against a run.** After a trace from the initial state, a pair is an
    `EufCmaForgery` against the final state exactly when it verifies under the enrolled key and
    its message was never the message of an emitted signature. -/
theorem idealSignMachine_eufCmaForgery_iff
    {s_final : IdealSignState PK Sig} {tr : List (SignRequest × Sig)}
    (hTrace : (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace
      (IdealSignState.empty pk₀ stateful₀) tr s_final) (msg : Bytes) (sig : Sig) :
    EufCmaForgery S s_final msg sig ↔
      (S.verify pk₀ msg sig = true ∧ ∀ p ∈ tr, p.1.message ≠ msg) := by
  have hPk : s_final.enrolledPk = pk₀ := (idealSignMachine_trace_key_mode hTrace).1
  unfold EufCmaForgery
  rw [hPk]
  constructor
  · rintro ⟨hFresh, hV⟩
    exact ⟨hV, fun p hp =>
      hFresh _ ((idealSignMachine_trace_log_complete hTrace).2 p hp)⟩
  · rintro ⟨hV, hFresh⟩
    refine ⟨fun e he => ?_, hV⟩
    rcases idealSignMachine_trace_log_sound hTrace e he with hOld | ⟨p, hp, hpe⟩
    · exact nomatch hOld
    · rw [hpe]
      exact hFresh p hp

/-- **`SUF-CMA` forgery against a run.** A pair is a `SufCmaForgery` against the final state
    exactly when it verifies under the enrolled key and was never emitted. -/
theorem idealSignMachine_sufCmaForgery_iff [DecidableEq Sig]
    {s_final : IdealSignState PK Sig} {tr : List (SignRequest × Sig)}
    (hTrace : (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace
      (IdealSignState.empty pk₀ stateful₀) tr s_final) (msg : Bytes) (sig : Sig) :
    SufCmaForgery S s_final msg sig ↔
      (S.verify pk₀ msg sig = true ∧ ∀ p ∈ tr, (p.1.message, p.2) ≠ (msg, sig)) := by
  have hPk : s_final.enrolledPk = pk₀ := (idealSignMachine_trace_key_mode hTrace).1
  unfold SufCmaForgery
  rw [hPk]
  constructor
  · rintro ⟨hFresh, hV⟩
    exact ⟨hV, fun p hp =>
      hFresh _ ((idealSignMachine_trace_log_complete hTrace).2 p hp)⟩
  · rintro ⟨hV, hFresh⟩
    refine ⟨fun e he => ?_, hV⟩
    rcases idealSignMachine_trace_log_sound hTrace e he with hOld | ⟨p, hp, hpe⟩
    · exact nomatch hOld
    · rw [hpe]
      exact hFresh p hp

/-- **No emitted signature is a forgery**, in either sense, against the state the run ends in. -/
theorem idealSignMachine_trace_outputs_not_forgeries [DecidableEq Sig]
    {s_final : IdealSignState PK Sig} {tr : List (SignRequest × Sig)}
    (hTrace : (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace
      (IdealSignState.empty pk₀ stateful₀) tr s_final) :
    ∀ p ∈ tr, ¬ EufCmaForgery S s_final p.1.message p.2 ∧
      ¬ SufCmaForgery S s_final p.1.message p.2 := by
  intro p hp
  have hSuf : ¬ SufCmaForgery S s_final p.1.message p.2 := fun h =>
    ((idealSignMachine_sufCmaForgery_iff hTrace _ _).mp h).2 p hp rfl
  exact ⟨fun h => hSuf h.toSufCma, hSuf⟩

end Forgery

/-- **The latched signer returns only outputs of `S.sign sk`.** The secret key is a parameter of
    the machine, not part of its state, and reaches the interface only through `S.sign` on an
    admitted request. -/
theorem latchedSigner_output_is_sign {PK SK Sig : Type} (S : SigScheme PK SK Sig) (sk : SK)
    (stateful₀ : Bool) (maxWindow : Nat) {c c' : LatchedSignerState} {req : SignRequest}
    {sig : Sig}
    (h : (latchedSignerMachine S sk stateful₀ maxWindow).step c req = some (c', sig)) :
    S.sign sk req.epoch req.message = some sig := by
  have h' : (if epochAdmissible stateful₀ maxWindow c.nextEpoch req.epoch = true then
      (S.sign sk req.epoch req.message).map
        (fun sig => ((⟨req.epoch + 1⟩ : LatchedSignerState), sig))
      else none) = some (c', sig) := h
  obtain ⟨_, hMap⟩ := signIteSome h'
  obtain ⟨s, hS, hPair⟩ := signMapSome hMap
  have hs : s = sig := congrArg Prod.snd hPair
  exact hs ▸ hS

/-- A pair the signer never emitted and that verifies is a forgery: with the accept-all scheme,
    after one signature on `[]`, the message `[1]` with the same signature is an `EufCmaForgery`
    against the reached state. The ideal machine records what was signed; it does not make
    forgeries impossible. -/
theorem idealSign_unsigned_message_is_forgery :
    EufCmaForgery acceptAllSigScheme
      ((idealSignMachine acceptAllSigScheme () true 8 (fun _ => some ())).runStep
        (IdealSignState.empty () true) ⟨0, []⟩).1 [1] () := by
  refine ⟨?_, rfl⟩
  decide

/-! ## Adaptive corruption

`idealSignCorruptibleMachine` extends `idealSignMachine` with a corruption input and an
adversarial injection input. Its state is the ideal state, a `corrupted` flag and the log of
injected signatures. -/

/-- Inputs of the corruptible signing functionality: an honest signing request, the corruption
    of the signer, and a signature supplied by the adversary for a request of its choice. -/
inductive SignCommand (Sig : Type) where
  | sign (req : SignRequest)
  | corrupt
  | inject (req : SignRequest) (sig : Sig)

/-- Outputs of the corruptible signing functionality: an emitted signature (signed or
    injected), or the acknowledgement of a corruption. No output carries key material. -/
inductive SignReply (Sig : Type) where
  | signature (sig : Sig)
  | corrupted

/-- State of the corruptible functionality: the state of `idealSignMachine`, the corruption
    flag, and the injected `(epoch, message, signature)` triples, newest first, kept apart from
    `inner.signedLog`. -/
structure CorruptibleSignState (PK Sig : Type) where
  inner : IdealSignState PK Sig
  corrupted : Bool
  injectedLog : List (Nat × Bytes × Sig)

/-- Initial state: the empty ideal state, uncorrupted, nothing injected. -/
@[expose] def CorruptibleSignState.empty {PK Sig : Type} (pk : PK) (stateful : Bool) :
    CorruptibleSignState PK Sig :=
  { inner := IdealSignState.empty pk stateful, corrupted := false, injectedLog := [] }

/-- **Ideal signing functionality with adaptive key exposure.**

    `.sign req` runs `idealSignMachine` on `inner` in every state, corrupted or not: same
    acceptance, same output, same `errStep` (an admissible epoch whose signing failed is
    consumed). `.corrupt` is always accepted and sets `corrupted`; nothing clears the flag.
    `.inject req sig` is accepted exactly when `corrupted = true` and
    `S.verify inner.enrolledPk req.message sig = true`; it does not consult the epoch latch and
    does not move it, and it appends the triple to `injectedLog`. A rejected `.inject` leaves
    the state unchanged.

    This is the ideal view of a key exposure: after `.corrupt` the adversary may have the
    interface emit any signature the verifier accepts, at any epoch. The state has no secret
    key and no output carries key material. No machine with a key-reveal output is shown to
    refine the behaviour after `.corrupt`: `Refines` demands equal outputs on equal inputs and
    cannot express a simulator that turns a revealed key into `.inject` inputs. -/
@[expose] def idealSignCorruptibleMachine {PK SK Sig : Type} (S : SigScheme PK SK Sig)
    (pk₀ : PK) (stateful₀ : Bool) (maxWindow : Nat) (oracleSign : SignRequest → Option Sig) :
    Machine (CorruptibleSignState PK Sig) (SignCommand Sig) (SignReply Sig) where
  Init st := st = CorruptibleSignState.empty pk₀ stateful₀
  step st cmd :=
    match cmd with
    | .sign req =>
      ((idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).step st.inner req).map
        (fun p => ({ st with inner := p.1 }, SignReply.signature p.2))
    | .corrupt => some ({ st with corrupted := true }, SignReply.corrupted)
    | .inject req sig =>
      if (st.corrupted && S.verify st.inner.enrolledPk req.message sig) = true then
        some ({ st with injectedLog := (req.epoch, req.message, sig) :: st.injectedLog },
          SignReply.signature sig)
      else none
  errStep st cmd :=
    match cmd with
    | .sign req =>
      { st with
        inner := (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).errStep st.inner req }
    | .corrupt => st
    | .inject _ _ => st

/-- The event of the corruptible machine in which the honest interface emits `p.2` on `p.1`. -/
@[expose] def honestSignEvent {Sig : Type} (p : SignRequest × Sig) :
    SignCommand Sig × SignReply Sig :=
  (SignCommand.sign p.1, SignReply.signature p.2)

/-- The accepted `.sign` events of a trace, in order. -/
@[expose] def signedEvents {Sig : Type} :
    List (SignCommand Sig × SignReply Sig) → List (SignRequest × Sig)
  | [] => []
  | (.sign req, .signature sig) :: rest => (req, sig) :: signedEvents rest
  | (.sign _, .corrupted) :: rest => signedEvents rest
  | (.corrupt, _) :: rest => signedEvents rest
  | (.inject _ _, _) :: rest => signedEvents rest

/-- The accepted `.inject` events of a trace, in order. -/
def injectedEvents {Sig : Type} :
    List (SignCommand Sig × SignReply Sig) → List (SignRequest × Sig)
  | [] => []
  | (.inject req _, .signature sig) :: rest => (req, sig) :: injectedEvents rest
  | (.inject _ _, .corrupted) :: rest => injectedEvents rest
  | (.corrupt, _) :: rest => injectedEvents rest
  | (.sign _, _) :: rest => injectedEvents rest

/-- Every signature a trace emitted, signed or injected, with its request, in order. -/
@[expose] def emittedEvents {Sig : Type} :
    List (SignCommand Sig × SignReply Sig) → List (SignRequest × Sig)
  | [] => []
  | (.sign req, .signature sig) :: rest => (req, sig) :: emittedEvents rest
  | (.inject req _, .signature sig) :: rest => (req, sig) :: emittedEvents rest
  | (.sign _, .corrupted) :: rest => emittedEvents rest
  | (.inject _ _, .corrupted) :: rest => emittedEvents rest
  | (.corrupt, _) :: rest => emittedEvents rest

theorem signedEvents_map_honest {Sig : Type} (l : List (SignRequest × Sig)) :
    signedEvents (l.map honestSignEvent) = l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    show p :: signedEvents (l.map honestSignEvent) = p :: l
    rw [ih]

theorem emittedEvents_map_honest {Sig : Type} (l : List (SignRequest × Sig)) :
    emittedEvents (l.map honestSignEvent) = l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    show p :: emittedEvents (l.map honestSignEvent) = p :: l
    rw [ih]

theorem injectedEvents_map_honest {Sig : Type} (l : List (SignRequest × Sig)) :
    injectedEvents (l.map honestSignEvent) = [] := by
  induction l with
  | nil => rfl
  | cons p l ih => exact ih

/-- An accepted `.inject` at the head of a trace is the first injected event. -/
theorem injectedEvents_cons_inject {Sig : Type} (req : SignRequest) (sig sig' : Sig)
    (rest : List (SignCommand Sig × SignReply Sig)) :
    injectedEvents ((SignCommand.inject req sig', SignReply.signature sig) :: rest) =
      (req, sig) :: injectedEvents rest := by
  rfl

/-- The emitted signatures of a trace are its signed ones and its injected ones. -/
theorem mem_emittedEvents {Sig : Type} {p : SignRequest × Sig} :
    ∀ {tr : List (SignCommand Sig × SignReply Sig)},
      p ∈ emittedEvents tr ↔ (p ∈ signedEvents tr ∨ p ∈ injectedEvents tr)
  | [] => ⟨fun h => .inl h, fun h => h.elim id id⟩
  | (.sign req, .signature sig) :: rest => by
    have ih := mem_emittedEvents (p := p) (tr := rest)
    show p ∈ (req, sig) :: emittedEvents rest ↔
      (p ∈ (req, sig) :: signedEvents rest ∨ p ∈ injectedEvents rest)
    constructor
    · intro h
      rcases List.mem_cons.mp h with hH | hT
      · exact .inl (List.mem_cons.mpr (.inl hH))
      · rcases ih.mp hT with h1 | h1
        · exact .inl (List.mem_cons_of_mem _ h1)
        · exact .inr h1
    · intro h
      rcases h with h1 | h1
      · rcases List.mem_cons.mp h1 with hH | hT
        · exact List.mem_cons.mpr (.inl hH)
        · exact List.mem_cons_of_mem _ (ih.mpr (.inl hT))
      · exact List.mem_cons_of_mem _ (ih.mpr (.inr h1))
  | (.inject req _, .signature sig) :: rest => by
    have ih := mem_emittedEvents (p := p) (tr := rest)
    show p ∈ (req, sig) :: emittedEvents rest ↔
      (p ∈ signedEvents rest ∨ p ∈ (req, sig) :: injectedEvents rest)
    constructor
    · intro h
      rcases List.mem_cons.mp h with hH | hT
      · exact .inr (List.mem_cons.mpr (.inl hH))
      · rcases ih.mp hT with h1 | h1
        · exact .inl h1
        · exact .inr (List.mem_cons_of_mem _ h1)
    · intro h
      rcases h with h1 | h1
      · exact List.mem_cons_of_mem _ (ih.mpr (.inl h1))
      · rcases List.mem_cons.mp h1 with hH | hT
        · exact List.mem_cons.mpr (.inl hH)
        · exact List.mem_cons_of_mem _ (ih.mpr (.inr hT))
  | (.sign _, .corrupted) :: rest => mem_emittedEvents (p := p) (tr := rest)
  | (.inject _ _, .corrupted) :: rest => mem_emittedEvents (p := p) (tr := rest)
  | (.corrupt, _) :: rest => mem_emittedEvents (p := p) (tr := rest)

private theorem validTrace_snoc {St In Out : Type} {M : Machine St In Out} :
    ∀ {s s' s'' : St} {tr : List (In × Out)} {inp : In} {out : Out},
      M.ValidTrace s tr s' → M.step s' inp = some (s'', out) →
      M.ValidTrace s (tr ++ [(inp, out)]) s''
  | _, _, _, _, _, _, .nil _, hStep => .accept hStep (.nil _)
  | _, _, _, _, _, _, .accept h hRest, hStep => .accept h (validTrace_snoc hRest hStep)
  | _, _, _, _, _, _, .reject i h hRest, hStep => .reject i h (validTrace_snoc hRest hStep)

section Corruptible
variable {PK SK Sig : Type} {S : SigScheme PK SK Sig} {pk₀ : PK} {stateful₀ : Bool}
  {maxWindow : Nat} {oracleSign : SignRequest → Option Sig}

/-! ### One step -/

/-- An accepted `.sign` is an accepted request of `idealSignMachine` on the inner state, with
    the same output; the flag and the injected log are untouched. -/
theorem idealSignCorruptibleMachine_sign_step_some {st st' : CorruptibleSignState PK Sig}
    {req : SignRequest} {out : SignReply Sig}
    (h : (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).step st
      (.sign req) = some (st', out)) :
    ∃ (inner' : IdealSignState PK Sig) (sig : Sig),
      (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).step st.inner req =
        some (inner', sig) ∧
      st' = { st with inner := inner' } ∧ out = SignReply.signature sig := by
  have h' : ((idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).step st.inner req).map
      (fun p => (({ st with inner := p.1 } : CorruptibleSignState PK Sig),
        SignReply.signature p.2)) = some (st', out) := h
  obtain ⟨p, hP, hPair⟩ := signMapSome h'
  exact ⟨p.1, p.2, hP, (congrArg Prod.fst hPair).symm, (congrArg Prod.snd hPair).symm⟩

/-- A request `idealSignMachine` accepts on the inner state is accepted as `.sign`, in every
    state. -/
theorem idealSignCorruptibleMachine_sign_step_of_ideal {st : CorruptibleSignState PK Sig}
    {req : SignRequest} {inner' : IdealSignState PK Sig} {sig : Sig}
    (h : (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).step st.inner req =
      some (inner', sig)) :
    (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).step st (.sign req) =
      some ({ st with inner := inner' }, SignReply.signature sig) := by
  show ((idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).step st.inner req).map
      (fun p => (({ st with inner := p.1 } : CorruptibleSignState PK Sig),
        SignReply.signature p.2)) = some ({ st with inner := inner' }, SignReply.signature sig)
  rw [h]
  rfl

/-- `.sign` is rejected exactly when `idealSignMachine` rejects the request on the inner
    state. -/
theorem idealSignCorruptibleMachine_sign_step_none_iff {st : CorruptibleSignState PK Sig}
    {req : SignRequest} :
    (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).step st (.sign req) =
      none ↔
    (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).step st.inner req = none := by
  constructor
  · intro h
    cases hI : (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).step st.inner req with
    | none => rfl
    | some p =>
      obtain ⟨inner', sig⟩ := p
      rw [idealSignCorruptibleMachine_sign_step_of_ideal hI] at h
      cases h
  · intro h
    show ((idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).step st.inner req).map
      (fun p => (({ st with inner := p.1 } : CorruptibleSignState PK Sig),
        SignReply.signature p.2)) = none
    rw [h]
    rfl

/-- A rejected `.sign` updates the inner state as `idealSignMachine` does on a rejection. -/
theorem idealSignCorruptibleMachine_sign_errStep (st : CorruptibleSignState PK Sig)
    (req : SignRequest) :
    (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).errStep st (.sign req) =
      { st with
        inner := (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).errStep st.inner req } :=
  by
  rfl

/-- `.corrupt` is accepted in every state and sets the flag. -/
theorem idealSignCorruptibleMachine_corrupt_step (st : CorruptibleSignState PK Sig) :
    (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).step st .corrupt =
      some ({ st with corrupted := true }, SignReply.corrupted) := by
  rfl

theorem idealSignCorruptibleMachine_corrupt_step_some {st st' : CorruptibleSignState PK Sig}
    {out : SignReply Sig}
    (h : (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).step st .corrupt =
      some (st', out)) :
    st' = { st with corrupted := true } ∧ out = SignReply.corrupted := by
  rw [idealSignCorruptibleMachine_corrupt_step] at h
  have hPair := Option.some.inj h
  exact ⟨(congrArg Prod.fst hPair).symm, (congrArg Prod.snd hPair).symm⟩

/-- **An accepted `.inject` happens in a corrupted state and carries a signature the verifier
    accepts under the enrolled key.** It changes only the injected log. -/
theorem idealSignCorruptibleMachine_inject_step_some {st st' : CorruptibleSignState PK Sig}
    {req : SignRequest} {sig : Sig} {out : SignReply Sig}
    (h : (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).step st
      (.inject req sig) = some (st', out)) :
    st.corrupted = true ∧ S.verify st.inner.enrolledPk req.message sig = true ∧
    st' = { st with injectedLog := (req.epoch, req.message, sig) :: st.injectedLog } ∧
    out = SignReply.signature sig := by
  have h' : (if (st.corrupted && S.verify st.inner.enrolledPk req.message sig) = true then
      some (({ st with injectedLog := (req.epoch, req.message, sig) :: st.injectedLog } :
        CorruptibleSignState PK Sig), SignReply.signature sig)
      else none) = some (st', out) := h
  obtain ⟨hC, hEq⟩ := signIteSome h'
  obtain ⟨hc, hv⟩ := signAndSplit hC
  have hPair := Option.some.inj hEq
  exact ⟨hc, hv, (congrArg Prod.fst hPair).symm, (congrArg Prod.snd hPair).symm⟩

/-- **After corruption every verifying signature can be emitted**, for any request: the epoch
    latch is not consulted. -/
theorem idealSignCorruptibleMachine_inject_step_of_corrupted
    {st : CorruptibleSignState PK Sig} {req : SignRequest} {sig : Sig}
    (hC : st.corrupted = true) (hV : S.verify st.inner.enrolledPk req.message sig = true) :
    (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).step st
      (.inject req sig) =
      some ({ st with injectedLog := (req.epoch, req.message, sig) :: st.injectedLog },
        SignReply.signature sig) := by
  show (if (st.corrupted && S.verify st.inner.enrolledPk req.message sig) = true then
      some (({ st with injectedLog := (req.epoch, req.message, sig) :: st.injectedLog } :
        CorruptibleSignState PK Sig), SignReply.signature sig)
      else none) = _
  rw [hC, hV]
  rfl

/-- Before corruption `.inject` is rejected. -/
theorem idealSignCorruptibleMachine_inject_step_of_uncorrupted
    {st : CorruptibleSignState PK Sig} (req : SignRequest) (sig : Sig)
    (hC : st.corrupted = false) :
    (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).step st
      (.inject req sig) = none := by
  show (if (st.corrupted && S.verify st.inner.enrolledPk req.message sig) = true then
      some (({ st with injectedLog := (req.epoch, req.message, sig) :: st.injectedLog } :
        CorruptibleSignState PK Sig), SignReply.signature sig)
      else none) = none
  rw [hC]
  rfl

/-- A signature the verifier rejects is not injected, corrupted or not. -/
theorem idealSignCorruptibleMachine_inject_step_of_unverified
    {st : CorruptibleSignState PK Sig} {req : SignRequest} {sig : Sig}
    (hV : S.verify st.inner.enrolledPk req.message sig = false) :
    (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).step st
      (.inject req sig) = none := by
  show (if (st.corrupted && S.verify st.inner.enrolledPk req.message sig) = true then
      some (({ st with injectedLog := (req.epoch, req.message, sig) :: st.injectedLog } :
        CorruptibleSignState PK Sig), SignReply.signature sig)
      else none) = none
  rw [hV]
  cases st.corrupted <;> rfl

/-- A rejected `.inject` leaves the state unchanged. -/
theorem idealSignCorruptibleMachine_inject_errStep (st : CorruptibleSignState PK Sig)
    (req : SignRequest) (sig : Sig) :
    (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).errStep st
      (.inject req sig) = st := by
  rfl

/-! ### Runs -/

/-- **The inner state of every run is a run of `idealSignMachine`** on the accepted `.sign`
    events, whatever corruptions and injections the run contains. -/
theorem idealSignCorruptibleMachine_trace_inner :
    ∀ {s₀ s_final : CorruptibleSignState PK Sig}
      {tr : List (SignCommand Sig × SignReply Sig)},
      (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace s₀ tr
        s_final →
      (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace s₀.inner
        (signedEvents tr) s_final.inner
  | _, _, _, .nil _ => .nil _
  | _, _, _, .accept (inp := inp) hStep hRest => by
    have ih := idealSignCorruptibleMachine_trace_inner hRest
    cases inp with
    | sign req =>
      obtain ⟨inner', sig, hI, hSt, hOut⟩ := idealSignCorruptibleMachine_sign_step_some hStep
      subst hSt hOut
      exact .accept hI ih
    | corrupt =>
      obtain ⟨hSt, hOut⟩ := idealSignCorruptibleMachine_corrupt_step_some hStep
      subst hSt hOut
      exact ih
    | inject req sig =>
      obtain ⟨_, _, hSt, hOut⟩ := idealSignCorruptibleMachine_inject_step_some hStep
      subst hSt hOut
      exact ih
  | _, _, _, .reject inp hNone hRest => by
    have ih := idealSignCorruptibleMachine_trace_inner hRest
    cases inp with
    | sign req =>
      exact .reject req (idealSignCorruptibleMachine_sign_step_none_iff.mp hNone) ih
    | corrupt => exact ih
    | inject req sig => exact ih

/-- **A run that ends uncorrupted started uncorrupted, accepted only `.sign` events, and left
    the injected log as it was.** -/
theorem idealSignCorruptibleMachine_trace_uncorrupted :
    ∀ {s₀ s_final : CorruptibleSignState PK Sig}
      {tr : List (SignCommand Sig × SignReply Sig)},
      (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace s₀ tr
        s_final →
      s_final.corrupted = false →
      s₀.corrupted = false ∧ tr = (signedEvents tr).map honestSignEvent ∧
        s_final.injectedLog = s₀.injectedLog
  | _, _, _, .nil _, hU => ⟨hU, rfl, rfl⟩
  | _, _, _, .accept (inp := inp) (rest := rest) hStep hRest, hU => by
    obtain ⟨ihC, ihTr, ihLog⟩ := idealSignCorruptibleMachine_trace_uncorrupted hRest hU
    cases inp with
    | sign req =>
      obtain ⟨inner', sig, _, hSt, hOut⟩ := idealSignCorruptibleMachine_sign_step_some hStep
      subst hSt hOut
      refine ⟨ihC, ?_, ihLog⟩
      show (SignCommand.sign req, SignReply.signature sig) :: rest =
        honestSignEvent (req, sig) :: (signedEvents rest).map honestSignEvent
      exact congrArg (List.cons _) ihTr
    | corrupt =>
      obtain ⟨hSt, _⟩ := idealSignCorruptibleMachine_corrupt_step_some hStep
      subst hSt
      exact Bool.noConfusion (ihC : true = false)
    | inject req sig =>
      obtain ⟨hc, _, hSt, _⟩ := idealSignCorruptibleMachine_inject_step_some hStep
      subst hSt
      exact Bool.noConfusion (hc.symm.trans ihC)
  | _, _, _, .reject inp _ hRest, hU => by
    obtain ⟨ihC, ihTr, ihLog⟩ := idealSignCorruptibleMachine_trace_uncorrupted hRest hU
    cases inp <;> exact ⟨ihC, ihTr, ihLog⟩

/-- **Corruption is monotone**: a run that starts corrupted ends corrupted. -/
theorem idealSignCorruptibleMachine_trace_corrupted_mono
    {s₀ s_final : CorruptibleSignState PK Sig} {tr : List (SignCommand Sig × SignReply Sig)}
    (hTrace : (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace s₀
      tr s_final)
    (hC : s₀.corrupted = true) : s_final.corrupted = true := by
  cases hF : s_final.corrupted with
  | true => rfl
  | false =>
    exact Bool.noConfusion
      (hC.symm.trans (idealSignCorruptibleMachine_trace_uncorrupted hTrace hF).1)

/-- **A run that ends uncorrupted accepted no `.corrupt` and no `.inject`**: each of its events
    is an honest signature. -/
theorem idealSignCorruptibleMachine_uncorrupted_trace_only_signs
    {s₀ s_final : CorruptibleSignState PK Sig} {tr : List (SignCommand Sig × SignReply Sig)}
    (hTrace : (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace s₀
      tr s_final)
    (hU : s_final.corrupted = false) :
    ∀ ev ∈ tr, ∃ (req : SignRequest) (sig : Sig),
      ev = (SignCommand.sign req, SignReply.signature sig) := by
  intro ev hev
  rw [(idealSignCorruptibleMachine_trace_uncorrupted hTrace hU).2.1] at hev
  obtain ⟨p, _, hp⟩ := List.mem_map.mp hev
  exact ⟨p.1, p.2, hp.symm⟩

/-- **Every run of `idealSignMachine` is a run of the corruptible machine** on the same
    requests with the same outputs, from any flag and injected log, which it leaves alone. -/
theorem idealSignMachine_trace_lifts_corruptible :
    ∀ {a₀ a_final : IdealSignState PK Sig} {tr : List (SignRequest × Sig)},
      (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace a₀ tr a_final →
      ∀ (c : Bool) (il : List (Nat × Bytes × Sig)),
        (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace
          ⟨a₀, c, il⟩ (tr.map honestSignEvent) ⟨a_final, c, il⟩
  | _, _, _, .nil _ => fun _ _ => .nil _
  | _, _, _, .accept hStep hRest => fun c il =>
    .accept (idealSignCorruptibleMachine_sign_step_of_ideal hStep)
      (idealSignMachine_trace_lifts_corruptible hRest c il)
  | _, _, _, .reject inp hNone hRest => fun c il =>
    Machine.ValidTrace.reject (SignCommand.sign inp)
      (idealSignCorruptibleMachine_sign_step_none_iff.mpr hNone)
      (idealSignMachine_trace_lifts_corruptible hRest c il)

/-- **`idealSignMachine` is the corruption-free fragment.** A run of the corruptible machine
    that ends uncorrupted is, event for event, a run of `idealSignMachine` between the inner
    states. -/
theorem idealSignCorruptibleMachine_uncorrupted_trace_is_ideal
    {s₀ s_final : CorruptibleSignState PK Sig} {tr : List (SignCommand Sig × SignReply Sig)}
    (hTrace : (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace s₀
      tr s_final)
    (hU : s_final.corrupted = false) :
    ∃ tr' : List (SignRequest × Sig), tr = tr'.map honestSignEvent ∧
      (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace s₀.inner tr'
        s_final.inner :=
  ⟨signedEvents tr, (idealSignCorruptibleMachine_trace_uncorrupted hTrace hU).2.1,
    idealSignCorruptibleMachine_trace_inner hTrace⟩

/-- **Conservative extension on initialized traces.** The corruptible machine admits a trace
    of honest signature events exactly when `idealSignMachine` admits the underlying trace. -/
theorem idealSignCorruptibleMachine_admits_honest_iff (tr : List (SignRequest × Sig)) :
    (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).AdmitsTrace
      (tr.map honestSignEvent) ↔
    (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).AdmitsTrace tr := by
  constructor
  · rintro ⟨s₀, s_final, hInit, hTrace⟩
    have hInit' : s₀ = CorruptibleSignState.empty pk₀ stateful₀ := hInit
    subst hInit'
    have hInner := idealSignCorruptibleMachine_trace_inner hTrace
    rw [signedEvents_map_honest] at hInner
    exact ⟨_, s_final.inner, rfl, hInner⟩
  · rintro ⟨a₀, a_final, hInit, hTrace⟩
    have hInit' : a₀ = IdealSignState.empty pk₀ stateful₀ := hInit
    subst hInit'
    exact ⟨_, _, rfl, idealSignMachine_trace_lifts_corruptible hTrace false []⟩

/-- The enrolled key and the mode never change along a run, corrupted or not. -/
theorem idealSignCorruptibleMachine_trace_key_mode
    {s₀ s_final : CorruptibleSignState PK Sig} {tr : List (SignCommand Sig × SignReply Sig)}
    (hTrace : (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace s₀
      tr s_final) :
    s_final.inner.enrolledPk = s₀.inner.enrolledPk ∧
    s_final.inner.statefulEpochs = s₀.inner.statefulEpochs :=
  idealSignMachine_trace_key_mode (idealSignCorruptibleMachine_trace_inner hTrace)

/-- The injected log of a run is what it held at the start plus the accepted `.inject`
    events. -/
theorem idealSignCorruptibleMachine_trace_injectedLog :
    ∀ {s₀ s_final : CorruptibleSignState PK Sig}
      {tr : List (SignCommand Sig × SignReply Sig)},
      (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace s₀ tr
        s_final →
      ∀ e, e ∈ s_final.injectedLog ↔
        (e ∈ s₀.injectedLog ∨ ∃ p ∈ injectedEvents tr, e = (p.1.epoch, p.1.message, p.2))
  | _, _, _, .nil _ => fun e => by
    constructor
    · exact fun h => .inl h
    · intro h
      rcases h with h | ⟨p, hp, _⟩
      · exact h
      · exact absurd (hp : p ∈ ([] : List (SignRequest × Sig))) List.not_mem_nil
  | s₀, _, _, .accept (inp := inp) (rest := rest) hStep hRest => fun e => by
    have ih := idealSignCorruptibleMachine_trace_injectedLog hRest e
    cases inp with
    | sign req =>
      obtain ⟨inner', sig, _, hSt, hOut⟩ := idealSignCorruptibleMachine_sign_step_some hStep
      subst hSt hOut
      exact ih
    | corrupt =>
      obtain ⟨hSt, hOut⟩ := idealSignCorruptibleMachine_corrupt_step_some hStep
      subst hSt hOut
      exact ih
    | inject req sig =>
      obtain ⟨_, _, hSt, hOut⟩ := idealSignCorruptibleMachine_inject_step_some hStep
      subst hSt hOut
      rw [injectedEvents_cons_inject]
      have ih' : e ∈ _ ↔ (e ∈ (req.epoch, req.message, sig) :: s₀.injectedLog ∨
          ∃ p ∈ injectedEvents rest, e = (p.1.epoch, p.1.message, p.2)) := ih
      constructor
      · intro h
        rcases ih'.mp h with h1 | ⟨p, hp, hpe⟩
        · rcases List.mem_cons.mp h1 with hH | hT
          · exact .inr ⟨(req, sig), List.mem_cons.mpr (.inl rfl), hH⟩
          · exact .inl hT
        · exact .inr ⟨p, List.mem_cons_of_mem _ hp, hpe⟩
      · intro h
        apply ih'.mpr
        rcases h with h1 | ⟨p, hp, hpe⟩
        · exact .inl (List.mem_cons_of_mem _ h1)
        · rcases List.mem_cons.mp hp with hH | hT
          · refine .inl (List.mem_cons.mpr (.inl ?_))
            rw [hpe, hH]
          · exact .inr ⟨p, hT, hpe⟩
  | _, _, _, .reject inp _ hRest => fun e => by
    have ih := idealSignCorruptibleMachine_trace_injectedLog hRest e
    cases inp <;> exact ih

/-- Every injected signature of a run verifies under the key of its starting state. -/
theorem idealSignCorruptibleMachine_trace_injected_verified :
    ∀ {s₀ s_final : CorruptibleSignState PK Sig}
      {tr : List (SignCommand Sig × SignReply Sig)},
      (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace s₀ tr
        s_final →
      ∀ p ∈ injectedEvents tr, S.verify s₀.inner.enrolledPk p.1.message p.2 = true
  | _, _, _, .nil _ => fun p hp =>
    absurd (hp : p ∈ ([] : List (SignRequest × Sig))) List.not_mem_nil
  | s₀, _, _, .accept (inp := inp) (rest := rest) hStep hRest => fun p hp => by
    have ih := idealSignCorruptibleMachine_trace_injected_verified hRest p
    cases inp with
    | sign req =>
      obtain ⟨inner', sig, hI, hSt, hOut⟩ := idealSignCorruptibleMachine_sign_step_some hStep
      have hRec := (idealSignMachine_step_some hI).2.2.2
      subst hRec hSt hOut
      exact ih hp
    | corrupt =>
      obtain ⟨hSt, hOut⟩ := idealSignCorruptibleMachine_corrupt_step_some hStep
      subst hSt hOut
      exact ih hp
    | inject req sig =>
      obtain ⟨_, hV, hSt, hOut⟩ := idealSignCorruptibleMachine_inject_step_some hStep
      subst hSt hOut
      rw [injectedEvents_cons_inject] at hp
      rcases List.mem_cons.mp hp with hH | hT
      · rw [hH]
        exact hV
      · exact ih hT
  | s₀, _, _, .reject inp _ hRest => fun p hp => by
    have ih := idealSignCorruptibleMachine_trace_injected_verified hRest p hp
    cases inp with
    | sign req =>
      have ih' : S.verify ((idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).errStep
          s₀.inner req).enrolledPk p.1.message p.2 = true := ih
      rw [(idealSignMachine_errStep_facts (S := S) (pk₀ := pk₀) (stateful₀ := stateful₀)
        (maxWindow := maxWindow) (oracleSign := oracleSign) s₀.inner req).1] at ih'
      exact ih'
    | corrupt => exact ih
    | inject req sig => exact ih

/-- **Every emitted signature of a run, signed or injected, before or after corruption,
    verifies under the key of its starting state.** -/
theorem idealSignCorruptibleMachine_trace_emitted_verified
    {s₀ s_final : CorruptibleSignState PK Sig} {tr : List (SignCommand Sig × SignReply Sig)}
    (hTrace : (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace s₀
      tr s_final) :
    ∀ p ∈ emittedEvents tr, S.verify s₀.inner.enrolledPk p.1.message p.2 = true := by
  intro p hp
  rcases mem_emittedEvents.mp hp with h | h
  · exact idealSignMachine_trace_outputs_verified
      (idealSignCorruptibleMachine_trace_inner hTrace) p h
  · exact idealSignCorruptibleMachine_trace_injected_verified hTrace p h

/-- **Honest-prefix safety.** If an initialized run ends uncorrupted, then each of its events
    is an honest signature, every emitted signature verifies under `pk₀`, in stateful mode
    the epochs of the emitted signatures strictly increase (no epoch signs twice), the signed
    log is exactly the emitted signatures, and nothing was injected. The verification clause
    holds without the hypothesis
    (`idealSignCorruptibleMachine_trace_emitted_verified`); the epoch clause does not
    (`idealSignCorruptible_corrupted_run_reuses_epoch`). -/
theorem idealSignCorruptibleMachine_uncorrupted_trace_safe
    {s_final : CorruptibleSignState PK Sig} {tr : List (SignCommand Sig × SignReply Sig)}
    (hTrace : (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace
      (CorruptibleSignState.empty pk₀ stateful₀) tr s_final)
    (hU : s_final.corrupted = false) :
    tr = (emittedEvents tr).map honestSignEvent ∧
    (∀ p ∈ emittedEvents tr, S.verify pk₀ p.1.message p.2 = true) ∧
    (stateful₀ = true → (emittedEvents tr).Pairwise (fun a b => a.1.epoch < b.1.epoch)) ∧
    (∀ e, e ∈ s_final.inner.signedLog ↔
      ∃ p ∈ emittedEvents tr, e = (p.1.epoch, p.1.message, p.2)) ∧
    s_final.injectedLog = [] := by
  obtain ⟨_, hTr, hLog⟩ := idealSignCorruptibleMachine_trace_uncorrupted hTrace hU
  have hInner : (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace
      (IdealSignState.empty pk₀ stateful₀) (signedEvents tr) s_final.inner :=
    idealSignCorruptibleMachine_trace_inner hTrace
  have hE : emittedEvents tr = signedEvents tr := by
    rw [hTr, emittedEvents_map_honest, signedEvents_map_honest]
  rw [hE]
  refine ⟨hTr, idealSignMachine_trace_outputs_verified hInner,
    fun hS => (idealSignMachine_trace_epochs_increasing hS hInner).2, fun e => ⟨fun he => ?_,
      fun h => ?_⟩, hLog⟩
  · rcases idealSignMachine_trace_log_sound hInner e he with hOld | hNew
    · exact absurd hOld List.not_mem_nil
    · exact hNew
  · obtain ⟨p, hp, hpe⟩ := h
    rw [hpe]
    exact (idealSignMachine_trace_log_complete hInner).2 p hp

end Corruptible

/-! ## Forgery events under corruption -/

/-- `EUF-CMA` forgery against the corruptible functionality: `msgStar` is fresh against the
    signed log and against the injected log, and `sigStar` verifies on it. -/
def CorruptibleEufCmaForgery {PK SK Sig : Type}
    (S : SigScheme PK SK Sig) (st : CorruptibleSignState PK Sig)
    (msgStar : Bytes) (sigStar : Sig) : Prop :=
  EufCmaForgery S st.inner msgStar sigStar ∧ ∀ entry ∈ st.injectedLog, entry.2.1 ≠ msgStar

/-- `SUF-CMA` forgery against the corruptible functionality: the pair is fresh against both
    logs and verifies. -/
def CorruptibleSufCmaForgery {PK SK Sig : Type} [DecidableEq Sig]
    (S : SigScheme PK SK Sig) (st : CorruptibleSignState PK Sig)
    (msgStar : Bytes) (sigStar : Sig) : Prop :=
  SufCmaForgery S st.inner msgStar sigStar ∧
    ∀ entry ∈ st.injectedLog, (entry.2.1, entry.2.2) ≠ (msgStar, sigStar)

theorem CorruptibleEufCmaForgery.toSufCma {PK SK Sig : Type} [DecidableEq Sig]
    {S : SigScheme PK SK Sig} {st : CorruptibleSignState PK Sig} {msgStar : Bytes}
    {sigStar : Sig} (h : CorruptibleEufCmaForgery S st msgStar sigStar) :
    CorruptibleSufCmaForgery S st msgStar sigStar := by
  refine ⟨h.1.toSufCma, fun entry hMem hEq => ?_⟩
  injection hEq with hMsg _
  exact h.2 entry hMem hMsg

section CorruptibleForgery
variable {PK SK Sig : Type} {S : SigScheme PK SK Sig} {pk₀ : PK} {stateful₀ : Bool}
  {maxWindow : Nat} {oracleSign : SignRequest → Option Sig}

/-- **`EUF-CMA` forgery against a run with corruption.** After any initialized run, a pair is
    a `CorruptibleEufCmaForgery` against the final state exactly when it verifies under `pk₀`
    and its message was never the message of an emitted signature, signed or injected. -/
theorem idealSignCorruptibleMachine_eufCmaForgery_iff
    {s_final : CorruptibleSignState PK Sig} {tr : List (SignCommand Sig × SignReply Sig)}
    (hTrace : (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace
      (CorruptibleSignState.empty pk₀ stateful₀) tr s_final) (msg : Bytes) (sig : Sig) :
    CorruptibleEufCmaForgery S s_final msg sig ↔
      (S.verify pk₀ msg sig = true ∧ ∀ p ∈ emittedEvents tr, p.1.message ≠ msg) := by
  have hInner : (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace
      (IdealSignState.empty pk₀ stateful₀) (signedEvents tr) s_final.inner :=
    idealSignCorruptibleMachine_trace_inner hTrace
  have hI := idealSignMachine_eufCmaForgery_iff hInner msg sig
  have hLog := idealSignCorruptibleMachine_trace_injectedLog hTrace
  unfold CorruptibleEufCmaForgery
  constructor
  · rintro ⟨hE, hInj⟩
    obtain ⟨hV, hFresh⟩ := hI.mp hE
    refine ⟨hV, fun p hp => ?_⟩
    rcases mem_emittedEvents.mp hp with h | h
    · exact hFresh p h
    · exact hInj _ ((hLog _).mpr (.inr ⟨p, h, rfl⟩))
  · rintro ⟨hV, hFresh⟩
    refine ⟨hI.mpr ⟨hV, fun p hp => hFresh p (mem_emittedEvents.mpr (.inl hp))⟩,
      fun e he => ?_⟩
    rcases (hLog e).mp he with h | ⟨p, hp, hpe⟩
    · exact absurd h List.not_mem_nil
    · rw [hpe]
      exact hFresh p (mem_emittedEvents.mpr (.inr hp))

/-- **`SUF-CMA` forgery against a run with corruption.** A pair is a
    `CorruptibleSufCmaForgery` against the final state exactly when it verifies under `pk₀` and
    was never emitted, signed or injected. -/
theorem idealSignCorruptibleMachine_sufCmaForgery_iff [DecidableEq Sig]
    {s_final : CorruptibleSignState PK Sig} {tr : List (SignCommand Sig × SignReply Sig)}
    (hTrace : (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace
      (CorruptibleSignState.empty pk₀ stateful₀) tr s_final) (msg : Bytes) (sig : Sig) :
    CorruptibleSufCmaForgery S s_final msg sig ↔
      (S.verify pk₀ msg sig = true ∧
        ∀ p ∈ emittedEvents tr, (p.1.message, p.2) ≠ (msg, sig)) := by
  have hInner : (idealSignMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace
      (IdealSignState.empty pk₀ stateful₀) (signedEvents tr) s_final.inner :=
    idealSignCorruptibleMachine_trace_inner hTrace
  have hI := idealSignMachine_sufCmaForgery_iff hInner msg sig
  have hLog := idealSignCorruptibleMachine_trace_injectedLog hTrace
  unfold CorruptibleSufCmaForgery
  constructor
  · rintro ⟨hE, hInj⟩
    obtain ⟨hV, hFresh⟩ := hI.mp hE
    refine ⟨hV, fun p hp => ?_⟩
    rcases mem_emittedEvents.mp hp with h | h
    · exact hFresh p h
    · exact hInj _ ((hLog _).mpr (.inr ⟨p, h, rfl⟩))
  · rintro ⟨hV, hFresh⟩
    refine ⟨hI.mpr ⟨hV, fun p hp => hFresh p (mem_emittedEvents.mpr (.inl hp))⟩,
      fun e he => ?_⟩
    rcases (hLog e).mp he with h | ⟨p, hp, hpe⟩
    · exact absurd h List.not_mem_nil
    · rw [hpe]
      exact hFresh p (mem_emittedEvents.mpr (.inr hp))

/-- **Forgery against an uncorrupted run is forgery against `idealSignMachine`.** If an
    initialized run ends uncorrupted, a `CorruptibleEufCmaForgery` against its final state is
    the same event as an `EufCmaForgery` against the inner state, which
    `idealSignMachine_eufCmaForgery_iff` characterises on the projected run. -/
theorem idealSignCorruptibleMachine_uncorrupted_eufCmaForgery_iff
    {s_final : CorruptibleSignState PK Sig} {tr : List (SignCommand Sig × SignReply Sig)}
    (hTrace : (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace
      (CorruptibleSignState.empty pk₀ stateful₀) tr s_final)
    (hU : s_final.corrupted = false) (msg : Bytes) (sig : Sig) :
    CorruptibleEufCmaForgery S s_final msg sig ↔ EufCmaForgery S s_final.inner msg sig := by
  have hLog : s_final.injectedLog = [] :=
    (idealSignCorruptibleMachine_trace_uncorrupted hTrace hU).2.2
  unfold CorruptibleEufCmaForgery
  rw [hLog]
  exact ⟨fun h => h.1, fun h => ⟨h, fun _ hMem => absurd hMem List.not_mem_nil⟩⟩

/-- **No emitted signature, signed or injected, is a forgery** against the state the run ends
    in. -/
theorem idealSignCorruptibleMachine_trace_emitted_not_forgeries [DecidableEq Sig]
    {s_final : CorruptibleSignState PK Sig} {tr : List (SignCommand Sig × SignReply Sig)}
    (hTrace : (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace
      (CorruptibleSignState.empty pk₀ stateful₀) tr s_final) :
    ∀ p ∈ emittedEvents tr, ¬ CorruptibleEufCmaForgery S s_final p.1.message p.2 ∧
      ¬ CorruptibleSufCmaForgery S s_final p.1.message p.2 := by
  intro p hp
  have hSuf : ¬ CorruptibleSufCmaForgery S s_final p.1.message p.2 := fun h =>
    ((idealSignCorruptibleMachine_sufCmaForgery_iff hTrace _ _).mp h).2 p hp rfl
  exact ⟨fun h => hSuf h.toSufCma, hSuf⟩

/-- **No unforgeability statement survives corruption.** In a corrupted state every pair the
    verifier accepts is emitted by one `.inject`, at any epoch; afterwards its message is not
    fresh, so no signature on it is a `CorruptibleEufCmaForgery` and the pair is not a
    `CorruptibleSufCmaForgery`. -/
theorem idealSignCorruptibleMachine_corrupted_absorbs_forgery [DecidableEq Sig]
    {st : CorruptibleSignState PK Sig} (hC : st.corrupted = true)
    (ep : Nat) (msg : Bytes) (sig : Sig)
    (hV : S.verify st.inner.enrolledPk msg sig = true) :
    ∃ st' : CorruptibleSignState PK Sig,
      (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).step st
        (.inject ⟨ep, msg⟩ sig) = some (st', SignReply.signature sig) ∧
      st'.corrupted = true ∧
      (∀ sig' : Sig, ¬ CorruptibleEufCmaForgery S st' msg sig') ∧
      ¬ CorruptibleSufCmaForgery S st' msg sig :=
  ⟨{ st with injectedLog := (ep, msg, sig) :: st.injectedLog },
    idealSignCorruptibleMachine_inject_step_of_corrupted (req := ⟨ep, msg⟩) hC hV, hC,
    fun _ h => h.2 (ep, msg, sig) (List.mem_cons.mpr (.inl rfl)) rfl,
    fun h => h.2 (ep, msg, sig) (List.mem_cons.mpr (.inl rfl)) rfl⟩

/-- **Every corrupted run extends by one accepted `.inject` that emits a given verifying
    pair**, at any epoch; no signature on its message is a forgery against the extended run. -/
theorem idealSignCorruptibleMachine_corrupted_run_absorbs_forgery [DecidableEq Sig]
    {s_final : CorruptibleSignState PK Sig} {tr : List (SignCommand Sig × SignReply Sig)}
    (hTrace : (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace
      (CorruptibleSignState.empty pk₀ stateful₀) tr s_final)
    (hC : s_final.corrupted = true) (ep : Nat) (msg : Bytes) (sig : Sig)
    (hV : S.verify pk₀ msg sig = true) :
    ∃ s' : CorruptibleSignState PK Sig,
      (idealSignCorruptibleMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace
        (CorruptibleSignState.empty pk₀ stateful₀)
        (tr ++ [(SignCommand.inject ⟨ep, msg⟩ sig, SignReply.signature sig)]) s' ∧
      (∀ sig' : Sig, ¬ CorruptibleEufCmaForgery S s' msg sig') ∧
      ¬ CorruptibleSufCmaForgery S s' msg sig := by
  have hPk : s_final.inner.enrolledPk = pk₀ :=
    (idealSignCorruptibleMachine_trace_key_mode hTrace).1
  have hV' : S.verify s_final.inner.enrolledPk msg sig = true := by
    rw [hPk]
    exact hV
  obtain ⟨s', hStep, _, hEuf, hSuf⟩ := idealSignCorruptibleMachine_corrupted_absorbs_forgery
    (S := S) (pk₀ := pk₀) (stateful₀ := stateful₀) (maxWindow := maxWindow)
    (oracleSign := oracleSign) hC ep msg sig hV'
  exact ⟨s', validTrace_snoc hTrace hStep, hEuf, hSuf⟩

end CorruptibleForgery

/-! ## Rejected behaviours of the corruptible machine -/

/-- `.inject` before `.corrupt` is rejected, although the verifier accepts the signature. -/
theorem idealSignCorruptible_rejects_inject_before_corrupt :
    ¬ (((idealSignCorruptibleMachine acceptAllSigScheme () true 8 (fun _ => some ())).step
      (CorruptibleSignState.empty () true) (.inject ⟨0, []⟩ ())).isSome = true) := by
  decide

/-- After `.corrupt`, a signature the verifier rejects is still not injected. -/
theorem idealSignCorruptible_rejects_unverified_inject_after_corrupt :
    ¬ (((idealSignCorruptibleMachine rejectAllSigScheme () false 0 (fun _ => some ())).step
      ((idealSignCorruptibleMachine rejectAllSigScheme () false 0 (fun _ => some ())).runStep
        (CorruptibleSignState.empty () false) .corrupt).1 (.inject ⟨0, []⟩ ())).isSome =
          true) := by
  decide

/-- The run `sign` at epoch `0`, `corrupt`, `inject` at epoch `0` of the stateful accept-all
    machine. -/
theorem idealSignCorruptible_epoch_reuse_run :
    ∃ s_final : CorruptibleSignState Unit Unit,
      (idealSignCorruptibleMachine acceptAllSigScheme () true 8 (fun _ => some ())).ValidTrace
        (CorruptibleSignState.empty () true)
        [(SignCommand.sign ⟨0, []⟩, SignReply.signature ()),
         (SignCommand.corrupt, SignReply.corrupted),
         (SignCommand.inject ⟨0, [1]⟩ (), SignReply.signature ())] s_final ∧
      s_final.corrupted = true :=
  ⟨_, .accept (idealSignCorruptibleMachine_sign_step_of_ideal
      (idealSignMachine_step_of_valid (by decide) rfl rfl))
    (.accept (idealSignCorruptibleMachine_corrupt_step _)
      (.accept (idealSignCorruptibleMachine_inject_step_of_corrupted rfl rfl) (.nil _))), rfl⟩

/-- **The one-time-epoch property fails for corrupted runs.** Without the hypothesis that the
    run ends uncorrupted, the epoch clause of
    `idealSignCorruptibleMachine_uncorrupted_trace_safe` is false: after `sign` at epoch `0`
    and `corrupt`, an `inject` at epoch `0` is accepted, so two emitted signatures share an
    epoch. -/
theorem idealSignCorruptible_corrupted_run_reuses_epoch :
    ¬ (∀ (tr : List (SignCommand Unit × SignReply Unit))
        (s_final : CorruptibleSignState Unit Unit),
        (idealSignCorruptibleMachine acceptAllSigScheme () true 8
          (fun _ => some ())).ValidTrace (CorruptibleSignState.empty () true) tr s_final →
        (emittedEvents tr).Pairwise (fun a b => a.1.epoch < b.1.epoch)) := by
  intro h
  obtain ⟨s_final, hTr, _⟩ := idealSignCorruptible_epoch_reuse_run
  have hPw : List.Pairwise (fun a b : SignRequest × Unit => a.1.epoch < b.1.epoch)
      [((⟨0, []⟩ : SignRequest), ()), ((⟨0, [1]⟩ : SignRequest), ())] := h _ _ hTr
  exact Nat.lt_irrefl 0 ((List.pairwise_cons.mp hPw).1 _ (List.mem_cons.mpr (.inl rfl)))

/-- An honest two-signature run of the stateful accept-all machine ends uncorrupted, so
    `idealSignCorruptibleMachine_uncorrupted_trace_safe` applies to it: its hypotheses are
    jointly satisfiable. -/
theorem idealSignCorruptible_honest_run_epochs_increase :
    (emittedEvents
      [(SignCommand.sign ⟨0, []⟩, SignReply.signature ()),
       (SignCommand.sign ⟨2, [1]⟩, SignReply.signature ())]).Pairwise
      (fun a b : SignRequest × Unit => a.1.epoch < b.1.epoch) :=
  (idealSignCorruptibleMachine_uncorrupted_trace_safe (S := acceptAllSigScheme) (pk₀ := ())
    (stateful₀ := true) (maxWindow := 8) (oracleSign := fun _ => some ())
    (s_final := ⟨((IdealSignState.empty () true).record ⟨0, []⟩ ()).record ⟨2, [1]⟩ (),
      false, []⟩)
    (.accept (idealSignCorruptibleMachine_sign_step_of_ideal
        (idealSignMachine_step_of_valid (by decide) rfl rfl))
      (.accept (idealSignCorruptibleMachine_sign_step_of_ideal
        (idealSignMachine_step_of_valid (by decide) rfl rfl)) (.nil _))) rfl).2.2.1 rfl

#tooth_pair idealSignCorruptibleMachine_inject_step_some vs
  idealSignCorruptible_rejects_inject_before_corrupt
#tooth_pair idealSignCorruptibleMachine_trace_emitted_verified vs
  idealSignCorruptible_rejects_unverified_inject_after_corrupt
#tooth_pair idealSignCorruptibleMachine_uncorrupted_trace_safe vs
  idealSignCorruptible_corrupted_run_reuses_epoch

/-! ## Per-Request Randomized Signing Refinement (`RandomizedSigScheme`)

`SigScheme.sign` above takes `(sk, ep, msg)` without a per-request randomness parameter, modeling
deterministic signing (or hedged signing at a fixed randomness slice). Here we model hedged /
per-request randomized signing (`optRand : Bytes`, as in FIPS 205 `slh_sign_internal` and QSAG
`prodSignQuery`) first-class:

* `RandomizedSigScheme`: `derivePk`, `sign sk ep optRand msg`, `verify`, and `correct`.
* `RandomizedSigScheme.atFixedRand`: every `RandomizedSigScheme` specializes at any fixed `optRand`
  to a `SigScheme`.
* `RandomizedSignRequest`, `RandomizedIdealSignState`, `idealRandomizedSignMachine`,
  `latchedRandomizedSignerMachine`, and `latchedRandomizedSigner_refines_ideal`: exact forward
  simulation (`latchedRandomizedSignerMachine ⊑ idealRandomizedSignMachine`) preserving
  per-signature `optRand`, verified outputs, strictly increasing epochs in stateful mode, and epoch
  consumption on failed signing. -/

/-- Signature scheme interface with explicit per-request signer randomness `optRand : Bytes`. -/
structure RandomizedSigScheme (PK SK Sig : Type) where
  derivePk : SK → PK
  sign : SK → Nat → Bytes → Bytes → Option Sig
  verify : PK → Bytes → Sig → Bool
  correct : ∀ (sk : SK) (ep : Nat) (optRand msg : Bytes) (sig : Sig),
    sign sk ep optRand msg = some sig → verify (derivePk sk) msg sig = true

/-- Fixing `optRand` projects a `RandomizedSigScheme` onto a deterministic-interface `SigScheme`. -/
def RandomizedSigScheme.atFixedRand {PK SK Sig : Type}
    (S : RandomizedSigScheme PK SK Sig) (optRand : Bytes) : SigScheme PK SK Sig where
  derivePk := S.derivePk
  sign sk ep msg := S.sign sk ep optRand msg
  verify := S.verify
  correct sk ep msg sig h := S.correct sk ep optRand msg sig h

/-- Per-request randomized signing request: target `epoch`, per-signature `optRand`, and `message`. -/
structure RandomizedSignRequest where
  epoch : Nat
  optRand : Bytes
  message : Bytes
  deriving DecidableEq, Repr

/-- Persistent state of the ideal per-request randomized signing functionality. -/
structure RandomizedIdealSignState (PK Sig : Type) where
  enrolledPk : PK
  statefulEpochs : Bool
  nextEpoch : Nat
  usedEpochs : List Nat
  signedLog : List (Nat × Bytes × Bytes × Sig)

def RandomizedIdealSignState.empty {PK Sig : Type} (pk : PK) (stateful : Bool) :
    RandomizedIdealSignState PK Sig :=
  { enrolledPk := pk
    statefulEpochs := stateful
    nextEpoch := 0
    usedEpochs := []
    signedLog := [] }

def RandomizedIdealSignState.consume {PK Sig : Type}
    (st : RandomizedIdealSignState PK Sig) (ep : Nat) :
    RandomizedIdealSignState PK Sig :=
  { st with nextEpoch := ep + 1, usedEpochs := ep :: st.usedEpochs }

def RandomizedIdealSignState.record {PK Sig : Type}
    (st : RandomizedIdealSignState PK Sig) (req : RandomizedSignRequest) (sig : Sig) :
    RandomizedIdealSignState PK Sig :=
  { st.consume req.epoch with
      signedLog := (req.epoch, req.optRand, req.message, sig) :: st.signedLog }

def verifiedRandomizedCandidate {PK SK Sig : Type} (S : RandomizedSigScheme PK SK Sig) (pk : PK)
    (oracleSign : RandomizedSignRequest → Option Sig) (req : RandomizedSignRequest) : Option Sig :=
  match oracleSign req with
  | some sig => if S.verify pk req.message sig = true then some sig else none
  | none => none

theorem verifiedRandomizedCandidate_some {PK SK Sig : Type}
    {S : RandomizedSigScheme PK SK Sig} {pk : PK}
    {oracleSign : RandomizedSignRequest → Option Sig} {req : RandomizedSignRequest} {sig : Sig}
    (h : verifiedRandomizedCandidate S pk oracleSign req = some sig) :
    oracleSign req = some sig ∧ S.verify pk req.message sig = true := by
  unfold verifiedRandomizedCandidate at h
  cases hO : oracleSign req with
  | none => rw [hO] at h; cases h
  | some s =>
    rw [hO] at h
    obtain ⟨hV, hEq⟩ := signIteSome h
    have hs : s = sig := Option.some.inj hEq
    exact ⟨congrArg some hs, hs ▸ hV⟩

theorem verifiedRandomizedCandidate_of_valid {PK SK Sig : Type}
    {S : RandomizedSigScheme PK SK Sig} {pk : PK}
    {oracleSign : RandomizedSignRequest → Option Sig} {req : RandomizedSignRequest} {sig : Sig}
    (hO : oracleSign req = some sig) (hV : S.verify pk req.message sig = true) :
    verifiedRandomizedCandidate S pk oracleSign req = some sig := by
  unfold verifiedRandomizedCandidate
  rw [hO]
  dsimp only
  rw [hV]
  rfl

/-- **Ideal per-request randomized signing machine.** -/
def idealRandomizedSignMachine {PK SK Sig : Type} (S : RandomizedSigScheme PK SK Sig)
    (pk₀ : PK) (stateful₀ : Bool) (maxWindow : Nat)
    (oracleSign : RandomizedSignRequest → Option Sig) :
    Machine (RandomizedIdealSignState PK Sig) RandomizedSignRequest Sig where
  Init st := st = RandomizedIdealSignState.empty pk₀ stateful₀
  step st req :=
    if epochAdmissible st.statefulEpochs maxWindow st.nextEpoch req.epoch = true then
      (verifiedRandomizedCandidate S st.enrolledPk oracleSign req).map
        (fun sig => (st.record req sig, sig))
    else none
  errStep st req :=
    if epochAdmissible st.statefulEpochs maxWindow st.nextEpoch req.epoch = true then
      st.consume req.epoch
    else st

theorem idealRandomizedSignMachine_step_some {PK SK Sig : Type}
    {S : RandomizedSigScheme PK SK Sig} {pk₀ : PK} {stateful₀ : Bool} {maxWindow : Nat}
    {oracleSign : RandomizedSignRequest → Option Sig}
    {st st' : RandomizedIdealSignState PK Sig} {req : RandomizedSignRequest} {sig : Sig}
    (h : (idealRandomizedSignMachine S pk₀ stateful₀ maxWindow oracleSign).step st req =
      some (st', sig)) :
    epochAdmissible st.statefulEpochs maxWindow st.nextEpoch req.epoch = true ∧
    oracleSign req = some sig ∧
    S.verify st.enrolledPk req.message sig = true ∧
    st' = st.record req sig := by
  unfold idealRandomizedSignMachine at h
  dsimp only at h
  obtain ⟨hA, hMap⟩ := signIteSome h
  obtain ⟨s, hC, hPair⟩ := signMapSome hMap
  have hs : s = sig := congrArg Prod.snd hPair
  have hSt : st.record req s = st' := congrArg Prod.fst hPair
  obtain ⟨hO, hV⟩ := verifiedRandomizedCandidate_some hC
  exact ⟨hA, hs ▸ hO, hs ▸ hV, hs ▸ hSt.symm⟩

theorem idealRandomizedSignMachine_step_emits_verified {PK SK Sig : Type}
    {S : RandomizedSigScheme PK SK Sig} {pk₀ : PK} {stateful₀ : Bool} {maxWindow : Nat}
    {oracleSign : RandomizedSignRequest → Option Sig}
    {st st' : RandomizedIdealSignState PK Sig} {req : RandomizedSignRequest} {sig : Sig}
    (h : (idealRandomizedSignMachine S pk₀ stateful₀ maxWindow oracleSign).step st req =
      some (st', sig)) :
    S.verify st.enrolledPk req.message sig = true :=
  (idealRandomizedSignMachine_step_some h).2.2.1

theorem idealRandomizedSignMachine_step_of_valid {PK SK Sig : Type}
    {S : RandomizedSigScheme PK SK Sig} {pk₀ : PK} {stateful₀ : Bool} {maxWindow : Nat}
    {oracleSign : RandomizedSignRequest → Option Sig}
    {st : RandomizedIdealSignState PK Sig} {req : RandomizedSignRequest} {sig : Sig}
    (hA : epochAdmissible st.statefulEpochs maxWindow st.nextEpoch req.epoch = true)
    (hO : oracleSign req = some sig)
    (hV : S.verify st.enrolledPk req.message sig = true) :
    (idealRandomizedSignMachine S pk₀ stateful₀ maxWindow oracleSign).step st req =
      some (st.record req sig, sig) := by
  unfold idealRandomizedSignMachine
  dsimp only
  rw [hA, verifiedRandomizedCandidate_of_valid hO hV]
  rfl

theorem idealRandomizedSignMachine_trace_outputs_verified {PK SK Sig : Type}
    {S : RandomizedSigScheme PK SK Sig} {pk₀ : PK} {stateful₀ : Bool} {maxWindow : Nat}
    {oracleSign : RandomizedSignRequest → Option Sig} :
    ∀ {s₀ s_final : RandomizedIdealSignState PK Sig}
      {tr : List (RandomizedSignRequest × Sig)},
      (idealRandomizedSignMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace s₀ tr s_final →
      ∀ p ∈ tr, S.verify s₀.enrolledPk p.1.message p.2 = true
  | _, _, _, .nil _ => fun _ h => nomatch h
  | s₀, _, _, .accept hStep hRest => fun p hp => by
    obtain ⟨_, _, hV, hEq⟩ := idealRandomizedSignMachine_step_some hStep
    rcases List.mem_cons.mp hp with hHead | hTail
    · rw [hHead]; exact hV
    · have ih := idealRandomizedSignMachine_trace_outputs_verified hRest p hTail
      rw [hEq] at ih
      exact ih
  | s₀, _, _, .reject inp _ hRest => fun p hp => by
    have ih := idealRandomizedSignMachine_trace_outputs_verified hRest p hp
    unfold idealRandomizedSignMachine at ih
    dsimp only at ih
    cases hA : epochAdmissible s₀.statefulEpochs maxWindow s₀.nextEpoch inp.epoch with
    | false => rw [hA] at ih; exact ih
    | true => rw [hA] at ih; exact ih

theorem idealRandomizedSignMachine_errStep_facts {PK SK Sig : Type}
    {S : RandomizedSigScheme PK SK Sig} {pk₀ : PK} {stateful₀ : Bool} {maxWindow : Nat}
    {oracleSign : RandomizedSignRequest → Option Sig}
    (st : RandomizedIdealSignState PK Sig) (req : RandomizedSignRequest) :
    ((idealRandomizedSignMachine S pk₀ stateful₀ maxWindow oracleSign).errStep st req).enrolledPk =
      st.enrolledPk ∧
    ((idealRandomizedSignMachine S pk₀ stateful₀ maxWindow oracleSign).errStep st req).statefulEpochs =
      st.statefulEpochs ∧
    (st.statefulEpochs = true → st.nextEpoch ≤
      ((idealRandomizedSignMachine S pk₀ stateful₀ maxWindow oracleSign).errStep st req).nextEpoch) := by
  unfold idealRandomizedSignMachine
  dsimp only
  cases hA : epochAdmissible st.statefulEpochs maxWindow st.nextEpoch req.epoch with
  | false =>
    exact ⟨rfl, rfl, fun _ => Nat.le_refl _⟩
  | true =>
    refine ⟨rfl, rfl, fun hS => ?_⟩
    rw [hS] at hA
    exact Nat.le_trans (epochAdmissible_stateful hA).1 (Nat.le_succ _)

theorem idealRandomizedSignMachine_trace_epochs_increasing {PK SK Sig : Type}
    {S : RandomizedSigScheme PK SK Sig} {pk₀ : PK} {stateful₀ : Bool} {maxWindow : Nat}
    {oracleSign : RandomizedSignRequest → Option Sig} :
    ∀ {s₀ s_final : RandomizedIdealSignState PK Sig}
      {tr : List (RandomizedSignRequest × Sig)},
      s₀.statefulEpochs = true →
      (idealRandomizedSignMachine S pk₀ stateful₀ maxWindow oracleSign).ValidTrace s₀ tr s_final →
      (∀ p ∈ tr, s₀.nextEpoch ≤ p.1.epoch) ∧ tr.Pairwise (fun a b => a.1.epoch < b.1.epoch)
  | _, _, _, _, .nil _ => ⟨fun _ h => (nomatch h), .nil⟩
  | s₀, _, _, hS, .accept (s' := s') (inp := inp) hStep hRest => by
    obtain ⟨hA, _, _, hEq⟩ := idealRandomizedSignMachine_step_some hStep
    have hNext : s₀.nextEpoch ≤ inp.epoch := by
      rw [hS] at hA
      exact (epochAdmissible_stateful hA).1
    have hS' : s'.statefulEpochs = true := by rw [hEq]; exact hS
    have hN' : s'.nextEpoch = inp.epoch + 1 := by rw [hEq]; rfl
    obtain ⟨ihLo, ihPw⟩ := idealRandomizedSignMachine_trace_epochs_increasing hS' hRest
    rw [hN'] at ihLo
    refine ⟨fun p hp => ?_, .cons (fun p hp => ihLo p hp) ihPw⟩
    rcases List.mem_cons.mp hp with hHead | hTail
    · rw [hHead]; exact hNext
    · exact Nat.le_trans (Nat.le_trans hNext (Nat.le_succ _)) (ihLo p hTail)
  | s₀, _, _, hS, .reject inp _ hRest => by
    obtain ⟨_, hSt, hGe⟩ := idealRandomizedSignMachine_errStep_facts (S := S) (pk₀ := pk₀)
      (stateful₀ := stateful₀) (maxWindow := maxWindow) (oracleSign := oracleSign) s₀ inp
    obtain ⟨ihLo, ihPw⟩ := idealRandomizedSignMachine_trace_epochs_increasing (hSt.trans hS) hRest
    exact ⟨fun p hp => Nat.le_trans (hGe hS) (ihLo p hp), ihPw⟩

/-- **Concrete epoch-latched per-request randomized signer.** -/
def latchedRandomizedSignerMachine {PK SK Sig : Type} (S : RandomizedSigScheme PK SK Sig) (sk : SK)
    (stateful₀ : Bool) (maxWindow : Nat) :
    Machine LatchedSignerState RandomizedSignRequest Sig where
  Init c := c = ⟨0⟩
  step c req :=
    if epochAdmissible stateful₀ maxWindow c.nextEpoch req.epoch = true then
      (S.sign sk req.epoch req.optRand req.message).map (fun sig => (⟨req.epoch + 1⟩, sig))
    else none
  errStep c req :=
    if epochAdmissible stateful₀ maxWindow c.nextEpoch req.epoch = true then ⟨req.epoch + 1⟩
    else c

/-- **Refinement (`latchedRandomizedSignerMachine ⊑ idealRandomizedSignMachine`).**
    Models hedged per-signature randomness `req.optRand` first-class alongside epoch latching. -/
def latchedRandomizedSigner_refines_ideal {PK SK Sig : Type}
    (S : RandomizedSigScheme PK SK Sig) (sk : SK) (stateful₀ : Bool) (maxWindow : Nat) :
    latchedRandomizedSignerMachine S sk stateful₀ maxWindow ⊑
      idealRandomizedSignMachine S (S.derivePk sk) stateful₀ maxWindow
        (fun req => S.sign sk req.epoch req.optRand req.message) where
  Rel c a := a.nextEpoch = c.nextEpoch ∧ a.statefulEpochs = stateful₀ ∧
    a.enrolledPk = S.derivePk sk
  absInit _ := RandomizedIdealSignState.empty (S.derivePk sk) stateful₀
  init_ok {c₀} hInit := by
    have hC : c₀ = ⟨0⟩ := hInit
    rw [hC]
    exact ⟨rfl, rfl, rfl, rfl⟩
  sim_ok {c c' a req sig} hRel hStepC := by
    obtain ⟨hN, hS, hPk⟩ := hRel
    unfold latchedRandomizedSignerMachine at hStepC
    dsimp only at hStepC
    obtain ⟨hA, hMap⟩ := signIteSome hStepC
    obtain ⟨s, hSign, hPair⟩ := signMapSome hMap
    have hs : s = sig := congrArg Prod.snd hPair
    have hc : (⟨req.epoch + 1⟩ : LatchedSignerState) = c' := congrArg Prod.fst hPair
    rw [hs] at hSign
    have hA' : epochAdmissible a.statefulEpochs maxWindow a.nextEpoch req.epoch = true := by
      rw [hS, hN]; exact hA
    have hV : S.verify a.enrolledPk req.message sig = true := by
      rw [hPk]; exact S.correct sk req.epoch req.optRand req.message sig hSign
    rw [idealRandomizedSignMachine_step_of_valid hA' hSign hV]
    exact ⟨rfl, hc ▸ rfl, hS, hPk⟩
  sim_err {c a req} hRel hNoneC := by
    obtain ⟨hN, hS, hPk⟩ := hRel
    unfold latchedRandomizedSignerMachine at hNoneC ⊢
    dsimp only at hNoneC ⊢
    cases hA : epochAdmissible stateful₀ maxWindow c.nextEpoch req.epoch with
    | false =>
      have hA' : epochAdmissible a.statefulEpochs maxWindow a.nextEpoch req.epoch = false := by
        rw [hS, hN]; exact hA
      unfold idealRandomizedSignMachine
      dsimp only
      rw [hA']
      exact ⟨rfl, hN, hS, hPk⟩
    | true =>
      have hA' : epochAdmissible a.statefulEpochs maxWindow a.nextEpoch req.epoch = true := by
        rw [hS, hN]; exact hA
      have hSign : S.sign sk req.epoch req.optRand req.message = none := by
        cases hSg : S.sign sk req.epoch req.optRand req.message with
        | none => rfl
        | some s => simp [hSg, hA] at hNoneC
      unfold idealRandomizedSignMachine verifiedRandomizedCandidate
      dsimp only
      rw [hA', hSign]
      exact ⟨rfl, rfl, hS, hPk⟩

/-- Every initialized trace of the stateful latched randomized signer emits verified signatures at
    strictly increasing epochs, regardless of adversary-chosen per-request `optRand`. -/
theorem latchedRandomizedSigner_trace_safe {PK SK Sig : Type}
    (S : RandomizedSigScheme PK SK Sig) (sk : SK) (maxWindow : Nat)
    {tr : List (RandomizedSignRequest × Sig)}
    (hAdmits : (latchedRandomizedSignerMachine S sk true maxWindow).AdmitsTrace tr) :
    (∀ p ∈ tr, S.verify (S.derivePk sk) p.1.message p.2 = true) ∧
    tr.Pairwise (fun a b => a.1.epoch < b.1.epoch) := by
  have hIdeal := (latchedRandomizedSigner_refines_ideal S sk true maxWindow).preserve_admitsTrace
    hAdmits
  rcases hIdeal with ⟨s₀, s_final, hInit, hTrace⟩
  have hInit' : s₀ = RandomizedIdealSignState.empty (S.derivePk sk) true := hInit
  rw [hInit'] at hTrace
  exact ⟨idealRandomizedSignMachine_trace_outputs_verified hTrace,
    (idealRandomizedSignMachine_trace_epochs_increasing rfl hTrace).2⟩

def acceptAllRandomizedSigScheme : RandomizedSigScheme Unit Unit Unit where
  derivePk _ := ()
  sign _ _ _ _ := some ()
  verify _ _ _ := true
  correct _ _ _ _ _ _ := rfl

def rejectAllRandomizedSigScheme : RandomizedSigScheme Unit Unit Unit where
  derivePk _ := ()
  sign _ _ _ _ := none
  verify _ _ _ := false
  correct _ _ _ _ _ h := nomatch h

theorem idealRandomizedSign_rejects_epoch_one_after_two :
    ¬ (((idealRandomizedSignMachine acceptAllRandomizedSigScheme () true 8 (fun _ => some ())).step
      ((idealRandomizedSignMachine acceptAllRandomizedSigScheme () true 8
        (fun _ => some ())).runStep
        (RandomizedIdealSignState.empty () true) ⟨2, [0xAA], []⟩).1 ⟨1, [0xBB], []⟩).isSome =
        true) := by
  decide

theorem idealRandomizedSign_rejects_unverified_candidate :
    ¬ (((idealRandomizedSignMachine rejectAllRandomizedSigScheme () false 0
        (fun _ => some ())).step
      (RandomizedIdealSignState.empty () false) ⟨0, [0xAA], []⟩).isSome = true) := by
  decide

#tooth_pair idealRandomizedSignMachine_trace_epochs_increasing vs
  idealRandomizedSign_rejects_epoch_one_after_two
#tooth_pair idealRandomizedSignMachine_step_emits_verified vs
  idealRandomizedSign_rejects_unverified_candidate

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
  Qsag.Spec.idealSignMachine_trace_log_complete
  Qsag.Spec.idealSignMachine_trace_log_sound
  Qsag.Spec.idealSignMachine_eufCmaForgery_iff
  Qsag.Spec.idealSignMachine_sufCmaForgery_iff
  Qsag.Spec.idealSignMachine_trace_outputs_not_forgeries
  Qsag.Spec.latchedSigner_output_is_sign
  Qsag.Spec.idealSign_unsigned_message_is_forgery
  Qsag.Spec.signedEvents_map_honest
  Qsag.Spec.emittedEvents_map_honest
  Qsag.Spec.injectedEvents_map_honest
  Qsag.Spec.injectedEvents_cons_inject
  Qsag.Spec.mem_emittedEvents
  Qsag.Spec.idealSignCorruptibleMachine_sign_step_some
  Qsag.Spec.idealSignCorruptibleMachine_sign_step_of_ideal
  Qsag.Spec.idealSignCorruptibleMachine_sign_step_none_iff
  Qsag.Spec.idealSignCorruptibleMachine_sign_errStep
  Qsag.Spec.idealSignCorruptibleMachine_corrupt_step
  Qsag.Spec.idealSignCorruptibleMachine_corrupt_step_some
  Qsag.Spec.idealSignCorruptibleMachine_inject_step_some
  Qsag.Spec.idealSignCorruptibleMachine_inject_step_of_corrupted
  Qsag.Spec.idealSignCorruptibleMachine_inject_step_of_uncorrupted
  Qsag.Spec.idealSignCorruptibleMachine_inject_step_of_unverified
  Qsag.Spec.idealSignCorruptibleMachine_inject_errStep
  Qsag.Spec.idealSignCorruptibleMachine_trace_inner
  Qsag.Spec.idealSignCorruptibleMachine_trace_uncorrupted
  Qsag.Spec.idealSignCorruptibleMachine_trace_corrupted_mono
  Qsag.Spec.idealSignCorruptibleMachine_uncorrupted_trace_only_signs
  Qsag.Spec.idealSignMachine_trace_lifts_corruptible
  Qsag.Spec.idealSignCorruptibleMachine_uncorrupted_trace_is_ideal
  Qsag.Spec.idealSignCorruptibleMachine_admits_honest_iff
  Qsag.Spec.idealSignCorruptibleMachine_trace_key_mode
  Qsag.Spec.idealSignCorruptibleMachine_trace_injectedLog
  Qsag.Spec.idealSignCorruptibleMachine_trace_injected_verified
  Qsag.Spec.idealSignCorruptibleMachine_trace_emitted_verified
  Qsag.Spec.idealSignCorruptibleMachine_uncorrupted_trace_safe
  Qsag.Spec.CorruptibleEufCmaForgery.toSufCma
  Qsag.Spec.idealSignCorruptibleMachine_eufCmaForgery_iff
  Qsag.Spec.idealSignCorruptibleMachine_sufCmaForgery_iff
  Qsag.Spec.idealSignCorruptibleMachine_uncorrupted_eufCmaForgery_iff
  Qsag.Spec.idealSignCorruptibleMachine_trace_emitted_not_forgeries
  Qsag.Spec.idealSignCorruptibleMachine_corrupted_absorbs_forgery
  Qsag.Spec.idealSignCorruptibleMachine_corrupted_run_absorbs_forgery
  Qsag.Spec.idealSignCorruptible_rejects_inject_before_corrupt
  Qsag.Spec.idealSignCorruptible_rejects_unverified_inject_after_corrupt
  Qsag.Spec.idealSignCorruptible_epoch_reuse_run
  Qsag.Spec.idealSignCorruptible_corrupted_run_reuses_epoch
  Qsag.Spec.idealSignCorruptible_honest_run_epochs_increase
  Qsag.Spec.verifiedRandomizedCandidate_some
  Qsag.Spec.verifiedRandomizedCandidate_of_valid
  Qsag.Spec.idealRandomizedSignMachine_step_some
  Qsag.Spec.idealRandomizedSignMachine_step_emits_verified
  Qsag.Spec.idealRandomizedSignMachine_step_of_valid
  Qsag.Spec.idealRandomizedSignMachine_trace_outputs_verified
  Qsag.Spec.idealRandomizedSignMachine_trace_epochs_increasing
  Qsag.Spec.latchedRandomizedSigner_trace_safe
  Qsag.Spec.idealRandomizedSign_rejects_epoch_one_after_two
  Qsag.Spec.idealRandomizedSign_rejects_unverified_candidate

end Qsag.Spec
end

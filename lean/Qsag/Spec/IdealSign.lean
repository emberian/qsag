module
/-
# Qsag.Spec.IdealSign — Ideal Standalone and Epoch-Stateful Signing Specification

Clean, self-contained Layer-0 ideal specification for standalone and one-time-epoch-stateful
digital signatures:
1. Canonical `SigScheme` interface (`verify`, `sign`),
2. Reactive `IdealSignMachine` tracking monotonic / non-reused signing epochs and approved
   `(epoch, message, signature)` log entries,
3. Existential (`EufCmaForgery`) and strong (`SufCmaForgery`) unforgeability predicates, and
4. Proof that `IdealSignMachine` maintains strict epoch uniqueness across all multi-turn traces.
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

/-- Signing request specifying target epoch, message bytes, and whether stateful epoch tracking applies. -/
structure SignRequest where
  epoch : Nat
  message : Bytes
  deriving DecidableEq, Repr

/-- Persistent state of the ideal signing functionality. -/
structure IdealSignState (PK Sig : Type) where
  enrolledPk : PK
  statefulEpochs : Bool
  usedEpochs : List Nat
  signedLog : List (Nat × Bytes × Sig)

/-- Canonical initial state of `IdealSignState` with empty epoch and signature logs. -/
@[expose] def IdealSignState.empty {PK Sig : Type} (pk : PK) (stateful : Bool) :
    IdealSignState PK Sig :=
  { enrolledPk := pk
    statefulEpochs := stateful
    usedEpochs := []
    signedLog := [] }

/-- Reactive ideal signing machine: in stateful mode, rejects any duplicate `req.epoch ∈ usedEpochs`
    without mutating state; on fresh epochs, emits `oracleSign req` and records `(epoch, msg, sig)`. -/
@[expose] def idealSignMachine {PK Sig : Type}
    (pk₀ : PK) (stateful₀ : Bool) (oracleSign : SignRequest → Option Sig) :
    Machine (IdealSignState PK Sig) SignRequest Sig where
  Init st := st = IdealSignState.empty pk₀ stateful₀
  step st req :=
    if st.statefulEpochs && decide (req.epoch ∈ st.usedEpochs) then
      none
    else
      match oracleSign req with
      | none => none
      | some sig =>
        some ({ st with
                usedEpochs := req.epoch :: st.usedEpochs
                signedLog := (req.epoch, req.message, sig) :: st.signedLog },
              sig)
  errStep st _ := st

/-- State invariant: in stateful mode, `usedEpochs` has no duplicates (`Nodup`) and matches
    the first projection of `signedLog`. -/
def IdealSignState.Inv {PK Sig : Type} (st : IdealSignState PK Sig) : Prop :=
  st.usedEpochs = st.signedLog.map (fun e => e.1) ∧
  (st.statefulEpochs = true → st.usedEpochs.Nodup)

theorem IdealSignState.empty_inv {PK Sig : Type} (pk : PK) (stateful : Bool) :
    (IdealSignState.empty pk stateful : IdealSignState PK Sig).Inv :=
  ⟨rfl, fun _ => .nil⟩

theorem idealSignMachine_step_preserves_inv {PK Sig : Type}
    {pk₀ : PK} {stateful₀ : Bool} {oracleSign : SignRequest → Option Sig}
    {st st' : IdealSignState PK Sig} {req : SignRequest} {sig : Sig}
    (hInv : st.Inv)
    (hStep : (idealSignMachine pk₀ stateful₀ oracleSign).step st req = some (st', sig)) :
    st'.Inv := by
  unfold idealSignMachine at hStep
  dsimp only at hStep
  by_cases hDup : (st.statefulEpochs && decide (req.epoch ∈ st.usedEpochs)) = true
  · simp only [hDup, ↓reduceIte] at hStep
    cases hStep
  · simp only [hDup] at hStep
    cases hOr : oracleSign req with
    | none =>
      rw [hOr] at hStep
      cases hStep
    | some s =>
      rw [hOr] at hStep
      injection hStep with hPair
      injection hPair with hSt _
      subst hSt
      rcases hInv with ⟨hMapEq, hNd⟩
      refine ⟨congrArg (req.epoch :: ·) hMapEq, ?_⟩
      intro hStf
      have hNotMem : req.epoch ∉ st.usedEpochs := by
        intro hMem
        apply hDup
        rw [hStf, Bool.true_and]
        exact decide_eq_true hMem
      exact .cons (fun x hx hEq => hNotMem (hEq ▸ hx)) (hNd hStf)

theorem idealSignMachine_trace_preserves_inv {PK Sig : Type}
    {pk₀ : PK} {stateful₀ : Bool} {oracleSign : SignRequest → Option Sig} :
    ∀ {s₀ s_final : IdealSignState PK Sig} {tr : List (SignRequest × Sig)},
      s₀.Inv →
      (idealSignMachine pk₀ stateful₀ oracleSign).ValidTrace s₀ tr s_final →
      s_final.Inv
  | _, _, _, hInv, .nil _ => hInv
  | _, _, _, hInv, .accept hStep hRest =>
    idealSignMachine_trace_preserves_inv
      (idealSignMachine_step_preserves_inv hInv hStep) hRest
  | _, _, _, hInv, .reject _ _ hRest =>
    idealSignMachine_trace_preserves_inv hInv hRest

/-- Every reachable state of `idealSignMachine` satisfies one-time epoch uniqueness in stateful mode! -/
theorem idealSignMachine_reachable_inv {PK Sig : Type}
    (pk₀ : PK) (stateful₀ : Bool) (oracleSign : SignRequest → Option Sig)
    {st : IdealSignState PK Sig}
    (hReach : (idealSignMachine pk₀ stateful₀ oracleSign).Reachable st) :
    st.Inv := by
  rcases hReach with ⟨s₀, tr, hInit, hTrace⟩
  rw [hInit] at hTrace
  exact idealSignMachine_trace_preserves_inv (IdealSignState.empty_inv pk₀ stateful₀) hTrace

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
  Qsag.Spec.IdealSignState.empty_inv
  Qsag.Spec.idealSignMachine_step_preserves_inv
  Qsag.Spec.idealSignMachine_trace_preserves_inv
  Qsag.Spec.idealSignMachine_reachable_inv
  Qsag.Spec.EufCmaForgery.toSufCma

end Qsag.Spec
end

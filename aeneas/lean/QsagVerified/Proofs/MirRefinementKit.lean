module
import all QsagVerified.Funs

public import Aeneas

/-!
# QsagVerified.Proofs.MirRefinementKit — Compositional MIR-to-Spec Refinement & Lifting Kit

Foundational `0 Classical.choice` single-step-to-multi-turn refinement framework for
Charon + Aeneas extracted Rust MIR protocol state machines:
1. **Partial Mealy Specifications & Valid Trace Engine (`MealySpec`, `ValidSpecTrace`, `MealySpec.ValidTrace`)**:
   Supports both pure partial transitions (`step : S → I → Option (S × O)`) and error-mutating
   quarantine/burn transitions (`errStep : S → I → S`), retaining both accepted `(i, o)` pairs
   and rejected invalid input transitions.
2. **Constructive Single-Step MIR Simulation (`MirOutcome`, `MirStepSim`)**:
   Supports all Aeneas return conventions (`Result (core.result.Result (M × O) E)`,
   `Result (M × core.result.Result O E)`, `&mut` `Result (core.result.Result O E × M)`,
   `Result (Option (M × O))`, `Result (M × Option O)`, `Result (M × Bool)`, `Result (M × O)`)
   via deterministic `Option` matching with **zero `Classical.choice`**.
3. **Turnkey Multi-Turn Lifting & Phased Composition (`lift_state_invariant`, `lift_trace_safety`, `MirStepSim.compose`, `MirPhaseSim`)**:
   Proves multi-turn trace induction once so protocol guard proofs only discharge 1-step obligations.
4. **Constructive Aeneas Data-Refinement Helpers**:
   `u64_val_add_checked`, `u64_val_sub_checked`, `u8_eq_iff`, `u64_eq_iff`,
   `array32_to_list_injective`, `arrayU8ToBytes_injective`, `result_bind_ok_split`.
-/

public section

namespace qsag_verified.proofs

open Aeneas Aeneas.Std Result ControlFlow Error

/-! ## 1. Generic Partial Mealy Spec & Multi-Turn Valid Trace Engine -/

/-- Pure specification state machine with optional quarantine/burn error state transition.
    When `errStep` is omitted, rejected inputs leave state `s` unchanged (`fun s _ => s`). -/
structure MealySpec (S I O : Type) where
  step : S → I → Option (S × O)
  errStep : S → I → S := fun s _ => s

/-- Construct a `MealySpec` from a pure partial transition `S → I → Option (S × O)`
    whose rejected inputs leave the state unchanged. -/
@[expose]
def MealySpec.ofPure {S I O : Type} (step : S → I → Option (S × O)) : MealySpec S I O :=
  { step := step, errStep := fun s _ => s }

/-- Observable spec-level turn outcome (recording both accepted I/O and rejected inputs). -/
inductive SpecTurn (I O : Type) where
  | accepted (input : I) (output : O)
  | rejected (input : I)
  deriving Repr, DecidableEq

/-- Project accepted `(input, output)` pairs from a full `SpecTurn` history. -/
@[expose]
def specAcceptedPairs {I O : Type} : List (SpecTurn I O) → List (I × O)
  | [] => []
  | .accepted i o :: rest => (i, o) :: specAcceptedPairs rest
  | .rejected _ :: rest => specAcceptedPairs rest

/-- Inductive multi-turn valid trace relation over a pure partial transition
    `step : S → I → Option (S × O)` with explicit error-refusal branch (`step s i = none`). -/
inductive ValidSpecTrace {S I O : Type} (step : S → I → Option (S × O)) :
    S → List (I × O) → S → Prop where
  | nil (s : S) : ValidSpecTrace step s [] s
  | accept {s s' s_final : S} {i : I} {o : O} {rest : List (I × O)} :
      step s i = some (s', o) →
      ValidSpecTrace step s' rest s_final →
      ValidSpecTrace step s ((i, o) :: rest) s_final
  | reject {s s_final : S} (i : I) {rest : List (I × O)} :
      step s i = none →
      ValidSpecTrace step s rest s_final →
      ValidSpecTrace step s rest s_final

/-- Inductive multi-turn valid trace relation for a `MealySpec` (supporting stateful
    quarantine/poison/nonce-burn transitions via `spec.errStep` when `spec.step s i = none`). -/
inductive MealySpec.ValidTrace {S I O : Type} (spec : MealySpec S I O) :
    S → List (I × O) → S → Prop where
  | nil (s : S) : spec.ValidTrace s [] s
  | accept {s s' s_final : S} {i : I} {o : O} {rest : List (I × O)} :
      spec.step s i = some (s', o) →
      spec.ValidTrace s' rest s_final →
      spec.ValidTrace s ((i, o) :: rest) s_final
  | reject {s s_final : S} (i : I) {rest : List (I × O)} :
      spec.step s i = none →
      spec.ValidTrace (spec.errStep s i) rest s_final →
      spec.ValidTrace s rest s_final

/-- For pure specs (`errStep = fun s _ => s`), `MealySpec.ValidTrace` coincides with `ValidSpecTrace`. -/
theorem MealySpec.validTrace_ofPure_iff {S I O : Type}
    (step : S → I → Option (S × O)) (s₀ : S) (trace : List (I × O)) (s_final : S) :
    (MealySpec.ofPure step).ValidTrace s₀ trace s_final ↔
      ValidSpecTrace step s₀ trace s_final := by
  constructor
  · intro h
    induction h with
    | nil s => exact .nil s
    | accept hStep _ ih => exact .accept hStep ih
    | reject i hNone _ ih => exact .reject i hNone ih
  · intro h
    induction h with
    | nil s => exact .nil s
    | accept hStep _ ih => exact .accept hStep ih
    | reject i hNone _ ih => exact .reject i hNone ih

/-- Deterministic multi-turn spec runner (`0 Classical.choice` witness generator). -/
@[expose]
def MealySpec.runInputs {S I O : Type} (spec : MealySpec S I O) :
    S → List I → List (I × O) × S
  | s, [] => ([], s)
  | s, i :: rest =>
    match spec.step s i with
    | some (s', o) =>
      let res := spec.runInputs s' rest
      ((i, o) :: res.1, res.2)
    | none =>
      spec.runInputs (spec.errStep s i) rest

theorem MealySpec.runInputs_validTrace {S I O : Type} (spec : MealySpec S I O) :
    ∀ (s₀ : S) (inputs : List I),
      spec.ValidTrace s₀ (spec.runInputs s₀ inputs).1 (spec.runInputs s₀ inputs).2
  | s, [] => .nil s
  | s, i :: rest => by
    dsimp only [MealySpec.runInputs]
    cases hStep : spec.step s i with
    | some pair =>
      exact .accept hStep (spec.runInputs_validTrace pair.1 rest)
    | none =>
      exact .reject i hStep (spec.runInputs_validTrace (spec.errStep s i) rest)

/-- Pure state-invariant induction on `ValidSpecTrace`. -/
theorem ValidSpecTrace.preserve_invariant {S I O : Type}
    {step : S → I → Option (S × O)} {P : S → Prop}
    (hPres : ∀ {s s' : S} {i : I} {o : O}, P s → step s i = some (s', o) → P s')
    {s₀ s_final : S} {trace : List (I × O)}
    (hInit : P s₀) (hTrace : ValidSpecTrace step s₀ trace s_final) :
    P s_final := by
  induction hTrace with
  | nil _ => exact hInit
  | accept hStep _ ih => exact ih (hPres hInit hStep)
  | reject _ _ _ ih => exact ih hInit

/-- Stateful state-invariant induction on `MealySpec.ValidTrace` (covering `errStep`). -/
theorem MealySpec.ValidTrace.preserve_invariant {S I O : Type}
    {spec : MealySpec S I O} {P : S → Prop}
    (hOk : ∀ {s s' : S} {i : I} {o : O}, P s → spec.step s i = some (s', o) → P s')
    (hErr : ∀ {s : S} {i : I}, P s → spec.step s i = none → P (spec.errStep s i))
    {s₀ s_final : S} {trace : List (I × O)}
    (hInit : P s₀) (hTrace : spec.ValidTrace s₀ trace s_final) :
    P s_final := by
  induction hTrace with
  | nil _ => exact hInit
  | accept hStep _ ih => exact ih (hOk hInit hStep)
  | reject _ hNone _ ih => exact ih (hErr hInit hNone)

/-! ## 2. Normalized MIR Step Outcome & Zero-Boilerplate Aeneas Return Adapters -/

/-- Canonical outcome of one Aeneas-extracted MIR transition:
    either `.accepted m' o_m` or `.rejected m' e` (tracking mutated `m'` on quarantine/burn
    or retaining `m' = m` on immutable error return). -/
inductive MirOutcome (M O E : Type) where
  | accepted (nextState : M) (output : O)
  | rejected (nextState : M) (err : E)
  deriving Repr, DecidableEq

/-- Adapter 1: `fn step(self, i) -> core::result::Result<(Self, O), E>` (e.g. `EpochLatch`).
    On `Err(e)`, callers retain prior state `m`. -/
@[expose]
def adaptResultPair {M I O E : Type}
    (f : M → I → Result (core.result.Result (M × O) E)) (m : M) (i : I) :
    Result (MirOutcome M O E) :=
  Result.bind (f m i) fun res =>
    match res with
    | .Ok (m', o) => .ok (.accepted m' o)
    | .Err e => .ok (.rejected m e)

/-- Adapter 2: `fn step(self, i) -> (Self, core::result::Result<O, E>)` (explicit state + result). -/
@[expose]
def adaptStateResult {M I O E : Type}
    (f : M → I → Result (M × core.result.Result O E)) (m : M) (i : I) :
    Result (MirOutcome M O E) :=
  Result.bind (f m i) fun (m', res) =>
    match res with
    | .Ok o => .ok (.accepted m' o)
    | .Err e => .ok (.rejected m' e)

/-- Adapter 3: `fn step(&mut self, i) -> core::result::Result<O, E>` (Aeneas `&mut` extraction
    returns `(core.result.Result O E × Self)`, mutating `self` even on `.Err e`). -/
@[expose]
def adaptMutResult {M I O E : Type}
    (f : M → I → Result (core.result.Result O E × M)) (m : M) (i : I) :
    Result (MirOutcome M O E) :=
  Result.bind (f m i) fun (res, m') =>
    match res with
    | .Ok o => .ok (.accepted m' o)
    | .Err e => .ok (.rejected m' e)

/-- Adapter 4: `fn step(self, i) -> Option<(Self, O)>` (immutable refusal on `none`). -/
@[expose]
def adaptOptionPair {M I O : Type}
    (f : M → I → Result (Option (M × O))) (m : M) (i : I) :
    Result (MirOutcome M O Unit) :=
  Result.bind (f m i) fun res =>
    match res with
    | some (m', o) => .ok (.accepted m' o)
    | none => .ok (.rejected m ())

/-- Adapter 5: `fn step(self, i) -> (Self, Option<O>)` or `&mut self -> Option<O>` flipped
    (quarantine/burn state mutation on `none`). -/
@[expose]
def adaptStateOption {M I O : Type}
    (f : M → I → Result (M × Option O)) (m : M) (i : I) :
    Result (MirOutcome M O Unit) :=
  Result.bind (f m i) fun (m', res) =>
    match res with
    | some o => .ok (.accepted m' o)
    | none => .ok (.rejected m' ())

/-- Adapter 6: `fn step(self, i) -> (Self, bool)` (e.g. `verify_mac_2lane_with_burn`). -/
@[expose]
def adaptStateBool {M I : Type}
    (f : M → I → Result (M × Bool)) (m : M) (i : I) :
    Result (MirOutcome M Unit Unit) :=
  Result.bind (f m i) fun (m', okFlag) =>
    if okFlag then .ok (.accepted m' ()) else .ok (.rejected m' ())

/-- Adapter 7: Infallible state-output tuple `fn step(self, i) -> (Self, O)`. -/
@[expose]
def adaptTuple {M I O : Type}
    (f : M → I → Result (M × O)) (m : M) (i : I) :
    Result (MirOutcome M O Empty) :=
  Result.bind (f m i) fun (m', o) => .ok (.accepted m' o)

/-! ## 3. `MirStepSim` — Constructive Single-Step MIR-to-MealySpec Refinement (`0 Classical.choice`) -/

/-- Single-step relational refinement from an Aeneas MIR step function `mirStep` to `spec : MealySpec`.
    Uses deterministic `match spec.step s i_s` rather than `Exists` so lifting requires
    **zero `Classical.choice`**. -/
structure MirStepSim {S M I_s I_m O_s O_m E : Type}
    (spec : MealySpec S I_s O_s)
    (mirStep : M → I_m → Result (MirOutcome M O_m E))
    (RelSt : S → M → Prop)
    (RelIn : I_s → I_m → Prop)
    (RelOut : O_s → O_m → Prop) : Prop where
  ok_sim : ∀ {s : S} {m m' : M} {i_s : I_s} {i_m : I_m} {o_m : O_m},
    RelSt s m →
    RelIn i_s i_m →
    mirStep m i_m = .ok (.accepted m' o_m) →
    match spec.step s i_s with
    | none => False
    | some (s', o_s) => RelSt s' m' ∧ RelOut o_s o_m
  err_preserves : ∀ {s : S} {m m' : M} {i_s : I_s} {i_m : I_m} {e : E},
    RelSt s m →
    RelIn i_s i_m →
    mirStep m i_m = .ok (.rejected m' e) →
    spec.step s i_s = none ∧ RelSt (spec.errStep s i_s) m'

/-- Smart constructor for `Result (core.result.Result (M × O_m) E)` against pure `step`:
    since `m` is unchanged on `.Err e`, `RelSt s m` is preserved automatically! -/
theorem MirStepSim.ofResultPair {S M I_s I_m O_s O_m E : Type}
    (step : S → I_s → Option (S × O_s))
    (f : M → I_m → Result (core.result.Result (M × O_m) E))
    (RelSt : S → M → Prop)
    (RelIn : I_s → I_m → Prop)
    (RelOut : O_s → O_m → Prop)
    (hOk : ∀ {s m m' i_s i_m o_m},
      RelSt s m → RelIn i_s i_m → f m i_m = .ok (.Ok (m', o_m)) →
      match step s i_s with
      | none => False
      | some (s', o_s) => RelSt s' m' ∧ RelOut o_s o_m)
    (hErr : ∀ {s m i_s i_m e},
      RelSt s m → RelIn i_s i_m → f m i_m = .ok (.Err e) →
      step s i_s = none) :
    MirStepSim (MealySpec.ofPure step) (adaptResultPair f) RelSt RelIn RelOut where
  ok_sim {s m m' i_s i_m o_m} hSt hIn hStep := by
    dsimp only [adaptResultPair, MealySpec.ofPure] at hStep ⊢
    cases hf : f m i_m with
    | fail err => simp [hf, Result.bind] at hStep
    | div => simp [hf, Result.bind] at hStep
    | ok r =>
      simp only [hf, Result.bind] at hStep
      cases r with
      | Ok pair =>
        injection hStep with hOut
        cases hOut
        exact hOk hSt hIn hf
      | Err e => cases hStep
  err_preserves {s m m' i_s i_m e} hSt hIn hStep := by
    dsimp only [adaptResultPair, MealySpec.ofPure] at hStep ⊢
    cases hf : f m i_m with
    | fail err => simp [hf, Result.bind] at hStep
    | div => simp [hf, Result.bind] at hStep
    | ok r =>
      simp only [hf, Result.bind] at hStep
      cases r with
      | Ok pair => cases hStep
      | Err errVal =>
        injection hStep with hRej
        cases hRej
        exact ⟨hErr hSt hIn hf, hSt⟩

/-- Smart constructor for `&mut self` returning `Result (core.result.Result O_m E × M)`
    where failed attempts may quarantine/poison `m'` tracked by `spec.errStep`. -/
theorem MirStepSim.ofMutResult {S M I_s I_m O_s O_m E : Type}
    (spec : MealySpec S I_s O_s)
    (f : M → I_m → Result (core.result.Result O_m E × M))
    (RelSt : S → M → Prop)
    (RelIn : I_s → I_m → Prop)
    (RelOut : O_s → O_m → Prop)
    (hOk : ∀ {s m m' i_s i_m o_m},
      RelSt s m → RelIn i_s i_m → f m i_m = .ok (.Ok o_m, m') →
      match spec.step s i_s with
      | none => False
      | some (s', o_s) => RelSt s' m' ∧ RelOut o_s o_m)
    (hErr : ∀ {s m m' i_s i_m e},
      RelSt s m → RelIn i_s i_m → f m i_m = .ok (.Err e, m') →
      spec.step s i_s = none ∧ RelSt (spec.errStep s i_s) m') :
    MirStepSim spec (adaptMutResult f) RelSt RelIn RelOut where
  ok_sim {s m m' i_s i_m o_m} hSt hIn hStep := by
    dsimp only [adaptMutResult] at hStep
    cases hf : f m i_m with
    | fail err => simp [hf, Result.bind] at hStep
    | div => simp [hf, Result.bind] at hStep
    | ok pair =>
      rcases pair with ⟨res, m1⟩
      simp only [hf, Result.bind] at hStep
      cases res with
      | Ok o =>
        injection hStep with hAcc
        cases hAcc
        exact hOk hSt hIn hf
      | Err e => cases hStep
  err_preserves {s m m' i_s i_m e} hSt hIn hStep := by
    dsimp only [adaptMutResult] at hStep
    cases hf : f m i_m with
    | fail err => simp [hf, Result.bind] at hStep
    | div => simp [hf, Result.bind] at hStep
    | ok pair =>
      rcases pair with ⟨res, m1⟩
      simp only [hf, Result.bind] at hStep
      cases res with
      | Ok o => cases hStep
      | Err errVal =>
        injection hStep with hRej
        cases hRej
        exact hErr hSt hIn hf

/-- Smart constructor for `Result (Option (M × O_m))` against pure `step`. -/
theorem MirStepSim.ofOptionPair {S M I_s I_m O_s O_m : Type}
    (step : S → I_s → Option (S × O_s))
    (f : M → I_m → Result (Option (M × O_m)))
    (RelSt : S → M → Prop)
    (RelIn : I_s → I_m → Prop)
    (RelOut : O_s → O_m → Prop)
    (hSome : ∀ {s m m' i_s i_m o_m},
      RelSt s m → RelIn i_s i_m → f m i_m = .ok (some (m', o_m)) →
      match step s i_s with
      | none => False
      | some (s', o_s) => RelSt s' m' ∧ RelOut o_s o_m)
    (hNone : ∀ {s m i_s i_m},
      RelSt s m → RelIn i_s i_m → f m i_m = .ok none →
      step s i_s = none) :
    MirStepSim (MealySpec.ofPure step) (adaptOptionPair f) RelSt RelIn RelOut where
  ok_sim {s m m' i_s i_m o_m} hSt hIn hStep := by
    dsimp only [adaptOptionPair, MealySpec.ofPure] at hStep ⊢
    cases hf : f m i_m with
    | fail err => simp [hf, Result.bind] at hStep
    | div => simp [hf, Result.bind] at hStep
    | ok opt =>
      simp only [hf, Result.bind] at hStep
      cases opt with
      | some pair =>
        injection hStep with hAcc
        cases hAcc
        exact hSome hSt hIn hf
      | none => cases hStep
  err_preserves {s m m' i_s i_m _} hSt hIn hStep := by
    dsimp only [adaptOptionPair, MealySpec.ofPure] at hStep ⊢
    cases hf : f m i_m with
    | fail err => simp [hf, Result.bind] at hStep
    | div => simp [hf, Result.bind] at hStep
    | ok opt =>
      simp only [hf, Result.bind] at hStep
      cases opt with
      | some pair => cases hStep
      | none =>
        injection hStep with hRej
        cases hRej
        exact ⟨hNone hSt hIn hf, hSt⟩

/-- Smart constructor for infallible `Result (M × O_m)` tuple transitions. -/
theorem MirStepSim.ofTuple {S M I_s I_m O_s O_m : Type}
    (step : S → I_s → Option (S × O_s))
    (f : M → I_m → Result (M × O_m))
    (RelSt : S → M → Prop)
    (RelIn : I_s → I_m → Prop)
    (RelOut : O_s → O_m → Prop)
    (hOk : ∀ {s m m' i_s i_m o_m},
      RelSt s m → RelIn i_s i_m → f m i_m = .ok (m', o_m) →
      match step s i_s with
      | none => False
      | some (s', o_s) => RelSt s' m' ∧ RelOut o_s o_m) :
    MirStepSim (MealySpec.ofPure step) (adaptTuple f) RelSt RelIn RelOut where
  ok_sim {s m m' i_s i_m o_m} hSt hIn hStep := by
    dsimp only [adaptTuple, MealySpec.ofPure] at hStep ⊢
    cases hf : f m i_m with
    | fail err => simp [hf, Result.bind] at hStep
    | div => simp [hf, Result.bind] at hStep
    | ok pair =>
      simp only [hf, Result.bind] at hStep
      injection hStep with hAcc
      cases hAcc
      exact hOk hSt hIn hf
  err_preserves {_ _ _ _ _ e} _ _ _ := Empty.elim e

/-! ## 4. Multi-Turn MIR Trace & Turnkey Lifting Theorems -/

/-- Observable MIR-level turn (recording input and either accepted output or rejection error). -/
inductive MirTurn (I_m O_m E : Type) where
  | accepted (input : I_m) (output : O_m)
  | rejected (input : I_m) (err : E)
  deriving Repr, DecidableEq

/-- Extract the input of any `MirTurn`. -/
def MirTurn.input {I_m O_m E : Type} : MirTurn I_m O_m E → I_m
  | .accepted i _ => i
  | .rejected i _ => i

/-- Project accepted `(input, output)` pairs from a multi-turn `MirTurn` trace. -/
@[expose]
def mirAcceptedPairs {I_m O_m E : Type} : List (MirTurn I_m O_m E) → List (I_m × O_m)
  | [] => []
  | .accepted i o :: rest => (i, o) :: mirAcceptedPairs rest
  | .rejected _ _ :: rest => mirAcceptedPairs rest

/-- Multi-turn executable MIR trace over `mirStep : M → I_m → Result (MirOutcome M O_m E)`. -/
inductive MirTrace {M I_m O_m E : Type}
    (mirStep : M → I_m → Result (MirOutcome M O_m E)) :
    M → List (MirTurn I_m O_m E) → M → Prop where
  | nil (m : M) : MirTrace mirStep m [] m
  | accept {m m' m_final : M} {i_m : I_m} {o_m : O_m} {rest : List (MirTurn I_m O_m E)} :
      mirStep m i_m = .ok (.accepted m' o_m) →
      MirTrace mirStep m' rest m_final →
      MirTrace mirStep m (.accepted i_m o_m :: rest) m_final
  | reject {m m' m_final : M} {i_m : I_m} {e : E} {rest : List (MirTurn I_m O_m E)} :
      mirStep m i_m = .ok (.rejected m' e) →
      MirTrace mirStep m' rest m_final →
      MirTrace mirStep m (.rejected i_m e :: rest) m_final

/-- Constructive pointwise relation between spec inputs and MIR turns (`0 Classical.choice`). -/
inductive InputsMatchTurns {I_s I_m O_m E : Type} (RelIn : I_s → I_m → Prop) :
    List I_s → List (MirTurn I_m O_m E) → Prop where
  | nil : InputsMatchTurns RelIn [] []
  | cons {i_s : I_s} {t_m : MirTurn I_m O_m E} {is_rest : List I_s} {ts_rest : List (MirTurn I_m O_m E)} :
      RelIn i_s t_m.input →
      InputsMatchTurns RelIn is_rest ts_rest →
      InputsMatchTurns RelIn (i_s :: is_rest) (t_m :: ts_rest)

/-- Constructive pointwise I/O relation between accepted spec pairs and accepted MIR pairs. -/
inductive AcceptedPairsRel {I_s I_m O_s O_m : Type}
    (RelIn : I_s → I_m → Prop) (RelOut : O_s → O_m → Prop) :
    List (I_s × O_s) → List (I_m × O_m) → Prop where
  | nil : AcceptedPairsRel RelIn RelOut [] []
  | cons {i_s : I_s} {i_m : I_m} {o_s : O_s} {o_m : O_m}
      {rest_s : List (I_s × O_s)} {rest_m : List (I_m × O_m)} :
      RelIn i_s i_m →
      RelOut o_s o_m →
      AcceptedPairsRel RelIn RelOut rest_s rest_m →
      AcceptedPairsRel RelIn RelOut ((i_s, o_s) :: rest_s) ((i_m, o_m) :: rest_m)

/-- Master constructive multi-turn simulation theorem: replays `spec.runInputs s₀ inputs_s`
    in lockstep with any `N`-turn `MirTrace`, establishing `ValidTrace`, `AcceptedPairsRel`,
    and final `RelSt` with **zero `Classical.choice`**. -/
theorem MirStepSim.lift_runInputs {S M I_s I_m O_s O_m E : Type}
    {spec : MealySpec S I_s O_s}
    {mirStep : M → I_m → Result (MirOutcome M O_m E)}
    {RelSt : S → M → Prop} {RelIn : I_s → I_m → Prop} {RelOut : O_s → O_m → Prop}
    (sim : MirStepSim spec mirStep RelSt RelIn RelOut) :
    ∀ {s₀ : S} {m₀ m_final : M} {inputs_s : List I_s} {turns_m : List (MirTurn I_m O_m E)},
      RelSt s₀ m₀ →
      MirTrace mirStep m₀ turns_m m_final →
      InputsMatchTurns RelIn inputs_s turns_m →
      let out := spec.runInputs s₀ inputs_s
      spec.ValidTrace s₀ out.1 out.2 ∧
      RelSt out.2 m_final ∧
      AcceptedPairsRel RelIn RelOut out.1 (mirAcceptedPairs turns_m)
  | s₀, _, _, _, _, hRel, .nil _, .nil =>
    ⟨.nil s₀, hRel, .nil⟩
  | s₀, _, _, i_s :: is_rest, _, hRel, .accept hStepM hTailM, .cons hIn hTailIn => by
    dsimp only [MirTurn.input] at hIn
    have hSim := sim.ok_sim hRel hIn hStepM
    dsimp only [MealySpec.runInputs]
    cases hStepS : spec.step s₀ i_s with
    | none =>
      rw [hStepS] at hSim
      exact False.elim hSim
    | some pair =>
      rw [hStepS] at hSim
      rcases pair with ⟨s₁, o_s⟩
      obtain ⟨hRel₁, hOut⟩ := hSim
      obtain ⟨hValTail, hRelFinal, hPairsTail⟩ :=
        sim.lift_runInputs hRel₁ hTailM hTailIn
      exact ⟨.accept hStepS hValTail, hRelFinal, .cons hIn hOut hPairsTail⟩
  | s₀, _, _, i_s :: is_rest, _, hRel, .reject hStepM hTailM, .cons hIn hTailIn => by
    dsimp only [MirTurn.input] at hIn
    obtain ⟨hNone, hRel₁⟩ := sim.err_preserves hRel hIn hStepM
    dsimp only [MealySpec.runInputs, mirAcceptedPairs]
    rw [hNone]
    obtain ⟨hValTail, hRelFinal, hPairsTail⟩ :=
      sim.lift_runInputs hRel₁ hTailM hTailIn
    exact ⟨.reject i_s hNone hValTail, hRelFinal, hPairsTail⟩

/-- **Turnkey Multi-Turn State-Invariant Lifter (`MirStepSim.lift_state_invariant`)**:
    Any inductive state invariant `P : S → Prop` preserved by `spec.step` and `spec.errStep`
    automatically holds on the corresponding spec witness of every reachable `m_final`
    across arbitrary `N`-turn `MirTrace`s (`0 Classical.choice`). -/
theorem MirStepSim.lift_state_invariant {S M I_s I_m O_s O_m E : Type}
    {spec : MealySpec S I_s O_s}
    {mirStep : M → I_m → Result (MirOutcome M O_m E)}
    {RelSt : S → M → Prop} {RelIn : I_s → I_m → Prop} {RelOut : O_s → O_m → Prop}
    (sim : MirStepSim spec mirStep RelSt RelIn RelOut)
    {P : S → Prop}
    (hOk : ∀ {s s' : S} {i : I_s} {o : O_s}, P s → spec.step s i = some (s', o) → P s')
    (hErr : ∀ {s : S} {i : I_s}, P s → spec.step s i = none → P (spec.errStep s i))
    {s₀ : S} {m₀ m_final : M} {inputs_s : List I_s} {turns_m : List (MirTurn I_m O_m E)}
    (hInitP : P s₀) (hInitRel : RelSt s₀ m₀)
    (hMir : MirTrace mirStep m₀ turns_m m_final)
    (hInputs : InputsMatchTurns RelIn inputs_s turns_m) :
    let s_final := (spec.runInputs s₀ inputs_s).2
    P s_final ∧ RelSt s_final m_final := by
  obtain ⟨hVal, hRelFinal, _⟩ := sim.lift_runInputs hInitRel hMir hInputs
  exact ⟨hVal.preserve_invariant hOk hErr hInitP, hRelFinal⟩

/-- **Turnkey Multi-Turn Trace-Safety Lifter (`MirStepSim.lift_trace_safety`)**:
    Any trace safety property `Safe : List (I_s × O_s) → Prop` (monotonicity, `atMostOnePerEpoch`,
    `sumApproved ≤ cap`, `releasedImpliesVerified`) proved on `spec.ValidTrace` automatically
    transfers to arbitrary-length multi-turn executions of `mirStep`! -/
theorem MirStepSim.lift_trace_safety {S M I_s I_m O_s O_m E : Type}
    {spec : MealySpec S I_s O_s}
    {mirStep : M → I_m → Result (MirOutcome M O_m E)}
    {RelSt : S → M → Prop} {RelIn : I_s → I_m → Prop} {RelOut : O_s → O_m → Prop}
    (sim : MirStepSim spec mirStep RelSt RelIn RelOut)
    {Safe : List (I_s × O_s) → Prop}
    {s₀ : S} {m₀ m_final : M} {inputs_s : List I_s} {turns_m : List (MirTurn I_m O_m E)}
    (hSpecSafe : ∀ {trace_s : List (I_s × O_s)} {s_f : S},
      spec.ValidTrace s₀ trace_s s_f → Safe trace_s)
    (hInitRel : RelSt s₀ m₀)
    (hMir : MirTrace mirStep m₀ turns_m m_final)
    (hInputs : InputsMatchTurns RelIn inputs_s turns_m) :
    let out := spec.runInputs s₀ inputs_s
    Safe out.1 ∧ AcceptedPairsRel RelIn RelOut out.1 (mirAcceptedPairs turns_m) ∧
      RelSt out.2 m_final := by
  obtain ⟨hVal, hRelFinal, hPairs⟩ := sim.lift_runInputs hInitRel hMir hInputs
  exact ⟨hSpecSafe hVal, hPairs, hRelFinal⟩

private theorem inputsMatch_of_absIn {I_s I_m O_m E : Type} (absIn : I_m → I_s) :
    ∀ (turns_m : List (MirTurn I_m O_m E)),
      InputsMatchTurns (fun i_s i_m => i_s = absIn i_m)
        (turns_m.map (fun t => absIn t.input)) turns_m
  | [] => .nil
  | _ :: rest => .cons rfl (inputsMatch_of_absIn absIn rest)

private theorem acceptedPairs_eq_map_of_abs {I_s I_m O_s O_m : Type}
    (absIn : I_m → I_s) (absOut : O_m → O_s) :
    ∀ {pairs_s : List (I_s × O_s)} {pairs_m : List (I_m × O_m)},
      AcceptedPairsRel (fun i_s i_m => i_s = absIn i_m) (fun o_s o_m => o_s = absOut o_m)
        pairs_s pairs_m →
      pairs_s = pairs_m.map (fun p => (absIn p.1, absOut p.2))
  | [], [], .nil => rfl
  | _, _, .cons hIn hOut hTail => by
    subst hIn; subst hOut
    exact congrArg ((_, _) :: ·) (acceptedPairs_eq_map_of_abs absIn absOut hTail)

/-- **Zero-Boilerplate Functional Abstraction Trace Lifter (`MirStepSim.lift_trace_safety_abs`)**:
    When `RelIn` and `RelOut` are given by abstraction functions `absIn : I_m → I_s` and
    `absOut : O_m → O_s`, `Safe` holds **directly** on `(mirAcceptedPairs turns_m).map ...`
    with zero auxiliary input witnesses required! -/
theorem MirStepSim.lift_trace_safety_abs {S M I_s I_m O_s O_m E : Type}
    {spec : MealySpec S I_s O_s}
    {mirStep : M → I_m → Result (MirOutcome M O_m E)}
    {RelSt : S → M → Prop} {absIn : I_m → I_s} {absOut : O_m → O_s}
    (sim : MirStepSim spec mirStep RelSt (fun i_s i_m => i_s = absIn i_m) (fun o_s o_m => o_s = absOut o_m))
    {Safe : List (I_s × O_s) → Prop}
    {s₀ : S} {m₀ m_final : M} {turns_m : List (MirTurn I_m O_m E)}
    (hSpecSafe : ∀ {trace_s : List (I_s × O_s)} {s_f : S},
      spec.ValidTrace s₀ trace_s s_f → Safe trace_s)
    (hInitRel : RelSt s₀ m₀)
    (hMir : MirTrace mirStep m₀ turns_m m_final) :
    Safe ((mirAcceptedPairs turns_m).map (fun p => (absIn p.1, absOut p.2))) ∧
      ∃ s_final, RelSt s_final m_final := by
  have hInputs := inputsMatch_of_absIn absIn turns_m
  obtain ⟨hSafe, hPairs, hRelFinal⟩ :=
    sim.lift_trace_safety hSpecSafe hInitRel hMir hInputs
  have hEq := acceptedPairs_eq_map_of_abs absIn absOut hPairs
  rw [hEq] at hSafe
  exact ⟨hSafe, ⟨_, hRelFinal⟩⟩

/-! ## 5. Horizontal / Phased Typestate Composition (`MirPhaseSim`, `MirStepSim.compose`) -/

/-- Single-phase cross-state refinement (`PhaseA → PhaseB` affine typestate transitions,
    such as `Round1MaskCommitted → Round2ChiEvaluated → Round3ConsistencyVerified → CutOpened`). -/
structure MirPhaseSim {S₁ S₂ M₁ M₂ I_s I_m O_s O_m E : Type}
    (specPhase : S₁ → I_s → Option (S₂ × O_s))
    (mirPhase : M₁ → I_m → Result (core.result.Result (M₂ × O_m) E))
    (Rel₁ : S₁ → M₁ → Prop)
    (Rel₂ : S₂ → M₂ → Prop)
    (RelIn : I_s → I_m → Prop)
    (RelOut : O_s → O_m → Prop) : Prop where
  ok_phase : ∀ {s₁ : S₁} {m₁ : M₁} {m₂ : M₂} {i_s : I_s} {i_m : I_m} {o_m : O_m},
    Rel₁ s₁ m₁ →
    RelIn i_s i_m →
    mirPhase m₁ i_m = .ok (.Ok (m₂, o_m)) →
    match specPhase s₁ i_s with
    | none => False
    | some (s₂, o_s) => Rel₂ s₂ m₂ ∧ RelOut o_s o_m
  err_phase : ∀ {s₁ : S₁} {m₁ : M₁} {i_s : I_s} {i_m : I_m} {e : E},
    Rel₁ s₁ m₁ →
    RelIn i_s i_m →
    mirPhase m₁ i_m = .ok (.Err e) →
    specPhase s₁ i_s = none

/-- Composed pure 2-phase spec step `(S₁ → S₂ → S₃)`. -/
def seqSpecPhases {S₁ S₂ S₃ I₁ I₂ O₁ O₂ : Type}
    (p1 : S₁ → I₁ → Option (S₂ × O₁))
    (p2 : S₂ → I₂ → Option (S₃ × O₂))
    (s₁ : S₁) (inp : I₁ × I₂) : Option (S₃ × (O₁ × O₂)) :=
  match p1 s₁ inp.1 with
  | none => none
  | some (s₂, o₁) =>
    match p2 s₂ inp.2 with
    | none => none
    | some (s₃, o₂) => some (s₃, (o₁, o₂))

/-- Composed MIR 2-phase transition `(M₁ → M₂ → M₃)`. -/
def seqMirPhases {M₁ M₂ M₃ I₁ I₂ O₁ O₂ E : Type}
    (f1 : M₁ → I₁ → Result (core.result.Result (M₂ × O₁) E))
    (f2 : M₂ → I₂ → Result (core.result.Result (M₃ × O₂) E))
    (m₁ : M₁) (inp : I₁ × I₂) : Result (core.result.Result (M₃ × (O₁ × O₂)) E) :=
  Result.bind (f1 m₁ inp.1) fun r1 =>
    match r1 with
    | .Err e => .ok (.Err e)
    | .Ok (m₂, o₁) =>
      Result.bind (f2 m₂ inp.2) fun r2 =>
        match r2 with
        | .Err e => .ok (.Err e)
        | .Ok (m₃, o₂) => .ok (.Ok (m₃, (o₁, o₂)))

/-- **Horizontal / Phased Composition (`MirStepSim.compose`)**:
    Composes `Phase1 → Phase2` and `Phase2 → Phase3` affine typestate simulations into a
    single verified `Phase1 → Phase3` simulation (`0 Classical.choice`). -/
theorem MirStepSim.compose {S₁ S₂ S₃ M₁ M₂ M₃ I_s1 I_m1 I_s2 I_m2 O_s1 O_m1 O_s2 O_m2 E : Type}
    {p1 : S₁ → I_s1 → Option (S₂ × O_s1)}
    {p2 : S₂ → I_s2 → Option (S₃ × O_s2)}
    {f1 : M₁ → I_m1 → Result (core.result.Result (M₂ × O_m1) E)}
    {f2 : M₂ → I_m2 → Result (core.result.Result (M₃ × O_m2) E)}
    {Rel₁ : S₁ → M₁ → Prop} {Rel₂ : S₂ → M₂ → Prop} {Rel₃ : S₃ → M₃ → Prop}
    {RelIn₁ : I_s1 → I_m1 → Prop} {RelIn₂ : I_s2 → I_m2 → Prop}
    {RelOut₁ : O_s1 → O_m1 → Prop} {RelOut₂ : O_s2 → O_m2 → Prop}
    (sim12 : MirPhaseSim p1 f1 Rel₁ Rel₂ RelIn₁ RelOut₁)
    (sim23 : MirPhaseSim p2 f2 Rel₂ Rel₃ RelIn₂ RelOut₂) :
    MirPhaseSim
      (seqSpecPhases p1 p2)
      (seqMirPhases f1 f2)
      Rel₁ Rel₃
      (fun a b => RelIn₁ a.1 b.1 ∧ RelIn₂ a.2 b.2)
      (fun a b => RelOut₁ a.1 b.1 ∧ RelOut₂ a.2 b.2) where
  ok_phase {s₁ m₁ m₃ i_s i_m o_m} hRel₁ hIn hStep := by
    dsimp only [seqMirPhases] at hStep
    cases hf1 : f1 m₁ i_m.1 with
    | fail err => simp [hf1, Result.bind] at hStep
    | div => simp [hf1, Result.bind] at hStep
    | ok r1 =>
      simp only [hf1, Result.bind] at hStep
      cases r1 with
      | Err e => cases hStep
      | Ok pair1 =>
        rcases pair1 with ⟨m₂, o_m1⟩
        have h1 := sim12.ok_phase hRel₁ hIn.1 hf1
        dsimp only [seqSpecPhases]
        cases hp1 : p1 s₁ i_s.1 with
        | none => rw [hp1] at h1; exact False.elim h1
        | some sp1 =>
          rw [hp1] at h1
          rcases sp1 with ⟨s₂, o_s1⟩
          obtain ⟨hRel₂, hOut₁⟩ := h1
          dsimp only
          cases hf2 : f2 m₂ i_m.2 with
          | fail err => simp [hf2] at hStep
          | div => simp [hf2] at hStep
          | ok r2 =>
            simp only [hf2] at hStep
            cases r2 with
            | Err e => cases hStep
            | Ok pair2 =>
              rcases pair2 with ⟨m₃', o_m2⟩
              injection hStep with hOkEq
              injection hOkEq with hProdEq
              injection hProdEq with hmEq hoEq
              subst hmEq; subst hoEq
              have h2 := sim23.ok_phase hRel₂ hIn.2 hf2
              cases hp2 : p2 s₂ i_s.2 with
              | none => rw [hp2] at h2; exact False.elim h2
              | some sp2 =>
                rw [hp2] at h2
                rcases sp2 with ⟨s₃, o_s2⟩
                dsimp only
                exact ⟨h2.1, hOut₁, h2.2⟩
  err_phase {s₁ m₁ i_s i_m e} hRel₁ hIn hStep := by
    dsimp only [seqMirPhases] at hStep
    cases hf1 : f1 m₁ i_m.1 with
    | fail err => simp [hf1, Result.bind] at hStep
    | div => simp [hf1, Result.bind] at hStep
    | ok r1 =>
      simp only [hf1, Result.bind] at hStep
      cases r1 with
      | Err e1 =>
        injection hStep with hErrEq
        cases hErrEq
        have hNone1 := sim12.err_phase hRel₁ hIn.1 hf1
        simp [seqSpecPhases, hNone1]
      | Ok pair1 =>
        rcases pair1 with ⟨m₂, o_m1⟩
        have h1 := sim12.ok_phase hRel₁ hIn.1 hf1
        dsimp only [seqSpecPhases]
        cases hp1 : p1 s₁ i_s.1 with
        | none => rfl
        | some sp1 =>
          rw [hp1] at h1
          rcases sp1 with ⟨s₂, o_s1⟩
          dsimp only
          cases hf2 : f2 m₂ i_m.2 with
          | fail err => simp [hf2] at hStep
          | div => simp [hf2] at hStep
          | ok r2 =>
            simp only [hf2] at hStep
            cases r2 with
            | Ok _ => cases hStep
            | Err e2 =>
              injection hStep with hErrEq
              cases hErrEq
              rw [sim23.err_phase h1.1 hIn.2 hf2]

/-- Convert any homogeneous `MirPhaseSim` (`S → S`, `M → M`) directly into a multi-turn `MirStepSim`. -/
theorem MirPhaseSim.toMirStepSim {S M I_s I_m O_s O_m E : Type}
    {step : S → I_s → Option (S × O_s)}
    {f : M → I_m → Result (core.result.Result (M × O_m) E)}
    {RelSt : S → M → Prop} {RelIn : I_s → I_m → Prop} {RelOut : O_s → O_m → Prop}
    (phase : MirPhaseSim step f RelSt RelSt RelIn RelOut) :
    MirStepSim (MealySpec.ofPure step) (adaptResultPair f) RelSt RelIn RelOut :=
  MirStepSim.ofResultPair step f RelSt RelIn RelOut phase.ok_phase phase.err_phase

/-! ## 6. Constructive Aeneas Data-Refinement Helpers (`0 Classical.choice`) -/

/-- Exact `iff` characterization of Aeneas checked `Std.U64` addition. -/
theorem u64_val_add_checked (a b c : Std.U64) :
    (a + b : Result Std.U64) = .ok c ↔ a.val + b.val < 2 ^ 64 ∧ c.val = a.val + b.val := by
  rw [hAdd_uscalar_eq]
  by_cases hlt : a.val + b.val < 2 ^ 64
  · simp only [hlt, ↓reduceIte, true_and]
    constructor
    · intro hEq
      injection hEq with hc
      subst hc
      change (a.bv + b.bv).toNat = a.bv.toNat + b.bv.toNat
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hlt]
    · intro hc
      apply congrArg Result.ok
      apply UScalar.eq_of_val_eq
      change (a.bv + b.bv).toNat = c.val
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hlt, hc]
  · simp only [hlt, ↓reduceIte, false_and]
    constructor
    · intro hEq; cases hEq
    · intro hFalse; exact False.elim hFalse

/-- Exact `iff` characterization of Aeneas checked `Std.U64` subtraction. -/
theorem u64_val_sub_checked (a b c : Std.U64) :
    (a - b : Result Std.U64) = .ok c ↔ b.val ≤ a.val ∧ c.val = a.val - b.val := by
  rw [hSub_uscalar_eq]
  by_cases hle : b.val ≤ a.val
  · simp only [hle, ↓reduceIte, true_and]
    constructor
    · intro hEq
      injection hEq with hc
      subst hc
      change (a.bv - b.bv).toNat = a.bv.toNat - b.bv.toNat
      exact BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)
    · intro hc
      apply congrArg Result.ok
      apply UScalar.eq_of_val_eq
      change (a.bv - b.bv).toNat = c.val
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle), hc]
  · simp only [hle, ↓reduceIte, false_and]
    constructor
    · intro hEq; cases hEq
    · intro hFalse; exact False.elim hFalse

/-- Exact `iff` characterization of Aeneas checked `Std.U32` addition. -/
theorem u32_val_add_checked (a b c : Std.U32) :
    (a + b : Result Std.U32) = .ok c ↔ a.val + b.val < 2 ^ 32 ∧ c.val = a.val + b.val := by
  rw [hAdd_uscalar_eq]
  by_cases hlt : a.val + b.val < 2 ^ 32
  · simp only [hlt, ↓reduceIte, true_and]
    constructor
    · intro hEq
      injection hEq with hc
      subst hc
      change (a.bv + b.bv).toNat = a.bv.toNat + b.bv.toNat
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hlt]
    · intro hc
      apply congrArg Result.ok
      apply UScalar.eq_of_val_eq
      change (a.bv + b.bv).toNat = c.val
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hlt, hc]
  · simp only [hlt, ↓reduceIte, false_and]
    constructor
    · intro hEq; cases hEq
    · intro hFalse; exact False.elim hFalse

/-- Generic `UScalar` equality iff underlying `Nat` value equality. -/
theorem uscalar_eq_iff {ty : UScalarTy} (a b : UScalar ty) : a = b ↔ a.val = b.val :=
  ⟨congrArg UScalar.val, UScalar.eq_of_val_eq⟩

/-- `Std.U8` equality iff `.val` equality. -/
theorem u8_eq_iff (a b : Std.U8) : a = b ↔ a.val = b.val :=
  uscalar_eq_iff a b

/-- `Std.U64` equality iff `.val` equality. -/
theorem u64_eq_iff (a b : Std.U64) : a = b ↔ a.val = b.val :=
  uscalar_eq_iff a b

/-- Constructive `Result` monadic bind `.ok` decomposition (`0 Classical.choice`). -/
theorem result_bind_ok_split {α β : Type} (r : Result α) (f : α → Result β) (y : β) :
    (r >>= f) = .ok y ↔ ∃ x, r = .ok x ∧ f x = .ok y := by
  cases r with
  | ok x =>
    constructor
    · intro h; exact ⟨x, rfl, h⟩
    · rintro ⟨x', hx', hfx'⟩
      injection hx' with hEq
      subst hEq
      exact hfx'
  | fail _ =>
    constructor
    · intro h; cases h
    · rintro ⟨_, hx, _⟩; cases hx
  | div =>
    constructor
    · intro h; cases h
    · rintro ⟨_, hx, _⟩; cases hx

/-- Fixed-length `[u8; 32]` Aeneas array `.val` projection is strictly injective. -/
theorem array32_to_list_injective {a b : Std.Array Std.U8 32#usize} (h : a.val = b.val) : a = b :=
  Std.Array.ext h

/-- Convert any fixed-length Aeneas `Std.Array Std.U8 n` into standard Lean `List UInt8`
    for direct bridging against `Qsag` pure byte specifications. -/
@[expose]
def arrayU8ToBytes {n : Std.Usize} (a : Std.Array Std.U8 n) : List UInt8 :=
  a.val.map (fun b => UInt8.ofBitVec b.bv)

theorem arrayU8ToBytes_length {n : Std.Usize} (a : Std.Array Std.U8 n) :
    (arrayU8ToBytes a).length = n.val := by
  simp [arrayU8ToBytes, a.property]

private theorem u8_list_eq_of_map_uint8 :
    ∀ {xs ys : List Std.U8},
      xs.map (fun b => UInt8.ofBitVec b.bv) = ys.map (fun b => UInt8.ofBitVec b.bv) →
      xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, h => by
    injection h with hHead hTail
    have hBv : x.bv = y.bv := congrArg UInt8.toBitVec hHead
    have hHeadEq : x = y := UScalar.ext hBv
    subst hHeadEq
    exact congrArg (x :: ·) (u8_list_eq_of_map_uint8 hTail)

/-- Bridging Aeneas `Std.Array Std.U8 n` to `List UInt8` is strictly injective (`0 Classical.choice`). -/
theorem arrayU8ToBytes_injective {n : Std.Usize} {a b : Std.Array Std.U8 n}
    (h : arrayU8ToBytes a = arrayU8ToBytes b) : a = b :=
  Std.Array.ext (u8_list_eq_of_map_uint8 h)

/-! ## 7. `#tooth` Mutation-Sensitivity & Refusal Witnesses -/

/-- `#tooth`: Checked `u64` addition refuses overflow (`u64::MAX + 1 ≠ .ok c` for all `c`). -/
theorem tooth_u64_val_add_checked_overflow_refused (c : Std.U64) :
    (18446744073709551615#u64 + 1#u64 : Result Std.U64) ≠ .ok c := by
  intro h
  obtain ⟨hlt, _⟩ := (u64_val_add_checked _ _ c).mp h
  have hv : (18446744073709551615#u64).val = 2 ^ 64 - 1 := rfl
  have hv1 : (1#u64).val = 1 := rfl
  rw [hv, hv1] at hlt
  exact absurd hlt (by decide)

/-- `#tooth`: A quarantine `MealySpec` that sets `poisoned = true` on `errStep` permanently
    refuses all subsequent inputs even when the input itself would have been valid! -/
theorem tooth_quarantine_errStep_blocks_subsequent_accept :
    let spec : MealySpec Bool Bool Unit := {
      step := fun poisoned okInput =>
        if !poisoned && okInput then some (false, ()) else none
      errStep := fun _ _ => true
    }
    (spec.runInputs false [false, true]).1 = [] ∧
      (spec.runInputs false [false, true]).2 = true ∧
      (spec.runInputs false [true]).1 = [(true, ())] := by
  decide

end qsag_verified.proofs

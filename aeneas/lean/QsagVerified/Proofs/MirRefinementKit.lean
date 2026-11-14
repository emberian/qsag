module

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

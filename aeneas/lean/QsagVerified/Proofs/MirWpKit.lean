module
public import Aeneas

/-!
# QsagVerified.Proofs.MirWpKit — Constructive `Result`-Monad Weakest-Precondition & Relational Refinement Kit

Zero-`Classical.choice` Hoare / weakest-precondition (`Result.wp`, `Result.wlp`) and relational
refinement (`MirRel1`, `MirRel2`) combinator layer over Aeneas's `Aeneas.Std.Result` monad:

1. **Total & Fail-Closed Weakest Preconditions (`Result.wp`, `Result.wlp`)**:
   `Result.wp r P` asserts total termination with `P v` (`r = .ok v ∧ P v`); `Result.wlp r P Qerr`
   asserts partial/fail-closed safety (either `.ok v` satisfying `P v` or `.fail e` satisfying `Qerr e`,
   never `.div`).
2. **Compositional Monadic Step Rules (`wp_ok`, `wp_fail_elim`, `wp_bind`, `wp_let`, `wp_ite`, `wp_massert`)**:
   Eliminates nested `cases h : f x <;> simp` boilerplate across multi-step extracted Rust functions
   via `simp` / `mir_wp` / `mir_sim_step` rewriting.
3. **Checked Rust Scalar Arithmetic WP Rules (`wp_uscalar_add`, `wp_uscalar_sub`, `wp_uscalar_mul`)**:
   Reduces checked `UScalar` `+`, `-`, `*` transitions directly to machine-word range guards + pure
   `BitVec` postconditions.
4. **Relational MIR Operator Combinators (`MirRel1`, `MirRel2`)**:
   Connects pure canonical specifications (`f_spec : α_s → β_s`) directly to monadic MIR functions
   (`f_mir : α_m → Result β_m`) via `Result.wp (f_mir x) (R_out (f_spec a))`.
-/

public section

namespace qsag_verified.proofs

open Aeneas Aeneas.Std Result Error

universe u

/-! ## 1. Total (`Result.wp`) and Fail-Closed (`Result.wlp`) Weakest Preconditions -/

/-- Total-correctness weakest precondition on `Aeneas.Std.Result`:
    `Result.wp r P` holds iff `r` terminates with `.ok v` and `P v` holds (`0 Classical.choice`). -/
@[expose] def Result.wp {α : Type u} (r : Result α) (P : α → Prop) : Prop :=
  match r with
  | .ok v => P v
  | .fail _ => False
  | .div => False

/-- Fail-closed weakest liberal precondition on `Aeneas.Std.Result`:
    `Result.wlp r P Qerr` holds iff `r` either returns `.ok v` with `P v` or fails cleanly with
    `.fail e` satisfying `Qerr e` (excluding divergence `.div`). -/
@[expose] def Result.wlp {α : Type u} (r : Result α) (P : α → Prop)
    (Qerr : Error → Prop := fun _ => True) : Prop :=
  match r with
  | .ok v => P v
  | .fail e => Qerr e
  | .div => False

@[simp] theorem wp_ok {α : Type u} (v : α) (P : α → Prop) :
    Result.wp (.ok v) P ↔ P v := Iff.rfl

@[simp] theorem wp_pure {α : Type u} (v : α) (P : α → Prop) :
    Result.wp (pure v : Result α) P ↔ P v := Iff.rfl

@[simp] theorem wp_lift {α : Type u} (v : α) (P : α → Prop) :
    Result.wp (lift v) P ↔ P v := Iff.rfl

@[simp] theorem wp_fail {α : Type u} (e : Error) (P : α → Prop) :
    Result.wp (.fail e : Result α) P ↔ False := Iff.rfl

/-- Direct elimination of impossible `.fail` branches under `Result.wp`. -/
theorem wp_fail_elim {α : Type u} {e : Error} {P : α → Prop} {Q : Prop}
    (h : Result.wp (.fail e : Result α) P) : Q :=
  False.elim h

@[simp] theorem wp_div {α : Type u} (P : α → Prop) :
    Result.wp (.div : Result α) P ↔ False := Iff.rfl

/-- Characterization of `Result.wp` as an explicit `.ok` witness (`0 Classical.choice`). -/
theorem wp_iff_exists_ok {α : Type u} (r : Result α) (P : α → Prop) :
    Result.wp r P ↔ ∃ v : α, r = .ok v ∧ P v := by
  cases r with
  | ok v =>
    constructor
    · intro hP; exact ⟨v, rfl, hP⟩
    · rintro ⟨v', hEq, hP⟩; injection hEq with hV; subst hV; exact hP
  | fail _ =>
    constructor
    · intro hF; exact False.elim hF
    · rintro ⟨_, hEq, _⟩; cases hEq
  | div =>
    constructor
    · intro hF; exact False.elim hF
    · rintro ⟨_, hEq, _⟩; cases hEq

/-- Construct `Result.wp r P` from an equation `r = .ok v` and `P v`. -/
theorem wp_of_eq_ok {α : Type u} {r : Result α} {v : α} {P : α → Prop}
    (hEq : r = .ok v) (hP : P v) : Result.wp r P := by
  rw [hEq]
  exact hP

/-- Covariance / consequence rule for `Result.wp`. -/
theorem wp_mono {α : Type u} {r : Result α} {P Q : α → Prop}
    (hWp : Result.wp r P) (hImp : ∀ v : α, P v → Q v) : Result.wp r Q := by
  cases r with
  | ok v => exact hImp v hWp
  | fail _ => exact False.elim hWp
  | div => exact False.elim hWp

/-- Sequencing rule for `Result.bind` (`wp_result_bind`). -/
@[simp] theorem wp_result_bind {α β : Type u}
    (x : Result α) (f : α → Result β) (P : β → Prop) :
    Result.wp (Result.bind x f) P ↔ Result.wp x (fun v => Result.wp (f v) P) := by
  cases x <;> exact Iff.rfl

/-- Sequencing rule for monadic `x >>= f` (`wp_bind`). -/
@[simp] theorem wp_bind {α β : Type u}
    (x : Result α) (f : α → Result β) (P : β → Prop) :
    Result.wp (x >>= f) P ↔ Result.wp x (fun v => Result.wp (f v) P) := by
  cases x <;> exact Iff.rfl

/-- `let`-binding transparency for `Result.wp` (`wp_let`). -/
theorem wp_let {α β : Type u}
    (e : α) (k : α → Result β) (P : β → Prop) :
    Result.wp (let v := e; k v) P ↔ Result.wp (k e) P := Iff.rfl

/-- Conditional branching rule for `Result.wp` (`wp_ite`). -/
theorem wp_ite {α : Type u} (c : Prop) [Decidable c]
    (t e : Result α) (P : α → Prop) :
    Result.wp (if c then t else e) P ↔ (if c then Result.wp t P else Result.wp e P) := by
  split <;> exact Iff.rfl

/-- Assertion rule for `Aeneas.Std.massert` (`wp_massert`). -/
@[simp] theorem wp_massert (b : Prop) [Decidable b] (P : Unit → Prop) :
    Result.wp (massert b) P ↔ (b ∧ P ()) := by
  unfold massert
  by_cases hb : b
  · simp only [hb, ↓reduceIte, wp_ok, true_and]
  · simp only [hb, ↓reduceIte, wp_fail, false_and]

/-- Every total `Result.wp r P` implies fail-closed `Result.wlp r P Qerr`. -/
theorem wlp_of_wp {α : Type u} {r : Result α} {P : α → Prop} {Qerr : Error → Prop}
    (h : Result.wp r P) : Result.wlp r P Qerr := by
  cases r with
  | ok v => exact h
  | fail _ => exact False.elim h
  | div => exact False.elim h

@[simp] theorem wlp_result_bind {α β : Type u}
    (x : Result α) (f : α → Result β) (P : β → Prop) (Qerr : Error → Prop) :
    Result.wlp (Result.bind x f) P Qerr ↔
      Result.wlp x (fun v => Result.wlp (f v) P Qerr) Qerr := by
  cases x <;> exact Iff.rfl

@[simp] theorem wlp_bind {α β : Type u}
    (x : Result α) (f : α → Result β) (P : β → Prop) (Qerr : Error → Prop) :
    Result.wlp (x >>= f) P Qerr ↔
      Result.wlp x (fun v => Result.wlp (f v) P Qerr) Qerr := by
  cases x <;> exact Iff.rfl

/-! ## 2. Checked Rust `UScalar` Arithmetic WP Rules -/

theorem wp_uscalar_add {ty : UScalarTy} (a b : UScalar ty) (P : UScalar ty → Prop) :
    Result.wp (a + b : Result (UScalar ty)) P ↔
      (a.val + b.val < 2 ^ ty.numBits ∧ P ⟨a.bv + b.bv⟩) := by
  show Result.wp (if a.val + b.val < 2 ^ ty.numBits then .ok ⟨a.bv + b.bv⟩ else .fail .integerOverflow) P ↔ _
  by_cases hLt : a.val + b.val < 2 ^ ty.numBits
  · simp only [hLt, ↓reduceIte, wp_ok, true_and]
  · simp only [hLt, ↓reduceIte, wp_fail, false_and]

theorem wp_uscalar_sub {ty : UScalarTy} (a b : UScalar ty) (P : UScalar ty → Prop) :
    Result.wp (a - b : Result (UScalar ty)) P ↔
      (b.val ≤ a.val ∧ P ⟨a.bv - b.bv⟩) := by
  show Result.wp (if b.val ≤ a.val then .ok ⟨a.bv - b.bv⟩ else .fail .integerOverflow) P ↔ _
  by_cases hLe : b.val ≤ a.val
  · simp only [hLe, ↓reduceIte, wp_ok, true_and]
  · simp only [hLe, ↓reduceIte, wp_fail, false_and]

theorem wp_uscalar_mul {ty : UScalarTy} (a b : UScalar ty) (P : UScalar ty → Prop) :
    Result.wp (a * b : Result (UScalar ty)) P ↔
      (a.val * b.val < 2 ^ ty.numBits ∧ P ⟨a.bv * b.bv⟩) := by
  show Result.wp (if a.val * b.val < 2 ^ ty.numBits then .ok ⟨a.bv * b.bv⟩ else .fail .integerOverflow) P ↔ _
  by_cases hLt : a.val * b.val < 2 ^ ty.numBits
  · simp only [hLt, ↓reduceIte, wp_ok, true_and]
  · simp only [hLt, ↓reduceIte, wp_fail, false_and]

/-! ## 3. Relational `Spec ↔ MIR` Operator Combinators (`MirRel1`, `MirRel2`) -/

/-- Unary relational refinement from a pure spec `f_spec : α_s → β_s` to an Aeneas MIR function
    `f_mir : α_m → Result β_m`: related inputs evaluate without failure/divergence to related outputs! -/
@[expose] def MirRel1 {α_s α_m β_s β_m : Type}
    (R_in : α_s → α_m → Prop) (R_out : β_s → β_m → Prop)
    (f_spec : α_s → β_s) (f_mir : α_m → Result β_m) : Prop :=
  ∀ {a : α_s} {x : α_m}, R_in a x → Result.wp (f_mir x) (R_out (f_spec a))

/-- Binary relational refinement from `f_spec : α_s → β_s → γ_s` to `f_mir : α_m → β_m → Result γ_m`. -/
@[expose] def MirRel2 {α_s α_m β_s β_m γ_s γ_m : Type}
    (R_a : α_s → α_m → Prop) (R_b : β_s → β_m → Prop) (R_out : γ_s → γ_m → Prop)
    (f_spec : α_s → β_s → γ_s) (f_mir : α_m → β_m → Result γ_m) : Prop :=
  ∀ {a : α_s} {x : α_m} {b : β_s} {y : β_m},
    R_a a x → R_b b y → Result.wp (f_mir x y) (R_out (f_spec a b))

/-- Monadic Kleisli composition of `MirRel1`: chaining two verified MIR functions `g₁ >=> g₂`
    refines `f₂ ∘ f₁` with zero manual `Result` case-splitting! -/
theorem MirRel1.comp_bind {α_s α_m β_s β_m γ_s γ_m : Type}
    {R₁ : α_s → α_m → Prop} {R₂ : β_s → β_m → Prop} {R₃ : γ_s → γ_m → Prop}
    {f₁ : α_s → β_s} {g₁ : α_m → Result β_m}
    {f₂ : β_s → γ_s} {g₂ : β_m → Result γ_m}
    (h₁ : MirRel1 R₁ R₂ f₁ g₁) (h₂ : MirRel1 R₂ R₃ f₂ g₂) :
    MirRel1 R₁ R₃ (f₂ ∘ f₁) (fun x => g₁ x >>= g₂) := by
  intro a x hR₁
  rw [wp_bind]
  exact wp_mono (h₁ hR₁) (fun y hR₂ => h₂ hR₂)

/-! ## 4. `mir_wp` / `mir_sim_step` Tactic Macros & Regression Exemplars -/

/-- One-shot weakest-precondition normalizer peeling `>>=`, `Result.bind`, `lift`, `pure`, `.ok`,
    `.fail`, `.div`, `massert`, `if`, and checked `UScalar` arithmetic in a single tactic call. -/
macro "mir_wp" : tactic =>
  `(tactic| simp only [bind_eq_result_bind, wp_result_bind, wp_bind, wp_ok, wp_pure, wp_lift,
      wp_fail, wp_div, wp_massert, wp_ite, wp_uscalar_add, wp_uscalar_sub, wp_uscalar_mul])

/-- Alias for `mir_wp` followed by `dsimp only` for stepping multi-bind MIR kernels. -/
macro "mir_sim_step" : tactic =>
  `(tactic| (mir_wp; try dsimp only))

/-- Exemplar: 3-bind Rust-style checked `U64` + `massert` pipeline verified in 2 lines via the
    mir_sim_step tactic macro with ZERO `cases` splits! -/
def mirCheckedDeltaCheck (base delta cap : Std.U64) : Result Std.U64 := do
  let next ← base + delta
  massert (next.val ≤ cap.val)
  let rem ← cap - next
  pure rem

theorem mirCheckedDeltaCheck_wp_spec (base delta cap : Std.U64)
    (hBound : base.val + delta.val ≤ cap.val) :
    Result.wp (mirCheckedDeltaCheck base delta cap)
      (fun rem => rem.val = cap.val - (base.val + delta.val)) := by
  unfold mirCheckedDeltaCheck
  mir_sim_step
  have hCapLt : cap.val < 2 ^ 64 := cap.val_lt
  have hSumLt : base.val + delta.val < 2 ^ 64 := Nat.lt_of_le_of_lt hBound hCapLt
  have hNextVal : (⟨base.bv + delta.bv⟩ : Std.U64).val = base.val + delta.val := by
    change (base.bv + delta.bv).toNat = base.val + delta.val
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt hSumLt
  refine ⟨hSumLt, hNextVal.symm ▸ hBound, hNextVal.symm ▸ hBound, ?_⟩
  change (cap.bv - (base.bv + delta.bv)).toNat = cap.val - (base.val + delta.val)
  have hBvLe : base.bv + delta.bv ≤ cap.bv :=
    (BitVec.le_def).mpr (by rw [BitVec.toNat_add, Nat.mod_eq_of_lt hSumLt]; exact hBound)
  rw [BitVec.toNat_sub_of_le hBvLe, BitVec.toNat_add, Nat.mod_eq_of_lt hSumLt]

/-- Tooth: when `base + delta > cap`, `Result.wp (mirCheckedDeltaCheck base delta cap) (fun _ => True)`
    is refuted (`False`), proving `mirCheckedDeltaCheck` fails closed on cap violation! -/
theorem tooth_mirCheckedDeltaCheck_exceeds_cap_fails (base delta cap : Std.U64)
    (hOver : cap.val < base.val + delta.val) :
    ¬ Result.wp (mirCheckedDeltaCheck base delta cap) (fun _ => True) := by
  unfold mirCheckedDeltaCheck
  mir_sim_step
  rintro ⟨hSumLt, hLeCap, _⟩
  have hNextVal : (⟨base.bv + delta.bv⟩ : Std.U64).val = base.val + delta.val := by
    change (base.bv + delta.bv).toNat = base.val + delta.val
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt hSumLt
  rw [hNextVal] at hLeCap
  exact Nat.not_lt_of_ge hLeCap hOver

end qsag_verified.proofs
end

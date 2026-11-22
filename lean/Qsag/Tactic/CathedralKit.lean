module
/-
# Qsag.Tactic.CathedralKit — `GPaco`, Polynomial `(Co)Algebra` Proof Repair & Scar-Free Audit Gates

Foundational Lean 4.35 (`LAW-M1` / `LAW-M2`, `0 Classical.choice`) automation and proof-repair core
below all `Qsag` library layers (`rank 0`, importing `Qsag.Tactic.AssuranceKit` and `Lean` only):

1. **Generalized Parameterized Coinduction (`Qsag.Paco`)**:
   Hur-et-al. (`paco`, `upaco`, POPL 2013) and Zakowski-et-al. (`gpaco`, `gupaco`, `rclo`,
   `Compatible`, `gpaco_clo`, CPP 2020) over pure `Init` binary relations (`0` Mathlib,
   `0 Classical.choice`), paired with `by gpaco_step`.
2. **Polynomial `(Co)Algebra` Equivalence & Scar-Free Proof Repair (`Qsag.Repair`, `arXiv:2610.36669v1`)**:
   Mechanizes Plante–Paul–Viola–Kavvos–Ringer polynomial endofunctors `PolyF A B`, homotopy-initial
   algebras `InitPAlg` (`AlgConfig`, `repair_by_instantiation`, total-space `elim_repair_ok`), and
   final coalgebras `FinalPCoalg` (`CoalgConfig`, constructive Rutten span `coind`, `corec_ok`,
   `pushRel_isBisim`, `coind_ok`) with **zero cubical/univalence/choice axioms**.
3. **Constructive Elaboration Guards & `#assert_no_scar` Kernel Dependency Scanner**:
   - `synthConstructiveDecidable?`: synthesizes `[Decidable c]` while actively rejecting any
     instance whose transitive constant/axiom cone touches `Classical.choice`.
   - `#assert_no_scar <RetiredId> in <TargetId>+`: compile-time kernel constant-cone verifier
     certifying that repaired definitions and theorems retain zero residual dependency ("scar") on
     a retired carrier or specification.
-/

public import Qsag.Tactic.AssuranceKit
public meta import Lean

public section

namespace Qsag.Paco

set_option autoImplicit false

universe u

/-! ## 1. Binary Relation Lattice & Monotone Endofunctors (`Rel`, `MonoRel`) -/

/-- Binary relations over `α`. -/
abbrev Rel (α : Type u) : Type u := α → α → Prop

namespace Rel

variable {α : Type u}

abbrev bot : Rel α := fun _ _ => False
abbrev top : Rel α := fun _ _ => True
abbrev union (R S : Rel α) : Rel α := fun x y => R x y ∨ S x y
abbrev inter (R S : Rel α) : Rel α := fun x y => R x y ∧ S x y
abbrev le (R S : Rel α) : Prop := ∀ x y, R x y → S x y

theorem le_refl (R : Rel α) : le R R := fun _ _ h => h

theorem le_trans {R S T : Rel α} (hRS : le R S) (hST : le S T) : le R T :=
  fun x y hR => hST x y (hRS x y hR)

theorem le_antisymm {R S : Rel α} (hRS : le R S) (hSR : le S R) : R = S :=
  funext fun x => funext fun y => propext ⟨hRS x y, hSR x y⟩

theorem bot_le (R : Rel α) : le bot R := fun _ _ h => False.elim h

theorem le_sup_left {R S : Rel α} : le R (union R S) := fun _ _ h => Or.inl h

theorem le_sup_right {R S : Rel α} : le S (union R S) := fun _ _ h => Or.inr h

theorem sup_le {R S T : Rel α} (hRT : le R T) (hST : le S T) : le (union R S) T :=
  fun x y h => h.elim (hRT x y) (hST x y)

theorem sup_le_sup {R₁ R₂ S₁ S₂ : Rel α} (h₁ : le R₁ R₂) (h₂ : le S₁ S₂) :
    le (union R₁ S₁) (union R₂ S₂) :=
  sup_le (le_trans h₁ le_sup_left) (le_trans h₂ le_sup_right)

theorem sup_bot (R : Rel α) : union R bot = R :=
  le_antisymm (sup_le (le_refl R) (bot_le R)) le_sup_left

theorem bot_sup (R : Rel α) : union bot R = R :=
  le_antisymm (sup_le (bot_le R) (le_refl R)) le_sup_right

theorem sup_idem (R : Rel α) : union R R = R :=
  le_antisymm (sup_le (le_refl R) (le_refl R)) le_sup_left

end Rel

/-- Bundled monotone relational operator on `Rel α`. -/
structure MonoRel (α : Type u) where
  fn : Rel α → Rel α
  mono : ∀ {R S : Rel α}, Rel.le R S → Rel.le (fn R) (fn S)

namespace MonoRel

variable {α : Type u}

/-- Greatest fixed point (Knaster–Tarski union of all post-fixpoints). -/
@[expose] def gfp (F : MonoRel α) : Rel α :=
  fun x y => ∃ R : Rel α, Rel.le R (F.fn R) ∧ R x y

theorem le_gfp (F : MonoRel α) {R : Rel α} (hPost : Rel.le R (F.fn R)) : Rel.le R F.gfp :=
  fun _ _ hxy => ⟨R, hPost, hxy⟩

theorem gfp_unfold (F : MonoRel α) : Rel.le F.gfp (F.fn F.gfp) := by
  intro x y ⟨R, hPost, hxy⟩
  exact F.mono (le_gfp F hPost) x y (hPost x y hxy)

theorem gfp_fold (F : MonoRel α) : Rel.le (F.fn F.gfp) F.gfp :=
  le_gfp F (F.mono (gfp_unfold F))

theorem gfp_fixed (F : MonoRel α) : F.gfp = F.fn F.gfp :=
  Rel.le_antisymm (gfp_unfold F) (gfp_fold F)

end MonoRel

/-! ## 2. Parameterized & Generalized Parameterized Coinduction (`paco`, `gpaco`, `rclo`) -/

section GPacoCore

variable {α : Type u}

/-- Parameterized greatest fixed point `paco F r := ν R. F (R ∪ r)`. -/
@[expose] def paco (F : MonoRel α) (r : Rel α) : Rel α :=
  fun x y => ∃ R : Rel α, Rel.le R (F.fn (Rel.union R r)) ∧ R x y

/-- Usable coinductive hypothesis `upaco F r := paco F r ∪ r`. -/
abbrev upaco (F : MonoRel α) (r : Rel α) : Rel α :=
  Rel.union (paco F r) r

/-- Generalized parameterized coinduction `gpaco F r g := paco F (r ∪ g) ∪ r`. -/
abbrev gpaco (F : MonoRel α) (r g : Rel α) : Rel α :=
  Rel.union (paco F (Rel.union r g)) r

/-- Usable guarded coinductive hypothesis after one `F` step: `gupaco F r g := gpaco F r g ∪ g`. -/
abbrev gupaco (F : MonoRel α) (r g : Rel α) : Rel α :=
  Rel.union (gpaco F r g) g

theorem paco_coind (F : MonoRel α) (R r : Rel α) {x y : α}
    (hPost : Rel.le R (F.fn (Rel.union R r))) (hxy : R x y) : paco F r x y :=
  ⟨R, hPost, hxy⟩

theorem paco_mon (F : MonoRel α) {r s : Rel α} (hrs : Rel.le r s) :
    Rel.le (paco F r) (paco F s) := by
  intro x y ⟨R, hPost, hxy⟩
  exact ⟨R, fun a b hab => F.mono (Rel.sup_le_sup (Rel.le_refl R) hrs) a b (hPost a b hab), hxy⟩

theorem paco_unfold (F : MonoRel α) (r : Rel α) :
    Rel.le (paco F r) (F.fn (upaco F r)) := by
  intro x y ⟨R, hPost, hxy⟩
  have hLe : Rel.le (Rel.union R r) (upaco F r) :=
    Rel.sup_le_sup (fun _ _ h => ⟨R, hPost, h⟩) (Rel.le_refl r)
  exact F.mono hLe x y (hPost x y hxy)

theorem paco_fold (F : MonoRel α) (r : Rel α) :
    Rel.le (F.fn (upaco F r)) (paco F r) := by
  intro x y hF
  refine ⟨F.fn (upaco F r), fun a b hab => ?_, hF⟩
  exact F.mono (Rel.sup_le_sup (paco_unfold F r) (Rel.le_refl r)) a b hab

theorem paco_init (F : MonoRel α) : paco F Rel.bot = F.gfp := by
  apply Rel.le_antisymm
  · intro x y ⟨R, hPost, hxy⟩
    refine ⟨R, fun a b hab => ?_, hxy⟩
    have h := hPost a b hab
    rw [Rel.sup_bot] at h
    exact h
  · intro x y ⟨R, hPost, hxy⟩
    refine ⟨R, fun a b hab => ?_, hxy⟩
    rw [Rel.sup_bot]
    exact hPost a b hab

theorem paco_acc_upaco (F : MonoRel α) (r : Rel α) :
    Rel.le (paco F (upaco F r)) (paco F r) := by
  intro x y ⟨R, hPost, hxy⟩
  refine ⟨Rel.union R (paco F r), fun a b hab => ?_, Or.inl hxy⟩
  cases hab with
  | inl hR =>
    refine F.mono (fun u v huv => ?_) a b (hPost a b hR)
    rcases huv with hRu | (hp | hr)
    · exact Or.inl (Or.inl hRu)
    · exact Or.inl (Or.inr hp)
    · exact Or.inr hr
  | inr hp =>
    refine F.mono (fun u v huv => ?_) a b (paco_unfold F r a b hp)
    rcases huv with hp' | hr
    · exact Or.inl (Or.inr hp')
    · exact Or.inr hr

theorem paco_acc (F : MonoRel α) (r : Rel α) :
    Rel.le (paco F (paco F r)) (paco F r) :=
  Rel.le_trans (paco_mon F Rel.le_sup_left) (paco_acc_upaco F r)

theorem paco_final (F : MonoRel α) (r : Rel α) (hr : Rel.le r F.gfp) :
    Rel.le (paco F r) F.gfp := by
  intro x y hp
  have h1 : paco F F.gfp x y := paco_mon F hr x y hp
  rw [← paco_init F] at h1 ⊢
  exact paco_acc F Rel.bot x y h1

theorem gupaco_eq_upaco (F : MonoRel α) (r g : Rel α) :
    gupaco F r g = upaco F (Rel.union r g) := by
  apply Rel.le_antisymm
  · intro x y h
    rcases h with (hp | hr) | hg
    · exact Or.inl hp
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr hg)
  · intro x y h
    rcases h with hp | (hr | hg)
    · exact Or.inl (Or.inl hp)
    · exact Or.inl (Or.inr hr)
    · exact Or.inr hg

theorem gpaco_init (F : MonoRel α) : gpaco F Rel.bot Rel.bot = F.gfp := by
  change Rel.union (paco F (Rel.union Rel.bot Rel.bot)) Rel.bot = F.gfp
  rw [Rel.sup_bot, Rel.sup_bot, paco_init]

theorem gpaco_unfold (F : MonoRel α) (r g : Rel α) :
    Rel.le (gpaco F r g) (Rel.union (F.fn (gupaco F r g)) r) := by
  intro x y hxy
  cases hxy with
  | inl hp =>
    left
    rw [gupaco_eq_upaco]
    exact paco_unfold F (Rel.union r g) x y hp
  | inr hr => exact Or.inr hr

theorem gpaco_fold (F : MonoRel α) (r g : Rel α) :
    Rel.le (F.fn (gupaco F r g)) (gpaco F r g) := by
  intro x y hF
  left
  rw [gupaco_eq_upaco] at hF
  exact paco_fold F (Rel.union r g) x y hF

theorem gpaco_acc (F : MonoRel α) (r g : Rel α) :
    Rel.le (gpaco F r (gupaco F r g)) (gpaco F r g) := by
  intro x y hxy
  cases hxy with
  | inl hp =>
    left
    have hLe : Rel.le (Rel.union r (gupaco F r g)) (upaco F (Rel.union r g)) := by
      intro a b hab
      rcases hab with hr | hgu
      · exact Or.inr (Or.inl hr)
      · rw [gupaco_eq_upaco] at hgu
        exact hgu
    exact paco_acc_upaco F (Rel.union r g) x y (paco_mon F hLe x y hp)
  | inr hr => exact Or.inr hr

/-- **Constructive `gpaco` Coinduction (`gpaco_coind`, `0 Classical.choice`)**:
    Any relation `R` that steps into `F (R ∪ gupaco F r g)` or lands in the base `r` is included
    in `gpaco F r g`. -/
theorem gpaco_coind (F : MonoRel α) (R r g : Rel α) {x y : α}
    (hPost : ∀ a b, R a b → F.fn (Rel.union R (gupaco F r g)) a b ∨ r a b)
    (hxy : R x y) : gpaco F r g x y := by
  cases hPost x y hxy with
  | inr hr => exact Or.inr hr
  | inl hFxy =>
    left
    let R' : Rel α := fun a b => R a b ∧ F.fn (Rel.union R (gupaco F r g)) a b
    refine paco_coind F (Rel.union R' (paco F (Rel.union r g))) (Rel.union r g)
      (fun a b hab => ?_) (Or.inl ⟨hxy, hFxy⟩)
    cases hab with
    | inl hR' =>
      refine F.mono (fun u v huv => ?_) a b hR'.2
      cases huv with
      | inl hRuv =>
        cases hPost u v hRuv with
        | inl hFuv => exact Or.inl (Or.inl ⟨hRuv, hFuv⟩)
        | inr hruv => exact Or.inr (Or.inl hruv)
      | inr hgu =>
        rw [gupaco_eq_upaco] at hgu
        cases hgu with
        | inl hp => exact Or.inl (Or.inr hp)
        | inr hrg => exact Or.inr hrg
    | inr hp =>
      refine F.mono (fun u v huv => ?_) a b (paco_unfold F (Rel.union r g) a b hp)
      cases huv with
      | inl hp' => exact Or.inl (Or.inr hp')
      | inr hrg => exact Or.inr hrg

theorem gpaco_final (F : MonoRel α) (r g : Rel α)
    (hr : Rel.le r F.gfp) (hg : Rel.le g F.gfp) :
    Rel.le (gpaco F r g) F.gfp :=
  Rel.sup_le (paco_final F (Rel.union r g) (Rel.sup_le hr hg)) hr

/-- Reflexive-transitive closure under an up-to operator `clo`. -/
inductive rclo (clo : Rel α → Rel α) (R : Rel α) : Rel α where
  | base {x y : α} (h : R x y) : rclo clo R x y
  | step {x y : α} (R' : Rel α) (hR' : Rel.le R' (rclo clo R)) (h : clo R' x y) : rclo clo R x y

/-- Compatibility of an up-to closure `clo` with `F`: `clo (F R) ≤ F (clo R)`. -/
def Compatible (F : MonoRel α) (clo : Rel α → Rel α) : Prop :=
  ∀ R : Rel α, Rel.le (clo (F.fn R)) (F.fn (clo R))

theorem gfp_closed_clo (F : MonoRel α) (clo : Rel α → Rel α)
    (hCompat : Compatible F clo) : Rel.le (clo F.gfp) F.gfp := by
  intro x y hClo
  have hPost : Rel.le (Rel.union (clo F.gfp) F.gfp) (F.fn (Rel.union (clo F.gfp) F.gfp)) := by
    apply Rel.sup_le
    · intro a b hab
      have h1 : clo (F.fn F.gfp) a b := F.gfp_fixed ▸ hab
      exact F.mono Rel.le_sup_left a b (hCompat F.gfp a b h1)
    · intro a b hab
      exact F.mono Rel.le_sup_right a b (F.gfp_unfold a b hab)
  exact F.le_gfp hPost x y (Or.inl hClo)

end GPacoCore

end Qsag.Paco

/-! ## 3. Polynomial `(Co)Algebra` Equivalence & Scar-Free Repair (`arXiv:2610.36669v1`) -/

namespace Qsag.Repair

set_option autoImplicit false

universe u v w w₁ w₂

/-- Polynomial endofunctor `P_{A, B}(X) := (a : A) × (B a → X)`. -/
abbrev PolyF (A : Type u) (B : A → Type v) (X : Type w) : Type (max u v w) :=
  (a : A) × (B a → X)

namespace PolyF

@[expose] def map {A : Type u} {B : A → Type v} {X : Type w₁} {Y : Type w₂}
    (f : X → Y) : PolyF A B X → PolyF A B Y
  | ⟨a, k⟩ => ⟨a, fun b => f (k b)⟩

@[simp] theorem map_id {A : Type u} {B : A → Type v} {X : Type w} (t : PolyF A B X) :
    PolyF.map (fun x => x) t = t := by
  cases t; rfl

theorem map_comp {A : Type u} {B : A → Type v} {X : Type w} {Y : Type w₁} {Z : Type w₂}
    (g : Y → Z) (f : X → Y) (t : PolyF A B X) :
    PolyF.map g (PolyF.map f t) = PolyF.map (fun x => g (f x)) t := by
  cases t; rfl

end PolyF

/-- Polynomial `P`-algebra `PolyF A B X → X`. -/
structure PAlg (A : Type u) (B : A → Type v) (X : Type w) where
  op : PolyF A B X → X

/-- Homomorphism of `P`-algebras `(X, α) → (Y, β)`. -/
structure PAlgHom {A : Type u} {B : A → Type v} {X : Type w₁} {Y : Type w₂}
    (α : PAlg A B X) (β : PAlg A B Y) where
  toFun : X → Y
  hom_comm : ∀ t : PolyF A B X, toFun (α.op t) = β.op (PolyF.map toFun t)

/-- Homotopy-initial `P`-algebra (`fold`, `fold_beta`, `fold_eta`). -/
structure InitPAlg (A : Type u) (B : A → Type v) (C : Type w) where
  alg : PAlg A B C
  fold : ∀ {Y : Type w}, PAlg A B Y → C → Y
  fold_beta : ∀ {Y : Type w} (γ : PAlg A B Y) (t : PolyF A B C),
    fold γ (alg.op t) = γ.op (PolyF.map (fold γ) t)
  fold_eta : ∀ {Y : Type w} (γ : PAlg A B Y) (h : C → Y),
    (∀ t : PolyF A B C, h (alg.op t) = γ.op (PolyF.map h t)) →
    ∀ x : C, h x = fold γ x

namespace InitPAlg

theorem fold_self {A : Type u} {B : A → Type v} {C : Type w}
    (I : InitPAlg A B C) (x : C) : I.fold I.alg x = x :=
  (I.fold_eta I.alg (fun c => c) (fun t => by simp [PolyF.map_id]) x).symm

def totalAlg {A : Type u} {B : A → Type v} {C : Type w}
    (I : InitPAlg A B C) (P : C → Type w)
    (cases : (a : A) → (k : B a → C) → ((b : B a) → P (k b)) → P (I.alg.op ⟨a, k⟩)) :
    PAlg A B ((x : C) × P x) where
  op := fun ⟨a, tk⟩ =>
    ⟨I.alg.op ⟨a, fun b => (tk b).1⟩, cases a (fun b => (tk b).1) (fun b => (tk b).2)⟩

def totalFold {A : Type u} {B : A → Type v} {C : Type w}
    (I : InitPAlg A B C) (P : C → Type w)
    (cases : (a : A) → (k : B a → C) → ((b : B a) → P (k b)) → P (I.alg.op ⟨a, k⟩)) :
    C → (x : C) × P x :=
  I.fold (I.totalAlg P cases)

theorem totalFold_fst {A : Type u} {B : A → Type v} {C : Type w}
    (I : InitPAlg A B C) (P : C → Type w)
    (cases : (a : A) → (k : B a → C) → ((b : B a) → P (k b)) → P (I.alg.op ⟨a, k⟩))
    (x : C) : (I.totalFold P cases x).1 = x := by
  have hfst : ∀ c : C, (I.totalFold P cases c).1 = I.fold I.alg c := by
    apply I.fold_eta I.alg (fun c => (I.totalFold P cases c).1)
    intro ⟨a, k⟩
    exact congrArg Sigma.fst (I.fold_beta (I.totalAlg P cases) ⟨a, k⟩)
  rw [hfst x, I.fold_self x]

/-- Total-space dependent eliminator derived from `InitPAlg` without univalence. -/
def elim {A : Type u} {B : A → Type v} {C : Type w}
    (I : InitPAlg A B C) (P : C → Type w)
    (cases : (a : A) → (k : B a → C) → ((b : B a) → P (k b)) → P (I.alg.op ⟨a, k⟩))
    (x : C) : P x :=
  I.totalFold_fst P cases x ▸ (I.totalFold P cases x).2

theorem elimProp {A : Type u} {B : A → Type v} {C : Type w}
    (I : InitPAlg A B C) (P : C → Prop)
    (cases : (a : A) → (k : B a → C) → ((b : B a) → P (k b)) → P (I.alg.op ⟨a, k⟩))
    (x : C) : P x := by
  let subAlg : PAlg A B { c : C // P c } :=
    { op := fun ⟨a, tk⟩ => ⟨I.alg.op ⟨a, fun b => (tk b).1⟩,
        cases a (fun b => (tk b).1) (fun b => (tk b).2)⟩ }
  let sect := I.fold subAlg
  have hfst : ∀ c : C, (sect c).1 = c := fun c =>
    (I.fold_eta I.alg (fun z => (sect z).1)
      (fun ⟨a, k⟩ => congrArg Subtype.val (I.fold_beta subAlg ⟨a, k⟩)) c).trans (I.fold_self c)
  exact hfst x ▸ (sect x).2

end InitPAlg

/-- Algebra configuration between carriers `C` and `D` (`arXiv:2610.36669v1` Definition 3.13). -/
abbrev AlgConfig (A : Type u) (B : A → Type v) (C D : Type w) :=
  InitPAlg A B C × InitPAlg A B D

namespace AlgConfig

abbrev forward {A : Type u} {B : A → Type v} {C D : Type w} (cfg : AlgConfig A B C D) : C → D :=
  cfg.1.fold cfg.2.alg

abbrev backward {A : Type u} {B : A → Type v} {C D : Type w} (cfg : AlgConfig A B C D) : D → C :=
  cfg.2.fold cfg.1.alg

theorem constr_ok {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : AlgConfig A B C D) (t : PolyF A B C) :
    cfg.forward (cfg.1.alg.op t) = cfg.2.alg.op (PolyF.map cfg.forward t) :=
  cfg.1.fold_beta cfg.2.alg t

/-- **Proposition 3.15 (`repair_by_instantiation`)**:
    Any `P`-algebra fold on `C` equals the *same* defining algebra `γ` folded on `D` after
    `cfg.forward`, justifying scar-free repair by re-instantiating `γ` directly on `D`. -/
theorem repair_by_instantiation {A : Type u} {B : A → Type v} {C D Y : Type w}
    (cfg : AlgConfig A B C D) (γ : PAlg A B Y) (x : C) :
    cfg.1.fold γ x = cfg.2.fold γ (cfg.forward x) := by
  symm
  apply cfg.1.fold_eta γ (fun c => cfg.2.fold γ (cfg.forward c))
  intro t
  rw [cfg.constr_ok, cfg.2.fold_beta γ, PolyF.map_comp]

theorem backward_forward {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : AlgConfig A B C D) (x : C) : cfg.backward (cfg.forward x) = x :=
  (cfg.repair_by_instantiation cfg.1.alg x).symm.trans (cfg.1.fold_self x)

theorem forward_backward {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : AlgConfig A B C D) (y : D) : cfg.forward (cfg.backward y) = y := by
  let symCfg : AlgConfig A B D C := (cfg.2, cfg.1)
  exact symCfg.backward_forward y

private theorem sigma_cast_symm {D : Type w} (P : D → Type w) {d₁ d₂ : D}
    (h : d₁ = d₂) (v : P d₂) :
    (⟨d₁, h.symm ▸ v⟩ : (y : D) × P y) = ⟨d₂, v⟩ := by
  cases h; rfl

private theorem elim_eq_of_sigma_eq {C D : Type w} (φ : C → D) (P : D → Type w)
    {x : C} {sc : (c : C) × P (φ c)} {sd : (d : D) × P d}
    (hPair : (⟨φ sc.1, sc.2⟩ : (d : D) × P d) = sd)
    (hc : sc.1 = x) (hd : sd.1 = φ x) :
    (hc ▸ sc.2 : P (φ x)) = (hd ▸ sd.2 : P (φ x)) := by
  rcases sc with ⟨c₀, pc⟩
  rcases sd with ⟨d₀, pd⟩
  dsimp only at hPair hc hd ⊢
  subst hc
  cases hPair
  cases hd
  rfl

abbrev pullbackCases {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : AlgConfig A B C D) (P : D → Type w)
    (casesD : (a : A) → (k : B a → D) → ((b : B a) → P (k b)) → P (cfg.2.alg.op ⟨a, k⟩)) :
    (a : A) → (k : B a → C) → ((b : B a) → P (cfg.forward (k b))) →
      P (cfg.forward (cfg.1.alg.op ⟨a, k⟩)) :=
  fun a k ih => (cfg.constr_ok ⟨a, k⟩).symm ▸ casesD a (fun b => cfg.forward (k b)) ih

/-- **Proposition 2.3(3) (`elim_repair_ok`)**:
    Dependent elimination over `C` equals native `D`-side dependent elimination at `cfg.forward x`. -/
theorem elim_repair_ok {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : AlgConfig A B C D) (P : D → Type w)
    (casesD : (a : A) → (k : B a → D) → ((b : B a) → P (k b)) → P (cfg.2.alg.op ⟨a, k⟩))
    (x : C) :
    cfg.1.elim (fun c => P (cfg.forward c)) (cfg.pullbackCases P casesD) x =
      cfg.2.elim P casesD (cfg.forward x) := by
  let casesC := cfg.pullbackCases P casesD
  let liftSigma : ((c : C) × P (cfg.forward c)) → ((d : D) × P d) :=
    fun ⟨c, pc⟩ => ⟨cfg.forward c, pc⟩
  have hPair :
      liftSigma (cfg.1.totalFold (fun c => P (cfg.forward c)) casesC x) =
        cfg.2.totalFold P casesD (cfg.forward x) := by
    have h₁ :
        liftSigma (cfg.1.totalFold (fun c => P (cfg.forward c)) casesC x) =
          cfg.1.fold (cfg.2.totalAlg P casesD) x := by
      apply cfg.1.fold_eta (cfg.2.totalAlg P casesD)
        (fun c => liftSigma (cfg.1.totalFold (fun z => P (cfg.forward z)) casesC c))
      intro ⟨a, k⟩
      dsimp only [InitPAlg.totalFold]
      rw [cfg.1.fold_beta]
      dsimp only [InitPAlg.totalAlg, liftSigma, PolyF.map, casesC, pullbackCases]
      exact sigma_cast_symm P
        (cfg.constr_ok ⟨a, fun b => (cfg.1.totalFold (fun z => P (cfg.forward z)) casesC (k b)).1⟩)
        (casesD a _ _)
    exact h₁.trans (cfg.repair_by_instantiation (cfg.2.totalAlg P casesD) x)
  exact elim_eq_of_sigma_eq cfg.forward P hPair
    (cfg.1.totalFold_fst (fun c => P (cfg.forward c)) casesC x)
    (cfg.2.totalFold_fst P casesD (cfg.forward x))

end AlgConfig

/-! ## 4. Polynomial Coalgebras (`PCoalg`), Finality (`FinalPCoalg`) & `CoalgConfig` -/

/-- Polynomial `P`-coalgebra `X → PolyF A B X`. -/
structure PCoalg (A : Type u) (B : A → Type v) (X : Type w) where
  out : X → PolyF A B X

namespace PCoalg

abbrev shape {A : Type u} {B : A → Type v} {X : Type w} (γ : PCoalg A B X) (x : X) : A :=
  (γ.out x).1

abbrev pos {A : Type u} {B : A → Type v} {X : Type w}
    (γ : PCoalg A B X) (x : X) : B (γ.shape x) → X :=
  (γ.out x).2

theorem out_eq_mk {A : Type u} {B : A → Type v} {X : Type w} (γ : PCoalg A B X) (x : X) :
    γ.out x = ⟨γ.shape x, γ.pos x⟩ := by
  rcases h : γ.out x with ⟨a, k⟩
  dsimp only [shape, pos]
  rw [h]

end PCoalg

/-- One-step polynomial bisimulation operator (`BisimStep`). -/
@[expose] def BisimStep {A : Type u} {B : A → Type v} {X : Type w}
    (γ : PCoalg A B X) (R : X → X → Prop) (x y : X) : Prop :=
  ∃ hShape : γ.shape x = γ.shape y,
    ∀ b : B (γ.shape x), R (γ.pos x b) (γ.pos y (hShape ▸ b))

/-- Coalgebraic bisimulation `R ≤ BisimStep γ R`. -/
abbrev Bisim (A : Type u) (B : A → Type v) {X : Type w}
    (γ : PCoalg A B X) (R : X → X → Prop) : Prop :=
  ∀ {x y : X}, R x y → BisimStep γ R x y

/-- Canonical `Paco.MonoRel` for `BisimStep γ`. -/
def BisimStep.toMonoRel {A : Type u} {B : A → Type v} {X : Type w}
    (γ : PCoalg A B X) : Qsag.Paco.MonoRel X where
  fn := BisimStep γ
  mono hRS _ _ := fun ⟨hs, hp⟩ => ⟨hs, fun b => hRS _ _ (hp b)⟩

theorem paco_bot_isBisim {A : Type u} {B : A → Type v} {X : Type w}
    (γ : PCoalg A B X) :
    Bisim A B γ (Qsag.Paco.paco (BisimStep.toMonoRel γ) Qsag.Paco.Rel.bot) := by
  intro x y hp
  obtain ⟨hs, hp'⟩ := Qsag.Paco.paco_unfold (BisimStep.toMonoRel γ) Qsag.Paco.Rel.bot x y hp
  exact ⟨hs, fun b => match hp' b with | .inl h => h | .inr hF => False.elim hF⟩

/-- Final `P`-coalgebra (`corec`, `corec_out`, `corec_uniq`). -/
structure FinalPCoalg (A : Type u) (B : A → Type v) (C : Type w) where
  coalg : PCoalg A B C
  corec : ∀ {E : Type w}, PCoalg A B E → E → C
  corec_out : ∀ {E : Type w} (δ : PCoalg A B E) (e : E),
    coalg.out (corec δ e) = PolyF.map (corec δ) (δ.out e)
  corec_uniq : ∀ {E : Type w} (δ : PCoalg A B E) (h : E → C),
    (∀ e : E, coalg.out (h e) = PolyF.map h (δ.out e)) →
    ∀ e : E, h e = corec δ e

namespace FinalPCoalg

theorem corec_shape {A : Type u} {B : A → Type v} {C E : Type w}
    (F : FinalPCoalg A B C) (δ : PCoalg A B E) (e : E) :
    F.coalg.shape (F.corec δ e) = δ.shape e :=
  congrArg Sigma.fst (F.corec_out δ e)

private theorem polyF_snd_of_eq {A : Type u} {B : A → Type v} {E C : Type w}
    (f : E → C) {p : PolyF A B C} {q : PolyF A B E}
    (h : p = PolyF.map f q) (b : B p.1) :
    p.2 b = f (q.2 (congrArg Sigma.fst h ▸ b)) := by
  cases q with
  | mk a k =>
    cases p with
    | mk a' k' =>
      dsimp only [PolyF.map] at h
      injection h with ha hk
      subst ha
      have hkEq : k' = fun x => f (k x) := eq_of_heq hk
      dsimp only
      rw [hkEq]

private theorem polyF_mk_cast {A : Type u} {B : A → Type v} {C : Type w}
    (p q : PolyF A B C) (h : p.1 = q.1) :
    q = ⟨p.1, fun b => q.2 (h ▸ b)⟩ := by
  cases p with
  | mk ap _ =>
    cases q with
    | mk aq _ =>
      dsimp only at h
      subst h
      rfl

theorem corec_pos {A : Type u} {B : A → Type v} {C E : Type w}
    (F : FinalPCoalg A B C) (δ : PCoalg A B E) (e : E)
    (b : B (F.coalg.shape (F.corec δ e))) :
    F.coalg.pos (F.corec δ e) b = F.corec δ (δ.pos e (F.corec_shape δ e ▸ b)) :=
  polyF_snd_of_eq (F.corec δ) (F.corec_out δ e) b

theorem corec_self {A : Type u} {B : A → Type v} {C : Type w}
    (F : FinalPCoalg A B C) (c : C) : F.corec F.coalg c = c :=
  (F.corec_uniq F.coalg (fun x => x) (fun x => (PolyF.map_id (F.coalg.out x)).symm) c).symm

/-- **Constructive Span Coinduction (`FinalPCoalg.coind`, `0 Classical.choice`)**:
    Derived purely from `FinalPCoalg` via the subtype span `{ p : C × C // R p.1 p.2 }` using
    `Prop` proof irrelevance on `hShape : shape u = shape v`. -/
theorem coind {A : Type u} {B : A → Type v} {C : Type w}
    (F : FinalPCoalg A B C) (R : C → C → Prop)
    (hBisim : Bisim A B F.coalg R) {x y : C} (hxy : R x y) : x = y := by
  let Span := { p : C × C // R p.1 p.2 }
  let spanCoalg : PCoalg A B Span :=
    { out := fun ⟨⟨u, v⟩, huv⟩ =>
        let hStep := hBisim huv
        ⟨F.coalg.shape u, fun b =>
          have hShape : F.coalg.shape u = F.coalg.shape v :=
            let ⟨hs, _⟩ := hStep; hs
          have hChild : R (F.coalg.pos u b) (F.coalg.pos v (hShape ▸ b)) :=
            let ⟨hs, hp⟩ := hStep
            (Subsingleton.elim hs hShape) ▸ hp b
          ⟨(F.coalg.pos u b, F.coalg.pos v (hShape ▸ b)), hChild⟩⟩ }
  have hFst : ∀ s : Span, s.1.1 = F.corec spanCoalg s :=
    F.corec_uniq spanCoalg (fun s => s.1.1) (fun ⟨⟨u, _⟩, _⟩ => F.coalg.out_eq_mk u)
  have hSnd : ∀ s : Span, s.1.2 = F.corec spanCoalg s := by
    apply F.corec_uniq spanCoalg (fun s => s.1.2)
    rintro ⟨⟨u, v⟩, huv⟩
    have hShape : F.coalg.shape u = F.coalg.shape v :=
      let ⟨hs, _⟩ := hBisim huv; hs
    exact polyF_mk_cast (F.coalg.out u) (F.coalg.out v) hShape
  exact (hFst ⟨(x, y), hxy⟩).trans (hSnd ⟨(x, y), hxy⟩).symm

theorem paco_eq {A : Type u} {B : A → Type v} {C : Type w}
    (F : FinalPCoalg A B C) {x y : C}
    (hp : Qsag.Paco.paco (BisimStep.toMonoRel F.coalg) Qsag.Paco.Rel.bot x y) : x = y :=
  F.coind _ (paco_bot_isBisim F.coalg) hp

end FinalPCoalg

/-- Coalgebra configuration between carriers `C` and `D` (`arXiv:2610.36669v1` Definition 4.12). -/
abbrev CoalgConfig (A : Type u) (B : A → Type v) (C D : Type w) :=
  FinalPCoalg A B C × FinalPCoalg A B D

namespace CoalgConfig

abbrev forward {A : Type u} {B : A → Type v} {C D : Type w} (cfg : CoalgConfig A B C D) : C → D :=
  cfg.2.corec cfg.1.coalg

abbrev backward {A : Type u} {B : A → Type v} {C D : Type w} (cfg : CoalgConfig A B C D) : D → C :=
  cfg.1.corec cfg.2.coalg

theorem destr_ok {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : CoalgConfig A B C D) (c : C) :
    cfg.2.coalg.out (cfg.forward c) = PolyF.map cfg.forward (cfg.1.coalg.out c) :=
  cfg.2.corec_out cfg.1.coalg c

theorem destr_shape_ok {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : CoalgConfig A B C D) (c : C) :
    cfg.2.coalg.shape (cfg.forward c) = cfg.1.coalg.shape c :=
  cfg.2.corec_shape cfg.1.coalg c

/-- **Proposition 4.19(3) (`corec_ok`)**:
    Corecursing into `C` followed by `cfg.forward` equals corecursing the same seed coalgebra `δ`
    directly into `D`. -/
theorem corec_ok {A : Type u} {B : A → Type v} {C D E : Type w}
    (cfg : CoalgConfig A B C D) (δ : PCoalg A B E) (e : E) :
    cfg.forward (cfg.1.corec δ e) = cfg.2.corec δ e := by
  apply cfg.2.corec_uniq δ (fun x => cfg.forward (cfg.1.corec δ x))
  intro x
  rw [cfg.destr_ok, cfg.1.corec_out, PolyF.map_comp]

theorem backward_forward {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : CoalgConfig A B C D) (c : C) : cfg.backward (cfg.forward c) = c := by
  let symCfg : CoalgConfig A B D C := (cfg.2, cfg.1)
  exact (symCfg.corec_ok cfg.1.coalg c).trans (cfg.1.corec_self c)

theorem forward_backward {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : CoalgConfig A B C D) (d : D) : cfg.forward (cfg.backward d) = d :=
  (cfg.corec_ok cfg.2.coalg d).trans (cfg.2.corec_self d)

abbrev pushRel {C D : Type w} (φ : C → D) (R : C → C → Prop) (d₁ d₂ : D) : Prop :=
  ∃ c₁ c₂ : C, φ c₁ = d₁ ∧ φ c₂ = d₂ ∧ R c₁ c₂

theorem pushRel_step {C D : Type w} (φ : C → D) (R : C → C → Prop) {x y : C} (r : R x y) :
    pushRel φ R (φ x) (φ y) :=
  ⟨x, y, rfl, rfl, r⟩

private theorem cast_trans_eq {A : Type u} {B : A → Type v}
    {a₁ a₂ a₃ a₄ : A} (h₁₂ : a₁ = a₂) (h₂₄ : a₂ = a₄) (h₁₃ : a₁ = a₃) (h₃₄ : a₃ = a₄)
    (b : B a₁) :
    h₃₄ ▸ (h₁₃ ▸ b) = h₂₄ ▸ (h₁₂ ▸ b) := by
  subst h₁₂; subst h₂₄; subst h₁₃
  have h : h₃₄ = rfl := Subsingleton.elim _ _
  rw [h]

theorem pushRel_isBisim {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : CoalgConfig A B C D) (R : C → C → Prop) (hB : Bisim A B cfg.1.coalg R) :
    Bisim A B cfg.2.coalg (pushRel cfg.forward R) := by
  rintro d₁ d₂ ⟨c₁, c₂, rfl, rfl, hrc⟩
  obtain ⟨hShapeC, hPosC⟩ := hB hrc
  have hs₁ := cfg.destr_shape_ok c₁
  have hs₂ := cfg.destr_shape_ok c₂
  have hShapeD : cfg.2.coalg.shape (cfg.forward c₁) = cfg.2.coalg.shape (cfg.forward c₂) :=
    hs₁.trans (hShapeC.trans hs₂.symm)
  refine ⟨hShapeD, fun b => ?_⟩
  let b₁ : B (cfg.1.coalg.shape c₁) := hs₁ ▸ b
  have hp₁ := cfg.2.corec_pos cfg.1.coalg c₁ b
  have hp₂ := cfg.2.corec_pos cfg.1.coalg c₂ (hShapeD ▸ b)
  have hbEq : (hs₂ ▸ (hShapeD ▸ b)) = (hShapeC ▸ b₁) :=
    cast_trans_eq hs₁ hShapeC hShapeD hs₂ b
  refine ⟨cfg.1.coalg.pos c₁ b₁, cfg.1.coalg.pos c₂ (hShapeC ▸ b₁), hp₁.symm, ?_, hPosC b₁⟩
  rw [hp₂, hbEq]

/-- **Proposition 4.19(4) (`coind_ok`)**:
    Coinduction on `C` pushed along `cfg.forward` agrees with `D`-side coinduction on the
    pushed-forward bisimulation `pushRel cfg.forward R`. -/
theorem coind_ok {A : Type u} {B : A → Type v} {C D : Type w}
    (cfg : CoalgConfig A B C D) (R : C → C → Prop) (hB : Bisim A B cfg.1.coalg R)
    {x y : C} (r : R x y) :
    congrArg cfg.forward (cfg.1.coind R hB r) =
      cfg.2.coind (pushRel cfg.forward R) (cfg.pushRel_isBisim R hB)
        (pushRel_step cfg.forward R r) :=
  Subsingleton.elim _ _

end CoalgConfig

end Qsag.Repair

end

/-! ## 5. Constructive Elaboration Guards, `gpaco_step` & `#assert_no_scar` -/

public meta section
namespace Qsag.Tactic.CathedralKit
open Lean Meta Elab Tactic Command

/-- Synthesize `[Decidable cond]` constructively, returning `none` if no instance exists or if the
    synthesized instance transitively touches `Classical.choice` (`Classical.propDecidable`). -/
def synthConstructiveDecidable? (cond : Expr) : MetaM (Option Expr) := do
  let decTy ← mkAppM ``Decidable #[cond]
  let some inst ← synthInstance? decTy | return none
  let inst ← instantiateMVars inst
  let used := inst.getUsedConstants
  if used.contains ``Classical.choice || used.contains ``Classical.propDecidable then
    return none
  for c in used do
    let axs ← Lean.collectAxioms c
    if axs.any (fun ax => ax != ``propext && ax != ``Quot.sound) then
      return none
  return some inst

/-- Collect the transitive constant cone of `root` in `env` (`setExporting false`) up to `fuel`
    BFS rounds (`0 partial`). Returns `true` iff `forbidden` appears anywhere in a type or value. -/
private def dependsOnConstAux (env : Environment) (forbidden : Name) :
    Nat → List Name → NameSet → Bool
  | 0, _, _ => false
  | _, [], _ => false
  | fuel + 1, n :: rest, seen =>
    if n == forbidden then true
    else if seen.contains n then dependsOnConstAux env forbidden fuel rest seen
    else
      let seen' := seen.insert n
      let nexts : List Name :=
        match env.find? n with
        | none => []
        | some ci =>
          let tyDeps := ci.type.getUsedConstants.toList
          let valDeps := match ci.value? (allowOpaque := true) with
            | some v => v.getUsedConstants.toList
            | none => []
          tyDeps ++ valDeps
      if nexts.contains forbidden then true
      else dependsOnConstAux env forbidden fuel (rest ++ nexts) seen'

/-- Verify at elaboration time that none of `targets` transitively reference `retired` in their
    kernel type or proof/definition body (`0` repair scars). -/
syntax (name := assertNoScarCmd) "#assert_no_scar " ident " in " ident+ : command
elab_rules : command
  | `(command| #assert_no_scar $retId:ident in $[$tgtIds:ident]*) => do
    let retired ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo retId
    let env := (← getEnv).setExporting false
    for tgtId in tgtIds do
      let tgt ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo tgtId
      if dependsOnConstAux env retired 8192 [tgt] {} then
        throwErrorAt tgtId "scar audit failed: `{tgt}` transitively references retired `{retired}`"

/-- Step a `Qsag.Paco.gpaco` or `Qsag.Paco.paco` goal by folding one `MonoRel` transition. -/
elab "gpaco_step" : tactic => do
  evalTactic (← `(tactic| first
    | refine Qsag.Paco.gpaco_fold _ _ _ _ _ ?_
    | refine Qsag.Paco.paco_fold _ _ _ _ ?_
    | (left; refine Qsag.Paco.paco_fold _ _ _ _ ?_)))

end Qsag.Tactic.CathedralKit
end

#verify_constructive
  Qsag.Paco.MonoRel.gfp_fixed
  Qsag.Paco.paco_acc
  Qsag.Paco.paco_final
  Qsag.Paco.gpaco_acc
  Qsag.Paco.gpaco_coind
  Qsag.Paco.gpaco_final
  Qsag.Paco.gfp_closed_clo
  Qsag.Repair.AlgConfig.repair_by_instantiation
  Qsag.Repair.AlgConfig.backward_forward
  Qsag.Repair.AlgConfig.forward_backward
  Qsag.Repair.AlgConfig.elim_repair_ok
  Qsag.Repair.FinalPCoalg.coind
  Qsag.Repair.FinalPCoalg.paco_eq
  Qsag.Repair.CoalgConfig.corec_ok
  Qsag.Repair.CoalgConfig.pushRel_isBisim
  Qsag.Repair.CoalgConfig.coind_ok

public section
namespace Qsag.CathedralKitRegression
set_option autoImplicit false

inductive RetiredFlag where | off | on
def scarredFn : Nat → Nat := fun n => match RetiredFlag.off with | .off => n | .on => n + 1
def cleanFn : Nat → Nat := fun n => n

#assert_no_scar RetiredFlag in cleanFn

/-- error: scar audit failed: `Qsag.CathedralKitRegression.scarredFn` transitively references retired `Qsag.CathedralKitRegression.RetiredFlag` -/
#guard_msgs in
#assert_no_scar RetiredFlag in scarredFn

end Qsag.CathedralKitRegression
end

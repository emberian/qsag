module
/-
# Qsag.Spec.GameBound — State-Separating Oracle Packages and Concrete Reduction Calculus

Layer-0 cryptographic reduction framework (`CryptHOL` / `SSProve` style) providing:
1. Typed query/response oracle interfaces (`Iface`) and free oracle programs (`Code E R`) with
   constructive per-path query-budget verification (`WithinBudget`),
2. State-separating oracle packages (`Pkg I E σ`) with sequential linking (`Pkg.link`) and
   independent-state parallel composition (`Pkg.par`), and
3. Exact finite-sample-space security games (`FinGame n`), rational distinguishing advantage
   (`AdvDist`), concrete reduction inequalities (`GameBound`), triangle/hybrid chains,
   until-bad game hops (`adv_until_bad`), and constructive witness-extraction bounds.
-/

public import Qsag.Spec.Primitives
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spec

set_option autoImplicit false

/-! ## 1. Oracle Interfaces, Free Oracle Programs, and Query Budgets (`Within`) -/

/-- Typed oracle interface specifying query type `Query` and query-dependent response family `Resp`. -/
structure Iface : Type 1 where
  Query : Type
  Resp : Query → Type

/-- Empty oracle interface (closed package export/import boundary). -/
@[expose] def Iface.empty : Iface where
  Query := PEmpty
  Resp e := PEmpty.elim e

/-- Disjoint sum of two oracle interfaces (`E₁ ⊕ E₂`) for parallel package composition. -/
@[expose] def Iface.sum (E₁ E₂ : Iface) : Iface where
  Query := PSum E₁.Query E₂.Query
  Resp
    | .inl q₁ => E₁.Resp q₁
    | .inr q₂ => E₂.Resp q₂

/-- Constructive free monad of oracle-calling computations over interface `E` returning `R`. -/
inductive Code (E : Iface) (R : Type) : Type 1 where
  | ret (val : R) : Code E R
  | call (q : E.Query) (k : E.Resp q → Code E R) : Code E R

/-- Monadic sequential composition for `Code E`. -/
def Code.bind {E : Iface} {A B : Type} : Code E A → (A → Code E B) → Code E B
  | .ret a, f => f a
  | .call q k, f => .call q (fun r => Code.bind (k r) f)

theorem Code.bind_ret {E : Iface} {A : Type} :
    ∀ (c : Code E A), Code.bind c Code.ret = c
  | .ret _ => rfl
  | .call q k => congrArg (Code.call q) (funext fun r => Code.bind_ret (k r))

theorem Code.bind_assoc {E : Iface} {A B C : Type} :
    ∀ (c : Code E A) (f : A → Code E B) (g : B → Code E C),
      Code.bind (Code.bind c f) g = Code.bind c (fun a => Code.bind (f a) g)
  | .ret _, _, _ => rfl
  | .call q k, f, g =>
    congrArg (Code.call q) (funext fun r => Code.bind_assoc (k r) f g)

/-- Evaluate `Code E R` against a deterministic stateful oracle handler `σ → (q : E.Query) → E.Resp q × σ`. -/
def Code.evalState {E : Iface} {R σ : Type}
    (handler : σ → (q : E.Query) → E.Resp q × σ) :
    Code E R → σ → R × σ
  | .ret val, st => (val, st)
  | .call q k, st =>
    let (resp, st') := handler st q
    Code.evalState handler (k resp) st'

/-- Evaluate a closed `Code Iface.empty R` program to its pure result `R` (`0` oracle calls). -/
def Code.evalClosed {R : Type} : Code Iface.empty R → R
  | .ret val => val
  | .call q _ => PEmpty.elim q

/-- Constructive worst-case query budget predicate (`Within qBudget c`): along every oracle
    response branch, `c` issues at most `qBudget` oracle calls. -/
inductive Within {E : Iface} {R : Type} : Nat → Code E R → Prop where
  | ret (b : Nat) (v : R) : Within b (.ret v)
  | call {b : Nat} (q : E.Query) (k : E.Resp q → Code E R) :
      (∀ r : E.Resp q, Within b (k r)) →
      Within (b + 1) (.call q k)

theorem Within.mono {E : Iface} {R : Type} :
    ∀ {b₁ b₂ : Nat} {c : Code E R}, b₁ ≤ b₂ → Within b₁ c → Within b₂ c
  | _, b₂, .ret v, _, .ret _ _ => .ret b₂ v
  | _ + 1, _ + 1, .call q k, hLe, .call _ _ hk =>
    .call q k (fun r => Within.mono (Nat.le_of_succ_le_succ hLe) (hk r))
  | _ + 1, 0, .call _ _, hLe, _ => False.elim (Nat.not_succ_le_zero _ hLe)

theorem Within.bind {E : Iface} {A B : Type} :
    ∀ {b₁ b₂ : Nat} {c : Code E A} {f : A → Code E B},
      Within b₁ c → (∀ a : A, Within b₂ (f a)) → Within (b₁ + b₂) (Code.bind c f)
  | _, _, .ret a, _, .ret _ _, hf => Within.mono (Nat.le_add_left _ _) (hf a)
  | b₁ + 1, b₂, .call q k, _, .call _ _ hk, hf => by
    have hEq : (b₁ + 1) + b₂ = (b₁ + b₂) + 1 := Nat.succ_add b₁ b₂
    rw [hEq]
    exact .call q _ (fun r => Within.bind (hk r) hf)

/-! ## 2. State-Separating Oracle Packages (`Pkg`, `Pkg.link`, `Pkg.par`) -/

/-- State-separating oracle package implementing export interface `I` using import interface `E`
    over private state `σ`. -/
structure Pkg (I E : Iface) (σ : Type) : Type 1 where
  init : σ
  handle : σ → (q : I.Query) → Code E (I.Resp q × σ)

/-- Interpret a single query of `M` against `Q : Pkg M E σ₂` while threading `Q`'s private state. -/
def Code.linkPkg {M E : Iface} {R σ₂ : Type} (Q : Pkg M E σ₂) :
    Code M R → σ₂ → Code E (R × σ₂)
  | .ret r, s₂ => .ret (r, s₂)
  | .call q k, s₂ =>
    Code.bind (Q.handle s₂ q) (fun (resp, s₂') => Code.linkPkg Q (k resp) s₂')

/-- Sequential composition (`P ∘ Q`): link upper package `P : Pkg I M σ₁` with lower package
    `Q : Pkg M E σ₂` over separated product state `σ₁ × σ₂`. -/
def Pkg.link {I M E : Iface} {σ₁ σ₂ : Type}
    (P : Pkg I M σ₁) (Q : Pkg M E σ₂) : Pkg I E (σ₁ × σ₂) where
  init := (P.init, Q.init)
  handle st q :=
    Code.bind (Code.linkPkg Q (P.handle st.1 q) st.2)
      (fun ((resp, s₁'), s₂') => .ret (resp, (s₁', s₂')))

/-- Parallel composition (`P₁ ⊗ P₂`): combine two packages `P₁ : Pkg I₁ E σ₁` and `P₂ : Pkg I₂ E σ₂`
    with disjoint private states `σ₁` and `σ₂` sharing import interface `E`. -/
def Pkg.par {I₁ I₂ E : Iface} {σ₁ σ₂ : Type}
    (P₁ : Pkg I₁ E σ₁) (P₂ : Pkg I₂ E σ₂) :
    Pkg (Iface.sum I₁ I₂) E (σ₁ × σ₂) where
  init := (P₁.init, P₂.init)
  handle st q :=
    match q with
    | .inl q₁ =>
      Code.bind (P₁.handle st.1 q₁) (fun (r₁, s₁') => .ret (r₁, (s₁', st.2)))
    | .inr q₂ =>
      Code.bind (P₂.handle st.2 q₂) (fun (r₂, s₂') => .ret (r₂, (st.1, s₂')))

/-- State-separation non-interference for `Pkg.par`: a left-interface query `.inl q₁` never mutates
    the right package's private state `st.2` along any evaluation against any deterministic `E`-handler! -/
theorem Pkg.par_left_preserves_right {I₁ I₂ E : Iface} {σ₁ σ₂ τ : Type}
    (P₁ : Pkg I₁ E σ₁) (P₂ : Pkg I₂ E σ₂)
    (env : τ → (q : E.Query) → E.Resp q × τ)
    (s₁ : σ₁) (s₂ : σ₂) (t : τ) (q₁ : I₁.Query) :
    ((Code.evalState env ((P₁.par P₂).handle (s₁, s₂) (.inl q₁)) t).1.2).2 = s₂ := by
  dsimp only [Pkg.par]
  generalize P₁.handle s₁ q₁ = c
  induction c generalizing t with
  | ret pair => rfl
  | call q k ih =>
    dsimp only [Code.bind, Code.evalState]
    exact ih (env t q).1 (env t q).2

/-- Symmetric state-separation non-interference: `.inr q₂` never mutates `st.1`. -/
theorem Pkg.par_right_preserves_left {I₁ I₂ E : Iface} {σ₁ σ₂ τ : Type}
    (P₁ : Pkg I₁ E σ₁) (P₂ : Pkg I₂ E σ₂)
    (env : τ → (q : E.Query) → E.Resp q × τ)
    (s₁ : σ₁) (s₂ : σ₂) (t : τ) (q₂ : I₂.Query) :
    ((Code.evalState env ((P₁.par P₂).handle (s₁, s₂) (.inr q₂)) t).1.2).1 = s₁ := by
  dsimp only [Pkg.par]
  generalize P₂.handle s₂ q₂ = c
  induction c generalizing t with
  | ret pair => rfl
  | call q k ih =>
    dsimp only [Code.bind, Code.evalState]
    exact ih (env t q).1 (env t q).2

/-! ## 3. Finite-Sample-Space Games, Advantage, and Reduction Calculus (`GameBound`) -/

/-- Exact finite-sample-space security game over `Fin n` (`0 < n`) with decidable win predicate `win`. -/
structure FinGame (n : Nat) where
  samplePos : 0 < n
  win : Fin n → Bool

/-- Exact structural finite sum `∑_{i < n} f i` over `Fin n`. -/
def sampleSum : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f ⟨0, Nat.zero_lt_succ n⟩ + sampleSum n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

/-- Exact count of winning sample points `|{ω ∈ Fin n | G.win ω = true}|`. -/
def FinGame.winCount {n : Nat} (G : FinGame n) : Nat :=
  sampleSum n (fun ω => if G.win ω then 1 else 0)

/-- Exact rational winning probability `winCount / n` in canonical `Spec.RatBound`. -/
@[expose] def FinGame.winProb {n : Nat} (G : FinGame n) : RatBound :=
  ⟨G.winCount, n, G.samplePos⟩

/-- Exact distinguishing advantage `|Pr[G₀ wins] - Pr[G₁ wins]| = |winCount G₀ - winCount G₁| / n`. -/
@[expose] def AdvDist {n : Nat} (G₀ G₁ : FinGame n) : RatBound :=
  ⟨natAbsDiff G₀.winCount G₁.winCount, n, G₀.samplePos⟩

/-- Concrete security reduction judgment: advantage `adv` is bounded above by `ε` (`adv ≤ ε`). -/
@[expose] def GameBound (adv ε : RatBound) : Prop :=
  adv.le ε

theorem GameBound.refl (adv : RatBound) : GameBound adv adv :=
  RatBound.le_refl adv

theorem GameBound.trans {adv ε₁ ε₂ : RatBound}
    (h₁ : GameBound adv ε₁) (h₂ : ε₁.le ε₂) : GameBound adv ε₂ :=
  RatBound.le_trans h₁ h₂

theorem GameBound.atLeastBits {b : Nat} {adv ε : RatBound}
    (hBound : GameBound adv ε) (hBits : ε.atLeastBits b) : adv.atLeastBits b :=
  RatBound.atLeastBits_of_le hBound hBits

private theorem qsum_le_qsum :
    ∀ (n : Nat) (f g : Fin n → Nat),
      (∀ i : Fin n, f i ≤ g i) →
      sampleSum n f ≤ sampleSum n g
  | 0, _, _, _ => Nat.le_refl 0
  | n + 1, f, g, hLe => by
    unfold sampleSum
    exact Nat.add_le_add (hLe ⟨0, Nat.zero_lt_succ n⟩)
      (qsum_le_qsum n _ _ (fun i => hLe ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))

private theorem qsum_add_eq :
    ∀ (n : Nat) (f g : Fin n → Nat),
      sampleSum n (fun i => f i + g i) = sampleSum n f + sampleSum n g
  | 0, _, _ => rfl
  | n + 1, f, g => by
    unfold sampleSum
    dsimp only
    rw [qsum_add_eq n]
    omega

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

private theorem natAbsDiff_add_same (b : Bool) (sp sq : Nat) :
    natAbsDiff ((if b then 1 else 0) + sp) ((if b then 1 else 0) + sq) =
      natAbsDiff sp sq := by
  cases b <;> unfold natAbsDiff
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
  · simp only [↓reduceIte]
    by_cases h1 : sp ≤ sq
    · have h2 : 1 + sp ≤ 1 + sq := by omega
      rw [ite_true h1, ite_true h2]
      omega
    · have h2 : ¬ (1 + sp ≤ 1 + sq) := by omega
      rw [ite_false h1, ite_false h2]
      omega

private theorem natAbsDiff_add_bad (b₁ b₂ : Bool) (sp sq sb : Nat)
    (ih : natAbsDiff sp sq ≤ sb) :
    natAbsDiff ((if b₁ then 1 else 0) + sp) ((if b₂ then 1 else 0) + sq) ≤ 1 + sb := by
  cases b₁ <;> cases b₂ <;> unfold natAbsDiff at ih ⊢
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases h1 : sp ≤ sq
    · rw [ite_true h1] at ih
      have h2 : 0 + sp ≤ 0 + sq := by omega
      rw [ite_true h2]; omega
    · rw [ite_false h1] at ih
      have h2 : ¬ (0 + sp ≤ 0 + sq) := by omega
      rw [ite_false h2]; omega
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases h1 : sp ≤ sq
    · rw [ite_true h1] at ih
      have h2 : 0 + sp ≤ 1 + sq := by omega
      rw [ite_true h2]; omega
    · rw [ite_false h1] at ih
      by_cases h2 : 0 + sp ≤ 1 + sq
      · rw [ite_true h2]; omega
      · rw [ite_false h2]; omega
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases h1 : sp ≤ sq
    · rw [ite_true h1] at ih
      by_cases h2 : 1 + sp ≤ 0 + sq
      · rw [ite_true h2]; omega
      · rw [ite_false h2]; omega
    · rw [ite_false h1] at ih
      have h2 : ¬ (1 + sp ≤ 0 + sq) := by omega
      rw [ite_false h2]; omega
  · simp only [↓reduceIte]
    by_cases h1 : sp ≤ sq
    · rw [ite_true h1] at ih
      have h2 : 1 + sp ≤ 1 + sq := by omega
      rw [ite_true h2]; omega
    · rw [ite_false h1] at ih
      have h2 : ¬ (1 + sp ≤ 1 + sq) := by omega
      rw [ite_false h2]; omega

private theorem natAbsDiff_qsum_le :
    ∀ (n : Nat) (p q bad : Fin n → Bool),
      (∀ i : Fin n, bad i = false → p i = q i) →
      natAbsDiff (sampleSum n (fun i => if p i then 1 else 0))
        (sampleSum n (fun i => if q i then 1 else 0)) ≤
        sampleSum n (fun i => if bad i then 1 else 0)
  | 0, _, _, _, _ => Nat.le_refl 0
  | n + 1, p, q, bad, hEq => by
    unfold sampleSum
    dsimp only
    have ih := natAbsDiff_qsum_le n
      (fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
      (fun i => q ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
      (fun i => bad ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
      (fun i hb => hEq ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ hb)
    generalize sampleSum n (fun i => if p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ then 1 else 0) = sp at ih ⊢
    generalize sampleSum n (fun i => if q ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ then 1 else 0) = sq at ih ⊢
    generalize sampleSum n (fun i => if bad ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ then 1 else 0) = sb at ih ⊢
    cases hb : bad ⟨0, Nat.zero_lt_succ n⟩
    · have hpq : p ⟨0, Nat.zero_lt_succ n⟩ = q ⟨0, Nat.zero_lt_succ n⟩ := hEq _ hb
      rw [hpq, natAbsDiff_add_same]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      exact ih
    · simp only [↓reduceIte]
      exact natAbsDiff_add_bad _ _ _ _ _ ih

/-- Reflexive distinguishing advantage is `0`. -/
theorem adv_refl {n : Nat} (G : FinGame n) : GameBound (AdvDist G G) RatBound.zero := by
  unfold GameBound RatBound.le AdvDist RatBound.zero natAbsDiff
  dsimp only
  simp only [Nat.le_refl, ↓reduceIte, Nat.sub_self, Nat.zero_mul]

/-- Symmetry of distinguishing advantage: `AdvDist G₀ G₁ = AdvDist G₁ G₀`. -/
theorem adv_symm {n : Nat} (G₀ G₁ : FinGame n) : AdvDist G₀ G₁ = AdvDist G₁ G₀ := by
  apply RatBound.ext
  · exact natAbsDiff_comm G₀.winCount G₁.winCount
  · rfl

/-- Triangle inequality for game hops: `Adv(G₀, G₂) ≤ Adv(G₀, G₁) + Adv(G₁, G₂)`. -/
theorem adv_triangle {n : Nat} (G₀ G₁ G₂ : FinGame n) :
    GameBound (AdvDist G₀ G₂) ((AdvDist G₀ G₁).add (AdvDist G₁ G₂)) := by
  unfold GameBound RatBound.le AdvDist RatBound.add
  dsimp only
  have hTri := natAbsDiff_triangle G₀.winCount G₁.winCount G₂.winCount
  have hL : natAbsDiff G₀.winCount G₂.winCount * (n * n) ≤
      (natAbsDiff G₀.winCount G₁.winCount + natAbsDiff G₁.winCount G₂.winCount) * (n * n) :=
    Nat.mul_le_mul_right (n * n) hTri
  have hR : (natAbsDiff G₀.winCount G₁.winCount + natAbsDiff G₁.winCount G₂.winCount) * (n * n) =
      (natAbsDiff G₀.winCount G₁.winCount * n + natAbsDiff G₁.winCount G₂.winCount * n) * n := by
    rw [Nat.right_distrib, Nat.right_distrib, Nat.mul_assoc, Nat.mul_assoc]
  rw [← hR]
  exact hL

/-- Multi-step hybrid argument over `k` game hops: if each adjacent hop `H i ↦ H (i + 1)` has
    `AdvDist ≤ stepBound`, then `AdvDist (H 0) (H k) ≤ k · stepBound`. -/
theorem adv_hybrid {n : Nat} (hPos : 0 < n) (stepBound : RatBound) :
    ∀ (k : Nat) (H : Nat → FinGame n),
      (∀ i : Nat, i < k → GameBound (AdvDist (H i) (H (i + 1))) stepBound) →
      GameBound (AdvDist (H 0) (H k)) (stepBound.scale k)
  | 0, H, _ => by
    unfold GameBound RatBound.le AdvDist RatBound.scale
    dsimp only
    have hZ : natAbsDiff (H 0).winCount (H 0).winCount = 0 := by
      unfold natAbsDiff; simp
    rw [hZ, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul]
    exact Nat.le_refl 0
  | k + 1, H, hStep => by
    have ih := adv_hybrid hPos stepBound k H (fun i hi => hStep i (Nat.lt_succ_of_lt hi))
    have hk := hStep k (Nat.lt_succ_self k)
    have hTri := adv_triangle (H 0) (H k) (H (k + 1))
    have hSum := RatBound.add_le_add ih hk
    have hChain := RatBound.le_trans hTri hSum
    unfold RatBound.le RatBound.add RatBound.scale at hChain
    unfold GameBound RatBound.le RatBound.scale
    dsimp only at hChain ⊢
    have hDenEq : (AdvDist (H 0) (H (k + 1))).den = n := rfl
    rw [hDenEq] at hChain ⊢
    have hFactorR : ((k * stepBound.num) * stepBound.den + stepBound.num * stepBound.den) * n =
        (((k + 1) * stepBound.num) * n) * stepBound.den := by
      have h1 : (k * stepBound.num) * stepBound.den + stepBound.num * stepBound.den =
          ((k + 1) * stepBound.num) * stepBound.den := by
        rw [Nat.succ_mul, Nat.right_distrib]
      rw [h1, Nat.mul_assoc, Nat.mul_comm stepBound.den n, ← Nat.mul_assoc]
    rw [hFactorR, ← Nat.mul_assoc ((AdvDist (H 0) (H (k + 1))).num)] at hChain
    exact nat_le_of_mul_le_mul_right hChain stepBound.den_pos

/-- **Fundamental Until-Bad Lemma (`adv_until_bad`)**:
    If `G₀` and `G₁` produce identical verdicts on every sample point `ω` where `bad ω = false`,
    then `AdvDist G₀ G₁ ≤ Pr[bad]`. -/
theorem adv_until_bad {n : Nat} (G₀ G₁ : FinGame n) (bad : Fin n → Bool)
    (hIdentical : ∀ ω : Fin n, bad ω = false → G₀.win ω = G₁.win ω) :
    GameBound (AdvDist G₀ G₁) (FinGame.mk G₀.samplePos bad).winProb := by
  unfold GameBound RatBound.le AdvDist FinGame.winProb FinGame.winCount
  dsimp only
  exact Nat.mul_le_mul_right n (natAbsDiff_qsum_le n G₀.win G₁.win bad hIdentical)

/-- **Constructive Witness-Extraction Monotonicity (`event_le_reduction_win`)**:
    If every winning tape `ω` of `G₀` constructively implies a win in reduction `R`
    (`G₀.win ω = true → R.win ω = true`), then `Pr[G₀ wins] ≤ Pr[R wins]`. -/
theorem event_le_reduction_win {n : Nat} (G₀ R : FinGame n)
    (hExtract : ∀ ω : Fin n, G₀.win ω = true → R.win ω = true) :
    GameBound G₀.winProb R.winProb := by
  unfold GameBound RatBound.le FinGame.winProb FinGame.winCount
  dsimp only
  apply Nat.mul_le_mul_right n
  apply qsum_le_qsum
  intro ω
  cases hg : G₀.win ω
  · exact Nat.zero_le _
  · rw [hExtract ω hg]
    exact Nat.le_refl 1

/-- **Disjunctive Witness-Extraction Union Bound (`event_le_two_reductions`)**:
    If every winning tape `ω` of `G₀` yields either a win in `R₁` or a win in `R₂`,
    then `Pr[G₀ wins] ≤ Pr[R₁ wins] + Pr[R₂ wins]`. -/
theorem event_le_two_reductions {n : Nat} (G₀ R₁ R₂ : FinGame n)
    (hExtract : ∀ ω : Fin n, G₀.win ω = true → R₁.win ω = true ∨ R₂.win ω = true) :
    GameBound G₀.winProb (R₁.winProb.add R₂.winProb) := by
  unfold GameBound RatBound.le FinGame.winProb FinGame.winCount RatBound.add
  dsimp only
  have hCountLe :
      sampleSum n (fun ω => if G₀.win ω then 1 else 0) ≤
        sampleSum n (fun ω => if R₁.win ω then 1 else 0) +
          sampleSum n (fun ω => if R₂.win ω then 1 else 0) := by
    rw [← qsum_add_eq]
    apply qsum_le_qsum
    intro ω
    cases hg : G₀.win ω
    · exact Nat.zero_le _
    · rcases hExtract ω hg with h1 | h2
      · rw [h1]; omega
      · rw [h2]; omega
  have hScaled := Nat.mul_le_mul_right (n * n) hCountLe
  have hRearr :
      (sampleSum n (fun ω => if R₁.win ω then 1 else 0) +
        sampleSum n (fun ω => if R₂.win ω then 1 else 0)) * (n * n) =
      (sampleSum n (fun ω => if R₁.win ω then 1 else 0) * n +
        sampleSum n (fun ω => if R₂.win ω then 1 else 0) * n) * n := by
    rw [Nat.right_distrib, Nat.right_distrib, Nat.mul_assoc, Nat.mul_assoc]
  rw [← hRearr]
  exact hScaled

#verify_constructive
  Qsag.Spec.Code.bind_ret
  Qsag.Spec.Code.bind_assoc
  Qsag.Spec.Within.mono
  Qsag.Spec.Within.bind
  Qsag.Spec.Pkg.par_left_preserves_right
  Qsag.Spec.Pkg.par_right_preserves_left
  Qsag.Spec.GameBound.refl
  Qsag.Spec.GameBound.trans
  Qsag.Spec.GameBound.atLeastBits
  Qsag.Spec.adv_refl
  Qsag.Spec.adv_symm
  Qsag.Spec.adv_triangle
  Qsag.Spec.adv_hybrid
  Qsag.Spec.adv_until_bad
  Qsag.Spec.event_le_reduction_win
  Qsag.Spec.event_le_two_reductions

end Qsag.Spec
end

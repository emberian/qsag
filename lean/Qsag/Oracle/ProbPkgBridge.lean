module
/-
# Qsag.Oracle.ProbPkgBridge — probabilistic packages, concurrent sessions, and the three bridges

`Spec.GameBound.Pkg`, `Spec.Refines.Machine` and `Qsag.OracleComp` (`Oracle.Qrom`) each had their own notion
of "system the adversary talks to". This module gives them one: a closed package is a
deterministic handler (`Pkg.closedHandler`), a distinguisher is an adaptive oracle program
`Code I Bool`, and a probabilistic package `ProbPkg n I E σ` is a family of packages indexed by
a coin `ω : Fin n` drawn once, uniformly. All advantages are exact counts over `Fin n`.

§1  Counting over `Fin n`: `sampleSum = qsum`, a coin permutation gives `AdvDist = 0`
    (`advDist_eq_zero_of_coin_perm`). Product coins `coinPair`/`coinFst`/`coinSnd` with the
    Fubini lemma `qsum_coinPair` are in §3.
§2  Semantics of closed packages and the reduction lemma `Pkg.runBool_link`:
    `D` against `R ∘ P` is `R.reduce D` against `P`. `Code.evalState_sim`: handlers related by
    a step-preserved relation give every adaptive program the same result.
§3  `ProbPkg`, `ProbPkg.linkDet`, `ProbPkg.link`, `ProbPkg.par` (independent coins, disjoint
    state), `ProbPkg.AdvBoundedOn` and its equivalence with `GameBound (AdvDist ..)`.
§4  Congruence. `ProbPkg.advDist_linkDet` (data processing, exact), `ProbPkg.link_congr`,
    `ProbPkg.par_congr_left`, `ProbPkg.par_congr_right`. Distinguisher classes (`DistClass`)
    are closed under reductions that make at most one call per query; `DistClass.all` and the
    query-budget class `DistClass.within b` are instances.
§5  `ProbPkg.multiSession K`: `K` sessions with independent coins and disjoint state behind
    the interface `Iface.sessions I K`, addressed by `sid : Fin K` (`Code.callSession`), in
    any adaptive interleaving. `ProbPkg.multiSession_hybrid`: a single-session bound `ε`
    gives `K · ε`, for every distinguisher class.
§6  `Machine.toProbPkg`, `Refines.toProbPkgEquiv`: a refinement gives `AdvDist = 0`.
§7  `OracleComp.toCode`, `Code.toOracleComp`, `ProbPkg.ofOracle`, `OracleComp.toProbPkg`:
    oracle adversaries are distinguishers, oracle families are packages, `OracleComp`
    simulators are open packages over the oracle interface.

Not covered: real and ideal packages are compared over the same coin count `n`; the coin is
drawn eagerly; distinguishers are deterministic (a randomized one is an average of these).
-/

public import Qsag.Spec.GameBound
public import Qsag.Spec.Refines
public import Qsag.Math.Counting
public import Qsag.Oracle.Qrom
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spec

set_option autoImplicit false

/-! ## §1. Counting over `Fin n` -/

theorem sampleSum_eq_qsum : ∀ (n : Nat) (f : Fin n → Nat), sampleSum n f = Qsag.qsum n f
  | 0, f => by rw [sampleSum_zero, Qsag.qsum_zero]
  | n + 1, f => by rw [sampleSum_succ, Qsag.qsum_succ, sampleSum_eq_qsum n]

theorem natAbsDiff_same (a : Nat) : natAbsDiff a a = 0 := by
  unfold natAbsDiff
  rw [ite_eq_left (Nat.le_refl a)]
  exact Nat.sub_self a

private theorem nad_add_le (a b c d : Nat) :
    natAbsDiff (a + b) (c + d) ≤ natAbsDiff a c + natAbsDiff b d := by
  unfold natAbsDiff
  by_cases h1 : a + b ≤ c + d <;> by_cases h2 : a ≤ c <;> by_cases h3 : b ≤ d <;>
    simp only [h1, h2, h3, ↓reduceIte] <;> omega

theorem natAbsDiff_qsum_le_qsum : ∀ (n : Nat) (f g : Fin n → Nat),
    natAbsDiff (Qsag.qsum n f) (Qsag.qsum n g) ≤
      Qsag.qsum n (fun i => natAbsDiff (f i) (g i))
  | 0, f, g => by
    simp only [Qsag.qsum_zero]
    exact Nat.le_of_eq (natAbsDiff_same 0)
  | n + 1, f, g => by
    simp only [Qsag.qsum_succ]
    exact Nat.le_trans (nad_add_le _ _ _ _)
      (Nat.add_le_add_left (natAbsDiff_qsum_le_qsum n _ _) _)

/-- Two win predicates that agree along a permutation of the coin space have the same
    number of winning coins: the advantage is exactly `0`. -/
theorem advDist_eq_zero_of_coin_perm {n : Nat} (hn : 0 < n) (π πinv : Fin n → Fin n)
    (hL : ∀ i, πinv (π i) = i) (hR : ∀ j, π (πinv j) = j) (w₀ w₁ : Fin n → Bool)
    (h : ∀ ω, w₀ ω = w₁ (π ω)) :
    AdvDist (FinGame.mk hn w₀) (FinGame.mk hn w₁) = ⟨0, n, hn⟩ := by
  have e : (FinGame.mk hn w₀).winCount = (FinGame.mk hn w₁).winCount := by
    rw [FinGame.winCount_eq, FinGame.winCount_eq, sampleSum_eq_qsum, sampleSum_eq_qsum,
      ← Qsag.qsum_perm_invariant π πinv hL hR
        (fun ω => if (FinGame.mk hn w₁).win ω then 1 else 0)]
    exact Qsag.qsum_congr (fun ω => by
      show (if w₀ ω then 1 else 0) = (if w₁ (π ω) then 1 else 0)
      rw [h ω])
  apply RatBound.ext
  · show natAbsDiff (FinGame.mk hn w₀).winCount (FinGame.mk hn w₁).winCount = 0
    rw [e, natAbsDiff_same]
  · rfl

/-! ## §2. Closed packages as handlers; the reduction lemma -/

/-- Deterministic stateful answer function for the interface `I`. -/
abbrev Handler (I : Iface) (σ : Type) : Type := σ → (q : I.Query) → I.Resp q × σ

theorem Code.evalClosed_bind {A B : Type} :
    ∀ (c : Code Iface.empty A) (f : A → Code Iface.empty B),
      Code.evalClosed (Code.bind c f) = Code.evalClosed (f (Code.evalClosed c))
  | .ret a, f => by rw [Code.ret_bind, Code.evalClosed_ret]
  | .call q _, _ => PEmpty.elim q

theorem Code.evalState_bind {E : Iface} {A B σ : Type} (h : Handler E σ) :
    ∀ (c : Code E A) (f : A → Code E B) (s : σ),
      Code.evalState h (Code.bind c f) s =
        Code.evalState h (f (Code.evalState h c s).1) (Code.evalState h c s).2
  | .ret a, f, s => by rw [Code.ret_bind, Code.evalState_ret]
  | .call q k, f, s => by
    simp only [Code.call_bind, Code.evalState_call]
    exact Code.evalState_bind h (k (h s q).1) f (h s q).2

/-- A package with no imports answers each query by a value: its handler. -/
def Pkg.closedHandler {I : Iface} {σ : Type} (P : Pkg I Iface.empty σ) : Handler I σ :=
  fun s q => Code.evalClosed (P.handle s q)

/-- Output bit of the adaptive distinguisher `D` interacting with the closed package `P`. -/
def Pkg.runBool {I : Iface} {σ : Type} (P : Pkg I Iface.empty σ) (D : Code I Bool) : Bool :=
  (Code.evalState P.closedHandler D P.init).1

theorem Pkg.closedHandler_eq {I : Iface} {σ : Type} (P : Pkg I Iface.empty σ) (s : σ)
    (q : I.Query) : P.closedHandler s q = Code.evalClosed (P.handle s q) := by rfl

theorem Pkg.runBool_eq {I : Iface} {σ : Type} (P : Pkg I Iface.empty σ) (D : Code I Bool) :
    P.runBool D = (Code.evalState P.closedHandler D P.init).1 := by rfl

/-- A program that asks nothing outputs its value. -/
theorem Pkg.runBool_ret {I : Iface} {σ : Type} (P : Pkg I Iface.empty σ) (b : Bool) :
    P.runBool (Code.ret b) = b := by
  rw [Pkg.runBool_eq, Code.evalState_ret]

/-- **Simulation.** Two handlers whose states stay related and whose answers agree give
    every adaptive program the same result. -/
theorem Code.evalState_sim {I : Iface} {A σ₁ σ₂ : Type} (h₁ : Handler I σ₁) (h₂ : Handler I σ₂)
    (Rel : σ₁ → σ₂ → Prop)
    (hStep : ∀ (s₁ : σ₁) (s₂ : σ₂) (q : I.Query), Rel s₁ s₂ →
      (h₁ s₁ q).1 = (h₂ s₂ q).1 ∧ Rel (h₁ s₁ q).2 (h₂ s₂ q).2) :
    ∀ (D : Code I A) (s₁ : σ₁) (s₂ : σ₂), Rel s₁ s₂ →
      (Code.evalState h₁ D s₁).1 = (Code.evalState h₂ D s₂).1
  | .ret _, _, _, _ => by simp only [Code.evalState_ret]
  | .call q k, s₁, s₂, hRel => by
    obtain ⟨hr, hrel⟩ := hStep s₁ s₂ q hRel
    simp only [Code.evalState_call]
    rw [← hr]
    exact Code.evalState_sim h₁ h₂ Rel hStep (k _) _ _ hrel

theorem Code.evalClosed_linkPkg {M : Iface} {R σ : Type} (Q : Pkg M Iface.empty σ) :
    ∀ (c : Code M R) (s : σ),
      Code.evalClosed (Code.linkPkg Q c s) = Code.evalState Q.closedHandler c s
  | .ret _, _ => by rw [Code.linkPkg_ret, Code.evalClosed_ret, Code.evalState_ret]
  | .call q k, s => by
    rw [Code.linkPkg_call, Code.evalClosed_bind, Code.evalState_call]
    exact Code.evalClosed_linkPkg Q (k _) _

theorem Pkg.closedHandler_link {J I : Iface} {τ σ : Type} (R : Pkg J I τ)
    (P : Pkg I Iface.empty σ) (t : τ) (s : σ) (q : J.Query) :
    (R.link P).closedHandler (t, s) q =
      ((Code.evalState P.closedHandler (R.handle t q) s).1.1,
        ((Code.evalState P.closedHandler (R.handle t q) s).1.2,
          (Code.evalState P.closedHandler (R.handle t q) s).2)) := by
  rw [Pkg.closedHandler_eq, Pkg.link_handle, Code.evalClosed_bind, Code.evalClosed_ret,
    Code.evalClosed_linkPkg]

theorem Code.evalState_linkPkg {J I : Iface} {A τ σ : Type} (R : Pkg J I τ)
    (P : Pkg I Iface.empty σ) :
    ∀ (D : Code J A) (t : τ) (s : σ),
      (Code.evalState (R.link P).closedHandler D (t, s)).1 =
        (Code.evalState P.closedHandler (Code.linkPkg R D t) s).1.1
  | .ret _, _, _ => by simp only [Code.evalState_ret, Code.linkPkg_ret]
  | .call q k, t, s => by
    rw [Code.evalState_call, Code.linkPkg_call, Pkg.closedHandler_link, Code.evalState_bind]
    exact Code.evalState_linkPkg R P (k _) _ _

/-- The distinguisher against `P` obtained by running `D` through the open package `R`. -/
def Pkg.reduce {J I : Iface} {τ : Type} (R : Pkg J I τ) (D : Code J Bool) : Code I Bool :=
  Code.bind (Code.linkPkg R D R.init) (fun x => .ret x.1)

/-- **Reduction lemma.** `D` against `R ∘ P` outputs what `R.reduce D` outputs against `P`. -/
theorem Pkg.runBool_link {J I : Iface} {τ σ : Type} (R : Pkg J I τ) (P : Pkg I Iface.empty σ)
    (D : Code J Bool) : (R.link P).runBool D = P.runBool (R.reduce D) := by
  show (Code.evalState (R.link P).closedHandler D (R.link P).init).1 =
    (Code.evalState P.closedHandler
      (Code.bind (Code.linkPkg R D R.init) (fun x => Code.ret x.1)) P.init).1
  rw [Pkg.link_init, Code.evalState_bind, Code.evalState_linkPkg, Code.evalState_ret]

/-- Each query to `R` costs at most one query to its import. -/
@[expose] def Pkg.SingleCall {J I : Iface} {τ : Type} (R : Pkg J I τ) : Prop :=
  ∀ (t : τ) (q : J.Query), Within 1 (R.handle t q)

theorem Within.linkPkg_singleCall {J I : Iface} {A τ : Type} (R : Pkg J I τ)
    (hR : R.SingleCall) :
    ∀ {b : Nat} {D : Code J A} (t : τ), Within b D → Within b (Code.linkPkg R D t)
  | b, .ret v, t, _ => by
    rw [Code.linkPkg_ret]
    exact Within.ret b (v, t)
  | b + 1, .call q k, t, .call _ _ hk => by
    rw [Code.linkPkg_call]
    have h := Within.bind (hR t q)
      (fun a : J.Resp q × τ => Within.linkPkg_singleCall R hR a.2 (hk a.1))
    exact Within.mono (Nat.le_of_eq (Nat.add_comm 1 b)) h

theorem Within.reduce_singleCall {J I : Iface} {τ : Type} (R : Pkg J I τ) (hR : R.SingleCall)
    {b : Nat} {D : Code J Bool} (hD : Within b D) : Within b (R.reduce D) :=
  Within.bind (Within.linkPkg_singleCall R hR R.init hD) (fun x => Within.ret 0 x.1)

/-- Open package answering the right summand from `Q` and forwarding the left summand. -/
def Pkg.absorbRight {I₁ I₂ : Iface} {σ₂ : Type} (Q : Pkg I₂ Iface.empty σ₂) :
    Pkg (Iface.sum I₁ I₂) I₁ σ₂ where
  init := Q.init
  handle s q :=
    match q with
    | .inl q₁ => .call q₁ (fun r => .ret (r, s))
    | .inr q₂ => .ret (Q.closedHandler s q₂)

/-- Open package answering the left summand from `P` and forwarding the right summand. -/
def Pkg.absorbLeft {I₁ I₂ : Iface} {σ₁ : Type} (P : Pkg I₁ Iface.empty σ₁) :
    Pkg (Iface.sum I₁ I₂) I₂ σ₁ where
  init := P.init
  handle s q :=
    match q with
    | .inl q₁ => .ret (P.closedHandler s q₁)
    | .inr q₂ => .call q₂ (fun r => .ret (r, s))

theorem Pkg.absorbRight_singleCall {I₁ I₂ : Iface} {σ₂ : Type} (Q : Pkg I₂ Iface.empty σ₂) :
    (Pkg.absorbRight (I₁ := I₁) Q).SingleCall := by
  intro t q
  cases q with
  | inl q₁ => exact Within.call q₁ _ (fun r => Within.ret 0 (r, t))
  | inr q₂ => exact Within.ret 1 _

theorem Pkg.absorbLeft_singleCall {I₁ I₂ : Iface} {σ₁ : Type} (P : Pkg I₁ Iface.empty σ₁) :
    (Pkg.absorbLeft (I₂ := I₂) P).SingleCall := by
  intro t q
  cases q with
  | inl q₁ => exact Within.ret 1 _
  | inr q₂ => exact Within.call q₂ _ (fun r => Within.ret 0 (r, t))

theorem Pkg.closedHandler_par_inl {I₁ I₂ : Iface} {σ₁ σ₂ : Type} (P : Pkg I₁ Iface.empty σ₁)
    (Q : Pkg I₂ Iface.empty σ₂) (s₁ : σ₁) (s₂ : σ₂) (q₁ : I₁.Query) :
    (P.par Q).closedHandler (s₁, s₂) (.inl q₁) =
      ((P.closedHandler s₁ q₁).1, ((P.closedHandler s₁ q₁).2, s₂)) := by
  exact (congrArg Code.evalClosed (Pkg.par_handle_inl P Q (s₁, s₂) q₁)).trans
    ((Code.evalClosed_bind _ _).trans (Code.evalClosed_ret _))

theorem Pkg.closedHandler_par_inr {I₁ I₂ : Iface} {σ₁ σ₂ : Type} (P : Pkg I₁ Iface.empty σ₁)
    (Q : Pkg I₂ Iface.empty σ₂) (s₁ : σ₁) (s₂ : σ₂) (q₂ : I₂.Query) :
    (P.par Q).closedHandler (s₁, s₂) (.inr q₂) =
      ((Q.closedHandler s₂ q₂).1, (s₁, (Q.closedHandler s₂ q₂).2)) := by
  exact (congrArg Code.evalClosed (Pkg.par_handle_inr P Q (s₁, s₂) q₂)).trans
    ((Code.evalClosed_bind _ _).trans (Code.evalClosed_ret _))

theorem Pkg.closedHandler_absorbRight_link_inl {I₁ I₂ : Iface} {σ₁ σ₂ : Type}
    (P : Pkg I₁ Iface.empty σ₁) (Q : Pkg I₂ Iface.empty σ₂) (s₁ : σ₁) (s₂ : σ₂)
    (q₁ : I₁.Query) :
    ((Pkg.absorbRight (I₁ := I₁) Q).link P).closedHandler (s₂, s₁) (.inl q₁) =
      ((P.closedHandler s₁ q₁).1, (s₂, (P.closedHandler s₁ q₁).2)) := by
  have e : Code.evalState P.closedHandler
      ((Pkg.absorbRight (I₁ := I₁) Q).handle s₂ (.inl q₁)) s₁ =
        (((P.closedHandler s₁ q₁).1, s₂), (P.closedHandler s₁ q₁).2) := by
    show Code.evalState P.closedHandler
      (Code.call q₁ (fun r => Code.ret (r, s₂))) s₁ = _
    rw [Code.evalState_call, Code.evalState_ret]
  have h := Pkg.closedHandler_link (Pkg.absorbRight (I₁ := I₁) Q) P s₂ s₁ (.inl q₁)
  rw [e] at h
  exact h

theorem Pkg.closedHandler_absorbRight_link_inr {I₁ I₂ : Iface} {σ₁ σ₂ : Type}
    (P : Pkg I₁ Iface.empty σ₁) (Q : Pkg I₂ Iface.empty σ₂) (s₁ : σ₁) (s₂ : σ₂)
    (q₂ : I₂.Query) :
    ((Pkg.absorbRight (I₁ := I₁) Q).link P).closedHandler (s₂, s₁) (.inr q₂) =
      ((Q.closedHandler s₂ q₂).1, ((Q.closedHandler s₂ q₂).2, s₁)) := by
  have e : Code.evalState P.closedHandler
      ((Pkg.absorbRight (I₁ := I₁) Q).handle s₂ (.inr q₂)) s₁ =
        (Q.closedHandler s₂ q₂, s₁) := by
    show Code.evalState P.closedHandler (Code.ret (Q.closedHandler s₂ q₂)) s₁ = _
    rw [Code.evalState_ret]
  have h := Pkg.closedHandler_link (Pkg.absorbRight (I₁ := I₁) Q) P s₂ s₁ (.inr q₂)
  rw [e] at h
  exact h

theorem Pkg.closedHandler_absorbLeft_link_inl {I₁ I₂ : Iface} {σ₁ σ₂ : Type}
    (P : Pkg I₁ Iface.empty σ₁) (Q : Pkg I₂ Iface.empty σ₂) (s₁ : σ₁) (s₂ : σ₂)
    (q₁ : I₁.Query) :
    ((Pkg.absorbLeft (I₂ := I₂) P).link Q).closedHandler (s₁, s₂) (.inl q₁) =
      ((P.closedHandler s₁ q₁).1, ((P.closedHandler s₁ q₁).2, s₂)) := by
  have e : Code.evalState Q.closedHandler
      ((Pkg.absorbLeft (I₂ := I₂) P).handle s₁ (.inl q₁)) s₂ =
        (P.closedHandler s₁ q₁, s₂) := by
    show Code.evalState Q.closedHandler (Code.ret (P.closedHandler s₁ q₁)) s₂ = _
    rw [Code.evalState_ret]
  have h := Pkg.closedHandler_link (Pkg.absorbLeft (I₂ := I₂) P) Q s₁ s₂ (.inl q₁)
  rw [e] at h
  exact h

theorem Pkg.closedHandler_absorbLeft_link_inr {I₁ I₂ : Iface} {σ₁ σ₂ : Type}
    (P : Pkg I₁ Iface.empty σ₁) (Q : Pkg I₂ Iface.empty σ₂) (s₁ : σ₁) (s₂ : σ₂)
    (q₂ : I₂.Query) :
    ((Pkg.absorbLeft (I₂ := I₂) P).link Q).closedHandler (s₁, s₂) (.inr q₂) =
      ((Q.closedHandler s₂ q₂).1, (s₁, (Q.closedHandler s₂ q₂).2)) := by
  have e : Code.evalState Q.closedHandler
      ((Pkg.absorbLeft (I₂ := I₂) P).handle s₁ (.inr q₂)) s₂ =
        (((Q.closedHandler s₂ q₂).1, s₁), (Q.closedHandler s₂ q₂).2) := by
    show Code.evalState Q.closedHandler
      (Code.call q₂ (fun r => Code.ret (r, s₁))) s₂ = _
    rw [Code.evalState_call, Code.evalState_ret]
  have h := Pkg.closedHandler_link (Pkg.absorbLeft (I₂ := I₂) P) Q s₁ s₂ (.inr q₂)
  rw [e] at h
  exact h

/-- `D` against `P ⊗ Q` is `D` with `Q` run inside it, against `P`. -/
theorem Pkg.runBool_par_absorbRight {I₁ I₂ : Iface} {σ₁ σ₂ : Type} (P : Pkg I₁ Iface.empty σ₁)
    (Q : Pkg I₂ Iface.empty σ₂) (D : Code (Iface.sum I₁ I₂) Bool) :
    (P.par Q).runBool D = P.runBool ((Pkg.absorbRight Q).reduce D) := by
  rw [← Pkg.runBool_link]
  have hInit : ((Pkg.absorbRight (I₁ := I₁) Q).link P).init =
      ((P.par Q).init.2, (P.par Q).init.1) := by
    rw [Pkg.link_init, Pkg.par_init]
    exact rfl
  refine Code.evalState_sim (P.par Q).closedHandler ((Pkg.absorbRight Q).link P).closedHandler
    (fun a b => b = (a.2, a.1)) ?_ D _ _ hInit
  rintro ⟨s₁, s₂⟩ _ q rfl
  cases q with
  | inl q₁ =>
    have e1 := Pkg.closedHandler_par_inl P Q s₁ s₂ q₁
    have e2 := Pkg.closedHandler_absorbRight_link_inl P Q s₁ s₂ q₁
    exact ⟨(congrArg Prod.fst e1).trans (congrArg Prod.fst e2).symm,
      (congrArg Prod.snd e2).trans (congrArg (fun x => (x.2.2, x.2.1)) e1).symm⟩
  | inr q₂ =>
    have e1 := Pkg.closedHandler_par_inr P Q s₁ s₂ q₂
    have e2 := Pkg.closedHandler_absorbRight_link_inr P Q s₁ s₂ q₂
    exact ⟨(congrArg Prod.fst e1).trans (congrArg Prod.fst e2).symm,
      (congrArg Prod.snd e2).trans (congrArg (fun x => (x.2.2, x.2.1)) e1).symm⟩

/-- `D` against `P ⊗ Q` is `D` with `P` run inside it, against `Q`. -/
theorem Pkg.runBool_par_absorbLeft {I₁ I₂ : Iface} {σ₁ σ₂ : Type} (P : Pkg I₁ Iface.empty σ₁)
    (Q : Pkg I₂ Iface.empty σ₂) (D : Code (Iface.sum I₁ I₂) Bool) :
    (P.par Q).runBool D = Q.runBool ((Pkg.absorbLeft P).reduce D) := by
  rw [← Pkg.runBool_link]
  have hInit : (P.par Q).init = ((Pkg.absorbLeft (I₂ := I₂) P).link Q).init := by
    rw [Pkg.link_init, Pkg.par_init]
    exact rfl
  refine Code.evalState_sim (P.par Q).closedHandler ((Pkg.absorbLeft P).link Q).closedHandler
    Eq ?_ D _ _ hInit
  rintro ⟨s₁, s₂⟩ _ q rfl
  cases q with
  | inl q₁ =>
    have e := (Pkg.closedHandler_par_inl P Q s₁ s₂ q₁).trans
      (Pkg.closedHandler_absorbLeft_link_inl P Q s₁ s₂ q₁).symm
    exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
  | inr q₂ =>
    have e := (Pkg.closedHandler_par_inr P Q s₁ s₂ q₂).trans
      (Pkg.closedHandler_absorbLeft_link_inr P Q s₁ s₂ q₂).symm
    exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩

/-! ## §3. Probabilistic packages -/

/-- Probabilistic package: a package for every value of a coin drawn uniformly from `Fin n`
    before the interaction. The coin may determine the initial state and every answer. -/
structure ProbPkg (n : Nat) (I E : Iface) (σ : Type) : Type 1 where
  sample : Fin n → Pkg I E σ

/-- A deterministic package as a probabilistic one, over any coin count. -/
def ProbPkg.lift (n : Nat) {I E : Iface} {σ : Type} (P : Pkg I E σ) : ProbPkg n I E σ :=
  ⟨fun _ => P⟩

theorem coin_pos_right {n m : Nat} (ω : Fin (n * m)) : 0 < m :=
  Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ ω.2)

/-- The product coin `(a, b)`, as the index `a * m + b`. -/
def coinPair {n m : Nat} (a : Fin n) (b : Fin m) : Fin (n * m) :=
  ⟨a.1 * m + b.1, Nat.lt_of_lt_of_le (Nat.add_lt_add_left b.2 (a.1 * m)) (by
    have h := Nat.mul_le_mul_right m (Nat.succ_le_of_lt a.2)
    rw [Nat.succ_mul] at h
    exact h)⟩

/-- First component of a product coin. -/
def coinFst {n m : Nat} (ω : Fin (n * m)) : Fin n :=
  ⟨ω.1 / m, (Nat.div_lt_iff_lt_mul (coin_pos_right ω)).mpr ω.2⟩

/-- Second component of a product coin. -/
def coinSnd {n m : Nat} (ω : Fin (n * m)) : Fin m :=
  ⟨ω.1 % m, Nat.mod_lt ω.1 (coin_pos_right ω)⟩

theorem coinPair_val {n m : Nat} (a : Fin n) (b : Fin m) :
    (coinPair a b).1 = a.1 * m + b.1 := by rfl

theorem coinFst_val {n m : Nat} (ω : Fin (n * m)) : (coinFst ω).1 = ω.1 / m := by rfl

theorem coinSnd_val {n m : Nat} (ω : Fin (n * m)) : (coinSnd ω).1 = ω.1 % m := by rfl

theorem coinFst_pair {n m : Nat} (a : Fin n) (b : Fin m) : coinFst (coinPair a b) = a := by
  apply Fin.ext
  rw [coinFst_val, coinPair_val, Nat.mul_comm a.1 m, Nat.mul_add_div (coin_pos_right (coinPair a b)),
    Nat.div_eq_of_lt b.2, Nat.add_zero]

theorem coinSnd_pair {n m : Nat} (a : Fin n) (b : Fin m) : coinSnd (coinPair a b) = b := by
  apply Fin.ext
  rw [coinSnd_val, coinPair_val, Nat.mul_comm a.1 m, Nat.mul_add_mod, Nat.mod_eq_of_lt b.2]

/-- Every product coin is the pair of its components. -/
theorem coinPair_fst_snd {n m : Nat} (ω : Fin (n * m)) :
    coinPair (coinFst ω) (coinSnd ω) = ω := by
  apply Fin.ext
  rw [coinPair_val, coinFst_val, coinSnd_val, Nat.mul_comm (ω.1 / m) m]
  exact Nat.div_add_mod ω.1 m

private theorem qsum_snoc : ∀ (k : Nat) (g : Nat → Nat),
    Qsag.qsum (k + 1) (fun i => g i.1) = Qsag.qsum k (fun i => g i.1) + g k
  | 0, g => by
    simp only [Qsag.qsum_succ, Qsag.qsum_zero]
    exact Nat.add_comm _ _
  | k + 1, g => by
    have ih := qsum_snoc k (fun j => g (j + 1))
    have e1 : Qsag.qsum (k + 1 + 1) (fun i => g i.1) =
        g 0 + Qsag.qsum (k + 1) (fun i => g (i.1 + 1)) := Qsag.qsum_succ (k + 1) _
    have e2 : Qsag.qsum (k + 1) (fun i => g i.1) =
        g 0 + Qsag.qsum k (fun i => g (i.1 + 1)) := Qsag.qsum_succ k _
    rw [e1, e2, ih]
    exact (Nat.add_assoc _ _ _).symm

private theorem qsum_cast {m n : Nat} (h : m = n) (g : Nat → Nat) :
    Qsag.qsum m (fun i => g i.1) = Qsag.qsum n (fun i => g i.1) := by
  subst h
  rfl

private theorem qsum_add_split (m : Nat) : ∀ (n : Nat) (g : Nat → Nat),
    Qsag.qsum (m + n) (fun i => g i.1) =
      Qsag.qsum m (fun i => g i.1) + Qsag.qsum n (fun j => g (m + j.1))
  | 0, g => by
    rw [Qsag.qsum_zero]
    exact rfl
  | n + 1, g => by
    have e : Qsag.qsum (m + (n + 1)) (fun i => g i.1) =
        Qsag.qsum ((m + n) + 1) (fun i => g i.1) := rfl
    rw [e, qsum_snoc (m + n) g, qsum_add_split m n g, qsum_snoc n (fun j => g (m + j)),
      Nat.add_assoc]

private theorem qsum_mul_nat : ∀ (n m : Nat) (g : Nat → Nat),
    Qsag.qsum (n * m) (fun i => g i.1) =
      Qsag.qsum n (fun a => Qsag.qsum m (fun b => g (a.1 * m + b.1)))
  | 0, m, g => by
    rw [qsum_cast (Nat.zero_mul m) g, Qsag.qsum_zero, Qsag.qsum_zero]
  | n + 1, m, g => by
    rw [qsum_cast (Nat.succ_mul n m) g, qsum_add_split (n * m) m g, qsum_mul_nat n m g,
      qsum_snoc n (fun a => Qsag.qsum m (fun b => g (a * m + b.1)))]

private theorem dite_lt_eq {N : Nat} (f : Fin N → Nat) (k : Nat) (h : k < N) :
    (if h' : k < N then f ⟨k, h'⟩ else 0) = f ⟨k, h⟩ := by
  split
  · rfl
  · next hn => exact absurd h hn

/-- Fubini over a product coin: a sum over `Fin (n * m)` is the iterated sum over the two
    components. -/
theorem qsum_coinPair {n m : Nat} (f : Fin (n * m) → Nat) :
    Qsag.qsum (n * m) f = Qsag.qsum n (fun a => Qsag.qsum m (fun b => f (coinPair a b))) := by
  have hL : Qsag.qsum (n * m) f =
      Qsag.qsum (n * m) (fun i => (fun k => if h : k < n * m then f ⟨k, h⟩ else 0) i.1) :=
    Qsag.qsum_congr (fun i => (dite_lt_eq f i.1 i.2).symm)
  have hR : Qsag.qsum n (fun a => Qsag.qsum m (fun b =>
        (fun k => if h : k < n * m then f ⟨k, h⟩ else 0) (a.1 * m + b.1))) =
      Qsag.qsum n (fun a => Qsag.qsum m (fun b => f (coinPair a b))) :=
    Qsag.qsum_congr (fun a => Qsag.qsum_congr (fun b =>
      dite_lt_eq f (a.1 * m + b.1) (coinPair a b).2))
  rw [hL, qsum_mul_nat n m (fun k => if h : k < n * m then f ⟨k, h⟩ else 0), hR]

/-- Link below a deterministic package: no new coins. -/
def ProbPkg.linkDet {n : Nat} {J I E : Iface} {τ σ : Type} (R : Pkg J I τ)
    (P : ProbPkg n I E σ) : ProbPkg n J E (τ × σ) :=
  ⟨fun ω => R.link (P.sample ω)⟩

/-- Sequential composition `R ∘ P` with independent coins. -/
def ProbPkg.link {n m : Nat} {J I E : Iface} {τ σ : Type} (R : ProbPkg n J I τ)
    (P : ProbPkg m I E σ) : ProbPkg (n * m) J E (τ × σ) :=
  ⟨fun ω => (R.sample (coinFst ω)).link (P.sample (coinSnd ω))⟩

/-- Parallel composition `P ⊗ Q` with independent coins and disjoint state. -/
def ProbPkg.par {n m : Nat} {I₁ I₂ E : Iface} {σ₁ σ₂ : Type} (P : ProbPkg n I₁ E σ₁)
    (Q : ProbPkg m I₂ E σ₂) : ProbPkg (n * m) (Iface.sum I₁ I₂) E (σ₁ × σ₂) :=
  ⟨fun ω => (P.sample (coinFst ω)).par (Q.sample (coinSnd ω))⟩

/-- State separation of `ProbPkg.par`: for every coin, a left query leaves the right state
    untouched. -/
theorem ProbPkg.par_left_preserves_right {n m : Nat} {I₁ I₂ E : Iface} {σ₁ σ₂ τ : Type}
    (P : ProbPkg n I₁ E σ₁) (Q : ProbPkg m I₂ E σ₂) (ω : Fin (n * m))
    (env : τ → (q : E.Query) → E.Resp q × τ) (s₁ : σ₁) (s₂ : σ₂) (t : τ) (q₁ : I₁.Query) :
    ((Code.evalState env (((P.par Q).sample ω).handle (s₁, s₂) (.inl q₁)) t).1.2).2 = s₂ :=
  Pkg.par_left_preserves_right _ _ env s₁ s₂ t q₁

/-- The distinguishing game of `D` against the closed probabilistic package `P`. -/
def ProbPkg.game {n : Nat} {I : Iface} {σ : Type} (hn : 0 < n)
    (P : ProbPkg n I Iface.empty σ) (D : Code I Bool) : FinGame n :=
  ⟨hn, fun ω => (P.sample ω).runBool D⟩

/-- Number of coins on which `D` outputs `true`. -/
def ProbPkg.winCount {n : Nat} {I : Iface} {σ : Type} (P : ProbPkg n I Iface.empty σ)
    (D : Code I Bool) : Nat :=
  Qsag.qsum n (fun ω => if (P.sample ω).runBool D then 1 else 0)

theorem ProbPkg.game_winCount {n : Nat} {I : Iface} {σ : Type} (hn : 0 < n)
    (P : ProbPkg n I Iface.empty σ) (D : Code I Bool) :
    (P.game hn D).winCount = P.winCount D :=
  (FinGame.winCount_eq _).trans (sampleSum_eq_qsum n _)

theorem ProbPkg.winCount_eq {n : Nat} {I : Iface} {σ : Type} (P : ProbPkg n I Iface.empty σ)
    (D : Code I Bool) :
    P.winCount D = Qsag.qsum n (fun ω => if (P.sample ω).runBool D then 1 else 0) := by rfl

/-- Every distinguisher in the class `Adm` has advantage at most `ε` between `P₀` and `P₁`:
    `|#win₀ - #win₁| / n ≤ ε`, cross-multiplied. -/
@[expose] def ProbPkg.AdvBoundedOn {n : Nat} {I : Iface} {σ₀ σ₁ : Type}
    (Adm : Code I Bool → Prop) (P₀ : ProbPkg n I Iface.empty σ₀)
    (P₁ : ProbPkg n I Iface.empty σ₁) (ε : RatBound) : Prop :=
  ∀ D : Code I Bool, Adm D → natAbsDiff (P₀.winCount D) (P₁.winCount D) * ε.den ≤ ε.num * n

/-- `AdvBoundedOn` is the `GameBound` on `AdvDist` of the two games, for each admitted `D`. -/
theorem ProbPkg.advBoundedOn_iff_gameBound {n : Nat} {I : Iface} {σ₀ σ₁ : Type} (hn : 0 < n)
    (Adm : Code I Bool → Prop) (P₀ : ProbPkg n I Iface.empty σ₀)
    (P₁ : ProbPkg n I Iface.empty σ₁) (ε : RatBound) :
    ProbPkg.AdvBoundedOn Adm P₀ P₁ ε ↔
      ∀ D : Code I Bool, Adm D → GameBound (AdvDist (P₀.game hn D) (P₁.game hn D)) ε := by
  constructor
  · intro h D hD
    show natAbsDiff (P₀.game hn D).winCount (P₁.game hn D).winCount * ε.den ≤ ε.num * n
    rw [ProbPkg.game_winCount, ProbPkg.game_winCount]
    exact h D hD
  · intro h D hD
    have h' : natAbsDiff (P₀.game hn D).winCount (P₁.game hn D).winCount * ε.den ≤ ε.num * n :=
      h D hD
    rw [ProbPkg.game_winCount, ProbPkg.game_winCount] at h'
    exact h'

/-- Same-denominator triangle inequality for package advantages. -/
theorem ProbPkg.AdvBoundedOn.triangle {n : Nat} {I : Iface} {σ₀ σ₁ σ₂ : Type}
    {Adm : Code I Bool → Prop} {P₀ : ProbPkg n I Iface.empty σ₀}
    {P₁ : ProbPkg n I Iface.empty σ₁} {P₂ : ProbPkg n I Iface.empty σ₂}
    {a b d : Nat} (hd : 0 < d)
    (h₀₁ : ProbPkg.AdvBoundedOn Adm P₀ P₁ ⟨a, d, hd⟩)
    (h₁₂ : ProbPkg.AdvBoundedOn Adm P₁ P₂ ⟨b, d, hd⟩) :
    ProbPkg.AdvBoundedOn Adm P₀ P₂ ⟨a + b, d, hd⟩ := by
  intro D hD
  have h1 : natAbsDiff (P₀.winCount D) (P₁.winCount D) * d ≤ a * n := h₀₁ D hD
  have h2 : natAbsDiff (P₁.winCount D) (P₂.winCount D) * d ≤ b * n := h₁₂ D hD
  show natAbsDiff (P₀.winCount D) (P₂.winCount D) * d ≤ (a + b) * n
  have hTri := natAbsDiff_triangle (P₀.winCount D) (P₁.winCount D) (P₂.winCount D)
  calc natAbsDiff (P₀.winCount D) (P₂.winCount D) * d
      ≤ (natAbsDiff (P₀.winCount D) (P₁.winCount D) +
          natAbsDiff (P₁.winCount D) (P₂.winCount D)) * d := Nat.mul_le_mul_right d hTri
    _ = natAbsDiff (P₀.winCount D) (P₁.winCount D) * d +
          natAbsDiff (P₁.winCount D) (P₂.winCount D) * d := Nat.add_mul _ _ _
    _ ≤ a * n + b * n := Nat.add_le_add h1 h2
    _ = (a + b) * n := (Nat.add_mul _ _ _).symm

/-- Packages that coincide along a permutation of the coin space are at advantage `0`
    against every distinguisher: identically distributed systems. -/
theorem ProbPkg.advBoundedOn_zero_of_coin_perm {n : Nat} {I : Iface} {σ : Type}
    (P₀ P₁ : ProbPkg n I Iface.empty σ) (π πinv : Fin n → Fin n)
    (hL : ∀ i, πinv (π i) = i) (hR : ∀ j, π (πinv j) = j)
    (h : ∀ ω, P₀.sample ω = P₁.sample (π ω)) (Adm : Code I Bool → Prop) :
    ProbPkg.AdvBoundedOn Adm P₀ P₁ RatBound.zero := by
  intro D _
  have e : P₀.winCount D = P₁.winCount D := by
    unfold ProbPkg.winCount
    rw [← Qsag.qsum_perm_invariant π πinv hL hR
      (fun ω => if (P₁.sample ω).runBool D then 1 else 0)]
    exact Qsag.qsum_congr (fun ω => by rw [h ω])
  rw [e, natAbsDiff_same, Nat.zero_mul]
  exact Nat.zero_le _

/-! ## §4. Congruence: data processing, link, par -/

/-- **Averaging.** If the win count of `Q_b` is the sum over `m` outer coins of the win
    counts of `P_b` against reduced distinguishers, a bound for `P₀, P₁` is a bound for
    `Q₀, Q₁`. -/
theorem ProbPkg.advBoundedOn_of_slices {n m N : Nat} {I J : Iface} {σ₀ σ₁ τ₀ τ₁ : Type}
    (hN : N = m * n) {AdmI : Code I Bool → Prop} {AdmJ : Code J Bool → Prop}
    (P₀ : ProbPkg n I Iface.empty σ₀) (P₁ : ProbPkg n I Iface.empty σ₁)
    (Q₀ : ProbPkg N J Iface.empty τ₀) (Q₁ : ProbPkg N J Iface.empty τ₁)
    (red₀ red₁ : Fin m → Code J Bool → Code I Bool)
    (hRed : ∀ a D, red₀ a D = red₁ a D)
    (hAdm : ∀ a D, AdmJ D → AdmI (red₀ a D))
    (h₀ : ∀ D, Q₀.winCount D = Qsag.qsum m (fun a => P₀.winCount (red₀ a D)))
    (h₁ : ∀ D, Q₁.winCount D = Qsag.qsum m (fun a => P₁.winCount (red₁ a D)))
    (ε : RatBound) (hP : ProbPkg.AdvBoundedOn AdmI P₀ P₁ ε) :
    ProbPkg.AdvBoundedOn AdmJ Q₀ Q₁ ε := by
  intro D hD
  rw [h₀ D, h₁ D, hN]
  have hPt : ∀ a : Fin m,
      natAbsDiff (P₀.winCount (red₀ a D)) (P₁.winCount (red₁ a D)) * ε.den ≤ ε.num * n :=
    fun a => by
      rw [← hRed a D]
      exact hP (red₀ a D) (hAdm a D hD)
  have h1 := natAbsDiff_qsum_le_qsum m (fun a => P₀.winCount (red₀ a D))
    (fun a => P₁.winCount (red₁ a D))
  have h2 := Nat.mul_le_mul_right ε.den h1
  rw [← Qsag.qsum_mul_right ε.den] at h2
  have h4 := Qsag.qsum_le_qsum (g := fun _ : Fin m => ε.num * n) hPt
  rw [Qsag.qsum_const] at h4
  exact Nat.le_trans h2 (Nat.le_trans h4 (Nat.le_of_eq (Nat.mul_left_comm m ε.num n)))

theorem ProbPkg.winCount_linkDet {n : Nat} {J I : Iface} {τ σ : Type} (R : Pkg J I τ)
    (P : ProbPkg n I Iface.empty σ) (D : Code J Bool) :
    (ProbPkg.linkDet R P).winCount D = P.winCount (R.reduce D) :=
  Qsag.qsum_congr (fun ω => by
    show (if (R.link (P.sample ω)).runBool D then 1 else 0) = _
    rw [Pkg.runBool_link])

/-- **Data processing, exact form.** Post-composing both packages with the same
    deterministic package `R` turns the advantage of `D` into the advantage of the reduced
    distinguisher `R.reduce D`: nothing is gained by processing. -/
theorem ProbPkg.advDist_linkDet {n : Nat} {J I : Iface} {τ σ₀ σ₁ : Type} (hn : 0 < n)
    (R : Pkg J I τ) (P₀ : ProbPkg n I Iface.empty σ₀) (P₁ : ProbPkg n I Iface.empty σ₁)
    (D : Code J Bool) :
    AdvDist ((ProbPkg.linkDet R P₀).game hn D) ((ProbPkg.linkDet R P₁).game hn D) =
      AdvDist (P₀.game hn (R.reduce D)) (P₁.game hn (R.reduce D)) := by
  apply RatBound.ext
  · show natAbsDiff ((ProbPkg.linkDet R P₀).game hn D).winCount
        ((ProbPkg.linkDet R P₁).game hn D).winCount =
      natAbsDiff (P₀.game hn (R.reduce D)).winCount (P₁.game hn (R.reduce D)).winCount
    rw [ProbPkg.game_winCount, ProbPkg.game_winCount, ProbPkg.game_winCount,
      ProbPkg.game_winCount, ProbPkg.winCount_linkDet, ProbPkg.winCount_linkDet]
  · rfl

/-- **Data processing.** A bound against every distinguisher survives composition with any
    deterministic package. -/
theorem ProbPkg.linkDet_congr {n : Nat} {J I : Iface} {τ σ₀ σ₁ : Type} (R : Pkg J I τ)
    {AdmI : Code I Bool → Prop} {AdmJ : Code J Bool → Prop}
    (hAdm : ∀ D, AdmJ D → AdmI (R.reduce D))
    {P₀ : ProbPkg n I Iface.empty σ₀} {P₁ : ProbPkg n I Iface.empty σ₁} {ε : RatBound}
    (h : ProbPkg.AdvBoundedOn AdmI P₀ P₁ ε) :
    ProbPkg.AdvBoundedOn AdmJ (ProbPkg.linkDet R P₀) (ProbPkg.linkDet R P₁) ε := by
  intro D hD
  rw [ProbPkg.winCount_linkDet, ProbPkg.winCount_linkDet]
  exact h (R.reduce D) (hAdm D hD)

theorem ProbPkg.winCount_link {n m : Nat} {J I : Iface} {τ σ : Type} (R : ProbPkg n J I τ)
    (P : ProbPkg m I Iface.empty σ) (D : Code J Bool) :
    (R.link P).winCount D = Qsag.qsum n (fun a => P.winCount ((R.sample a).reduce D)) := by
  unfold ProbPkg.winCount
  rw [qsum_coinPair]
  apply Qsag.qsum_congr
  intro a
  apply Qsag.qsum_congr
  intro b
  show (if ((R.sample (coinFst (coinPair a b))).link
      (P.sample (coinSnd (coinPair a b)))).runBool D then 1 else 0) = _
  rw [coinFst_pair, coinSnd_pair, Pkg.runBool_link]

/-- **Link congruence.** A bound for `P₀, P₁` is a bound for `R ∘ P₀, R ∘ P₁` for any
    probabilistic `R` with its own coins. -/
theorem ProbPkg.link_congr {n m : Nat} {J I : Iface} {τ σ₀ σ₁ : Type} (R : ProbPkg n J I τ)
    {AdmI : Code I Bool → Prop} {AdmJ : Code J Bool → Prop}
    (hAdm : ∀ a D, AdmJ D → AdmI ((R.sample a).reduce D))
    {P₀ : ProbPkg m I Iface.empty σ₀} {P₁ : ProbPkg m I Iface.empty σ₁} {ε : RatBound}
    (h : ProbPkg.AdvBoundedOn AdmI P₀ P₁ ε) :
    ProbPkg.AdvBoundedOn AdmJ (R.link P₀) (R.link P₁) ε :=
  ProbPkg.advBoundedOn_of_slices rfl P₀ P₁ (R.link P₀) (R.link P₁)
    (fun a D => (R.sample a).reduce D) (fun a D => (R.sample a).reduce D) (fun _ _ => rfl) hAdm
    (ProbPkg.winCount_link R P₀) (ProbPkg.winCount_link R P₁) ε h

theorem ProbPkg.winCount_par_fixLeft {n m : Nat} {I₁ I₂ : Iface} {σ₁ σ₂ : Type}
    (P : ProbPkg n I₁ Iface.empty σ₁) (Q : ProbPkg m I₂ Iface.empty σ₂)
    (D : Code (Iface.sum I₁ I₂) Bool) :
    (P.par Q).winCount D =
      Qsag.qsum n (fun a => Q.winCount ((Pkg.absorbLeft (P.sample a)).reduce D)) := by
  unfold ProbPkg.winCount
  rw [qsum_coinPair]
  apply Qsag.qsum_congr
  intro a
  apply Qsag.qsum_congr
  intro b
  show (if ((P.sample (coinFst (coinPair a b))).par
      (Q.sample (coinSnd (coinPair a b)))).runBool D then 1 else 0) = _
  rw [coinFst_pair, coinSnd_pair, Pkg.runBool_par_absorbLeft]

theorem ProbPkg.winCount_par_fixRight {n m : Nat} {I₁ I₂ : Iface} {σ₁ σ₂ : Type}
    (P : ProbPkg n I₁ Iface.empty σ₁) (Q : ProbPkg m I₂ Iface.empty σ₂)
    (D : Code (Iface.sum I₁ I₂) Bool) :
    (P.par Q).winCount D =
      Qsag.qsum m (fun b => P.winCount ((Pkg.absorbRight (Q.sample b)).reduce D)) := by
  unfold ProbPkg.winCount
  rw [qsum_coinPair, Qsag.qsum_comm]
  apply Qsag.qsum_congr
  intro b
  apply Qsag.qsum_congr
  intro a
  show (if ((P.sample (coinFst (coinPair a b))).par
      (Q.sample (coinSnd (coinPair a b)))).runBool D then 1 else 0) = _
  rw [coinFst_pair, coinSnd_pair, Pkg.runBool_par_absorbRight]

/-- A class of distinguishers over every interface, closed under reductions that make at
    most one call per query. -/
structure DistClass where
  mem : (I : Iface) → Code I Bool → Prop
  closed : ∀ {J I : Iface} {τ : Type} (R : Pkg J I τ), R.SingleCall →
    ∀ D : Code J Bool, mem J D → mem I (R.reduce D)

/-- All distinguishers. -/
def DistClass.all : DistClass := ⟨fun _ _ => True, fun _ _ _ _ => True.intro⟩

/-- Distinguishers making at most `b` queries on every path. -/
def DistClass.within (b : Nat) : DistClass :=
  ⟨fun _ D => Within b D, fun R hR _ hD => Within.reduce_singleCall R hR hD⟩

theorem DistClass.mem_all {I : Iface} (D : Code I Bool) : DistClass.all.mem I D := True.intro

theorem DistClass.mem_within_iff (b : Nat) {I : Iface} (D : Code I Bool) :
    (DistClass.within b).mem I D ↔ Within b D := Iff.rfl

/-- **Parallel congruence, left.** Composing both sides with the same independent `Q` on the
    right preserves the bound. -/
theorem ProbPkg.par_congr_left (𝒞 : DistClass) {n m : Nat} {I₁ I₂ : Iface} {σ₀ σ₁ τ : Type}
    {P₀ : ProbPkg n I₁ Iface.empty σ₀} {P₁ : ProbPkg n I₁ Iface.empty σ₁}
    (Q : ProbPkg m I₂ Iface.empty τ) {ε : RatBound}
    (h : ProbPkg.AdvBoundedOn (𝒞.mem I₁) P₀ P₁ ε) :
    ProbPkg.AdvBoundedOn (𝒞.mem (Iface.sum I₁ I₂)) (P₀.par Q) (P₁.par Q) ε :=
  ProbPkg.advBoundedOn_of_slices (Nat.mul_comm n m) P₀ P₁ (P₀.par Q) (P₁.par Q)
    (fun b D => (Pkg.absorbRight (Q.sample b)).reduce D)
    (fun b D => (Pkg.absorbRight (Q.sample b)).reduce D) (fun _ _ => rfl)
    (fun b D hD => 𝒞.closed _ (Pkg.absorbRight_singleCall (Q.sample b)) D hD)
    (ProbPkg.winCount_par_fixRight P₀ Q) (ProbPkg.winCount_par_fixRight P₁ Q) ε h

/-- **Parallel congruence, right.** -/
theorem ProbPkg.par_congr_right (𝒞 : DistClass) {n m : Nat} {I₁ I₂ : Iface} {σ τ₀ τ₁ : Type}
    (P : ProbPkg n I₁ Iface.empty σ)
    {Q₀ : ProbPkg m I₂ Iface.empty τ₀} {Q₁ : ProbPkg m I₂ Iface.empty τ₁} {ε : RatBound}
    (h : ProbPkg.AdvBoundedOn (𝒞.mem I₂) Q₀ Q₁ ε) :
    ProbPkg.AdvBoundedOn (𝒞.mem (Iface.sum I₁ I₂)) (P.par Q₀) (P.par Q₁) ε :=
  ProbPkg.advBoundedOn_of_slices rfl Q₀ Q₁ (P.par Q₀) (P.par Q₁)
    (fun a D => (Pkg.absorbLeft (P.sample a)).reduce D)
    (fun a D => (Pkg.absorbLeft (P.sample a)).reduce D) (fun _ _ => rfl)
    (fun a D hD => 𝒞.closed _ (Pkg.absorbLeft_singleCall (P.sample a)) D hD)
    (ProbPkg.winCount_par_fixLeft P Q₀) (ProbPkg.winCount_par_fixLeft P Q₁) ε h

/-! ## §5. Concurrent sessions and the `K`-session hybrid -/

/-- Interface of `K` sessions of `I`: the `K`-fold sum. -/
@[expose] def Iface.sessions (I : Iface) : Nat → Iface
  | 0 => Iface.empty
  | K + 1 => Iface.sum I (Iface.sessions I K)

/-- State of `K` sessions: one private state per session. -/
@[expose] def SessState (σ : Type) : Nat → Type
  | 0 => Unit
  | K + 1 => σ × SessState σ K

/-- Coin count of `K` independent sessions, `n ^ K`. -/
@[expose] def coinPow (n : Nat) : Nat → Nat
  | 0 => 1
  | K + 1 => n * coinPow n K

theorem coinPow_eq_pow (n : Nat) : ∀ K : Nat, coinPow n K = n ^ K
  | 0 => by rfl
  | K + 1 => by
    show n * coinPow n K = n ^ (K + 1)
    rw [coinPow_eq_pow n K, Nat.pow_succ, Nat.mul_comm]

theorem coinPow_pos {n : Nat} (hn : 0 < n) : ∀ K : Nat, 0 < coinPow n K
  | 0 => Nat.one_pos
  | K + 1 => Nat.mul_pos hn (coinPow_pos hn K)

/-- The query to session `sid` carrying the single-session query `q`. -/
def Iface.sessQuery {I : Iface} : (K : Nat) → Fin K → I.Query → (Iface.sessions I K).Query
  | 0, sid, _ => sid.elim0
  | _ + 1, ⟨0, _⟩, q => PSum.inl q
  | K + 1, ⟨j + 1, h⟩, q => PSum.inr (Iface.sessQuery K ⟨j, Nat.lt_of_succ_lt_succ h⟩ q)

/-- The answer of session `sid` read back at the single-session answer type. -/
def Iface.sessResp {I : Iface} : (K : Nat) → (sid : Fin K) → (q : I.Query) →
    (Iface.sessions I K).Resp (Iface.sessQuery K sid q) → I.Resp q
  | 0, sid, _, _ => sid.elim0
  | _ + 1, ⟨0, _⟩, _, r => r
  | K + 1, ⟨j + 1, h⟩, q, r => Iface.sessResp K ⟨j, Nat.lt_of_succ_lt_succ h⟩ q r

/-- Every query of the `K`-session interface is a query to some session `sid : Fin K`. -/
theorem Iface.sessQuery_surjective {I : Iface} : ∀ (K : Nat) (x : (Iface.sessions I K).Query),
    ∃ (sid : Fin K) (q : I.Query), x = Iface.sessQuery K sid q
  | 0, x => PEmpty.elim x
  | K + 1, .inl q => ⟨⟨0, Nat.zero_lt_succ K⟩, q, rfl⟩
  | K + 1, .inr y => by
    obtain ⟨sid, q, h⟩ := Iface.sessQuery_surjective K y
    exact ⟨⟨sid.1 + 1, Nat.succ_lt_succ sid.2⟩, q, congrArg PSum.inr h⟩

/-- Adaptive call to session `sid`; the continuation may call any session next. -/
def Code.callSession {I : Iface} {R : Type} (K : Nat) (sid : Fin K) (q : I.Query)
    (k : I.Resp q → Code (Iface.sessions I K) R) : Code (Iface.sessions I K) R :=
  .call (Iface.sessQuery K sid q) (fun r => k (Iface.sessResp K sid q r))

/-- The package with no queries. -/
def Pkg.unit (E : Iface) : Pkg Iface.empty E Unit := ⟨(), fun _ q => PEmpty.elim q⟩

/-- `K` concurrent sessions of `P`: session `sid` runs its own copy of `P` on its own coin
    and its own state. The coin space is `n ^ K` (`coinPow_eq_pow`). -/
def ProbPkg.multiSession {n : Nat} {I E : Iface} {σ : Type} (P : ProbPkg n I E σ) :
    (K : Nat) → ProbPkg (coinPow n K) (Iface.sessions I K) E (SessState σ K)
  | 0 => ⟨fun _ => Pkg.unit E⟩
  | K + 1 => P.par (P.multiSession K)

theorem ProbPkg.multiSession_succ {n : Nat} {I E : Iface} {σ : Type} (P : ProbPkg n I E σ)
    (K : Nat) : P.multiSession (K + 1) = P.par (P.multiSession K) := by rfl

/-- State of session `sid`. -/
def SessState.get {σ : Type} : (K : Nat) → SessState σ K → Fin K → σ
  | 0, _, sid => sid.elim0
  | _ + 1, st, ⟨0, _⟩ => st.1
  | K + 1, st, ⟨j + 1, h⟩ => SessState.get K st.2 ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- Replace the state of session `sid`, leaving every other session's state as it is. -/
def SessState.set {σ : Type} : (K : Nat) → SessState σ K → Fin K → σ → SessState σ K
  | 0, st, _, _ => st
  | _ + 1, st, ⟨0, _⟩, s => (s, st.2)
  | K + 1, st, ⟨j + 1, h⟩, s => (st.1, SessState.set K st.2 ⟨j, Nat.lt_of_succ_lt_succ h⟩ s)

/-- Coin of session `sid` inside the product coin. -/
def sessCoin {n : Nat} : (K : Nat) → Fin (coinPow n K) → Fin K → Fin n
  | 0, _, sid => sid.elim0
  | _ + 1, ω, ⟨0, _⟩ => coinFst ω
  | K + 1, ω, ⟨j + 1, h⟩ => sessCoin K (coinSnd ω) ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- **Session semantics.** A query to session `sid` of `multiSession K P` is answered by
    `P` on that session's own coin and own state, and changes no other session's state. -/
theorem ProbPkg.multiSession_step {n : Nat} {I : Iface} {σ : Type}
    (P : ProbPkg n I Iface.empty σ) :
    ∀ (K : Nat) (ω : Fin (coinPow n K)) (st : SessState σ K) (sid : Fin K) (q : I.Query),
      Iface.sessResp K sid q
          (((P.multiSession K).sample ω).closedHandler st (Iface.sessQuery K sid q)).1 =
        ((P.sample (sessCoin K ω sid)).closedHandler (SessState.get K st sid) q).1 ∧
      (((P.multiSession K).sample ω).closedHandler st (Iface.sessQuery K sid q)).2 =
        SessState.set K st sid
          ((P.sample (sessCoin K ω sid)).closedHandler (SessState.get K st sid) q).2
  | 0, _, _, sid, _ => sid.elim0
  | K + 1, ω, (s, rest), ⟨0, _⟩, q => by
    have e := Pkg.closedHandler_par_inl (P.sample (coinFst ω))
      ((P.multiSession K).sample (coinSnd ω)) s rest q
    exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
  | K + 1, ω, (s, rest), ⟨j + 1, h⟩, q => by
    have e := Pkg.closedHandler_par_inr (P.sample (coinFst ω))
      ((P.multiSession K).sample (coinSnd ω)) s rest
      (Iface.sessQuery K ⟨j, Nat.lt_of_succ_lt_succ h⟩ q)
    have ih := ProbPkg.multiSession_step P K (coinSnd ω) rest ⟨j, Nat.lt_of_succ_lt_succ h⟩ q
    have e1 : ((((P.sample (coinFst ω)).par ((P.multiSession K).sample (coinSnd ω))).closedHandler
          (s, rest) (PSum.inr (Iface.sessQuery K ⟨j, Nat.lt_of_succ_lt_succ h⟩ q))).1 :
          (Iface.sessions I K).Resp (Iface.sessQuery K ⟨j, Nat.lt_of_succ_lt_succ h⟩ q)) =
        (((P.multiSession K).sample (coinSnd ω)).closedHandler rest
          (Iface.sessQuery K ⟨j, Nat.lt_of_succ_lt_succ h⟩ q)).1 := congrArg Prod.fst e
    exact ⟨(congrArg (Iface.sessResp K ⟨j, Nat.lt_of_succ_lt_succ h⟩ q) e1).trans ih.1,
      (congrArg Prod.snd e).trans (congrArg (fun t => (s, t)) ih.2)⟩

/-- **Concurrent `K`-session hybrid.** If every distinguisher of the class has advantage at
    most `ε` between one session of `P₀` and one session of `P₁`, then every distinguisher of
    the class, interleaving its calls over `K` sessions in any adaptive order, has advantage
    at most `K · ε` between `K` sessions of `P₀` and `K` sessions of `P₁`. -/
theorem ProbPkg.multiSession_hybrid (𝒞 : DistClass) {n : Nat} {I : Iface} {σ₀ σ₁ : Type}
    (P₀ : ProbPkg n I Iface.empty σ₀) (P₁ : ProbPkg n I Iface.empty σ₁) (ε : RatBound)
    (h : ProbPkg.AdvBoundedOn (𝒞.mem I) P₀ P₁ ε) :
    ∀ K : Nat, ProbPkg.AdvBoundedOn (𝒞.mem (Iface.sessions I K))
      (P₀.multiSession K) (P₁.multiSession K) (ε.scale K)
  | 0 => by
    intro D _
    have e : (P₀.multiSession 0).winCount D = (P₁.multiSession 0).winCount D := by rfl
    rw [e, natAbsDiff_same, Nat.zero_mul]
    exact Nat.zero_le _
  | K + 1 => by
    have ih := ProbPkg.multiSession_hybrid 𝒞 P₀ P₁ ε h K
    have hA : ProbPkg.AdvBoundedOn (𝒞.mem (Iface.sum I (Iface.sessions I K)))
        (P₀.par (P₀.multiSession K)) (P₁.par (P₀.multiSession K)) ε :=
      ProbPkg.par_congr_left 𝒞 (P₀.multiSession K) h
    have hB : ProbPkg.AdvBoundedOn (𝒞.mem (Iface.sum I (Iface.sessions I K)))
        (P₁.par (P₀.multiSession K)) (P₁.par (P₁.multiSession K)) (ε.scale K) :=
      ProbPkg.par_congr_right 𝒞 P₁ ih
    intro D hD
    have h1 : natAbsDiff ((P₀.par (P₀.multiSession K)).winCount D)
        ((P₁.par (P₀.multiSession K)).winCount D) * ε.den ≤ ε.num * (n * coinPow n K) :=
      hA D hD
    have h2 : natAbsDiff ((P₁.par (P₀.multiSession K)).winCount D)
        ((P₁.par (P₁.multiSession K)).winCount D) * ε.den ≤
        (K * ε.num) * (n * coinPow n K) := hB D hD
    have hTri := natAbsDiff_triangle ((P₀.par (P₀.multiSession K)).winCount D)
      ((P₁.par (P₀.multiSession K)).winCount D) ((P₁.par (P₁.multiSession K)).winCount D)
    show natAbsDiff ((P₀.par (P₀.multiSession K)).winCount D)
        ((P₁.par (P₁.multiSession K)).winCount D) * ε.den ≤
      ((K + 1) * ε.num) * (n * coinPow n K)
    calc natAbsDiff ((P₀.par (P₀.multiSession K)).winCount D)
          ((P₁.par (P₁.multiSession K)).winCount D) * ε.den
        ≤ (natAbsDiff ((P₀.par (P₀.multiSession K)).winCount D)
            ((P₁.par (P₀.multiSession K)).winCount D) +
          natAbsDiff ((P₁.par (P₀.multiSession K)).winCount D)
            ((P₁.par (P₁.multiSession K)).winCount D)) * ε.den :=
          Nat.mul_le_mul_right ε.den hTri
      _ = natAbsDiff ((P₀.par (P₀.multiSession K)).winCount D)
            ((P₁.par (P₀.multiSession K)).winCount D) * ε.den +
          natAbsDiff ((P₁.par (P₀.multiSession K)).winCount D)
            ((P₁.par (P₁.multiSession K)).winCount D) * ε.den := Nat.add_mul _ _ _
      _ ≤ ε.num * (n * coinPow n K) + (K * ε.num) * (n * coinPow n K) := Nat.add_le_add h1 h2
      _ = ((K + 1) * ε.num) * (n * coinPow n K) := by
          rw [Nat.succ_mul, Nat.add_mul, Nat.add_comm]

/-- The hybrid against all distinguishers, as a `GameBound` on `AdvDist`. -/
theorem ProbPkg.multiSession_advDist_le {n : Nat} {I : Iface} {σ₀ σ₁ : Type} (hn : 0 < n)
    (P₀ : ProbPkg n I Iface.empty σ₀) (P₁ : ProbPkg n I Iface.empty σ₁) (ε : RatBound)
    (h : ∀ D : Code I Bool, GameBound (AdvDist (P₀.game hn D) (P₁.game hn D)) ε)
    (K : Nat) (D : Code (Iface.sessions I K) Bool) :
    GameBound (AdvDist ((P₀.multiSession K).game (coinPow_pos hn K) D)
      ((P₁.multiSession K).game (coinPow_pos hn K) D)) (ε.scale K) :=
  (ProbPkg.advBoundedOn_iff_gameBound (coinPow_pos hn K) _ _ _ _).mp
    (ProbPkg.multiSession_hybrid DistClass.all P₀ P₁ ε
      ((ProbPkg.advBoundedOn_iff_gameBound hn _ P₀ P₁ ε).mpr (fun D _ => h D)) K) D True.intro

/-- The hybrid for query-bounded distinguishers: `b` bounds the total number of queries over
    all sessions, and the single-session hypothesis is only used at budget `b`. -/
theorem ProbPkg.multiSession_advDist_le_within {n : Nat} {I : Iface} {σ₀ σ₁ : Type}
    (hn : 0 < n) (b : Nat)
    (P₀ : ProbPkg n I Iface.empty σ₀) (P₁ : ProbPkg n I Iface.empty σ₁) (ε : RatBound)
    (h : ∀ D : Code I Bool, Within b D →
      GameBound (AdvDist (P₀.game hn D) (P₁.game hn D)) ε)
    (K : Nat) (D : Code (Iface.sessions I K) Bool) (hD : Within b D) :
    GameBound (AdvDist ((P₀.multiSession K).game (coinPow_pos hn K) D)
      ((P₁.multiSession K).game (coinPow_pos hn K) D)) (ε.scale K) :=
  (ProbPkg.advBoundedOn_iff_gameBound (coinPow_pos hn K) _ _ _ _).mp
    (ProbPkg.multiSession_hybrid (DistClass.within b) P₀ P₁ ε
      ((ProbPkg.advBoundedOn_iff_gameBound hn _ P₀ P₁ ε).mpr h) K) D hD

/-! ## §6. `Spec.Refines` machines as packages -/

/-- Interface of a reactive machine: an input is answered by `some out` or by a rejection. -/
@[expose] def Iface.ofMachine (In Out : Type) : Iface := ⟨In, fun _ => Option Out⟩

/-- The machine `M` started in `s₀` as a closed package (`Machine.runStep` per query). -/
def Machine.toPkg {S In Out : Type} (M : Machine S In Out) (s₀ : S) :
    Pkg (Iface.ofMachine In Out) Iface.empty S where
  init := s₀
  handle s inp := .ret ((M.runStep s inp).2, (M.runStep s inp).1)

theorem Machine.toPkg_closedHandler {S In Out : Type} (M : Machine S In Out) (s₀ s : S)
    (inp : In) :
    (M.toPkg s₀).closedHandler s inp = ((M.runStep s inp).2, (M.runStep s inp).1) :=
  Code.evalClosed_ret _

/-- The machine `M` with its initial state drawn by the coin. -/
def Machine.toProbPkg {S In Out : Type} (M : Machine S In Out) {n : Nat} (init : Fin n → S) :
    ProbPkg n (Iface.ofMachine In Out) Iface.empty S :=
  ⟨fun ω => M.toPkg (init ω)⟩

/-- Under `C ⊑ A`, every adaptive multi-turn distinguisher outputs the same bit against `C`
    from `c₀` and against `A` from any related `a₀`. -/
theorem Refines.runBool_eq {S_c S_a In Out : Type} {C : Machine S_c In Out}
    {A : Machine S_a In Out} (sim : C ⊑ A) {c₀ : S_c} {a₀ : S_a} (hRel : sim.Rel c₀ a₀)
    (D : Code (Iface.ofMachine In Out) Bool) :
    (C.toPkg c₀).runBool D = (A.toPkg a₀).runBool D :=
  Code.evalState_sim (C.toPkg c₀).closedHandler (A.toPkg a₀).closedHandler sim.Rel
    (fun c a inp hR => by
      have e1 := Machine.toPkg_closedHandler C c₀ c inp
      have e2 := Machine.toPkg_closedHandler A a₀ a inp
      rw [e1, e2]
      exact sim.preserve_runStep inp hR) D c₀ a₀ hRel

/-- **Refinement gives advantage exactly `0`.** If `C ⊑ A`, the package of `C` on any
    coin-chosen initial states satisfying `C.Init` and the package of `A` on the abstracted
    initial states have the same win count against every distinguisher. -/
theorem Refines.toProbPkgEquiv {S_c S_a In Out : Type} {C : Machine S_c In Out}
    {A : Machine S_a In Out} (sim : C ⊑ A) {n : Nat} (hn : 0 < n) (init : Fin n → S_c)
    (hInit : ∀ ω, C.Init (init ω)) (D : Code (Iface.ofMachine In Out) Bool) :
    AdvDist ((C.toProbPkg init).game hn D)
      ((A.toProbPkg (fun ω => sim.absInit (init ω))).game hn D) = ⟨0, n, hn⟩ := by
  have e : ((C.toProbPkg init).game hn D).winCount =
      ((A.toProbPkg (fun ω => sim.absInit (init ω))).game hn D).winCount := by
    rw [ProbPkg.game_winCount, ProbPkg.game_winCount]
    exact Qsag.qsum_congr (fun ω => by
      show (if (C.toPkg (init ω)).runBool D then 1 else 0) =
        (if (A.toPkg (sim.absInit (init ω))).runBool D then 1 else 0)
      rw [sim.runBool_eq (sim.init_ok (hInit ω)).2 D])
  apply RatBound.ext
  · show natAbsDiff ((C.toProbPkg init).game hn D).winCount
      ((A.toProbPkg (fun ω => sim.absInit (init ω))).game hn D).winCount = 0
    rw [e, natAbsDiff_same]
  · rfl

/-- The same as an `AdvBoundedOn` statement, ready for `link`, `par` and `multiSession`. -/
theorem Refines.toProbPkg_advBounded {S_c S_a In Out : Type} {C : Machine S_c In Out}
    {A : Machine S_a In Out} (sim : C ⊑ A) {n : Nat} (init : Fin n → S_c)
    (hInit : ∀ ω, C.Init (init ω)) (Adm : Code (Iface.ofMachine In Out) Bool → Prop) :
    ProbPkg.AdvBoundedOn Adm (C.toProbPkg init)
      (A.toProbPkg (fun ω => sim.absInit (init ω))) RatBound.zero := by
  intro D _
  have e : (C.toProbPkg init).winCount D =
      (A.toProbPkg (fun ω => sim.absInit (init ω))).winCount D :=
    Qsag.qsum_congr (fun ω => by
      show (if (C.toPkg (init ω)).runBool D then 1 else 0) =
        (if (A.toPkg (sim.absInit (init ω))).runBool D then 1 else 0)
      rw [sim.runBool_eq (sim.init_ok (hInit ω)).2 D])
  rw [e, natAbsDiff_same, Nat.zero_mul]
  exact Nat.zero_le _

/-- Refinement composes concurrently: `K` interleaved sessions of `C` and of `A` are at
    advantage `0`. -/
theorem Refines.multiSession_advBounded {S_c S_a In Out : Type} {C : Machine S_c In Out}
    {A : Machine S_a In Out} (sim : C ⊑ A) {n : Nat} (init : Fin n → S_c)
    (hInit : ∀ ω, C.Init (init ω)) (K : Nat) :
    ProbPkg.AdvBoundedOn (DistClass.all.mem (Iface.sessions (Iface.ofMachine In Out) K))
      ((C.toProbPkg init).multiSession K)
      ((A.toProbPkg (fun ω => sim.absInit (init ω))).multiSession K) (RatBound.zero.scale K) :=
  ProbPkg.multiSession_hybrid DistClass.all _ _ RatBound.zero
    (sim.toProbPkg_advBounded init hInit _) K

/-! ## §7. `Qsag.OracleComp` adversaries, oracles and simulators as packages -/

/-- Interface of a function oracle `Dom → Cod`. -/
@[expose] def Iface.ofOracle (Dom Cod : Type) : Iface := ⟨Dom, fun _ => Cod⟩

/-- An `OracleComp` adversary as an oracle program over `Iface.ofOracle`. -/
def OracleComp.toCode {Dom Cod α : Type} :
    Qsag.OracleComp Dom Cod α → Code (Iface.ofOracle Dom Cod) α
  | .pure a => .ret a
  | .query q next => .call q (fun r => OracleComp.toCode (next r))

/-- An oracle program over `Iface.ofOracle` as an `OracleComp` adversary. -/
def Code.toOracleComp {Dom Cod α : Type} :
    Code (Iface.ofOracle Dom Cod) α → Qsag.OracleComp Dom Cod α
  | .ret a => .pure a
  | .call q k => .query q (fun r => Code.toOracleComp (k r))

theorem OracleComp.toCode_toOracleComp {Dom Cod α : Type} :
    ∀ c : Qsag.OracleComp Dom Cod α, Code.toOracleComp (OracleComp.toCode c) = c
  | .pure _ => by rfl
  | .query q next =>
    congrArg (Qsag.OracleComp.query q) (funext fun r => OracleComp.toCode_toOracleComp (next r))

theorem Code.toOracleComp_toCode {Dom Cod α : Type} :
    ∀ c : Code (Iface.ofOracle Dom Cod) α, OracleComp.toCode (Code.toOracleComp c) = c
  | .ret _ => by rfl
  | .call q k =>
    congrArg (Code.call q) (funext fun r => Code.toOracleComp_toCode (k r))

/-- The stateless closed package answering with the function `O`. -/
def Pkg.ofOracle {Dom Cod : Type} (O : Dom → Cod) :
    Pkg (Iface.ofOracle Dom Cod) Iface.empty Unit where
  init := ()
  handle s q := .ret (O q, s)

/-- An oracle drawn by the coin, as a probabilistic package. -/
def ProbPkg.ofOracle {n : Nat} {Dom Cod : Type} (O : Fin n → Dom → Cod) :
    ProbPkg n (Iface.ofOracle Dom Cod) Iface.empty Unit :=
  ⟨fun ω => Pkg.ofOracle (O ω)⟩

theorem Pkg.ofOracle_closedHandler {Dom Cod : Type} (O : Dom → Cod) (s : Unit) (q : Dom) :
    (Pkg.ofOracle O).closedHandler s q = (O q, s) :=
  Code.evalClosed_ret _

theorem ProbPkg.ofOracle_sample {n : Nat} {Dom Cod : Type} (O : Fin n → Dom → Cod) (ω : Fin n) :
    (ProbPkg.ofOracle O).sample ω = Pkg.ofOracle (O ω) := by rfl

/-- Coin-drawn oracles that coincide along a permutation of the coin space are at
    advantage `0`. -/
theorem ProbPkg.ofOracle_zero_of_coin_perm {n : Nat} {Dom Cod : Type}
    (O₀ O₁ : Fin n → Dom → Cod) (π πinv : Fin n → Fin n)
    (hL : ∀ i, πinv (π i) = i) (hR : ∀ j, π (πinv j) = j) (h : ∀ ω, O₀ ω = O₁ (π ω))
    (Adm : Code (Iface.ofOracle Dom Cod) Bool → Prop) :
    ProbPkg.AdvBoundedOn Adm (ProbPkg.ofOracle O₀) (ProbPkg.ofOracle O₁) RatBound.zero :=
  ProbPkg.advBoundedOn_zero_of_coin_perm _ _ π πinv hL hR
    (fun ω => by
      show Pkg.ofOracle (O₀ ω) = Pkg.ofOracle (O₁ (π ω))
      rw [h ω]) Adm

/-- `Spec.natAbsDiff` and the counting library's `Qsag.natAbsDiff` are the same function. -/
theorem natAbsDiff_eq_counting (a b : Nat) : natAbsDiff a b = Qsag.natAbsDiff a b :=
  (Qsag.natAbsDiff_eq a b).symm

/-- Running the embedded adversary against the oracle package is `evalOracleComp`. -/
theorem Code.evalState_ofOracle {Dom Cod α : Type} (O : Dom → Cod) :
    ∀ (c : Qsag.OracleComp Dom Cod α) (s : Unit),
      Code.evalState (Pkg.ofOracle O).closedHandler (OracleComp.toCode c) s =
        (Qsag.evalOracleComp O c, s)
  | .pure a, s => by
    show Code.evalState (Pkg.ofOracle O).closedHandler (Code.ret a) s = _
    rw [Code.evalState_ret]
    exact rfl
  | .query q next, s => by
    have e := Code.evalState_call (E := Iface.ofOracle Dom Cod) (Pkg.ofOracle O).closedHandler q
      (fun r => OracleComp.toCode (next r)) s
    rw [Pkg.ofOracle_closedHandler O s q] at e
    exact e.trans (Code.evalState_ofOracle O (next (O q)) s)

theorem Pkg.runBool_ofOracle {Dom Cod : Type} (O : Dom → Cod)
    (A : Qsag.OracleComp Dom Cod Bool) :
    (Pkg.ofOracle O).runBool (OracleComp.toCode A) = Qsag.evalOracleComp O A :=
  congrArg Prod.fst (Code.evalState_ofOracle O A ())

theorem ProbPkg.winCount_ofOracle {n : Nat} {Dom Cod : Type} (O : Fin n → Dom → Cod)
    (A : Qsag.OracleComp Dom Cod Bool) :
    (ProbPkg.ofOracle O).winCount (OracleComp.toCode A) =
      Qsag.qsum n (fun ω => if Qsag.evalOracleComp (O ω) A then 1 else 0) :=
  Qsag.qsum_congr (fun ω => by
    show (if (Pkg.ofOracle (O ω)).runBool (OracleComp.toCode A) then 1 else 0) = _
    rw [Pkg.runBool_ofOracle])

/-- Query budgets agree: `QueryBounded Q` adversaries are `Within Q` distinguishers. -/
theorem OracleComp.within_toCode {Dom Cod α : Type} :
    ∀ (Q : Nat) (c : Qsag.OracleComp Dom Cod α), Qsag.QueryBounded Q c →
      Within Q (OracleComp.toCode c)
  | Q, .pure a, _ => Within.ret Q a
  | 0, .query q next, h => False.elim ((Qsag.QueryBounded_zero_query q next).mp h)
  | Q + 1, .query q next, h => by
    have h := (Qsag.QueryBounded_succ_query Q q next).mp h
    show Within (Q + 1) (Code.call (E := Iface.ofOracle Dom Cod) q
      (fun r => OracleComp.toCode (next r)))
    exact Within.call (E := Iface.ofOracle Dom Cod) q (fun r => OracleComp.toCode (next r))
      (fun r => OracleComp.within_toCode Q (next r) (h r))

theorem Code.queryBounded_toOracleComp {Dom Cod α : Type} :
    ∀ (Q : Nat) (c : Code (Iface.ofOracle Dom Cod) α), Within Q c →
      Qsag.QueryBounded Q (Code.toOracleComp c)
  | Q, .ret a, _ => (Qsag.QueryBounded_pure Q a).mpr True.intro
  | Q + 1, .call q k, .call _ _ hk =>
    (Qsag.QueryBounded_succ_query Q q (fun r => Code.toOracleComp (k r))).mpr
      (fun y => Code.queryBounded_toOracleComp Q (k y) (hk y))

/-- **Import of standalone `OracleComp` bounds.** A bound stated over `Qsag.evalOracleComp`, for
    every `OracleComp` adversary of a class against two coin-indexed oracles, is an
    `AdvBoundedOn` bound between the two oracle packages. -/
theorem ProbPkg.advBoundedOn_ofOracle {n : Nat} {Dom Cod : Type} (O₀ O₁ : Fin n → Dom → Cod)
    (Adv : Qsag.OracleComp Dom Cod Bool → Prop) (ε : RatBound)
    (h : ∀ A : Qsag.OracleComp Dom Cod Bool, Adv A →
      Qsag.natAbsDiff (Qsag.qsum n (fun ω => if Qsag.evalOracleComp (O₀ ω) A then 1 else 0))
        (Qsag.qsum n (fun ω => if Qsag.evalOracleComp (O₁ ω) A then 1 else 0)) * ε.den ≤
        ε.num * n) :
    ProbPkg.AdvBoundedOn (fun D => Adv (Code.toOracleComp D)) (ProbPkg.ofOracle O₀)
      (ProbPkg.ofOracle O₁) ε := by
  intro D hD
  have h' := h (Code.toOracleComp D) hD
  rw [← ProbPkg.winCount_ofOracle, ← ProbPkg.winCount_ofOracle, Code.toOracleComp_toCode,
    ← natAbsDiff_eq_counting] at h'
  exact h'

/-- The same import for `Q`-query adversaries, landing in the class `DistClass.within Q`
    that `par` and `multiSession` preserve. -/
theorem ProbPkg.advBoundedOn_ofOracle_within {n : Nat} {Dom Cod : Type}
    (O₀ O₁ : Fin n → Dom → Cod) (Q : Nat) (ε : RatBound)
    (h : ∀ A : Qsag.OracleComp Dom Cod Bool, Qsag.QueryBounded Q A →
      Qsag.natAbsDiff (Qsag.qsum n (fun ω => if Qsag.evalOracleComp (O₀ ω) A then 1 else 0))
        (Qsag.qsum n (fun ω => if Qsag.evalOracleComp (O₁ ω) A then 1 else 0)) * ε.den ≤
        ε.num * n) :
    ProbPkg.AdvBoundedOn ((DistClass.within Q).mem (Iface.ofOracle Dom Cod))
      (ProbPkg.ofOracle O₀) (ProbPkg.ofOracle O₁) ε := by
  intro D hD
  exact ProbPkg.advBoundedOn_ofOracle O₀ O₁ (Qsag.QueryBounded Q) ε h D
    (Code.queryBounded_toOracleComp Q D hD)

/-- An `OracleComp` simulator, answering each query of `J` by an oracle computation over
    `Dom → Cod` and threading its own state, as an open package over the oracle interface. -/
def OracleComp.toPkg {Dom Cod : Type} {J : Iface} {τ : Type} (init : τ)
    (handle : τ → (q : J.Query) → Qsag.OracleComp Dom Cod (J.Resp q × τ)) :
    Pkg J (Iface.ofOracle Dom Cod) τ :=
  ⟨init, fun t q => OracleComp.toCode (handle t q)⟩

/-- The ideal game of an `OracleComp` simulator: the simulator linked with the coin-drawn
    oracle it queries. -/
def OracleComp.toProbPkg {n : Nat} {Dom Cod : Type} {J : Iface} {τ : Type} (init : τ)
    (handle : τ → (q : J.Query) → Qsag.OracleComp Dom Cod (J.Resp q × τ))
    (O : Fin n → Dom → Cod) : ProbPkg n J Iface.empty (τ × Unit) :=
  ProbPkg.linkDet (OracleComp.toPkg init handle) (ProbPkg.ofOracle O)

/-- Adequacy: each answer of the embedded game is the simulator's `evalOracleComp`. -/
theorem OracleComp.toProbPkg_closedHandler {n : Nat} {Dom Cod : Type} {J : Iface} {τ : Type}
    (init : τ) (handle : τ → (q : J.Query) → Qsag.OracleComp Dom Cod (J.Resp q × τ))
    (O : Fin n → Dom → Cod) (ω : Fin n) (t : τ) (q : J.Query) :
    ((OracleComp.toProbPkg init handle O).sample ω).closedHandler (t, ()) q =
      ((Qsag.evalOracleComp (O ω) (handle t q)).1,
        ((Qsag.evalOracleComp (O ω) (handle t q)).2, ())) := by
  show ((OracleComp.toPkg init handle).link (Pkg.ofOracle (O ω))).closedHandler (t, ()) q = _
  rw [Pkg.closedHandler_link]
  show ((Code.evalState (Pkg.ofOracle (O ω)).closedHandler (OracleComp.toCode (handle t q)) ()).1.1,
    ((Code.evalState (Pkg.ofOracle (O ω)).closedHandler (OracleComp.toCode (handle t q)) ()).1.2,
      (Code.evalState (Pkg.ofOracle (O ω)).closedHandler (OracleComp.toCode (handle t q)) ()).2)) = _
  rw [Code.evalState_ofOracle]

/-- A simulator inherits `link`: replacing the oracle under it preserves any bound. -/
theorem OracleComp.toProbPkg_congr {n : Nat} {Dom Cod : Type} {J : Iface} {τ : Type}
    (init : τ) (handle : τ → (q : J.Query) → Qsag.OracleComp Dom Cod (J.Resp q × τ))
    (O₀ O₁ : Fin n → Dom → Cod) (ε : RatBound)
    (h : ProbPkg.AdvBoundedOn (fun _ => True) (ProbPkg.ofOracle O₀) (ProbPkg.ofOracle O₁) ε) :
    ProbPkg.AdvBoundedOn (fun _ => True) (OracleComp.toProbPkg init handle O₀)
      (OracleComp.toProbPkg init handle O₁) ε :=
  ProbPkg.linkDet_congr (OracleComp.toPkg init handle) (fun _ _ => True.intro) h

/-- A simulator inherits concurrent composition: a single-session real/ideal bound `ε`
    against the embedded simulator game gives `K · ε` for `K` interleaved sessions, each
    session with its own simulator state and its own oracle. -/
theorem OracleComp.toProbPkg_multiSession (𝒞 : DistClass) {n : Nat} {Dom Cod : Type}
    {J : Iface} {σ τ : Type} (real : ProbPkg n J Iface.empty σ) (init : τ)
    (handle : τ → (q : J.Query) → Qsag.OracleComp Dom Cod (J.Resp q × τ))
    (O : Fin n → Dom → Cod) (ε : RatBound)
    (h : ProbPkg.AdvBoundedOn (𝒞.mem J) real (OracleComp.toProbPkg init handle O) ε) (K : Nat) :
    ProbPkg.AdvBoundedOn (𝒞.mem (Iface.sessions J K)) (real.multiSession K)
      ((OracleComp.toProbPkg init handle O).multiSession K) (ε.scale K) :=
  ProbPkg.multiSession_hybrid 𝒞 real _ ε h K

#verify_constructive
  Qsag.Spec.sampleSum_eq_qsum
  Qsag.Spec.advDist_eq_zero_of_coin_perm
  Qsag.Spec.Code.evalState_sim
  Qsag.Spec.Pkg.runBool_link
  Qsag.Spec.Within.reduce_singleCall
  Qsag.Spec.Pkg.runBool_par_absorbRight
  Qsag.Spec.Pkg.runBool_par_absorbLeft
  Qsag.Spec.ProbPkg.par_left_preserves_right
  Qsag.Spec.ProbPkg.advBoundedOn_iff_gameBound
  Qsag.Spec.ProbPkg.AdvBoundedOn.triangle
  Qsag.Spec.ProbPkg.advBoundedOn_of_slices
  Qsag.Spec.ProbPkg.advDist_linkDet
  Qsag.Spec.ProbPkg.linkDet_congr
  Qsag.Spec.ProbPkg.link_congr
  Qsag.Spec.ProbPkg.par_congr_left
  Qsag.Spec.ProbPkg.par_congr_right
  Qsag.Spec.coinPow_eq_pow
  Qsag.Spec.Iface.sessQuery_surjective
  Qsag.Spec.ProbPkg.multiSession_step
  Qsag.Spec.ProbPkg.advBoundedOn_zero_of_coin_perm
  Qsag.Spec.ProbPkg.multiSession_hybrid
  Qsag.Spec.ProbPkg.multiSession_advDist_le
  Qsag.Spec.ProbPkg.multiSession_advDist_le_within
  Qsag.Spec.Refines.runBool_eq
  Qsag.Spec.Refines.toProbPkgEquiv
  Qsag.Spec.Refines.toProbPkg_advBounded
  Qsag.Spec.Refines.multiSession_advBounded
  Qsag.Spec.OracleComp.toCode_toOracleComp
  Qsag.Spec.Code.toOracleComp_toCode
  Qsag.Spec.Pkg.runBool_ofOracle
  Qsag.Spec.OracleComp.within_toCode
  Qsag.Spec.ProbPkg.ofOracle_zero_of_coin_perm
  Qsag.Spec.Code.queryBounded_toOracleComp
  Qsag.Spec.ProbPkg.advBoundedOn_ofOracle
  Qsag.Spec.ProbPkg.advBoundedOn_ofOracle_within
  Qsag.Spec.OracleComp.toProbPkg_closedHandler
  Qsag.Spec.OracleComp.toProbPkg_congr
  Qsag.Spec.OracleComp.toProbPkg_multiSession

end Qsag.Spec
end

/-! ### Exports for lane misc -/

public section
namespace Qsag.Spec

theorem ProbPkg.par_sample {n m : Nat} {I₁ I₂ E : Iface} {σ₁ σ₂ : Type} (P : ProbPkg n I₁ E σ₁)
    (Q : ProbPkg m I₂ E σ₂) (ω : Fin (n * m)) :
    (P.par Q).sample ω = (P.sample (coinFst ω)).par (Q.sample (coinSnd ω)) := by rfl

theorem Pkg.ofOracle_init {Dom Cod : Type} (O : Dom → Cod) : (Pkg.ofOracle O).init = () := by rfl

theorem Machine.toPkg_init {S In Out : Type} (M : Machine S In Out) (s₀ : S) :
    (M.toPkg s₀).init = s₀ := by rfl

theorem Machine.toProbPkg_sample {S In Out : Type} (M : Machine S In Out) {n : Nat}
    (init : Fin n → S) (ω : Fin n) : (M.toProbPkg init).sample ω = M.toPkg (init ω) := by rfl

theorem Code.callSession_eq {I : Iface} {R : Type} (K : Nat) (sid : Fin K) (q : I.Query)
    (k : I.Resp q → Code (Iface.sessions I K) R) :
    Code.callSession K sid q k =
      Code.call (Iface.sessQuery K sid q) (fun r => k (Iface.sessResp K sid q r)) := by rfl

theorem sessCoin_zero {n : Nat} (K : Nat) (ω : Fin (coinPow n (K + 1))) (h : 0 < K + 1) :
    sessCoin (K + 1) ω ⟨0, h⟩ = coinFst ω := by rfl

theorem sessCoin_succ {n : Nat} (K : Nat) (ω : Fin (coinPow n (K + 1))) (j : Nat)
    (h : j + 1 < K + 1) :
    sessCoin (K + 1) ω ⟨j + 1, h⟩ = sessCoin K (coinSnd ω) ⟨j, Nat.lt_of_succ_lt_succ h⟩ := by
  rfl

/-- A distinguisher's call to session `sid` of `multiSession K P` continues with the answer
    of `P` on that session's coin and state; only that session's state is replaced. -/
theorem ProbPkg.multiSession_evalState_callSession {n : Nat} {I : Iface} {σ R : Type}
    (P : ProbPkg n I Iface.empty σ) (K : Nat) (ω : Fin (coinPow n K)) (st : SessState σ K)
    (sid : Fin K) (q : I.Query) (k : I.Resp q → Code (Iface.sessions I K) R) :
    Code.evalState ((P.multiSession K).sample ω).closedHandler (Code.callSession K sid q k) st =
      Code.evalState ((P.multiSession K).sample ω).closedHandler
        (k ((P.sample (sessCoin K ω sid)).closedHandler (SessState.get K st sid) q).1)
        (SessState.set K st sid
          ((P.sample (sessCoin K ω sid)).closedHandler (SessState.get K st sid) q).2) := by
  have h := ProbPkg.multiSession_step P K ω st sid q
  rw [Code.callSession_eq, Code.evalState_call, h.1, h.2]

#verify_constructive
  Qsag.Spec.ProbPkg.multiSession_evalState_callSession

end Qsag.Spec
end

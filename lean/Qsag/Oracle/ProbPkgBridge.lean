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

module
/-
# Qsag.Tests.ProbPkgBridgeTeeth — the hypotheses of the package calculus are needed

1. `tooth_shared_coins_break_par_congruence`: two oracles that no single-session
   distinguisher can tell apart are told apart with advantage `1` once both components of a
   parallel composition read the same coin. `ProbPkg.par` draws independent coins, and
   `echo_flip_par_perfect` is the bound it gives for the same pair.
2. `tooth_multiSession_exceeds_single_session_bound`: a pair at single-session advantage
   exactly `1/2` is at advantage `3/4` over two sessions. The factor `K` of
   `ProbPkg.multiSession_hybrid` cannot be dropped; `echo_zero_two_sessions` is the `2 · 1/2`
   bound the theorem gives.
3. `tooth_output_mismatch_breaks_refinement_equivalence`: without the output clause of
   `Refines.sim_ok` two machines are told apart with advantage `1`.
4. The keyed-ROM hiding game of `Qsag.Top.ProbPkgGames` on two key slots.
   `keyedRom_two_slot_bound` is the `1/2` bound for one query, and
   `keyedRom_two_slot_bound_attained` shows a one-query distinguisher reaches it (the bound
   `0` fails). `tooth_keyedRom_bound_fails_without_query_budget`: a two-query distinguisher
   reads both slots and has advantage `1`, so the bound `1/2` fails for the class of all
   distinguishers. `tooth_keyedRom_multiSession_fails_without_query_budget`: over two
   sessions the budget-`0` bound fails for a distinguisher that asks session `1` once.
-/
public import Qsag.Oracle.ProbPkgBridge
public import Qsag.Top.ProbPkgGames
public import Qsag.Spec.GameBound
public import Qsag.Spec.Refines
public import Qsag.Spec.Primitives
public import Qsag.Math.Counting
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spec.ProbPkgTeeth

set_option autoImplicit false

/-! ## Evaluation equations for the fixtures

The interpreter (`Code.evalState`, `Pkg.par`, `Code.callSession`, `ProbPkg.multiSession`) is sealed
in its owning modules. The executed counts below are derived from the exported equations of
those modules; these four lemmas put them in the shape of an oracle-package call. -/

/-- One call against an oracle package. -/
theorem evalState_ofOracle_call {Dom Cod R : Type} (O : Dom → Cod) (q : Dom)
    (k : Cod → Code (Iface.ofOracle Dom Cod) R) (s : Unit) :
    Code.evalState (Pkg.ofOracle O).closedHandler (Code.call q k) s =
      Code.evalState (Pkg.ofOracle O).closedHandler (k (O q)) s := by
  have e := Code.evalState_call (E := Iface.ofOracle Dom Cod) (Pkg.ofOracle O).closedHandler q k s
  rw [Pkg.ofOracle_closedHandler O s q] at e
  exact e

/-- One call to the left component of a pair of oracle packages. -/
theorem evalState_par_ofOracle_inl {D₁ C₁ D₂ C₂ R : Type} (O₁ : D₁ → C₁) (O₂ : D₂ → C₂) (q : D₁)
    (k : C₁ → Code (Iface.sum (Iface.ofOracle D₁ C₁) (Iface.ofOracle D₂ C₂)) R) (s₁ s₂ : Unit) :
    Code.evalState ((Pkg.ofOracle O₁).par (Pkg.ofOracle O₂)).closedHandler
        (Code.call (PSum.inl q) k) (s₁, s₂) =
      Code.evalState ((Pkg.ofOracle O₁).par (Pkg.ofOracle O₂)).closedHandler (k (O₁ q))
        (s₁, s₂) := by
  have e := Code.evalState_call (E := Iface.sum (Iface.ofOracle D₁ C₁) (Iface.ofOracle D₂ C₂))
    ((Pkg.ofOracle O₁).par (Pkg.ofOracle O₂)).closedHandler (PSum.inl q) k (s₁, s₂)
  rw [Pkg.closedHandler_par_inl (Pkg.ofOracle O₁) (Pkg.ofOracle O₂) s₁ s₂ q,
    Pkg.ofOracle_closedHandler O₁ s₁ q] at e
  exact e

/-- One call to the right component of a pair of oracle packages. -/
theorem evalState_par_ofOracle_inr {D₁ C₁ D₂ C₂ R : Type} (O₁ : D₁ → C₁) (O₂ : D₂ → C₂) (q : D₂)
    (k : C₂ → Code (Iface.sum (Iface.ofOracle D₁ C₁) (Iface.ofOracle D₂ C₂)) R) (s₁ s₂ : Unit) :
    Code.evalState ((Pkg.ofOracle O₁).par (Pkg.ofOracle O₂)).closedHandler
        (Code.call (PSum.inr q) k) (s₁, s₂) =
      Code.evalState ((Pkg.ofOracle O₁).par (Pkg.ofOracle O₂)).closedHandler (k (O₂ q))
        (s₁, s₂) := by
  have e := Code.evalState_call (E := Iface.sum (Iface.ofOracle D₁ C₁) (Iface.ofOracle D₂ C₂))
    ((Pkg.ofOracle O₁).par (Pkg.ofOracle O₂)).closedHandler (PSum.inr q) k (s₁, s₂)
  rw [Pkg.closedHandler_par_inr (Pkg.ofOracle O₁) (Pkg.ofOracle O₂) s₁ s₂ q,
    Pkg.ofOracle_closedHandler O₂ s₂ q] at e
  exact e

/-- One session call against `K` sessions of a coin-drawn oracle: session `sid` answers with
    the oracle of its own coin. -/
theorem evalState_multiSession_ofOracle_callSession {n : Nat} {Dom Cod R : Type}
    (O : Fin n → Dom → Cod) (K : Nat) (ω : Fin (coinPow n K)) (st : SessState Unit K)
    (sid : Fin K) (q : Dom) (k : Cod → Code (Iface.sessions (Iface.ofOracle Dom Cod) K) R) :
    Code.evalState (((ProbPkg.ofOracle O).multiSession K).sample ω).closedHandler
        (Code.callSession (I := Iface.ofOracle Dom Cod) K sid q k) st =
      Code.evalState (((ProbPkg.ofOracle O).multiSession K).sample ω).closedHandler
        (k (O (sessCoin K ω sid) q)) (SessState.set K st sid (SessState.get K st sid)) := by
  have e := ProbPkg.evalState_multiSession_callSession (ProbPkg.ofOracle O) K ω st sid q k
  rw [ProbPkg.ofOracle_sample O (sessCoin K ω sid),
    Pkg.ofOracle_closedHandler (O (sessCoin K ω sid)) (SessState.get K st sid) q] at e
  exact e

/-- A sum over the coins of two sessions is the iterated sum over the two session coins. -/
theorem qsum_two_session_coins {n : Nat} (f : Fin n → Fin n → Nat) :
    Qsag.qsum (coinPow n 2) (fun ω => f (coinFst ω) (coinFst (coinSnd ω))) =
      Qsag.qsum n (fun a => Qsag.qsum n (fun b => f a b)) := by
  show Qsag.qsum (n * (n * 1))
    (fun ω : Fin (n * (n * 1)) => f (coinFst ω) (coinFst (coinSnd ω))) = _
  rw [qsum_coinPair]
  refine Qsag.qsum_congr (fun a => ?_)
  simp only [coinFst_pair, coinSnd_pair]
  rw [qsum_coinPair]
  refine Qsag.qsum_congr (fun b => ?_)
  simp only [coinFst_pair]
  exact Nat.add_zero _

/-- One call against a machine package. -/
theorem evalState_toPkg_call {S In Out R : Type} (M : Machine S In Out) (s₀ s : S) (q : In)
    (k : Option Out → Code (Iface.ofMachine In Out) R) :
    Code.evalState (M.toPkg s₀).closedHandler (Code.call q k) s =
      Code.evalState (M.toPkg s₀).closedHandler (k (M.runStep s q).2) (M.runStep s q).1 := by
  have e := Code.evalState_call (E := Iface.ofMachine In Out) (M.toPkg s₀).closedHandler q k s
  rw [Machine.toPkg_closedHandler M s₀ s q] at e
  exact e

/-- One-bit oracle interface: the query `()` is answered by a bit. -/
abbrev bitIface : Iface := Iface.ofOracle Unit Bool

/-- Answers every query with the coin bit. -/
def echoBit : ProbPkg 2 bitIface Iface.empty Unit :=
  ProbPkg.ofOracle (fun ω _ => decide (ω.1 = 1))

/-- Answers every query with the complement of the coin bit. -/
def flipBit : ProbPkg 2 bitIface Iface.empty Unit :=
  ProbPkg.ofOracle (fun ω _ => decide (ω.1 = 0))

/-- Answers every query with `false`. -/
def zeroBit : ProbPkg 2 bitIface Iface.empty Unit :=
  ProbPkg.ofOracle (fun _ _ => false)

/-- Parallel composition in which both components read the same coin. -/
def sharedPar {n : Nat} {I₁ I₂ E : Iface} {σ₁ σ₂ : Type} (P : ProbPkg n I₁ E σ₁)
    (Q : ProbPkg n I₂ E σ₂) : ProbPkg n (Iface.sum I₁ I₂) E (σ₁ × σ₂) :=
  ⟨fun ω => (P.sample ω).par (Q.sample ω)⟩

/-- Query both components and compare the answers. -/
def compareBoth : Code (Iface.sum bitIface bitIface) Bool :=
  .call (.inl ()) (fun (a : Bool) => .call (.inr ()) (fun (b : Bool) => .ret (a == b)))

/-- A uniform bit and its complement are identically distributed. -/
theorem echo_flip_perfect (Adm : Code bitIface Bool → Prop) :
    ProbPkg.AdvBoundedOn Adm echoBit flipBit RatBound.zero := by
  intro D _
  have e : echoBit.winCount D = flipBit.winCount D := by
    rw [ProbPkg.winCount_eq, ProbPkg.winCount_eq]
    simp only [echoBit, flipBit, ProbPkg.ofOracle_sample]
    show (if (Pkg.ofOracle (fun _ : Unit => false)).runBool D then 1 else 0) +
        ((if (Pkg.ofOracle (fun _ : Unit => true)).runBool D then 1 else 0) + 0) =
      (if (Pkg.ofOracle (fun _ : Unit => true)).runBool D then 1 else 0) +
        ((if (Pkg.ofOracle (fun _ : Unit => false)).runBool D then 1 else 0) + 0)
    rw [Nat.add_zero, Nat.add_zero, Nat.add_comm]
  rw [e, natAbsDiff_same, Nat.zero_mul]
  exact Nat.zero_le _

/-- With independent coins the pair stays perfectly indistinguishable next to any package. -/
theorem echo_flip_par_perfect :
    ProbPkg.AdvBoundedOn (DistClass.all.mem (Iface.sum bitIface bitIface))
      (echoBit.par echoBit) (flipBit.par echoBit) RatBound.zero :=
  ProbPkg.par_congr_left DistClass.all echoBit (echo_flip_perfect _)

/-- Executed count: with a shared coin both components answer alike on both coins. -/
theorem sharedPar_echo_echo_winCount : (sharedPar echoBit echoBit).winCount compareBoth = 2 := by
  rw [ProbPkg.winCount_eq]
  simp only [sharedPar, echoBit, compareBoth, ProbPkg.ofOracle_sample, Pkg.runBool_eq,
    Pkg.par_init, evalState_par_ofOracle_inl, evalState_par_ofOracle_inr, Code.evalState_ret]
  decide

/-- Executed count: a bit and its complement of the same coin never answer alike. -/
theorem sharedPar_flip_echo_winCount : (sharedPar flipBit echoBit).winCount compareBoth = 0 := by
  rw [ProbPkg.winCount_eq]
  simp only [sharedPar, echoBit, flipBit, compareBoth, ProbPkg.ofOracle_sample, Pkg.runBool_eq,
    Pkg.par_init, evalState_par_ofOracle_inl, evalState_par_ofOracle_inr, Code.evalState_ret]
  decide

/-- With a shared coin the same pair is distinguished on every coin. -/
theorem tooth_shared_coins_break_par_congruence :
    ¬ ProbPkg.AdvBoundedOn (DistClass.all.mem (Iface.sum bitIface bitIface))
      (sharedPar echoBit echoBit) (sharedPar flipBit echoBit) RatBound.zero := fun h => by
  have hh := h compareBoth (DistClass.mem_all _)
  rw [sharedPar_echo_echo_winCount, sharedPar_flip_echo_winCount] at hh
  exact absurd hh (by decide)

/-- Single-session advantage between the coin bit and the constant `false` is at most `1/2`. -/
theorem echo_zero_half (Adm : Code bitIface Bool → Prop) :
    ProbPkg.AdvBoundedOn Adm echoBit zeroBit ⟨1, 2, by decide⟩ := by
  intro D _
  have key : ∀ x y : Bool,
      natAbsDiff ((if x then 1 else 0) + ((if y then 1 else 0) + 0))
        ((if x then 1 else 0) + ((if x then 1 else 0) + 0)) * 2 ≤ 1 * 2 := by decide
  rw [ProbPkg.winCount_eq, ProbPkg.winCount_eq]
  simp only [echoBit, zeroBit, ProbPkg.ofOracle_sample]
  exact key ((Pkg.ofOracle (fun _ : Unit => false)).runBool D)
    ((Pkg.ofOracle (fun _ : Unit => true)).runBool D)

/-- Ask session `0` and session `1`, output the disjunction. -/
def orOfTwoSessions : Code (Iface.sessions bitIface 2) Bool :=
  Code.callSession 2 ⟨0, by decide⟩ () (fun (a : Bool) =>
    Code.callSession 2 ⟨1, by decide⟩ () (fun (b : Bool) => .ret (a || b)))

/-- The bound of the hybrid theorem for two sessions: `2 · 1/2`. -/
theorem echo_zero_two_sessions :
    ProbPkg.AdvBoundedOn (DistClass.all.mem (Iface.sessions bitIface 2))
      (echoBit.multiSession 2) (zeroBit.multiSession 2) (RatBound.scale 2 ⟨1, 2, by decide⟩) :=
  ProbPkg.multiSession_hybrid DistClass.all echoBit zeroBit _ (echo_zero_half _) 2

/-- Executed count: the disjunction of two independent coin bits is `true` on 3 of 4 coins. -/
theorem echo_two_sessions_winCount : (echoBit.multiSession 2).winCount orOfTwoSessions = 3 := by
  rw [ProbPkg.winCount_eq]
  simp only [echoBit, orOfTwoSessions, Pkg.runBool_eq,
    evalState_multiSession_ofOracle_callSession, Code.evalState_ret, sessCoin.public_eqs]
  exact (qsum_two_session_coins (n := 2)
    (fun a b => if (decide (a.1 = 1) || decide (b.1 = 1)) = true then 1 else 0)).trans (by decide)

/-- Executed count: the constant `false` oracle never answers `true`. -/
theorem zero_two_sessions_winCount : (zeroBit.multiSession 2).winCount orOfTwoSessions = 0 := by
  rw [ProbPkg.winCount_eq]
  simp only [zeroBit, orOfTwoSessions, Pkg.runBool_eq,
    evalState_multiSession_ofOracle_callSession, Code.evalState_ret]
  decide

/-- Two sessions exceed the single-session bound `1/2`: the advantage is `3/4`. -/
theorem tooth_multiSession_exceeds_single_session_bound :
    ¬ ProbPkg.AdvBoundedOn (DistClass.all.mem (Iface.sessions bitIface 2))
      (echoBit.multiSession 2) (zeroBit.multiSession 2) ⟨1, 2, by decide⟩ := fun h => by
  have hh := h orOfTwoSessions (DistClass.mem_all _)
  rw [echo_two_sessions_winCount, zero_two_sessions_winCount] at hh
  exact absurd hh (by decide)

/-- Stateless machine answering every input with the fixed bit `b`. -/
def constMachine (b : Bool) : Machine Unit Unit Bool :=
  Machine.ofTotal (fun _ => True) (fun s _ => (s, b))

/-- One query; output the answered bit. -/
def readAnswer : Code (Iface.ofMachine Unit Bool) Bool :=
  .call () (fun (r : Option Bool) => .ret (r.getD false))

/-- Executed count: on the single coin, `readAnswer` outputs the machine's fixed bit. -/
theorem constMachine_winCount (b : Bool) :
    ((constMachine b).toProbPkg (n := 1) (fun _ => ())).winCount readAnswer =
      if b then 1 else 0 := by
  rw [ProbPkg.winCount_eq]
  simp only [readAnswer, Machine.toProbPkg.public_eqs, Pkg.runBool_eq, evalState_toPkg_call,
    Code.evalState_ret, constMachine, Machine.runStep, Machine.ofTotal]
  cases b <;> decide

/-- Machines with related states but different outputs are distinguished on every coin. -/
theorem tooth_output_mismatch_breaks_refinement_equivalence :
    ¬ ProbPkg.AdvBoundedOn (DistClass.all.mem (Iface.ofMachine Unit Bool))
      ((constMachine true).toProbPkg (n := 1) (fun _ => ()))
      ((constMachine false).toProbPkg (n := 1) (fun _ => ())) RatBound.zero := fun h => by
  have hh := h readAnswer (DistClass.mem_all _)
  rw [constMachine_winCount, constMachine_winCount] at hh
  exact absurd hh (by decide)

/-! ## The keyed-ROM hiding game on two key slots -/

/-- Two key slots, one tag, bit answers. -/
abbrev twoSlotIface : Iface := Qsag.Top.keyedRomIface 2 Unit Bool

/-- Real world: the hidden slot answers `true`, the other slot `false`. -/
def twoSlotReal : ProbPkg 2 twoSlotIface Iface.empty Unit :=
  Qsag.Top.keyedRomReal (fun _ => false) (fun _ => true)

/-- Ideal world: both slots answer `false`. -/
def twoSlotIdeal : ProbPkg 2 twoSlotIface Iface.empty Unit :=
  Qsag.Top.keyedRomIdeal (fun _ => false)

/-- Ask slot `0`, output the answer. -/
def probeSlotZero : Code twoSlotIface Bool :=
  .call (⟨0, by decide⟩, ()) (fun (a : Bool) => .ret a)

/-- Ask slot `0` and slot `1`, output the disjunction. -/
def readBothSlots : Code twoSlotIface Bool :=
  .call (⟨0, by decide⟩, ()) (fun (a : Bool) =>
    .call (⟨1, by decide⟩, ()) (fun (b : Bool) => .ret (a || b)))

/-- Ask slot `0` of session `1`, output the answer. -/
def probeSessionOne : Code (Iface.sessions twoSlotIface 2) Bool :=
  Code.callSession (I := twoSlotIface) 2 ⟨1, by decide⟩ (⟨0, by decide⟩, ())
    (fun (a : Bool) => .ret a)

theorem probeSlotZero_within : Within 1 probeSlotZero :=
  Within.call (E := twoSlotIface) _ _ (fun r => Within.ret 0 r)

/-- One query against two slots: advantage at most `1/2`. The only premise of
    `Qsag.Top.keyedRom_hiding_advBoundedOn` is `0 < cardB`, so this closed instance is its
    positive witness. -/
theorem keyedRom_two_slot_bound :
    ProbPkg.AdvBoundedOn ((DistClass.within 1).mem twoSlotIface) twoSlotReal twoSlotIdeal
      ⟨1, 2, by decide⟩ :=
  Qsag.Top.keyedRom_hiding_advBoundedOn 2 1 (by decide) _ _

/-- Executed counts of the two-slot game. -/
theorem twoSlotReal_probeSlotZero_winCount : twoSlotReal.winCount probeSlotZero = 1 := by
  rw [ProbPkg.winCount_eq]
  simp only [twoSlotReal, probeSlotZero, Qsag.Top.keyedRomReal_eq, ProbPkg.ofOracle_sample,
    Pkg.runBool_eq, evalState_ofOracle_call, Code.evalState_ret]
  decide

theorem twoSlotIdeal_probeSlotZero_winCount : twoSlotIdeal.winCount probeSlotZero = 0 := by
  rw [ProbPkg.winCount_eq]
  simp only [twoSlotIdeal, probeSlotZero, Qsag.Top.keyedRomIdeal_eq, ProbPkg.ofOracle_sample,
    Pkg.runBool_eq, evalState_ofOracle_call, Code.evalState_ret]
  decide

theorem twoSlotReal_readBothSlots_winCount : twoSlotReal.winCount readBothSlots = 2 := by
  rw [ProbPkg.winCount_eq]
  simp only [twoSlotReal, readBothSlots, Qsag.Top.keyedRomReal_eq, ProbPkg.ofOracle_sample,
    Pkg.runBool_eq, evalState_ofOracle_call, Code.evalState_ret]
  decide

theorem twoSlotIdeal_readBothSlots_winCount : twoSlotIdeal.winCount readBothSlots = 0 := by
  rw [ProbPkg.winCount_eq]
  simp only [twoSlotIdeal, readBothSlots, Qsag.Top.keyedRomIdeal_eq, ProbPkg.ofOracle_sample,
    Pkg.runBool_eq, evalState_ofOracle_call, Code.evalState_ret]
  decide

theorem twoSlotReal_probeSessionOne_winCount :
    (twoSlotReal.multiSession 2).winCount probeSessionOne = 2 := by
  rw [ProbPkg.winCount_eq]
  simp only [twoSlotReal, probeSessionOne, Qsag.Top.keyedRomReal_eq, Pkg.runBool_eq,
    evalState_multiSession_ofOracle_callSession, Code.evalState_ret, sessCoin.public_eqs]
  exact (qsum_two_session_coins (n := 2)
    (fun _ b => if Qsag.Top.keyedRomRealOracle (fun _ => false) (fun _ => true) b
      (⟨0, by decide⟩, ()) = true then 1 else 0)).trans (by decide)

theorem twoSlotIdeal_probeSessionOne_winCount :
    (twoSlotIdeal.multiSession 2).winCount probeSessionOne = 0 := by
  rw [ProbPkg.winCount_eq]
  simp only [twoSlotIdeal, probeSessionOne, Qsag.Top.keyedRomIdeal_eq, Pkg.runBool_eq,
    evalState_multiSession_ofOracle_callSession, Code.evalState_ret]
  decide

/-- The one-query bound is attained: `probeSlotZero` has advantage exactly `1/2`, so the
    bound `0` fails for the same class. -/
theorem keyedRom_two_slot_bound_attained :
    ¬ ProbPkg.AdvBoundedOn ((DistClass.within 1).mem twoSlotIface) twoSlotReal twoSlotIdeal
      ⟨0, 2, by decide⟩ := fun h => by
  have hh := h probeSlotZero ((DistClass.mem_within_iff 1 _).mpr probeSlotZero_within)
  rw [twoSlotReal_probeSlotZero_winCount, twoSlotIdeal_probeSlotZero_winCount] at hh
  exact absurd hh (by decide)

/-- Without the query budget the one-query bound fails: reading both slots finds the hidden
    one on every coin. -/
theorem tooth_keyedRom_bound_fails_without_query_budget :
    ¬ ProbPkg.AdvBoundedOn (DistClass.all.mem twoSlotIface) twoSlotReal twoSlotIdeal
      ⟨1, 2, by decide⟩ := fun h => by
  have hh := h readBothSlots (DistClass.mem_all _)
  rw [twoSlotReal_readBothSlots_winCount, twoSlotIdeal_readBothSlots_winCount] at hh
  exact absurd hh (by decide)

/-- Two sessions, no queries allowed: the bound of
    `Qsag.Top.keyedRom_hiding_multiSession` is `2 · 0/2`. -/
theorem keyedRom_two_sessions_zero_budget :
    ProbPkg.AdvBoundedOn ((DistClass.within 0).mem (Iface.sessions twoSlotIface 2))
      (twoSlotReal.multiSession 2) (twoSlotIdeal.multiSession 2)
      (RatBound.scale 2 ⟨0, 2, by decide⟩) :=
  Qsag.Top.keyedRom_hiding_multiSession 2 0 (by decide) _ _ 2

/-- Without the query budget the two-session bound fails: one query to session `1` hits that
    session's hidden slot on half of the coins. -/
theorem tooth_keyedRom_multiSession_fails_without_query_budget :
    ¬ ProbPkg.AdvBoundedOn (DistClass.all.mem (Iface.sessions twoSlotIface 2))
      (twoSlotReal.multiSession 2) (twoSlotIdeal.multiSession 2)
      (RatBound.scale 2 ⟨0, 2, by decide⟩) := fun h => by
  have hh := h probeSessionOne (DistClass.mem_all _)
  rw [twoSlotReal_probeSessionOne_winCount, twoSlotIdeal_probeSessionOne_winCount] at hh
  exact absurd hh (by decide)

#verify_constructive
  Qsag.Spec.ProbPkgTeeth.keyedRom_two_slot_bound
  Qsag.Spec.ProbPkgTeeth.keyedRom_two_slot_bound_attained
  Qsag.Spec.ProbPkgTeeth.tooth_keyedRom_bound_fails_without_query_budget
  Qsag.Spec.ProbPkgTeeth.keyedRom_two_sessions_zero_budget
  Qsag.Spec.ProbPkgTeeth.tooth_keyedRom_multiSession_fails_without_query_budget

#tooth_pair Qsag.Spec.ProbPkgTeeth.keyedRom_two_slot_bound vs
  Qsag.Spec.ProbPkgTeeth.tooth_keyedRom_bound_fails_without_query_budget
#tooth_pair Qsag.Spec.ProbPkgTeeth.keyedRom_two_sessions_zero_budget vs
  Qsag.Spec.ProbPkgTeeth.tooth_keyedRom_multiSession_fails_without_query_budget

#verify_constructive
  Qsag.Spec.ProbPkgTeeth.echo_flip_perfect
  Qsag.Spec.ProbPkgTeeth.echo_flip_par_perfect
  Qsag.Spec.ProbPkgTeeth.tooth_shared_coins_break_par_congruence
  Qsag.Spec.ProbPkgTeeth.echo_zero_half
  Qsag.Spec.ProbPkgTeeth.echo_zero_two_sessions
  Qsag.Spec.ProbPkgTeeth.tooth_multiSession_exceeds_single_session_bound
  Qsag.Spec.ProbPkgTeeth.tooth_output_mismatch_breaks_refinement_equivalence

#tooth_pair Qsag.Spec.ProbPkg.par_congr_left vs
  Qsag.Spec.ProbPkgTeeth.tooth_shared_coins_break_par_congruence
#tooth_pair Qsag.Spec.ProbPkg.multiSession_hybrid vs
  Qsag.Spec.ProbPkgTeeth.tooth_multiSession_exceeds_single_session_bound
#tooth_pair Qsag.Spec.Refines.toProbPkg_advBounded vs
  Qsag.Spec.ProbPkgTeeth.tooth_output_mismatch_breaks_refinement_equivalence

end Qsag.Spec.ProbPkgTeeth
end

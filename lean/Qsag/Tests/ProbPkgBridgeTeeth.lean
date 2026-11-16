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
    simp only [Qsag.qsum_succ, Qsag.qsum_zero, echoBit, flipBit, ProbPkg.ofOracle_sample]
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

/-- `compareBoth` against two oracle packages in parallel outputs whether the answers agree. -/
theorem runBool_par_compareBoth (a b : Unit → Bool) :
    ((Pkg.ofOracle a).par (Pkg.ofOracle b)).runBool compareBoth = (a () == b ()) := by
  rw [Pkg.runBool_eq, Pkg.par_init, Pkg.ofOracle_init]
  unfold compareBoth
  rw (config := { transparency := .default }) [Code.evalState_call, Pkg.closedHandler_par_inl, Pkg.ofOracle_closedHandler]
  dsimp only
  rw (config := { transparency := .default }) [Code.evalState_call, Pkg.closedHandler_par_inr, Pkg.ofOracle_closedHandler,
    Code.evalState_ret]

/-- Win count of `compareBoth` against two coin-drawn oracles reading the same coin. -/
theorem sharedPar_winCount_compareBoth (O₁ O₂ : Fin 2 → Unit → Bool) :
    (sharedPar (ProbPkg.ofOracle O₁) (ProbPkg.ofOracle O₂)).winCount compareBoth =
      Qsag.qsum 2 (fun ω => if (O₁ ω () == O₂ ω ()) then 1 else 0) :=
  (ProbPkg.winCount_eq _ _).trans (Qsag.qsum_congr fun ω => by
    show (if (((ProbPkg.ofOracle O₁).sample ω).par
        ((ProbPkg.ofOracle O₂).sample ω)).runBool compareBoth then 1 else 0) = _
    rw [ProbPkg.ofOracle_sample, ProbPkg.ofOracle_sample, runBool_par_compareBoth])

/-- With a shared coin the same pair is distinguished on every coin. -/
theorem tooth_shared_coins_break_par_congruence :
    ¬ ProbPkg.AdvBoundedOn (DistClass.all.mem (Iface.sum bitIface bitIface))
      (sharedPar echoBit echoBit) (sharedPar flipBit echoBit) RatBound.zero :=
  fun h => absurd (h compareBoth (DistClass.mem_all _)) (by
    unfold echoBit flipBit
    rw [sharedPar_winCount_compareBoth, sharedPar_winCount_compareBoth]
    decide)

/-- Single-session advantage between the coin bit and the constant `false` is at most `1/2`. -/
theorem echo_zero_half (Adm : Code bitIface Bool → Prop) :
    ProbPkg.AdvBoundedOn Adm echoBit zeroBit ⟨1, 2, by decide⟩ := by
  intro D _
  rw [ProbPkg.winCount_eq, ProbPkg.winCount_eq]
  simp only [Qsag.qsum_succ, Qsag.qsum_zero, echoBit, zeroBit, ProbPkg.ofOracle_sample]
  have key : ∀ x y : Bool,
      natAbsDiff ((if x then 1 else 0) + ((if y then 1 else 0) + 0))
        ((if x then 1 else 0) + ((if x then 1 else 0) + 0)) * 2 ≤ 1 * 2 := by decide
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

/-- Coin of session `0` inside a two-session coin over `Fin 2`: the high bit. -/
theorem sessCoin_two_zero_val (ω : Fin (coinPow 2 2)) :
    (sessCoin 2 ω ⟨0, by decide⟩).1 = ω.1 / 2 :=
  (congrArg Fin.val (sessCoin_zero 1 ω (by decide))).trans (coinFst_val ω)

/-- Coin of session `1` inside a two-session coin over `Fin 2`: the low bit. -/
theorem sessCoin_two_one_val (ω : Fin (coinPow 2 2)) :
    (sessCoin 2 ω ⟨1, by decide⟩).1 = ω.1 % 2 :=
  ((congrArg Fin.val ((sessCoin_succ 1 ω 0 (by decide)).trans
    (sessCoin_zero 0 (coinSnd ω) (by decide)))).trans
    ((coinFst_val (coinSnd ω)).trans (congrArg (· / 1) (coinSnd_val ω)))).trans
    (Nat.div_one _)

/-- `orOfTwoSessions` against two sessions of a coin-drawn oracle: the disjunction of the two
    sessions' answers, each on its own coin. -/
theorem multiSession_runBool_orOfTwoSessions (O : Fin 2 → Unit → Bool)
    (ω : Fin (coinPow 2 2)) :
    (((ProbPkg.ofOracle O).multiSession 2).sample ω).runBool orOfTwoSessions =
      (O (sessCoin 2 ω ⟨0, by decide⟩) () || O (sessCoin 2 ω ⟨1, by decide⟩) ()) := by
  rw [Pkg.runBool_eq]
  unfold orOfTwoSessions
  rw (config := { transparency := .default }) [ProbPkg.multiSession_evalState_callSession, ProbPkg.multiSession_evalState_callSession,
    Code.evalState_ret, ProbPkg.ofOracle_sample, ProbPkg.ofOracle_sample,
    Pkg.ofOracle_closedHandler, Pkg.ofOracle_closedHandler]

theorem echoBit_two_sessions_winCount :
    (echoBit.multiSession 2).winCount orOfTwoSessions =
      Qsag.qsum (coinPow 2 2)
        (fun ω => if (decide (ω.1 / 2 = 1) || decide (ω.1 % 2 = 1)) then 1 else 0) :=
  (ProbPkg.winCount_eq _ _).trans (Qsag.qsum_congr fun ω => by
    unfold echoBit
    rw [multiSession_runBool_orOfTwoSessions, sessCoin_two_zero_val, sessCoin_two_one_val])

theorem zeroBit_two_sessions_winCount :
    (zeroBit.multiSession 2).winCount orOfTwoSessions =
      Qsag.qsum (coinPow 2 2) (fun _ => 0) :=
  (ProbPkg.winCount_eq _ _).trans (Qsag.qsum_congr fun ω => by
    unfold zeroBit
    rw [multiSession_runBool_orOfTwoSessions]
    rfl)

/-- Two sessions exceed the single-session bound `1/2`: the advantage is `3/4`. -/
theorem tooth_multiSession_exceeds_single_session_bound :
    ¬ ProbPkg.AdvBoundedOn (DistClass.all.mem (Iface.sessions bitIface 2))
      (echoBit.multiSession 2) (zeroBit.multiSession 2) ⟨1, 2, by decide⟩ :=
  fun h => absurd (h orOfTwoSessions (DistClass.mem_all _)) (by
    rw [echoBit_two_sessions_winCount, zeroBit_two_sessions_winCount]
    decide)

/-- Stateless machine answering every input with the fixed bit `b`. -/
def constMachine (b : Bool) : Machine Unit Unit Bool :=
  Machine.ofTotal (fun _ => True) (fun s _ => (s, b))

/-- One query; output the answered bit. -/
def readAnswer : Code (Iface.ofMachine Unit Bool) Bool :=
  .call () (fun (r : Option Bool) => .ret (r.getD false))

/-- `readAnswer` against the constant machine outputs its bit. -/
theorem constMachine_runBool (b : Bool) (ω : Fin 1) :
    (((constMachine b).toProbPkg (n := 1) (fun _ => ())).sample ω).runBool readAnswer = b := by
  rw [Machine.toProbPkg_sample, Pkg.runBool_eq]
  unfold readAnswer
  rw (config := { transparency := .default }) [Code.evalState_call, Machine.toPkg_closedHandler, Code.evalState_ret]
  rfl

theorem constMachine_winCount (b : Bool) :
    ((constMachine b).toProbPkg (n := 1) (fun _ => ())).winCount readAnswer =
      Qsag.qsum 1 (fun _ => if b then 1 else 0) :=
  (ProbPkg.winCount_eq _ _).trans (Qsag.qsum_congr fun ω => by rw [constMachine_runBool])

/-- Machines with related states but different outputs are distinguished on every coin. -/
theorem tooth_output_mismatch_breaks_refinement_equivalence :
    ¬ ProbPkg.AdvBoundedOn (DistClass.all.mem (Iface.ofMachine Unit Bool))
      ((constMachine true).toProbPkg (n := 1) (fun _ => ()))
      ((constMachine false).toProbPkg (n := 1) (fun _ => ())) RatBound.zero :=
  fun h => absurd (h readAnswer (DistClass.mem_all _)) (by
    rw [constMachine_winCount, constMachine_winCount]
    decide)

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

/-- One query to an oracle package, answer returned. -/
theorem ofOracle_runBool_probe {Dom : Type} (O : Dom → Bool) (q : Dom) :
    (Pkg.ofOracle O).runBool (.call q (fun (a : Bool) => .ret a)) = O q := by
  rw (config := { transparency := .default }) [Pkg.runBool_eq, Code.evalState_call, Pkg.ofOracle_closedHandler, Code.evalState_ret]

/-- Two queries to an oracle package, disjunction returned. -/
theorem ofOracle_runBool_probe_or {Dom : Type} (O : Dom → Bool) (q₁ q₂ : Dom) :
    (Pkg.ofOracle O).runBool
        (.call q₁ (fun (a : Bool) => .call q₂ (fun (b : Bool) => .ret (a || b)))) =
      (O q₁ || O q₂) := by
  rw (config := { transparency := .default }) [Pkg.runBool_eq, Code.evalState_call, Pkg.ofOracle_closedHandler, Code.evalState_call,
    Pkg.ofOracle_closedHandler, Code.evalState_ret]

theorem twoSlotReal_winCount_probeSlotZero :
    twoSlotReal.winCount probeSlotZero =
      Qsag.qsum 2 (fun ω => if Qsag.Top.keyedRomRealOracle (fun _ => false) (fun _ => true) ω
        ((⟨0, by decide⟩ : Fin 2), ()) then 1 else 0) :=
  (ProbPkg.winCount_eq _ _).trans (Qsag.qsum_congr fun ω => by
    unfold twoSlotReal probeSlotZero
    rw [Qsag.Top.keyedRomReal_eq, ProbPkg.ofOracle_sample, ofOracle_runBool_probe])

theorem twoSlotIdeal_winCount_probeSlotZero :
    twoSlotIdeal.winCount probeSlotZero = Qsag.qsum 2 (fun _ => 0) :=
  (ProbPkg.winCount_eq _ _).trans (Qsag.qsum_congr fun ω => by
    unfold twoSlotIdeal probeSlotZero
    rw [Qsag.Top.keyedRomIdeal_eq, ProbPkg.ofOracle_sample, ofOracle_runBool_probe]
    rfl)

theorem twoSlotReal_winCount_readBothSlots :
    twoSlotReal.winCount readBothSlots =
      Qsag.qsum 2 (fun ω =>
        if (Qsag.Top.keyedRomRealOracle (fun _ => false) (fun _ => true) ω
            ((⟨0, by decide⟩ : Fin 2), ()) ||
          Qsag.Top.keyedRomRealOracle (fun _ => false) (fun _ => true) ω
            ((⟨1, by decide⟩ : Fin 2), ())) then 1 else 0) :=
  (ProbPkg.winCount_eq _ _).trans (Qsag.qsum_congr fun ω => by
    unfold twoSlotReal readBothSlots
    rw [Qsag.Top.keyedRomReal_eq, ProbPkg.ofOracle_sample, ofOracle_runBool_probe_or])

theorem twoSlotIdeal_winCount_readBothSlots :
    twoSlotIdeal.winCount readBothSlots = Qsag.qsum 2 (fun _ => 0) :=
  (ProbPkg.winCount_eq _ _).trans (Qsag.qsum_congr fun ω => by
    unfold twoSlotIdeal readBothSlots
    rw [Qsag.Top.keyedRomIdeal_eq, ProbPkg.ofOracle_sample, ofOracle_runBool_probe_or]
    rfl)

/-- `probeSessionOne` against two sessions of a coin-drawn oracle: session `1` answers slot
    `0` on its own coin. -/
theorem multiSession_runBool_probeSessionOne (O : Fin 2 → Fin 2 × Unit → Bool)
    (ω : Fin (coinPow 2 2)) :
    (((ProbPkg.ofOracle O).multiSession 2).sample ω).runBool probeSessionOne =
      O (sessCoin 2 ω ⟨1, by decide⟩) (⟨0, by decide⟩, ()) := by
  rw [Pkg.runBool_eq]
  unfold probeSessionOne
  rw (config := { transparency := .default }) [ProbPkg.multiSession_evalState_callSession, Code.evalState_ret, ProbPkg.ofOracle_sample,
    Pkg.ofOracle_closedHandler]

theorem twoSlotReal_two_sessions_winCount :
    (twoSlotReal.multiSession 2).winCount probeSessionOne =
      Qsag.qsum (coinPow 2 2) (fun ω => if 0 = ω.1 % 2 then 1 else 0) :=
  (ProbPkg.winCount_eq _ _).trans (Qsag.qsum_congr fun ω => by
    unfold twoSlotReal
    rw [Qsag.Top.keyedRomReal_eq, multiSession_runBool_probeSessionOne]
    unfold Qsag.Top.keyedRomRealOracle
    simp only [Fin.ext_iff, sessCoin_two_one_val]
    cases Nat.decEq 0 (ω.1 % 2) with
    | isTrue h => simp only [h, ite_true]
    | isFalse h => simp only [h, ite_false, Bool.false_eq_true])

theorem twoSlotIdeal_two_sessions_winCount :
    (twoSlotIdeal.multiSession 2).winCount probeSessionOne =
      Qsag.qsum (coinPow 2 2) (fun _ => 0) :=
  (ProbPkg.winCount_eq _ _).trans (Qsag.qsum_congr fun ω => by
    unfold twoSlotIdeal
    rw [Qsag.Top.keyedRomIdeal_eq, multiSession_runBool_probeSessionOne]
    rfl)

/-- One query against two slots: advantage at most `1/2`. The only premise of
    `Qsag.Top.keyedRom_hiding_advBoundedOn` is `0 < cardB`, so this closed instance is its
    positive witness. -/
theorem keyedRom_two_slot_bound :
    ProbPkg.AdvBoundedOn ((DistClass.within 1).mem twoSlotIface) twoSlotReal twoSlotIdeal
      ⟨1, 2, by decide⟩ :=
  Qsag.Top.keyedRom_hiding_advBoundedOn 2 1 (by decide) _ _

/-- The one-query bound is attained: `probeSlotZero` has advantage exactly `1/2`, so the
    bound `0` fails for the same class. -/
theorem keyedRom_two_slot_bound_attained :
    ¬ ProbPkg.AdvBoundedOn ((DistClass.within 1).mem twoSlotIface) twoSlotReal twoSlotIdeal
      ⟨0, 2, by decide⟩ :=
  fun h => absurd (h probeSlotZero ((DistClass.mem_within_iff 1 _).mpr probeSlotZero_within)) (by
    rw [twoSlotReal_winCount_probeSlotZero, twoSlotIdeal_winCount_probeSlotZero]
    decide)

/-- Without the query budget the one-query bound fails: reading both slots finds the hidden
    one on every coin. -/
theorem tooth_keyedRom_bound_fails_without_query_budget :
    ¬ ProbPkg.AdvBoundedOn (DistClass.all.mem twoSlotIface) twoSlotReal twoSlotIdeal
      ⟨1, 2, by decide⟩ :=
  fun h => absurd (h readBothSlots (DistClass.mem_all _)) (by
    rw [twoSlotReal_winCount_readBothSlots, twoSlotIdeal_winCount_readBothSlots]
    decide)

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
      (RatBound.scale 2 ⟨0, 2, by decide⟩) :=
  fun h => absurd (h probeSessionOne (DistClass.mem_all _)) (by
    rw [twoSlotReal_two_sessions_winCount, twoSlotIdeal_two_sessions_winCount]
    decide)

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

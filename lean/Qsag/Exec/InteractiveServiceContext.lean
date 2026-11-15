module

public import Init

public section
namespace Qsag.InteractiveService
set_option autoImplicit false

/-- A single activation has explicit input/output and persistent private state.
Random coins, when needed, are part of the initial state (a fixed infinite tape).
This is classical message semantics, not a model of quantum registers. -/
structure Machine (I O S : Type) where
  step : S → I → S × O

/-- The next query depends on the preceding answer. This interface therefore
includes adaptive feedback, unlike postprocessing a completed transcript. -/
structure Environment (I O E : Type) where
  query : E → I
  receive : E → O → E

def run {I O S E : Type} (m : Machine I O S) (z : Environment I O E) :
    Nat → S → E → S × E
  | 0, s, e => (s, e)
  | n + 1, s, e =>
    let (s', o) := m.step s (z.query e)
    run m z n s' (z.receive e o)

/-- One-step simulation obligation at the actual input/output boundary.
It must hold for every next input, including inputs selected using prior output. -/
structure Bisimulation {I O S T : Type} (m : Machine I O S) (n : Machine I O T)
    (R : S → T → Prop) : Prop where
  step : ∀ s t, R s t → ∀ i,
    R (m.step s i).1 (n.step t i).1 ∧ (m.step s i).2 = (n.step t i).2

/-- Replacement under arbitrary interactive feedback, preserving the relation
for subsequent activations as well as the environment's entire memory. -/
theorem replacement {I O S T E : Type} (m : Machine I O S) (n : Machine I O T)
    (R : S → T → Prop) (h : Bisimulation m n R) (z : Environment I O E)
    (fuel : Nat) (s : S) (t : T) (e : E) (hr : R s t) :
    R (run m z fuel s e).1 (run n z fuel t e).1 ∧
      (run m z fuel s e).2 = (run n z fuel t e).2 := by
  induction fuel generalizing s t e with
  | zero => exact ⟨hr, rfl⟩
  | succ fuel ih =>
    have hs := h.step s t hr (z.query e)
    simp only [run]
    rw [hs.2]
    exact ih _ _ _ hs.1

/-- An outer protocol can itself be a stateful feedback transducer. Composition
exposes only the outer output, and retains both local states. -/
def plug {I O J P S C : Type} (m : Machine I O S)
    (send : C → J → C × I) (receive : C → O → C × P) : Machine J P (S × C) where
  step sc j :=
    let ci := send sc.2 j
    let so := m.step sc.1 ci.2
    let cp := receive ci.1 so.2
    ((so.1, cp.1), cp.2)

theorem plug_bisimulation {I O J P S T C : Type}
    (m : Machine I O S) (n : Machine I O T) (R : S → T → Prop)
    (h : Bisimulation m n R) (send : C → J → C × I)
    (receive : C → O → C × P) :
    Bisimulation (plug m send receive) (plug n send receive)
      (fun sc tc => R sc.1 tc.1 ∧ sc.2 = tc.2) := by
  constructor
  intro sc tc hr j
  rcases sc with ⟨s,c⟩
  rcases tc with ⟨t,d⟩
  dsimp only at hr
  rcases hr with ⟨hr, rfl⟩
  have hs := h.step s t hr (send c j).2
  dsimp only [plug]
  rw [hs.2]
  exact ⟨⟨hs.1, rfl⟩, rfl⟩

/-- Equality at every finite prefix is a quantified infinite-trace statement;
a theorem at one fixed fuel does not imply it. -/
def PrefixEquivalent {I O S T : Type} (m : Machine I O S) (n : Machine I O T)
    (s : S) (t : T) : Prop :=
  ∀ (E : Type) (z : Environment I O E) (e : E) (fuel : Nat),
    (run m z fuel s e).2 = (run n z fuel t e).2

theorem bisimulation_prefixEquivalent {I O S T : Type}
    (m : Machine I O S) (n : Machine I O T) (R : S → T → Prop)
    (h : Bisimulation m n R) (s : S) (t : T) (hr : R s t) :
    PrefixEquivalent m n s t := by
  intro E z e fuel
  exact (replacement m n R h z fuel s t e hr).2

/-- Negative witness: equal final service state is insufficient for replacement.
Both services erase their state; an interactive caller remembers their output. -/
def bitService (b : Bool) : Machine Unit Bool Unit where
  step _ _ := ((), b)
def remembering : Environment Unit Bool Bool where
  query _ := ()
  receive _ b := b

theorem equal_final_state_but_distinguished :
    (run (bitService false) remembering 1 () false).1 =
      (run (bitService true) remembering 1 () false).1 ∧
    (run (bitService false) remembering 1 () false).2 ≠
      (run (bitService true) remembering 1 () false).2 := by
  exact ⟨rfl, Bool.false_ne_true⟩

end Qsag.InteractiveService

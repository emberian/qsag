module
public import Qsag.Exec.InteractiveServiceContext

public section
namespace Qsag.InteractiveService
set_option autoImplicit false

/-- Uniform finite sampling; duplicate states retain their probability weight.
The independent product of party/adversary/environment tapes must be supplied
by a concrete implementation, not assumed from the word `samples`. -/
structure SampledMachine (I O S : Type) where
  machine : Machine I O S
  samples : List S
  nonempty : samples ≠ []

structure Observer (I O E : Type) where
  environment : Environment I O E
  initial : List E
  nonempty : initial ≠ []
  accept : E → Bool
  fuel : Nat

def accepts {I O S E : Type} (m : SampledMachine I O S) (z : Observer I O E) : Nat :=
  ((m.samples.flatMap (fun s => z.initial.map (fun e => z.accept
    (run m.machine z.environment z.fuel s e).2))).filter id).length

def sampleCount {I O S E : Type} (m : SampledMachine I O S) (z : Observer I O E) : Nat :=
  m.samples.length * z.initial.length

/-- Numerator of the acceptance-probability difference over the product of
the two nonzero sample counts. No common coin-space assumption is hidden. -/
def gapNumerator {I O S T E : Type}
    (m : SampledMachine I O S) (n : SampledMachine I O T) (z : Observer I O E) : Nat :=
  let a := accepts m z * sampleCount n z
  let b := accepts n z * sampleCount m z
  (a - b) + (b - a)

/-- A nonnegative rational error family, represented constructively. -/
structure ErrorFamily where
  numerator : Nat → Nat
  denominator : Nat → Nat
  positive : ∀ n, 0 < denominator n

def ErrorFamily.Negligible (ε : ErrorFamily) : Prop :=
  ∀ k : Nat, ∃ cutoff : Nat, ∀ n, cutoff ≤ n →
    ε.numerator n * (n + 1)^k ≤ ε.denominator n

def PolynomialBound (cost : Nat → Nat) : Prop :=
  ∃ c d : Nat, ∀ n, cost n ≤ c * (n + 1)^d

/-- Quantifier contract for an eventual classical computational theorem.
`real` and `ideal` must be the operational *linked* protocol/adversary machines.
Efficiency predicates must be derived from a machine/circuit cost semantics;
they are parameters here, not proofs that arbitrary Lean functions are PPT.
One simulator is chosen before the environment, its advice, and security
parameter. Every polynomial activation budget is included by `envEfficient`.
This definition alone asserts no security of QSAG. -/
def ComputationalEmulation {I O S T A Sim : Type}
    (real : A → Nat → SampledMachine I O S)
    (ideal : Sim → Nat → SampledMachine I O T)
    (advEfficient : A → Prop) (simEfficient : Sim → Prop)
    (envEfficient : (E : Type) → (Nat → Observer I O E) → Prop) : Prop :=
  ∀ a, advEfficient a → ∃ sim, simEfficient sim ∧
    ∀ (E : Type) (z : Nat → Observer I O E), envEfficient E z →
      ∃ ε : ErrorFamily, ε.Negligible ∧ ∀ n,
        gapNumerator (real a n) (ideal sim n) (z n) * ε.denominator n ≤
          ε.numerator n * (sampleCount (real a n) (z n) * sampleCount (ideal sim n) (z n))

/-- Exact online coupling transfers arbitrary interactive accept bits. This is
not a final-transcript postprocessor lemma: `z.environment.query` is evaluated
again after each matched output, including under an outer plugged protocol. -/
theorem coupled_accept_bits {I O S T E : Type}
    (m : Machine I O S) (n : Machine I O T) (R : S → T → Prop)
    (h : Bisimulation m n R) (z : Observer I O E)
    (coins : List ((S × T) × E)) (hc : ∀ st ∈ coins, R st.1.1 st.1.2) :
    coins.map (fun st => z.accept (run m z.environment z.fuel st.1.1 st.2).2) =
      coins.map (fun st => z.accept (run n z.environment z.fuel st.1.2 st.2).2) := by
  apply List.map_congr_left
  intro st hm
  rw [(replacement m n R h z.environment z.fuel st.1.1 st.1.2 st.2 (hc st hm)).2]

/-- Quantification over all fuel is essential: no fixed finite horizon can
exclude a later leak. These services first diverge on activation two. -/
def delayedBit (b : Bool) : Machine Unit Bool Nat where
  step s _ := (s + 1, if s = 0 then false else b)

theorem finite_horizon_not_lifting :
    (run (delayedBit false) remembering 1 0 false).2 =
      (run (delayedBit true) remembering 1 0 false).2 ∧
    (run (delayedBit false) remembering 2 0 false).2 ≠
      (run (delayedBit true) remembering 2 0 false).2 := by
  exact ⟨rfl, Bool.false_ne_true⟩

end Qsag.InteractiveService

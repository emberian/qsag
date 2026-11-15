module
/-
# Operational coherent bit-oracle runtime in a Fourier truth-table register

Each step executes one controlled XOR query, one adversary local gate, and known Walsh
basis changes. The oracle register is never measured during execution. Exact integer
normalizations are tracked; this is full-table infrastructure, not sparse online extraction.
-/
public import Qsag.QromFourierTable
import all Qsag.QromFourierTable
import all Qsag.QromClassicalQueryTransfer
import all Qsag.MultiRoundFsQrom
import all Qsag.ConcreteSecurityBudget

public section
namespace Qsag
set_option autoImplicit false

def tableBitOracle : (n : Nat) → OracleBitTable n → Fin n → BitVec 1
  | 0, _, x => Fin.elim0 x
  | n + 1, (b, h), x => Fin.cases (if b then 1#1 else 0#1) (tableBitOracle n h) x

/-- This table enumeration is precisely the existing uniform random-function experiment. -/
theorem oracleTableSum_eq_uniform : ∀ n (f : (Fin n → BitVec 1) → Nat),
    oracleTableSum n (fun h => f (tableBitOracle n h)) = uniformOracleSum 1 n f
  | 0, _ => rfl
  | n + 1, f => by
    change oracleTableSum n (fun h => f (Fin.cases 0#1 (tableBitOracle n h))) +
      oracleTableSum n (fun h => f (Fin.cases 1#1 (tableBitOracle n h))) = _
    rw [oracleTableSum_eq_uniform n (fun H => f (Fin.cases 0#1 H)),
      oracleTableSum_eq_uniform n (fun H => f (Fin.cases 1#1 H))]
    simp only [uniformOracleSum, qsum]
    rfl

/-- Finite sum exchange between the oracle register and a computational register. -/
theorem oracleTableSum_qsum (n k : Nat) (f : OracleBitTable n → Fin k → Nat) :
    oracleTableSum n (fun h => qsum k (f h)) = qsum k (fun i => oracleTableSum n (fun h => f h i)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [oracleTableSum, ih, qsum_add]

theorem ScaledUnitary.map_add {cardX w cardAnc : Nat} (U : ScaledUnitary cardX w cardAnc)
    (ψ φ : QVec cardX w cardAnc) : U.apply (ψ.add φ) = (U.apply ψ).add (U.apply φ) := by
  have he : (ψ.add φ).sub φ = ψ := by
    funext x y a
    apply GaussInt.ext <;> simp [QVec.add, QVec.sub, GaussInt.add, GaussInt.sub]
  have h := U.map_sub (ψ.add φ) φ
  rw [he] at h
  funext x y a
  have hp := congrArg (fun v => v x y a) h
  have hr := congrArg GaussInt.re hp
  have hi := congrArg GaussInt.im hp
  apply GaussInt.ext <;> simp only [QVec.add, QVec.sub, GaussInt.add, GaussInt.sub] at * <;> omega

def qvecDoublePow {cardX w cardAnc : Nat} (k : Nat) (ψ : QVec cardX w cardAnc) : QVec cardX w cardAnc :=
  fun x y a => gaussDoublePow k (ψ x y a)

theorem ScaledUnitary.map_doublePow {cardX w cardAnc : Nat} (U : ScaledUnitary cardX w cardAnc)
    (k : Nat) (ψ : QVec cardX w cardAnc) : U.apply (qvecDoublePow k ψ) = qvecDoublePow k (U.apply ψ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change U.apply ((qvecDoublePow k ψ).add (qvecDoublePow k ψ)) =
      (qvecDoublePow k (U.apply ψ)).add (qvecDoublePow k (U.apply ψ))
    rw [U.map_add, ih]

theorem gaussDoublePow_add (k l : Nat) (z : GaussInt) :
    gaussDoublePow k (gaussDoublePow l z) = gaussDoublePow (k + l) z := by
  induction k with
  | zero => simp only [gaussDoublePow, Nat.zero_add]
  | succ k ih => simp only [gaussDoublePow, ih, Nat.succ_add]

abbrev CoherentBitState (n cardAnc : Nat) := OracleBitTable n → QVec n 1 cardAnc

def fourierOracleState {n cardAnc : Nat} (ψ : CoherentBitState n cardAnc) : CoherentBitState n cardAnc :=
  fun d x y a => oracleWalsh n (fun h => ψ h x y a) d

def doubleOracleState {n cardAnc : Nat} (k : Nat) (ψ : CoherentBitState n cardAnc) : CoherentBitState n cardAnc :=
  fun h => qvecDoublePow k (ψ h)

theorem fourierOracleState_square {n cardAnc : Nat} (ψ : CoherentBitState n cardAnc) :
    fourierOracleState (fourierOracleState ψ) = doubleOracleState n ψ := by
  funext h x y a
  exact oracleWalsh_square n _ h

theorem fourierOracleState_double {n cardAnc : Nat} (k : Nat) (ψ : CoherentBitState n cardAnc) :
    fourierOracleState (doubleOracleState k ψ) = doubleOracleState k (fourierOracleState ψ) := by
  funext h x y a
  exact oracleWalsh_doublePow n k _ h

theorem doubleOracleState_add {n cardAnc : Nat} (k l : Nat) (ψ : CoherentBitState n cardAnc) :
    doubleOracleState k (doubleOracleState l ψ) = doubleOracleState (k + l) ψ := by
  funext h x y a
  exact gaussDoublePow_add k l _

/-- Scaled isometry on the joint oracle and adversary state. -/
theorem fourierOracleState_norm {n cardAnc : Nat} (ψ : CoherentBitState n cardAnc) :
    oracleTableSum n (fun d => QVec.stateNormSq (fourierOracleState ψ d)) =
      2 ^ n * oracleTableSum n (fun h => QVec.stateNormSq (ψ h)) := by
  unfold QVec.stateNormSq QVec.queryWeight fourierOracleState
  simp only [oracleTableSum_qsum, oracleWalsh_norm, qsum_mul_left]

/-- One ordinary coherent query to the table, followed by the oracle-independent local gate. -/
def coherentOracleStep {n cardAnc : Nat} (U : ScaledUnitary n 1 cardAnc)
    (ψ : CoherentBitState n cardAnc) : CoherentBitState n cardAnc :=
  fun h => U.apply (oracleXor (tableBitOracle n h) (ψ h))

/-- Operational conjugated step. Both transforms are known gates; exactly one oracle query
    occurs. Unnormalized Walsh multiplies amplitude by 2^n per completed step. -/
def fourierOracleStep {n cardAnc : Nat} (U : ScaledUnitary n 1 cardAnc)
    (ψ : CoherentBitState n cardAnc) : CoherentBitState n cardAnc :=
  fourierOracleState (coherentOracleStep U (fourierOracleState ψ))

theorem coherentOracleStep_double {n cardAnc : Nat} (U : ScaledUnitary n 1 cardAnc)
    (k : Nat) (ψ : CoherentBitState n cardAnc) :
    coherentOracleStep U (doubleOracleState k ψ) = doubleOracleState k (coherentOracleStep U ψ) := by
  funext h
  exact U.map_doublePow k (oracleXor (tableBitOracle n h) (ψ h))

/-- Independently stepped runtime, starting with the Fourier encoding of the uniform table. -/
def fourierAdvStateAt {n cardAnc Q : Nat} (A : QuantumAdv n 1 cardAnc Q) :
    (t : Nat) → t ≤ Q → CoherentBitState n cardAnc
  | 0, _ => fourierOracleState (fun _ => A.init)
  | t + 1, ht => fourierOracleStep (A.steps ⟨t, ht⟩)
      (fourierAdvStateAt A t (Nat.le_of_succ_le ht))

/-- Exact state equivalence for arbitrary superposition-query adversaries. No classical
    address restriction and no event cover occurs in this theorem. -/
theorem fourierAdvStateAt_eq {n cardAnc Q : Nat} (A : QuantumAdv n 1 cardAnc Q) :
    ∀ t (ht : t ≤ Q), fourierAdvStateAt A t ht =
      doubleOracleState (n * t) (fourierOracleState (fun h => advStateAt A (tableBitOracle n h) t ht))
  | 0, _ => rfl
  | t + 1, ht => by
    simp only [fourierAdvStateAt, fourierOracleStep, fourierAdvStateAt_eq,
      fourierOracleState_double, fourierOracleState_square, doubleOracleState_add,
      coherentOracleStep_double, Nat.mul_succ]
    rfl

/-- Decoding the final Fourier register recovers the actual coherent execution, including
    all oracle/output correlations; the normalization is known and oracle-independent. -/
theorem fourierAdvStateAt_decode {n cardAnc Q : Nat} (A : QuantumAdv n 1 cardAnc Q) :
    fourierOracleState (fourierAdvStateAt A Q (Nat.le_refl Q)) =
      doubleOracleState (n * Q + n) (fun h => runQuantumAdv A (tableBitOracle n h)) := by
  rw [fourierAdvStateAt_eq, fourierOracleState_double, fourierOracleState_square, doubleOracleState_add]
  rfl

/-- Observable event after decoding the oracle register. It may depend on both H and the
    final output x (e.g. root verification). No query-address measurement is inserted. -/
def coherentTableEventMass {n cardAnc : Nat}
    (event : (Fin n → BitVec 1) → Fin n → Bool) (ψ : CoherentBitState n cardAnc) : Nat :=
  oracleTableSum n (fun h => QVec.queryMassOn (event (tableBitOracle n h)) (ψ h))

theorem queryMassOn_doublePow {n w cardAnc : Nat} (k : Nat) (E : Fin n → Bool)
    (ψ : QVec n w cardAnc) : QVec.queryMassOn E (qvecDoublePow k ψ) = 4 ^ k * QVec.queryMassOn E ψ := by
  unfold QVec.queryMassOn QVec.queryWeight qvecDoublePow
  simp only [gaussDoublePow_norm, qsum_mul_left]
  rw [← qsum_mul_left]
  apply qsum_congr
  intro x
  cases E x <;> simp

/-- Exact unnormalized observable equivalence for every event, with explicit scale. -/
theorem fourierAdv_event_eq {n cardAnc Q : Nat} (A : QuantumAdv n 1 cardAnc Q)
    (event : (Fin n → BitVec 1) → Fin n → Bool) :
    coherentTableEventMass event (fourierOracleState (fourierAdvStateAt A Q (Nat.le_refl Q))) =
      4 ^ (n * Q + n) * uniformOracleSum 1 n
        (fun H => QVec.queryMassOn (event H) (runQuantumAdv A H)) := by
  rw [fourierAdvStateAt_decode]
  unfold coherentTableEventMass doubleOracleState
  simp only [queryMassOn_doublePow]
  rw [oracleTableSum_mul, oracleTableSum_eq_uniform n
    (fun H => QVec.queryMassOn (event H) (runQuantumAdv A H))]

#verify_constructive
  Qsag.fourierOracleState_norm
  Qsag.fourierAdvStateAt_eq
  Qsag.fourierAdvStateAt_decode
  Qsag.fourierAdv_event_eq
end Qsag
end

module
/-
# Boundaries of the classical-query-table / quantum target-hit interface

These countermodels do not refute the conditional target-hit theorem. They rule out two
unsound shortcuts for supplying its hypotheses: cardinality alone does not give locality,
and copying a coherent query into an orthogonal record is not observationally neutral.
-/

public import Qsag.Oracle.QromMerkleOnlineExtraction
import all Qsag.Oracle.QromMerkleOnlineExtraction

public section
namespace Qsag

set_option autoImplicit false

/-- A singleton adaptive target can contain the answer being tested. -/
def qromSelfTarget (H : Fin 1 → BitVec 1) (x : Fin 1) : List (BitVec 1) := [H x]

/-- Small target cardinality is insufficient: this event always succeeds, but changing its
    tested oracle coordinate changes its target list and violates `hLocal`. -/
theorem tooth_qrom_self_target_not_local :
    (∀ (H : Fin 1 → BitVec 1) (x : Fin 1),
      (qromSelfTarget H x).length = 1 ∧ listHasElem (H x) (qromSelfTarget H x) = true) ∧
    ¬ (∀ (H : Fin 1 → BitVec 1) (x : Fin 1) (ch : BitVec 1),
      qromSelfTarget (reprogramOracle H x ch) x = qromSelfTarget H x) := by
  constructor
  · intro H x
    simp [qromSelfTarget, listHasElem]
  · intro h
    have h01 := h (fun _ => 0#1) 0 1#1
    have hne : qromSelfTarget (reprogramOracle (fun _ : Fin 1 => 0#1) 0 1#1) 0 ≠
        qromSelfTarget (fun _ : Fin 1 => 0#1) 0 := by decide
    exact hne h01

/-- Uniform query register, phase-kickback response, and a blank record register. -/
def qromParityInit : QVec 2 1 2 := fun _ y a =>
  if a.val = 0 then (if y.val = 0 then ⟨1, 0⟩ else ⟨-1, 0⟩) else GaussInt.zero

/-- The two input addresses have different oracle answers. -/
def qromParityOracle (x : Fin 2) : BitVec 1 := BitVec.ofFin x

/-- One coherent oracle call followed by a query-register Hadamard. -/
def qromParityAdv : QuantumAdv 2 1 2 1 where
  init := qromParityInit
  h_init_pos := by decide
  steps := fun _ => hadamardQuery2 1 2

/-- The same initial state after copying the query address to an orthogonal record.
    This is the controlled-X copy on a blank ancilla, before the oracle call. -/
def qromRecordedParityInit : QVec 2 1 2 := fun x y a =>
  if a = x then (if y.val = 0 then ⟨1, 0⟩ else ⟨-1, 0⟩) else GaussInt.zero

def qromRecordedParityAdv : QuantumAdv 2 1 2 1 where
  init := qromRecordedParityInit
  h_init_pos := by decide
  steps := fun _ => hadamardQuery2 1 2

/-- A classical record of the queried address destroys interference even for one query.
    Both final states have squared norm eight. The coherent circuit outputs one with
    probability one; retaining the address record changes that probability to one half.
    An online extractor therefore needs a proved disturbance/simulation bound, not just a
    consistent classical query list handed to `classifyOnlineMerkleOpening`. -/
theorem tooth_qrom_query_record_changes_born_probability :
    QVec.stateNormSq (runQuantumAdv qromParityAdv qromParityOracle) = 8 ∧
    QVec.stateNormSq (runQuantumAdv qromRecordedParityAdv qromParityOracle) = 8 ∧
    QVec.queryMassOn (fun x : Fin 2 => decide (x.val = 1))
      (runQuantumAdv qromParityAdv qromParityOracle) = 8 ∧
    QVec.queryMassOn (fun x : Fin 2 => decide (x.val = 1))
      (runQuantumAdv qromRecordedParityAdv qromParityOracle) = 4 := by
  decide

/-- A genuine measured-query interface: branch `x` is obtained by projecting the actual
    post-oracle state onto the observed query address. It is not an unobserved query log. -/
def measuredOracleQueryBranch {cardX w cardAnc : Nat}
    (H : Fin cardX → BitVec w) (ψ : QVec cardX w cardAnc) (x : Fin cardX) :
    QVec cardX w cardAnc := projSingle x (oracleXor H ψ)

/-- The measured branches have exactly the input query weights and conserve total mass.
    This supplies probabilities for an explicit measurement instrument; it does not identify
    the instrument with the original coherent execution. -/
theorem measuredOracleQueryBranch_mass {cardX w cardAnc : Nat}
    (H : Fin cardX → BitVec w) (ψ : QVec cardX w cardAnc) :
    (∀ x, QVec.stateNormSq (measuredOracleQueryBranch H ψ x) = QVec.queryWeight ψ x) ∧
    qsum cardX (fun x => QVec.stateNormSq (measuredOracleQueryBranch H ψ x)) =
      QVec.stateNormSq ψ := by
  have h : ∀ x, QVec.stateNormSq (measuredOracleQueryBranch H ψ x) =
      QVec.queryWeight ψ x := fun x => by
    rw [measuredOracleQueryBranch, projSingle_normSq, oracleXor_queryWeight]
  exact ⟨h, qsum_congr h⟩

/-- When a query's response register starts at zero, measuring its address and answer
    produces an oracle-consistent classical record. This is a positive bridge to classical
    query-table consistency for explicitly measured executions, not for arbitrary QROM runs. -/
theorem measuredOracleQueryBranch_consistent {cardX w cardAnc : Nat}
    (H : Fin cardX → BitVec w) (ψ : QVec cardX w cardAnc)
    (hZero : ∀ x y a, y.val ≠ 0 → ψ x y a = GaussInt.zero)
    (recorded x : Fin cardX) (y : Fin (2 ^ w)) (a : Fin cardAnc)
    (hMass : measuredOracleQueryBranch H ψ recorded x y a ≠ GaussInt.zero) :
    x = recorded ∧ BitVec.ofFin y = H recorded := by
  have hx : x = recorded := by
    by_cases heq : x = recorded
    · exact heq
    · exact False.elim (hMass (by simp [measuredOracleQueryBranch, projSingle, heq]))
  subst hx
  have hAnsZero : (xorFin y (H x)).val = 0 := by
    by_cases heq : (xorFin y (H x)).val = 0
    · exact heq
    · exact False.elim (hMass (by
        simp only [measuredOracleQueryBranch, projSingle, ↓reduceIte, oracleXor]
        exact hZero x (xorFin y (H x)) a heq))
  have hFinZero : xorFin y (H x) = (0 : Fin (2 ^ w)) := Fin.ext hAnsZero
  have hInv := congrArg (fun z => xorFin z (H x)) hFinZero
  rw [xorFin_involutive] at hInv
  have hZeroXor : (0#w ^^^ H x) = H x := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_zero, Bool.false_xor]
  have hOutput : y = (H x).toFin := by
    change y = (0#w ^^^ H x).toFin at hInv
    rw [hZeroXor] at hInv
    exact hInv
  exact ⟨rfl, by rw [hOutput, BitVec.ofFin_toFin]⟩

/-- An observed zero-response oracle query supplies the classical classifier's actual
    `merkleQueryConsistent` premise for a chosen compression-input encoding. This lemma
    only establishes record consistency: injective domain encoding, sequential recording,
    pre-challenge timing, and disturbance bounds remain separate obligations. -/
theorem measuredOracleQuery_merkle_record_consistent {cardX w cardAnc : Nat}
    (H : Fin cardX → BitVec w)
    (encode : Nat → Nat → BitVec w → BitVec w → Fin cardX)
    (ψ : QVec cardX w cardAnc)
    (hZero : ∀ x y a, y.val ≠ 0 → ψ x y a = GaussInt.zero)
    (lvl node : Nat) (left right : BitVec w)
    (y : Fin (2 ^ w)) (a : Fin cardAnc)
    (hMass : measuredOracleQueryBranch H ψ (encode lvl node left right)
      (encode lvl node left right) y a ≠ GaussInt.zero) :
    merkleQueryConsistent (fun l n u v => H (encode l n u v))
      ⟨lvl, node, left, right, BitVec.ofFin y⟩ :=
  (measuredOracleQueryBranch_consistent H ψ hZero
    (encode lvl node left right) (encode lvl node left right) y a hMass).2.symm

#verify_constructive
  Qsag.tooth_qrom_self_target_not_local
  Qsag.tooth_qrom_query_record_changes_born_probability
  Qsag.measuredOracleQueryBranch_mass
  Qsag.measuredOracleQueryBranch_consistent
  Qsag.measuredOracleQuery_merkle_record_consistent

end Qsag
end

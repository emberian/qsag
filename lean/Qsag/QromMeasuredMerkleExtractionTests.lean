module
/-
# Executed instances of the measured-query Merkle extraction experiment

A four-address layout with one-bit digests (one tree position, addresses `2 * left + right`)
satisfies the layout laws, so `MerkleAddressLayout` is inhabited. Two one-query adversaries
output the same depth-one opening `(root 0, leaf 0, sibling 1)`:

* the one that measured-queries the verifier's address is accepted on 8 of 16 oracles and
  never fails extraction;
* the one that queries a different address is accepted on the same 8 oracles and fails
  extraction on all of them: failure mass 8 of 16, the single-target lazy-sampling value.

At one-bit digests the general bound exceeds one; these instances exercise the experiment
and the failure event, not the size of the bound.
-/

public import Qsag.QromClassicalQueryTransfer
import all Qsag.QromClassicalQueryTransfer
import all Qsag.QromMeasuredMerkleExtraction
import all Qsag.QromMeasuredQueryExperiment
import all Qsag.QromMerkleOnlineExtraction
import all Qsag.MultiRoundFsQrom
import all Qsag.ConcreteSecurityBudget

public section
namespace Qsag

set_option autoImplicit false

def toyMerkleEncode (u v : BitVec 1) : Fin 4 :=
  ⟨2 * u.toFin.val + v.toFin.val, by have := u.toFin.isLt; have := v.toFin.isLt; omega⟩

def toyMerkleDecode (x : Fin 4) : Nat × Nat × BitVec 1 × BitVec 1 :=
  (0, 0, BitVec.ofNat 1 (x.val / 2), BitVec.ofNat 1 (x.val % 2))

def toyMerkleLayout : MerkleAddressLayout 4 1 where
  encode := fun _ _ u v => toyMerkleEncode u v
  decode := fun x => some (toyMerkleDecode x)
  levels := 1
  nodes := 1
  decode_sound := by
    intro x l n u v h
    have h' := Option.some.inj h
    have hu : BitVec.ofNat 1 (x.val / 2) = u := congrArg (fun τ => τ.2.2.1) h'
    have hv : BitVec.ofNat 1 (x.val % 2) = v := congrArg (fun τ => τ.2.2.2) h'
    rw [← hu, ← hv]
    clear h h' hu hv
    revert x
    decide
  decode_encode := by
    intro l n u v hl hn
    have hl0 : l = 0 := by omega
    have hn0 : n = 0 := by omega
    subst hl0 hn0
    cases u with | ofFin fu =>
    cases v with | ofFin fv =>
    revert fu fv
    decide

/-- Basis state at query address `x₀`, zero response register. -/
def toyBasisInit (x₀ : Fin 4) : QVec 4 1 1 := fun x y _ =>
  if x = x₀ ∧ y.val = 0 then ⟨1, 0⟩ else GaussInt.zero

def toyQueryAdv (x₀ : Fin 4) (h : 0 < QVec.stateNormSq (toyBasisInit x₀)) : QuantumAdv 4 1 1 1 where
  init := toyBasisInit x₀
  h_init_pos := h
  steps := fun _ => ScaledUnitary.id 4 1 1

/-- Every output claims: root `0`, index `0`, leaf `0`, sibling `1`. The verifier therefore
    evaluates the oracle at address `2 * 0 + 1 = 1`. -/
def toyOpening (_ : Fin 4) : MerkleOpeningReadout 1 := ⟨0#1, 0, 0#1, [1#1]⟩

/-- Acceptance without the extraction comparison. -/
def toyAccepted (H : Fin 4 → BitVec 1) (o : Fin 4) : Bool :=
  decide (merkleRootFromPath (toyMerkleLayout.hash H) 0 (toyOpening o).idx (toyOpening o).leaf
    (toyOpening o).path = (toyOpening o).rt)

theorem toy_measured_merkle_execution :
    let honest := toyQueryAdv ⟨1, by decide⟩ (by decide)
    let guesser := toyQueryAdv ⟨0, by decide⟩ (by decide)
    -- both are accepted on 8 of the 16 oracles
    uniformOracleSum 1 4 (fun H => sumLogs 4 1 (fun xs =>
      QVec.queryMassOn (toyAccepted H) (measuredStateAt honest H 1 (Nat.le_refl 1) xs))) = 8 ∧
    uniformOracleSum 1 4 (fun H => sumLogs 4 1 (fun xs =>
      QVec.queryMassOn (toyAccepted H) (measuredStateAt guesser H 1 (Nat.le_refl 1) xs))) = 8 ∧
    -- the honest log always yields the opening; the other log never does
    uniformOracleSum 1 4 (fun H => sumLogs 4 1 (fun xs =>
      QVec.queryMassOn (measuredMerkleFailure toyMerkleLayout 0 1 toyOpening H xs)
        (measuredStateAt honest H 1 (Nat.le_refl 1) xs))) = 0 ∧
    uniformOracleSum 1 4 (fun H => sumLogs 4 1 (fun xs =>
      QVec.queryMassOn (measuredMerkleFailure toyMerkleLayout 0 1 toyOpening H xs)
        (measuredStateAt guesser H 1 (Nat.le_refl 1) xs))) = 8 ∧
    (2 ^ 1) ^ 4 * (prefixScale guesser 1 (Nat.le_refl 1) * QVec.stateNormSq guesser.init) = 16 := by
  decide +kernel

/-- The toy adversaries are classical-address adversaries, so `ClassicalQueryAddresses` is
    satisfiable and the transfer theorem applies to them. -/
theorem toyQueryAdv_classical (x₀ : Fin 4) (h : 0 < QVec.stateNormSq (toyBasisInit x₀)) :
    ClassicalQueryAddresses (toyQueryAdv x₀ h) (fun _ _ => x₀) := by
  intro H t ht x y a hx
  have ht0 : t = 0 := by omega
  subst ht0
  show (if x = x₀ ∧ y.val = 0 then (⟨1, 0⟩ : GaussInt) else GaussInt.zero) = GaussInt.zero
  exact ite_eq_right (fun hh => hx hh.1)

/-- The coherent run of the non-querying-the-right-address adversary, with its own address
    log `[0]`, has failure mass 8 of 16: the value the measured experiment gave, as the
    transfer theorem states, and within the general bound `(1 * 4 + 0) / 2`. -/
theorem toy_classical_run_execution :
    let guesser := toyQueryAdv ⟨0, by decide⟩ (by decide)
    uniformOracleSum 1 4 (fun H =>
      QVec.queryMassOn (measuredMerkleFailure toyMerkleLayout 0 1 toyOpening H
          (classicalQueryLog (fun _ _ => (⟨0, by decide⟩ : Fin 4)) H 1))
        (runQuantumAdv guesser H)) = 8 ∧
    2 ^ 1 * 8 ≤ (1 * (3 * 1 + 1) + triangleSum 1) *
      ((2 ^ 1) ^ 4 * (prefixScale guesser 1 (Nat.le_refl 1) * QVec.stateNormSq guesser.init)) := by
  decide +kernel

#verify_constructive
  Qsag.toy_measured_merkle_execution
  Qsag.toyQueryAdv_classical
  Qsag.toy_classical_run_execution

end Qsag
end

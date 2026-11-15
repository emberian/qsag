module
/-
# Batched opening extraction in the measured-query experiment

The batch is a fixed list of output-register readouts; the openings themselves may depend
on the adversary's output. Each slot has its own tree level and depth cap. This is a union
bound on full Merkle paths, not a proof for the deployed Canopy multiproof decoder.
The coherent-run corollary requires classical query addresses explicitly.
-/
public import Qsag.Oracle.QromClassicalQueryTransfer
import all Qsag.Oracle.QromClassicalQueryTransfer
import all Qsag.Oracle.QromMeasuredMerkleExtraction
import all Qsag.Oracle.QromMeasuredQueryExperiment
import all Qsag.Oracle.MultiRoundFsQrom

public section
namespace Qsag
set_option autoImplicit false

/-- Unnormalized event mass, including the measured query log and uniform oracle. -/
def measuredEventMass {cardX w cardAnc Q : Nat} (A : QuantumAdv cardX w cardAnc Q)
    (event : (Fin cardX → BitVec w) → List (Fin cardX) → Fin cardX → Bool) : Nat :=
  uniformOracleSum w cardX (fun H => sumLogs cardX Q (fun xs =>
    QVec.queryMassOn (event H xs) (measuredStateAt A H Q (Nat.le_refl Q) xs)))

def quantumExperimentTotal {cardX w cardAnc Q : Nat} (A : QuantumAdv cardX w cardAnc Q) : Nat :=
  (2 ^ w) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init)

theorem queryMassOn_union_le {cardX w cardAnc : Nat}
    (p r : Fin cardX → Bool) (ψ : QVec cardX w cardAnc) :
    QVec.queryMassOn (fun x => p x || r x) ψ ≤
      QVec.queryMassOn p ψ + QVec.queryMassOn r ψ := by
  unfold QVec.queryMassOn
  rw [← qsum_add]
  apply qsum_le_qsum
  intro x
  cases hp : p x <;> cases hr : r x <;> simp [hp, hr]

theorem measuredEventMass_union_le {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (p r : (Fin cardX → BitVec w) → List (Fin cardX) → Fin cardX → Bool) :
    measuredEventMass A (fun H xs x => p H xs x || r H xs x) ≤
      measuredEventMass A p + measuredEventMass A r := by
  unfold measuredEventMass
  rw [← uniformOracleSum_add]
  apply uniformOracleSum_le
  intro H
  rw [← sumLogs_add]
  exact sumLogs_le_of_length cardX Q _ _ (fun xs _ => queryMassOn_union_le _ _ _)

theorem measuredEventMass_mono {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (p r : (Fin cardX → BitVec w) → List (Fin cardX) → Fin cardX → Bool)
    (h : ∀ H xs x, p H xs x = true → r H xs x = true) :
    measuredEventMass A p ≤ measuredEventMass A r := by
  apply uniformOracleSum_le
  intro H
  apply sumLogs_le_of_length
  intro xs _
  apply qsum_le_qsum
  intro x
  change (if p H xs x = true then _ else 0) ≤ (if r H xs x = true then _ else 0)
  cases hp : p H xs x with
  | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact Nat.zero_le _
  | true => simp [h H xs x hp]

structure MerkleOpeningSlot (cardX w : Nat) where
  level : Nat
  depth : Nat
  readout : Fin cardX → MerkleOpeningReadout w

def batchMerkleFailure {cardX w : Nat} (L : MerkleAddressLayout cardX w)
    (slots : List (MerkleOpeningSlot cardX w))
    (H : Fin cardX → BitVec w) (xs : List (Fin cardX)) (x : Fin cardX) : Bool :=
  slots.any (fun s => measuredMerkleFailure L s.level s.depth s.readout H xs x)

/-- This conservative budget counts the shared collision term once per opening. -/
def batchMerkleCost {cardX w : Nat} (Q : Nat) (slots : List (MerkleOpeningSlot cardX w)) : Nat :=
  (slots.map (fun s => s.depth * (3 * Q + 1) + triangleSum Q)).sum

/-- No locality or extraction-failure cover premise is required. -/
theorem measured_batch_merkle_extraction_failure_bound {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q) (L : MerkleAddressLayout cardX w)
    (slots : List (MerkleOpeningSlot cardX w))
    (hLevels : ∀ s ∈ slots, s.level + s.depth ≤ L.levels) :
    2 ^ w * measuredEventMass A (batchMerkleFailure L slots) ≤
      batchMerkleCost Q slots * quantumExperimentTotal A := by
  induction slots with
  | nil =>
    unfold measuredEventMass
    change 2 ^ w * uniformOracleSum w cardX (fun H => sumLogs cardX Q (fun xs =>
      QVec.queryMassOn (fun _ => false) (measuredStateAt A H Q (Nat.le_refl Q) xs))) ≤ _
    have hz : ∀ H : Fin cardX → BitVec w,
        sumLogs cardX Q (fun xs => QVec.queryMassOn (fun _ => false)
          (measuredStateAt A H Q (Nat.le_refl Q) xs)) = 0 := by
      intro H
      have hp : ∀ xs, QVec.queryMassOn (fun _ => false)
          (measuredStateAt A H Q (Nat.le_refl Q) xs) = 0 := by
        intro xs; simp [QVec.queryMassOn, qsum_const]
      rw [show (fun xs => QVec.queryMassOn (fun _ => false)
        (measuredStateAt A H Q (Nat.le_refl Q) xs)) = fun _ => 0 * 0 from funext hp]
      rw [sumLogs_mul, Nat.zero_mul]
    rw [uniformOracleSum_congr w cardX _ _ hz, uniformOracleSum_const]
    simp
  | cons s rest ih =>
    have hOne := measured_merkle_extraction_failure_bound A L s.level s.depth
      (hLevels s (.head rest)) s.readout
    have hRest := ih (fun t ht => hLevels t (.tail s ht))
    have hUnion := measuredEventMass_union_le A
      (measuredMerkleFailure L s.level s.depth s.readout) (batchMerkleFailure L rest)
    have h := Nat.le_trans (Nat.mul_le_mul_left (2 ^ w) hUnion)
      (by rw [Nat.mul_add]; exact Nat.add_le_add hOne hRest)
    change 2 ^ w * measuredEventMass A (fun H xs x =>
      measuredMerkleFailure L s.level s.depth s.readout H xs x || batchMerkleFailure L rest H xs x) ≤ _
    simpa only [batchMerkleFailure, List.any_cons, batchMerkleCost, List.map_cons,
      List.sum_cons, Nat.add_mul, quantumExperimentTotal, measuredEventMass] using h

/-- General event transfer; no identification is made for superposition queries. -/
theorem measuredEventMass_classical {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (addr : (Fin cardX → BitVec w) → Nat → Fin cardX) (hC : ClassicalQueryAddresses A addr)
    (event : (Fin cardX → BitVec w) → List (Fin cardX) → Fin cardX → Bool) :
    measuredEventMass A event = uniformOracleSum w cardX (fun H =>
      QVec.queryMassOn (event H (classicalQueryLog addr H Q)) (runQuantumAdv A H)) := by
  apply uniformOracleSum_congr
  intro H
  exact classical_query_measured_eq A addr hC H
    (fun xs ψ => QVec.queryMassOn (event H xs) ψ) (fun _ => queryMassOn_zero _)

/-- The batch bound transferred to the coherent run only for classical-address queries. -/
theorem classical_query_batch_merkle_extraction_failure_bound {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (addr : (Fin cardX → BitVec w) → Nat → Fin cardX) (hC : ClassicalQueryAddresses A addr)
    (L : MerkleAddressLayout cardX w) (slots : List (MerkleOpeningSlot cardX w))
    (hLevels : ∀ s ∈ slots, s.level + s.depth ≤ L.levels) :
    2 ^ w * uniformOracleSum w cardX (fun H =>
      QVec.queryMassOn (batchMerkleFailure L slots H (classicalQueryLog addr H Q))
        (runQuantumAdv A H)) ≤ batchMerkleCost Q slots * quantumExperimentTotal A := by
  rw [← measuredEventMass_classical A addr hC (batchMerkleFailure L slots)]
  exact measured_batch_merkle_extraction_failure_bound A L slots hLevels

#verify_constructive
  Qsag.measuredEventMass_classical
  Qsag.measured_batch_merkle_extraction_failure_bound
  Qsag.classical_query_batch_merkle_extraction_failure_bound
end Qsag
end

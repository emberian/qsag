module
/-
# Classical-address adversaries: the measured experiment is the coherent run

If the state of a `QuantumAdv` before each oracle call is supported on one query address
(which may depend on the oracle and on everything computed so far), then measuring the
query register changes nothing: exactly one measured branch is nonzero and it equals the
coherent state. For such adversaries the measured-experiment bounds are statements about
`runQuantumAdv` itself, the object used by the other QROM theorems.

The class is defined by a property of the adversary's own execution
(`ClassicalQueryAddresses`), not by an event cover. It contains classical adversaries and
adversaries with quantum local computation in the response and ancilla registers. It
excludes superposition queries: `qromParityAdv` is outside it, and for that adversary the
two executions differ (`measured_parity_execution`).
-/

public import Qsag.Oracle.QromMeasuredMerkleExtraction
import all Qsag.Oracle.QromMeasuredMerkleExtraction
import all Qsag.Oracle.QromMeasuredQueryExperiment
import all Qsag.Oracle.QromExtractionBoundary
import all Qsag.Oracle.QromMerkleOnlineExtraction
import all Qsag.Oracle.MultiRoundFsQrom
import all Qsag.Oracle.ConcreteSecurityBudget

public section
namespace Qsag

set_option autoImplicit false

/-- The state before query `t` is supported on the single query address `addr H t`. -/
def ClassicalQueryAddresses {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (addr : (Fin cardX → BitVec w) → Nat → Fin cardX) : Prop :=
  ∀ (H : Fin cardX → BitVec w) (t : Nat) (ht : t < q) (x : Fin cardX) (y : Fin (2 ^ w))
    (a : Fin cardAnc), x ≠ addr H t → advStateAt A H t (Nat.le_of_lt ht) x y a = GaussInt.zero

/-- The address log of the first `t` queries, most recent first. -/
def classicalQueryLog {cardX w : Nat} (addr : (Fin cardX → BitVec w) → Nat → Fin cardX)
    (H : Fin cardX → BitVec w) : Nat → List (Fin cardX)
  | 0 => []
  | t + 1 => addr H t :: classicalQueryLog addr H t

theorem classicalQueryLog_length {cardX w : Nat}
    (addr : (Fin cardX → BitVec w) → Nat → Fin cardX) (H : Fin cardX → BitVec w) :
    ∀ t, (classicalQueryLog addr H t).length = t
  | 0 => rfl
  | t + 1 => congrArg Nat.succ (classicalQueryLog_length addr H t)

theorem ScaledUnitary.apply_zero {cardX w cardAnc : Nat} (U : ScaledUnitary cardX w cardAnc) :
    U.apply (QVec.zero cardX w cardAnc) = QVec.zero cardX w cardAnc := by
  have hz : (QVec.zero cardX w cardAnc).sub (QVec.zero cardX w cardAnc) =
      QVec.zero cardX w cardAnc := rfl
  have h := U.map_sub (QVec.zero cardX w cardAnc) (QVec.zero cardX w cardAnc)
  rw [hz] at h
  rw [h]
  funext x y a
  exact GaussInt.ext (Int.sub_self _) (Int.sub_self _)

theorem queryMassOn_zero {cardX w cardAnc : Nat} (S : Fin cardX → Bool) :
    QVec.queryMassOn S (QVec.zero cardX w cardAnc) = 0 := by
  have hw : ∀ x, QVec.queryWeight (QVec.zero cardX w cardAnc) x = 0 := by
    intro x
    show qsum (2 ^ w) (fun _ => qsum cardAnc (fun _ => 0)) = 0
    simp only [qsum_const, Nat.mul_zero]
  have h0 : ∀ x, (if S x = true then QVec.queryWeight (QVec.zero cardX w cardAnc) x else 0) = 0 :=
    fun x => by rw [hw x]; exact ite_self 0
  show qsum cardX (fun x => if S x = true then
    QVec.queryWeight (QVec.zero cardX w cardAnc) x else 0) = 0
  rw [qsum_congr h0, qsum_const, Nat.mul_zero]

/-- Only the branch of the adversary's own address log is nonzero, and it is the coherent
    state. -/
theorem measuredStateAt_classical {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (addr : (Fin cardX → BitVec w) → Nat → Fin cardX) (hC : ClassicalQueryAddresses A addr)
    (H : Fin cardX → BitVec w) :
    ∀ (t : Nat) (ht : t ≤ q) (xs : List (Fin cardX)), xs.length = t →
      measuredStateAt A H t ht xs =
        if xs = classicalQueryLog addr H t then advStateAt A H t ht
        else QVec.zero cardX w cardAnc
  | 0, _, [], _ => (ite_eq_left rfl).symm
  | 0, _, _ :: _, h => absurd h (Nat.succ_ne_zero _)
  | _ + 1, _, [], h => absurd h.symm (Nat.succ_ne_zero _)
  | t + 1, ht, x :: xs, h => by
    have hLen : xs.length = t := Nat.succ.inj h
    have ih := measuredStateAt_classical A addr hC H t (Nat.le_of_succ_le ht) xs hLen
    show (A.steps ⟨t, ht⟩).apply (measuredOracleQueryBranch H
        (measuredStateAt A H t (Nat.le_of_succ_le ht) xs) x) =
      if x :: xs = addr H t :: classicalQueryLog addr H t then
        (A.steps ⟨t, ht⟩).apply (oracleXor H (advStateAt A H t (Nat.le_of_succ_le ht)))
      else QVec.zero cardX w cardAnc
    rw [ih]
    by_cases hxs : xs = classicalQueryLog addr H t
    · rw [ite_eq_left hxs]
      by_cases hx : x = addr H t
      · rw [ite_eq_left (by rw [hx, hxs])]
        refine congrArg (A.steps ⟨t, ht⟩).apply ?_
        funext x' y a
        show (if x' = x then oracleXor H (advStateAt A H t (Nat.le_of_succ_le ht)) x' y a
          else GaussInt.zero) = oracleXor H (advStateAt A H t (Nat.le_of_succ_le ht)) x' y a
        by_cases hx' : x' = x
        · rw [ite_eq_left hx']
        · rw [ite_eq_right hx']
          exact (hC H t ht x' _ a (fun he => hx' (he.trans hx.symm))).symm
      · rw [ite_eq_right (fun he => hx (List.cons.inj he).1)]
        have hz : measuredOracleQueryBranch H (advStateAt A H t (Nat.le_of_succ_le ht)) x =
            QVec.zero cardX w cardAnc := by
          funext x' y a
          show (if x' = x then oracleXor H (advStateAt A H t (Nat.le_of_succ_le ht)) x' y a
            else GaussInt.zero) = GaussInt.zero
          by_cases hx' : x' = x
          · rw [ite_eq_left hx']
            exact hC H t ht x' _ a (fun he => hx (hx'.symm.trans he))
          · rw [ite_eq_right hx']
        rw [hz, ScaledUnitary.apply_zero]
    · rw [ite_eq_right hxs, ite_eq_right (fun he => hxs (List.cons.inj he).2)]
      have hz : measuredOracleQueryBranch H (QVec.zero cardX w cardAnc) x =
          QVec.zero cardX w cardAnc := by
        funext x' y a
        show (if x' = x then GaussInt.zero else GaussInt.zero) = GaussInt.zero
        exact ite_self _
      rw [hz, ScaledUnitary.apply_zero]

/-- A log sum whose summand vanishes off one log is the summand at that log. -/
theorem sumLogs_single (cardX : Nat) : ∀ (t : Nat) (l : List (Fin cardX)), l.length = t →
    ∀ (f : List (Fin cardX) → Nat), (∀ xs, xs.length = t → xs ≠ l → f xs = 0) →
      sumLogs cardX t f = f l
  | 0, [], _, _, _ => rfl
  | 0, _ :: _, h, _, _ => absurd h (Nat.succ_ne_zero _)
  | _ + 1, [], h, _, _ => absurd h.symm (Nat.succ_ne_zero _)
  | t + 1, a :: l, h, f, hf => by
    have hInner : ∀ x, sumLogs cardX t (fun xs => f (x :: xs)) =
        if x = a then f (a :: l) else 0 := by
      intro x
      by_cases hx : x = a
      · rw [ite_eq_left hx, hx]
        exact sumLogs_single cardX t l (Nat.succ.inj h) (fun xs => f (a :: xs))
          (fun xs hLen hne => hf _ (congrArg Nat.succ hLen) (fun he => hne (List.cons.inj he).2))
      · rw [ite_eq_right hx]
        have hz : ∀ xs, xs.length = t → f (x :: xs) = 0 :=
          fun xs hLen => hf _ (congrArg Nat.succ hLen) (fun he => hx (List.cons.inj he).1)
        have hLe : sumLogs cardX t (fun xs => f (x :: xs)) ≤ sumLogs cardX t (fun _ => 0 * 0) :=
          sumLogs_le_of_length cardX t _ _ (fun xs hLen => Nat.le_of_eq (hz xs hLen))
        have hZero : sumLogs cardX t (fun _ => 0 * 0) = 0 :=
          (sumLogs_mul cardX t 0 (fun _ => 0)).trans (Nat.zero_mul _)
        exact Nat.le_antisymm (hZero ▸ hLe) (Nat.zero_le _)
    show qsum cardX (fun x => sumLogs cardX t (fun xs => f (x :: xs))) = f (a :: l)
    rw [qsum_congr hInner, qsum_ite_eq]

/-- **Transfer.** For a classical-address adversary, any log-indexed payoff that vanishes on
    the zero state has the same value in the measured experiment and in the coherent run
    with the adversary's own address log. -/
theorem classical_query_measured_eq {cardX w cardAnc q : Nat} (A : QuantumAdv cardX w cardAnc q)
    (addr : (Fin cardX → BitVec w) → Nat → Fin cardX) (hC : ClassicalQueryAddresses A addr)
    (H : Fin cardX → BitVec w) (F : List (Fin cardX) → QVec cardX w cardAnc → Nat)
    (hF : ∀ xs, F xs (QVec.zero cardX w cardAnc) = 0) :
    sumLogs cardX q (fun xs => F xs (measuredStateAt A H q (Nat.le_refl q) xs)) =
      F (classicalQueryLog addr H q) (runQuantumAdv A H) := by
  have hAt := measuredStateAt_classical A addr hC H q (Nat.le_refl q)
  rw [sumLogs_single cardX q (classicalQueryLog addr H q) (classicalQueryLog_length addr H q)
    (fun xs => F xs (measuredStateAt A H q (Nat.le_refl q) xs))
    (fun xs hLen hne => by rw [hAt xs hLen, ite_eq_right hne]; exact hF xs)]
  rw [hAt _ (classicalQueryLog_length addr H q), ite_eq_left rfl]
  rfl

/-- **Merkle extraction-failure bound for classical-address adversaries, on the coherent
    run.** The extractor reads the adversary's own address log and the oracle answers at
    those addresses; the failure mass of `runQuantumAdv` is at most
    `(d * (3 * Q + 1) + triangleSum Q) / 2^w` of the total. -/
theorem classical_query_merkle_extraction_failure_bound {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q)
    (addr : (Fin cardX → BitVec w) → Nat → Fin cardX) (hC : ClassicalQueryAddresses A addr)
    (L : MerkleAddressLayout cardX w) (lvl d : Nat) (hLvl : lvl + d ≤ L.levels)
    (opening : Fin cardX → MerkleOpeningReadout w) :
    2 ^ w * uniformOracleSum w cardX (fun H =>
        QVec.queryMassOn (measuredMerkleFailure L lvl d opening H (classicalQueryLog addr H Q))
          (runQuantumAdv A H)) ≤
      (d * (3 * Q + 1) + triangleSum Q) *
        ((2 ^ w) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init)) := by
  have hEq : uniformOracleSum w cardX (fun H =>
        QVec.queryMassOn (measuredMerkleFailure L lvl d opening H (classicalQueryLog addr H Q))
          (runQuantumAdv A H)) =
      uniformOracleSum w cardX (fun H => sumLogs cardX Q (fun xs =>
        QVec.queryMassOn (measuredMerkleFailure L lvl d opening H xs)
          (measuredStateAt A H Q (Nat.le_refl Q) xs))) :=
    uniformOracleSum_congr w cardX _ _ (fun H =>
      (classical_query_measured_eq A addr hC H
        (fun xs ψ => QVec.queryMassOn (measuredMerkleFailure L lvl d opening H xs) ψ)
        (fun _ => queryMassOn_zero _)).symm)
  rw [hEq]
  exact measured_merkle_extraction_failure_bound A L lvl d hLvl opening

#verify_constructive
  Qsag.measuredStateAt_classical
  Qsag.classical_query_measured_eq
  Qsag.classical_query_merkle_extraction_failure_bound

end Qsag
end

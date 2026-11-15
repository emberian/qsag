module
/-
# Coherent Fourier labels record dependence, not classical answers

A phase query toggles one Fourier coordinate. This is a coherent permutation of the
oracle basis, not an observation of a query address. The empty-label initialization and
Hamming-weight facts are the first sparse-database invariant components.
-/
public import Qsag.Oracle.QromCoherentOracleRegister
import all Qsag.Oracle.QromCoherentOracleRegister
import all Qsag.Oracle.QromFourierTable
import all Qsag.Oracle.ConcreteSecurityBudget

public section
namespace Qsag
set_option autoImplicit false

@[reducible] def tableBit : (n : Nat) → OracleBitTable n → Fin n → Bool
  | 0, _, x => Fin.elim0 x
  | _ + 1, (b, _), ⟨0, _⟩ => b
  | n + 1, (_, h), ⟨i + 1, hi⟩ => tableBit n h ⟨i, Nat.lt_of_succ_lt_succ hi⟩

@[reducible] def toggleTableBit : (n : Nat) → OracleBitTable n → Fin n → OracleBitTable n
  | 0, _, x => Fin.elim0 x
  | _ + 1, (b, d), ⟨0, _⟩ => (!b, d)
  | n + 1, (b, d), ⟨i + 1, hi⟩ => (b, toggleTableBit n d ⟨i, Nat.lt_of_succ_lt_succ hi⟩)

@[reducible] def tableWeight : (n : Nat) → OracleBitTable n → Nat
  | 0, _ => 0
  | n + 1, (b, d) => (if b then 1 else 0) + tableWeight n d

/-- A single queried coordinate can change the Fourier database size by at most one. -/
theorem tableWeight_toggle_le : ∀ n (d : OracleBitTable n) (x : Fin n),
    tableWeight n d ≤ tableWeight n (toggleTableBit n d x) + 1
  | 0, _, x => Fin.elim0 x
  | n + 1, (b, d), x => by
    refine Fin.cases ?_ (fun j => ?_) x
    · change (if b then 1 else 0) + tableWeight n d ≤
        (if !b then 1 else 0) + tableWeight n d + 1
      cases b <;> simp <;> omega
    · have ih := tableWeight_toggle_le n d j
      change (if b then 1 else 0) + tableWeight n d ≤
        (if b then 1 else 0) + tableWeight n (toggleTableBit n d j) + 1
      omega

theorem oracleWalsh_neg : ∀ n (f : OracleBitTable n → GaussInt) (d : OracleBitTable n),
    oracleWalsh n (fun h => (f h).neg) d = (oracleWalsh n f d).neg
  | 0, _, _ => rfl
  | n + 1, f, (b, d) => by
    simp only [oracleWalsh, oracleWalsh_neg]
    cases b <;> apply GaussInt.ext <;> simp [GaussInt.neg, GaussInt.add, GaussInt.sub] <;> omega

/-- Operational Fourier query law for phase kickback, valid at superposed input addresses.
    Multiplication by (-1)^H(x) toggles database coordinate x coherently. -/
theorem oracleWalsh_phase_query : ∀ n (f : OracleBitTable n → GaussInt)
    (d : OracleBitTable n) (x : Fin n),
    oracleWalsh n (fun h => if tableBit n h x then (f h).neg else f h) d =
      oracleWalsh n f (toggleTableBit n d x)
  | 0, _, _, x => Fin.elim0 x
  | n + 1, f, (b, d), x => by
    refine Fin.cases ?_ (fun j => ?_) x
    · change (if b then
        (oracleWalsh n (fun h => f (false, h)) d).sub
          (oracleWalsh n (fun h => (f (true, h)).neg) d)
        else (oracleWalsh n (fun h => f (false, h)) d).add
          (oracleWalsh n (fun h => (f (true, h)).neg) d)) =
        (if !b then (oracleWalsh n (fun h => f (false, h)) d).sub
          (oracleWalsh n (fun h => f (true, h)) d)
        else (oracleWalsh n (fun h => f (false, h)) d).add
          (oracleWalsh n (fun h => f (true, h)) d))
      rw [oracleWalsh_neg]
      cases b <;> apply GaussInt.ext <;> simp [GaussInt.neg, GaussInt.add, GaussInt.sub] <;> omega
    · change (if b then
        (oracleWalsh n (fun h => if tableBit n h j then (f (false, h)).neg else f (false, h)) d).sub
          (oracleWalsh n (fun h => if tableBit n h j then (f (true, h)).neg else f (true, h)) d)
        else (oracleWalsh n (fun h => if tableBit n h j then (f (false, h)).neg else f (false, h)) d).add
          (oracleWalsh n (fun h => if tableBit n h j then (f (true, h)).neg else f (true, h)) d)) =
        (if b then (oracleWalsh n (fun h => f (false, h)) (toggleTableBit n d j)).sub
          (oracleWalsh n (fun h => f (true, h)) (toggleTableBit n d j))
        else (oracleWalsh n (fun h => f (false, h)) (toggleTableBit n d j)).add
          (oracleWalsh n (fun h => f (true, h)) (toggleTableBit n d j)))
      rw [oracleWalsh_phase_query n (fun h => f (false, h)) d j,
        oracleWalsh_phase_query n (fun h => f (true, h)) d j]

theorem oracleWalsh_const : ∀ n (z : GaussInt) (d : OracleBitTable n),
    oracleWalsh n (fun _ => z) d = if tableWeight n d = 0 then gaussDoublePow n z else GaussInt.zero
  | 0, _, _ => rfl
  | n + 1, z, (b, d) => by
    simp only [oracleWalsh, oracleWalsh_const, tableWeight]
    by_cases hd : tableWeight n d = 0
    · rw [ite_eq_left hd]
      cases b <;> apply GaussInt.ext <;>
        simp [hd, gaussDoublePow, GaussInt.add, GaussInt.sub, GaussInt.zero]
    · rw [ite_eq_right hd]
      have hn : 0 < tableWeight n d := Nat.pos_of_ne_zero hd
      cases b <;> apply GaussInt.ext <;>
        simp [hd, GaussInt.add, GaussInt.sub, GaussInt.zero]

/-- Uniform oracle purification starts at the empty Fourier label, without measuring H. -/
theorem fourier_initial_empty {n cardAnc Q : Nat} (A : QuantumAdv n 1 cardAnc Q)
    (d : OracleBitTable n) (h : tableWeight n d ≠ 0) :
    fourierAdvStateAt A 0 (Nat.zero_le Q) d = QVec.zero n 1 cardAnc := by
  funext x y a
  exact (oracleWalsh_const n (A.init x y a) d).trans (ite_eq_right h)

/-- The finite bit-table decoder agrees pointwise with its Boolean coordinate. -/
theorem tableBitOracle_eq : ∀ n (h : OracleBitTable n) (x : Fin n),
    tableBitOracle n h x = if tableBit n h x then 1#1 else 0#1
  | 0, _, x => Fin.elim0 x
  | n + 1, (b, h), x => by
    refine Fin.cases ?_ (fun j => ?_) x
    · rfl
    · exact tableBitOracle_eq n h j

/-- Multiplexer law: the computational-response query is a coherent sum of an unchanged
    database label and a one-coordinate toggle, with exact factor two normalization. -/
theorem oracleWalsh_mux (n : Nat) (f g : OracleBitTable n → GaussInt)
    (d : OracleBitTable n) (x : Fin n) :
    gaussDoublePow 1 (oracleWalsh n (fun h => if tableBit n h x then g h else f h) d) =
      ((oracleWalsh n f d).add (oracleWalsh n g d)).add
        ((oracleWalsh n f (toggleTableBit n d x)).sub (oracleWalsh n g (toggleTableBit n d x))) := by
  rw [← oracleWalsh_doublePow]
  have hp : ∀ h, gaussDoublePow 1 (if tableBit n h x then g h else f h) =
      ((f h).add (g h)).add (if tableBit n h x then ((f h).sub (g h)).neg else (f h).sub (g h)) := by
    intro h
    cases tableBit n h x <;> apply GaussInt.ext <;>
      simp [gaussDoublePow, GaussInt.add, GaussInt.sub, GaussInt.neg] <;> omega
  rw [oracleWalsh_congr n _ _ hp, oracleWalsh_add, oracleWalsh_add,
    oracleWalsh_phase_query, oracleWalsh_sub]

/-- Fourier transform commutes with every existing adversary local gate: no operation
    on the oracle register is smuggled into the adversary interface. -/
theorem oracleWalsh_local {cardX w cardAnc : Nat} (U : ScaledUnitary cardX w cardAnc) :
    ∀ k (ψ : OracleBitTable k → QVec cardX w cardAnc) (d : OracleBitTable k),
    U.apply (fun x y a => oracleWalsh k (fun h => ψ h x y a) d) =
      fun x y a => oracleWalsh k (fun h => U.apply (ψ h) x y a) d
  | 0, _, () => rfl
  | k + 1, ψ, (b, d) => by
    cases b
    · change U.apply (QVec.add (fun x y a => oracleWalsh k (fun h => ψ (false, h) x y a) d)
        (fun x y a => oracleWalsh k (fun h => ψ (true, h) x y a) d)) = _
      rw [U.map_add, oracleWalsh_local, oracleWalsh_local]
      rfl
    · change U.apply (QVec.sub (fun x y a => oracleWalsh k (fun h => ψ (false, h) x y a) d)
        (fun x y a => oracleWalsh k (fun h => ψ (true, h) x y a) d)) = _
      rw [U.map_sub, oracleWalsh_local, oracleWalsh_local]
      rfl

/-- A full XOR-response query can only use the old label and a one-coordinate toggle. -/
theorem fourier_query_zero_of_neighbors {n cardAnc : Nat} (ψ : CoherentBitState n cardAnc)
    (d : OracleBitTable n)
    (hd : fourierOracleState ψ d = QVec.zero n 1 cardAnc)
    (ht : ∀ x, fourierOracleState ψ (toggleTableBit n d x) = QVec.zero n 1 cardAnc) :
    fourierOracleState (fun h => oracleXor (tableBitOracle n h) (ψ h)) d = QVec.zero n 1 cardAnc := by
  funext x y a
  have hq : (fun h => oracleXor (tableBitOracle n h) (ψ h) x y a) =
      (fun h => if tableBit n h x then ψ h x (xorFin y 1#1) a else ψ h x y a) := by
    funext h
    unfold oracleXor
    rw [tableBitOracle_eq]
    cases tableBit n h x
    · have hz : xorFin y 0#1 = y := by revert y; decide
      simp only [Bool.false_eq_true, ↓reduceIte, hz]
    · rfl
  have hm := oracleWalsh_mux n (fun h => ψ h x y a) (fun h => ψ h x (xorFin y 1#1) a) d x
  have hd0 := congrArg (fun v => v x y a) hd
  have hd1 := congrArg (fun v => v x (xorFin y 1#1) a) hd
  have ht0 := congrArg (fun v => v x y a) (ht x)
  have ht1 := congrArg (fun v => v x (xorFin y 1#1) a) (ht x)
  change oracleWalsh n (fun h => ψ h x y a) d = GaussInt.zero at hd0
  change oracleWalsh n (fun h => ψ h x (xorFin y 1#1) a) d = GaussInt.zero at hd1
  change oracleWalsh n (fun h => ψ h x y a) (toggleTableBit n d x) = GaussInt.zero at ht0
  change oracleWalsh n (fun h => ψ h x (xorFin y 1#1) a) (toggleTableBit n d x) = GaussInt.zero at ht1
  rw [hd0, hd1, ht0, ht1] at hm
  change oracleWalsh n (fun h => oracleXor (tableBitOracle n h) (ψ h) x y a) d = GaussInt.zero
  rw [hq]
  have hr := congrArg GaussInt.re hm
  have hi := congrArg GaussInt.im hm
  apply GaussInt.ext <;> simp only [gaussDoublePow, GaussInt.add, GaussInt.sub, GaussInt.zero] at * <;> omega

/-- Genuine coherent sparsity invariant: after t queries the Fourier truth-table register
    has zero amplitude on labels with more than t nonzero coordinates. This is not a list
    of queried addresses or a table of measured oracle answers. -/
theorem fourier_coherent_support {n cardAnc Q : Nat} (A : QuantumAdv n 1 cardAnc Q) :
    ∀ t (ht : t ≤ Q) (d : OracleBitTable n), t < tableWeight n d →
      fourierOracleState (fun h => advStateAt A (tableBitOracle n h) t ht) d = QVec.zero n 1 cardAnc
  | 0, _, d, hd => by
    funext x y a
    exact (oracleWalsh_const n (A.init x y a) d).trans (ite_eq_right (by omega))
  | t + 1, ht, d, hd => by
    let ψ := fun h => advStateAt A (tableBitOracle n h) t (Nat.le_of_succ_le ht)
    have hD : fourierOracleState ψ d = QVec.zero n 1 cardAnc :=
      fourier_coherent_support A t (Nat.le_of_succ_le ht) d (by omega)
    have hT : ∀ x, fourierOracleState ψ (toggleTableBit n d x) = QVec.zero n 1 cardAnc := by
      intro x
      have hw := tableWeight_toggle_le n d x
      exact fourier_coherent_support A t (Nat.le_of_succ_le ht) _ (by omega)
    have hz := fourier_query_zero_of_neighbors ψ d hD hT
    have hl := oracleWalsh_local (A.steps ⟨t, ht⟩) n
      (fun h => oracleXor (tableBitOracle n h) (ψ h)) d
    change (fun x y a => oracleWalsh n
      (fun h => (A.steps ⟨t, ht⟩).apply (oracleXor (tableBitOracle n h) (ψ h)) x y a) d) = _
    rw [← hl]
    change (A.steps ⟨t, ht⟩).apply (fourierOracleState
      (fun h => oracleXor (tableBitOracle n h) (ψ h)) d) = _
    rw [hz, ScaledUnitary.apply_zero]

/-- The independently executed Fourier runtime obeys the same Q-entry support cap. -/
theorem fourier_runtime_support {n cardAnc Q : Nat} (A : QuantumAdv n 1 cardAnc Q)
    (t : Nat) (ht : t ≤ Q) (d : OracleBitTable n) (hd : t < tableWeight n d) :
    fourierAdvStateAt A t ht d = QVec.zero n 1 cardAnc := by
  rw [fourierAdvStateAt_eq]
  have hz := fourier_coherent_support A t ht d hd
  change qvecDoublePow (n * t) (fourierOracleState
    (fun h => advStateAt A (tableBitOracle n h) t ht) d) = _
  rw [hz]
  funext x y a
  change gaussDoublePow (n * t) GaussInt.zero = GaussInt.zero
  generalize n * t = k
  induction k with
  | zero => rfl
  | succ k ih => simp only [gaussDoublePow, ih]; rfl

/-- Terminal measurement of the Fourier label never reports more than Q nonzero entries.
    Reading such a label is not reading the original oracle answers. -/
theorem fourier_database_overflow_mass_zero {n cardAnc Q : Nat} (A : QuantumAdv n 1 cardAnc Q) :
    oracleTableSum n (fun d => if Q < tableWeight n d then
      QVec.stateNormSq (fourierAdvStateAt A Q (Nat.le_refl Q) d) else 0) = 0 := by
  have h : ∀ d : OracleBitTable n, (if Q < tableWeight n d then
      QVec.stateNormSq (fourierAdvStateAt A Q (Nat.le_refl Q) d) else 0) = 0 := by
    intro d
    by_cases hd : Q < tableWeight n d
    · rw [ite_eq_left hd, fourier_runtime_support A Q (Nat.le_refl Q) d hd]
      simp [QVec.stateNormSq, QVec.queryWeight, QVec.zero, GaussInt.normSq_zero, qsum_const]
    · exact ite_eq_right hd
  rw [oracleTableSum_congr n _ _ h]
  have hz : ∀ k, oracleTableSum k (fun _ => 0) = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp only [oracleTableSum, ih, Nat.zero_add]
  exact hz n

def tableSame : (n : Nat) → OracleBitTable n → OracleBitTable n → Bool
  | 0, _, _ => true
  | n + 1, (a, d), (b, e) => (a == b) && tableSame n d e

/-- Actual projective measurement branch on the Fourier database. -/
def projectFourierLabel {n cardAnc : Nat} (d : OracleBitTable n)
    (ψ : CoherentBitState n cardAnc) : CoherentBitState n cardAnc :=
  fun e x y a => if tableSame n d e then ψ e x y a else GaussInt.zero

theorem oracleTableSum_zero : ∀ n, oracleTableSum n (fun _ => 0) = 0
  | 0 => rfl
  | n + 1 => by simp only [oracleTableSum, oracleTableSum_zero, Nat.zero_add]

/-- A complete computational-basis label projector picks exactly one summand. -/
theorem oracleTableSum_single : ∀ n (d : OracleBitTable n) (f : OracleBitTable n → Nat),
    oracleTableSum n (fun e => if tableSame n d e then f e else 0) = f d
  | 0, (), _ => rfl
  | n + 1, (b, d), f => by
    cases b <;> simp only [oracleTableSum, tableSame, Bool.false_beq, Bool.true_beq,
      Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · rw [oracleTableSum_single, oracleTableSum_zero, Nat.add_zero]
    · rw [oracleTableSum_zero, oracleTableSum_single, Nat.zero_add]

/-- Mass of one explicit Fourier-label measurement branch. -/
theorem projectFourierLabel_norm {n cardAnc : Nat} (d : OracleBitTable n)
    (ψ : CoherentBitState n cardAnc) :
    oracleTableSum n (fun e => QVec.stateNormSq (projectFourierLabel d ψ e)) = QVec.stateNormSq (ψ d) := by
  have h : ∀ e : OracleBitTable n, QVec.stateNormSq (projectFourierLabel d ψ e) =
      if tableSame n d e then QVec.stateNormSq (ψ e) else 0 := by
    intro e
    cases he : tableSame n d e
    · simp only [projectFourierLabel, he, Bool.false_eq_true, ↓reduceIte,
        QVec.stateNormSq, QVec.queryWeight, GaussInt.normSq_zero, qsum_const, Nat.mul_zero]
    · have hp : projectFourierLabel d ψ e = ψ e := by
        funext x y a
        exact ite_eq_left he
      rw [hp]
      rfl
  rw [oracleTableSum_congr n _ _ h, oracleTableSum_single]

/-- Measuring the database preserves total probability, even though the correlations
    tested by an oracle-dependent verifier can change after decoding. -/
theorem fourier_label_measurement_total {n cardAnc : Nat} (ψ : CoherentBitState n cardAnc) :
    oracleTableSum n (fun d => oracleTableSum n (fun e =>
      QVec.stateNormSq (fourierOracleState (projectFourierLabel d ψ) e))) =
      oracleTableSum n (fun e => QVec.stateNormSq (fourierOracleState ψ e)) := by
  simp only [fourierOracleState_norm, projectFourierLabel_norm, oracleTableSum_mul]

#verify_constructive
  Qsag.tableWeight_toggle_le
  Qsag.oracleWalsh_phase_query
  Qsag.fourier_initial_empty
  Qsag.fourier_query_zero_of_neighbors
  Qsag.fourier_coherent_support
  Qsag.fourier_runtime_support
  Qsag.fourier_database_overflow_mass_zero
  Qsag.projectFourierLabel_norm
  Qsag.fourier_label_measurement_total
end Qsag
end

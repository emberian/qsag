module
/-
# Qsag.Tests.ConstructiveQuantumHilbertTeeth — legacy bridge, exact unitaries and teeth

1. The legacy `GaussInt` register (`QVec`, `oracleXor`, `ScaledUnitary`, `QuantumAdv`) embeds into
   `QVecOver GaussIntRing`; the general measure-and-reprogram theorem specialises to the legacy
   projected inequality (`legacy_rbr_step_from_general`).
2. Exact scale-one unitaries that the scaled `ℤ[i]` register can only carry with a scale factor:
   the rational phase gate `diag(3/5 + 4/5 i, 1)` over `ℚ[i]`, and a `ℚ[i]` adversary to which the
   general theorem applies.
3. Teeth: Cauchy–Schwarz is not an equality, an idempotent that is not self-adjoint breaks the
   Pythagorean decomposition, a shear is not a scaled unitary, `3/5 + 4/5 i` is not dyadic.
-/
public import Qsag.Oracle.ConstructiveQuantumHilbert
public import Qsag.Oracle.Qrom
public import Qsag.Math.ConstructiveAmplitudeRing
public import Qsag.Math.Counting

public section
namespace Qsag
set_option autoImplicit false

open CommRingOps
open ConstructiveAmplitudeRing

/-! ## 1. The legacy `GaussInt` register inside `QVecOver GaussIntRing` -/

def gaussToRing (z : GaussInt) : GaussIntRing := ⟨z.re, z.im⟩
def ringToGauss (z : GaussIntRing) : GaussInt := ⟨z.re, z.im⟩

theorem ringToGauss_gaussToRing (z : GaussInt) : ringToGauss (gaussToRing z) = z := by rfl
theorem gaussToRing_ringToGauss (z : GaussIntRing) : gaussToRing (ringToGauss z) = z := by rfl
theorem gaussToRing_add (z w : GaussInt) :
    gaussToRing (GaussInt.add z w) = add (gaussToRing z) (gaussToRing w) := by
  rw [GaussInt.add_def]; rfl
theorem gaussToRing_sub (z w : GaussInt) :
    gaussToRing (GaussInt.sub z w) = sub (gaussToRing z) (gaussToRing w) := by
  rw [GaussInt.sub_def]; rfl
theorem gaussToRing_mul (z w : GaussInt) :
    gaussToRing (GaussInt.mul z w) = mul (gaussToRing z) (gaussToRing w) := by
  rw [GaussInt.mul_def]; rfl
theorem ringToGauss_sub (z w : GaussIntRing) :
    ringToGauss (sub z w) = GaussInt.sub (ringToGauss z) (ringToGauss w) := by
  rw [GaussInt.sub_def]; rfl

/-- The class norm on `ℤ[i]` is the legacy natural-number norm. -/
theorem gaussToRing_normSq (z : GaussInt) :
    (normSq (gaussToRing z) : Int) = Int.ofNat (GaussInt.normSq z) := by
  rw [← GaussInt.normSqInt_eq_ofNat_normSq, GaussInt.normSqInt_def, Complexified.normSq_eq]
  rfl

theorem ringSum_int_ofNat : ∀ (n : Nat) (f : Fin n → Nat),
    ringSum n (fun i => Int.ofNat (f i)) = Int.ofNat (qsum n f)
  | 0, _ => by rw [ringSum_zero_eq]; rfl
  | n + 1, f => by
    rw [ringSum_succ_eq, ringSum_int_ofNat n]
    rfl

theorem natCastR_int : ∀ n : Nat, (natCastR n : Int) = Int.ofNat n
  | 0 => by rw [natCastR_zero_eq]; rfl
  | n + 1 => by
    rw [natCastR_succ_eq, natCastR_int n]
    rfl

theorem finCountTrue_eq_qsum : ∀ (n : Nat) (p : Fin n → Bool),
    finCountTrue n p = qsum n (fun j => if p j = true then 1 else 0)
  | 0, _ => by rw [finCountTrue_zero_eq]; rfl
  | n + 1, p => by
    simp only [finCountTrue_succ_eq, qsum]
    rw [finCountTrue_eq_qsum n]
    cases p ⟨0, Nat.zero_lt_succ n⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    · simp only [↓reduceIte]
      exact Nat.add_comm _ _

section LegacyBridge
variable {cardX w cardAnc : Nat}

def liftQVec (ψ : QVec cardX w cardAnc) : QVecOver GaussIntRing cardX (2 ^ w) cardAnc :=
  fun x y a => gaussToRing (ψ x y a)

def unliftQVec (ψ : QVecOver GaussIntRing cardX (2 ^ w) cardAnc) : QVec cardX w cardAnc :=
  fun x y a => ringToGauss (ψ x y a)

theorem liftQVec_queryWeight (ψ : QVec cardX w cardAnc) (x : Fin cardX) :
    queryWeightOver (liftQVec ψ) x = Int.ofNat (QVec.queryWeight ψ x) := by
  rw [queryWeightOver_def, QVec.queryWeight_def]
  unfold liftQVec
  rw [← ringSum_int_ofNat]
  apply ringSum_congr; intro y
  rw [← ringSum_int_ofNat]
  apply ringSum_congr; intro a
  exact gaussToRing_normSq _

theorem liftQVec_stateNormSq (ψ : QVec cardX w cardAnc) :
    stateNormSqOver (liftQVec ψ) = Int.ofNat (QVec.stateNormSq ψ) := by
  rw [stateNormSqOver_def]
  unfold QVec.stateNormSq
  rw [← ringSum_int_ofNat]
  exact ringSum_congr (liftQVec_queryWeight ψ)

theorem liftQVec_queryMassOn (T : Fin cardX → Bool) (ψ : QVec cardX w cardAnc) :
    queryMassOnOver T (liftQVec ψ) = Int.ofNat (QVec.queryMassOn T ψ) := by
  rw [queryMassOnOver_def, QVec.queryMassOn_def]
  rw [← ringSum_int_ofNat]
  apply ringSum_congr; intro x
  cases T x
  · rfl
  · simp only [↓reduceIte]
    exact liftQVec_queryWeight ψ x

/-- Bitwise XOR of the answer into the response register, as a response gate. -/
def xorGate (w : Nat) : ResponseGate (BitVec w) (2 ^ w) where
  act v y := xorFin y v
  actInv v y := xorFin y v
  left_inv v y := xorFin_involutive v y
  right_inv v y := xorFin_involutive v y

theorem liftQVec_oracleXor (H : Fin cardX → BitVec w) (ψ : QVec cardX w cardAnc) :
    oracleGate (xorGate w) H (liftQVec ψ) = liftQVec (oracleXor H ψ) := by
  rw [oracleGate_def, oracleXor_def]; rfl

theorem pointUpdate_eq_reprogramOracle (H : Fin cardX → BitVec w) (x : Fin cardX) (v : BitVec w) :
    pointUpdate H x v = reprogramOracle H x v := by
  rw [pointUpdate_def, reprogramOracle_def]

theorem liftQVec_sub (ψ φ : QVec cardX w cardAnc) :
    liftQVec (ψ.sub φ) = qvSub (liftQVec ψ) (liftQVec φ) := by
  rw [qvSub_def, QVec.sub_def]
  funext x y a
  exact gaussToRing_sub _ _

theorem unliftQVec_sub (ψ φ : QVecOver GaussIntRing cardX (2 ^ w) cardAnc) :
    unliftQVec (qvSub ψ φ) = (unliftQVec ψ).sub (unliftQVec φ) := by
  rw [qvSub_def, QVec.sub_def]
  funext x y a
  exact ringToGauss_sub _ _

/-- Every legacy scaled unitary is a scaled unitary over `ℤ[i]`, with the same scale. -/
def liftScaledUnitary (U : ScaledUnitary cardX w cardAnc) :
    ScaledUnitaryOver Int GaussIntRing cardX (2 ^ w) cardAnc where
  apply ψ := liftQVec (U.apply (unliftQVec ψ))
  scaleSq := Int.ofNat U.scaleSq
  map_sub ψ φ := by
    rw [unliftQVec_sub, U.map_sub, liftQVec_sub]
  normSq_eq ψ := by
    have h2 : stateNormSqOver ψ = Int.ofNat (QVec.stateNormSq (unliftQVec ψ)) :=
      liftQVec_stateNormSq (unliftQVec ψ)
    rw [liftQVec_stateNormSq, U.normSq_eq, h2]
    rfl

/-- The layers `t, …, q - 1` of a legacy adversary. -/
def liftStepsFrom {q : Nat} (A : QuantumAdv cardX w cardAnc q) :
    (k t : Nat) → t + k = q → List (ScaledUnitaryOver Int GaussIntRing cardX (2 ^ w) cardAnc)
  | 0, _, _ => []
  | k + 1, t, h =>
    liftScaledUnitary (A.steps ⟨t, Nat.lt_of_lt_of_eq (Nat.lt_add_of_pos_right (Nat.succ_pos k)) h⟩) ::
      liftStepsFrom A k (t + 1) ((Nat.succ_add_eq_add_succ t k).trans h)

theorem liftStepsFrom_length {q : Nat} (A : QuantumAdv cardX w cardAnc q) :
    ∀ (k t : Nat) (h : t + k = q), (liftStepsFrom A k t h).length = k
  | 0, _, _ => by rfl
  | k + 1, t, h => by
    show (liftStepsFrom A k (t + 1) _).length + 1 = k + 1
    rw [liftStepsFrom_length A k]

theorem run_liftStepsFrom {q : Nat} (A : QuantumAdv cardX w cardAnc q) (H : Fin cardX → BitVec w) :
    ∀ (k t : Nat) (h : t + k = q) (ht : t ≤ q),
      runStepsOver (xorGate w) H (liftStepsFrom A k t h) (liftQVec (advStateAt A H t ht)) =
        liftQVec (runQuantumAdv A H)
  | 0, t, h, ht => by
    have e : t = q := h
    subst e
    show runStepsOver (xorGate w) H [] _ = _
    rw [runStepsOver_nil, runQuantumAdv_def]
  | k + 1, t, h, ht => by
    have hlt : t < q := Nat.lt_of_lt_of_eq (Nat.lt_add_of_pos_right (Nat.succ_pos k)) h
    have ih := run_liftStepsFrom A H k (t + 1) ((Nat.succ_add_eq_add_succ t k).trans h) hlt
    rw [advStateAt_succ] at ih
    show runStepsOver (xorGate w) H
      (liftScaledUnitary (A.steps ⟨t, hlt⟩) :: liftStepsFrom A k (t + 1) _) _ = _
    rw [runStepsOver_cons, liftQVec_oracleXor]
    exact ih

/-- A legacy adversary as an adversary over `ℤ[i]`. -/
def liftQuantumAdv {q : Nat} (A : QuantumAdv cardX w cardAnc q) :
    QuantumAdvOver Int GaussIntRing cardX (2 ^ w) cardAnc :=
  ⟨liftQVec A.init, liftStepsFrom A q 0 (Nat.zero_add q)⟩

theorem liftQuantumAdv_length {q : Nat} (A : QuantumAdv cardX w cardAnc q) :
    (liftQuantumAdv A).steps.length = q :=
  liftStepsFrom_length A q 0 (Nat.zero_add q)

/-- The general runtime reproduces the legacy runtime exactly. -/
theorem liftQuantumAdv_run {q : Nat} (A : QuantumAdv cardX w cardAnc q) (H : Fin cardX → BitVec w) :
    runQuantumAdvOver (xorGate w) (liftQuantumAdv A) H = liftQVec (runQuantumAdv A H) := by
  have h := run_liftStepsFrom A H q 0 (Nat.zero_add q) (Nat.zero_le q)
  rw [advStateAt_zero] at h
  rw [runQuantumAdvOver_def]
  exact h

/-- **The general theorem specialises to the legacy projected step.** This is the inequality of
    `qrom_unitary_measure_reprogram_rbr_step_projected` with the common factor `2^w` cancelled,
    obtained from `qrom_measure_reprogram_rbr_step_over` at `A = ℤ[i]` and the XOR gate. -/
theorem legacy_rbr_step_from_general {Q : Nat} (A : QuantumAdv cardX w cardAnc Q)
    (H : Fin cardX → BitVec w) (proj : Fin cardX → Fin cardX) (isDoomed : Fin cardX → Bool)
    (flipsToLive : Fin cardX → BitVec w → Bool) (badCard : Nat)
    (hRbr : ∀ x : Fin cardX, isDoomed x = true →
      qsum (2 ^ w) (fun j => if flipsToLive x (BitVec.ofFin j) = true then 1 else 0) ≤ badCard) :
    qsum cardX (fun xStar =>
        if isDoomed xStar = true then
          qsum (2 ^ w) (fun j =>
            if flipsToLive xStar (BitVec.ofFin j) = true then
              QVec.queryMassOn (fun x => decide (xStar = proj x))
                (runQuantumAdv A (reprogramOracle H xStar (BitVec.ofFin j)))
            else 0)
        else 0) ≤
      (2 * Q + 1) ^ 2 * badCard * QVec.stateNormSq (runQuantumAdv A H) := by
  have h := qrom_measure_reprogram_rbr_step_over (xorGate w) (liftQuantumAdv A) H proj
    (fun j : Fin (2 ^ w) => BitVec.ofFin j) isDoomed
    (fun x j => flipsToLive x (BitVec.ofFin j)) badCard
    (fun x hx => by rw [finCountTrue_eq_qsum]; exact hRbr x hx)
  rw [liftQuantumAdv_length, liftQuantumAdv_run, liftQVec_stateNormSq, natCastR_int] at h
  have hL : ringSum cardX (fun xStar =>
        if isDoomed xStar = true then
          ringSum (2 ^ w) (fun j =>
            if flipsToLive xStar (BitVec.ofFin j) = true then
              queryMassOnOver (fun x => decide (xStar = proj x))
                (runQuantumAdvOver (xorGate w) (liftQuantumAdv A)
                  (pointUpdate H xStar (BitVec.ofFin j)))
            else zero)
        else zero) =
      Int.ofNat (qsum cardX (fun xStar =>
        if isDoomed xStar = true then
          qsum (2 ^ w) (fun j =>
            if flipsToLive xStar (BitVec.ofFin j) = true then
              QVec.queryMassOn (fun x => decide (xStar = proj x))
                (runQuantumAdv A (reprogramOracle H xStar (BitVec.ofFin j)))
            else 0)
        else 0)) := by
    rw [← ringSum_int_ofNat]
    apply ringSum_congr; intro xStar
    cases isDoomed xStar
    · rfl
    · simp only [↓reduceIte]
      rw [← ringSum_int_ofNat]
      apply ringSum_congr; intro j
      cases flipsToLive xStar (BitVec.ofFin j)
      · rfl
      · simp only [↓reduceIte]
        rw [liftQuantumAdv_run, liftQVec_queryMassOn, pointUpdate_eq_reprogramOracle]
  rw [hL] at h
  exact Int.ofNat_le.mp h

end LegacyBridge

/-! ## 2. Exact scale-one unitaries over `ℚ[i]` -/

/-- The phase gate `diag(3/5 + 4/5 i, 1)`. -/
def rationalPhaseMatrix : Fin 2 → Fin 2 → RatComplex
  | ⟨0, _⟩, ⟨0, _⟩ => unitThreeFourFifths
  | ⟨1, _⟩, ⟨1, _⟩ => one
  | _, _ => zero

/-- It is an exact unitary: `M† M = 1 • I`, with scale one and no rescaling. -/
theorem rationalPhaseMatrix_unitary : IsScaledUnitary rationalPhaseMatrix (one : RatQ) := by
  have hu : mul (star unitThreeFourFifths) unitThreeFourFifths = one := by
    rw [LawfulCommRing.mul_comm]
    exact unitThreeFourFifths_mul_star
  rw [IsScaledUnitary_def]
  intro j k
  rw [ringSum_succ_eq, ringSum_succ_eq, ringSum_zero_eq]
  match j, k with
  | ⟨0, _⟩, ⟨0, _⟩ =>
    show add (mul (star unitThreeFourFifths) unitThreeFourFifths)
      (add (mul (star (zero : RatComplex)) zero) zero) = ofReal one
    rw [hu, star_zero (R := RatQ), ofReal_one]
    constructive_ring
  | ⟨0, _⟩, ⟨1, _⟩ =>
    show add (mul (star unitThreeFourFifths) zero)
      (add (mul (star (zero : RatComplex)) one) zero) = zero
    rw [star_zero (R := RatQ)]
    constructive_ring
  | ⟨1, _⟩, ⟨0, _⟩ =>
    show add (mul (star (zero : RatComplex)) unitThreeFourFifths)
      (add (mul (star (one : RatComplex)) zero) zero) = zero
    rw [star_zero (R := RatQ)]
    constructive_ring
  | ⟨1, _⟩, ⟨1, _⟩ =>
    show add (mul (star (zero : RatComplex)) zero)
      (add (mul (star (one : RatComplex)) one) zero) = ofReal one
    rw [star_zero (R := RatQ), star_one (R := RatQ), ofReal_one]
    constructive_ring
  | ⟨n + 2, h⟩, _ => exact absurd h (by omega)
  | _, ⟨n + 2, h⟩ => exact absurd h (by omega)

/-- The rational phase gate preserves every norm exactly. -/
theorem rationalPhaseMatrix_preserves_norm (ψ : HVec RatComplex 2) :
    normSqVec (matVec rationalPhaseMatrix ψ) = normSqVec ψ := by
  rw [matVec_normSq rationalPhaseMatrix_unitary, LawfulCommRing.one_mul]

/-- The unnormalised Hadamard matrix over `ℤ[i]`, a scaled unitary with scale two. -/
def hadamardMatrix : Fin 2 → Fin 2 → GaussIntRing
  | ⟨1, _⟩, ⟨1, _⟩ => neg one
  | _, _ => one

theorem hadamardMatrix_scaled_unitary : IsScaledUnitary hadamardMatrix (2 : Int) := by
  rw [IsScaledUnitary_def]
  simp only [ringSum_succ_eq, ringSum_zero_eq]
  intro j k
  apply Complexified.ext'
  · revert j k; decide
  · revert j k; decide

/-- A controlled swap of a one-bit response register. -/
def boolSwapGate : ResponseGate Bool 2 where
  act v y := if v = true then ⟨1 - y.val, by omega⟩ else y
  actInv v y := if v = true then ⟨1 - y.val, by omega⟩ else y
  left_inv v y := by
    cases v
    · rfl
    · apply Fin.ext
      show 1 - (1 - y.val) = y.val
      have := y.isLt
      omega
  right_inv v y := by
    cases v
    · rfl
    · apply Fin.ext
      show 1 - (1 - y.val) = y.val
      have := y.isLt
      omega

/-- A one-query adversary over `ℚ[i]` whose layer is the rational phase `3/5 + 4/5 i`. -/
def rationalPhaseAdv : QuantumAdvOver RatQ RatComplex 2 2 1 :=
  ⟨fun _ _ _ => one, [ScaledUnitaryOver.phase unitThreeFourFifths]⟩

/-- Its run is exactly norm-preserving: the scale is one, not `25`. -/
theorem rationalPhaseAdv_exact_unitary (H : Fin 2 → Bool) :
    stateNormSqOver (runQuantumAdvOver boolSwapGate rationalPhaseAdv H) =
      stateNormSqOver rationalPhaseAdv.init := by
  rw [runQuantumAdvOver_normSq]
  show mul (stepsScaleOver [ScaledUnitaryOver.phase unitThreeFourFifths]) _ = _
  rw [stepsScaleOver_cons, stepsScaleOver_nil, ScaledUnitaryOver.phase_scaleSq,
    unitThreeFourFifths_normSq]
  constructive_ring

/-- The general measure-and-reprogram step applies to it: one flipping challenge of two,
    one query, factor `(2 · 1 + 1)² · 1`. -/
theorem rationalPhaseAdv_rbr_step (H : Fin 2 → Bool) :
    OrderedCommRing.le
      (ringSum 2 (fun xStar =>
        if (fun _ : Fin 2 => true) xStar = true then
          ringSum 2 (fun j =>
            if (fun (_ : Fin 2) (j : Fin 2) => decide (j.val = 0)) xStar j = true then
              queryWeightOver (runQuantumAdvOver boolSwapGate rationalPhaseAdv
                (pointUpdate H xStar ((fun j : Fin 2 => decide (j.val = 1)) j))) xStar
            else zero)
        else zero))
      (mul (natCastR ((2 * rationalPhaseAdv.steps.length + 1) ^ 2 * 1))
        (stateNormSqOver (runQuantumAdvOver boolSwapGate rationalPhaseAdv H))) :=
  qrom_measure_reprogram_rbr_step_over_point boolSwapGate rationalPhaseAdv H
    (fun j : Fin 2 => decide (j.val = 1)) (fun _ => true)
    (fun _ j => decide (j.val = 0)) 1 (fun _ _ => by
      rw [finCountTrue_succ_eq, finCountTrue_succ_eq, finCountTrue_zero_eq]
      decide)

/-! ## 3. Teeth -/

def basisE0 : HVec GaussIntRing 2
  | ⟨0, _⟩ => one
  | _ => zero

def basisE1 : HVec GaussIntRing 2
  | ⟨1, _⟩ => one
  | _ => zero

/-- Cauchy–Schwarz is a strict inequality for orthogonal basis states: `0 ≠ 1 · 1`. -/
theorem tooth_cauchy_schwarz_not_equality :
    ¬ (normSq (hvInner basisE0 basisE1) = mul (normSqVec basisE0) (normSqVec basisE1)) := by
  simp only [hvInner_def, normSqVec_def, ringSum_succ_eq, ringSum_zero_eq]
  decide

/-- An idempotent map that is not self-adjoint: `(x, y) ↦ (x + y, 0)`. -/
def obliqueMap (ψ : HVec GaussIntRing 2) : HVec GaussIntRing 2
  | ⟨0, _⟩ => add (ψ ⟨0, by decide⟩) (ψ ⟨1, by decide⟩)
  | _ => zero

/-- Self-adjointness is needed for the Pythagorean decomposition: `1 ≠ 1 + 2`. -/
theorem tooth_oblique_idempotent_breaks_pythagoras :
    ¬ (normSqVec basisE1 =
      add (normSqVec (obliqueMap basisE1)) (normSqVec (hvSub basisE1 (obliqueMap basisE1)))) := by
  simp only [normSqVec_def, hvSub_def, ringSum_succ_eq, ringSum_zero_eq]
  decide

/-- The shear `[[1, 1], [0, 1]]`. -/
def shearMatrix : Fin 2 → Fin 2 → GaussIntRing
  | ⟨1, _⟩, ⟨0, _⟩ => zero
  | _, _ => one

/-- A shear is not a scaled unitary for any scale: its columns are not orthogonal. -/
theorem tooth_shear_not_scaled_unitary : ¬ ∃ s : Int, IsScaledUnitary shearMatrix s := by
  rintro ⟨s, h⟩
  rw [IsScaledUnitary_def] at h
  have h01 := h ⟨0, by decide⟩ ⟨1, by decide⟩
  rw [ringSum_succ_eq, ringSum_succ_eq, ringSum_zero_eq] at h01
  have h01' : (one : GaussIntRing) = zero := h01
  have hre : (one : Int) = zero := congrArg Complexified.re h01'
  exact absurd hre (by decide)

#verify_constructive
  Qsag.gaussToRing_normSq
  Qsag.liftQVec_stateNormSq
  Qsag.liftQVec_queryMassOn
  Qsag.liftQuantumAdv_run
  Qsag.legacy_rbr_step_from_general
  Qsag.rationalPhaseMatrix_unitary
  Qsag.rationalPhaseMatrix_preserves_norm
  Qsag.hadamardMatrix_scaled_unitary
  Qsag.rationalPhaseAdv_exact_unitary
  Qsag.rationalPhaseAdv_rbr_step

#tooth_pair cauchy_schwarz_normSq vs tooth_cauchy_schwarz_not_equality
#tooth_pair OrthoProjector.pythagoras vs tooth_oblique_idempotent_breaks_pythagoras
#tooth_pair matVec_normSq vs tooth_shear_not_scaled_unitary
#tooth_pair unitThreeFourFifths_normSq vs unitThreeFourFifths_not_dyadic

end Qsag
end

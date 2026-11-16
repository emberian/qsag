module
/-
# Qsag.Oracle.ConstructiveQuantumHilbert — exact Hilbert registers over any amplitude ring

Finite-dimensional quantum registers with amplitudes in an arbitrary
`ConstructiveAmplitudeRing R A` (`ℤ[i]`, `ℚ[i]`, `ℚ[√2, i]`, …). Norms take values in the ordered
ring `R`; nothing is normalised, so no square root or division occurs.

1. Finite sums `ringSum` and their order and `*`-compatibility.
2. `HVec A n`: inner product, Lagrange's identity (hence Cauchy–Schwarz as an exact sum of
   squares), orthogonal projectors and the Pythagorean decomposition, matrices with
   `M† M = s • I` and their exact norm scaling.
3. `QVecOver A cardX cardY cardAnc`: query/response/ancilla registers, oracle gates given by any
   controlled permutation of the response register, list-of-layers adversaries `QuantumAdvOver`,
   and the measure-and-reprogram round-by-round step with factor `(2Q + 1)²`.
-/
public import Qsag.Math.ConstructiveAmplitudeRing

public section
namespace Qsag
set_option autoImplicit false

open CommRingOps
open ConstructiveAmplitudeRing (star ofReal normSq)

/-! ## 1. Finite sums in a commutative ring -/

/-- `∑_{i : Fin n} f i` in any ring, peeling the first index. -/
def ringSum {R : Type} [CommRingOps R] : (n : Nat) → (Fin n → R) → R
  | 0, _ => zero
  | n + 1, f => add (f ⟨0, Nat.zero_lt_succ n⟩)
      (ringSum n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))

/-- The canonical image of a natural number, by unary recursion. -/
def natCastR {R : Type} [CommRingOps R] : Nat → R
  | 0 => zero
  | n + 1 => add (natCastR n) one

section RingSum
variable {R : Type} [LawfulCommRing R]

theorem ringSum_congr {n : Nat} {f g : Fin n → R} (h : ∀ i, f i = g i) :
    ringSum n f = ringSum n g :=
  congrArg (ringSum n) (funext h)

theorem ringSum_zero : ∀ n : Nat, ringSum n (fun _ => (zero : R)) = zero
  | 0 => by rfl
  | n + 1 => by
    simp only [ringSum]
    rw [ringSum_zero n, LawfulCommRing.add_zero]

theorem ringSum_add : ∀ (n : Nat) (f g : Fin n → R),
    ringSum n (fun i => add (f i) (g i)) = add (ringSum n f) (ringSum n g)
  | 0, _, _ => by
    simp only [ringSum]
    rw [LawfulCommRing.add_zero]
  | n + 1, f, g => by
    simp only [ringSum]
    rw [ringSum_add n]
    constructive_ring

theorem ringSum_mul_left (c : R) : ∀ (n : Nat) (f : Fin n → R),
    ringSum n (fun i => mul c (f i)) = mul c (ringSum n f)
  | 0, _ => by
    simp only [ringSum]
    rw [LawfulCommRing.mul_zero]
  | n + 1, f => by
    simp only [ringSum]
    rw [ringSum_mul_left c n, LawfulCommRing.left_distrib]

theorem ringSum_mul_right (c : R) (n : Nat) (f : Fin n → R) :
    ringSum n (fun i => mul (f i) c) = mul (ringSum n f) c := by
  rw [LawfulCommRing.mul_comm, ← ringSum_mul_left]
  exact ringSum_congr (fun i => LawfulCommRing.mul_comm _ _)

theorem ringSum_comm : ∀ (m n : Nat) (f : Fin m → Fin n → R),
    ringSum m (fun a => ringSum n (fun b => f a b)) =
      ringSum n (fun b => ringSum m (fun a => f a b))
  | 0, n, _ => by
    simp only [ringSum]
    exact (ringSum_zero n).symm
  | m + 1, n, f => by
    simp only [ringSum]
    rw [ringSum_comm m n, ← ringSum_add]

theorem ringSum_ite_eq : ∀ (n : Nat) (a : Fin n) (v : R),
    ringSum n (fun i => if i = a then v else zero) = v
  | 0, a, _ => Fin.elim0 a
  | n + 1, ⟨0, h0⟩, v => by
    simp only [ringSum, ↓reduceIte]
    have ht : ringSum n (fun i : Fin n =>
        if (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) = ⟨0, h0⟩ then v else zero) =
        ringSum n (fun _ => zero) := by
      apply ringSum_congr
      intro i
      have hne : (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) ≠ ⟨0, h0⟩ :=
        fun he => Nat.noConfusion (congrArg Fin.val he)
      simp only [hne, ↓reduceIte]
    rw [ht, ringSum_zero, LawfulCommRing.add_zero]
  | n + 1, ⟨k + 1, hk⟩, v => by
    simp only [ringSum]
    have h0 : (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) ≠ ⟨k + 1, hk⟩ :=
      fun he => Nat.noConfusion (congrArg Fin.val he)
    simp only [h0, ↓reduceIte]
    rw [LawfulCommRing.zero_add]
    have hShift : ringSum n (fun i : Fin n =>
        if (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) = ⟨k + 1, hk⟩ then v else zero) =
        ringSum n (fun i => if i = ⟨k, Nat.lt_of_succ_lt_succ hk⟩ then v else zero) := by
      apply ringSum_congr
      intro i
      by_cases hik : i.1 = k
      · have h2 : i = ⟨k, Nat.lt_of_succ_lt_succ hk⟩ := Fin.ext hik
        have h1 : (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) = ⟨k + 1, hk⟩ :=
          Fin.ext (congrArg Nat.succ hik)
        rw [ite_eq_left h1, ite_eq_left h2]
      · have h2 : i ≠ ⟨k, Nat.lt_of_succ_lt_succ hk⟩ := fun he => hik (congrArg Fin.val he)
        have h1 : (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) ≠ ⟨k + 1, hk⟩ :=
          fun he => hik (Nat.succ.inj (congrArg Fin.val he))
        rw [ite_eq_right h1, ite_eq_right h2]
    rw [hShift]
    exact ringSum_ite_eq n ⟨k, Nat.lt_of_succ_lt_succ hk⟩ v

/-- Reindexing a finite sum along a bijection given with its inverse. -/
theorem ringSum_bijection {n : Nat} (π ρ : Fin n → Fin n)
    (hLeft : ∀ i, ρ (π i) = i) (hRight : ∀ k, π (ρ k) = k) (g : Fin n → R) :
    ringSum n (fun i => g (π i)) = ringSum n g := by
  have hExpand : ringSum n (fun i => g (π i)) =
      ringSum n (fun i => ringSum n (fun k => if k = π i then g k else zero)) := by
    apply ringSum_congr
    intro i
    have hk : ringSum n (fun k => if k = π i then g k else zero) =
        ringSum n (fun k => if k = π i then g (π i) else zero) := by
      apply ringSum_congr
      intro k
      by_cases hk : k = π i
      · rw [ite_eq_left hk, ite_eq_left hk, hk]
      · rw [ite_eq_right hk, ite_eq_right hk]
    rw [hk, ringSum_ite_eq]
  rw [hExpand, ringSum_comm]
  apply ringSum_congr
  intro k
  have hSwap : ringSum n (fun i => if k = π i then g k else zero) =
      ringSum n (fun i => if i = ρ k then g k else zero) := by
    apply ringSum_congr
    intro i
    by_cases h : i = ρ k
    · have hk : k = π i := by rw [h, hRight]
      rw [ite_eq_left hk, ite_eq_left h]
    · have hk : k ≠ π i := fun he => h (by rw [he, hLeft])
      rw [ite_eq_right hk, ite_eq_right h]
  rw [hSwap, ringSum_ite_eq]

theorem natCastR_add (m : Nat) : ∀ n : Nat,
    (natCastR (m + n) : R) = add (natCastR m) (natCastR n)
  | 0 => by
    show natCastR m = add (natCastR m) zero
    rw [LawfulCommRing.add_zero]
  | n + 1 => by
    show add (natCastR (m + n)) one = add (natCastR m) (add (natCastR n) one)
    rw [natCastR_add m n, LawfulCommRing.add_assoc]

theorem natCastR_mul (m : Nat) : ∀ n : Nat,
    (natCastR (m * n) : R) = mul (natCastR m) (natCastR n)
  | 0 => by
    show (zero : R) = mul (natCastR m) zero
    rw [LawfulCommRing.mul_zero]
  | n + 1 => by
    show natCastR (m * n + m) = mul (natCastR m) (add (natCastR n) one)
    rw [natCastR_add, natCastR_mul m n]
    constructive_ring

end RingSum

section RingSumOrder
variable {R : Type} [OrderedCommRing R]
open OrderedCommRing

theorem ringSum_le : ∀ {n : Nat} {f g : Fin n → R}, (∀ i, le (f i) (g i)) →
    le (ringSum n f) (ringSum n g)
  | 0, _, _, _ => le_refl _
  | n + 1, _, _, h => by
    simp only [ringSum]
    exact add_le_add (h _) (ringSum_le (fun i => h _))

theorem ringSum_nonneg {n : Nat} {f : Fin n → R} (h : ∀ i, le zero (f i)) :
    le zero (ringSum n f) := by
  have h1 := ringSum_le h
  rw [ringSum_zero] at h1
  exact h1

/-- A sum of nonnegative terms vanishes only if every term does. -/
theorem ringSum_eq_zero_of_nonneg : ∀ {n : Nat} {f : Fin n → R}, (∀ i, le zero (f i)) →
    ringSum n f = zero → ∀ i, f i = zero
  | 0, _, _, _, i => Fin.elim0 i
  | n + 1, f, hf, h, ⟨0, _⟩ => by
    simp only [ringSum] at h
    exact eq_zero_of_add_eq_zero_left (hf _) (ringSum_nonneg (fun i => hf _)) h
  | n + 1, f, hf, h, ⟨k + 1, hk⟩ => by
    simp only [ringSum] at h
    have ht := eq_zero_of_add_eq_zero_right (hf _) (ringSum_nonneg (fun i => hf _)) h
    exact ringSum_eq_zero_of_nonneg (f := fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
      (fun i => hf _) ht ⟨k, Nat.lt_of_succ_lt_succ hk⟩

end RingSumOrder

section AmplitudeSums
variable {R A : Type} [OrderedCommRing R] [ConstructiveAmplitudeRing R A]
open OrderedCommRing ConstructiveAmplitudeRing

theorem ofReal_ringSum : ∀ (n : Nat) (f : Fin n → R),
    (ofReal (ringSum n f) : A) = ringSum n (fun i => ofReal (f i))
  | 0, _ => by
    simp only [ringSum]
    exact ofReal_zero
  | n + 1, f => by
    simp only [ringSum]
    rw [ofReal_add, ofReal_ringSum n]

theorem star_ringSum : ∀ (n : Nat) (f : Fin n → A),
    star (ringSum n f) = ringSum n (fun i => star (f i))
  | 0, _ => by
    simp only [ringSum]
    exact star_zero (R := R)
  | n + 1, f => by
    simp only [ringSum]
    rw [star_add, star_ringSum n]

/-- `0 ≤ 1` holds in the real ring of every amplitude ring, because `1 = |1|²`. -/
theorem amplitude_one_nonneg (A : Type) [ConstructiveAmplitudeRing R A] : le (zero : R) one := by
  have h := normSq_nonneg (one : A)
  rw [normSq_one] at h
  exact h

omit [ConstructiveAmplitudeRing R A] in
theorem natCastR_nonneg (h1 : le (zero : R) one) : ∀ n : Nat, le (zero : R) (natCastR n)
  | 0 => le_refl _
  | n + 1 => add_nonneg (natCastR_nonneg h1 n) h1

omit [ConstructiveAmplitudeRing R A] in
theorem natCastR_le (h1 : le (zero : R) one) {m n : Nat} (h : m ≤ n) :
    le (natCastR m : R) (natCastR n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [natCastR_add]
  exact le_add_of_nonneg_right (natCastR_nonneg h1 k)

end AmplitudeSums

/-! ## 2. Finite-dimensional Hilbert registers -/

/-- A state vector with `n` basis states and amplitudes in `A`. -/
abbrev HVec (A : Type) (n : Nat) : Type := Fin n → A

section Hilbert
variable {R A : Type} [OrderedCommRing R] [ConstructiveAmplitudeRing R A]
open OrderedCommRing ConstructiveAmplitudeRing

def hvAdd {n : Nat} (ψ φ : HVec A n) : HVec A n := fun i => add (ψ i) (φ i)
def hvSub {n : Nat} (ψ φ : HVec A n) : HVec A n := fun i => sub (ψ i) (φ i)
def hvZero (n : Nat) : HVec A n := fun _ => zero

/-- The sesquilinear inner product `⟨ψ, φ⟩ = ∑ᵢ star (ψ i) * φ i`. -/
def hvInner {n : Nat} (ψ φ : HVec A n) : A := ringSum n (fun i => mul (star (ψ i)) (φ i))

/-- The squared norm `‖ψ‖² = ∑ᵢ |ψ i|²`, valued in the ordered ring. -/
def normSqVec {n : Nat} (ψ : HVec A n) : R := ringSum n (fun i => normSq (ψ i))

def hvHead {n : Nat} (ψ : HVec A (n + 1)) : A := ψ ⟨0, Nat.zero_lt_succ n⟩
def hvTail {n : Nat} (ψ : HVec A (n + 1)) : HVec A n :=
  fun i => ψ ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩

theorem normSqVec_succ {n : Nat} (ψ : HVec A (n + 1)) :
    normSqVec ψ = add (normSq (hvHead ψ)) (normSqVec (hvTail ψ)) := by rfl

theorem hvInner_succ {n : Nat} (ψ φ : HVec A (n + 1)) :
    hvInner ψ φ = add (mul (star (hvHead ψ)) (hvHead φ)) (hvInner (hvTail ψ) (hvTail φ)) := by
  rfl

theorem hvInner_self {n : Nat} (ψ : HVec A n) : hvInner ψ ψ = ofReal (normSqVec ψ) := by
  unfold hvInner normSqVec
  rw [ofReal_ringSum]
  apply ringSum_congr
  intro i
  rw [LawfulCommRing.mul_comm, mul_star_self]

theorem normSqVec_nonneg {n : Nat} (ψ : HVec A n) : le zero (normSqVec ψ) :=
  ringSum_nonneg (fun _ => normSq_nonneg _)

/-- Definiteness of the norm. -/
theorem normSqVec_eq_zero {n : Nat} {ψ : HVec A n} (h : normSqVec ψ = zero) (i : Fin n) :
    ψ i = zero :=
  normSq_eq_zero (ringSum_eq_zero_of_nonneg (fun _ => normSq_nonneg _) h i)

theorem hvInner_conj {n : Nat} (ψ φ : HVec A n) : star (hvInner ψ φ) = hvInner φ ψ := by
  unfold hvInner
  rw [star_ringSum]
  apply ringSum_congr
  intro i
  rw [star_mul, star_star, LawfulCommRing.mul_comm]

theorem hvInner_add_right {n : Nat} (ψ φ χ : HVec A n) :
    hvInner ψ (hvAdd φ χ) = add (hvInner ψ φ) (hvInner ψ χ) := by
  unfold hvInner hvAdd
  rw [← ringSum_add]
  exact ringSum_congr (fun i => LawfulCommRing.left_distrib _ _ _)

theorem hvInner_add_left {n : Nat} (ψ φ χ : HVec A n) :
    hvInner (hvAdd ψ φ) χ = add (hvInner ψ χ) (hvInner φ χ) := by
  unfold hvInner hvAdd
  rw [← ringSum_add]
  apply ringSum_congr
  intro i
  rw [star_add, LawfulCommRing.right_distrib]

theorem hvInner_zero_right {n : Nat} (ψ : HVec A n) : hvInner ψ (hvZero n) = zero := by
  unfold hvInner hvZero
  exact (ringSum_congr (fun i => LawfulCommRing.mul_zero _)).trans (ringSum_zero n)

/-- The sum of the squared `2 × 2` minors pairing the first coordinate with every later one,
    plus the same for the tails: `∑_{i < j} |ψᵢ φⱼ - ψⱼ φᵢ|²`. -/
def lagrangeDefect : (n : Nat) → HVec A n → HVec A n → R
  | 0, _, _ => zero
  | n + 1, ψ, φ =>
    add (ringSum n (fun j =>
        normSq (sub (mul (hvHead ψ) (hvTail φ j)) (mul (hvTail ψ j) (hvHead φ)))))
      (lagrangeDefect n (hvTail ψ) (hvTail φ))

theorem lagrangeDefect_nonneg : ∀ (n : Nat) (ψ φ : HVec A n), le zero (lagrangeDefect n ψ φ)
  | 0, _, _ => le_refl _
  | n + 1, ψ, φ =>
    add_nonneg (ringSum_nonneg (fun _ => normSq_nonneg _))
      (lagrangeDefect_nonneg n (hvTail ψ) (hvTail φ))

private theorem lagrange_cross (a b : A) : ∀ (n : Nat) (u v : HVec A n),
    (ofReal (ringSum n (fun j => normSq (sub (mul a (v j)) (mul (u j) b)))) : A) =
      sub (add (mul (mul a (star a)) (ofReal (normSqVec v)))
          (mul (mul b (star b)) (ofReal (normSqVec u))))
        (add (mul (mul a (star b)) (hvInner u v))
          (mul (mul (star a) b) (star (hvInner u v))))
  | 0, _, _ => by
    simp only [ringSum, normSqVec, hvInner]
    rw [ofReal_zero, star_zero (R := R)]
    constructive_ring
  | n + 1, u, v => by
    have ih := lagrange_cross a b n (hvTail u) (hvTail v)
    rw [normSqVec_succ, normSqVec_succ, hvInner_succ]
    simp only [ringSum]
    rw [ofReal_add]
    change add (ofReal (normSq (sub (mul a (hvHead v)) (mul (hvHead u) b))))
      (ofReal (ringSum n (fun j => normSq (sub (mul a (hvTail v j)) (mul (hvTail u j) b))))) = _
    rw [ih, ← mul_star_self, ofReal_add, ofReal_add, ← mul_star_self (hvHead v),
      ← mul_star_self (hvHead u), star_sub, star_mul, star_mul, star_add, star_mul, star_star]
    constructive_ring

/-- **Lagrange's identity** over any amplitude ring:
    `‖ψ‖² ‖φ‖² = |⟨ψ, φ⟩|² + ∑_{i < j} |ψᵢ φⱼ - ψⱼ φᵢ|²`. -/
theorem lagrange_identity : ∀ (n : Nat) (ψ φ : HVec A n),
    mul (normSqVec ψ) (normSqVec φ) = add (normSq (hvInner ψ φ)) (lagrangeDefect n ψ φ)
  | 0, ψ, φ => by
    simp only [normSqVec, hvInner, lagrangeDefect, ringSum]
    rw [normSq_zero]
    constructive_ring
  | n + 1, ψ, φ => by
    have ih := lagrange_identity n (hvTail ψ) (hvTail φ)
    have ihA : (ofReal (lagrangeDefect n (hvTail ψ) (hvTail φ)) : A) =
        sub (mul (ofReal (normSqVec (hvTail ψ))) (ofReal (normSqVec (hvTail φ))))
          (mul (hvInner (hvTail ψ) (hvTail φ)) (star (hvInner (hvTail ψ) (hvTail φ)))) := by
      rw [← ofReal_mul, ih, ofReal_add, ← mul_star_self]
      constructive_ring
    apply ofReal_injective (A := A)
    rw [normSqVec_succ, normSqVec_succ, hvInner_succ]
    change ofReal (mul (add (normSq (hvHead ψ)) (normSqVec (hvTail ψ)))
        (add (normSq (hvHead φ)) (normSqVec (hvTail φ)))) =
      ofReal (add (normSq (add (mul (star (hvHead ψ)) (hvHead φ)) (hvInner (hvTail ψ) (hvTail φ))))
        (add (ringSum n (fun j =>
            normSq (sub (mul (hvHead ψ) (hvTail φ j)) (mul (hvTail ψ j) (hvHead φ)))))
          (lagrangeDefect n (hvTail ψ) (hvTail φ))))
    rw [ofReal_mul, ofReal_add, ofReal_add, ofReal_add, ofReal_add, ihA,
      lagrange_cross (hvHead ψ) (hvHead φ) n (hvTail ψ) (hvTail φ),
      ← mul_star_self (hvHead ψ), ← mul_star_self (hvHead φ), ← mul_star_self,
      star_add, star_mul, star_star]
    constructive_ring

/-- **Cauchy–Schwarz** `|⟨ψ, φ⟩|² ≤ ‖ψ‖² ‖φ‖²`, with no square root and no division. -/
theorem cauchy_schwarz_normSq {n : Nat} (ψ φ : HVec A n) :
    le (normSq (hvInner ψ φ)) (mul (normSqVec ψ) (normSqVec φ)) := by
  rw [lagrange_identity]
  exact le_add_of_nonneg_right (lagrangeDefect_nonneg n ψ φ)

/-- An orthogonal projector: a difference-preserving idempotent self-adjoint map. -/
structure OrthoProjector (A : Type) {R : Type} [OrderedCommRing R]
    [ConstructiveAmplitudeRing R A] (n : Nat) where
  apply : HVec A n → HVec A n
  map_sub : ∀ ψ φ, apply (hvSub ψ φ) = hvSub (apply ψ) (apply φ)
  idem : ∀ ψ, apply (apply ψ) = apply ψ
  self_adjoint : ∀ ψ φ, hvInner (apply ψ) φ = hvInner ψ (apply φ)

/-- The range of `P` is orthogonal to the range of `I - P`. -/
theorem OrthoProjector.inner_complement {n : Nat} (P : OrthoProjector A n) (ψ : HVec A n) :
    hvInner (P.apply ψ) (hvSub ψ (P.apply ψ)) = zero := by
  rw [P.self_adjoint, P.map_sub, P.idem]
  have hz : hvSub (P.apply ψ) (P.apply ψ) = hvZero n :=
    funext (fun i => LawfulCommRing.sub_self _)
  rw [hz, hvInner_zero_right]

/-- **Pythagorean decomposition** `‖ψ‖² = ‖P ψ‖² + ‖(I - P) ψ‖²`. -/
theorem OrthoProjector.pythagoras {n : Nat} (P : OrthoProjector A n) (ψ : HVec A n) :
    normSqVec ψ = add (normSqVec (P.apply ψ)) (normSqVec (hvSub ψ (P.apply ψ))) := by
  apply ofReal_injective (A := A)
  have hψ : ψ = hvAdd (P.apply ψ) (hvSub ψ (P.apply ψ)) := by
    funext i
    show ψ i = add (P.apply ψ i) (sub (ψ i) (P.apply ψ i))
    constructive_ring
  have h1 := P.inner_complement ψ
  have h2 : hvInner (hvSub ψ (P.apply ψ)) (P.apply ψ) = zero := by
    rw [← hvInner_conj, h1, star_zero (R := R)]
  rw [ofReal_add, ← hvInner_self, ← hvInner_self, ← hvInner_self]
  conv => lhs; rw [hψ]
  rw [hvInner_add_left, hvInner_add_right, hvInner_add_right, h1, h2]
  constructive_ring

/-- Projection onto the basis states selected by `S`. -/
def coordProjector {n : Nat} (S : Fin n → Bool) : OrthoProjector A n where
  apply ψ := fun i => if S i = true then ψ i else zero
  map_sub ψ φ := by
    funext i
    show (if S i = true then sub (ψ i) (φ i) else zero) =
      sub (if S i = true then ψ i else zero) (if S i = true then φ i else zero)
    cases S i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (LawfulCommRing.sub_self _).symm
    · simp only [↓reduceIte]
  idem ψ := by
    funext i
    show (if S i = true then (if S i = true then ψ i else zero) else zero) =
      (if S i = true then ψ i else zero)
    cases S i <;> simp only [Bool.false_eq_true, ↓reduceIte]
  self_adjoint ψ φ := by
    unfold hvInner
    apply ringSum_congr
    intro i
    show mul (star (if S i = true then ψ i else zero)) (φ i) =
      mul (star (ψ i)) (if S i = true then φ i else zero)
    cases S i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [star_zero (R := R), LawfulCommRing.zero_mul, LawfulCommRing.mul_zero]
    · simp only [↓reduceIte]

/-- Matrix action on a register. -/
def matVec {n : Nat} (M : Fin n → Fin n → A) (ψ : HVec A n) : HVec A n :=
  fun i => ringSum n (fun j => mul (M i j) (ψ j))

/-- `M† M = s • I` for a scale `s` in the ordered ring: an exact unitary when `s = 1`. -/
def IsScaledUnitary {n : Nat} (M : Fin n → Fin n → A) (s : R) : Prop :=
  ∀ j k : Fin n, ringSum n (fun i => mul (star (M i j)) (M i k)) =
    if j = k then ofReal s else zero

/-- A scaled unitary scales every inner product by `s`. -/
theorem matVec_inner {n : Nat} {M : Fin n → Fin n → A} {s : R} (hU : IsScaledUnitary M s)
    (ψ φ : HVec A n) : hvInner (matVec M ψ) (matVec M φ) = mul (ofReal s) (hvInner ψ φ) := by
  unfold IsScaledUnitary at hU
  unfold hvInner matVec
  have step1 : ∀ i : Fin n,
      mul (star (ringSum n (fun j => mul (M i j) (ψ j)))) (ringSum n (fun k => mul (M i k) (φ k))) =
        ringSum n (fun j => ringSum n (fun k =>
          mul (mul (star (ψ j)) (φ k)) (mul (star (M i j)) (M i k)))) := by
    intro i
    rw [star_ringSum, ← ringSum_mul_right]
    apply ringSum_congr
    intro j
    rw [← ringSum_mul_left]
    apply ringSum_congr
    intro k
    rw [star_mul]
    constructive_ring
  rw [ringSum_congr step1, ringSum_comm]
  have step2 : ∀ j : Fin n,
      ringSum n (fun i => ringSum n (fun k =>
        mul (mul (star (ψ j)) (φ k)) (mul (star (M i j)) (M i k)))) =
        mul (mul (star (ψ j)) (φ j)) (ofReal s) := by
    intro j
    rw [ringSum_comm]
    have hk : ∀ k : Fin n,
        ringSum n (fun i => mul (mul (star (ψ j)) (φ k)) (mul (star (M i j)) (M i k))) =
          if k = j then mul (mul (star (ψ j)) (φ j)) (ofReal s) else zero := by
      intro k
      rw [ringSum_mul_left, hU j k]
      by_cases h : k = j
      · subst h
        rw [ite_eq_left rfl, ite_eq_left rfl]
      · have h' : ¬ j = k := fun e => h e.symm
        rw [ite_eq_right h, ite_eq_right h', LawfulCommRing.mul_zero]
    rw [ringSum_congr hk, ringSum_ite_eq]
  rw [ringSum_congr step2, ringSum_mul_right, LawfulCommRing.mul_comm]

/-- **Exact norm scaling** `‖M ψ‖² = s ‖ψ‖²` for `M† M = s • I`. -/
theorem matVec_normSq {n : Nat} {M : Fin n → Fin n → A} {s : R} (hU : IsScaledUnitary M s)
    (ψ : HVec A n) : normSqVec (matVec M ψ) = mul s (normSqVec ψ) := by
  apply ofReal_injective (A := A)
  rw [ofReal_mul, ← hvInner_self, ← hvInner_self, matVec_inner hU]

theorem matVec_sub {n : Nat} (M : Fin n → Fin n → A) (ψ φ : HVec A n) :
    matVec M (hvSub ψ φ) = hvSub (matVec M ψ) (matVec M φ) := by
  funext i
  show ringSum n (fun j => mul (M i j) (sub (ψ j) (φ j))) =
    sub (ringSum n (fun j => mul (M i j) (ψ j))) (ringSum n (fun j => mul (M i j) (φ j)))
  have e : ∀ j : Fin n, mul (M i j) (sub (ψ j) (φ j)) =
      add (mul (M i j) (ψ j)) (mul (neg one) (mul (M i j) (φ j))) := by
    intro j
    constructive_ring
  rw [ringSum_congr e, ringSum_add, ringSum_mul_left]
  constructive_ring

end Hilbert

/-! ## 3. Sums over lists and the `m`-term Cauchy–Schwarz inequality -/

/-- The sum of a list in any ring. -/
def ampListSum {R : Type} [CommRingOps R] : List R → R
  | [] => zero
  | v :: vs => add v (ampListSum vs)

section ListSums
variable {R A : Type} [OrderedCommRing R] [ConstructiveAmplitudeRing R A]
open OrderedCommRing ConstructiveAmplitudeRing

omit [ConstructiveAmplitudeRing R A] in
theorem ampListSum_map_zero {V : Type} : ∀ vs : List V,
    ampListSum (vs.map (fun _ => (zero : R))) = zero
  | [] => by rfl
  | _ :: vs => by
    show add zero (ampListSum (vs.map (fun _ => (zero : R)))) = zero
    rw [ampListSum_map_zero vs, LawfulCommRing.add_zero]

omit [ConstructiveAmplitudeRing R A] in
theorem ampListSum_map_nonneg {V : Type} (g : V → R) (h : ∀ v, le zero (g v)) :
    ∀ vs : List V, le zero (ampListSum (vs.map g))
  | [] => le_refl _
  | v :: vs => add_nonneg (h v) (ampListSum_map_nonneg g h vs)

omit [ConstructiveAmplitudeRing R A] in
/-- Exchange of a finite sum with a list sum. -/
theorem ringSum_ampListSum {V : Type} (n : Nat) (g : V → Fin n → R) : ∀ vs : List V,
    ringSum n (fun i => ampListSum (vs.map (fun v => g v i))) =
      ampListSum (vs.map (fun v => ringSum n (g v)))
  | [] => ringSum_zero n
  | v :: vs => by
    show ringSum n (fun i => add (g v i) (ampListSum (vs.map (fun v => g v i)))) =
      add (ringSum n (g v)) (ampListSum (vs.map (fun v => ringSum n (g v))))
    rw [ringSum_add, ringSum_ampListSum n g vs]

theorem ofReal_natCastR : ∀ n : Nat, (ofReal (natCastR n : R) : A) = natCastR n
  | 0 => ofReal_zero
  | n + 1 => by
    show ofReal (add (natCastR n) one) = add (natCastR n) one
    rw [ofReal_add, ofReal_natCastR n, ofReal_one]

/-- `∑_{t ∈ l} |v - t|²`. -/
def pairHeadNormSq (v : A) : List A → R
  | [] => zero
  | t :: l => add (normSq (sub v t)) (pairHeadNormSq v l)

/-- `∑_{s < t} |l_s - l_t|²`. -/
def pairAllNormSq : List A → R
  | [] => zero
  | v :: l => add (pairHeadNormSq v l) (pairAllNormSq l)

theorem pairHeadNormSq_nonneg (v : A) : ∀ l : List A, le zero (pairHeadNormSq v l)
  | [] => le_refl _
  | _ :: l => add_nonneg (normSq_nonneg _) (pairHeadNormSq_nonneg v l)

theorem pairAllNormSq_nonneg : ∀ l : List A, le zero (pairAllNormSq l)
  | [] => le_refl _
  | v :: l => add_nonneg (pairHeadNormSq_nonneg v l) (pairAllNormSq_nonneg l)

private theorem pairHeadNormSq_ofReal (v : A) : ∀ l : List A,
    (ofReal (pairHeadNormSq v l) : A) =
      sub (add (mul (natCastR l.length) (mul v (star v))) (ofReal (ampListSum (l.map normSq))))
        (add (mul v (star (ampListSum l))) (mul (star v) (ampListSum l)))
  | [] => by
    show ofReal zero = sub (add (mul zero (mul v (star v))) (ofReal zero))
      (add (mul v (star zero)) (mul (star v) zero))
    rw [ofReal_zero, star_zero (R := R)]
    constructive_ring
  | t :: l => by
    show ofReal (add (normSq (sub v t)) (pairHeadNormSq v l)) =
      sub (add (mul (add (natCastR l.length) one) (mul v (star v)))
          (ofReal (add (normSq t) (ampListSum (l.map normSq)))))
        (add (mul v (star (add t (ampListSum l)))) (mul (star v) (add t (ampListSum l))))
    rw [ofReal_add, pairHeadNormSq_ofReal v l, ← mul_star_self, ofReal_add, ← mul_star_self t,
      star_sub, star_add]
    constructive_ring

/-- **Sum-of-squares identity** `m ∑ₖ |vₖ|² = |∑ₖ vₖ|² + ∑_{s < t} |v_s - v_t|²`. -/
theorem list_sum_of_squares_identity : ∀ l : List A,
    mul (natCastR l.length) (ampListSum (l.map normSq)) =
      add (normSq (ampListSum l)) (pairAllNormSq l)
  | [] => by
    show mul zero zero = add (normSq (zero : A)) zero
    rw [normSq_zero]
    constructive_ring
  | v :: l => by
    have ih := list_sum_of_squares_identity l
    have ihA : (ofReal (pairAllNormSq l) : A) =
        sub (mul (natCastR l.length) (ofReal (ampListSum (l.map normSq))))
          (mul (ampListSum l) (star (ampListSum l))) := by
      rw [← ofReal_natCastR (R := R), ← ofReal_mul, ih, ofReal_add, ← mul_star_self]
      constructive_ring
    apply ofReal_injective (A := A)
    show ofReal (mul (add (natCastR l.length) one) (add (normSq v) (ampListSum (l.map normSq)))) =
      ofReal (add (normSq (add v (ampListSum l))) (add (pairHeadNormSq v l) (pairAllNormSq l)))
    rw [ofReal_mul, ofReal_add, ofReal_add, ofReal_add, ofReal_add, ofReal_natCastR, ofReal_one,
      pairHeadNormSq_ofReal, ihA, ← mul_star_self v, ← mul_star_self, star_add]
    constructive_ring

/-- **`m`-term Cauchy–Schwarz** `|∑ₖ vₖ|² ≤ m ∑ₖ |vₖ|²`. -/
theorem normSq_ampListSum_le (l : List A) :
    le (normSq (ampListSum l)) (mul (natCastR l.length) (ampListSum (l.map normSq))) := by
  rw [list_sum_of_squares_identity]
  exact le_add_of_nonneg_right (pairAllNormSq_nonneg l)

theorem normSq_ampListSum_map_le {V : Type} (f : V → A) (vs : List V) :
    le (normSq (ampListSum (vs.map f)))
      (mul (natCastR vs.length) (ampListSum (vs.map (fun v => normSq (f v))))) := by
  have h := normSq_ampListSum_le (vs.map f)
  rw [List.length_map, List.map_map] at h
  exact h

end ListSums

/-! ## 4. Query registers, oracle gates and adversaries -/

/-- A state on a query register `Fin cardX`, a response register `Fin cardY` and an ancilla
    `Fin cardAnc`, with amplitudes in `A`. -/
abbrev QVecOver (A : Type) (cardX cardY cardAnc : Nat) : Type :=
  Fin cardX → Fin cardY → Fin cardAnc → A

/-- How an oracle answer `v : Y` acts on the response register: a permutation with its inverse.
    Bitwise XOR, addition in a finite field and a table lookup all have this form. -/
structure ResponseGate (Y : Type) (cardY : Nat) where
  act : Y → Fin cardY → Fin cardY
  actInv : Y → Fin cardY → Fin cardY
  left_inv : ∀ v y, actInv v (act v y) = y
  right_inv : ∀ v y, act v (actInv v y) = y

/-- Reprogram a classical oracle at one point. -/
def pointUpdate {cardX : Nat} {Y : Type} (H : Fin cardX → Y) (xStar : Fin cardX) (v : Y) :
    Fin cardX → Y :=
  fun x => if x = xStar then v else H x

/-- The number of indices on which a Boolean predicate holds. -/
def finCountTrue : (n : Nat) → (Fin n → Bool) → Nat
  | 0, _ => 0
  | n + 1, p =>
    if p ⟨0, Nat.zero_lt_succ n⟩ = true then
      finCountTrue n (fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) + 1
    else finCountTrue n (fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

theorem ringSum_indicator_mul {R : Type} [LawfulCommRing R] (c : R) : ∀ (n : Nat) (p : Fin n → Bool),
    ringSum n (fun j => if p j = true then c else zero) = mul (natCastR (finCountTrue n p)) c
  | 0, _ => by
    show (zero : R) = mul zero c
    rw [LawfulCommRing.zero_mul]
  | n + 1, p => by
    have ih := ringSum_indicator_mul c n (fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    simp only [ringSum, finCountTrue]
    rw [ih]
    cases p ⟨0, Nat.zero_lt_succ n⟩
    · simp only [Bool.false_eq_true, ↓reduceIte]
      constructive_ring
    · simp only [↓reduceIte, natCastR]
      constructive_ring

section QueryRegister
variable {R A : Type} [OrderedCommRing R] [ConstructiveAmplitudeRing R A]
variable {cardX cardY cardAnc : Nat}
open OrderedCommRing ConstructiveAmplitudeRing

def qvZero : QVecOver A cardX cardY cardAnc := fun _ _ _ => zero
def qvAdd (ψ φ : QVecOver A cardX cardY cardAnc) : QVecOver A cardX cardY cardAnc :=
  fun x y a => add (ψ x y a) (φ x y a)
def qvSub (ψ φ : QVecOver A cardX cardY cardAnc) : QVecOver A cardX cardY cardAnc :=
  fun x y a => sub (ψ x y a) (φ x y a)
def qvNeg (ψ : QVecOver A cardX cardY cardAnc) : QVecOver A cardX cardY cardAnc :=
  fun x y a => neg (ψ x y a)

def qvListSum : List (QVecOver A cardX cardY cardAnc) → QVecOver A cardX cardY cardAnc
  | [] => qvZero
  | v :: vs => qvAdd v (qvListSum vs)

theorem qvListSum_apply (x : Fin cardX) (y : Fin cardY) (a : Fin cardAnc) :
    ∀ vs : List (QVecOver A cardX cardY cardAnc),
      qvListSum vs x y a = ampListSum (vs.map (fun v => v x y a))
  | [] => by rfl
  | v :: vs => by
    show add (v x y a) (qvListSum vs x y a) = add (v x y a) (ampListSum (vs.map (fun v => v x y a)))
    rw [qvListSum_apply x y a vs]

/-- Squared amplitude mass on one query value. -/
def queryWeightOver (ψ : QVecOver A cardX cardY cardAnc) (x : Fin cardX) : R :=
  ringSum cardY (fun y => ringSum cardAnc (fun a => normSq (ψ x y a)))

/-- Total squared norm. -/
def stateNormSqOver (ψ : QVecOver A cardX cardY cardAnc) : R :=
  ringSum cardX (fun x => queryWeightOver ψ x)

/-- Unnormalised Born mass of the event `S` on the query/output register. -/
def queryMassOnOver (S : Fin cardX → Bool) (ψ : QVecOver A cardX cardY cardAnc) : R :=
  ringSum cardX (fun x => if S x = true then queryWeightOver ψ x else zero)

theorem queryWeightOver_nonneg (ψ : QVecOver A cardX cardY cardAnc) (x : Fin cardX) :
    le zero (queryWeightOver ψ x) :=
  ringSum_nonneg (fun _ => ringSum_nonneg (fun _ => normSq_nonneg _))

theorem queryMassOnOver_nonneg (S : Fin cardX → Bool) (ψ : QVecOver A cardX cardY cardAnc) :
    le zero (queryMassOnOver S ψ) := by
  apply ringSum_nonneg
  intro x
  cases S x
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact le_refl _
  · simp only [↓reduceIte]
    exact queryWeightOver_nonneg ψ x

theorem queryMassOnOver_le_stateNormSqOver (S : Fin cardX → Bool)
    (ψ : QVecOver A cardX cardY cardAnc) : le (queryMassOnOver S ψ) (stateNormSqOver ψ) := by
  apply ringSum_le
  intro x
  cases S x
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact queryWeightOver_nonneg ψ x
  · simp only [↓reduceIte]
    exact le_refl _

theorem qvNeg_normSq (ψ : QVecOver A cardX cardY cardAnc) :
    stateNormSqOver (qvNeg ψ) = stateNormSqOver ψ := by
  unfold stateNormSqOver queryWeightOver qvNeg
  apply ringSum_congr; intro x
  apply ringSum_congr; intro y
  apply ringSum_congr; intro a
  exact normSq_neg _

/-- The query gate `|x, y, a⟩ ↦ |x, G_{H x}(y), a⟩` of a classical oracle `H`. -/
def oracleGate {Y : Type} (G : ResponseGate Y cardY) (H : Fin cardX → Y)
    (ψ : QVecOver A cardX cardY cardAnc) : QVecOver A cardX cardY cardAnc :=
  fun x y a => ψ x (G.act (H x) y) a

theorem oracleGate_sub {Y : Type} (G : ResponseGate Y cardY) (H : Fin cardX → Y)
    (ψ φ : QVecOver A cardX cardY cardAnc) :
    oracleGate G H (qvSub ψ φ) = qvSub (oracleGate G H ψ) (oracleGate G H φ) := by rfl

theorem oracleGate_queryWeight {Y : Type} (G : ResponseGate Y cardY) (H : Fin cardX → Y)
    (ψ : QVecOver A cardX cardY cardAnc) (x : Fin cardX) :
    queryWeightOver (oracleGate G H ψ) x = queryWeightOver ψ x :=
  ringSum_bijection (G.act (H x)) (G.actInv (H x)) (G.left_inv _) (G.right_inv _)
    (fun y => ringSum cardAnc (fun a => normSq (ψ x y a)))

/-- Every oracle gate is an exact isometry. -/
theorem oracleGate_isometry {Y : Type} (G : ResponseGate Y cardY) (H : Fin cardX → Y)
    (ψ : QVecOver A cardX cardY cardAnc) :
    stateNormSqOver (oracleGate G H ψ) = stateNormSqOver ψ :=
  ringSum_congr (oracleGate_queryWeight G H ψ)

/-- Projection onto one query value. -/
def projSingleOver (xStar : Fin cardX) (ψ : QVecOver A cardX cardY cardAnc) :
    QVecOver A cardX cardY cardAnc :=
  fun x y a => if x = xStar then ψ x y a else zero

theorem projSingleOver_normSq (xStar : Fin cardX) (ψ : QVecOver A cardX cardY cardAnc) :
    stateNormSqOver (projSingleOver xStar ψ) = queryWeightOver ψ xStar := by
  have hPt : ∀ x : Fin cardX, queryWeightOver (projSingleOver xStar ψ) x =
      if x = xStar then queryWeightOver ψ xStar else zero := by
    intro x
    by_cases hx : x = xStar
    · subst hx
      simp only [queryWeightOver, projSingleOver, ↓reduceIte]
    · simp only [queryWeightOver, projSingleOver, hx, ↓reduceIte]
      have h0 : ∀ y : Fin cardY, ringSum cardAnc (fun _ => normSq (zero : A)) = (zero : R) := by
        intro _
        rw [ringSum_congr (fun _ => normSq_zero), ringSum_zero]
      rw [ringSum_congr h0, ringSum_zero]
  unfold stateNormSqOver
  rw [ringSum_congr hPt, ringSum_ite_eq]

/-- Two oracles that agree away from `xStar` act identically except on the `xStar` component. -/
theorem oracleGate_diff_localizes {Y : Type} (G : ResponseGate Y cardY)
    (H H' : Fin cardX → Y) (xStar : Fin cardX) (hAgree : ∀ x, x ≠ xStar → H' x = H x)
    (ψ : QVecOver A cardX cardY cardAnc) :
    qvSub (oracleGate G H' ψ) (oracleGate G H ψ) =
      qvSub (oracleGate G H' (projSingleOver xStar ψ)) (oracleGate G H (projSingleOver xStar ψ)) := by
  funext x y a
  by_cases hx : x = xStar
  · subst hx
    simp only [qvSub, oracleGate, projSingleOver, ↓reduceIte]
  · simp only [qvSub, oracleGate, projSingleOver, hx, ↓reduceIte, hAgree x hx]
    rw [LawfulCommRing.sub_self, LawfulCommRing.sub_self]

/-- A difference-preserving operator that scales every squared norm by `scaleSq`. Exact
    unitaries have `scaleSq = 1`; over `ℚ[i]` or `ℚ[√2, i]` every rational or Clifford+T circuit
    is one. -/
structure ScaledUnitaryOver (R A : Type) [OrderedCommRing R] [ConstructiveAmplitudeRing R A]
    (cardX cardY cardAnc : Nat) where
  apply : QVecOver A cardX cardY cardAnc → QVecOver A cardX cardY cardAnc
  scaleSq : R
  map_sub : ∀ ψ φ, apply (qvSub ψ φ) = qvSub (apply ψ) (apply φ)
  normSq_eq : ∀ ψ, stateNormSqOver (apply ψ) = mul scaleSq (stateNormSqOver ψ)

/-- Multiplication of every amplitude by `u`; an exact unitary when `normSq u = 1`. -/
def ScaledUnitaryOver.phase (u : A) : ScaledUnitaryOver R A cardX cardY cardAnc where
  apply ψ := fun x y a => mul u (ψ x y a)
  scaleSq := normSq u
  map_sub ψ φ := by
    funext x y a
    show mul u (sub (ψ x y a) (φ x y a)) = sub (mul u (ψ x y a)) (mul u (φ x y a))
    constructive_ring
  normSq_eq ψ := by
    unfold stateNormSqOver queryWeightOver
    rw [← ringSum_mul_left]
    apply ringSum_congr; intro x
    rw [← ringSum_mul_left]
    apply ringSum_congr; intro y
    rw [← ringSum_mul_left]
    apply ringSum_congr; intro a
    exact normSq_mul u _

/-- A `Q`-query adversary: an initial state and `Q` layers, each applied after an oracle
    query. `Q` is `steps.length`. -/
structure QuantumAdvOver (R A : Type) [OrderedCommRing R] [ConstructiveAmplitudeRing R A]
    (cardX cardY cardAnc : Nat) where
  init : QVecOver A cardX cardY cardAnc
  steps : List (ScaledUnitaryOver R A cardX cardY cardAnc)

/-- Query, apply a layer, repeat. -/
def runStepsOver {Y : Type} (G : ResponseGate Y cardY) (H : Fin cardX → Y) :
    List (ScaledUnitaryOver R A cardX cardY cardAnc) →
      QVecOver A cardX cardY cardAnc → QVecOver A cardX cardY cardAnc
  | [], ψ => ψ
  | U :: rest, ψ => runStepsOver G H rest (U.apply (oracleGate G H ψ))

/-- The final state of the adversary against the oracle `H`. -/
def runQuantumAdvOver {Y : Type} (G : ResponseGate Y cardY)
    (Adv : QuantumAdvOver R A cardX cardY cardAnc) (H : Fin cardX → Y) :
    QVecOver A cardX cardY cardAnc :=
  runStepsOver G H Adv.steps Adv.init

/-- The product of the squared-norm scales of a list of layers. -/
def stepsScaleOver : List (ScaledUnitaryOver R A cardX cardY cardAnc) → R
  | [] => one
  | U :: rest => mul U.scaleSq (stepsScaleOver rest)

theorem runStepsOver_sub {Y : Type} (G : ResponseGate Y cardY) (H : Fin cardX → Y) :
    ∀ (steps : List (ScaledUnitaryOver R A cardX cardY cardAnc))
      (ψ φ : QVecOver A cardX cardY cardAnc),
      runStepsOver G H steps (qvSub ψ φ) =
        qvSub (runStepsOver G H steps ψ) (runStepsOver G H steps φ)
  | [], _, _ => by rfl
  | U :: rest, ψ, φ => by
    show runStepsOver G H rest (U.apply (oracleGate G H (qvSub ψ φ))) =
      qvSub (runStepsOver G H rest (U.apply (oracleGate G H ψ)))
        (runStepsOver G H rest (U.apply (oracleGate G H φ)))
    rw [oracleGate_sub, U.map_sub, runStepsOver_sub G H rest]

/-- The norm of the final state does not depend on the oracle. -/
theorem runStepsOver_normSq {Y : Type} (G : ResponseGate Y cardY) (H : Fin cardX → Y) :
    ∀ (steps : List (ScaledUnitaryOver R A cardX cardY cardAnc))
      (ψ : QVecOver A cardX cardY cardAnc),
      stateNormSqOver (runStepsOver G H steps ψ) =
        mul (stepsScaleOver steps) (stateNormSqOver ψ)
  | [], ψ => (LawfulCommRing.one_mul _).symm
  | U :: rest, ψ => by
    show stateNormSqOver (runStepsOver G H rest (U.apply (oracleGate G H ψ))) =
      mul (mul U.scaleSq (stepsScaleOver rest)) (stateNormSqOver ψ)
    rw [runStepsOver_normSq G H rest, U.normSq_eq, oracleGate_isometry]
    constructive_ring

theorem runQuantumAdvOver_normSq {Y : Type} (G : ResponseGate Y cardY)
    (Adv : QuantumAdvOver R A cardX cardY cardAnc) (H : Fin cardX → Y) :
    stateNormSqOver (runQuantumAdvOver G Adv H) =
      mul (stepsScaleOver Adv.steps) (stateNormSqOver Adv.init) :=
  runStepsOver_normSq G H Adv.steps Adv.init

/-! ## 5. Measure-and-reprogram over an arbitrary amplitude ring -/

/-- The `2Q + 1` branches of the reprogrammed run: for every query, the reprogrammed and the
    original oracle applied to the `xStar` component of the unreprogrammed state and continued
    with the reprogrammed oracle; and last the unreprogrammed run itself. -/
def dfmBranchesOver {Y : Type} (G : ResponseGate Y cardY) (H H' : Fin cardX → Y)
    (xStar : Fin cardX) :
    List (ScaledUnitaryOver R A cardX cardY cardAnc) → QVecOver A cardX cardY cardAnc →
      List (QVecOver A cardX cardY cardAnc)
  | [], ψ => [ψ]
  | U :: rest, ψ =>
    runStepsOver G H' rest (U.apply (oracleGate G H' (projSingleOver xStar ψ))) ::
    qvNeg (runStepsOver G H' rest (U.apply (oracleGate G H (projSingleOver xStar ψ)))) ::
    dfmBranchesOver G H H' xStar rest (U.apply (oracleGate G H ψ))

/-- The number of branches, `2Q + 1`, by structural recursion. -/
def dfmCount {α : Type} : List α → Nat
  | [] => 1
  | _ :: rest => dfmCount rest + 2

theorem dfmCount_eq {α : Type} : ∀ l : List α, dfmCount l = 2 * l.length + 1
  | [] => by rfl
  | _ :: rest => by
    show dfmCount rest + 2 = 2 * (rest.length + 1) + 1
    rw [dfmCount_eq rest, Nat.mul_succ]

theorem dfmBranchesOver_length {Y : Type} (G : ResponseGate Y cardY) (H H' : Fin cardX → Y)
    (xStar : Fin cardX) :
    ∀ (steps : List (ScaledUnitaryOver R A cardX cardY cardAnc))
      (ψ : QVecOver A cardX cardY cardAnc),
      (dfmBranchesOver G H H' xStar steps ψ).length = dfmCount steps
  | [], _ => by rfl
  | U :: rest, ψ => by
    show (dfmBranchesOver G H H' xStar rest (U.apply (oracleGate G H ψ))).length + 1 + 1 =
      dfmCount rest + 2
    rw [dfmBranchesOver_length G H H' xStar rest]

private theorem add_neg_add_of_sub_eq {p q r s : A} (h : sub p q = sub r s) :
    add r (add (neg s) q) = p := by
  have e : p = add (sub p q) q := by constructive_ring
  rw [e, h]
  constructive_ring

/-- **Branch decomposition.** If `H'` agrees with `H` away from `xStar`, the run against `H'`
    is the sum of the `2Q + 1` branches. -/
theorem dfmBranchesOver_sum {Y : Type} (G : ResponseGate Y cardY) (H H' : Fin cardX → Y)
    (xStar : Fin cardX) (hAgree : ∀ x, x ≠ xStar → H' x = H x) :
    ∀ (steps : List (ScaledUnitaryOver R A cardX cardY cardAnc))
      (ψ : QVecOver A cardX cardY cardAnc),
      qvListSum (dfmBranchesOver G H H' xStar steps ψ) = runStepsOver G H' steps ψ
  | [], ψ => by
    funext x y a
    show add (ψ x y a) zero = ψ x y a
    exact LawfulCommRing.add_zero _
  | U :: rest, ψ => by
    have ih := dfmBranchesOver_sum G H H' xStar hAgree rest (U.apply (oracleGate G H ψ))
    have hlin : qvSub (runStepsOver G H' rest (U.apply (oracleGate G H' ψ)))
        (runStepsOver G H' rest (U.apply (oracleGate G H ψ))) =
        qvSub (runStepsOver G H' rest (U.apply (oracleGate G H' (projSingleOver xStar ψ))))
          (runStepsOver G H' rest (U.apply (oracleGate G H (projSingleOver xStar ψ)))) := by
      rw [← runStepsOver_sub, ← U.map_sub, oracleGate_diff_localizes G H H' xStar hAgree ψ,
        U.map_sub, runStepsOver_sub]
    funext x y a
    have h := congrFun (congrFun (congrFun hlin x) y) a
    show add (runStepsOver G H' rest (U.apply (oracleGate G H' (projSingleOver xStar ψ))) x y a)
        (add (neg (runStepsOver G H' rest (U.apply (oracleGate G H (projSingleOver xStar ψ))) x y a))
          (qvListSum (dfmBranchesOver G H H' xStar rest (U.apply (oracleGate G H ψ))) x y a)) =
      runStepsOver G H' rest (U.apply (oracleGate G H' ψ)) x y a
    rw [ih]
    exact add_neg_add_of_sub_eq h

/-- Event mass of a sum of `m` states is at most `m` times the sum of their event masses. -/
theorem queryMassOnOver_qvListSum_le (T : Fin cardX → Bool)
    (vs : List (QVecOver A cardX cardY cardAnc)) :
    le (queryMassOnOver T (qvListSum vs))
      (mul (natCastR vs.length) (ampListSum (vs.map (queryMassOnOver T)))) := by
  have hW : ∀ x : Fin cardX, le (queryWeightOver (qvListSum vs) x)
      (mul (natCastR vs.length) (ampListSum (vs.map (fun v => queryWeightOver v x)))) := by
    intro x
    have hPt : le (queryWeightOver (qvListSum vs) x)
        (ringSum cardY (fun y => ringSum cardAnc (fun a =>
          mul (natCastR vs.length) (ampListSum (vs.map (fun v => normSq (v x y a))))))) := by
      apply ringSum_le; intro y
      apply ringSum_le; intro a
      rw [qvListSum_apply]
      exact normSq_ampListSum_map_le (fun v => v x y a) vs
    have hEq : ringSum cardY (fun y => ringSum cardAnc (fun a =>
          mul (natCastR vs.length) (ampListSum (vs.map (fun v => normSq (v x y a)))))) =
        mul (natCastR vs.length) (ampListSum (vs.map (fun v => queryWeightOver v x))) := by
      have hA : ∀ y : Fin cardY, ringSum cardAnc (fun a =>
          mul (natCastR vs.length) (ampListSum (vs.map (fun v => normSq (v x y a))))) =
          mul (natCastR vs.length)
            (ampListSum (vs.map (fun v => ringSum cardAnc (fun a => normSq (v x y a))))) := by
        intro y
        rw [ringSum_mul_left, ringSum_ampListSum cardAnc (fun v a => normSq (v x y a)) vs]
      rw [ringSum_congr hA, ringSum_mul_left,
        ringSum_ampListSum cardY (fun v y => ringSum cardAnc (fun a => normSq (v x y a))) vs]
      rfl
    rw [hEq] at hPt
    exact hPt
  have hX : le (queryMassOnOver T (qvListSum vs))
      (ringSum cardX (fun x => mul (natCastR vs.length)
        (ampListSum (vs.map (fun v => if T x = true then queryWeightOver v x else zero))))) := by
    apply ringSum_le
    intro x
    cases T x
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ampListSum_map_zero, LawfulCommRing.mul_zero]
      exact le_refl _
    · simp only [↓reduceIte]
      exact hW x
  rw [ringSum_mul_left, ringSum_ampListSum cardX
    (fun v x => if T x = true then queryWeightOver v x else zero) vs] at hX
  exact hX

/-- Challenge-independent envelope: twice the scaled mass that each intermediate state of the
    unreprogrammed run puts on `xStar`, plus the event mass of the unreprogrammed output. -/
def dfmEnvelopeOver {Y : Type} (G : ResponseGate Y cardY) (H : Fin cardX → Y)
    (xStar : Fin cardX) (T : Fin cardX → Bool) :
    List (ScaledUnitaryOver R A cardX cardY cardAnc) → QVecOver A cardX cardY cardAnc → R
  | [], ψ => queryMassOnOver T ψ
  | U :: rest, ψ =>
    add (add (mul (stepsScaleOver (U :: rest)) (queryWeightOver ψ xStar))
        (mul (stepsScaleOver (U :: rest)) (queryWeightOver ψ xStar)))
      (dfmEnvelopeOver G H xStar T rest (U.apply (oracleGate G H ψ)))

theorem branch_mass_le {Y : Type} (G : ResponseGate Y cardY) (H₁ H₂ : Fin cardX → Y)
    (xStar : Fin cardX) (T : Fin cardX → Bool) (U : ScaledUnitaryOver R A cardX cardY cardAnc)
    (rest : List (ScaledUnitaryOver R A cardX cardY cardAnc))
    (ψ : QVecOver A cardX cardY cardAnc) :
    le (queryMassOnOver T
        (runStepsOver G H₁ rest (U.apply (oracleGate G H₂ (projSingleOver xStar ψ)))))
      (mul (stepsScaleOver (U :: rest)) (queryWeightOver ψ xStar)) := by
  have h := queryMassOnOver_le_stateNormSqOver T
    (runStepsOver G H₁ rest (U.apply (oracleGate G H₂ (projSingleOver xStar ψ))))
  rw [runStepsOver_normSq, U.normSq_eq, oracleGate_isometry, projSingleOver_normSq] at h
  have e : mul (stepsScaleOver rest) (mul U.scaleSq (queryWeightOver ψ xStar)) =
      mul (mul U.scaleSq (stepsScaleOver rest)) (queryWeightOver ψ xStar) := by constructive_ring
  rw [e] at h
  exact h

theorem dfmEnvelopeOver_nonneg {Y : Type} (G : ResponseGate Y cardY) (H : Fin cardX → Y)
    (xStar : Fin cardX) (T : Fin cardX → Bool) :
    ∀ (steps : List (ScaledUnitaryOver R A cardX cardY cardAnc))
      (ψ : QVecOver A cardX cardY cardAnc), le zero (dfmEnvelopeOver G H xStar T steps ψ)
  | [], ψ => queryMassOnOver_nonneg T ψ
  | U :: rest, ψ => by
    have hb := le_trans (queryMassOnOver_nonneg T _) (branch_mass_le G H H xStar T U rest ψ)
    exact add_nonneg (add_nonneg hb hb) (dfmEnvelopeOver_nonneg G H xStar T rest _)

theorem dfmBranchesOver_mass_le {Y : Type} (G : ResponseGate Y cardY) (H H' : Fin cardX → Y)
    (xStar : Fin cardX) (T : Fin cardX → Bool) :
    ∀ (steps : List (ScaledUnitaryOver R A cardX cardY cardAnc))
      (ψ : QVecOver A cardX cardY cardAnc),
      le (ampListSum ((dfmBranchesOver G H H' xStar steps ψ).map (queryMassOnOver T)))
        (dfmEnvelopeOver G H xStar T steps ψ)
  | [], ψ => by
    show le (add (queryMassOnOver T ψ) zero) (queryMassOnOver T ψ)
    rw [LawfulCommRing.add_zero]
    exact le_refl _
  | U :: rest, ψ => by
    have ih := dfmBranchesOver_mass_le G H H' xStar T rest (U.apply (oracleGate G H ψ))
    have h1 := branch_mass_le G H' H' xStar T U rest ψ
    have h2 := branch_mass_le G H' H xStar T U rest ψ
    have hneg : queryMassOnOver T
        (qvNeg (runStepsOver G H' rest (U.apply (oracleGate G H (projSingleOver xStar ψ))))) =
        queryMassOnOver T
          (runStepsOver G H' rest (U.apply (oracleGate G H (projSingleOver xStar ψ)))) := by
      unfold queryMassOnOver queryWeightOver qvNeg
      apply ringSum_congr; intro x
      cases T x
      · rfl
      · simp only [↓reduceIte]
        apply ringSum_congr; intro y
        apply ringSum_congr; intro a
        exact normSq_neg _
    show le (add (queryMassOnOver T
          (runStepsOver G H' rest (U.apply (oracleGate G H' (projSingleOver xStar ψ)))))
        (add (queryMassOnOver T
            (qvNeg (runStepsOver G H' rest (U.apply (oracleGate G H (projSingleOver xStar ψ))))))
          (ampListSum ((dfmBranchesOver G H H' xStar rest (U.apply (oracleGate G H ψ))).map
            (queryMassOnOver T)))))
      (add (add (mul (stepsScaleOver (U :: rest)) (queryWeightOver ψ xStar))
          (mul (stepsScaleOver (U :: rest)) (queryWeightOver ψ xStar)))
        (dfmEnvelopeOver G H xStar T rest (U.apply (oracleGate G H ψ))))
    rw [hneg, ← LawfulCommRing.add_assoc]
    exact add_le_add (add_le_add h1 h2) ih

/-- **Reprogramming one point costs a factor `2Q + 1` against the envelope**, for every
    challenge value and every output event. -/
theorem queryMassOnOver_reprogram_le {Y : Type} (G : ResponseGate Y cardY)
    (H H' : Fin cardX → Y) (xStar : Fin cardX) (hAgree : ∀ x, x ≠ xStar → H' x = H x)
    (T : Fin cardX → Bool) (steps : List (ScaledUnitaryOver R A cardX cardY cardAnc))
    (ψ : QVecOver A cardX cardY cardAnc) :
    le (queryMassOnOver T (runStepsOver G H' steps ψ))
      (mul (natCastR (dfmCount steps)) (dfmEnvelopeOver G H xStar T steps ψ)) := by
  rw [← dfmBranchesOver_sum G H H' xStar hAgree steps ψ]
  have h1 := queryMassOnOver_qvListSum_le T (dfmBranchesOver G H H' xStar steps ψ)
  rw [dfmBranchesOver_length] at h1
  exact le_trans h1 (mul_le_mul_of_nonneg_left (dfmBranchesOver_mass_le G H H' xStar T steps ψ)
    (natCastR_nonneg (amplitude_one_nonneg A) _))

theorem queryMassOnOver_fiber_sum (proj : Fin cardX → Fin cardX)
    (ψ : QVecOver A cardX cardY cardAnc) :
    ringSum cardX (fun xStar => queryMassOnOver (fun x => decide (xStar = proj x)) ψ) =
      stateNormSqOver ψ := by
  unfold queryMassOnOver stateNormSqOver
  rw [ringSum_comm]
  apply ringSum_congr
  intro x
  have h : ringSum cardX (fun xs =>
      if decide (xs = proj x) = true then queryWeightOver ψ x else zero) =
      ringSum cardX (fun xs => if xs = proj x then queryWeightOver ψ x else zero) := by
    apply ringSum_congr
    intro xs
    simp only [decide_eq_true_eq]
  rw [h, ringSum_ite_eq]

/-- Summed over the reprogrammed point, with the disjoint output events `proj x = xStar`, the
    envelopes add up to `(2Q + 1) ‖ψ_final‖²`. -/
theorem dfmEnvelopeOver_fiber_sum {Y : Type} (G : ResponseGate Y cardY) (H : Fin cardX → Y)
    (proj : Fin cardX → Fin cardX) :
    ∀ (steps : List (ScaledUnitaryOver R A cardX cardY cardAnc))
      (ψ : QVecOver A cardX cardY cardAnc),
      ringSum cardX (fun xStar =>
        dfmEnvelopeOver G H xStar (fun x => decide (xStar = proj x)) steps ψ) =
        mul (natCastR (dfmCount steps)) (stateNormSqOver (runStepsOver G H steps ψ))
  | [], ψ => by
    show ringSum cardX (fun xStar => queryMassOnOver (fun x => decide (xStar = proj x)) ψ) =
      mul (add zero one) (stateNormSqOver ψ)
    rw [queryMassOnOver_fiber_sum]
    constructive_ring
  | U :: rest, ψ => by
    have ih := dfmEnvelopeOver_fiber_sum G H proj rest (U.apply (oracleGate G H ψ))
    have hN := runStepsOver_normSq G H (U :: rest) ψ
    show ringSum cardX (fun xStar =>
        add (add (mul (stepsScaleOver (U :: rest)) (queryWeightOver ψ xStar))
            (mul (stepsScaleOver (U :: rest)) (queryWeightOver ψ xStar)))
          (dfmEnvelopeOver G H xStar (fun x => decide (xStar = proj x)) rest
            (U.apply (oracleGate G H ψ)))) =
      mul (add (add (natCastR (dfmCount rest)) one) one)
        (stateNormSqOver (runStepsOver G H rest (U.apply (oracleGate G H ψ))))
    rw [ringSum_add, ringSum_add, ringSum_mul_left, ih]
    have hN' : mul (stepsScaleOver (U :: rest)) (ringSum cardX (fun x => queryWeightOver ψ x)) =
        stateNormSqOver (runStepsOver G H rest (U.apply (oracleGate G H ψ))) := hN.symm
    rw [hN']
    constructive_ring

/-- **Projected measure-and-reprogram round-by-round step over any amplitude ring.**

    `Adv` is an arbitrary adversary with amplitudes in `A` making `Q = Adv.steps.length`
    superposition queries through any response gate `G`; `H` is any background oracle;
    `chal : Fin cardC → Y` lists the challenge values; `proj` maps the adversary's output to the
    query point it must be consistent with. If every doomed point has at most `badCard`
    challenge indices that flip it to live, then the Born mass of outputs whose projected point
    is doomed and was reprogrammed to a flipping challenge, summed over points and challenge
    indices, is at most `(2Q + 1)² · badCard · ‖ψ_final‖²`.

    Dividing by `cardC · ‖ψ_final‖²` gives the probability bound `(2Q + 1)² · badCard / cardC`
    for a uniformly random challenge; the statement is cross-multiplied so that it needs no
    division, and the adversary may use any exact unitaries over `A`. -/
theorem qrom_measure_reprogram_rbr_step_over {Y : Type} (G : ResponseGate Y cardY)
    (Adv : QuantumAdvOver R A cardX cardY cardAnc) (H : Fin cardX → Y)
    (proj : Fin cardX → Fin cardX) {cardC : Nat} (chal : Fin cardC → Y)
    (isDoomed : Fin cardX → Bool) (flipsToLive : Fin cardX → Fin cardC → Bool) (badCard : Nat)
    (hRbr : ∀ x : Fin cardX, isDoomed x = true → finCountTrue cardC (flipsToLive x) ≤ badCard) :
    le (ringSum cardX (fun xStar =>
        if isDoomed xStar = true then
          ringSum cardC (fun j =>
            if flipsToLive xStar j = true then
              queryMassOnOver (fun x => decide (xStar = proj x))
                (runQuantumAdvOver G Adv (pointUpdate H xStar (chal j)))
            else zero)
        else zero))
      (mul (natCastR ((2 * Adv.steps.length + 1) ^ 2 * badCard))
        (stateNormSqOver (runQuantumAdvOver G Adv H))) := by
  have h1nn : le (zero : R) one := amplitude_one_nonneg A
  have hc : le (zero : R) (natCastR (dfmCount Adv.steps)) := natCastR_nonneg h1nn _
  have hPer : ∀ xStar : Fin cardX,
      le (if isDoomed xStar = true then
          ringSum cardC (fun j =>
            if flipsToLive xStar j = true then
              queryMassOnOver (fun x => decide (xStar = proj x))
                (runQuantumAdvOver G Adv (pointUpdate H xStar (chal j)))
            else zero)
        else zero)
        (mul (natCastR badCard) (mul (natCastR (dfmCount Adv.steps))
          (dfmEnvelopeOver G H xStar (fun x => decide (xStar = proj x)) Adv.steps Adv.init))) := by
    intro xStar
    have hEnv := dfmEnvelopeOver_nonneg G H xStar (fun x => decide (xStar = proj x))
      Adv.steps Adv.init
    cases hD : isDoomed xStar
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact mul_nonneg (natCastR_nonneg h1nn _) (mul_nonneg hc hEnv)
    · simp only [↓reduceIte]
      have hIn : le (ringSum cardC (fun j =>
            if flipsToLive xStar j = true then
              queryMassOnOver (fun x => decide (xStar = proj x))
                (runQuantumAdvOver G Adv (pointUpdate H xStar (chal j)))
            else zero))
          (ringSum cardC (fun j =>
            if flipsToLive xStar j = true then
              mul (natCastR (dfmCount Adv.steps))
                (dfmEnvelopeOver G H xStar (fun x => decide (xStar = proj x)) Adv.steps Adv.init)
            else zero)) := by
        apply ringSum_le
        intro j
        cases flipsToLive xStar j
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact le_refl _
        · simp only [↓reduceIte]
          exact queryMassOnOver_reprogram_le G H (pointUpdate H xStar (chal j)) xStar
            (fun x hx => by unfold pointUpdate; rw [ite_eq_right hx]) _ Adv.steps Adv.init
      rw [ringSum_indicator_mul] at hIn
      exact le_trans hIn (mul_le_mul_of_nonneg_right (natCastR_le h1nn (hRbr xStar hD))
        (mul_nonneg hc hEnv))
  have hSum := ringSum_le hPer
  rw [ringSum_mul_left, ringSum_mul_left, dfmEnvelopeOver_fiber_sum] at hSum
  have hScalar : (natCastR ((2 * Adv.steps.length + 1) ^ 2 * badCard) : R) =
      mul (natCastR badCard) (mul (natCastR (dfmCount Adv.steps)) (natCastR (dfmCount Adv.steps))) := by
    rw [dfmCount_eq, Nat.pow_two, natCastR_mul, natCastR_mul]
    constructive_ring
  have hFinal : mul (natCastR badCard) (mul (natCastR (dfmCount Adv.steps))
      (mul (natCastR (dfmCount Adv.steps)) (stateNormSqOver (runStepsOver G H Adv.steps Adv.init)))) =
      mul (natCastR ((2 * Adv.steps.length + 1) ^ 2 * badCard))
        (stateNormSqOver (runQuantumAdvOver G Adv H)) := by
    rw [hScalar]
    show _ = mul _ (stateNormSqOver (runStepsOver G H Adv.steps Adv.init))
    constructive_ring
  rw [hFinal] at hSum
  exact hSum

/-- The unprojected step: the output register is the reprogrammed point itself. -/
theorem qrom_measure_reprogram_rbr_step_over_point {Y : Type} (G : ResponseGate Y cardY)
    (Adv : QuantumAdvOver R A cardX cardY cardAnc) (H : Fin cardX → Y)
    {cardC : Nat} (chal : Fin cardC → Y)
    (isDoomed : Fin cardX → Bool) (flipsToLive : Fin cardX → Fin cardC → Bool) (badCard : Nat)
    (hRbr : ∀ x : Fin cardX, isDoomed x = true → finCountTrue cardC (flipsToLive x) ≤ badCard) :
    le (ringSum cardX (fun xStar =>
        if isDoomed xStar = true then
          ringSum cardC (fun j =>
            if flipsToLive xStar j = true then
              queryWeightOver (runQuantumAdvOver G Adv (pointUpdate H xStar (chal j))) xStar
            else zero)
        else zero))
      (mul (natCastR ((2 * Adv.steps.length + 1) ^ 2 * badCard))
        (stateNormSqOver (runQuantumAdvOver G Adv H))) := by
  have hPoint : ∀ (ψ : QVecOver A cardX cardY cardAnc) (xStar : Fin cardX),
      queryMassOnOver (fun x => decide (xStar = x)) ψ = queryWeightOver ψ xStar := by
    intro ψ xStar
    unfold queryMassOnOver
    have hEq : ringSum cardX (fun x =>
        if decide (xStar = x) = true then queryWeightOver ψ x else zero) =
        ringSum cardX (fun x => if x = xStar then queryWeightOver ψ xStar else zero) := by
      apply ringSum_congr
      intro x
      by_cases hx : x = xStar
      · subst hx
        simp only [decide_true, ↓reduceIte]
      · have hx' : ¬ xStar = x := fun h => hx h.symm
        simp only [hx, hx', decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [hEq, ringSum_ite_eq]
  have h := qrom_measure_reprogram_rbr_step_over G Adv H id chal isDoomed flipsToLive badCard hRbr
  refine le_trans (le_of_eq ?_) h
  apply ringSum_congr
  intro xStar
  cases isDoomed xStar
  · rfl
  · simp only [↓reduceIte]
    apply ringSum_congr
    intro j
    cases flipsToLive xStar j
    · rfl
    · simp only [↓reduceIte]
      exact (hPoint _ xStar).symm

end QueryRegister

#verify_constructive
  Qsag.ringSum_bijection
  Qsag.ringSum_eq_zero_of_nonneg
  Qsag.amplitude_one_nonneg
  Qsag.hvInner_self
  Qsag.normSqVec_eq_zero
  Qsag.lagrange_identity
  Qsag.cauchy_schwarz_normSq
  Qsag.OrthoProjector.inner_complement
  Qsag.OrthoProjector.pythagoras
  Qsag.matVec_inner
  Qsag.matVec_normSq
  Qsag.list_sum_of_squares_identity
  Qsag.normSq_ampListSum_le
  Qsag.oracleGate_isometry
  Qsag.oracleGate_diff_localizes
  Qsag.runQuantumAdvOver_normSq
  Qsag.dfmBranchesOver_sum
  Qsag.queryMassOnOver_qvListSum_le
  Qsag.queryMassOnOver_reprogram_le
  Qsag.dfmEnvelopeOver_fiber_sum
  Qsag.qrom_measure_reprogram_rbr_step_over
  Qsag.qrom_measure_reprogram_rbr_step_over_point

end Qsag
end

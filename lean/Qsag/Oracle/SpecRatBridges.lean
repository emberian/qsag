module
/-
# Qsag.Oracle.SpecRatBridges — Conversions Between `Spec.RatBound` and the Library Rationals

`Qsag.Spec.RatBound` (Layer 0) is the canonical non-negative rational bound. This module sits
above both sides and gives the lossless, order-preserving conversions to
1. the `(num, den)` pairs compared by `Qsag.ratLe` in the QROM games (`Qsag.Oracle.Qrom`), and
2. the signed `Qsag.ExactRat` of the lattice library (`Qsag.Math.Lattices`).
-/

public import Qsag.Spec.Primitives
public import Qsag.Math.Lattices
public import Qsag.Oracle.Qrom
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spec

set_option autoImplicit false

/-- Lossless pair projection to `UcGames` `(num, den)` carrier. -/
def RatBound.toUcPair (r : RatBound) : Nat × Nat :=
  (r.num, r.den)

/-- Lift a certified positive-denominator `UcGames` pair `(num, den)` into `Spec.RatBound`. -/
def RatBound.ofUcPair (p : Nat × Nat) (hp : 0 < p.2) : RatBound :=
  ⟨p.1, p.2, hp⟩

/-- Equivalence between `Spec.RatBound.le` and `UcGames.ratLe`. -/
theorem RatBound.le_iff_ucRatLe (r₁ r₂ : RatBound) :
    r₁.le r₂ ↔ Qsag.ratLe r₁.toUcPair r₂.toUcPair := by
  unfold RatBound.le Qsag.ratLe RatBound.toUcPair
  dsimp only
  exact ⟨fun h => ⟨r₁.den_pos, r₂.den_pos, h⟩, fun ⟨_, _, h⟩ => h⟩

theorem RatBound.ucRatLe_iff_ofUcPair_le {p₁ p₂ : Nat × Nat}
    (hp₁ : 0 < p₁.2) (hp₂ : 0 < p₂.2) :
    Qsag.ratLe p₁ p₂ ↔ (RatBound.ofUcPair p₁ hp₁).le (RatBound.ofUcPair p₂ hp₂) := by
  unfold Qsag.ratLe RatBound.le RatBound.ofUcPair
  dsimp only
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hp₁, hp₂, h⟩⟩

/-- Order-preserving embedding into signed `Qsag.ExactRat` (`GaussianHvzkAndDualLpn`). -/
def RatBound.toExactRat (r : RatBound) : Qsag.ExactRat :=
  ⟨(r.num : Int), r.den, r.den_pos⟩

/-- Magnitude projection from signed `Qsag.ExactRat` (`|x.num| / x.den`) into `Spec.RatBound`. -/
def RatBound.ofExactRatAbs (x : Qsag.ExactRat) : RatBound :=
  ⟨x.num.natAbs, x.den, x.den_pos⟩

theorem RatBound.toExactRat_nonneg (r : RatBound) :
    0 ≤ (r.toExactRat).num :=
  Int.natCast_nonneg r.num

theorem RatBound.ofExactRatAbs_toExactRat (r : RatBound) :
    RatBound.ofExactRatAbs r.toExactRat = r := by
  cases r with
  | mk num den hpos =>
    unfold RatBound.ofExactRatAbs RatBound.toExactRat
    dsimp only
    rw [Int.natAbs_natCast]

theorem RatBound.toExactRat_ofNonneg {x : Qsag.ExactRat} (hx : 0 ≤ x.num) :
    (RatBound.ofExactRatAbs x).toExactRat = x := by
  cases x with
  | mk num den hpos =>
    dsimp only at hx
    unfold RatBound.ofExactRatAbs RatBound.toExactRat
    dsimp only
    exact congrArg (fun n => Qsag.ExactRat.mk n den hpos) (Int.natAbs_of_nonneg hx)

theorem RatBound.le_iff_toExactRat_le (r₁ r₂ : RatBound) :
    r₁.le r₂ ↔ Qsag.ExactRat.le r₁.toExactRat r₂.toExactRat := by
  unfold RatBound.le Qsag.ExactRat.le RatBound.toExactRat
  dsimp only
  rw [← Int.natCast_mul, ← Int.natCast_mul]
  exact Int.ofNat_le.symm

theorem RatBound.lt_iff_toExactRat_lt (r₁ r₂ : RatBound) :
    r₁.lt r₂ ↔ Qsag.ExactRat.lt r₁.toExactRat r₂.toExactRat := by
  unfold RatBound.lt Qsag.ExactRat.lt RatBound.toExactRat
  dsimp only
  rw [← Int.natCast_mul, ← Int.natCast_mul]
  exact Int.ofNat_lt.symm

theorem RatBound.exactRat_nonneg_le_iff {x y : Qsag.ExactRat}
    (hx : 0 ≤ x.num) (hy : 0 ≤ y.num) :
    (RatBound.ofExactRatAbs x).le (RatBound.ofExactRatAbs y) ↔
      Qsag.ExactRat.le x y := by
  rw [RatBound.le_iff_toExactRat_le, RatBound.toExactRat_ofNonneg hx,
      RatBound.toExactRat_ofNonneg hy]

/-- Non-negative clamping projection `max(0, x.num) / x.den` from `Qsag.ExactRat` into `Spec.RatBound`. -/
def RatBound.clampExactRat (x : Qsag.ExactRat) : RatBound :=
  ⟨x.num.toNat, x.den, x.den_pos⟩

/-- Any `Qsag.ExactRat` bounded by `ExactRat.twoNegPow b` maps under `clampExactRat` to `atLeastBits b`. -/
theorem RatBound.clampExactRat_atLeastBits_of_le_twoNegPow {x : Qsag.ExactRat} {b : Nat}
    (hLe : Qsag.ExactRat.le x (Qsag.ExactRat.twoNegPow b)) :
    (RatBound.clampExactRat x).atLeastBits b := by
  unfold Qsag.ExactRat.le Qsag.ExactRat.twoNegPow at hLe
  dsimp only at hLe
  unfold RatBound.atLeastBits RatBound.clampExactRat
  dsimp only
  by_cases hx : 0 ≤ x.num
  · have hEq : ((x.num.toNat : Nat) : Int) = x.num := Int.toNat_of_nonneg hx
    apply Int.ofNat_le.mp
    rw [Int.natCast_mul, hEq]
    omega
  · have hZero : x.num.toNat = 0 := Int.toNat_of_nonpos (by omega)
    rw [hZero, Nat.zero_mul]
    exact Nat.zero_le _

theorem RatBound.clampExactRat_strictlyMoreThanBits_of_lt_twoNegPow {x : Qsag.ExactRat} {b : Nat}
    (hLt : Qsag.ExactRat.lt x (Qsag.ExactRat.twoNegPow b)) :
    (RatBound.clampExactRat x).strictlyMoreThanBits b := by
  unfold Qsag.ExactRat.lt Qsag.ExactRat.twoNegPow at hLt
  dsimp only at hLt
  unfold RatBound.strictlyMoreThanBits RatBound.clampExactRat
  dsimp only
  have hPowPos : (0 : Int) < ((2 ^ b : Nat) : Int) := Int.ofNat_lt.mpr (Nat.two_pow_pos b)
  by_cases hx : 0 ≤ x.num
  · have hEq : ((x.num.toNat : Nat) : Int) = x.num := Int.toNat_of_nonneg hx
    apply Int.ofNat_lt.mp
    rw [Int.natCast_mul, hEq]
    omega
  · have hZero : x.num.toNat = 0 := Int.toNat_of_nonpos (by omega)
    rw [hZero, Nat.zero_mul]
    exact x.den_pos

#verify_constructive
  Qsag.Spec.RatBound.le_iff_ucRatLe
  Qsag.Spec.RatBound.ucRatLe_iff_ofUcPair_le
  Qsag.Spec.RatBound.ofExactRatAbs_toExactRat
  Qsag.Spec.RatBound.toExactRat_ofNonneg
  Qsag.Spec.RatBound.le_iff_toExactRat_le
  Qsag.Spec.RatBound.lt_iff_toExactRat_lt
  Qsag.Spec.RatBound.exactRat_nonneg_le_iff
  Qsag.Spec.RatBound.clampExactRat_atLeastBits_of_le_twoNegPow
  Qsag.Spec.RatBound.clampExactRat_strictlyMoreThanBits_of_lt_twoNegPow

end Qsag.Spec
end

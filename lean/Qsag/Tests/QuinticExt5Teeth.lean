module
public import Qsag.Math.QuinticExt5
/-
Teeth and known answers for the quintic extension field `Qsag.QuinticGoldilocks`
(`Qsag.Math.QuinticExt5`, the Lean twin of `Fp5` in `crates/qsag-agg/src/zk_hem/v2/field5.rs`).

* `tooth_reduction_two_has_zero_divisor`: the same schoolbook product with the reduction
  constant `2 = t^5` in place of `3` has the zero divisors `X - t` and
  `X^4 + t X^3 + t^2 X^2 + t^3 X + t^4`, so `mulWith_nonResidue_eq_zero` depends on `3` not
  being a fifth power.
* `tooth_two_is_fifth_power`: the fifth root `t` itself, against `nonResidue_not_fifth_power`.
* `tooth_frob_moves_xBasis`: `frob` is not the identity.
* `tooth_norm_vanishes_at_zero`, `tooth_ext5_zero_has_no_inverse`: the `z ≠ 0` hypotheses of
  `norm_ne_zero` and `ext5_mul_inv_cancel` are needed.
* `kat_mul_small`, `kat_square_small`, `kat_mul_wide`, `kat_inv_small`, `kat_inv_wide`,
  `kat_linear_factor_inverse`: products and inverses equal values computed independently in
  Python; they pin the Rust twin.
-/

public section
namespace Qsag
namespace QuinticExt5Teeth

set_option autoImplicit false

/-- `a0 + a1 X + a2 X^2 + a3 X^3 + a4 X^4` from canonical residues. -/
def q5 (a0 a1 a2 a3 a4 : Nat) : QuinticGoldilocks :=
  ⟨Goldilocks.ofNat a0, Goldilocks.ofNat a1, Goldilocks.ofNat a2, Goldilocks.ofNat a3,
    Goldilocks.ofNat a4⟩

/-! ## Known answers -/

theorem kat_mul_small :
    QuinticGoldilocks.mul (q5 1 2 3 4 5) (q5 6 7 8 9 10) = q5 348 337 295 220 110 := by
  decide +kernel

theorem kat_mul_wide :
    QuinticGoldilocks.mul
      (q5 81985529216486895 18364758544493064720 16045690984503098046 1089357896855742840
        1234605616436508552)
      (q5 9833440827789222417 1161981756646125696 11936128517019425370 841540910831230720
        9223372032559808513) =
    q5 5283752099695157823 16353582266922402083 1603729258236403860 4980090312857646783
      4444493412652145093 := by
  decide +kernel

theorem kat_square_small :
    QuinticGoldilocks.mul (q5 1 2 3 4 5) (q5 1 2 3 4 5) = q5 133 142 130 95 35 := by
  decide +kernel

private theorem mul_inv_small :
    QuinticGoldilocks.mul (q5 1 2 3 4 5)
      (q5 16227807958868272813 4552730750487813724 11612833514307017418 9161515214422980997
        13509202856671625680) = QuinticGoldilocks.one := by
  decide +kernel

private theorem mul_inv_wide :
    QuinticGoldilocks.mul
      (q5 81985529216486895 18364758544493064720 16045690984503098046 1089357896855742840
        1234605616436508552)
      (q5 17033286724174752684 16464919206864593009 3901309921467269908 17713944588012397749
        16392840534563784651) = QuinticGoldilocks.one := by
  decide +kernel

/-- `(1 + 2X + 3X^2 + 4X^3 + 5X^4)⁻¹`, through uniqueness of inverses. -/
theorem kat_inv_small :
    QuinticGoldilocks.inv (q5 1 2 3 4 5) =
      q5 16227807958868272813 4552730750487813724 11612833514307017418 9161515214422980997
        13509202856671625680 :=
  QuinticGoldilocks.inv_eq_of_mul_eq_one mul_inv_small

theorem kat_inv_wide :
    QuinticGoldilocks.inv
      (q5 81985529216486895 18364758544493064720 16045690984503098046 1089357896855742840
        1234605616436508552) =
      q5 17033286724174752684 16464919206864593009 3901309921467269908 17713944588012397749
        16392840534563784651 :=
  QuinticGoldilocks.inv_eq_of_mul_eq_one mul_inv_wide

/-! ## Teeth -/

/-- `t = 2^45 - 2^13` satisfies `t^5 = 2` in `Goldilocks`. -/
def fifthRootOfTwo : Goldilocks := Goldilocks.ofNat 35184372080640

/-- `2` IS a fifth power in `Goldilocks`, unlike the reduction constant `3`. -/
theorem tooth_two_is_fifth_power :
    ∃ t : Goldilocks, CRing.npow t 5 = Goldilocks.ofNat 2 :=
  ⟨fifthRootOfTwo, by decide +kernel⟩

/-- With the reduction `X^5 = 2` the product has zero divisors. -/
theorem tooth_reduction_two_has_zero_divisor :
    ∃ a b : QuinticGoldilocks, ¬ (a = QuinticGoldilocks.zero) ∧ ¬ (b = QuinticGoldilocks.zero) ∧
      QuinticGoldilocks.mulWith (Goldilocks.ofNat 2) a b = QuinticGoldilocks.zero := by
  refine ⟨⟨CommRingOps.neg fifthRootOfTwo, CommRingOps.one, CommRingOps.zero, CommRingOps.zero,
      CommRingOps.zero⟩,
    ⟨CRing.npow fifthRootOfTwo 4, CRing.npow fifthRootOfTwo 3, CRing.npow fifthRootOfTwo 2,
      fifthRootOfTwo, CommRingOps.one⟩, ?_, ?_,
    QuinticGoldilocks.mulWith_fifth_power_zero_divisor _ fifthRootOfTwo (by decide +kernel)⟩
  · intro h
    exact LawfulField.zero_ne_one (F := Goldilocks) (congrArg QuinticGoldilocks.c1 h).symm
  · intro h
    exact LawfulField.zero_ne_one (F := Goldilocks) (congrArg QuinticGoldilocks.c4 h).symm

/-- In the field itself the same pair multiplies to `X^5 - t^5 = 3 - 2 = 1`, so the linear
    factor is a unit there and its inverse is the quartic cofactor. -/
theorem kat_linear_factor_inverse :
    QuinticGoldilocks.inv
      ⟨CommRingOps.neg fifthRootOfTwo, CommRingOps.one, CommRingOps.zero, CommRingOps.zero,
        CommRingOps.zero⟩ =
      ⟨CRing.npow fifthRootOfTwo 4, CRing.npow fifthRootOfTwo 3, CRing.npow fifthRootOfTwo 2,
        fifthRootOfTwo, CommRingOps.one⟩ :=
  QuinticGoldilocks.inv_eq_of_mul_eq_one (by decide +kernel)

/-- `frob` moves `X` (to `ζ X`). -/
theorem tooth_frob_moves_xBasis :
    ¬ (QuinticGoldilocks.frob QuinticGoldilocks.xBasis = QuinticGoldilocks.xBasis) := by
  intro h
  have hb := (QuinticGoldilocks.frob_eq_self_iff _).mp h
  exact LawfulField.zero_ne_one (F := Goldilocks) (congrArg QuinticGoldilocks.c1 hb).symm

/-- The norm does vanish at zero. -/
theorem tooth_norm_vanishes_at_zero :
    ¬ (QuinticGoldilocks.norm QuinticGoldilocks.zero ≠ Goldilocks.zero) :=
  fun h => h QuinticGoldilocks.norm_zero

/-- Zero has no inverse. -/
theorem tooth_ext5_zero_has_no_inverse :
    ¬ (GoldilocksField.GoldilocksExt5.zero * GoldilocksField.GoldilocksExt5.zero⁻¹ =
      GoldilocksField.GoldilocksExt5.one) := by
  intro hEq
  have hZero : GoldilocksField.GoldilocksExt5.zero * GoldilocksField.GoldilocksExt5.zero⁻¹ =
      GoldilocksField.GoldilocksExt5.zero :=
    LawfulCommRing.zero_mul (GoldilocksField.GoldilocksExt5.zero⁻¹)
  rw [hZero] at hEq
  exact LawfulField.zero_ne_one (F := Goldilocks) (congrArg QuinticGoldilocks.c0 hEq)

#tooth_pair Qsag.QuinticGoldilocks.mulWith_nonResidue_eq_zero vs
  Qsag.QuinticExt5Teeth.tooth_reduction_two_has_zero_divisor
#tooth_pair Qsag.QuinticGoldilocks.nonResidue_not_fifth_power vs
  Qsag.QuinticExt5Teeth.tooth_two_is_fifth_power
#tooth_pair Qsag.QuinticGoldilocks.frob_eq_self_iff vs
  Qsag.QuinticExt5Teeth.tooth_frob_moves_xBasis
#tooth_pair Qsag.QuinticGoldilocks.norm_ne_zero vs
  Qsag.QuinticExt5Teeth.tooth_norm_vanishes_at_zero
#tooth_pair Qsag.GoldilocksField.GoldilocksExt5.ext5_mul_inv_cancel vs
  Qsag.QuinticExt5Teeth.tooth_ext5_zero_has_no_inverse

#verify_constructive
  Qsag.QuinticExt5Teeth.kat_mul_small
  Qsag.QuinticExt5Teeth.kat_mul_wide
  Qsag.QuinticExt5Teeth.kat_inv_small
  Qsag.QuinticExt5Teeth.kat_square_small
  Qsag.QuinticExt5Teeth.kat_inv_wide
  Qsag.QuinticExt5Teeth.kat_linear_factor_inverse

end QuinticExt5Teeth
end Qsag

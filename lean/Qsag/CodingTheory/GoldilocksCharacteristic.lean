module
/-
# Qsag.CodingTheory.GoldilocksCharacteristic — small naturals are invertible

`Poly3.simple_root_of_hasse`, and with it `nonExcluded_pairs_card_le` and
`cwyz26_affineMcaBound_sliced`, assume that `1, …, deg_Z Q` are nonzero in the field. Here
that is proved for `Goldilocks` and for `QuarticGoldilocks`, for every `k` below the
Goldilocks prime; an injective ring homomorphism transports it to any other extension.
-/

public import Qsag.ConcreteSecurityBudget
public import Qsag.CodingTheory.SimpleRootStratification
import all Qsag.ConcreteSecurityBudget
import all Qsag.CodingTheory.SimpleRootStratification
import all Qsag.CodingTheory.PolyMv3
import all Qsag.AffineProximityGaps
import all Qsag.Goldilocks

public section
namespace Qsag

set_option autoImplicit false

open CommRingOps

/-- Nonvanishing of a natural number is reflected by ring homomorphisms. -/
theorem natCast_ne_zero_of_hom {R S : Type} [LawfulCommRing R] [LawfulCommRing S]
    (φ : RingHom R S) (k : Nat) (h : (CRing.natCast k : S) ≠ zero) :
    (CRing.natCast k : R) ≠ zero := fun e => h (by
  rw [← RingHom.map_natCast φ k, e, φ.map_zero])

/-- Nonvanishing of a natural number is preserved by injective ring homomorphisms. -/
theorem natCast_ne_zero_of_injective_hom {R S : Type} [LawfulCommRing R] [LawfulCommRing S]
    (φ : RingHom R S) (hinj : ∀ x, φ.toFun x = zero → x = zero) (k : Nat)
    (h : (CRing.natCast k : R) ≠ zero) : (CRing.natCast k : S) ≠ zero := fun e =>
  h (hinj _ ((RingHom.map_natCast φ k).trans e))

namespace Goldilocks

theorem natCast_val : ∀ k : Nat, (CRing.natCast k : Goldilocks).val = k % goldilocksPrime
  | 0 => rfl
  | 1 => by decide
  | n + 2 => by
    show (Goldilocks.add (CRing.natCast (n + 1)) Goldilocks.one).val = _
    rw [Goldilocks.add_val, natCast_val (n + 1), Goldilocks.one_val, Nat.mod_add_mod]

/-- `1, …, p - 1` are nonzero in `Goldilocks`. -/
theorem natCast_ne_zero (k : Nat) (h1 : 1 ≤ k) (hk : k < goldilocksPrime) :
    (CRing.natCast k : Goldilocks) ≠ zero := fun e => by
  have hv := congrArg Goldilocks.val e
  rw [natCast_val, Nat.mod_eq_of_lt hk] at hv
  have h0 : k = 0 := hv
  rw [h0] at h1
  exact absurd h1 (by decide)

end Goldilocks

namespace QuarticGoldilocks

private theorem base_add_zero :
    CommRingOps.add (CommRingOps.zero : Goldilocks) CommRingOps.zero = CommRingOps.zero := by
  decide

theorem natCast_eq : ∀ k : Nat, (CRing.natCast k : QuarticGoldilocks) =
    ⟨⟨(CRing.natCast k : Goldilocks), CommRingOps.zero⟩, CommRingOps.zero⟩
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    show QuarticGoldilocks.add (CRing.natCast (n + 1)) QuarticGoldilocks.one = _
    rw [natCast_eq (n + 1)]
    apply QuarticGoldilocks.ext
    · apply GoldilocksExt2.ext
      · rfl
      · exact base_add_zero
    · apply GoldilocksExt2.ext
      · exact base_add_zero
      · exact base_add_zero

/-- `1, …, p - 1` are nonzero in `QuarticGoldilocks`. -/
theorem natCast_ne_zero (k : Nat) (h1 : 1 ≤ k) (hk : k < goldilocksPrime) :
    (CRing.natCast k : QuarticGoldilocks) ≠ CommRingOps.zero := fun e => by
  rw [natCast_eq] at e
  exact Goldilocks.natCast_ne_zero k h1 hk
    (congrArg (fun q : QuarticGoldilocks => q.c0.c0) e)

end QuarticGoldilocks

/-- The hypotheses are met by a concrete case: `5 ≠ 0` in both fields. -/
theorem inhabited_natCast_ne_zero :
    ∃ k : Nat, 1 ≤ k ∧ k < goldilocksPrime ∧ (CRing.natCast k : Goldilocks) ≠ zero ∧
      (CRing.natCast k : QuarticGoldilocks) ≠ zero :=
  ⟨5, by decide, by decide, Goldilocks.natCast_ne_zero 5 (by decide) (by decide),
    QuarticGoldilocks.natCast_ne_zero 5 (by decide) (by decide)⟩

/-- The bound `k < p` cannot be dropped: `p = 0` in `Goldilocks`. -/
theorem tooth_natCast_prime_eq_zero :
    ∃ k : Nat, 1 ≤ k ∧ ¬ (CRing.natCast k : Goldilocks) ≠ zero :=
  ⟨goldilocksPrime, by decide, fun h => h (Goldilocks.ext (by
    rw [Goldilocks.natCast_val, Nat.mod_self]; rfl))⟩

#verify_constructive natCast_ne_zero_of_hom natCast_ne_zero_of_injective_hom
#verify_constructive Goldilocks.natCast_val Goldilocks.natCast_ne_zero
#verify_constructive QuarticGoldilocks.natCast_eq QuarticGoldilocks.natCast_ne_zero
#verify_constructive inhabited_natCast_ne_zero tooth_natCast_prime_eq_zero
#verify_inhabited Goldilocks.natCast_ne_zero inhabited_natCast_ne_zero
#tooth_pair Goldilocks.natCast_ne_zero vs tooth_natCast_prime_eq_zero

end Qsag
end

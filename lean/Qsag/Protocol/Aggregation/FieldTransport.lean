module
/-
# Qsag.Protocol.Aggregation.FieldTransport — Protocol Uses of the Canonical Quartic Field

Unifies the four quartic Goldilocks field representations across the codebase:
1. `Qsag.QuarticGoldilocks` (`ConcreteSecurityBudget`, used by `CodingTheory/*` and `Hem*`),
2. `Qsag.GoldilocksExt4` (`SuccinctAggregationIop`, limb & Karatsuba model),
3. `Qsag.Aggregation.GoldilocksExt4` (`Aggregation`, 32-byte codec & verifier model), and
4. `Qsag.GoldilocksField.GoldilocksExt4` + `Ext4Poly` (`GoldilocksPrimalityAndExt4Field`,
   primality-certified tower and direct polynomial basis `𝔽_p[v]/(v^4 - 7)`).

Provides:
- Generic constructive `RingIso R S` and `FieldIso F G` (`≃+*`) with `refl`, `symm`, `trans`,
  and automatic inverse preservation (`RingIso.toFieldIso`),
- `LawfulField` instances for `Qsag.GoldilocksExt4`, `Qsag.Aggregation.GoldilocksExt4`, and
  `Qsag.GoldilocksField.GoldilocksExt4`,
- Explicit `FieldIso` bijections connecting all four `Ext4` types,
- Canonical 32-byte `Spec.FixedCodec` instances for `Aggregation.GoldilocksExt4` and
  `QuarticGoldilocks`, and
- Generic polynomial evaluation, `Nodup` domain, root-count, and Welch–Berlekamp proximity-gap
  transport theorems across `FieldIso`.
-/

public import Qsag.Spec.Primitives
public import Qsag.Math.QuarticExt4
public import Qsag.Protocol.Aggregation.ConcreteSecurityBudget
public import Qsag.Protocol.Aggregation.SuccinctAggregationIop
public import Qsag.Protocol.Aggregation.Aggregation
public import Qsag.Coding.Cwyz26
import all Qsag.Protocol.Aggregation.ConcreteSecurityBudget
import all Qsag.Protocol.Aggregation.SuccinctAggregationIop
import all Qsag.Protocol.Aggregation.Aggregation
import all Qsag.Math.QuarticExt4
import Qsag.Tactic.AssuranceKit

public section

/-! ## 1. `LawfulField` Instances for All Three `GoldilocksExt4` Models -/

namespace Qsag

instance instLawfulFieldSuccinctExt4 : LawfulField Qsag.GoldilocksExt4 where
  inv := Qsag.GoldilocksExt4.inv
  zero_ne_one := by decide
  inv_zero := Qsag.QuarticGoldilocks.inv_zero
  mul_inv_cancel := Qsag.GoldilocksExt4.mul_inv_cancel

instance instLawfulFieldAggExt4 : LawfulField Qsag.Aggregation.GoldilocksExt4 where
  inv := Qsag.Aggregation.GoldilocksExt4.inv
  zero_ne_one := by decide
  inv_zero := Qsag.QuarticGoldilocks.inv_zero
  mul_inv_cancel := Qsag.Aggregation.GoldilocksExt4.mul_inv_cancel

theorem certifiedExt4_zero_ne_one :
    (CommRingOps.zero : Qsag.GoldilocksField.GoldilocksExt4) ≠ CommRingOps.one := by
  intro h
  have hc0 : (CommRingOps.zero : Qsag.GoldilocksExt2) = CommRingOps.one :=
    congrArg Qsag.GoldilocksField.GoldilocksExt4.c0 h
  exact LawfulField.zero_ne_one hc0

instance instLawfulFieldCertifiedExt4 : LawfulField Qsag.GoldilocksField.GoldilocksExt4 where
  inv := Qsag.GoldilocksField.GoldilocksExt4.inv
  zero_ne_one := certifiedExt4_zero_ne_one
  inv_zero := Qsag.QuarticGoldilocks.inv_zero
  mul_inv_cancel {_a} ha := (Qsag.GoldilocksField.GoldilocksExt4.ext4_mul_inv_cancel ha).1

end Qsag

namespace Qsag.Math

set_option autoImplicit false

/-! ## 3. Canonical `FieldIso` Bridges Across All Four `GoldilocksExt4` Models -/

/-- Ring isomorphism `QuarticGoldilocks ≃+* Qsag.GoldilocksExt4` (`SuccinctAggregationIop`). -/
def ringIsoQuarticToSuccinct : RingIso Qsag.QuarticGoldilocks Qsag.GoldilocksExt4 where
  toFun x := ⟨x.c0, x.c1⟩
  invFun y := ⟨y.c0, y.c1⟩
  left_inv x := by cases x; rfl
  right_inv y := by cases y; rfl
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_neg _ := rfl
  map_sub _ _ := rfl
  map_mul _ _ := rfl

/-- Ring isomorphism `QuarticGoldilocks ≃+* Qsag.Aggregation.GoldilocksExt4`. -/
def ringIsoQuarticToAgg : RingIso Qsag.QuarticGoldilocks Qsag.Aggregation.GoldilocksExt4 where
  toFun x := ⟨x.c0, x.c1⟩
  invFun y := ⟨y.c0, y.c1⟩
  left_inv x := by cases x; rfl
  right_inv y := by cases y; rfl
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_neg _ := rfl
  map_sub _ _ := rfl
  map_mul _ _ := rfl

/-- Ring isomorphism `QuarticGoldilocks ≃+* Qsag.GoldilocksField.GoldilocksExt4`. -/
def ringIsoQuarticToCertified :
    RingIso Qsag.QuarticGoldilocks Qsag.GoldilocksField.GoldilocksExt4 where
  toFun x := ⟨x.c0, x.c1⟩
  invFun y := ⟨y.c0, y.c1⟩
  left_inv x := by cases x; rfl
  right_inv y := by cases y; rfl
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_neg _ := rfl
  map_sub _ _ := rfl
  map_mul _ _ := rfl

theorem succinctExt4_inv_zero :
    LawfulField.inv (CommRingOps.zero : Qsag.GoldilocksExt4) = CommRingOps.zero :=
  LawfulField.inv_zero

theorem aggExt4_inv_zero :
    LawfulField.inv (CommRingOps.zero : Qsag.Aggregation.GoldilocksExt4) = CommRingOps.zero :=
  LawfulField.inv_zero

theorem certifiedExt4_inv_zero :
    LawfulField.inv (CommRingOps.zero : Qsag.GoldilocksField.GoldilocksExt4) = CommRingOps.zero :=
  LawfulField.inv_zero

theorem quarticGoldilocks_inv_zero :
    LawfulField.inv (CommRingOps.zero : Qsag.QuarticGoldilocks) = CommRingOps.zero :=
  LawfulField.inv_zero

/-- Full field isomorphism `QuarticGoldilocks ≃+* Qsag.GoldilocksExt4`. -/
@[expose] def isoQuarticToSuccinct : FieldIso Qsag.QuarticGoldilocks Qsag.GoldilocksExt4 :=
  ringIsoQuarticToSuccinct.toFieldIso

/-- Full field isomorphism `QuarticGoldilocks ≃+* Qsag.Aggregation.GoldilocksExt4`. -/
@[expose] def isoQuarticToAgg : FieldIso Qsag.QuarticGoldilocks Qsag.Aggregation.GoldilocksExt4 :=
  ringIsoQuarticToAgg.toFieldIso

/-- Full field isomorphism `QuarticGoldilocks ≃+* Qsag.GoldilocksField.GoldilocksExt4`. -/
@[expose] def isoQuarticToCertified :
    FieldIso Qsag.QuarticGoldilocks Qsag.GoldilocksField.GoldilocksExt4 :=
  ringIsoQuarticToCertified.toFieldIso

/-- Composed field isomorphism `Qsag.GoldilocksExt4 ≃+* Qsag.Aggregation.GoldilocksExt4`. -/
@[expose] def isoSuccinctToAgg :
    FieldIso Qsag.GoldilocksExt4 Qsag.Aggregation.GoldilocksExt4 :=
  isoQuarticToSuccinct.symm.trans isoQuarticToAgg

/-- Direct polynomial-basis `[1, v, v^2, v^3]` multiplication homomorphism from `QuarticGoldilocks`
    into `GoldilocksField.Ext4Poly` modulo `v^4 - 7`. -/
theorem quartic_to_ext4Poly_mul_hom (x y : Qsag.QuarticGoldilocks) :
    let toPoly := fun z : Qsag.QuarticGoldilocks =>
      Qsag.GoldilocksField.GoldilocksExt4.towerToPoly (isoQuarticToCertified.toFun z)
    toPoly (CommRingOps.mul x y) =
      Qsag.GoldilocksField.GoldilocksExt4.Ext4Poly.mul (toPoly x) (toPoly y) := by
  intro toPoly
  dsimp only [toPoly]
  rw [isoQuarticToCertified.map_mul]
  exact Qsag.GoldilocksField.GoldilocksExt4.towerToPoly_mul_hom _ _

/-- Canonical 32-byte `Spec.FixedCodec` for `Qsag.Aggregation.GoldilocksExt4`. -/
def aggExt4Codec32 : Qsag.Spec.FixedCodec Qsag.Aggregation.GoldilocksExt4 32 where
  encode := Qsag.Aggregation.GoldilocksExt4.encodeBytes32
  decode := Qsag.Aggregation.GoldilocksExt4.decodeBytes32
  encode_len := Qsag.Aggregation.GoldilocksExt4.encodeBytes32_length
  decode_encode := Qsag.Aggregation.GoldilocksExt4.decodeBytes32_encodeBytes32

/-- Canonical 32-byte `Spec.FixedCodec` for `Qsag.QuarticGoldilocks` transported via `isoQuarticToAgg`. -/
def quarticExt4Codec32 : Qsag.Spec.FixedCodec Qsag.QuarticGoldilocks 32 where
  encode x := Qsag.Aggregation.GoldilocksExt4.encodeBytes32 (isoQuarticToAgg.toFun x)
  decode bs := (Qsag.Aggregation.GoldilocksExt4.decodeBytes32 bs).map isoQuarticToAgg.invFun
  encode_len x := Qsag.Aggregation.GoldilocksExt4.encodeBytes32_length _
  decode_encode x := by
    rw [Qsag.Aggregation.GoldilocksExt4.decodeBytes32_encodeBytes32]
    dsimp only [Option.map]
    rw [isoQuarticToAgg.left_inv]

/-! ## 4. Generic Polynomial, `Nodup`, and Correlated-Agreement Transport Across `FieldIso` -/

/-- `RoundPoly.evalCoeffs` commutes with any `RingIso`. -/
theorem RingIso.map_evalCoeffs {R S : Type} [CommRingOps R] [CommRingOps S]
    (φ : RingIso R S) :
    ∀ (cs : List R) (x : R),
      φ.toFun (Qsag.RoundPoly.evalCoeffs cs x) =
        Qsag.RoundPoly.evalCoeffs (cs.map φ.toFun) (φ.toFun x)
  | [], _ => φ.map_zero
  | c :: cs, x => by
    simp only [List.map_cons, Qsag.RoundPoly.evalCoeffs_cons, φ.map_add, φ.map_mul,
      φ.map_evalCoeffs cs x]

/-- Mapping a `Nodup` domain through an injective `RingIso` preserves `Nodup`. -/
theorem RingIso.map_nodup {R S : Type} [CommRingOps R] [CommRingOps S]
    (φ : RingIso R S) :
    ∀ {xs : List R}, xs.Nodup → (xs.map φ.toFun).Nodup
  | [], .nil => .nil
  | x :: xs, .cons hNotMem hNd =>
    .cons
      (fun y hy hEq => by
        obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hy
        exact hNotMem x' hx' (φ.toFun_injective hEq))
      (φ.map_nodup hNd)

/-- Exact root-count preservation across any `RingIso`. -/
theorem RingIso.filter_roots_length {R S : Type} [CommRingOps R] [CommRingOps S]
    [DecidableEq R] [DecidableEq S]
    (φ : RingIso R S) (cs : List R) :
    ∀ (D : List R),
      ((D.map φ.toFun).filter (fun y =>
        decide (Qsag.RoundPoly.evalCoeffs (cs.map φ.toFun) y = CommRingOps.zero))).length =
      (D.filter (fun x =>
        decide (Qsag.RoundPoly.evalCoeffs cs x = CommRingOps.zero))).length
  | [] => rfl
  | x :: xs => by
    have ih := φ.filter_roots_length cs xs
    have hIff :
        decide (Qsag.RoundPoly.evalCoeffs (cs.map φ.toFun) (φ.toFun x) = CommRingOps.zero) =
        decide (Qsag.RoundPoly.evalCoeffs cs x = CommRingOps.zero) := by
      rw [← φ.map_evalCoeffs cs x]
      by_cases h0 : Qsag.RoundPoly.evalCoeffs cs x = CommRingOps.zero
      · rw [h0, φ.map_zero]; simp
      · have hNe : φ.toFun (Qsag.RoundPoly.evalCoeffs cs x) ≠ CommRingOps.zero :=
          fun hEq => h0 ((φ.map_eq_zero_iff _).mp hEq)
        simp [h0, hNe]
    simp only [List.map_cons, List.filter]
    rw [hIff]
    cases decide (Qsag.RoundPoly.evalCoeffs cs x = CommRingOps.zero) <;>
      simp only [List.length_cons, ih]

/-- **Welch–Berlekamp Affine Proximity-Gap on `Qsag.Aggregation.GoldilocksExt4`**:
    Direct specialization over `Aggregation.GoldilocksExt4` (via its new `LawfulField` instance
    and `isoQuarticToAgg`), bounding bad `(α, β)` affine-combiner pairs by `max(|S|, |D|(|D|-1)/2)`
    whenever `2|D| + d + 1 < 3A`! -/
theorem aggExt4_welch_berlekamp_affine_proximity_gap
    (f g : Qsag.Aggregation.GoldilocksExt4 → Qsag.Aggregation.GoldilocksExt4)
    (D S : List Qsag.Aggregation.GoldilocksExt4)
    (d A : Nat)
    (badPairs : List (Qsag.Aggregation.GoldilocksExt4 × Qsag.Aggregation.GoldilocksExt4))
    (P_of : Qsag.Aggregation.GoldilocksExt4 × Qsag.Aggregation.GoldilocksExt4 →
      List Qsag.Aggregation.GoldilocksExt4)
    (hD : D.Nodup) (hS : S.Nodup)
    (hAD : A ≤ D.length)
    (hWB : 2 * D.length + d + 1 < 3 * A)
    (hBadNd : badPairs.Nodup)
    (hBadSub : ∀ p ∈ badPairs, p ∈ Qsag.prodPool S)
    (hBadDeg : ∀ p ∈ badPairs, (P_of p).length ≤ d + 1)
    (hBadAgree : ∀ p ∈ badPairs,
      A ≤ (D.filter (fun z =>
        decide (Qsag.RoundPoly.evalCoeffs (P_of p) z =
          CommRingOps.add (f z)
            (CommRingOps.mul (CommRingOps.add p.1 (CommRingOps.mul p.2 z)) (g z))))).length)
    (hBadExc : ∀ p ∈ badPairs, ¬ Qsag.HasAffineWitnessS1 d f g D p.1 p.2 (P_of p)) :
    badPairs.length ≤ Nat.max S.length (D.length * (D.length - 1) / 2) :=
  Qsag.welch_berlekamp_affine_proximity_gap
    f g D S d A badPairs P_of hD hS hAD hWB hBadNd hBadSub hBadDeg hBadAgree hBadExc

#verify_constructive
  Qsag.Math.RingIso.toFun_injective
  Qsag.Math.RingIso.map_eq_zero_iff
  Qsag.Math.quartic_to_ext4Poly_mul_hom
  Qsag.Math.RingIso.map_evalCoeffs
  Qsag.Math.RingIso.map_nodup
  Qsag.Math.RingIso.filter_roots_length
  Qsag.Math.aggExt4_welch_berlekamp_affine_proximity_gap

end Qsag.Math
end

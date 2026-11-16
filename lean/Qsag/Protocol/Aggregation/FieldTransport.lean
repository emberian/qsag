module
/-
# Qsag.Protocol.Aggregation.FieldTransport — One Canonical Quartic Field, Two Bases

There is one GF(p^4) carrier: the certified tower `Qsag.QuarticGoldilocks`
(`Math/QuarticExt4.lean`, `𝔽_{p^2}[v]/(v^2 - u)`, the layout of `field.rs:GoldilocksExt4`).
`Qsag.GoldilocksExt4`, `Qsag.Aggregation.GoldilocksExt4` and `Qsag.GoldilocksField.GoldilocksExt4`
are `abbrev`s of it, so a theorem stated over any of the four names applies to the others with no
transport step. The isomorphisms between those names kept here are the identity, with
`toFun`/`invFun` rewrite lemmas.

The one genuinely different representation is the polynomial basis
`GoldilocksField.GoldilocksExt4.Ext4Poly` (`a0 + a1 v + a2 v^2 + a3 v^3` over `𝔽_p[v]/(v^4 - 7)`,
the layout of `qsag-whir-verified`'s `Ext4`). This file provides

- `isoQuarticToPoly : FieldIso QuarticGoldilocks Ext4Poly` (preserves `0, 1, +, -, sub, *, inv`),
- wire-encoding preservation: the tower's 32 little-endian bytes are the polynomial-basis bytes in
  limb order `a0, a2, a1, a3` (`isoQuarticToPoly_encode`, `isoQuarticToPoly_decode`),
- `Spec.FixedCodec` instances for both bases, and
- transfer of polynomial evaluation, `Nodup` domains and exact root counts across any `RingIso`,
  instantiated for the polynomial basis.
-/

public import Qsag.Spec.Primitives
public import Qsag.Math.QuarticExt4
public import Qsag.Math.PolyRing
public import Qsag.Protocol.Aggregation.ConcreteSecurityBudget
public import Qsag.Protocol.Aggregation.SuccinctAggregationIop
public import Qsag.Protocol.Aggregation.Aggregation
public import Qsag.Coding.Cwyz26
import Qsag.Tactic.AssuranceKit

public section

/-! ## 1. Compatibility names for the canonical `LawfulField` instance -/

namespace Qsag

/-- The canonical `LawfulField QuarticGoldilocks` instance under its `SuccinctAggregationIop`
    spelling. Not an instance: instance search already finds the canonical one. -/
abbrev instLawfulFieldSuccinctExt4 : LawfulField Qsag.GoldilocksExt4 := inferInstance

/-- The canonical `LawfulField QuarticGoldilocks` instance under its `Aggregation` spelling. -/
abbrev instLawfulFieldAggExt4 : LawfulField Qsag.Aggregation.GoldilocksExt4 := inferInstance

/-- The canonical `LawfulField QuarticGoldilocks` instance under its `GoldilocksField` spelling. -/
abbrev instLawfulFieldCertifiedExt4 : LawfulField Qsag.GoldilocksField.GoldilocksExt4 :=
  inferInstance

theorem certifiedExt4_zero_ne_one :
    (CommRingOps.zero : Qsag.GoldilocksField.GoldilocksExt4) ≠ CommRingOps.one :=
  LawfulField.zero_ne_one

end Qsag

namespace Qsag.Math

set_option autoImplicit false

open Qsag.GoldilocksField.GoldilocksExt4 (Ext4Poly towerToPoly polyToTower)

/-! ## 2. Identity isomorphisms between the spellings of the canonical carrier -/

/-- The identity on `QuarticGoldilocks`, typed `QuarticGoldilocks ≃+* Qsag.GoldilocksExt4`. -/
def ringIsoQuarticToSuccinct : RingIso Qsag.QuarticGoldilocks Qsag.GoldilocksExt4 where
  toFun x := x
  invFun y := y
  left_inv _ := rfl
  right_inv _ := rfl
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_neg _ := rfl
  map_sub _ _ := rfl
  map_mul _ _ := rfl

/-- The identity on `QuarticGoldilocks`, typed `QuarticGoldilocks ≃+* Aggregation.GoldilocksExt4`. -/
def ringIsoQuarticToAgg : RingIso Qsag.QuarticGoldilocks Qsag.Aggregation.GoldilocksExt4 where
  toFun x := x
  invFun y := y
  left_inv _ := rfl
  right_inv _ := rfl
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_neg _ := rfl
  map_sub _ _ := rfl
  map_mul _ _ := rfl

/-- The identity on `QuarticGoldilocks`, typed
    `QuarticGoldilocks ≃+* GoldilocksField.GoldilocksExt4`. -/
def ringIsoQuarticToCertified :
    RingIso Qsag.QuarticGoldilocks Qsag.GoldilocksField.GoldilocksExt4 where
  toFun x := x
  invFun y := y
  left_inv _ := rfl
  right_inv _ := rfl
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

/-- The identity field isomorphism `QuarticGoldilocks ≃+* Qsag.GoldilocksExt4`. -/
def isoQuarticToSuccinct : FieldIso Qsag.QuarticGoldilocks Qsag.GoldilocksExt4 where
  toRingIso := ringIsoQuarticToSuccinct
  map_inv _ := rfl

/-- The identity field isomorphism `QuarticGoldilocks ≃+* Qsag.Aggregation.GoldilocksExt4`. -/
def isoQuarticToAgg : FieldIso Qsag.QuarticGoldilocks Qsag.Aggregation.GoldilocksExt4 where
  toRingIso := ringIsoQuarticToAgg
  map_inv _ := rfl

/-- The identity field isomorphism `QuarticGoldilocks ≃+* Qsag.GoldilocksField.GoldilocksExt4`. -/
def isoQuarticToCertified :
    FieldIso Qsag.QuarticGoldilocks Qsag.GoldilocksField.GoldilocksExt4 where
  toRingIso := ringIsoQuarticToCertified
  map_inv _ := rfl

/-- Composed field isomorphism `Qsag.GoldilocksExt4 ≃+* Qsag.Aggregation.GoldilocksExt4`. -/
def isoSuccinctToAgg :
    FieldIso Qsag.GoldilocksExt4 Qsag.Aggregation.GoldilocksExt4 :=
  isoQuarticToSuccinct.symm.trans isoQuarticToAgg

@[simp] theorem isoQuarticToSuccinct_toFun (x : Qsag.QuarticGoldilocks) :
    isoQuarticToSuccinct.toFun x = x := by rfl
@[simp] theorem isoQuarticToSuccinct_invFun (x : Qsag.GoldilocksExt4) :
    isoQuarticToSuccinct.invFun x = x := by rfl
@[simp] theorem isoQuarticToAgg_toFun (x : Qsag.QuarticGoldilocks) :
    isoQuarticToAgg.toFun x = x := by rfl
@[simp] theorem isoQuarticToAgg_invFun (x : Qsag.Aggregation.GoldilocksExt4) :
    isoQuarticToAgg.invFun x = x := by rfl
@[simp] theorem isoQuarticToCertified_toFun (x : Qsag.QuarticGoldilocks) :
    isoQuarticToCertified.toFun x = x := by rfl
@[simp] theorem isoQuarticToCertified_invFun (x : Qsag.GoldilocksField.GoldilocksExt4) :
    isoQuarticToCertified.invFun x = x := by rfl

/-! ## 3. The polynomial basis `𝔽_p[v]/(v^4 - 7)` -/

/-- Ring isomorphism from the canonical tower to the polynomial basis `[1, v, v^2, v^3]`:
    `(A0 + A1 u) + (B0 + B1 u) v ↦ A0 + B0 v + A1 v^2 + B1 v^3`. -/
def ringIsoQuarticToPoly : RingIso Qsag.QuarticGoldilocks Ext4Poly where
  toFun := towerToPoly
  invFun := polyToTower
  left_inv := Qsag.GoldilocksField.GoldilocksExt4.polyToTower_towerToPoly
  right_inv := Qsag.GoldilocksField.GoldilocksExt4.towerToPoly_polyToTower
  map_zero := Qsag.GoldilocksField.GoldilocksExt4.towerToPoly_zero
  map_one := Qsag.GoldilocksField.GoldilocksExt4.towerToPoly_one
  map_add := Qsag.GoldilocksField.GoldilocksExt4.towerToPoly_add
  map_neg := Qsag.GoldilocksField.GoldilocksExt4.towerToPoly_neg
  map_sub := Qsag.GoldilocksField.GoldilocksExt4.towerToPoly_sub
  map_mul := Qsag.GoldilocksField.GoldilocksExt4.towerToPoly_mul

/-- Field isomorphism from the canonical tower to the polynomial basis. -/
def isoQuarticToPoly : FieldIso Qsag.QuarticGoldilocks Ext4Poly where
  toRingIso := ringIsoQuarticToPoly
  map_inv := Qsag.GoldilocksField.GoldilocksExt4.towerToPoly_inv

@[simp] theorem isoQuarticToPoly_toFun (x : Qsag.QuarticGoldilocks) :
    isoQuarticToPoly.toFun x = towerToPoly x := by rfl
@[simp] theorem isoQuarticToPoly_invFun (p : Ext4Poly) :
    isoQuarticToPoly.invFun p = polyToTower p := by rfl

/-- Multiplication in the polynomial basis is the image of tower multiplication. -/
theorem quartic_to_ext4Poly_mul_hom (x y : Qsag.QuarticGoldilocks) :
    let toPoly := fun z : Qsag.QuarticGoldilocks =>
      Qsag.GoldilocksField.GoldilocksExt4.towerToPoly (isoQuarticToCertified.toFun z)
    toPoly (CommRingOps.mul x y) =
      Qsag.GoldilocksField.GoldilocksExt4.Ext4Poly.mul (toPoly x) (toPoly y) := by
  intro toPoly
  dsimp only [toPoly]
  rw [isoQuarticToCertified.map_mul]
  exact Qsag.GoldilocksField.GoldilocksExt4.towerToPoly_mul_hom _ _

/-- The isomorphism preserves the wire encoding: the 32 bytes `field.rs:to_le_bytes` writes for a
    tower element are the polynomial-basis bytes of its image. -/
theorem isoQuarticToPoly_encode (x : Qsag.QuarticGoldilocks) :
    Qsag.encodeExt4PolyBytes32 (isoQuarticToPoly.toFun x) = Qsag.encodeExt4Bytes32 x :=
  (Qsag.encodeExt4Bytes32_eq_poly x).symm

/-- The isomorphism preserves canonical decoding, including every rejection. -/
theorem isoQuarticToPoly_decode (bs : List UInt8) :
    Qsag.decodeExt4PolyBytes32 bs = (Qsag.decodeExt4Bytes32 bs).map isoQuarticToPoly.toFun :=
  Qsag.decodeExt4PolyBytes32_eq_tower bs

/-- Canonical 32-byte big-endian `Spec.FixedCodec` for `Qsag.Aggregation.GoldilocksExt4`. -/
def aggExt4Codec32 : Qsag.Spec.FixedCodec Qsag.Aggregation.GoldilocksExt4 32 where
  encode := Qsag.Aggregation.GoldilocksExt4.encodeBytes32
  decode := Qsag.Aggregation.GoldilocksExt4.decodeBytes32
  encode_len := Qsag.Aggregation.GoldilocksExt4.encodeBytes32_length
  decode_encode := Qsag.Aggregation.GoldilocksExt4.decodeBytes32_encodeBytes32

/-- The same codec under the `QuarticGoldilocks` spelling. -/
def quarticExt4Codec32 : Qsag.Spec.FixedCodec Qsag.QuarticGoldilocks 32 := aggExt4Codec32

/-- The wire codec of `field.rs:GoldilocksExt4` (`to_le_bytes` / `from_le_bytes_canonical`). -/
def quarticExt4WireCodec32 : Qsag.Spec.FixedCodec Qsag.QuarticGoldilocks 32 where
  encode := Qsag.encodeExt4Bytes32
  decode := Qsag.decodeExt4Bytes32
  encode_len := Qsag.encodeExt4Bytes32_length
  decode_encode := Qsag.decodeExt4Bytes32_encode

/-- The same wire codec read in the polynomial basis (`decode_canonical_ext4`). -/
def ext4PolyWireCodec32 : Qsag.Spec.FixedCodec Ext4Poly 32 where
  encode := Qsag.encodeExt4PolyBytes32
  decode := Qsag.decodeExt4PolyBytes32
  encode_len p := by
    rw [← Qsag.GoldilocksField.GoldilocksExt4.towerToPoly_polyToTower p,
      ← Qsag.encodeExt4Bytes32_eq_poly]
    exact Qsag.encodeExt4Bytes32_length _
  decode_encode := Qsag.decodeExt4PolyBytes32_encode

/-- The two wire codecs agree through `isoQuarticToPoly` on encoding. -/
theorem ext4PolyWireCodec32_encode (x : Qsag.QuarticGoldilocks) :
    ext4PolyWireCodec32.encode (isoQuarticToPoly.toFun x) = quarticExt4WireCodec32.encode x :=
  isoQuarticToPoly_encode x

/-- The two wire codecs agree through `isoQuarticToPoly` on decoding. -/
theorem ext4PolyWireCodec32_decode (bs : List UInt8) :
    ext4PolyWireCodec32.decode bs =
      (quarticExt4WireCodec32.decode bs).map isoQuarticToPoly.toFun :=
  isoQuarticToPoly_decode bs

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
    The generic theorem at the canonical carrier, bounding bad `(α, β)` affine-combiner pairs by `max(|S|, |D|(|D|-1)/2)`
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

/-- Polynomial evaluation in the polynomial basis is the image of evaluation in the tower. -/
theorem ext4Poly_evalCoeffs (cs : List Qsag.QuarticGoldilocks) (x : Qsag.QuarticGoldilocks) :
    towerToPoly (Qsag.RoundPoly.evalCoeffs cs x) =
      Qsag.RoundPoly.evalCoeffs (cs.map towerToPoly) (towerToPoly x) :=
  ringIsoQuarticToPoly.map_evalCoeffs cs x

/-- A polynomial has exactly as many roots in a domain read in the polynomial basis as in the
    tower: root-count bounds proved over `QuarticGoldilocks` hold verbatim for `Ext4Poly`. -/
theorem ext4Poly_filter_roots_length (cs D : List Qsag.QuarticGoldilocks) :
    ((D.map towerToPoly).filter (fun y =>
      decide (Qsag.RoundPoly.evalCoeffs (cs.map towerToPoly) y = CommRingOps.zero))).length =
    (D.filter (fun x =>
      decide (Qsag.RoundPoly.evalCoeffs cs x = CommRingOps.zero))).length :=
  ringIsoQuarticToPoly.filter_roots_length cs D

/-- A duplicate-free tower domain stays duplicate-free in the polynomial basis. -/
theorem ext4Poly_map_nodup {D : List Qsag.QuarticGoldilocks} (h : D.Nodup) :
    (D.map towerToPoly).Nodup :=
  ringIsoQuarticToPoly.map_nodup h

#verify_constructive
  Qsag.Math.quartic_to_ext4Poly_mul_hom
  Qsag.Math.RingIso.map_evalCoeffs
  Qsag.Math.RingIso.map_nodup
  Qsag.Math.RingIso.filter_roots_length
  Qsag.Math.aggExt4_welch_berlekamp_affine_proximity_gap
  Qsag.Math.isoQuarticToPoly_encode
  Qsag.Math.isoQuarticToPoly_decode
  Qsag.Math.ext4Poly_evalCoeffs
  Qsag.Math.ext4Poly_filter_roots_length
  Qsag.Math.ext4Poly_map_nodup

end Qsag.Math
end

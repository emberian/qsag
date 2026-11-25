module


public import Qsag.Tactic.CathedralKit
public import Qsag.Math.Tactic.MaskBijection
public import Qsag.Math.PolyRing
public import Qsag.Math.Gf2Pow128
public import Qsag.Math.GoldilocksEncoding
public import Qsag.Math.QuinticExt5

public section

namespace Qsag.Repair

set_option autoImplicit false

open Qsag.Math

/-! ## 1. Generic `RingIso` & `FieldIso` Proof-Repair Transport Combinators -/

/-- Conjugate any `SimpleEquiv R R` pad bijection across a `RingIso R S` (`s ↦ φ(e(φ⁻¹(s)))`). -/
def transportEquiv {R S : Type} [CommRingOps R] [CommRingOps S]
    (φ : RingIso R S) (e : SimpleEquiv R R) : SimpleEquiv S S where
  toFun s := φ.toFun (e.toFun (φ.invFun s))
  invFun s := φ.toFun (e.invFun (φ.invFun s))
  left_inv s := by rw [φ.left_inv, e.left_inv, φ.right_inv]
  right_inv s := by rw [φ.left_inv, e.right_inv, φ.right_inv]

/-- Conjugating `ringAddEquiv delta` across `φ : RingIso R S` computes `ringAddEquiv (φ.toFun delta)`
    pointwise on `S`. -/
theorem transportEquiv_ringAdd_toFun {R S : Type} [LawfulCommRing R] [LawfulCommRing S]
    (φ : RingIso R S) (delta : R) (s : S) :
    (transportEquiv φ (ringAddEquiv delta)).toFun s =
      (ringAddEquiv (φ.toFun delta)).toFun s := by
  change φ.toFun (CommRingOps.add (φ.invFun s) delta) = CommRingOps.add s (φ.toFun delta)
  rw [φ.map_add, φ.right_inv]

/-- Lift an enumeration `Fin C ≃ R` across `φ : RingIso R S` to `Fin C ≃ S`. -/
def transportEnum {R S : Type} [CommRingOps R] [CommRingOps S] {C : Nat}
    (φ : RingIso R S) (enumR : SimpleEquiv (Fin C) R) : SimpleEquiv (Fin C) S where
  toFun i := φ.toFun (enumR.toFun i)
  invFun s := enumR.invFun (φ.invFun s)
  left_inv i := by rw [φ.left_inv, enumR.left_inv]
  right_inv s := by rw [enumR.right_inv, φ.right_inv]

/-- **Algebraic `qsum` Pad-Invariance Repair (`transport_qsum_pad_invariance`)**:
    Transports uniform additive mask invariance directly from carrier `R` to isomorphic carrier `S`. -/
theorem transport_qsum_pad_invariance {R S : Type} [LawfulCommRing R] [LawfulCommRing S] {C : Nat}
    (φ : RingIso R S) (enumR : SimpleEquiv (Fin C) R) (deltaS : S) (f : S → Nat) :
    qsum C (fun i => f (CommRingOps.add ((transportEnum φ enumR).toFun i) deltaS)) =
      qsum C (fun i => f ((transportEnum φ enumR).toFun i)) := by
  let enumS := transportEnum φ enumR
  exact qsum_bijection_hop_eq enumS (SimpleEquiv.symm (ringAddEquiv deltaS))
    (fun s => f (CommRingOps.add s deltaS)) f
    (fun s => congrArg f (ring_sub_add_cancel_right s deltaS))

/-- **Affine Linear-Combination Transport (`transport_affine_eq`)**:
    Transports an affine equation `p + α * q = target` across any `RingIso R S`. -/
theorem transport_affine_eq {R S : Type} [CommRingOps R] [CommRingOps S]
    (φ : RingIso R S) {p α q target : R} :
    CommRingOps.add p (CommRingOps.mul α q) = target ↔
      CommRingOps.add (φ.toFun p) (CommRingOps.mul (φ.toFun α) (φ.toFun q)) = φ.toFun target := by
  rw [← φ.map_mul, ← φ.map_add]
  exact ⟨congrArg φ.toFun, φ.toFun_injective⟩

/-- **Field Affine Bijection Transport (`transport_field_affine_cancel`)**:
    Transports nonzero affine unmasking `(base + scale * x - base) * scale⁻¹ = x` across any `FieldIso`. -/
theorem transport_field_affine_cancel {F G : Type} [LawfulField F] [LawfulField G]
    (φ : FieldIso F G) {base scale x : F} (hScale : scale ≠ CommRingOps.zero) :
    CommRingOps.mul
      (CommRingOps.sub
        (CommRingOps.add (φ.toFun base) (CommRingOps.mul (φ.toFun scale) (φ.toFun x)))
        (φ.toFun base))
      (LawfulField.inv (φ.toFun scale)) = φ.toFun x := by
  rw [← φ.map_mul, ← φ.map_add, ← φ.map_sub, ← φ.map_inv, ← φ.map_mul]
  apply congrArg φ.toFun
  rw [ring_left_add_sub_cancel, LawfulCommRing.mul_comm scale x, LawfulCommRing.mul_assoc,
      LawfulField.mul_inv_cancel hScale, LawfulCommRing.mul_one]

/-! ## 2. `TowerElem k ≃+* PackedTower k` (`Tower128 ≃ BitVec 128` Hardware Carrier Isomorphism) -/

/-- Packed `2^k`-bit word carrier equipped with XOR addition and carryless Karatsuba `mulExec`. -/
structure PackedTower (k : Nat) where
  bits : BitVec (2 ^ k)
  deriving DecidableEq, Repr

namespace PackedTower

theorem ext {k : Nat} {a b : PackedTower k} (h : a.bits = b.bits) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

instance instCommRingOps (k : Nat) : CommRingOps (PackedTower k) where
  zero := ⟨0⟩
  one := ⟨packTower k (towerOne k)⟩
  add x y := ⟨x.bits ^^^ y.bits⟩
  mul x y := ⟨mulExec k x.bits y.bits⟩
  neg x := x
  sub x y := ⟨x.bits ^^^ y.bits⟩

instance instLawfulCommRing (k : Nat) : LawfulCommRing (PackedTower k) where
  add_assoc a b c := ext (BitVec.xor_assoc a.bits b.bits c.bits)
  add_comm a b := ext (BitVec.xor_comm a.bits b.bits)
  zero_add a := ext (Qsag.bv_zero_xor a.bits)
  add_zero a := ext (Qsag.bv_xor_zero a.bits)
  add_left_neg a := ext (Qsag.bv_xor_self a.bits)
  sub_eq_add_neg _ _ := rfl
  mul_assoc a b c := by
    apply ext
    change mulExec k (mulExec k a.bits b.bits) c.bits =
      mulExec k a.bits (mulExec k b.bits c.bits)
    rw [← packTower_unpackTower k a.bits, ← packTower_unpackTower k b.bits,
        ← packTower_unpackTower k c.bits]
    simp only [mulExec_refines, towerMul_assoc]
  mul_comm a b := by
    apply ext
    change mulExec k a.bits b.bits = mulExec k b.bits a.bits
    rw [← packTower_unpackTower k a.bits, ← packTower_unpackTower k b.bits]
    simp only [mulExec_refines, towerMul_comm]
  one_mul a := by
    apply ext
    change mulExec k (packTower k (towerOne k)) a.bits = a.bits
    rw [← packTower_unpackTower k a.bits, mulExec_refines, towerOne_mul, packTower_unpackTower]
  mul_one a := by
    apply ext
    change mulExec k a.bits (packTower k (towerOne k)) = a.bits
    rw [← packTower_unpackTower k a.bits, mulExec_refines, towerMul_one, packTower_unpackTower]
  left_distrib a b c := by
    apply ext
    change mulExec k a.bits (b.bits ^^^ c.bits) =
      mulExec k a.bits b.bits ^^^ mulExec k a.bits c.bits
    rw [← packTower_unpackTower k a.bits, ← packTower_unpackTower k b.bits,
        ← packTower_unpackTower k c.bits, ← packTower_add, mulExec_refines,
        towerMul_add_distrib, packTower_add, mulExec_refines, mulExec_refines]
  right_distrib a b c := by
    apply ext
    change mulExec k (a.bits ^^^ b.bits) c.bits =
      mulExec k a.bits c.bits ^^^ mulExec k b.bits c.bits
    rw [← packTower_unpackTower k a.bits, ← packTower_unpackTower k b.bits,
        ← packTower_unpackTower k c.bits, ← packTower_add, mulExec_refines,
        towerAdd_mul_distrib, packTower_add, mulExec_refines, mulExec_refines]

end PackedTower

/-- Two-sided `RingIso` between recursive `TowerElem k` and packed `BitVec (2^k)` (`PackedTower k`). -/
def towerPackedRingIso (k : Nat) : RingIso (TowerElem k) (PackedTower k) where
  toFun x := ⟨packTower k x⟩
  invFun y := unpackTower k y.bits
  left_inv x := unpackTower_packTower k x
  right_inv y := PackedTower.ext (packTower_unpackTower k y.bits)
  map_zero := PackedTower.ext (packTower_zero k)
  map_one := rfl
  map_add x y := PackedTower.ext (packTower_add k x y)
  map_neg _ := rfl
  map_sub x y := PackedTower.ext (packTower_add k x y)
  map_mul x y := PackedTower.ext (mulExec_refines k x y).symm

/-- Deployed `Tower128 ≃+* PackedTower 7` (`BitVec 128`) isomorphism. -/
abbrev tower128PackedIso : RingIso Tower128 (PackedTower 7) := towerPackedRingIso 7


private theorem quintic_frob_neg (z : QuinticGoldilocks) :
    QuinticGoldilocks.frob (CommRingOps.neg z) = CommRingOps.neg (QuinticGoldilocks.frob z) := by
  apply LawfulCommRing.add_left_cancel (a := QuinticGoldilocks.frob z)
  rw [← QuinticGoldilocks.frob_add, LawfulCommRing.add_right_neg,
      LawfulCommRing.add_right_neg, QuinticGoldilocks.frob_zero]

private theorem quintic_frob_sub (x y : QuinticGoldilocks) :
    QuinticGoldilocks.frob (CommRingOps.sub x y) =
      CommRingOps.sub (QuinticGoldilocks.frob x) (QuinticGoldilocks.frob y) := by
  rw [LawfulCommRing.sub_eq_add_neg, QuinticGoldilocks.frob_add,
      quintic_frob_neg, ← LawfulCommRing.sub_eq_add_neg]

/-- Fourfold Frobenius `z ↦ frob⁴(z)` (two-sided inverse of `QuinticGoldilocks.frob`). -/
def quinticFrob4 (z : QuinticGoldilocks) : QuinticGoldilocks :=
  QuinticGoldilocks.frob (QuinticGoldilocks.frob (QuinticGoldilocks.frob (QuinticGoldilocks.frob z)))

/-- Order-5 Galois Frobenius `FieldIso` on `QuinticGoldilocks = 𝔽_p[X]/(X^5 - 3)`. -/
def quinticFrobRingIso : RingIso QuinticGoldilocks QuinticGoldilocks where
  toFun := QuinticGoldilocks.frob
  invFun := quinticFrob4
  left_inv z := QuinticGoldilocks.frob_pow5 z
  right_inv z := QuinticGoldilocks.frob_pow5 z
  map_zero := QuinticGoldilocks.frob_zero
  map_one := QuinticGoldilocks.frob_one
  map_add := QuinticGoldilocks.frob_add
  map_neg := quintic_frob_neg
  map_sub := quintic_frob_sub
  map_mul := QuinticGoldilocks.frob_mul

def quinticFrobFieldIso : FieldIso QuinticGoldilocks QuinticGoldilocks :=
  quinticFrobRingIso.toFieldIso

/-- Base-field polynomials over `QuinticGoldilocks` preserve roots across the Frobenius `FieldIso`:
    if `P` has coefficients fixed by `frob` (`∈ 𝔽_p`), then `P(z) = 0 ↔ P(frob z) = 0`. -/
theorem quintic_frob_preserves_poly_root
    (cs : List QuinticGoldilocks) (hBase : ∀ c ∈ cs, QuinticGoldilocks.frob c = c)
    (z : QuinticGoldilocks) :
    RoundPoly.evalCoeffs cs z = CommRingOps.zero ↔
      RoundPoly.evalCoeffs cs (QuinticGoldilocks.frob z) = CommRingOps.zero := by
  have hMapEq : cs.map QuinticGoldilocks.frob = cs := by
    induction cs with
    | nil => rfl
    | cons c rest ih =>
      simp only [List.map_cons]
      rw [hBase c (.head rest), ih (fun x hx => hBase x (.tail c hx))]
  have hEval : QuinticGoldilocks.frob (RoundPoly.evalCoeffs cs z) =
      RoundPoly.evalCoeffs cs (QuinticGoldilocks.frob z) := by
    have hMap : ∀ (ps : List QuinticGoldilocks),
        QuinticGoldilocks.frob (RoundPoly.evalCoeffs ps z) =
          RoundPoly.evalCoeffs (ps.map QuinticGoldilocks.frob) (QuinticGoldilocks.frob z) := by
      intro ps
      induction ps with
      | nil => exact QuinticGoldilocks.frob_zero
      | cons p tail ih =>
        simp only [List.map_cons, RoundPoly.evalCoeffs_cons]
        rw [QuinticGoldilocks.frob_add, QuinticGoldilocks.frob_mul, ih]
    rw [hMap cs, hMapEq]
  rw [← hEval]
  exact (quinticFrobRingIso.map_eq_zero_iff _).symm

/-! ## 4. Scar-Free Repair & 1-Line `by mask_bijection_hop` Demonstrations -/

/-- Carrier-polymorphic quadratic evaluation `c0 + c1 * x + c2 * x^2` over any `LawfulCommRing R`. -/
def evalQuadGeneric {R : Type} [LawfulCommRing R] (c0 c1 c2 x : R) : R :=
  CommRingOps.add c0 (CommRingOps.mul x (CommRingOps.add c1 (CommRingOps.mul x c2)))

theorem evalQuadGeneric_zero {R : Type} [LawfulCommRing R] (c0 c1 c2 : R) :
    evalQuadGeneric c0 c1 c2 CommRingOps.zero = c0 := by
  unfold evalQuadGeneric
  rw [LawfulCommRing.zero_mul, LawfulCommRing.add_zero]


/-- Left-inverse roundtrip for `towerPackedRingIso` (`TowerElem k ≃+* PackedTower k`). -/
theorem towerPackedRingIso_left_inv (k : Nat) (x : TowerElem k) :
    (towerPackedRingIso k).invFun ((towerPackedRingIso k).toFun x) = x :=
  (towerPackedRingIso k).left_inv x


/-- 1-line `by mask_bijection_hop` uniform pad-invariance over `Goldilocks`. -/
theorem mask_hop_goldilocks {C : Nat} (enum : SimpleEquiv (Fin C) Goldilocks)
    (delta : Goldilocks) (f : Goldilocks → Nat) :
    qsum C (fun i => f (CommRingOps.add (enum.toFun i) delta)) =
      qsum C (fun i => f (enum.toFun i)) := by
  mask_bijection_hop


/-- 1-line `by mask_bijection_hop` uniform pad-invariance over `QuinticGoldilocks` (`Fp5`). -/
theorem mask_hop_quintic_ext5 {C : Nat} (enum : SimpleEquiv (Fin C) QuinticGoldilocks)
    (delta : QuinticGoldilocks) (f : QuinticGoldilocks → Nat) :
    qsum C (fun i => f (CommRingOps.add (enum.toFun i) delta)) =
      qsum C (fun i => f (enum.toFun i)) := by
  mask_bijection_hop

/-- 1-line `by mask_bijection_hop` uniform pad-invariance over `Tower128 × BitVec 128` product space. -/
theorem mask_hop_tower128_prod {C : Nat}
    (enum : SimpleEquiv (Fin C) (Tower128 × BitVec 128))
    (dT : Tower128) (dB : BitVec 128) (f : Tower128 × BitVec 128 → Nat) :
    qsum C (fun i =>
      f (CommRingOps.add (enum.toFun i).1 dT, (enum.toFun i).2 ^^^ dB)) =
      qsum C (fun i => f (enum.toFun i)) := by
  mask_bijection_hop


#verify_constructive Qsag.Repair.transportEquiv_ringAdd_toFun
  Qsag.Repair.transport_qsum_pad_invariance
  Qsag.Repair.transport_affine_eq
  Qsag.Repair.transport_field_affine_cancel
  Qsag.Repair.towerPackedRingIso_left_inv
  Qsag.Repair.quintic_frob_preserves_poly_root
  Qsag.Repair.mask_hop_goldilocks
  Qsag.Repair.mask_hop_quintic_ext5
  Qsag.Repair.mask_hop_tower128_prod

end Qsag.Repair
end

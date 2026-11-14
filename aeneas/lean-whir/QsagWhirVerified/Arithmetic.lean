module
public import QsagWhirVerified.Funs
import all Aeneas
import all Aeneas.Std.Types
public section
open Aeneas Aeneas.Std
namespace qsag_whir_verified.proofs
theorem u64_cast_u128_val (x : Std.U64) :
    (UScalar.cast .U128 x).val = x.val := by
  have hx : x.val < 2 ^ 64 := x.bv.isLt
  have hx128 : x.val < 2 ^ 128 := Nat.lt_of_lt_of_le hx (by decide)
  change (x.bv.setWidth 128).toNat = x.bv.toNat
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx128]

theorem u128_cast_u64_val_of_lt (x : Std.U128) (h : x.val < 2 ^ 64) :
    (UScalar.cast .U64 x).val = x.val := by
  change (x.bv.setWidth 64).toNat = x.bv.toNat
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h]

theorem u128_add_ok {a b : Std.U128} (h : a.val + b.val < 2 ^ 128) :
    (a + b : Result Std.U128) = .ok ⟨a.bv + b.bv⟩ ∧
      (⟨a.bv + b.bv⟩ : Std.U128).val = a.val + b.val := by
  have h1 : (a + b : Result Std.U128) = .ok ⟨a.bv + b.bv⟩ := by
    simp [hAdd_uscalar_eq, h]
  refine ⟨h1, ?_⟩
  change (a.bv + b.bv).toNat = a.bv.toNat + b.bv.toNat
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem u128_sub_ok {a b : Std.U128} (h : b.val ≤ a.val) :
    (a - b : Result Std.U128) = .ok ⟨a.bv - b.bv⟩ ∧
      (⟨a.bv - b.bv⟩ : Std.U128).val = a.val - b.val := by
  have h1 : (a - b : Result Std.U128) = .ok ⟨a.bv - b.bv⟩ := by
    simp [hSub_uscalar_eq, h]
  refine ⟨h1, ?_⟩
  change (a.bv - b.bv).toNat = a.bv.toNat - b.bv.toNat
  have ha : a.bv.toNat < 2 ^ 128 := a.bv.isLt
  exact BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)

theorem u128_mul_ok {a b : Std.U128} (h : a.val * b.val < 2 ^ 128) :
    (a * b : Result Std.U128) = .ok ⟨a.bv * b.bv⟩ ∧
      (⟨a.bv * b.bv⟩ : Std.U128).val = a.val * b.val := by
  have h1 : (a * b : Result Std.U128) = .ok ⟨a.bv * b.bv⟩ := by
    simp [hMul_uscalar_eq, h]
  refine ⟨h1, ?_⟩
  change (a.bv * b.bv).toNat = a.bv.toNat * b.bv.toNat
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]


private theorem reduce_wide (x : U128) :
    ∃ r : U128, (x % UScalar.cast .U128 GOLDILOCKS_P : Result U128) = .ok r ∧
      (UScalar.cast .U64 r).val = x.val % 18446744069414584321 := by
  have hp : (UScalar.cast .U128 GOLDILOCKS_P).val = 18446744069414584321 := by
    unfold GOLDILOCKS_P
    rfl
  let r : U128 := ⟨x.bv % (UScalar.cast .U128 GOLDILOCKS_P).bv⟩
  have hr : r.val = x.val % 18446744069414584321 := by
    change (x.bv % (UScalar.cast .U128 GOLDILOCKS_P).bv).toNat = _
    rw [BitVec.toNat_umod]
    exact congrArg (x.val % ·) hp
  refine ⟨r, ?_, ?_⟩
  · simp only [hMod_uscalar_eq, hp]
    rfl
  · rw [u128_cast_u64_val_of_lt r (by rw [hr]; exact Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)), hr]

theorem add_modular_spec (a b : U64) :
    ∃ r, add a b = .ok r ∧ r.val = (a.val + b.val) % 18446744069414584321 := by
  have ha := u64_cast_u128_val a
  have hb := u64_cast_u128_val b
  obtain ⟨hs, hv⟩ := u128_add_ok (a := UScalar.cast .U128 a) (b := UScalar.cast .U128 b)
    (by rw [ha, hb]; have ha64 : a.val < 2^64 := a.bv.isLt; have hb64 : b.val < 2^64 := b.bv.isLt; omega)
  obtain ⟨r, hr, hrv⟩ := reduce_wide ⟨(UScalar.cast .U128 a).bv + (UScalar.cast .U128 b).bv⟩
  refine ⟨UScalar.cast .U64 r, ?_, ?_⟩
  · simp only [add, lift_eq_ok, bind_eq_result_bind, Result.bind, hs, hr]
  · rw [hrv, hv, ha, hb]

theorem mul_modular_spec (a b : U64) :
    ∃ r, mul a b = .ok r ∧ r.val = (a.val * b.val) % 18446744069414584321 := by
  have ha := u64_cast_u128_val a
  have hb := u64_cast_u128_val b
  obtain ⟨hs, hv⟩ := u128_mul_ok (a := UScalar.cast .U128 a) (b := UScalar.cast .U128 b)
    (by rw [ha, hb]; have hh := Nat.mul_lt_mul'' (show a.val < 2^64 from a.bv.isLt) (show b.val < 2^64 from b.bv.isLt); exact hh)
  obtain ⟨r, hr, hrv⟩ := reduce_wide ⟨(UScalar.cast .U128 a).bv * (UScalar.cast .U128 b).bv⟩
  refine ⟨UScalar.cast .U64 r, ?_, ?_⟩
  · simp only [mul, lift_eq_ok, bind_eq_result_bind, Result.bind, hs, hr]
  · rw [hrv, hv, ha, hb]

private theorem reduce_limb (b : U64) :
    ∃ bm : U64, (b % GOLDILOCKS_P : Result U64) = .ok bm ∧
      bm.val = b.val % 18446744069414584321 := by
  have hp : GOLDILOCKS_P.val = 18446744069414584321 := by unfold GOLDILOCKS_P; rfl
  refine ⟨⟨b.bv % GOLDILOCKS_P.bv⟩, ?_, ?_⟩
  · simp only [hMod_uscalar_eq, hp]; rfl
  · change (b.bv % GOLDILOCKS_P.bv).toNat = _
    rw [BitVec.toNat_umod]
    exact congrArg (b.val % ·) hp

private theorem subtract_limb (a b : U64) (h : b.val ≤ a.val) :
    ∃ r, (a - b : Result U64) = .ok r ∧ r.val = a.val - b.val := by
  refine ⟨⟨a.bv - b.bv⟩, ?_, ?_⟩
  · simp only [hSub_uscalar_eq, h, ↓reduceIte]
  · exact BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)

theorem sub_modular_spec (a b : U64) :
    ∃ r, sub a b = .ok r ∧ r.val =
      (a.val + (18446744069414584321 - b.val % 18446744069414584321)) % 18446744069414584321 := by
  have hp : GOLDILOCKS_P.val = 18446744069414584321 := by unfold GOLDILOCKS_P; rfl
  obtain ⟨bm, hr, hbm⟩ := reduce_limb b
  obtain ⟨neg, hn, hnv⟩ := subtract_limb GOLDILOCKS_P bm (by
    rw [hp, hbm]
    exact Nat.le_of_lt (Nat.mod_lt _ (by decide)))
  obtain ⟨r, ha, hav⟩ := add_modular_spec a neg
  refine ⟨r, ?_, ?_⟩
  · simp only [sub, hr, bind_eq_result_bind, result_bind_ok, hn, ha]
  · have hnval : neg.val = 18446744069414584321 - b.val % 18446744069414584321 :=
      hnv.trans ((congrArg (fun t => t - bm.val) hp).trans (congrArg (fun t => 18446744069414584321 - t) hbm))
    exact hav.trans (congrArg (fun t => (a.val + t) % 18446744069414584321) hnval)

@[expose] def fieldAdd (a b : U64) : U64 := UScalar.ofNat .U64 ((a.val+b.val) % 18446744069414584321)
@[expose] def fieldSub (a b : U64) : U64 := UScalar.ofNat .U64 ((a.val+(18446744069414584321-b.val%18446744069414584321)) % 18446744069414584321)
@[expose] def fieldMul (a b : U64) : U64 := UScalar.ofNat .U64 ((a.val*b.val) % 18446744069414584321)

private theorem canonical_ofNat (x : Nat) :
    (UScalar.ofNat .U64 (x % 18446744069414584321)).val = x % 18446744069414584321 := by
  rw [UScalar.val_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))

theorem add_refines (a b : U64) : add a b = .ok (fieldAdd a b) := by
  obtain ⟨r, hr, hv⟩ := add_modular_spec a b
  rw [hr]
  congr 1
  apply UScalar.eq_of_val_eq
  exact hv.trans (canonical_ofNat _).symm

theorem sub_refines (a b : U64) : sub a b = .ok (fieldSub a b) := by
  obtain ⟨r, hr, hv⟩ := sub_modular_spec a b
  rw [hr]
  congr 1
  apply UScalar.eq_of_val_eq
  exact hv.trans (canonical_ofNat _).symm

theorem mul_refines (a b : U64) : mul a b = .ok (fieldMul a b) := by
  obtain ⟨r, hr, hv⟩ := mul_modular_spec a b
  rw [hr]
  congr 1
  apply UScalar.eq_of_val_eq
  exact hv.trans (canonical_ofNat _).symm

attribute [irreducible] fieldAdd fieldSub fieldMul

@[expose] def extAdd (x y : Ext4) : Ext4 :=
  ⟨fieldAdd x.a y.a, fieldAdd x.b y.b, fieldAdd x.c y.c, fieldAdd x.d y.d⟩
@[expose] def extSub (x y : Ext4) : Ext4 :=
  ⟨fieldSub x.a y.a, fieldSub x.b y.b, fieldSub x.c y.c, fieldSub x.d y.d⟩
@[expose] def extScale (x : Ext4) (s : U64) : Ext4 :=
  ⟨fieldMul x.a s, fieldMul x.b s, fieldMul x.c s, fieldMul x.d s⟩
/-- Multiplication in polynomial order modulo u to the fourth minus seven. -/
@[expose] def extMul (x y : Ext4) : Ext4 :=
  ⟨fieldAdd (fieldMul x.a y.a) (fieldMul 7#u64 (fieldAdd (fieldAdd (fieldMul x.b y.d) (fieldMul x.c y.c)) (fieldMul x.d y.b))),
   fieldAdd (fieldAdd (fieldMul x.a y.b) (fieldMul x.b y.a)) (fieldMul 7#u64 (fieldAdd (fieldMul x.c y.d) (fieldMul x.d y.c))),
   fieldAdd (fieldAdd (fieldAdd (fieldMul x.a y.c) (fieldMul x.b y.b)) (fieldMul x.c y.a)) (fieldMul 7#u64 (fieldMul x.d y.d)),
   fieldAdd (fieldAdd (fieldMul x.a y.d) (fieldMul x.b y.c)) (fieldAdd (fieldMul x.c y.b) (fieldMul x.d y.a))⟩

theorem ext_add_refines (x y : Ext4) : ext_add x y = .ok (extAdd x y) := by
  simp [ext_add, extAdd, add_refines, Result.bind]
theorem ext_sub_refines (x y : Ext4) : ext_sub x y = .ok (extSub x y) := by
  simp [ext_sub, extSub, sub_refines, Result.bind]
theorem ext_scale_refines (x : Ext4) (y : U64) : ext_scale x y = .ok (extScale x y) := by
  simp [ext_scale, extScale, mul_refines, Result.bind]
theorem ext_mul_refines (x y : Ext4) : ext_mul x y = .ok (extMul x y) := by
  simp [ext_mul, extMul, mul_refines, add_refines, Result.bind]

attribute [irreducible] extAdd extSub extScale extMul

/-- Total mathematical duet expression, with modular operations on natural-number limbs. -/
@[expose] def duetValue (v0 v1 : Ext4) (iy it : U64) (alpha : Ext4) : Ext4 :=
  extAdd (extScale (extSub v0 v1) iy) (extMul alpha (extScale (extAdd v0 v1) it))

theorem duet_refines (v0 v1 : Ext4) (iy it : U64) (alpha : Ext4) :
    duet_fold v0 v1 iy it alpha = .ok (duetValue v0 v1 iy it alpha) := by
  simp only [duet_fold, duetValue, affine_combine, add_refines,
    ext_sub_refines, ext_scale_refines, ext_mul_refines, ext_add_refines, bind_eq_result_bind, Result.bind]
  simp only [extAdd]

@[expose] def cwyzValue (v0 v1 : Ext4) (iy it yy : U64) (theta alpha beta : Ext4) : Ext4 :=
  let even := extScale (extAdd v0 v1) it
  let odd := extScale (extSub v0 v1) iy
  extAdd odd (extMul (extAdd alpha (extScale beta yy)) (extAdd even (extMul theta odd)))

theorem cwyz_duet_refines (v0 v1 : Ext4) (iy it yy : U64) (theta alpha beta : Ext4) :
    cwyz_duet_fold v0 v1 iy it yy theta alpha beta = .ok (cwyzValue v0 v1 iy it yy theta alpha beta) := by
  simp only [cwyz_duet_fold, cwyzValue, affine_combine,
    ext_sub_refines, ext_scale_refines, ext_mul_refines, ext_add_refines, bind_eq_result_bind, Result.bind]
end qsag_whir_verified.proofs

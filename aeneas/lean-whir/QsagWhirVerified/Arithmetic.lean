module
import Qsag.Tactic.AssuranceKit
public import QsagWhirVerified.Types
public import QsagWhirVerified.Funs
public import Aeneas
public import Aeneas.Std.Types
public import Aeneas.Std.Containers
public section
open Aeneas Aeneas.Std
set_option linter.unusedSimpArgs false

namespace qsag_whir_verified

@[ext]
theorem Fp5.ext {x y : Fp5}
    (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1) (h2 : x.c2 = y.c2)
    (h3 : x.c3 = y.c3) (h4 : x.c4 = y.c4) : x = y := by
  cases x; cases y; subst h0 h1 h2 h3 h4; rfl

instance : DecidableEq Fp5 := fun x y =>
  match decEq x.c0 y.c0 with
  | isFalse h => isFalse (fun e => h (congrArg Fp5.c0 e))
  | isTrue h0 =>
    match decEq x.c1 y.c1 with
    | isFalse h => isFalse (fun e => h (congrArg Fp5.c1 e))
    | isTrue h1 =>
      match decEq x.c2 y.c2 with
      | isFalse h => isFalse (fun e => h (congrArg Fp5.c2 e))
      | isTrue h2 =>
        match decEq x.c3 y.c3 with
        | isFalse h => isFalse (fun e => h (congrArg Fp5.c3 e))
        | isTrue h3 =>
          match decEq x.c4 y.c4 with
          | isFalse h => isFalse (fun e => h (congrArg Fp5.c4 e))
          | isTrue h4 => isTrue (Fp5.ext h0 h1 h2 h3 h4)

@[ext]
theorem MerklePair400.ext {x y : MerklePair400}
    (hl : x.left = y.left) (hr : x.right = y.right) : x = y := by
  cases x; cases y; subst hl hr; rfl

instance : DecidableEq MerklePair400 := fun x y =>
  match decEq x.left y.left with
  | isFalse h => isFalse (fun e => h (congrArg MerklePair400.left e))
  | isTrue hl =>
    match decEq x.right y.right with
    | isFalse h => isFalse (fun e => h (congrArg MerklePair400.right e))
    | isTrue hr => isTrue (MerklePair400.ext hl hr)

@[ext]
theorem Gl24Digest.ext {x y : Gl24Digest}
    (h0 : x.l0 = y.l0) (h1 : x.l1 = y.l1) (h2 : x.l2 = y.l2) (h3 : x.l3 = y.l3)
    (h4 : x.l4 = y.l4) (h5 : x.l5 = y.l5) (h6 : x.l6 = y.l6) : x = y := by
  cases x; cases y; subst h0 h1 h2 h3 h4 h5 h6; rfl

instance : DecidableEq Gl24Digest := fun x y =>
  match decEq x.l0 y.l0 with
  | isFalse h => isFalse (fun e => h (congrArg Gl24Digest.l0 e))
  | isTrue h0 =>
    match decEq x.l1 y.l1 with
    | isFalse h => isFalse (fun e => h (congrArg Gl24Digest.l1 e))
    | isTrue h1 =>
      match decEq x.l2 y.l2 with
      | isFalse h => isFalse (fun e => h (congrArg Gl24Digest.l2 e))
      | isTrue h2 =>
        match decEq x.l3 y.l3 with
        | isFalse h => isFalse (fun e => h (congrArg Gl24Digest.l3 e))
        | isTrue h3 =>
          match decEq x.l4 y.l4 with
          | isFalse h => isFalse (fun e => h (congrArg Gl24Digest.l4 e))
          | isTrue h4 =>
            match decEq x.l5 y.l5 with
            | isFalse h => isFalse (fun e => h (congrArg Gl24Digest.l5 e))
            | isTrue h5 =>
              match decEq x.l6 y.l6 with
              | isFalse h => isFalse (fun e => h (congrArg Gl24Digest.l6 e))
              | isTrue h6 => isTrue (Gl24Digest.ext h0 h1 h2 h3 h4 h5 h6)

@[ext]
theorem MerklePairGl24.ext {x y : MerklePairGl24}
    (hl : x.left = y.left) (hr : x.right = y.right) : x = y := by
  cases x; cases y; subst hl hr; rfl

instance : DecidableEq MerklePairGl24 := fun x y =>
  match decEq x.left y.left with
  | isFalse h => isFalse (fun e => h (congrArg MerklePairGl24.left e))
  | isTrue hl =>
    match decEq x.right y.right with
    | isFalse h => isFalse (fun e => h (congrArg MerklePairGl24.right e))
    | isTrue hr => isTrue (MerklePairGl24.ext hl hr)

@[ext]
theorem Qsaghqm2Header.ext {x y : Qsaghqm2Header}
    (hp : x.profile_tag = y.profile_tag)
    (ha : x.active_signers = y.active_signers)
    (hl : x.payload_len = y.payload_len) : x = y := by
  cases x; cases y; subst hp ha hl; rfl

instance : DecidableEq Qsaghqm2Header := fun x y =>
  match decEq x.profile_tag y.profile_tag with
  | isFalse h => isFalse (fun e => h (congrArg Qsaghqm2Header.profile_tag e))
  | isTrue hp =>
    match decEq x.active_signers y.active_signers with
    | isFalse h => isFalse (fun e => h (congrArg Qsaghqm2Header.active_signers e))
    | isTrue ha =>
      match decEq x.payload_len y.payload_len with
      | isFalse h => isFalse (fun e => h (congrArg Qsaghqm2Header.payload_len e))
      | isTrue hl => isTrue (Qsaghqm2Header.ext hp ha hl)

end qsag_whir_verified

namespace qsag_whir_verified.proofs

abbrev goldilocksMod : Nat := 18446744069414584321

theorem goldilocks_p_val : GOLDILOCKS_P.val = 18446744069414584321 := by
  simp only [GOLDILOCKS_P.public_eqs]
  rfl

theorem max_u64_word_val : MAX_U64_WORD.val = 18446744073709551615 := by
  simp only [MAX_U64_WORD.public_eqs]
  rfl

theorem fp5_nonresidue_w_val : FP5_NONRESIDUE_W = 3#u64 := by
  simp only [FP5_NONRESIDUE_W.public_eqs]

theorem frobenius_zeta5_1_val : FROBENIUS_ZETA5_1 = 1041288259238279555#u64 := by
  simp only [FROBENIUS_ZETA5_1.public_eqs]

theorem frobenius_zeta5_2_val : FROBENIUS_ZETA5_2 = 15820824984080659046#u64 := by
  simp only [FROBENIUS_ZETA5_2.public_eqs]

theorem frobenius_zeta5_3_val : FROBENIUS_ZETA5_3 = 211587555138949697#u64 := by
  simp only [FROBENIUS_ZETA5_3.public_eqs]

theorem frobenius_zeta5_4_val : FROBENIUS_ZETA5_4 = 1373043270956696022#u64 := by
  simp only [FROBENIUS_ZETA5_4.public_eqs]

theorem qsaghqm2_profile_turbo400_val : QSAGHQM2_PROFILE_TURBO400 = 1#u8 := by
  simp only [QSAGHQM2_PROFILE_TURBO400.public_eqs]

theorem qsaghqm2_profile_gl24_val : QSAGHQM2_PROFILE_GL24 = 2#u8 := by
  simp only [QSAGHQM2_PROFILE_GL24.public_eqs]

theorem min_quintic_log_cells_val : MIN_QUINTIC_LOG_CELLS = 16#u32 := by
  simp only [MIN_QUINTIC_LOG_CELLS.public_eqs]

theorem max_quintic_log_cells_val : MAX_QUINTIC_LOG_CELLS = 28#u32 := by
  simp only [MAX_QUINTIC_LOG_CELLS.public_eqs]

theorem max_canopy_log_leaves_val : MAX_CANOPY_LOG_LEAVES = 28#u32 := by
  simp only [MAX_CANOPY_LOG_LEAVES.public_eqs]

theorem copy_fp5_spec (x : Fp5) : copy_fp5 x = .ok x := by
  simp only [copy_fp5.public_eqs]

abbrev IsCanonical (x : U64) : Prop := x.val < 18446744069414584321

abbrev IsCanonicalFp5 (x : Fp5) : Prop :=
  IsCanonical x.c0 ∧ IsCanonical x.c1 ∧ IsCanonical x.c2 ∧ IsCanonical x.c3 ∧ IsCanonical x.c4

abbrev IsCanonicalGl24 (d : Gl24Digest) : Prop :=
  IsCanonical d.l0 ∧ IsCanonical d.l1 ∧ IsCanonical d.l2 ∧ IsCanonical d.l3 ∧
  IsCanonical d.l4 ∧ IsCanonical d.l5 ∧ IsCanonical d.l6

/-- Pure little-endian 8-byte word assembly at byte offset `off`. -/
@[expose] def lePackU64At (bs : List U8) (off : Nat) : U64 :=
  ⟨(UScalar.cast .U64 (bs.getD off 0#u8)).bv |||
    ((UScalar.cast .U64 (bs.getD (off + 1) 0#u8)).bv <<< 8) |||
    ((UScalar.cast .U64 (bs.getD (off + 2) 0#u8)).bv <<< 16) |||
    ((UScalar.cast .U64 (bs.getD (off + 3) 0#u8)).bv <<< 24) |||
    ((UScalar.cast .U64 (bs.getD (off + 4) 0#u8)).bv <<< 32) |||
    ((UScalar.cast .U64 (bs.getD (off + 5) 0#u8)).bv <<< 40) |||
    ((UScalar.cast .U64 (bs.getD (off + 6) 0#u8)).bv <<< 48) |||
    ((UScalar.cast .U64 (bs.getD (off + 7) 0#u8)).bv <<< 56)⟩

/-! ## Scalar Width-Cast and Checked `U128` Arithmetic Lemmas -/

theorem u64_cast_u128_val (x : Std.U64) :
    (UScalar.cast .U128 x).val = x.val := by
  have hx : x.val < 2 ^ 64 := x.bv.isLt
  have hx128 : x.val < 2 ^ 128 := Nat.lt_of_lt_of_le hx (by decide)
  rw [UScalar.cast_val]
  exact Nat.mod_eq_of_lt hx128

theorem u128_cast_u64_val_of_lt (x : Std.U128) (h : x.val < 2 ^ 64) :
    (UScalar.cast .U64 x).val = x.val := by
  rw [UScalar.cast_val]
  exact Nat.mod_eq_of_lt h

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
    rw [UScalar.cast_val, goldilocks_p_val]
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
  · simp only [add.public_eqs, lift_eq_ok, bind_eq_result_bind, Result.bind, hs, hr]
  · rw [hrv, hv, ha, hb]

theorem mul_modular_spec (a b : U64) :
    ∃ r, mul a b = .ok r ∧ r.val = (a.val * b.val) % 18446744069414584321 := by
  have ha := u64_cast_u128_val a
  have hb := u64_cast_u128_val b
  obtain ⟨hs, hv⟩ := u128_mul_ok (a := UScalar.cast .U128 a) (b := UScalar.cast .U128 b)
    (by
      rw [ha, hb]
      exact Nat.lt_of_lt_of_eq (Nat.mul_lt_mul'' a.bv.isLt b.bv.isLt) (by decide))
  obtain ⟨r, hr, hrv⟩ := reduce_wide ⟨(UScalar.cast .U128 a).bv * (UScalar.cast .U128 b).bv⟩
  refine ⟨UScalar.cast .U64 r, ?_, ?_⟩
  · simp only [mul.public_eqs, lift_eq_ok, bind_eq_result_bind, Result.bind, hs, hr]
  · rw [hrv, hv, ha, hb]

private theorem reduce_limb (b : U64) :
    (b % GOLDILOCKS_P : Result U64) = .ok (UScalar.ofNat .U64 (b.val % 18446744069414584321)) := by
  have hp : GOLDILOCKS_P.val = 18446744069414584321 := goldilocks_p_val
  have hne : ¬(18446744069414584321 = 0) := by decide
  simp only [hMod_uscalar_eq, hp, hne, ↓reduceIte, Result.ok.injEq]
  apply UScalar.eq_of_val_eq
  change (b.bv % GOLDILOCKS_P.bv).toNat = _
  rw [BitVec.toNat_umod]
  change b.val % GOLDILOCKS_P.val = _
  rw [hp, UScalar.val_ofNat]
  exact (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))).symm

private theorem subtract_limb (a b : U64) (h : b.val ≤ a.val) :
    ∃ r, (a - b : Result U64) = .ok r ∧ r.val = a.val - b.val := by
  refine ⟨⟨a.bv - b.bv⟩, ?_, ?_⟩
  · simp only [hSub_uscalar_eq, h, ↓reduceIte]
  · exact BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)

theorem sub_modular_spec (a b : U64) :
    ∃ r, sub a b = .ok r ∧ r.val =
      (a.val + (18446744069414584321 - b.val % 18446744069414584321)) % 18446744069414584321 := by
  have hp : GOLDILOCKS_P.val = 18446744069414584321 := goldilocks_p_val
  let bm : U64 := UScalar.ofNat .U64 (b.val % 18446744069414584321)
  have hr : (b % GOLDILOCKS_P : Result U64) = .ok bm := reduce_limb b
  have hbm : bm.val = b.val % 18446744069414584321 := by
    dsimp only [bm]; rw [UScalar.val_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))
  obtain ⟨neg, hn, hnv⟩ := subtract_limb GOLDILOCKS_P bm (by
    rw [hp, hbm]
    exact Nat.le_of_lt (Nat.mod_lt _ (by decide)))
  obtain ⟨r, ha, hav⟩ := add_modular_spec a neg
  refine ⟨r, ?_, ?_⟩
  · simp only [sub.public_eqs, hr, bind_eq_result_bind, result_bind_ok, hn, ha]
  · have hnval : neg.val = 18446744069414584321 - b.val % 18446744069414584321 :=
      hnv.trans ((congrArg (fun t => t - bm.val) hp).trans (congrArg (fun t => 18446744069414584321 - t) hbm))
    exact hav.trans (congrArg (fun t => (a.val + t) % 18446744069414584321) hnval)

/-! ## Pure Goldilocks Field Operations & `Int`-Modular Commutative Ring Laws -/

@[expose] def fieldAdd (a b : U64) : U64 :=
  UScalar.ofNat .U64 ((a.val + b.val) % 18446744069414584321)

@[expose] def fieldSub (a b : U64) : U64 :=
  UScalar.ofNat .U64 ((a.val + (18446744069414584321 - b.val % 18446744069414584321)) % 18446744069414584321)

@[expose] def fieldMul (a b : U64) : U64 :=
  UScalar.ofNat .U64 ((a.val * b.val) % 18446744069414584321)

private theorem canonical_ofNat (x : Nat) :
    (UScalar.ofNat .U64 (x % 18446744069414584321)).val = x % 18446744069414584321 := by
  rw [UScalar.val_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))

theorem fieldAdd_val (a b : U64) : (fieldAdd a b).val = (a.val + b.val) % 18446744069414584321 :=
  canonical_ofNat (a.val + b.val)

theorem fieldSub_val (a b : U64) :
    (fieldSub a b).val = (a.val + (18446744069414584321 - b.val % 18446744069414584321)) % 18446744069414584321 :=
  canonical_ofNat _

theorem fieldMul_val (a b : U64) : (fieldMul a b).val = (a.val * b.val) % 18446744069414584321 :=
  canonical_ofNat (a.val * b.val)

theorem fieldAdd_canonical (a b : U64) : IsCanonical (fieldAdd a b) := by
  rw [IsCanonical, fieldAdd_val]
  exact Nat.mod_lt _ (by decide)

theorem fieldSub_canonical (a b : U64) : IsCanonical (fieldSub a b) := by
  rw [IsCanonical, fieldSub_val]
  exact Nat.mod_lt _ (by decide)

theorem fieldMul_canonical (a b : U64) : IsCanonical (fieldMul a b) := by
  rw [IsCanonical, fieldMul_val]
  exact Nat.mod_lt _ (by decide)

theorem add_refines (a b : U64) : add a b = .ok (fieldAdd a b) := by
  obtain ⟨r, hr, hv⟩ := add_modular_spec a b
  rw [hr]
  congr 1
  apply UScalar.eq_of_val_eq
  exact hv.trans (fieldAdd_val a b).symm

theorem sub_refines (a b : U64) : sub a b = .ok (fieldSub a b) := by
  obtain ⟨r, hr, hv⟩ := sub_modular_spec a b
  rw [hr]
  congr 1
  apply UScalar.eq_of_val_eq
  exact hv.trans (fieldSub_val a b).symm

theorem mul_refines (a b : U64) : mul a b = .ok (fieldMul a b) := by
  obtain ⟨r, hr, hv⟩ := mul_modular_spec a b
  rw [hr]
  congr 1
  apply UScalar.eq_of_val_eq
  exact hv.trans (fieldMul_val a b).symm

/-! ### Constructive `Int`-Modular Projection & Structural Horner Ring Normalizer -/

private def toZ (x : U64) : Int := (x.val : Int)

private def modP (z : Int) : U64 :=
  UScalar.ofNat .U64 (z % (18446744069414584321 : Int)).toNat

private theorem nat_mul_toInt (a b : Nat) :
    ((a * b : Nat) : Int) = (a : Int) * (b : Int) := by
  induction a with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul]
    have h1 : ((k * b + b : Nat) : Int) = ((k * b : Nat) : Int) + (b : Int) := by omega
    have h2 : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
    rw [h1, ih, h2, Int.add_mul, Int.one_mul]

private theorem modP_val (z : Int) :
    (modP z).val = (z % (18446744069414584321 : Int)).toNat := by
  unfold modP
  rw [UScalar.val_ofNat]
  have hlt : z % (18446744069414584321 : Int) < 18446744069414584321 :=
    Int.emod_lt_of_pos z (by decide)
  have hnat : (z % (18446744069414584321 : Int)).toNat < 2 ^ 64 := by omega
  exact Nat.mod_eq_of_lt hnat

private theorem toZ_modP (z : Int) :
    toZ (modP z) = z % (18446744069414584321 : Int) := by
  unfold toZ
  rw [modP_val]
  have hnn : 0 ≤ z % (18446744069414584321 : Int) := Int.emod_nonneg z (by decide)
  omega

private theorem modP_toZ_of_canonical {x : U64} (hx : IsCanonical x) :
    modP (toZ x) = x := by
  apply UScalar.eq_of_val_eq
  rw [modP_val]
  unfold toZ
  have hx' : x.val < 18446744069414584321 := hx
  omega

private theorem fieldAdd_eq_modP (a b : U64) :
    fieldAdd a b = modP (toZ a + toZ b) := by
  apply UScalar.eq_of_val_eq
  rw [fieldAdd_val, modP_val]
  unfold toZ
  omega

private theorem fieldSub_eq_modP (a b : U64) :
    fieldSub a b = modP (toZ a - toZ b) := by
  apply UScalar.eq_of_val_eq
  rw [fieldSub_val, modP_val]
  unfold toZ
  omega

private theorem fieldMul_eq_modP (a b : U64) :
    fieldMul a b = modP (toZ a * toZ b) := by
  apply UScalar.eq_of_val_eq
  rw [fieldMul_val, modP_val]
  unfold toZ
  have hm := nat_mul_toInt a.val b.val
  have hmod : (((a.val * b.val) % 18446744069414584321 : Nat) : Int) =
      ((a.val * b.val : Nat) : Int) % (18446744069414584321 : Int) := by omega
  omega

private theorem modP_add_left (x y : Int) :
    modP (x % (18446744069414584321 : Int) + y) = modP (x + y) := by
  apply UScalar.eq_of_val_eq
  rw [modP_val, modP_val]
  have h : (x % (18446744069414584321 : Int) + y) % (18446744069414584321 : Int) =
      (x + y) % (18446744069414584321 : Int) := by
    rw [Int.add_emod (x % _), Int.emod_emod, ← Int.add_emod]
  rw [h]

private theorem modP_add_right (x y : Int) :
    modP (x + y % (18446744069414584321 : Int)) = modP (x + y) := by
  apply UScalar.eq_of_val_eq
  rw [modP_val, modP_val]
  have h : (x + y % (18446744069414584321 : Int)) % (18446744069414584321 : Int) =
      (x + y) % (18446744069414584321 : Int) := by
    rw [Int.add_emod x (y % _), Int.emod_emod, ← Int.add_emod]
  rw [h]

private theorem modP_sub_left (x y : Int) :
    modP (x % (18446744069414584321 : Int) - y) = modP (x - y) := by
  apply UScalar.eq_of_val_eq
  rw [modP_val, modP_val]
  have h : (x % (18446744069414584321 : Int) - y) % (18446744069414584321 : Int) =
      (x - y) % (18446744069414584321 : Int) := by
    rw [Int.sub_emod (x % _), Int.emod_emod, ← Int.sub_emod]
  rw [h]

private theorem modP_sub_right (x y : Int) :
    modP (x - y % (18446744069414584321 : Int)) = modP (x - y) := by
  apply UScalar.eq_of_val_eq
  rw [modP_val, modP_val]
  have h : (x - y % (18446744069414584321 : Int)) % (18446744069414584321 : Int) =
      (x - y) % (18446744069414584321 : Int) := by
    rw [Int.sub_emod x (y % _), Int.emod_emod, ← Int.sub_emod]
  rw [h]

private theorem modP_mul_left (x y : Int) :
    modP (x % (18446744069414584321 : Int) * y) = modP (x * y) := by
  apply UScalar.eq_of_val_eq
  rw [modP_val, modP_val]
  have h : (x % (18446744069414584321 : Int) * y) % (18446744069414584321 : Int) =
      (x * y) % (18446744069414584321 : Int) := by
    rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
  rw [h]

private theorem modP_mul_right (x y : Int) :
    modP (x * (y % (18446744069414584321 : Int))) = modP (x * y) := by
  apply UScalar.eq_of_val_eq
  rw [modP_val, modP_val]
  have h : (x * (y % (18446744069414584321 : Int))) % (18446744069414584321 : Int) =
      (x * y) % (18446744069414584321 : Int) := by
    rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
  rw [h]

/-- Constructive sorted sum-of-monomials (`SOP`) normalizer over `Int` using strictly
    single-argument structural recursion on `List` so `FExpr.norm` reduces by kernel WHNF (`rfl`)
    with `0` choice and `0` well-founded recursion. -/
private abbrev Mono := List Nat

private def evalMono (env : Nat → Int) : Mono → Int
  | [] => 1
  | v :: vs => env v * evalMono env vs

private def insertVar (v : Nat) : Mono → Mono
  | [] => [v]
  | u :: us => if v ≤ u then v :: u :: us else u :: insertVar v us

private theorem evalMono_insertVar (env : Nat → Int) (v : Nat) :
    ∀ (m : Mono), evalMono env (insertVar v m) = env v * evalMono env m
  | [] => rfl
  | u :: us => by
    unfold insertVar
    by_cases h : v ≤ u
    · simp only [h, ↓reduceIte, evalMono]
    · simp only [h, ↓reduceIte, evalMono, evalMono_insertVar env v us]
      rw [← Int.mul_assoc (env u) (env v) (evalMono env us),
          Int.mul_comm (env u) (env v),
          Int.mul_assoc (env v) (env u) (evalMono env us)]

private def monoMul : Mono → Mono → Mono
  | [], ys => ys
  | x :: xs, ys => insertVar x (monoMul xs ys)

private theorem evalMono_monoMul (env : Nat → Int) :
    ∀ (xs ys : Mono), evalMono env (monoMul xs ys) = evalMono env xs * evalMono env ys
  | [], ys => (Int.one_mul _).symm
  | x :: xs, ys => by
    simp only [monoMul, evalMono_insertVar, evalMono, evalMono_monoMul env xs ys, Int.mul_assoc]

private def monoLt : Mono → Mono → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x < y then true else if y < x then false else monoLt xs ys

private abbrev SOP := List (Int × Mono)

private def evalSOP (env : Nat → Int) : SOP → Int
  | [] => 0
  | (c, m) :: rest => c * evalMono env m + evalSOP env rest

private def sopInsert (c : Int) (m : Mono) : SOP → SOP
  | [] => if c = 0 then [] else [(c, m)]
  | (d, n) :: rest =>
    if c = 0 then (d, n) :: rest
    else if m = n then
      if c + d = 0 then rest else (c + d, m) :: rest
    else if monoLt m n then
      (c, m) :: (d, n) :: rest
    else
      (d, n) :: sopInsert c m rest

private theorem evalSOP_sopInsert (env : Nat → Int) (c : Int) (m : Mono) :
    ∀ (s : SOP), evalSOP env (sopInsert c m s) = c * evalMono env m + evalSOP env s
  | [] => by
    unfold sopInsert
    by_cases hc : c = 0
    · subst hc; simp [evalSOP]
    · simp [hc, evalSOP]
  | (d, n) :: rest => by
    unfold sopInsert
    by_cases hc : c = 0
    · subst hc; simp [evalSOP]
    · simp only [hc, ↓reduceIte]
      by_cases hmn : m = n
      · subst hmn
        simp only [↓reduceIte]
        by_cases hcd : c + d = 0
        · simp only [hcd, ↓reduceIte, evalSOP]
          have h0 : (c + d) * evalMono env m = 0 := by rw [hcd, Int.zero_mul]
          rw [Int.add_mul] at h0
          omega
        · simp only [hcd, ↓reduceIte, evalSOP, Int.add_mul]
          omega
      · simp only [hmn, ↓reduceIte]
        cases hlt : monoLt m n with
        | true => simp only [↓reduceIte, evalSOP]
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, evalSOP, evalSOP_sopInsert env c m rest]
          omega

private def sopAdd : SOP → SOP → SOP
  | [], q => q
  | (c, m) :: p, q => sopInsert c m (sopAdd p q)

private theorem evalSOP_sopAdd (env : Nat → Int) :
    ∀ (p q : SOP), evalSOP env (sopAdd p q) = evalSOP env p + evalSOP env q
  | [], q => by simp [sopAdd, evalSOP]
  | (c, m) :: p, q => by
    simp only [sopAdd, evalSOP_sopInsert, evalSOP, evalSOP_sopAdd env p q]
    omega

private def sopNeg : SOP → SOP
  | [] => []
  | (c, m) :: p => sopInsert (-c) m (sopNeg p)

private theorem evalSOP_sopNeg (env : Nat → Int) :
    ∀ (p : SOP), evalSOP env (sopNeg p) = -(evalSOP env p)
  | [] => rfl
  | (c, m) :: p => by
    simp only [sopNeg, evalSOP_sopInsert, evalSOP, evalSOP_sopNeg env p, Int.neg_mul]
    omega

private def sopMulTerm (c : Int) (m : Mono) : SOP → SOP
  | [] => []
  | (d, n) :: q => sopInsert (c * d) (monoMul m n) (sopMulTerm c m q)

private theorem evalSOP_sopMulTerm (env : Nat → Int) (c : Int) (m : Mono) :
    ∀ (q : SOP), evalSOP env (sopMulTerm c m q) = c * evalMono env m * evalSOP env q
  | [] => by simp [sopMulTerm, evalSOP]
  | (d, n) :: q => by
    simp only [sopMulTerm, evalSOP_sopInsert, evalMono_monoMul, evalSOP, evalSOP_sopMulTerm env c m q]
    have hmul : (c * d) * (evalMono env m * evalMono env n) =
        (c * evalMono env m) * (d * evalMono env n) := by
      calc
        (c * d) * (evalMono env m * evalMono env n)
            = c * (d * (evalMono env m * evalMono env n)) := Int.mul_assoc _ _ _
        _ = c * (d * evalMono env m * evalMono env n) := by rw [← Int.mul_assoc d]
        _ = c * (evalMono env m * d * evalMono env n) := by rw [Int.mul_comm d (evalMono env m)]
        _ = c * (evalMono env m * (d * evalMono env n)) := by rw [Int.mul_assoc (evalMono env m)]
        _ = (c * evalMono env m) * (d * evalMono env n) := (Int.mul_assoc _ _ _).symm
    rw [hmul, Int.mul_add]

private def sopMul : SOP → SOP → SOP
  | [], _ => []
  | (c, m) :: p, q => sopAdd (sopMulTerm c m q) (sopMul p q)

private theorem evalSOP_sopMul (env : Nat → Int) :
    ∀ (p q : SOP), evalSOP env (sopMul p q) = evalSOP env p * evalSOP env q
  | [], _ => by simp [sopMul, evalSOP]
  | (c, m) :: p, q => by
    simp only [sopMul, evalSOP_sopAdd, evalSOP_sopMulTerm, evalSOP, evalSOP_sopMul env p q, Int.add_mul]

private theorem modP_emod (z : Int) :
    modP (z % (18446744069414584321 : Int)) = modP z := by
  apply UScalar.eq_of_val_eq
  rw [modP_val, modP_val, Int.emod_emod]

/-- Small canonical field constants (`0`, `1`, `2`, `3`) for `F_p[X]/(X^5 - 3)`. -/
private inductive FConst where
  | c0 | c1 | c2 | c3

private def FConst.toU64 : FConst → U64
  | .c0 => 0#u64 | .c1 => 1#u64 | .c2 => 2#u64 | .c3 => 3#u64

private def FConst.toInt : FConst → Int
  | .c0 => 0 | .c1 => 1 | .c2 => 2 | .c3 => 3

private theorem FConst.toZ_toU64 (k : FConst) : toZ k.toU64 = k.toInt := by
  cases k <;> rfl

private theorem FConst.canonical (k : FConst) : IsCanonical k.toU64 := by
  unfold FConst.toU64 IsCanonical
  cases k <;> decide

private inductive FExpr where
  | const : FConst → FExpr
  | var : Nat → FExpr
  | add : FExpr → FExpr → FExpr
  | sub : FExpr → FExpr → FExpr
  | mul : FExpr → FExpr → FExpr

private def FExpr.norm : FExpr → SOP
  | .const k => sopInsert k.toInt [] []
  | .var i => [(1, [i])]
  | .add a b => sopAdd a.norm b.norm
  | .sub a b => sopAdd a.norm (sopNeg b.norm)
  | .mul a b => sopMul a.norm b.norm

private def FExpr.evalF (env : Nat → U64) : FExpr → U64
  | .const k => k.toU64
  | .var i => env i
  | .add a b => fieldAdd (a.evalF env) (b.evalF env)
  | .sub a b => fieldSub (a.evalF env) (b.evalF env)
  | .mul a b => fieldMul (a.evalF env) (b.evalF env)

private def FExpr.evalZ (env : Nat → U64) : FExpr → Int
  | .const k => k.toInt
  | .var i => toZ (env i)
  | .add a b => a.evalZ env + b.evalZ env
  | .sub a b => a.evalZ env - b.evalZ env
  | .mul a b => a.evalZ env * b.evalZ env

private def FExpr.wf (env : Nat → U64) : FExpr → Prop
  | .const _ => True
  | .var i => IsCanonical (env i)
  | .add _ _ => True
  | .sub _ _ => True
  | .mul _ _ => True

private theorem FExpr.evalF_canonical (env : Nat → U64) :
    ∀ (e : FExpr), e.wf env → IsCanonical (e.evalF env)
  | .const k, _ => k.canonical
  | .var _, h => h
  | .add a b, _ => fieldAdd_canonical (a.evalF env) (b.evalF env)
  | .sub a b, _ => fieldSub_canonical (a.evalF env) (b.evalF env)
  | .mul a b, _ => fieldMul_canonical (a.evalF env) (b.evalF env)

private theorem FExpr.evalSOP_norm (env : Nat → U64) (e : FExpr) :
    evalSOP (fun i => toZ (env i)) e.norm = e.evalZ env := by
  induction e with
  | const _ =>
    simp only [FExpr.norm, FExpr.evalZ, evalSOP_sopInsert, evalMono, evalSOP]
    omega
  | var _ =>
    simp only [FExpr.norm, FExpr.evalZ, evalSOP, evalMono]
    omega
  | add a b iha ihb =>
    simp only [FExpr.norm, FExpr.evalZ, evalSOP_sopAdd, iha, ihb]
  | sub a b iha ihb =>
    simp only [FExpr.norm, FExpr.evalZ, evalSOP_sopAdd, evalSOP_sopNeg, iha, ihb]
    omega
  | mul a b iha ihb =>
    simp only [FExpr.norm, FExpr.evalZ, evalSOP_sopMul, iha, ihb]

private theorem FExpr.toZ_evalF_emod (env : Nat → U64) (e : FExpr) :
    toZ (e.evalF env) % (18446744069414584321 : Int) =
      e.evalZ env % (18446744069414584321 : Int) := by
  induction e with
  | const k => rw [FExpr.evalF, FExpr.evalZ, k.toZ_toU64]
  | var _ => rfl
  | add a b iha ihb =>
    simp only [FExpr.evalF, FExpr.evalZ, fieldAdd_eq_modP, toZ_modP, Int.emod_emod]
    rw [Int.add_emod, iha, ihb, ← Int.add_emod]
  | sub a b iha ihb =>
    simp only [FExpr.evalF, FExpr.evalZ, fieldSub_eq_modP, toZ_modP, Int.emod_emod]
    rw [Int.sub_emod, iha, ihb, ← Int.sub_emod]
  | mul a b iha ihb =>
    simp only [FExpr.evalF, FExpr.evalZ, fieldMul_eq_modP, toZ_modP, Int.emod_emod]
    rw [Int.mul_emod, iha, ihb, ← Int.mul_emod]

private theorem FExpr.evalF_eq_modP (env : Nat → U64) (e : FExpr)
    (hwf : e.wf env) :
    e.evalF env = modP (e.evalZ env) := by
  rw [← modP_toZ_of_canonical (FExpr.evalF_canonical env e hwf),
      ← modP_emod (toZ (e.evalF env)),
      FExpr.toZ_evalF_emod env e, modP_emod]

private theorem FExpr.evalF_eq_of_norm (env : Nat → U64) (lhs rhs : FExpr)
    (hl : lhs.wf env) (hr : rhs.wf env)
    (h : lhs.norm = rhs.norm) :
    lhs.evalF env = rhs.evalF env := by
  rw [FExpr.evalF_eq_modP env lhs hl, FExpr.evalF_eq_modP env rhs hr,
      ← FExpr.evalSOP_norm env lhs, ← FExpr.evalSOP_norm env rhs, h]

private theorem toZ_zero : toZ 0#u64 = 0 := rfl
private theorem toZ_one : toZ 1#u64 = 1 := rfl
private theorem modP_zero : modP 0 = 0#u64 := by
  apply UScalar.eq_of_val_eq; rw [modP_val]; rfl

private theorem fieldAdd_modP_left (x : Int) (b : U64) :
    fieldAdd (modP x) b = modP (x + toZ b) := by
  rw [fieldAdd_eq_modP, toZ_modP, modP_add_left]

private theorem fieldAdd_modP_right (a : U64) (y : Int) :
    fieldAdd a (modP y) = modP (toZ a + y) := by
  rw [fieldAdd_eq_modP, toZ_modP, modP_add_right]

private theorem fieldAdd_modP_both (x y : Int) :
    fieldAdd (modP x) (modP y) = modP (x + y) := by
  rw [fieldAdd_eq_modP, toZ_modP, toZ_modP, modP_add_left, modP_add_right]

private theorem fieldSub_modP_left (x : Int) (b : U64) :
    fieldSub (modP x) b = modP (x - toZ b) := by
  rw [fieldSub_eq_modP, toZ_modP, modP_sub_left]

private theorem fieldSub_modP_right (a : U64) (y : Int) :
    fieldSub a (modP y) = modP (toZ a - y) := by
  rw [fieldSub_eq_modP, toZ_modP, modP_sub_right]

private theorem fieldSub_modP_both (x y : Int) :
    fieldSub (modP x) (modP y) = modP (x - y) := by
  rw [fieldSub_eq_modP, toZ_modP, toZ_modP, modP_sub_left, modP_sub_right]

private theorem fieldMul_modP_left (x : Int) (b : U64) :
    fieldMul (modP x) b = modP (x * toZ b) := by
  rw [fieldMul_eq_modP, toZ_modP, modP_mul_left]

private theorem fieldMul_modP_right (a : U64) (y : Int) :
    fieldMul a (modP y) = modP (toZ a * y) := by
  rw [fieldMul_eq_modP, toZ_modP, modP_mul_right]

/-! ### Exported Goldilocks Commutative Ring & Frobenius Root Theorems -/

theorem fieldAdd_comm (a b : U64) : fieldAdd a b = fieldAdd b a := by
  rw [fieldAdd_eq_modP, fieldAdd_eq_modP, Int.add_comm]

theorem fieldAdd_assoc (a b c : U64) :
    fieldAdd (fieldAdd a b) c = fieldAdd a (fieldAdd b c) := by
  rw [fieldAdd_eq_modP a b, fieldAdd_modP_left, fieldAdd_eq_modP b c, fieldAdd_modP_right, Int.add_assoc]

theorem fieldAdd_zero {a : U64} (ha : IsCanonical a) : fieldAdd a 0#u64 = a := by
  rw [fieldAdd_eq_modP, toZ_zero, Int.add_zero, modP_toZ_of_canonical ha]

theorem zero_fieldAdd {a : U64} (ha : IsCanonical a) : fieldAdd 0#u64 a = a := by
  rw [fieldAdd_comm, fieldAdd_zero ha]

theorem fieldSub_self (a : U64) : fieldSub a a = 0#u64 := by
  rw [fieldSub_eq_modP, Int.sub_self, modP_zero]

theorem fieldAdd_sub_cancel {a : U64} (ha : IsCanonical a) (b : U64) :
    fieldSub (fieldAdd a b) b = a := by
  rw [fieldAdd_eq_modP, fieldSub_modP_left]
  have h : toZ a + toZ b - toZ b = toZ a := by omega
  rw [h, modP_toZ_of_canonical ha]

theorem fieldSub_add_cancel {a : U64} (ha : IsCanonical a) (b : U64) :
    fieldAdd (fieldSub a b) b = a := by
  rw [fieldSub_eq_modP, fieldAdd_modP_left]
  have h : toZ a - toZ b + toZ b = toZ a := by omega
  rw [h, modP_toZ_of_canonical ha]

theorem fieldMul_comm (a b : U64) : fieldMul a b = fieldMul b a := by
  rw [fieldMul_eq_modP, fieldMul_eq_modP, Int.mul_comm]

theorem fieldMul_assoc (a b c : U64) :
    fieldMul (fieldMul a b) c = fieldMul a (fieldMul b c) := by
  rw [fieldMul_eq_modP a b, fieldMul_modP_left, fieldMul_eq_modP b c, fieldMul_modP_right, Int.mul_assoc]

theorem fieldMul_one {a : U64} (ha : IsCanonical a) : fieldMul a 1#u64 = a := by
  rw [fieldMul_eq_modP, toZ_one, Int.mul_one, modP_toZ_of_canonical ha]

theorem one_fieldMul {a : U64} (ha : IsCanonical a) : fieldMul 1#u64 a = a := by
  rw [fieldMul_comm, fieldMul_one ha]

theorem fieldMul_zero (a : U64) : fieldMul a 0#u64 = 0#u64 := by
  rw [fieldMul_eq_modP, toZ_zero, Int.mul_zero, modP_zero]

theorem zero_fieldMul (a : U64) : fieldMul 0#u64 a = 0#u64 := by
  rw [fieldMul_comm, fieldMul_zero]

theorem fieldMul_add (a b c : U64) :
    fieldMul a (fieldAdd b c) = fieldAdd (fieldMul a b) (fieldMul a c) := by
  rw [fieldAdd_eq_modP, fieldMul_modP_right, fieldMul_eq_modP, fieldMul_eq_modP, fieldAdd_modP_both, Int.mul_add]

theorem add_fieldMul (a b c : U64) :
    fieldMul (fieldAdd a b) c = fieldAdd (fieldMul a c) (fieldMul b c) := by
  rw [fieldAdd_eq_modP, fieldMul_modP_left, fieldMul_eq_modP, fieldMul_eq_modP, fieldAdd_modP_both, Int.add_mul]

theorem fieldMul_sub (a b c : U64) :
    fieldMul a (fieldSub b c) = fieldSub (fieldMul a b) (fieldMul a c) := by
  rw [fieldSub_eq_modP, fieldMul_modP_right, fieldMul_eq_modP, fieldMul_eq_modP, fieldSub_modP_both, Int.mul_sub]

theorem sub_fieldMul (a b c : U64) :
    fieldMul (fieldSub a b) c = fieldSub (fieldMul a c) (fieldMul b c) := by
  rw [fieldSub_eq_modP, fieldMul_modP_left, fieldMul_eq_modP, fieldMul_eq_modP, fieldSub_modP_both, Int.sub_mul]

private theorem eval_fieldMul_const (a b c : U64)
    (h : (a.val * b.val) % 18446744069414584321 = c.val) : fieldMul a b = c :=
  UScalar.eq_of_val_eq ((fieldMul_val a b).trans h)

/-- Exact multiplicative fifth-root-of-unity relations among `FROBENIUS_ZETA5_1..4`. -/
theorem zeta5_powers_spec :
    fieldMul FROBENIUS_ZETA5_1 FROBENIUS_ZETA5_1 = FROBENIUS_ZETA5_2 ∧
    fieldMul FROBENIUS_ZETA5_2 FROBENIUS_ZETA5_1 = FROBENIUS_ZETA5_3 ∧
    fieldMul FROBENIUS_ZETA5_3 FROBENIUS_ZETA5_1 = FROBENIUS_ZETA5_4 ∧
    fieldMul FROBENIUS_ZETA5_4 FROBENIUS_ZETA5_1 = 1#u64 := by
  rw [frobenius_zeta5_1_val, frobenius_zeta5_2_val, frobenius_zeta5_3_val, frobenius_zeta5_4_val]
  exact ⟨eval_fieldMul_const _ _ _ (by decide),
         eval_fieldMul_const _ _ _ (by decide),
         eval_fieldMul_const _ _ _ (by decide),
         eval_fieldMul_const _ _ _ (by decide)⟩

attribute [irreducible] fieldAdd fieldSub fieldMul

/-! ## Quintic Extension Ring `Fp5 = F_p[X] / (X^5 - 3)` -/

abbrev fp5Zero : Fp5 := ⟨0#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩
abbrev fp5One : Fp5 := ⟨1#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩
abbrev fp5FromBase (x : U64) : Fp5 :=
  ⟨UScalar.ofNat .U64 (x.val % 18446744069414584321), 0#u64, 0#u64, 0#u64, 0#u64⟩
abbrev fp5X : Fp5 := ⟨0#u64, 1#u64, 0#u64, 0#u64, 0#u64⟩
abbrev fp5Three : Fp5 := ⟨3#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩

@[expose] def fp5Add (x y : Fp5) : Fp5 :=
  ⟨fieldAdd x.c0 y.c0, fieldAdd x.c1 y.c1, fieldAdd x.c2 y.c2, fieldAdd x.c3 y.c3, fieldAdd x.c4 y.c4⟩

@[expose] def fp5Sub (x y : Fp5) : Fp5 :=
  ⟨fieldSub x.c0 y.c0, fieldSub x.c1 y.c1, fieldSub x.c2 y.c2, fieldSub x.c3 y.c3, fieldSub x.c4 y.c4⟩

abbrev fp5Neg (x : Fp5) : Fp5 := fp5Sub fp5Zero x

@[expose] def fp5Scale (x : Fp5) (s : U64) : Fp5 :=
  ⟨fieldMul x.c0 s, fieldMul x.c1 s, fieldMul x.c2 s, fieldMul x.c3 s, fieldMul x.c4 s⟩

/-- Multiplication in power basis `[1, X, X^2, X^3, X^4]` modulo `X^5 - 3`. -/
@[expose] def fp5Mul (x y : Fp5) : Fp5 :=
  ⟨fieldAdd (fieldMul x.c0 y.c0)
     (fieldMul 3#u64
       (fieldAdd (fieldAdd (fieldMul x.c1 y.c4) (fieldMul x.c2 y.c3))
                 (fieldAdd (fieldMul x.c3 y.c2) (fieldMul x.c4 y.c1)))),
   fieldAdd (fieldAdd (fieldMul x.c0 y.c1) (fieldMul x.c1 y.c0))
     (fieldMul 3#u64
       (fieldAdd (fieldAdd (fieldMul x.c2 y.c4) (fieldMul x.c3 y.c3))
                 (fieldMul x.c4 y.c2))),
   fieldAdd (fieldAdd (fieldAdd (fieldMul x.c0 y.c2) (fieldMul x.c1 y.c1)) (fieldMul x.c2 y.c0))
     (fieldMul 3#u64 (fieldAdd (fieldMul x.c3 y.c4) (fieldMul x.c4 y.c3))),
   fieldAdd (fieldAdd (fieldAdd (fieldMul x.c0 y.c3) (fieldMul x.c1 y.c2))
                      (fieldAdd (fieldMul x.c2 y.c1) (fieldMul x.c3 y.c0)))
     (fieldMul 3#u64 (fieldMul x.c4 y.c4)),
   fieldAdd (fieldAdd (fieldAdd (fieldMul x.c0 y.c4) (fieldMul x.c1 y.c3))
                      (fieldAdd (fieldMul x.c2 y.c2) (fieldMul x.c3 y.c1)))
     (fieldMul x.c4 y.c0)⟩

/-- Pure Frobenius endomorphism `x ↦ x^p` (`c_i ↦ ζ_5^i · c_i mod p`). -/
@[expose] def fp5Frob (x : Fp5) : Fp5 :=
  ⟨UScalar.ofNat .U64 (x.c0.val % 18446744069414584321),
   fieldMul x.c1 1041288259238279555#u64,
   fieldMul x.c2 15820824984080659046#u64,
   fieldMul x.c3 211587555138949697#u64,
   fieldMul x.c4 1373043270956696022#u64⟩

theorem fp5_zero_refines : fp5_zero = .ok fp5Zero := by
  simp only [fp5_zero.public_eqs]

theorem fp5_one_refines : fp5_one = .ok fp5One := by
  simp only [fp5_one.public_eqs]

theorem fp5_from_base_refines (x : U64) : fp5_from_base x = .ok (fp5FromBase x) := by
  simp only [fp5_from_base.public_eqs, reduce_limb, bind_eq_result_bind, result_bind_ok]

theorem fp5_add_refines (x y : Fp5) : fp5_add x y = .ok (fp5Add x y) := by
  simp [fp5_add.public_eqs, fp5Add, add_refines, Result.bind]

theorem fp5_sub_refines (x y : Fp5) : fp5_sub x y = .ok (fp5Sub x y) := by
  simp [fp5_sub.public_eqs, fp5Sub, sub_refines, Result.bind]

theorem fp5_neg_refines (x : Fp5) : fp5_neg x = .ok (fp5Neg x) := by
  simp [fp5_neg.public_eqs, fp5_zero_refines, fp5_sub_refines, Result.bind]

theorem fp5_scale_refines (x : Fp5) (s : U64) : fp5_scale x s = .ok (fp5Scale x s) := by
  simp [fp5_scale.public_eqs, fp5Scale, mul_refines, Result.bind]

theorem fp5_mul_refines (x y : Fp5) : fp5_mul x y = .ok (fp5Mul x y) := by
  simp [fp5_mul.public_eqs, fp5_nonresidue_w_val, fp5Mul, mul_refines, add_refines, Result.bind]

theorem fp5_frobenius_refines (x : Fp5) : fp5_frobenius x = .ok (fp5Frob x) := by
  simp only [fp5_frobenius.public_eqs, reduce_limb, frobenius_zeta5_1_val, frobenius_zeta5_2_val,
    frobenius_zeta5_3_val, frobenius_zeta5_4_val, fp5Frob, mul_refines, bind_eq_result_bind, Result.bind]

theorem affine_combine_fp5_refines (even odd alpha : Fp5) :
    affine_combine_fp5 even odd alpha = .ok (fp5Add odd (fp5Mul alpha even)) := by
  simp [affine_combine_fp5.public_eqs, fp5_mul_refines, fp5_add_refines, Result.bind]

theorem fp5Add_canonical (x y : Fp5) : IsCanonicalFp5 (fp5Add x y) :=
  ⟨fieldAdd_canonical _ _, fieldAdd_canonical _ _, fieldAdd_canonical _ _,
   fieldAdd_canonical _ _, fieldAdd_canonical _ _⟩

theorem fp5Sub_canonical (x y : Fp5) : IsCanonicalFp5 (fp5Sub x y) :=
  ⟨fieldSub_canonical _ _, fieldSub_canonical _ _, fieldSub_canonical _ _,
   fieldSub_canonical _ _, fieldSub_canonical _ _⟩

theorem fp5Scale_canonical (x : Fp5) (s : U64) : IsCanonicalFp5 (fp5Scale x s) :=
  ⟨fieldMul_canonical _ _, fieldMul_canonical _ _, fieldMul_canonical _ _,
   fieldMul_canonical _ _, fieldMul_canonical _ _⟩

theorem fp5Mul_canonical (x y : Fp5) : IsCanonicalFp5 (fp5Mul x y) :=
  ⟨fieldAdd_canonical _ _, fieldAdd_canonical _ _, fieldAdd_canonical _ _,
   fieldAdd_canonical _ _, fieldAdd_canonical _ _⟩

theorem fp5Frob_canonical (x : Fp5) : IsCanonicalFp5 (fp5Frob x) := by
  refine ⟨?_, fieldMul_canonical _ _, fieldMul_canonical _ _,
    fieldMul_canonical _ _, fieldMul_canonical _ _⟩
  dsimp only [fp5Frob]
  rw [IsCanonical, canonical_ofNat]
  exact Nat.mod_lt _ (by decide)

theorem fp5Frob_pow5_id {x : Fp5} (hx : IsCanonicalFp5 x) :
    fp5Frob (fp5Frob (fp5Frob (fp5Frob (fp5Frob x)))) = x := by
  rcases hx with ⟨h0, h1, h2, h3, h4⟩
  have hc0 : ∀ {u : U64}, IsCanonical u → UScalar.ofNat .U64 (u.val % 18446744069414584321) = u := by
    intro u hu
    apply UScalar.eq_of_val_eq
    rw [canonical_ofNat, Nat.mod_eq_of_lt hu]
  have hp1 : fieldMul (fieldMul (fieldMul (fieldMul 1041288259238279555#u64 1041288259238279555#u64)
      1041288259238279555#u64) 1041288259238279555#u64) 1041288259238279555#u64 = 1#u64 := by
    rw [eval_fieldMul_const 1041288259238279555#u64 1041288259238279555#u64 15820824984080659046#u64 (by decide)]
    rw [eval_fieldMul_const 15820824984080659046#u64 1041288259238279555#u64 211587555138949697#u64 (by decide)]
    rw [eval_fieldMul_const 211587555138949697#u64 1041288259238279555#u64 1373043270956696022#u64 (by decide)]
    exact eval_fieldMul_const 1373043270956696022#u64 1041288259238279555#u64 1#u64 (by decide)
  have hp2 : fieldMul (fieldMul (fieldMul (fieldMul 15820824984080659046#u64 15820824984080659046#u64)
      15820824984080659046#u64) 15820824984080659046#u64) 15820824984080659046#u64 = 1#u64 := by
    rw [eval_fieldMul_const 15820824984080659046#u64 15820824984080659046#u64 1373043270956696022#u64 (by decide)]
    rw [eval_fieldMul_const 1373043270956696022#u64 15820824984080659046#u64 1041288259238279555#u64 (by decide)]
    rw [eval_fieldMul_const 1041288259238279555#u64 15820824984080659046#u64 211587555138949697#u64 (by decide)]
    exact eval_fieldMul_const 211587555138949697#u64 15820824984080659046#u64 1#u64 (by decide)
  have hp3 : fieldMul (fieldMul (fieldMul (fieldMul 211587555138949697#u64 211587555138949697#u64)
      211587555138949697#u64) 211587555138949697#u64) 211587555138949697#u64 = 1#u64 := by
    rw [eval_fieldMul_const 211587555138949697#u64 211587555138949697#u64 1041288259238279555#u64 (by decide)]
    rw [eval_fieldMul_const 1041288259238279555#u64 211587555138949697#u64 1373043270956696022#u64 (by decide)]
    rw [eval_fieldMul_const 1373043270956696022#u64 211587555138949697#u64 15820824984080659046#u64 (by decide)]
    exact eval_fieldMul_const 15820824984080659046#u64 211587555138949697#u64 1#u64 (by decide)
  have hp4 : fieldMul (fieldMul (fieldMul (fieldMul 1373043270956696022#u64 1373043270956696022#u64)
      1373043270956696022#u64) 1373043270956696022#u64) 1373043270956696022#u64 = 1#u64 := by
    rw [eval_fieldMul_const 1373043270956696022#u64 1373043270956696022#u64 211587555138949697#u64 (by decide)]
    rw [eval_fieldMul_const 211587555138949697#u64 1373043270956696022#u64 15820824984080659046#u64 (by decide)]
    rw [eval_fieldMul_const 15820824984080659046#u64 1373043270956696022#u64 1041288259238279555#u64 (by decide)]
    exact eval_fieldMul_const 1041288259238279555#u64 1373043270956696022#u64 1#u64 (by decide)
  have fold5 : ∀ (c z : U64), IsCanonical c →
      fieldMul (fieldMul (fieldMul (fieldMul z z) z) z) z = 1#u64 →
      fieldMul (fieldMul (fieldMul (fieldMul (fieldMul c z) z) z) z) z = c := by
    intro c z hc hz
    rw [fieldMul_assoc c z z, fieldMul_assoc c _ z, fieldMul_assoc c _ z, fieldMul_assoc c _ z,
        hz, fieldMul_one hc]
  unfold fp5Frob
  refine Fp5.ext ?_ (fold5 _ _ h1 hp1) (fold5 _ _ h2 hp2) (fold5 _ _ h3 hp3) (fold5 _ _ h4 hp4)
  rw [hc0 h0, hc0 h0, hc0 h0, hc0 h0, hc0 h0]

/-! ### Syntactic Lifting of `Fp5` Expressions into 5-Tuple `FExpr` -/

private structure Fp5Expr where
  c0 : FExpr
  c1 : FExpr
  c2 : FExpr
  c3 : FExpr
  c4 : FExpr

private def Fp5Expr.var5 (base : Nat) : Fp5Expr :=
  ⟨.var base, .var (base + 1), .var (base + 2), .var (base + 3), .var (base + 4)⟩

private def Fp5Expr.add (x y : Fp5Expr) : Fp5Expr :=
  ⟨.add x.c0 y.c0, .add x.c1 y.c1, .add x.c2 y.c2, .add x.c3 y.c3, .add x.c4 y.c4⟩

private def Fp5Expr.sub (x y : Fp5Expr) : Fp5Expr :=
  ⟨.sub x.c0 y.c0, .sub x.c1 y.c1, .sub x.c2 y.c2, .sub x.c3 y.c3, .sub x.c4 y.c4⟩

private def Fp5Expr.mul (x y : Fp5Expr) : Fp5Expr :=
  let three := FExpr.const .c3
  ⟨.add (.mul x.c0 y.c0)
     (.mul three (.add (.add (.mul x.c1 y.c4) (.mul x.c2 y.c3))
                       (.add (.mul x.c3 y.c2) (.mul x.c4 y.c1)))),
   .add (.add (.mul x.c0 y.c1) (.mul x.c1 y.c0))
     (.mul three (.add (.add (.mul x.c2 y.c4) (.mul x.c3 y.c3)) (.mul x.c4 y.c2))),
   .add (.add (.add (.mul x.c0 y.c2) (.mul x.c1 y.c1)) (.mul x.c2 y.c0))
     (.mul three (.add (.mul x.c3 y.c4) (.mul x.c4 y.c3))),
   .add (.add (.add (.mul x.c0 y.c3) (.mul x.c1 y.c2))
              (.add (.mul x.c2 y.c1) (.mul x.c3 y.c0)))
     (.mul three (.mul x.c4 y.c4)),
   .add (.add (.add (.mul x.c0 y.c4) (.mul x.c1 y.c3))
              (.add (.mul x.c2 y.c2) (.mul x.c3 y.c1)))
     (.mul x.c4 y.c0)⟩

private def Fp5Expr.evalF (env : Nat → U64) (e : Fp5Expr) : Fp5 :=
  ⟨e.c0.evalF env, e.c1.evalF env, e.c2.evalF env, e.c3.evalF env, e.c4.evalF env⟩

private def Fp5Expr.wf (env : Nat → U64) (e : Fp5Expr) : Prop :=
  e.c0.wf env ∧ e.c1.wf env ∧ e.c2.wf env ∧ e.c3.wf env ∧ e.c4.wf env

private theorem Fp5Expr.eq_of_norm (env : Nat → U64) (lhs rhs : Fp5Expr)
    (hl : lhs.wf env) (hr : rhs.wf env)
    (h0 : lhs.c0.norm = rhs.c0.norm) (h1 : lhs.c1.norm = rhs.c1.norm)
    (h2 : lhs.c2.norm = rhs.c2.norm) (h3 : lhs.c3.norm = rhs.c3.norm)
    (h4 : lhs.c4.norm = rhs.c4.norm) :
    lhs.evalF env = rhs.evalF env :=
  Fp5.ext
    (FExpr.evalF_eq_of_norm env lhs.c0 rhs.c0 hl.1 hr.1 h0)
    (FExpr.evalF_eq_of_norm env lhs.c1 rhs.c1 hl.2.1 hr.2.1 h1)
    (FExpr.evalF_eq_of_norm env lhs.c2 rhs.c2 hl.2.2.1 hr.2.2.1 h2)
    (FExpr.evalF_eq_of_norm env lhs.c3 rhs.c3 hl.2.2.2.1 hr.2.2.2.1 h3)
    (FExpr.evalF_eq_of_norm env lhs.c4 rhs.c4 hl.2.2.2.2 hr.2.2.2.2 h4)

private def envFp5_3 (x y z : Fp5) : Nat → U64
  | 0 => x.c0 | 1 => x.c1 | 2 => x.c2 | 3 => x.c3 | 4 => x.c4
  | 5 => y.c0 | 6 => y.c1 | 7 => y.c2 | 8 => y.c3 | 9 => y.c4
  | 10 => z.c0 | 11 => z.c1 | 12 => z.c2 | 13 => z.c3 | 14 => z.c4
  | _ => 0#u64

/-! ### Full `Fp5` Commutative Ring Laws & Defining `X^5 = 3` Identity -/

theorem fp5Add_comm (x y : Fp5) : fp5Add x y = fp5Add y x := by
  ext <;> exact fieldAdd_comm _ _

theorem fp5Add_assoc (x y z : Fp5) :
    fp5Add (fp5Add x y) z = fp5Add x (fp5Add y z) := by
  ext <;> exact fieldAdd_assoc _ _ _

theorem fp5Add_zero {x : Fp5} (hx : IsCanonicalFp5 x) : fp5Add x fp5Zero = x := by
  rcases hx with ⟨h0, h1, h2, h3, h4⟩
  exact Fp5.ext (fieldAdd_zero h0) (fieldAdd_zero h1) (fieldAdd_zero h2)
    (fieldAdd_zero h3) (fieldAdd_zero h4)

theorem zero_fp5Add {x : Fp5} (hx : IsCanonicalFp5 x) : fp5Add fp5Zero x = x := by
  rw [fp5Add_comm, fp5Add_zero hx]

theorem fp5Sub_self (x : Fp5) : fp5Sub x x = fp5Zero := by
  ext <;> exact fieldSub_self _

theorem fp5Add_sub_cancel {x : Fp5} (hx : IsCanonicalFp5 x) (y : Fp5) :
    fp5Sub (fp5Add x y) y = x := by
  rcases hx with ⟨h0, h1, h2, h3, h4⟩
  exact Fp5.ext (fieldAdd_sub_cancel h0 _) (fieldAdd_sub_cancel h1 _)
    (fieldAdd_sub_cancel h2 _) (fieldAdd_sub_cancel h3 _) (fieldAdd_sub_cancel h4 _)

theorem fp5Sub_add_cancel {x : Fp5} (hx : IsCanonicalFp5 x) (y : Fp5) :
    fp5Add (fp5Sub x y) y = x := by
  rcases hx with ⟨h0, h1, h2, h3, h4⟩
  exact Fp5.ext (fieldSub_add_cancel h0 _) (fieldSub_add_cancel h1 _)
    (fieldSub_add_cancel h2 _) (fieldSub_add_cancel h3 _) (fieldSub_add_cancel h4 _)

theorem fp5Mul_comm (x y : Fp5) : fp5Mul x y = fp5Mul y x :=
  Fp5Expr.eq_of_norm (envFp5_3 x y fp5Zero)
    (Fp5Expr.mul (.var5 0) (.var5 5))
    (Fp5Expr.mul (.var5 5) (.var5 0))
    ⟨trivial, trivial, trivial, trivial, trivial⟩
    ⟨trivial, trivial, trivial, trivial, trivial⟩
    rfl rfl rfl rfl rfl

theorem fp5Mul_assoc (x y z : Fp5) :
    fp5Mul (fp5Mul x y) z = fp5Mul x (fp5Mul y z) :=
  Fp5Expr.eq_of_norm (envFp5_3 x y z)
    (Fp5Expr.mul (Fp5Expr.mul (.var5 0) (.var5 5)) (.var5 10))
    (Fp5Expr.mul (.var5 0) (Fp5Expr.mul (.var5 5) (.var5 10)))
    ⟨trivial, trivial, trivial, trivial, trivial⟩
    ⟨trivial, trivial, trivial, trivial, trivial⟩
    rfl rfl rfl rfl rfl

theorem fp5Mul_add (x y z : Fp5) :
    fp5Mul x (fp5Add y z) = fp5Add (fp5Mul x y) (fp5Mul x z) :=
  Fp5Expr.eq_of_norm (envFp5_3 x y z)
    (Fp5Expr.mul (.var5 0) (Fp5Expr.add (.var5 5) (.var5 10)))
    (Fp5Expr.add (Fp5Expr.mul (.var5 0) (.var5 5)) (Fp5Expr.mul (.var5 0) (.var5 10)))
    ⟨trivial, trivial, trivial, trivial, trivial⟩
    ⟨trivial, trivial, trivial, trivial, trivial⟩
    rfl rfl rfl rfl rfl

theorem add_fp5Mul (x y z : Fp5) :
    fp5Mul (fp5Add x y) z = fp5Add (fp5Mul x z) (fp5Mul y z) := by
  rw [fp5Mul_comm, fp5Mul_add, fp5Mul_comm z x, fp5Mul_comm z y]

theorem fp5Mul_sub (x y z : Fp5) :
    fp5Mul x (fp5Sub y z) = fp5Sub (fp5Mul x y) (fp5Mul x z) :=
  Fp5Expr.eq_of_norm (envFp5_3 x y z)
    (Fp5Expr.mul (.var5 0) (Fp5Expr.sub (.var5 5) (.var5 10)))
    (Fp5Expr.sub (Fp5Expr.mul (.var5 0) (.var5 5)) (Fp5Expr.mul (.var5 0) (.var5 10)))
    ⟨trivial, trivial, trivial, trivial, trivial⟩
    ⟨trivial, trivial, trivial, trivial, trivial⟩
    rfl rfl rfl rfl rfl

theorem sub_fp5Mul (x y z : Fp5) :
    fp5Mul (fp5Sub x y) z = fp5Sub (fp5Mul x z) (fp5Mul y z) := by
  rw [fp5Mul_comm, fp5Mul_sub, fp5Mul_comm z x, fp5Mul_comm z y]

theorem fp5Mul_one {x : Fp5} (hx : IsCanonicalFp5 x) : fp5Mul x fp5One = x :=
  Fp5Expr.eq_of_norm (envFp5_3 x fp5Zero fp5Zero)
    (Fp5Expr.mul (.var5 0) ⟨.const .c1, .const .c0, .const .c0, .const .c0, .const .c0⟩)
    (.var5 0)
    ⟨trivial, trivial, trivial, trivial, trivial⟩
    hx rfl rfl rfl rfl rfl

theorem one_fp5Mul {x : Fp5} (hx : IsCanonicalFp5 x) : fp5Mul fp5One x = x := by
  rw [fp5Mul_comm, fp5Mul_one hx]

theorem fp5Mul_zero (x : Fp5) : fp5Mul x fp5Zero = fp5Zero :=
  Fp5Expr.eq_of_norm (envFp5_3 x fp5Zero fp5Zero)
    (Fp5Expr.mul (.var5 0) ⟨.const .c0, .const .c0, .const .c0, .const .c0, .const .c0⟩)
    ⟨.const .c0, .const .c0, .const .c0, .const .c0, .const .c0⟩
    ⟨trivial, trivial, trivial, trivial, trivial⟩
    ⟨trivial, trivial, trivial, trivial, trivial⟩
    rfl rfl rfl rfl rfl

theorem zero_fp5Mul (x : Fp5) : fp5Mul fp5Zero x = fp5Zero := by
  rw [fp5Mul_comm, fp5Mul_zero]

/-- Defining quintic field relation `X^5 = 3` in `Fp5`. -/
theorem fp5X_pow5_eq_three :
    fp5Mul (fp5Mul (fp5Mul fp5X fp5X) (fp5Mul fp5X fp5X)) fp5X = fp5Three := by
  have hx2 : fp5Mul fp5X fp5X = ⟨0#u64, 0#u64, 1#u64, 0#u64, 0#u64⟩ :=
    Fp5Expr.eq_of_norm (envFp5_3 fp5Zero fp5Zero fp5Zero)
      (Fp5Expr.mul ⟨.const .c0, .const .c1, .const .c0, .const .c0, .const .c0⟩
                   ⟨.const .c0, .const .c1, .const .c0, .const .c0, .const .c0⟩)
      ⟨.const .c0, .const .c0, .const .c1, .const .c0, .const .c0⟩
      ⟨trivial, trivial, trivial, trivial, trivial⟩
      ⟨trivial, trivial, trivial, trivial, trivial⟩
      rfl rfl rfl rfl rfl
  have hx4 : fp5Mul ⟨0#u64, 0#u64, 1#u64, 0#u64, 0#u64⟩ ⟨0#u64, 0#u64, 1#u64, 0#u64, 0#u64⟩ =
      ⟨0#u64, 0#u64, 0#u64, 0#u64, 1#u64⟩ :=
    Fp5Expr.eq_of_norm (envFp5_3 fp5Zero fp5Zero fp5Zero)
      (Fp5Expr.mul ⟨.const .c0, .const .c0, .const .c1, .const .c0, .const .c0⟩
                   ⟨.const .c0, .const .c0, .const .c1, .const .c0, .const .c0⟩)
      ⟨.const .c0, .const .c0, .const .c0, .const .c0, .const .c1⟩
      ⟨trivial, trivial, trivial, trivial, trivial⟩
      ⟨trivial, trivial, trivial, trivial, trivial⟩
      rfl rfl rfl rfl rfl
  rw [hx2, hx4]
  exact Fp5Expr.eq_of_norm (envFp5_3 fp5Zero fp5Zero fp5Zero)
    (Fp5Expr.mul ⟨.const .c0, .const .c0, .const .c0, .const .c0, .const .c1⟩
                 ⟨.const .c0, .const .c1, .const .c0, .const .c0, .const .c0⟩)
    ⟨.const .c3, .const .c0, .const .c0, .const .c0, .const .c0⟩
    ⟨trivial, trivial, trivial, trivial, trivial⟩
    ⟨trivial, trivial, trivial, trivial, trivial⟩
    rfl rfl rfl rfl rfl

/-! ## Duet Fold, CWYZ Fold, Bridge, Quadratic Sumcheck Wire, & Horner Refinements -/

/-- Total mathematical duet expression `odd + alpha * even`. -/
def duetFp5Value (v0 v1 : Fp5) (iy it : U64) (alpha : Fp5) : Fp5 :=
  fp5Add (fp5Scale (fp5Sub v0 v1) iy) (fp5Mul alpha (fp5Scale (fp5Add v0 v1) it))

theorem duet_fold_fp5_refines (v0 v1 : Fp5) (iy it : U64) (alpha : Fp5) :
    duet_fold_fp5 v0 v1 iy it alpha = .ok (duetFp5Value v0 v1 iy it alpha) := by
  simp only [duet_fold_fp5.public_eqs, duetFp5Value, copy_fp5_spec, affine_combine_fp5_refines,
    fp5_sub_refines, fp5_scale_refines, fp5_mul_refines, fp5_add_refines, bind_eq_result_bind, Result.bind]

def cwyzFp5Value (v0 v1 : Fp5) (iy it yy : U64) (theta alpha beta : Fp5) : Fp5 :=
  let even := fp5Scale (fp5Add v0 v1) it
  let odd := fp5Scale (fp5Sub v0 v1) iy
  fp5Add odd (fp5Mul (fp5Add alpha (fp5Scale beta yy)) (fp5Add even (fp5Mul theta odd)))

theorem cwyz_duet_fold_fp5_refines (v0 v1 : Fp5) (iy it yy : U64) (theta alpha beta : Fp5) :
    cwyz_duet_fold_fp5 v0 v1 iy it yy theta alpha beta =
      .ok (cwyzFp5Value v0 v1 iy it yy theta alpha beta) := by
  simp only [cwyz_duet_fold_fp5.public_eqs, cwyzFp5Value, copy_fp5_spec, affine_combine_fp5_refines,
    fp5_sub_refines, fp5_scale_refines, fp5_mul_refines, fp5_add_refines, bind_eq_result_bind, Result.bind]

private theorem scale_add_sub_even_fp5 {even odd : Fp5} {y0 it : U64}
    (he : IsCanonicalFp5 even) (hit : fieldMul 2#u64 it = 1#u64) :
    fp5Scale (fp5Add (fp5Add even (fp5Scale odd y0)) (fp5Sub even (fp5Scale odd y0))) it = even := by
  have limb_recover : ∀ (e o : U64), IsCanonical e →
      fieldMul (fieldAdd (fieldAdd e (fieldMul o y0)) (fieldSub e (fieldMul o y0))) it = e := by
    intro e o he_c
    let env : Nat → U64 := fun | 0 => e | 1 => o | 2 => y0 | _ => 0#u64
    have hsum : fieldAdd (fieldAdd e (fieldMul o y0)) (fieldSub e (fieldMul o y0)) = fieldMul 2#u64 e :=
      FExpr.evalF_eq_of_norm env
        (.add (.add (.var 0) (.mul (.var 1) (.var 2))) (.sub (.var 0) (.mul (.var 1) (.var 2))))
        (.mul (.const .c2) (.var 0))
        trivial trivial rfl
    rw [hsum, fieldMul_comm 2#u64 e, fieldMul_assoc, hit, fieldMul_one he_c]
  rcases he with ⟨h0, h1, h2, h3, h4⟩
  unfold fp5Scale fp5Add fp5Sub
  exact Fp5.ext (limb_recover _ _ h0) (limb_recover _ _ h1) (limb_recover _ _ h2)
    (limb_recover _ _ h3) (limb_recover _ _ h4)

private theorem scale_add_sub_odd_fp5 {even odd : Fp5} {y0 iy : U64}
    (ho : IsCanonicalFp5 odd) (hiy : fieldMul (fieldMul 2#u64 y0) iy = 1#u64) :
    fp5Scale (fp5Sub (fp5Add even (fp5Scale odd y0)) (fp5Sub even (fp5Scale odd y0))) iy = odd := by
  have limb_recover : ∀ (e o : U64), IsCanonical o →
      fieldMul (fieldSub (fieldAdd e (fieldMul o y0)) (fieldSub e (fieldMul o y0))) iy = o := by
    intro e o ho_c
    let env : Nat → U64 := fun | 0 => e | 1 => o | 2 => y0 | _ => 0#u64
    have hdiff : fieldSub (fieldAdd e (fieldMul o y0)) (fieldSub e (fieldMul o y0)) =
        fieldMul o (fieldMul 2#u64 y0) :=
      FExpr.evalF_eq_of_norm env
        (.sub (.add (.var 0) (.mul (.var 1) (.var 2))) (.sub (.var 0) (.mul (.var 1) (.var 2))))
        (.mul (.var 1) (.mul (.const .c2) (.var 2)))
        trivial trivial rfl
    rw [hdiff, fieldMul_assoc, hiy, fieldMul_one ho_c]
  rcases ho with ⟨h0, h1, h2, h3, h4⟩
  unfold fp5Scale fp5Add fp5Sub
  exact Fp5.ext (limb_recover _ _ h0) (limb_recover _ _ h1) (limb_recover _ _ h2)
    (limb_recover _ _ h3) (limb_recover _ _ h4)

/-- Algebraic coset soundness of `duet_fold_fp5`: on `v0 = E + y0 * O`, `v1 = E - y0 * O`,
    `duetFp5Value` recovers `O + alpha * E`. -/
theorem duet_fold_fp5_algebraic_sound
    {even odd : Fp5} {y0 iy it : U64} (alpha : Fp5)
    (he : IsCanonicalFp5 even) (ho : IsCanonicalFp5 odd)
    (hit : fieldMul 2#u64 it = 1#u64)
    (hiy : fieldMul (fieldMul 2#u64 y0) iy = 1#u64) :
    duetFp5Value (fp5Add even (fp5Scale odd y0)) (fp5Sub even (fp5Scale odd y0)) iy it alpha =
      fp5Add odd (fp5Mul alpha even) := by
  unfold duetFp5Value
  rw [scale_add_sub_even_fp5 he hit, scale_add_sub_odd_fp5 ho hiy]

/-- Algebraic coset soundness of `cwyz_duet_fold_fp5`: on `v0 = E + y0 * O`, `v1 = E - y0 * O`,
    `cwyzFp5Value` recovers `O + (alpha + beta * y0^2) * (E + theta * O)`. -/
theorem cwyz_duet_fold_fp5_algebraic_sound
    {even odd : Fp5} {y0 iy it : U64} (theta alpha beta : Fp5)
    (he : IsCanonicalFp5 even) (ho : IsCanonicalFp5 odd)
    (hit : fieldMul 2#u64 it = 1#u64)
    (hiy : fieldMul (fieldMul 2#u64 y0) iy = 1#u64) :
    cwyzFp5Value (fp5Add even (fp5Scale odd y0)) (fp5Sub even (fp5Scale odd y0))
        iy it (fieldMul y0 y0) theta alpha beta =
      fp5Add odd (fp5Mul (fp5Add alpha (fp5Scale beta (fieldMul y0 y0))) (fp5Add even (fp5Mul theta odd))) := by
  unfold cwyzFp5Value
  rw [scale_add_sub_even_fp5 he hit, scale_add_sub_odd_fp5 ho hiy]

/-- Pure CWYZ dual linear-functional bridge expression over `Fp5`. -/
def cwyzBridgeFp5Value (w0 w1 w2 w3 w4 claim phi theta alpha beta : Fp5) : Fp5 :=
  let f := fp5Add w0 (fp5Mul phi w1)
  let g := fp5Add w2 (fp5Mul phi (fp5Sub claim w0))
  let core := fp5Add g (fp5Mul alpha (fp5Add f (fp5Mul theta g)))
  let shift := fp5Mul beta (fp5Add w3 (fp5Mul theta w4))
  fp5Add core shift

theorem cwyz_bridge_claim_step_fp5_refines
    (w0 w1 w2 w3 w4 claim phi theta alpha beta : Fp5) :
    cwyz_bridge_claim_step_fp5 w0 w1 w2 w3 w4 claim phi theta alpha beta =
      .ok (cwyzBridgeFp5Value w0 w1 w2 w3 w4 claim phi theta alpha beta) := by
  simp only [cwyz_bridge_claim_step_fp5.public_eqs, cwyzBridgeFp5Value, copy_fp5_spec,
    fp5_mul_refines, fp5_add_refines, fp5_sub_refines, bind_eq_result_bind, Result.bind]

/-- Dual-functional soundness of `cwyz_bridge_claim_step_fp5`. -/
theorem cwyz_bridge_claim_step_fp5_dual_sound
    (a0 a1 b0 b1 kn phi theta alpha beta : Fp5) :
    cwyzBridgeFp5Value
        (fp5Mul a0 b0) (fp5Mul a0 b1) (fp5Mul a1 b0) (fp5Mul a0 kn) (fp5Mul a1 kn)
        (fp5Add (fp5Mul a0 b0) (fp5Mul a1 b1)) phi theta alpha beta =
      fp5Add
        (fp5Mul (fp5Add a1 (fp5Mul alpha (fp5Add a0 (fp5Mul theta a1)))) (fp5Add b0 (fp5Mul phi b1)))
        (fp5Mul (fp5Mul beta (fp5Add a0 (fp5Mul theta a1))) kn) := by
  let k0' := fp5Add b0 (fp5Mul phi b1)
  have hf : fp5Add (fp5Mul a0 b0) (fp5Mul phi (fp5Mul a0 b1)) = fp5Mul a0 k0' := by
    rw [← fp5Mul_assoc phi a0 b1, fp5Mul_comm phi a0, fp5Mul_assoc a0 phi b1, ← fp5Mul_add]
  have hsub : fp5Sub (fp5Add (fp5Mul a0 b0) (fp5Mul a1 b1)) (fp5Mul a0 b0) = fp5Mul a1 b1 := by
    rw [fp5Add_comm (fp5Mul a0 b0) (fp5Mul a1 b1), fp5Add_sub_cancel (fp5Mul_canonical a1 b1)]
  have hg : fp5Add (fp5Mul a1 b0) (fp5Mul phi (fp5Sub (fp5Add (fp5Mul a0 b0) (fp5Mul a1 b1)) (fp5Mul a0 b0))) =
      fp5Mul a1 k0' := by
    rw [hsub, ← fp5Mul_assoc phi a1 b1, fp5Mul_comm phi a1, fp5Mul_assoc a1 phi b1, ← fp5Mul_add]
  have hcore : fp5Add (fp5Mul a1 k0') (fp5Mul alpha (fp5Add (fp5Mul a0 k0') (fp5Mul theta (fp5Mul a1 k0')))) =
      fp5Mul (fp5Add a1 (fp5Mul alpha (fp5Add a0 (fp5Mul theta a1)))) k0' := by
    rw [← fp5Mul_assoc theta a1 k0',
        ← add_fp5Mul a0 (fp5Mul theta a1) k0',
        ← fp5Mul_assoc alpha (fp5Add a0 (fp5Mul theta a1)) k0',
        ← add_fp5Mul a1 (fp5Mul alpha (fp5Add a0 (fp5Mul theta a1))) k0']
  have hshift : fp5Mul beta (fp5Add (fp5Mul a0 kn) (fp5Mul theta (fp5Mul a1 kn))) =
      fp5Mul (fp5Mul beta (fp5Add a0 (fp5Mul theta a1))) kn := by
    rw [← fp5Mul_assoc theta a1 kn,
        ← add_fp5Mul a0 (fp5Mul theta a1) kn,
        ← fp5Mul_assoc beta (fp5Add a0 (fp5Mul theta a1)) kn]
  dsimp only [cwyzBridgeFp5Value]
  rw [hf, hg, hcore, hshift]

/-- Pure quadratic wire reconstruction `c0 + r * ((sum_claim - 2*c0 - c2) + c2 * r)` over `Fp5`. -/
def quadraticWireFp5Value (c0 c2 sum_claim r : Fp5) : Fp5 :=
  let c1 := fp5Sub (fp5Sub sum_claim (fp5Add c0 c0)) c2
  fp5Add (fp5Mul (fp5Add (fp5Mul c2 r) c1) r) c0

theorem eval_quadratic_sumcheck_wire_fp5_refines (c0 c2 sum_claim r : Fp5) :
    eval_quadratic_sumcheck_wire_fp5 c0 c2 sum_claim r =
      .ok (quadraticWireFp5Value c0 c2 sum_claim r) := by
  simp only [eval_quadratic_sumcheck_wire_fp5.public_eqs, quadraticWireFp5Value, copy_fp5_spec,
    fp5_add_refines, fp5_sub_refines, fp5_mul_refines, bind_eq_result_bind, Result.bind]

private theorem fp5Mul_fp5One_eq_scale_one (x : Fp5) :
    fp5Mul x fp5One = fp5Scale x 1#u64 :=
  Fp5Expr.eq_of_norm (envFp5_3 x fp5Zero fp5Zero)
    (Fp5Expr.mul (.var5 0) ⟨.const .c1, .const .c0, .const .c0, .const .c0, .const .c0⟩)
    ⟨.mul (.var 0) (.const .c1), .mul (.var 1) (.const .c1),
     .mul (.var 2) (.const .c1), .mul (.var 3) (.const .c1), .mul (.var 4) (.const .c1)⟩
    ⟨trivial, trivial, trivial, trivial, trivial⟩
    ⟨trivial, trivial, trivial, trivial, trivial⟩
    rfl rfl rfl rfl rfl

private theorem quadratic_limb_sum (a0 a2 s : U64) (hs : IsCanonical s) :
    fieldAdd (fieldAdd 0#u64 a0)
      (fieldAdd (fieldAdd (fieldMul a2 1#u64) (fieldSub (fieldSub s (fieldAdd a0 a0)) a2)) a0) = s :=
  let env : Nat → U64 := fun | 0 => a0 | 1 => a2 | 2 => s | _ => 0#u64
  FExpr.evalF_eq_of_norm env
    (.add (.add (.const .c0) (.var 0))
          (.add (.add (.mul (.var 1) (.const .c1))
                      (.sub (.sub (.var 2) (.add (.var 0) (.var 0))) (.var 1)))
                (.var 0)))
    (.var 2)
    trivial hs rfl

/-- Boolean hypercube sum guarantee: `eval(0) + eval(1) = sum_claim` unconditionally for canonical `sum_claim`. -/
theorem eval_quadratic_sumcheck_wire_fp5_hypercube_sum
    (c0 c2 sum_claim : Fp5) (hs : IsCanonicalFp5 sum_claim) :
    fp5Add (quadraticWireFp5Value c0 c2 sum_claim fp5Zero)
           (quadraticWireFp5Value c0 c2 sum_claim fp5One) = sum_claim := by
  rcases hs with ⟨hs0, hs1, hs2, hs3, hs4⟩
  dsimp only [quadraticWireFp5Value]
  rw [fp5Mul_zero, fp5Mul_one (fp5Add_canonical _ _), fp5Mul_fp5One_eq_scale_one]
  unfold fp5Add fp5Sub fp5Scale fp5Zero
  exact Fp5.ext
    (quadratic_limb_sum c0.c0 c2.c0 sum_claim.c0 hs0)
    (quadratic_limb_sum c0.c1 c2.c1 sum_claim.c1 hs1)
    (quadratic_limb_sum c0.c2 c2.c2 sum_claim.c2 hs2)
    (quadratic_limb_sum c0.c3 c2.c3 sum_claim.c3 hs3)
    (quadratic_limb_sum c0.c4 c2.c4 sum_claim.c4 hs4)

attribute [irreducible] fp5Add fp5Sub fp5Scale fp5Mul

/-! ## Arbitrary-Length Horner Evaluation over `Fp5` at Base Point `z : U64` -/

/-- Exact descending-index Horner fold matching `eval_fp5_univariate_at_base_loop`. -/
@[expose] def hornerSpec (coeffs : List Fp5) (z : U64) (init : Fp5 := fp5Zero) : Fp5 :=
  coeffs.foldr (fun c acc => fp5Add (fp5Scale acc z) c) init

/-- Textbook ascending-degree polynomial evaluation `c_0 + z * (c_1 + z * ...)`. -/
@[expose] def evalPolyAscending : List Fp5 → U64 → Fp5
  | [], _ => fp5Zero
  | c :: rest, z => fp5Add c (fp5Scale (evalPolyAscending rest z) z)

theorem hornerSpec_nil (z : U64) (init : Fp5) : hornerSpec [] z init = init := rfl

theorem hornerSpec_cons (c : Fp5) (rest : List Fp5) (z : U64) (init : Fp5) :
    hornerSpec (c :: rest) z init = fp5Add (fp5Scale (hornerSpec rest z init) z) c := rfl

theorem hornerSpec_canonical (coeffs : List Fp5) (z : U64) :
    IsCanonicalFp5 (hornerSpec coeffs z fp5Zero) := by
  induction coeffs with
  | nil =>
    rw [hornerSpec_nil]
    unfold fp5Zero IsCanonicalFp5 IsCanonical
    exact ⟨by decide, by decide, by decide, by decide, by decide⟩
  | cons _ _ _ => exact fp5Add_canonical _ _

/-- For canonical coefficients, `hornerSpec coeffs z fp5Zero` coincides with `evalPolyAscending coeffs z`. -/
theorem hornerSpec_eq_evalPolyAscending (coeffs : List Fp5) (z : U64)
    (_hcan : ∀ c ∈ coeffs, IsCanonicalFp5 c) :
    hornerSpec coeffs z fp5Zero = evalPolyAscending coeffs z := by
  induction coeffs with
  | nil => rfl
  | cons c rest ih =>
    have hrest : ∀ x ∈ rest, IsCanonicalFp5 x := fun x hx => _hcan x (List.mem_cons_of_mem c hx)
    simp only [hornerSpec_cons, evalPolyAscending, ih hrest, fp5Add_comm]

end qsag_whir_verified.proofs

public section
namespace qsag_whir_verified.proofs
#export_eqns duetFp5Value cwyzFp5Value cwyzBridgeFp5Value quadraticWireFp5Value
end qsag_whir_verified.proofs
end

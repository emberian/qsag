module
public import QsagWhirVerified.Funs
import all Aeneas
import all Aeneas.Std.Types
public section
open Aeneas Aeneas.Std

namespace qsag_whir_verified

@[ext]
theorem Ext4.ext {x y : Ext4}
    (ha : x.a = y.a) (hb : x.b = y.b) (hc : x.c = y.c) (hd : x.d = y.d) : x = y := by
  cases x; cases y; subst ha hb hc hd; rfl

instance : DecidableEq Ext4 := fun x y =>
  match decEq x.a y.a with
  | isFalse h => isFalse (fun e => h (congrArg Ext4.a e))
  | isTrue ha =>
    match decEq x.b y.b with
    | isFalse h => isFalse (fun e => h (congrArg Ext4.b e))
    | isTrue hb =>
      match decEq x.c y.c with
      | isFalse h => isFalse (fun e => h (congrArg Ext4.c e))
      | isTrue hc =>
        match decEq x.d y.d with
        | isFalse h => isFalse (fun e => h (congrArg Ext4.d e))
        | isTrue hd => isTrue (Ext4.ext ha hb hc hd)

@[ext]
theorem MerklePair.ext {x y : MerklePair}
    (ht : x.tag = y.tag) (hl : x.left = y.left) (hr : x.right = y.right) : x = y := by
  cases x; cases y; subst ht hl hr; rfl

instance : DecidableEq MerklePair := fun x y =>
  match decEq x.tag y.tag with
  | isFalse h => isFalse (fun e => h (congrArg MerklePair.tag e))
  | isTrue ht =>
    match decEq x.left y.left with
    | isFalse h => isFalse (fun e => h (congrArg MerklePair.left e))
    | isTrue hl =>
      match decEq x.right y.right with
      | isFalse h => isFalse (fun e => h (congrArg MerklePair.right e))
      | isTrue hr => isTrue (MerklePair.ext ht hl hr)

end qsag_whir_verified

namespace qsag_whir_verified.proofs

abbrev goldilocksMod : Nat := 18446744069414584321
abbrev goldilocksModZ : Int := 18446744069414584321

theorem goldilocks_p_val : GOLDILOCKS_P.val = goldilocksMod := by
  unfold GOLDILOCKS_P
  rfl

theorem max_u64_word_val : MAX_U64_WORD.val = 18446744073709551615 := by
  unfold MAX_U64_WORD
  rfl

theorem tag_canopy_merkle_internal_eq : TAG_CANOPY_MERKLE_INTERNAL = 0#u8 := by
  unfold TAG_CANOPY_MERKLE_INTERNAL
  rfl

abbrev IsCanonical (x : U64) : Prop := x.val < goldilocksMod

abbrev IsCanonicalExt4 (x : Ext4) : Prop :=
  IsCanonical x.a ∧ IsCanonical x.b ∧ IsCanonical x.c ∧ IsCanonical x.d

/-! ## Scalar Width-Cast and Checked `U128` Arithmetic Lemmas -/

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
      (UScalar.cast .U64 r).val = x.val % goldilocksMod := by
  have hp : (UScalar.cast .U128 GOLDILOCKS_P).val = goldilocksMod := by
    unfold GOLDILOCKS_P
    rfl
  let r : U128 := ⟨x.bv % (UScalar.cast .U128 GOLDILOCKS_P).bv⟩
  have hr : r.val = x.val % goldilocksMod := by
    change (x.bv % (UScalar.cast .U128 GOLDILOCKS_P).bv).toNat = _
    rw [BitVec.toNat_umod]
    exact congrArg (x.val % ·) hp
  refine ⟨r, ?_, ?_⟩
  · simp only [hMod_uscalar_eq, hp]
    rfl
  · rw [u128_cast_u64_val_of_lt r (by rw [hr]; exact Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)), hr]

theorem add_modular_spec (a b : U64) :
    ∃ r, add a b = .ok r ∧ r.val = (a.val + b.val) % goldilocksMod := by
  have ha := u64_cast_u128_val a
  have hb := u64_cast_u128_val b
  obtain ⟨hs, hv⟩ := u128_add_ok (a := UScalar.cast .U128 a) (b := UScalar.cast .U128 b)
    (by rw [ha, hb]; have ha64 : a.val < 2^64 := a.bv.isLt; have hb64 : b.val < 2^64 := b.bv.isLt; omega)
  obtain ⟨r, hr, hrv⟩ := reduce_wide ⟨(UScalar.cast .U128 a).bv + (UScalar.cast .U128 b).bv⟩
  refine ⟨UScalar.cast .U64 r, ?_, ?_⟩
  · simp only [add, lift_eq_ok, bind_eq_result_bind, Result.bind, hs, hr]
  · rw [hrv, hv, ha, hb]

theorem mul_modular_spec (a b : U64) :
    ∃ r, mul a b = .ok r ∧ r.val = (a.val * b.val) % goldilocksMod := by
  have ha := u64_cast_u128_val a
  have hb := u64_cast_u128_val b
  obtain ⟨hs, hv⟩ := u128_mul_ok (a := UScalar.cast .U128 a) (b := UScalar.cast .U128 b)
    (by rw [ha, hb]; exact Nat.mul_lt_mul'' (show a.val < 2^64 from a.bv.isLt) (show b.val < 2^64 from b.bv.isLt))
  obtain ⟨r, hr, hrv⟩ := reduce_wide ⟨(UScalar.cast .U128 a).bv * (UScalar.cast .U128 b).bv⟩
  refine ⟨UScalar.cast .U64 r, ?_, ?_⟩
  · simp only [mul, lift_eq_ok, bind_eq_result_bind, Result.bind, hs, hr]
  · rw [hrv, hv, ha, hb]

private theorem reduce_limb (b : U64) :
    ∃ bm : U64, (b % GOLDILOCKS_P : Result U64) = .ok bm ∧
      bm.val = b.val % goldilocksMod := by
  have hp : GOLDILOCKS_P.val = goldilocksMod := goldilocks_p_val
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
      (a.val + (goldilocksMod - b.val % goldilocksMod)) % goldilocksMod := by
  have hp : GOLDILOCKS_P.val = goldilocksMod := goldilocks_p_val
  obtain ⟨bm, hr, hbm⟩ := reduce_limb b
  obtain ⟨neg, hn, hnv⟩ := subtract_limb GOLDILOCKS_P bm (by
    rw [hp, hbm]
    exact Nat.le_of_lt (Nat.mod_lt _ (by decide)))
  obtain ⟨r, ha, hav⟩ := add_modular_spec a neg
  refine ⟨r, ?_, ?_⟩
  · simp only [sub, hr, bind_eq_result_bind, result_bind_ok, hn, ha]
  · have hnval : neg.val = goldilocksMod - b.val % goldilocksMod :=
      hnv.trans ((congrArg (fun t => t - bm.val) hp).trans (congrArg (fun t => goldilocksMod - t) hbm))
    exact hav.trans (congrArg (fun t => (a.val + t) % goldilocksMod) hnval)

/-! ## Pure Goldilocks Field Operations & `Int`-Modular Commutative Ring Laws -/

@[expose] def fieldAdd (a b : U64) : U64 :=
  UScalar.ofNat .U64 ((a.val + b.val) % goldilocksMod)

@[expose] def fieldSub (a b : U64) : U64 :=
  UScalar.ofNat .U64 ((a.val + (goldilocksMod - b.val % goldilocksMod)) % goldilocksMod)

@[expose] def fieldMul (a b : U64) : U64 :=
  UScalar.ofNat .U64 ((a.val * b.val) % goldilocksMod)

private theorem canonical_ofNat (x : Nat) :
    (UScalar.ofNat .U64 (x % goldilocksMod)).val = x % goldilocksMod := by
  rw [UScalar.val_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))

theorem fieldAdd_val (a b : U64) : (fieldAdd a b).val = (a.val + b.val) % goldilocksMod :=
  canonical_ofNat (a.val + b.val)

theorem fieldSub_val (a b : U64) :
    (fieldSub a b).val = (a.val + (goldilocksMod - b.val % goldilocksMod)) % goldilocksMod :=
  canonical_ofNat _

theorem fieldMul_val (a b : U64) : (fieldMul a b).val = (a.val * b.val) % goldilocksMod :=
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

attribute [irreducible] fieldAdd fieldSub fieldMul

/-! ### Constructive `Int`-Modular Projection & Multivariate Horner Ring Normalizer -/

private def toZ (x : U64) : Int := (x.val : Int)

private def modP (z : Int) : U64 :=
  UScalar.ofNat .U64 (z % goldilocksModZ).toNat

private theorem modP_val (z : Int) :
    (modP z).val = (z % goldilocksModZ).toNat := by
  unfold modP
  rw [UScalar.val_ofNat]
  have hnn : 0 ≤ z % goldilocksModZ := Int.emod_nonneg z (by decide)
  have hlt : z % goldilocksModZ < goldilocksModZ := Int.emod_lt_of_pos z (by decide)
  have hnat : (z % goldilocksModZ).toNat < 2 ^ 64 := by omega
  exact Nat.mod_eq_of_lt hnat

private theorem toZ_modP (z : Int) : toZ (modP z) = z % goldilocksModZ := by
  unfold toZ
  rw [modP_val]
  have hnn : 0 ≤ z % goldilocksModZ := Int.emod_nonneg z (by decide)
  omega

private theorem modP_idem (z : Int) : modP (z % goldilocksModZ) = modP z := by
  apply UScalar.eq_of_val_eq
  rw [modP_val, modP_val, Int.emod_emod]

private theorem modP_toZ_of_canonical {x : U64} (hx : IsCanonical x) :
    modP (toZ x) = x := by
  apply UScalar.eq_of_val_eq
  rw [modP_val]
  unfold toZ IsCanonical at *
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
  have hmul : ((a.val * b.val : Nat) : Int) = (a.val : Int) * (b.val : Int) := Int.ofNat_mul a.val b.val
  have hmod : (((a.val * b.val) % goldilocksMod : Nat) : Int) =
      ((a.val : Int) * (b.val : Int)) % goldilocksModZ := by
    rw [Int.ofNat_emod, hmul]
    rfl
  omega

private theorem modP_add_left (x y : Int) :
    modP (x % goldilocksModZ + y) = modP (x + y) := by
  apply UScalar.eq_of_val_eq
  rw [modP_val, modP_val]
  omega

private theorem modP_add_right (x y : Int) :
    modP (x + y % goldilocksModZ) = modP (x + y) := by
  apply UScalar.eq_of_val_eq
  rw [modP_val, modP_val]
  omega

private theorem modP_sub_left (x y : Int) :
    modP (x % goldilocksModZ - y) = modP (x - y) := by
  apply UScalar.eq_of_val_eq
  rw [modP_val, modP_val]
  omega

private theorem modP_sub_right (x y : Int) :
    modP (x - y % goldilocksModZ) = modP (x - y) := by
  apply UScalar.eq_of_val_eq
  rw [modP_val, modP_val]
  omega

private theorem modP_mul_left (x y : Int) :
    modP (x % goldilocksModZ * y) = modP (x * y) := by
  apply UScalar.eq_of_val_eq
  rw [modP_val, modP_val]
  have h : (x % goldilocksModZ * y) % goldilocksModZ = (x * y) % goldilocksModZ := by
    rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
  rw [h]

private theorem modP_mul_right (x y : Int) :
    modP (x * (y % goldilocksModZ)) = modP (x * y) := by
  apply UScalar.eq_of_val_eq
  rw [modP_val, modP_val]
  have h : (x * (y % goldilocksModZ)) % goldilocksModZ = (x * y) % goldilocksModZ := by
    rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
  rw [h]

/-- Constructive multivariate Horner polynomial over `Int` (`0 Classical.choice`). -/
private inductive HPoly where
  | const : Int → HPoly
  | var : Nat → HPoly → HPoly → HPoly
  deriving DecidableEq

private def HPoly.eval (env : Nat → Int) : HPoly → Int
  | .const c => c
  | .var i p q => p.eval env * env i + q.eval env

private def HPoly.size : HPoly → Nat
  | .const _ => 1
  | .var _ p q => 1 + p.size + q.size

private def HPoly.mkVar (i : Nat) (p q : HPoly) : HPoly :=
  match p with
  | .const 0 => q
  | _ => .var i p q

private theorem HPoly.eval_mkVar (env : Nat → Int) (i : Nat) (p q : HPoly) :
    (HPoly.mkVar i p q).eval env = p.eval env * env i + q.eval env := by
  unfold HPoly.mkVar
  cases p with
  | const c =>
    by_cases hc : c = 0
    · subst hc
      simp [HPoly.eval]
    · simp [hc, HPoly.eval]
  | var j p' q' =>
    rfl

private def HPoly.neg : HPoly → HPoly
  | .const c => .const (-c)
  | .var i p q => .var i p.neg q.neg

private theorem HPoly.eval_neg (env : Nat → Int) (p : HPoly) :
    p.neg.eval env = -(p.eval env) := by
  induction p with
  | const c => rfl
  | var i p q ihp ihq =>
    simp only [HPoly.neg, HPoly.eval, ihp, ihq]
    rw [Int.neg_mul]
    omega

private def HPoly.add : HPoly → HPoly → HPoly
  | .const c1, .const c2 => .const (c1 + c2)
  | .const c1, .var j p2 q2 => HPoly.mkVar j p2 (HPoly.add (.const c1) q2)
  | .var i p1 q1, .const c2 => HPoly.mkVar i p1 (HPoly.add q1 (.const c2))
  | .var i p1 q1, .var j p2 q2 =>
    if i < j then
      HPoly.mkVar i p1 (HPoly.add q1 (.var j p2 q2))
    else if j < i then
      HPoly.mkVar j p2 (HPoly.add (.var i p1 q1) q2)
    else
      HPoly.mkVar i (HPoly.add p1 p2) (HPoly.add q1 q2)
termination_by a b => a.size + b.size
decreasing_by
  all_goals simp_wf; simp [HPoly.size]; omega

private theorem HPoly.eval_add (env : Nat → Int) (a b : HPoly) :
    (HPoly.add a b).eval env = a.eval env + b.eval env := by
  match a, b with
  | .const c1, .const c2 => rfl
  | .const c1, .var j p2 q2 =>
    simp only [HPoly.add, HPoly.eval_mkVar, HPoly.eval]
    rw [HPoly.eval_add env (.const c1) q2]
    simp only [HPoly.eval]
    omega
  | .var i p1 q1, .const c2 =>
    simp only [HPoly.add, HPoly.eval_mkVar, HPoly.eval]
    rw [HPoly.eval_add env q1 (.const c2)]
    simp only [HPoly.eval]
    omega
  | .var i p1 q1, .var j p2 q2 =>
    unfold HPoly.add
    split
    · rw [HPoly.eval_mkVar, HPoly.eval_add env q1 (.var j p2 q2)]
      simp only [HPoly.eval]
      omega
    · split
      · rw [HPoly.eval_mkVar, HPoly.eval_add env (.var i p1 q1) q2]
        simp only [HPoly.eval]
        omega
      · rename_i h1 h2
        have hij : i = j := by omega
        subst hij
        rw [HPoly.eval_mkVar, HPoly.eval_add env p1 p2, HPoly.eval_add env q1 q2]
        simp only [HPoly.eval, Int.add_mul]
        omega
termination_by a.size + b.size
decreasing_by
  all_goals simp_wf; simp [HPoly.size]; omega

private def HPoly.mulConst (c : Int) : HPoly → HPoly
  | .const d => .const (c * d)
  | .var i p q => HPoly.mkVar i (HPoly.mulConst c p) (HPoly.mulConst c q)

private theorem HPoly.eval_mulConst (env : Nat → Int) (c : Int) (p : HPoly) :
    (HPoly.mulConst c p).eval env = c * p.eval env := by
  induction p with
  | const d => rfl
  | var i p q ihp ihq =>
    simp only [HPoly.mulConst, HPoly.eval_mkVar, HPoly.eval, ihp, ihq]
    rw [Int.mul_assoc, Int.mul_add]

private theorem horner_mul_step (a b c d x : Int) :
    ((a * c * x + (a * d + b * c)) * x + b * d) = (a * x + b) * (c * x + d) := by
  calc
    ((a * c * x + (a * d + b * c)) * x + b * d)
        = a * c * x * x + (a * d * x + b * c * x) + b * d := by
          rw [Int.add_mul, Int.add_mul]
    _ = (a * x * (c * x) + a * x * d) + (b * (c * x) + b * d) := by
          have h1 : a * c * x * x = a * x * (c * x) := by
            rw [Int.mul_assoc a c x, Int.mul_comm c x, ← Int.mul_assoc a x c, Int.mul_assoc (a * x) c x]
          have h2 : a * d * x = a * x * d := by
            rw [Int.mul_assoc a d x, Int.mul_comm d x, ← Int.mul_assoc a x d]
          have h3 : b * c * x = b * (c * x) := Int.mul_assoc b c x
          rw [h1, h2, h3]
          omega
    _ = a * x * (c * x + d) + b * (c * x + d) := by
          rw [← Int.mul_add, ← Int.mul_add]
    _ = (a * x + b) * (c * x + d) := by
          rw [← Int.add_mul]

private def HPoly.mul : HPoly → HPoly → HPoly
  | .const c1, b => HPoly.mulConst c1 b
  | .var i p1 q1, .const c2 => HPoly.mulConst c2 (.var i p1 q1)
  | .var i p1 q1, .var j p2 q2 =>
    if i < j then
      HPoly.mkVar i (HPoly.mul p1 (.var j p2 q2)) (HPoly.mul q1 (.var j p2 q2))
    else if j < i then
      HPoly.mkVar j (HPoly.mul (.var i p1 q1) p2) (HPoly.mul (.var i p1 q1) q2)
    else
      let pp := HPoly.mul p1 p2
      let pq := HPoly.add (HPoly.mul p1 q2) (HPoly.mul q1 p2)
      let qq := HPoly.mul q1 q2
      HPoly.add (HPoly.mkVar i (HPoly.add (HPoly.mkVar i pp (.const 0)) pq) (.const 0)) qq
termination_by a b => a.size + b.size
decreasing_by
  all_goals simp_wf; simp [HPoly.size]; omega

private theorem HPoly.eval_mul (env : Nat → Int) (a b : HPoly) :
    (HPoly.mul a b).eval env = a.eval env * b.eval env := by
  match a, b with
  | .const c1, b =>
    exact HPoly.eval_mulConst env c1 b
  | .var i p1 q1, .const c2 =>
    rw [HPoly.mul, HPoly.eval_mulConst]
    exact Int.mul_comm c2 _
  | .var i p1 q1, .var j p2 q2 =>
    unfold HPoly.mul
    split
    · rw [HPoly.eval_mkVar, HPoly.eval_mul env p1 (.var j p2 q2), HPoly.eval_mul env q1 (.var j p2 q2)]
      simp only [HPoly.eval]
      rw [Int.add_mul, Int.mul_assoc, Int.mul_comm ((HPoly.var j p2 q2).eval env) (env i), ← Int.mul_assoc]
    · split
      · rw [HPoly.eval_mkVar, HPoly.eval_mul env (.var i p1 q1) p2, HPoly.eval_mul env (.var i p1 q1) q2]
        simp only [HPoly.eval]
        rw [Int.mul_add, Int.mul_assoc]
      · rename_i h1 h2
        have hij : i = j := by omega
        subst hij
        simp only [HPoly.eval_add, HPoly.eval_mkVar, HPoly.eval,
          HPoly.eval_mul env p1 p2, HPoly.eval_mul env p1 q2,
          HPoly.eval_mul env q1 p2, HPoly.eval_mul env q1 q2, Int.add_zero]
        exact horner_mul_step (p1.eval env) (q1.eval env) (p2.eval env) (q2.eval env) (env i)
termination_by a.size + b.size
decreasing_by
  all_goals simp_wf; simp [HPoly.size]; omega

/-- Syntactic ring expressions over `U64` variables evaluated in `modP`. -/
private inductive FExpr where
  | const : Int → FExpr
  | var : Nat → FExpr
  | add : FExpr → FExpr → FExpr
  | sub : FExpr → FExpr → FExpr
  | mul : FExpr → FExpr → FExpr

private def FExpr.norm : FExpr → HPoly
  | .const c => .const c
  | .var i => .var i (.const 1) (.const 0)
  | .add a b => HPoly.add a.norm b.norm
  | .sub a b => HPoly.add a.norm b.norm.neg
  | .mul a b => HPoly.mul a.norm b.norm

private def FExpr.evalZ (env : Nat → U64) : FExpr → Int
  | .const c => c
  | .var i => toZ (env i)
  | .add a b => a.evalZ env + b.evalZ env
  | .sub a b => a.evalZ env - b.evalZ env
  | .mul a b => a.evalZ env * b.evalZ env

private theorem FExpr.eval_norm (env : Nat → U64) (e : FExpr) :
    e.norm.eval (fun i => toZ (env i)) = e.evalZ env := by
  induction e with
  | const c => rfl
  | var i => simp [FExpr.norm, FExpr.evalZ, HPoly.eval]
  | add a b iha ihb => simp [FExpr.norm, FExpr.evalZ, HPoly.eval_add, iha, ihb]
  | sub a b iha ihb =>
    simp only [FExpr.norm, FExpr.evalZ, HPoly.eval_add, HPoly.eval_neg, iha, ihb]
    omega
  | mul a b iha ihb => simp [FExpr.norm, FExpr.evalZ, HPoly.eval_mul, iha, ihb]

private theorem modP_eq_of_fexpr (env : Nat → U64) (lhs rhs : FExpr)
    (h : lhs.norm = rhs.norm) :
    modP (lhs.evalZ env) = modP (rhs.evalZ env) := by
  rw [← FExpr.eval_norm env lhs, ← FExpr.eval_norm env rhs, h]

/-! ### Simp Normalization of `fieldAdd` / `fieldSub` / `fieldMul` into `modP` -/

private theorem toZ_zero : toZ 0#u64 = 0 := rfl
private theorem toZ_one : toZ 1#u64 = 1 := rfl
private theorem toZ_two : toZ 2#u64 = 2 := rfl
private theorem toZ_seven : toZ 7#u64 = 7 := rfl

private theorem modP_zero : modP 0 = 0#u64 := by
  apply UScalar.eq_of_val_eq; rw [modP_val]; rfl

private theorem modP_one : modP 1 = 1#u64 := by
  apply UScalar.eq_of_val_eq; rw [modP_val]; rfl

private theorem modP_seven : modP 7 = 7#u64 := by
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

private theorem fieldMul_modP_both (x y : Int) :
    fieldMul (modP x) (modP y) = modP (x * y) := by
  rw [fieldMul_eq_modP, toZ_modP, toZ_modP, modP_mul_left, modP_mul_right]

/-! ### Exported Goldilocks Commutative Ring Theorems -/

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

/-! ## Quartic Extension Ring `Ext4 = F_p[u] / (u^4 - 7)` -/

def extZero : Ext4 := ⟨0#u64, 0#u64, 0#u64, 0#u64⟩
def extOne : Ext4 := ⟨1#u64, 0#u64, 0#u64, 0#u64⟩
def extU : Ext4 := ⟨0#u64, 1#u64, 0#u64, 0#u64⟩
def extSeven : Ext4 := ⟨7#u64, 0#u64, 0#u64, 0#u64⟩

@[simp] theorem extZero_limbs : extZero.a = 0#u64 ∧ extZero.b = 0#u64 ∧ extZero.c = 0#u64 ∧ extZero.d = 0#u64 :=
  ⟨rfl, rfl, rfl, rfl⟩

@[expose] def extAdd (x y : Ext4) : Ext4 :=
  ⟨fieldAdd x.a y.a, fieldAdd x.b y.b, fieldAdd x.c y.c, fieldAdd x.d y.d⟩

@[expose] def extSub (x y : Ext4) : Ext4 :=
  ⟨fieldSub x.a y.a, fieldSub x.b y.b, fieldSub x.c y.c, fieldSub x.d y.d⟩

@[expose] def extScale (x : Ext4) (s : U64) : Ext4 :=
  ⟨fieldMul x.a s, fieldMul x.b s, fieldMul x.c s, fieldMul x.d s⟩

/-- Multiplication in polynomial basis `[1, u, u^2, u^3]` modulo `u^4 - 7`. -/
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

theorem affine_combine_refines (even odd alpha : Ext4) :
    affine_combine even odd alpha = .ok (extAdd odd (extMul alpha even)) := by
  simp [affine_combine, ext_mul_refines, ext_add_refines, Result.bind]

theorem extAdd_canonical (x y : Ext4) : IsCanonicalExt4 (extAdd x y) :=
  ⟨fieldAdd_canonical _ _, fieldAdd_canonical _ _, fieldAdd_canonical _ _, fieldAdd_canonical _ _⟩

theorem extSub_canonical (x y : Ext4) : IsCanonicalExt4 (extSub x y) :=
  ⟨fieldSub_canonical _ _, fieldSub_canonical _ _, fieldSub_canonical _ _, fieldSub_canonical _ _⟩

theorem extScale_canonical (x : Ext4) (s : U64) : IsCanonicalExt4 (extScale x s) :=
  ⟨fieldMul_canonical _ _, fieldMul_canonical _ _, fieldMul_canonical _ _, fieldMul_canonical _ _⟩

theorem extMul_canonical (x y : Ext4) : IsCanonicalExt4 (extMul x y) :=
  ⟨fieldAdd_canonical _ _, fieldAdd_canonical _ _, fieldAdd_canonical _ _, fieldAdd_canonical _ _⟩

/-! ### Syntactic Lifting of `Ext4` Expressions into 4-Tuple `FExpr` -/

private structure Ext4Expr where
  a : FExpr
  b : FExpr
  c : FExpr
  d : FExpr

private def Ext4Expr.var4 (base : Nat) : Ext4Expr :=
  ⟨.var base, .var (base + 1), .var (base + 2), .var (base + 3)⟩

private def Ext4Expr.add (x y : Ext4Expr) : Ext4Expr :=
  ⟨.add x.a y.a, .add x.b y.b, .add x.c y.c, .add x.d y.d⟩

private def Ext4Expr.sub (x y : Ext4Expr) : Ext4Expr :=
  ⟨.sub x.a y.a, .sub x.b y.b, .sub x.c y.c, .sub x.d y.d⟩

private def Ext4Expr.scale (x : Ext4Expr) (s : FExpr) : Ext4Expr :=
  ⟨.mul x.a s, .mul x.b s, .mul x.c s, .mul x.d s⟩

private def Ext4Expr.mul (x y : Ext4Expr) : Ext4Expr :=
  let seven := FExpr.const 7
  ⟨.add (.mul x.a y.a) (.mul seven (.add (.add (.mul x.b y.d) (.mul x.c y.c)) (.mul x.d y.b))),
   .add (.add (.mul x.a y.b) (.mul x.b y.a)) (.mul seven (.add (.mul x.c y.d) (.mul x.d y.c))),
   .add (.add (.add (.mul x.a y.c) (.mul x.b y.b)) (.mul x.c y.a)) (.mul seven (.mul x.d y.d)),
   .add (.add (.mul x.a y.d) (.mul x.b y.c)) (.add (.mul x.c y.b) (.mul x.d y.a))⟩

private def Ext4Expr.eval (env : Nat → U64) (e : Ext4Expr) : Ext4 :=
  ⟨modP (e.a.evalZ env), modP (e.b.evalZ env), modP (e.c.evalZ env), modP (e.d.evalZ env)⟩

private theorem Ext4Expr.eval_add (env : Nat → U64) (x y : Ext4Expr) :
    extAdd (x.eval env) (y.eval env) = (Ext4Expr.add x y).eval env := by
  ext <;> simp [extAdd, Ext4Expr.eval, Ext4Expr.add, FExpr.evalZ, fieldAdd_modP_both]

private theorem Ext4Expr.eval_sub (env : Nat → U64) (x y : Ext4Expr) :
    extSub (x.eval env) (y.eval env) = (Ext4Expr.sub x y).eval env := by
  ext <;> simp [extSub, Ext4Expr.eval, Ext4Expr.sub, FExpr.evalZ, fieldSub_modP_both]

private theorem Ext4Expr.eval_scale_var (env : Nat → U64) (x : Ext4Expr) (i : Nat) :
    extScale (x.eval env) (env i) = (Ext4Expr.scale x (.var i)).eval env := by
  ext <;> simp [extScale, Ext4Expr.eval, Ext4Expr.scale, FExpr.evalZ, fieldMul_modP_left]

private theorem Ext4Expr.eval_mul (env : Nat → U64) (x y : Ext4Expr) :
    extMul (x.eval env) (y.eval env) = (Ext4Expr.mul x y).eval env := by
  ext <;> simp [extMul, Ext4Expr.eval, Ext4Expr.mul, FExpr.evalZ,
    fieldMul_modP_both, fieldAdd_modP_both, fieldMul_eq_modP, toZ_seven, fieldMul_modP_right]

private theorem Ext4Expr.eq_of_norm (env : Nat → U64) (lhs rhs : Ext4Expr)
    (ha : lhs.a.norm = rhs.a.norm) (hb : lhs.b.norm = rhs.b.norm)
    (hc : lhs.c.norm = rhs.c.norm) (hd : lhs.d.norm = rhs.d.norm) :
    lhs.eval env = rhs.eval env := by
  refine Ext4.ext ?_ ?_ ?_ ?_
  · exact modP_eq_of_fexpr env lhs.a rhs.a ha
  · exact modP_eq_of_fexpr env lhs.b rhs.b hb
  · exact modP_eq_of_fexpr env lhs.c rhs.c hc
  · exact modP_eq_of_fexpr env lhs.d rhs.d hd

private def envExt3 (x y z : Ext4) : Nat → U64
  | 0 => x.a | 1 => x.b | 2 => x.c | 3 => x.d
  | 4 => y.a | 5 => y.b | 6 => y.c | 7 => y.d
  | 8 => z.a | 9 => z.b | 10 => z.c | 11 => z.d
  | _ => 0#u64

private theorem eval_var4_0 {x y z : Ext4} (hx : IsCanonicalExt4 x) :
    (Ext4Expr.var4 0).eval (envExt3 x y z) = x := by
  rcases hx with ⟨ha, hb, hc, hd⟩
  exact Ext4.ext (modP_toZ_of_canonical ha) (modP_toZ_of_canonical hb)
    (modP_toZ_of_canonical hc) (modP_toZ_of_canonical hd)

private theorem eval_var4_4 {x y z : Ext4} (hy : IsCanonicalExt4 y) :
    (Ext4Expr.var4 4).eval (envExt3 x y z) = y := by
  rcases hy with ⟨ha, hb, hc, hd⟩
  exact Ext4.ext (modP_toZ_of_canonical ha) (modP_toZ_of_canonical hb)
    (modP_toZ_of_canonical hc) (modP_toZ_of_canonical hd)

private theorem eval_var4_8 {x y z : Ext4} (hz : IsCanonicalExt4 z) :
    (Ext4Expr.var4 8).eval (envExt3 x y z) = z := by
  rcases hz with ⟨ha, hb, hc, hd⟩
  exact Ext4.ext (modP_toZ_of_canonical ha) (modP_toZ_of_canonical hb)
    (modP_toZ_of_canonical hc) (modP_toZ_of_canonical hd)

/-- Every limb of `extAdd`, `extSub`, `extScale`, `extMul` depends only on `modP ∘ toZ` of its inputs. -/
private def extCanon (x : Ext4) : Ext4 :=
  ⟨modP (toZ x.a), modP (toZ x.b), modP (toZ x.c), modP (toZ x.d)⟩

private theorem extCanon_eq_of_canonical {x : Ext4} (hx : IsCanonicalExt4 x) :
    extCanon x = x := by
  rcases hx with ⟨ha, hb, hc, hd⟩
  exact Ext4.ext (modP_toZ_of_canonical ha) (modP_toZ_of_canonical hb)
    (modP_toZ_of_canonical hc) (modP_toZ_of_canonical hd)

private theorem extAdd_canon (x y : Ext4) : extAdd (extCanon x) (extCanon y) = extAdd x y := by
  ext <;> simp [extAdd, extCanon, fieldAdd_modP_both, fieldAdd_eq_modP]

private theorem extSub_canon (x y : Ext4) : extSub (extCanon x) (extCanon y) = extSub x y := by
  ext <;> simp [extSub, extCanon, fieldSub_modP_both, fieldSub_eq_modP]

private theorem extMul_canon (x y : Ext4) : extMul (extCanon x) (extCanon y) = extMul x y := by
  ext <;> simp [extMul, extCanon, fieldMul_modP_both, fieldAdd_modP_both,
    fieldMul_eq_modP, fieldAdd_eq_modP, fieldMul_modP_right]

/-! ### Full `Ext4` Commutative Ring Laws & Defining `u^4 = 7` Identity -/

theorem extAdd_comm (x y : Ext4) : extAdd x y = extAdd y x := by
  ext <;> exact fieldAdd_comm _ _

theorem extAdd_assoc (x y z : Ext4) :
    extAdd (extAdd x y) z = extAdd x (extAdd y z) := by
  ext <;> exact fieldAdd_assoc _ _ _

theorem extAdd_zero {x : Ext4} (hx : IsCanonicalExt4 x) : extAdd x extZero = x := by
  rcases hx with ⟨ha, hb, hc, hd⟩
  exact Ext4.ext (fieldAdd_zero ha) (fieldAdd_zero hb) (fieldAdd_zero hc) (fieldAdd_zero hd)

theorem zero_extAdd {x : Ext4} (hx : IsCanonicalExt4 x) : extAdd extZero x = x := by
  rw [extAdd_comm, extAdd_zero hx]

theorem extSub_self (x : Ext4) : extSub x x = extZero := by
  ext <;> exact fieldSub_self _

theorem extAdd_sub_cancel {x : Ext4} (hx : IsCanonicalExt4 x) (y : Ext4) :
    extSub (extAdd x y) y = x := by
  rcases hx with ⟨ha, hb, hc, hd⟩
  exact Ext4.ext (fieldAdd_sub_cancel ha _) (fieldAdd_sub_cancel hb _)
    (fieldAdd_sub_cancel hc _) (fieldAdd_sub_cancel hd _)

theorem extSub_add_cancel {x : Ext4} (hx : IsCanonicalExt4 x) (y : Ext4) :
    extAdd (extSub x y) y = x := by
  rcases hx with ⟨ha, hb, hc, hd⟩
  exact Ext4.ext (fieldSub_add_cancel ha _) (fieldSub_add_cancel hb _)
    (fieldSub_add_cancel hc _) (fieldSub_add_cancel hd _)

theorem extMul_comm (x y : Ext4) : extMul x y = extMul y x := by
  let env := envExt3 x y extZero
  have hx : (Ext4Expr.var4 0).eval env = extCanon x := rfl
  have hy : (Ext4Expr.var4 4).eval env = extCanon y := rfl
  rw [← extMul_canon x y, ← extMul_canon y x, ← hx, ← hy,
    Ext4Expr.eval_mul, Ext4Expr.eval_mul]
  exact Ext4Expr.eq_of_norm env _ _ rfl rfl rfl rfl

theorem extMul_assoc (x y z : Ext4) :
    extMul (extMul x y) z = extMul x (extMul y z) := by
  let env := envExt3 x y z
  have hx : (Ext4Expr.var4 0).eval env = extCanon x := rfl
  have hy : (Ext4Expr.var4 4).eval env = extCanon y := rfl
  have hz : (Ext4Expr.var4 8).eval env = extCanon z := rfl
  have hl : extMul (extMul x y) z =
      (Ext4Expr.mul (Ext4Expr.mul (.var4 0) (.var4 4)) (.var4 8)).eval env := by
    rw [← Ext4Expr.eval_mul, ← Ext4Expr.eval_mul, hx, hy, hz, extMul_canon,
      ← extCanon_eq_of_canonical (extMul_canonical x y), extMul_canon]
  have hr : extMul x (extMul y z) =
      (Ext4Expr.mul (.var4 0) (Ext4Expr.mul (.var4 4) (.var4 8))).eval env := by
    rw [← Ext4Expr.eval_mul, ← Ext4Expr.eval_mul, hx, hy, hz, extMul_canon,
      ← extCanon_eq_of_canonical (extMul_canonical y z), extMul_canon]
  rw [hl, hr]
  exact Ext4Expr.eq_of_norm env _ _ rfl rfl rfl rfl

theorem extMul_add (x y z : Ext4) :
    extMul x (extAdd y z) = extAdd (extMul x y) (extMul x z) := by
  let env := envExt3 x y z
  have hx : (Ext4Expr.var4 0).eval env = extCanon x := rfl
  have hy : (Ext4Expr.var4 4).eval env = extCanon y := rfl
  have hz : (Ext4Expr.var4 8).eval env = extCanon z := rfl
  have hl : extMul x (extAdd y z) =
      (Ext4Expr.mul (.var4 0) (Ext4Expr.add (.var4 4) (.var4 8))).eval env := by
    rw [← Ext4Expr.eval_mul, ← Ext4Expr.eval_add, hx, hy, hz, extAdd_canon,
      ← extCanon_eq_of_canonical (extAdd_canonical y z), extMul_canon]
  have hr : extAdd (extMul x y) (extMul x z) =
      (Ext4Expr.add (Ext4Expr.mul (.var4 0) (.var4 4)) (Ext4Expr.mul (.var4 0) (.var4 8))).eval env := by
    rw [← Ext4Expr.eval_add, ← Ext4Expr.eval_mul, ← Ext4Expr.eval_mul, hx, hy, hz,
      extMul_canon, extMul_canon]
  rw [hl, hr]
  exact Ext4Expr.eq_of_norm env _ _ rfl rfl rfl rfl

theorem add_extMul (x y z : Ext4) :
    extMul (extAdd x y) z = extAdd (extMul x z) (extMul y z) := by
  rw [extMul_comm, extMul_add, extMul_comm z x, extMul_comm z y]

theorem extMul_sub (x y z : Ext4) :
    extMul x (extSub y z) = extSub (extMul x y) (extMul x z) := by
  let env := envExt3 x y z
  have hx : (Ext4Expr.var4 0).eval env = extCanon x := rfl
  have hy : (Ext4Expr.var4 4).eval env = extCanon y := rfl
  have hz : (Ext4Expr.var4 8).eval env = extCanon z := rfl
  have hl : extMul x (extSub y z) =
      (Ext4Expr.mul (.var4 0) (Ext4Expr.sub (.var4 4) (.var4 8))).eval env := by
    rw [← Ext4Expr.eval_mul, ← Ext4Expr.eval_sub, hx, hy, hz, extSub_canon,
      ← extCanon_eq_of_canonical (extSub_canonical y z), extMul_canon]
  have hr : extSub (extMul x y) (extMul x z) =
      (Ext4Expr.sub (Ext4Expr.mul (.var4 0) (.var4 4)) (Ext4Expr.mul (.var4 0) (.var4 8))).eval env := by
    rw [← Ext4Expr.eval_sub, ← Ext4Expr.eval_mul, ← Ext4Expr.eval_mul, hx, hy, hz,
      extMul_canon, extMul_canon]
  rw [hl, hr]
  exact Ext4Expr.eq_of_norm env _ _ rfl rfl rfl rfl

theorem extMul_one {x : Ext4} (hx : IsCanonicalExt4 x) : extMul x extOne = x := by
  let env := envExt3 x extZero extZero
  have hxe : (Ext4Expr.var4 0).eval env = x := eval_var4_0 hx
  have h1e : (⟨.const 1, .const 0, .const 0, .const 0⟩ : Ext4Expr).eval env = extOne := by
    exact Ext4.ext modP_one modP_zero modP_zero modP_zero
  rw [← hxe, ← h1e, Ext4Expr.eval_mul]
  exact Ext4Expr.eq_of_norm env _ _ rfl rfl rfl rfl

theorem one_extMul {x : Ext4} (hx : IsCanonicalExt4 x) : extMul extOne x = x := by
  rw [extMul_comm, extMul_one hx]

theorem extMul_zero (x : Ext4) : extMul x extZero = extZero := by
  let env := envExt3 x extZero extZero
  have hxe : (Ext4Expr.var4 0).eval env = extCanon x := rfl
  have h0e : (⟨.const 0, .const 0, .const 0, .const 0⟩ : Ext4Expr).eval env = extZero := by
    exact Ext4.ext modP_zero modP_zero modP_zero modP_zero
  have hz : extCanon extZero = extZero := by
    exact Ext4.ext modP_zero modP_zero modP_zero modP_zero
  rw [← extMul_canon x extZero, hz, ← hxe, ← h0e, Ext4Expr.eval_mul]
  exact Ext4Expr.eq_of_norm env _ _ rfl rfl rfl rfl

theorem zero_extMul (x : Ext4) : extMul extZero x = extZero := by
  rw [extMul_comm, extMul_zero]

/-- Defining quartic field relation `u^4 = 7` in `Ext4`. -/
theorem extU_pow4_eq_seven :
    extMul (extMul extU extU) (extMul extU extU) = extSeven := by
  let env := envExt3 extZero extZero extZero
  let uE : Ext4Expr := ⟨.const 0, .const 1, .const 0, .const 0⟩
  let sE : Ext4Expr := ⟨.const 7, .const 0, .const 0, .const 0⟩
  have hu : uE.eval env = extU := Ext4.ext modP_zero modP_one modP_zero modP_zero
  have hs : sE.eval env = extSeven := Ext4.ext modP_seven modP_zero modP_zero modP_zero
  rw [← hu, Ext4Expr.eval_mul, Ext4Expr.eval_mul, ← hs]
  exact Ext4Expr.eq_of_norm env _ _ rfl rfl rfl rfl

/-! ### Karatsuba Quadratic-Over-Quadratic Tower `[1, u^2, u, u^3]` Isomorphism -/

/-- Maps production `GoldilocksExt4` tower coordinates `(c00, c01, c10, c11)` (`[1, u^2, u, u^3]`)
    into `qsag_whir_verified::Ext4` polynomial coordinates `[1, u, u^2, u^3]`. -/
def towerToPoly (t : Ext4) : Ext4 := ⟨t.a, t.c, t.b, t.d⟩

/-- Production Karatsuba tower multiplication in `F_{p^2}[v]/(v^2 - w)` where `w^2 = 7`. -/
def towerMul (x y : Ext4) : Ext4 :=
  let a0b0_0 := fieldAdd (fieldMul x.a y.a) (fieldMul 7#u64 (fieldMul x.b y.b))
  let a0b0_1 := fieldSub (fieldMul (fieldAdd x.a x.b) (fieldAdd y.a y.b))
                  (fieldAdd (fieldMul x.a y.a) (fieldMul x.b y.b))
  let a1b1_0 := fieldAdd (fieldMul x.c y.c) (fieldMul 7#u64 (fieldMul x.d y.d))
  let a1b1_1 := fieldSub (fieldMul (fieldAdd x.c x.d) (fieldAdd y.c y.d))
                  (fieldAdd (fieldMul x.c y.c) (fieldMul x.d y.d))
  -- Mul by `w` in `F_{p^2}` maps `(u0, u1) -> (7 * u1, u0)`.
  let c0_0 := fieldAdd a0b0_0 (fieldMul 7#u64 a1b1_1)
  let c0_1 := fieldAdd a0b0_1 a1b1_0
  let s0 := fieldAdd x.a x.c
  let s1 := fieldAdd x.b x.d
  let t0 := fieldAdd y.a y.c
  let t1 := fieldAdd y.b y.d
  let st_0 := fieldAdd (fieldMul s0 t0) (fieldMul 7#u64 (fieldMul s1 t1))
  let st_1 := fieldSub (fieldMul (fieldAdd s0 s1) (fieldAdd t0 t1))
                (fieldAdd (fieldMul s0 t0) (fieldMul s1 t1))
  let c1_0 := fieldSub st_0 (fieldAdd a0b0_0 a1b1_0)
  let c1_1 := fieldSub st_1 (fieldAdd a0b0_1 a1b1_1)
  ⟨c0_0, c0_1, c1_0, c1_1⟩

/-- Exact ring isomorphism between production Karatsuba tower multiplication and `extMul`. -/
theorem towerToPoly_mul_hom (x y : Ext4) :
    towerToPoly (towerMul x y) = extMul (towerToPoly x) (towerToPoly y) := by
  let env := envExt3 x y extZero
  let xT := Ext4Expr.var4 0
  let yT := Ext4Expr.var4 4
  let xP : Ext4Expr := ⟨.var 0, .var 2, .var 1, .var 3⟩
  let yP : Ext4Expr := ⟨.var 4, .var 6, .var 5, .var 7⟩
  let seven := FExpr.const 7
  let a0b0_0 := FExpr.add (.mul xT.a yT.a) (.mul seven (.mul xT.b yT.b))
  let a0b0_1 := FExpr.sub (.mul (.add xT.a xT.b) (.add yT.a yT.b)) (.add (.mul xT.a yT.a) (.mul xT.b yT.b))
  let a1b1_0 := FExpr.add (.mul xT.c yT.c) (.mul seven (.mul xT.d yT.d))
  let a1b1_1 := FExpr.sub (.mul (.add xT.c xT.d) (.add yT.c yT.d)) (.add (.mul xT.c yT.c) (.mul xT.d yT.d))
  let c0_0 := FExpr.add a0b0_0 (.mul seven a1b1_1)
  let c0_1 := FExpr.add a0b0_1 a1b1_0
  let s0 := FExpr.add xT.a xT.c
  let s1 := FExpr.add xT.b xT.d
  let t0 := FExpr.add yT.a yT.c
  let t1 := FExpr.add yT.b yT.d
  let st_0 := FExpr.add (.mul s0 t0) (.mul seven (.mul s1 t1))
  let st_1 := FExpr.sub (.mul (.add s0 s1) (.add t0 t1)) (.add (.mul s0 t0) (.mul s1 t1))
  let c1_0 := FExpr.sub st_0 (.add a0b0_0 a1b1_0)
  let c1_1 := FExpr.sub st_1 (.add a0b0_1 a1b1_1)
  let lhsE : Ext4Expr := ⟨c0_0, c1_0, c0_1, c1_1⟩
  let rhsE : Ext4Expr := Ext4Expr.mul xP yP
  have hl : towerToPoly (towerMul x y) = lhsE.eval env := by
    ext <;> simp [towerToPoly, towerMul, lhsE, c0_0, c0_1, c1_0, c1_1, st_0, st_1, s0, s1, t0, t1,
      a0b0_0, a0b0_1, a1b1_0, a1b1_1, xT, yT, seven, env, envExt3, Ext4Expr.eval, Ext4Expr.var4,
      FExpr.evalZ, fieldAdd_eq_modP, fieldSub_eq_modP, fieldMul_eq_modP, toZ_seven,
      fieldAdd_modP_both, fieldSub_modP_both, fieldMul_modP_both, fieldMul_modP_right]
  have hr : extMul (towerToPoly x) (towerToPoly y) = rhsE.eval env := by
    have hxp : xP.eval env = extCanon (towerToPoly x) := rfl
    have hyp : yP.eval env = extCanon (towerToPoly y) := rfl
    rw [← extMul_canon (towerToPoly x) (towerToPoly y), ← hxp, ← hyp, Ext4Expr.eval_mul]
  rw [hl, hr]
  exact Ext4Expr.eq_of_norm env lhsE rhsE rfl rfl rfl rfl

attribute [irreducible] extAdd extSub extScale extMul

/-! ## Duet Fold, CWYZ Fold, Bridge, Quadratic Sumcheck Wire, Cascade, & Horner Refinements -/

/-- Total mathematical duet expression `odd + alpha * even`. -/
@[expose] def duetValue (v0 v1 : Ext4) (iy it : U64) (alpha : Ext4) : Ext4 :=
  extAdd (extScale (extSub v0 v1) iy) (extMul alpha (extScale (extAdd v0 v1) it))

theorem duet_refines (v0 v1 : Ext4) (iy it : U64) (alpha : Ext4) :
    duet_fold v0 v1 iy it alpha = .ok (duetValue v0 v1 iy it alpha) := by
  simp only [duet_fold, duetValue, affine_combine_refines,
    ext_sub_refines, ext_scale_refines, ext_mul_refines, ext_add_refines, bind_eq_result_bind, Result.bind]

@[expose] def cwyzValue (v0 v1 : Ext4) (iy it yy : U64) (theta alpha beta : Ext4) : Ext4 :=
  let even := extScale (extAdd v0 v1) it
  let odd := extScale (extSub v0 v1) iy
  extAdd odd (extMul (extAdd alpha (extScale beta yy)) (extAdd even (extMul theta odd)))

theorem cwyz_duet_refines (v0 v1 : Ext4) (iy it yy : U64) (theta alpha beta : Ext4) :
    cwyz_duet_fold v0 v1 iy it yy theta alpha beta = .ok (cwyzValue v0 v1 iy it yy theta alpha beta) := by
  simp only [cwyz_duet_fold, cwyzValue, affine_combine_refines,
    ext_sub_refines, ext_scale_refines, ext_mul_refines, ext_add_refines, bind_eq_result_bind, Result.bind]

private theorem scale_add_sub_even {even odd : Ext4} {y0 it : U64}
    (he : IsCanonicalExt4 even) (hit : fieldMul 2#u64 it = 1#u64) :
    extScale (extAdd (extAdd even (extScale odd y0)) (extSub even (extScale odd y0))) it = even := by
  have limb_recover : ∀ (e o : U64), IsCanonical e →
      fieldMul (fieldAdd (fieldAdd e (fieldMul o y0)) (fieldSub e (fieldMul o y0))) it = e := by
    intro e o he_c
    have hsum : fieldAdd (fieldAdd e (fieldMul o y0)) (fieldSub e (fieldMul o y0)) = fieldMul 2#u64 e := by
      let env : Nat → U64 := fun | 0 => e | 1 => o | 2 => y0 | _ => 0#u64
      have h1 : fieldAdd (fieldAdd e (fieldMul o y0)) (fieldSub e (fieldMul o y0)) =
          modP ((FExpr.add (.add (.var 0) (.mul (.var 1) (.var 2))) (.sub (.var 0) (.mul (.var 1) (.var 2)))).evalZ env) := by
        simp [env, FExpr.evalZ, fieldMul_eq_modP, fieldAdd_eq_modP, fieldSub_eq_modP,
          fieldAdd_modP_both, fieldAdd_modP_right, fieldSub_modP_right]
      have h2 : fieldMul 2#u64 e = modP ((FExpr.mul (.const 2) (.var 0)).evalZ env) := by
        simp [env, FExpr.evalZ, fieldMul_eq_modP, toZ_two]
      rw [h1, h2]
      exact modP_eq_of_fexpr env _ _ rfl
    rw [hsum, fieldMul_comm 2#u64 e, fieldMul_assoc, hit, fieldMul_one he_c]
  rcases he with ⟨ha, hb, hc, hd⟩
  unfold extScale extAdd extSub
  exact Ext4.ext (limb_recover _ _ ha) (limb_recover _ _ hb) (limb_recover _ _ hc) (limb_recover _ _ hd)

private theorem scale_add_sub_odd {even odd : Ext4} {y0 iy : U64}
    (ho : IsCanonicalExt4 odd) (hiy : fieldMul (fieldMul 2#u64 y0) iy = 1#u64) :
    extScale (extSub (extAdd even (extScale odd y0)) (extSub even (extScale odd y0))) iy = odd := by
  have limb_recover : ∀ (e o : U64), IsCanonical o →
      fieldMul (fieldSub (fieldAdd e (fieldMul o y0)) (fieldSub e (fieldMul o y0))) iy = o := by
    intro e o ho_c
    have hdiff : fieldSub (fieldAdd e (fieldMul o y0)) (fieldSub e (fieldMul o y0)) =
        fieldMul o (fieldMul 2#u64 y0) := by
      let env : Nat → U64 := fun | 0 => e | 1 => o | 2 => y0 | _ => 0#u64
      have h1 : fieldSub (fieldAdd e (fieldMul o y0)) (fieldSub e (fieldMul o y0)) =
          modP ((FExpr.sub (.add (.var 0) (.mul (.var 1) (.var 2))) (.sub (.var 0) (.mul (.var 1) (.var 2)))).evalZ env) := by
        simp [env, FExpr.evalZ, fieldMul_eq_modP, fieldAdd_eq_modP, fieldSub_eq_modP,
          fieldSub_modP_both, fieldAdd_modP_right, fieldSub_modP_right]
      have h2 : fieldMul o (fieldMul 2#u64 y0) = modP ((FExpr.mul (.var 1) (.mul (.const 2) (.var 2))).evalZ env) := by
        simp [env, FExpr.evalZ, fieldMul_eq_modP, fieldMul_modP_right, toZ_two]
      rw [h1, h2]
      exact modP_eq_of_fexpr env _ _ rfl
    rw [hdiff, fieldMul_assoc, hiy, fieldMul_one ho_c]
  rcases ho with ⟨ha, hb, hc, hd⟩
  unfold extScale extAdd extSub
  exact Ext4.ext (limb_recover _ _ ha) (limb_recover _ _ hb) (limb_recover _ _ hc) (limb_recover _ _ hd)

/-- Algebraic coset soundness of `duet_fold`: on `v0 = E + y0 * O`, `v1 = E - y0 * O`,
    `duetValue` recovers `O + alpha * E`. -/
theorem duet_fold_algebraic_sound
    {even odd : Ext4} {y0 iy it : U64} (alpha : Ext4)
    (he : IsCanonicalExt4 even) (ho : IsCanonicalExt4 odd)
    (hit : fieldMul 2#u64 it = 1#u64)
    (hiy : fieldMul (fieldMul 2#u64 y0) iy = 1#u64) :
    duetValue (extAdd even (extScale odd y0)) (extSub even (extScale odd y0)) iy it alpha =
      extAdd odd (extMul alpha even) := by
  unfold duetValue
  rw [scale_add_sub_even he hit, scale_add_sub_odd ho hiy]

/-- Algebraic coset soundness of `cwyz_duet_fold`: on `v0 = E + y0 * O`, `v1 = E - y0 * O`,
    `cwyzValue` recovers `O + (alpha + beta * y0^2) * (E + theta * O)`. -/
theorem cwyz_duet_fold_algebraic_sound
    {even odd : Ext4} {y0 iy it : U64} (theta alpha beta : Ext4)
    (he : IsCanonicalExt4 even) (ho : IsCanonicalExt4 odd)
    (hit : fieldMul 2#u64 it = 1#u64)
    (hiy : fieldMul (fieldMul 2#u64 y0) iy = 1#u64) :
    cwyzValue (extAdd even (extScale odd y0)) (extSub even (extScale odd y0))
        iy it (fieldMul y0 y0) theta alpha beta =
      extAdd odd (extMul (extAdd alpha (extScale beta (fieldMul y0 y0))) (extAdd even (extMul theta odd))) := by
  unfold cwyzValue
  rw [scale_add_sub_even he hit, scale_add_sub_odd ho hiy]

/-- Pure CWYZ dual linear-functional bridge expression. -/
def cwyzBridgeValue (w0 w1 w2 w3 w4 claim phi theta alpha beta : Ext4) : Ext4 :=
  let f := extAdd w0 (extMul phi w1)
  let g := extAdd w2 (extMul phi (extSub claim w0))
  let core := extAdd g (extMul alpha (extAdd f (extMul theta g)))
  let shift := extMul beta (extAdd w3 (extMul theta w4))
  extAdd core shift

theorem cwyz_bridge_claim_step_refines
    (w0 w1 w2 w3 w4 claim phi theta alpha beta : Ext4) :
    cwyz_bridge_claim_step w0 w1 w2 w3 w4 claim phi theta alpha beta =
      .ok (cwyzBridgeValue w0 w1 w2 w3 w4 claim phi theta alpha beta) := by
  simp only [cwyz_bridge_claim_step, cwyzBridgeValue,
    ext_mul_refines, ext_add_refines, ext_sub_refines, bind_eq_result_bind, Result.bind]

private def envExt9 (a0 a1 b0 b1 kn phi theta alpha beta : Ext4) : Nat → U64 := fun idx =>
  let sel (e : Ext4) (r : Nat) : U64 :=
    match r with | 0 => e.a | 1 => e.b | 2 => e.c | _ => e.d
  match idx / 4 with
  | 0 => sel a0 (idx % 4)
  | 1 => sel a1 (idx % 4)
  | 2 => sel b0 (idx % 4)
  | 3 => sel b1 (idx % 4)
  | 4 => sel kn (idx % 4)
  | 5 => sel phi (idx % 4)
  | 6 => sel theta (idx % 4)
  | 7 => sel alpha (idx % 4)
  | 8 => sel beta (idx % 4)
  | _ => 0#u64

/-- Dual-functional soundness of `cwyz_bridge_claim_step`: on honest cross-terms
    `w0 = a0*b0`, `w1 = a0*b1`, `w2 = a1*b0`, `claim = a0*b0 + a1*b1`, `w3 = a0*kn`, `w4 = a1*kn`,
    `cwyzBridgeValue` equals `c0' * k0' + c1' * kn` where
    `c0' = a1 + alpha*(a0 + theta*a1)`, `c1' = beta*(a0 + theta*a1)`, `k0' = b0 + phi*b1`. -/
theorem cwyz_bridge_claim_step_dual_sound
    (a0 a1 b0 b1 kn phi theta alpha beta : Ext4) :
    cwyzBridgeValue
        (extMul a0 b0) (extMul a0 b1) (extMul a1 b0) (extMul a0 kn) (extMul a1 kn)
        (extAdd (extMul a0 b0) (extMul a1 b1)) phi theta alpha beta =
      extAdd
        (extMul (extAdd a1 (extMul alpha (extAdd a0 (extMul theta a1)))) (extAdd b0 (extMul phi b1)))
        (extMul (extMul beta (extAdd a0 (extMul theta a1))) kn) := by
  let env := envExt9 a0 a1 b0 b1 kn phi theta alpha beta
  have v0 : (Ext4Expr.var4 0).eval env = extCanon a0 := rfl
  have v1 : (Ext4Expr.var4 4).eval env = extCanon a1 := rfl
  have v2 : (Ext4Expr.var4 8).eval env = extCanon b0 := rfl
  have v3 : (Ext4Expr.var4 12).eval env = extCanon b1 := rfl
  have v4 : (Ext4Expr.var4 16).eval env = extCanon kn := rfl
  have v5 : (Ext4Expr.var4 20).eval env = extCanon phi := rfl
  have v6 : (Ext4Expr.var4 24).eval env = extCanon theta := rfl
  have v7 : (Ext4Expr.var4 28).eval env = extCanon alpha := rfl
  have v8 : (Ext4Expr.var4 32).eval env = extCanon beta := rfl
  let ea0 := Ext4Expr.var4 0
  let ea1 := Ext4Expr.var4 4
  let eb0 := Ext4Expr.var4 8
  let eb1 := Ext4Expr.var4 12
  let ekn := Ext4Expr.var4 16
  let ephi := Ext4Expr.var4 20
  let etheta := Ext4Expr.var4 24
  let ealpha := Ext4Expr.var4 28
  let ebeta := Ext4Expr.var4 32
  let ew0 := Ext4Expr.mul ea0 eb0
  let ew1 := Ext4Expr.mul ea0 eb1
  let ew2 := Ext4Expr.mul ea1 eb0
  let ew3 := Ext4Expr.mul ea0 ekn
  let ew4 := Ext4Expr.mul ea1 ekn
  let eclaim := Ext4Expr.add ew0 (Ext4Expr.mul ea1 eb1)
  let ef := Ext4Expr.add ew0 (Ext4Expr.mul ephi ew1)
  let eg := Ext4Expr.add ew2 (Ext4Expr.mul ephi (Ext4Expr.sub eclaim ew0))
  let lhsE := Ext4Expr.add (Ext4Expr.add eg (Ext4Expr.mul ealpha (Ext4Expr.add ef (Ext4Expr.mul etheta eg))))
                (Ext4Expr.mul ebeta (Ext4Expr.add ew3 (Ext4Expr.mul etheta ew4)))
  let ec0' := Ext4Expr.add ea1 (Ext4Expr.mul ealpha (Ext4Expr.add ea0 (Ext4Expr.mul etheta ea1)))
  let ec1' := Ext4Expr.mul ebeta (Ext4Expr.add ea0 (Ext4Expr.mul etheta ea1))
  let ek0' := Ext4Expr.add eb0 (Ext4Expr.mul ephi eb1)
  let rhsE := Ext4Expr.add (Ext4Expr.mul ec0' ek0') (Ext4Expr.mul ec1' ekn)
  have hw0 : ew0.eval env = extMul a0 b0 := by rw [← Ext4Expr.eval_mul, v0, v2, extMul_canon]
  have hw1 : ew1.eval env = extMul a0 b1 := by rw [← Ext4Expr.eval_mul, v0, v3, extMul_canon]
  have hw2 : ew2.eval env = extMul a1 b0 := by rw [← Ext4Expr.eval_mul, v1, v2, extMul_canon]
  have hw3 : ew3.eval env = extMul a0 kn := by rw [← Ext4Expr.eval_mul, v0, v4, extMul_canon]
  have hw4 : ew4.eval env = extMul a1 kn := by rw [← Ext4Expr.eval_mul, v1, v4, extMul_canon]
  have hb11 : (Ext4Expr.mul ea1 eb1).eval env = extMul a1 b1 := by rw [← Ext4Expr.eval_mul, v1, v3, extMul_canon]
  have hcl : eclaim.eval env = extAdd (extMul a0 b0) (extMul a1 b1) := by
    rw [← Ext4Expr.eval_add, hw0, hb11]
  have hl : cwyzBridgeValue (extMul a0 b0) (extMul a0 b1) (extMul a1 b0) (extMul a0 kn) (extMul a1 kn)
      (extAdd (extMul a0 b0) (extMul a1 b1)) phi theta alpha beta = lhsE.eval env := by
    unfold cwyzBridgeValue
    simp only [lhsE, ef, eg]
    rw [← Ext4Expr.eval_add, ← Ext4Expr.eval_add, ← Ext4Expr.eval_mul, ← Ext4Expr.eval_add,
      ← Ext4Expr.eval_mul, ← Ext4Expr.eval_add, ← Ext4Expr.eval_mul, ← Ext4Expr.eval_sub,
      ← Ext4Expr.eval_add, ← Ext4Expr.eval_mul, ← Ext4Expr.eval_add, ← Ext4Expr.eval_mul,
      ← Ext4Expr.eval_add, ← Ext4Expr.eval_mul,
      hw0, hw1, hw2, hw3, hw4, hcl, v5, v6, v7, v8]
    have c_w1 : extCanon (extMul a0 b1) = extMul a0 b1 := extCanon_eq_of_canonical (extMul_canonical a0 b1)
    have c_w4 : extCanon (extMul a1 kn) = extMul a1 kn := extCanon_eq_of_canonical (extMul_canonical a1 kn)
    have hsub_c : extCanon (extSub (extAdd (extMul a0 b0) (extMul a1 b1)) (extMul a0 b0)) =
        extSub (extAdd (extMul a0 b0) (extMul a1 b1)) (extMul a0 b0) :=
      extCanon_eq_of_canonical (extSub_canonical _ _)
    rw [← c_w1, extMul_canon phi, c_w1, ← hsub_c, extMul_canon phi, hsub_c]
    set gVal := extAdd (extMul a1 b0) (extMul phi (extSub (extAdd (extMul a0 b0) (extMul a1 b1)) (extMul a0 b0)))
    have c_g : extCanon gVal = gVal := extCanon_eq_of_canonical (extAdd_canonical _ _)
    rw [← c_g, extMul_canon theta, c_g]
    set fgVal := extAdd (extAdd (extMul a0 b0) (extMul phi (extMul a0 b1))) (extMul theta gVal)
    have c_fg : extCanon fgVal = fgVal := extCanon_eq_of_canonical (extAdd_canonical _ _)
    rw [← c_fg, extMul_canon alpha, c_fg]
    rw [← c_w4, extMul_canon theta, c_w4]
    set sVal := extAdd (extMul a0 kn) (extMul theta (extMul a1 kn))
    have c_s : extCanon sVal = sVal := extCanon_eq_of_canonical (extAdd_canonical _ _)
    rw [← c_s, extMul_canon beta, c_s]
  have hr : extAdd
      (extMul (extAdd a1 (extMul alpha (extAdd a0 (extMul theta a1)))) (extAdd b0 (extMul phi b1)))
      (extMul (extMul beta (extAdd a0 (extMul theta a1))) kn) = rhsE.eval env := by
    simp only [rhsE, ec0', ec1', ek0']
    rw [← Ext4Expr.eval_add, ← Ext4Expr.eval_mul, ← Ext4Expr.eval_mul,
      ← Ext4Expr.eval_add, ← Ext4Expr.eval_mul, ← Ext4Expr.eval_add, ← Ext4Expr.eval_mul,
      ← Ext4Expr.eval_add, ← Ext4Expr.eval_mul, ← Ext4Expr.eval_mul, ← Ext4Expr.eval_add,
      ← Ext4Expr.eval_mul, v0, v1, v2, v3, v4, v5, v6, v7, v8]
    rw [extMul_canon theta a1, extMul_canon phi b1]
    have ca01 : extCanon (extMul theta a1) = extMul theta a1 := extCanon_eq_of_canonical (extMul_canonical theta a1)
    have cb01 : extCanon (extMul phi b1) = extMul phi b1 := extCanon_eq_of_canonical (extMul_canonical phi b1)
    rw [← ca01, extAdd_canon a0, ca01, ← cb01, extAdd_canon b0, cb01]
    set m01 := extAdd a0 (extMul theta a1)
    have cm01 : extCanon m01 = m01 := extCanon_eq_of_canonical (extAdd_canonical _ _)
    rw [← cm01, extMul_canon alpha, extMul_canon beta, cm01]
    have cam : extCanon (extMul alpha m01) = extMul alpha m01 := extCanon_eq_of_canonical (extMul_canonical _ _)
    rw [← cam, extAdd_canon a1, cam]
    have cbm : extCanon (extMul beta m01) = extMul beta m01 := extCanon_eq_of_canonical (extMul_canonical _ _)
    rw [← cbm, extMul_canon (extMul beta m01) kn, cbm]
  rw [hl, hr]
  exact Ext4Expr.eq_of_norm env lhsE rhsE rfl rfl rfl rfl

/-- Pure quadratic wire reconstruction `c0 + r * ((sum_claim - 2*c0 - c2) + c2 * r)`. -/
def quadraticWireValue (c0 c2 sum_claim r : Ext4) : Ext4 :=
  let c1 := extSub (extSub sum_claim (extAdd c0 c0)) c2
  extAdd (extMul (extAdd (extMul c2 r) c1) r) c0

theorem eval_quadratic_sumcheck_wire_refines (c0 c2 sum_claim r : Ext4) :
    eval_quadratic_sumcheck_wire c0 c2 sum_claim r =
      .ok (quadraticWireValue c0 c2 sum_claim r) := by
  simp only [eval_quadratic_sumcheck_wire, quadraticWireValue,
    ext_add_refines, ext_sub_refines, ext_mul_refines, bind_eq_result_bind, Result.bind]

/-- Boolean hypercube sum guarantee: `eval(0) + eval(1) = sum_claim` unconditionally for canonical `sum_claim`. -/
theorem eval_quadratic_sumcheck_wire_hypercube_sum
    (c0 c2 sum_claim : Ext4) (hs : IsCanonicalExt4 sum_claim) :
    extAdd (quadraticWireValue c0 c2 sum_claim extZero)
           (quadraticWireValue c0 c2 sum_claim extOne) = sum_claim := by
  unfold quadraticWireValue
  rw [extMul_zero, extMul_zero, zero_extAdd (extSub_canonical _ _), extMul_one (extAdd_canonical _ _)]
  let env := envExt3 c0 c2 sum_claim
  have hc0 : (Ext4Expr.var4 0).eval env = extCanon c0 := rfl
  have hc2 : (Ext4Expr.var4 4).eval env = extCanon c2 := rfl
  have hsc : (Ext4Expr.var4 8).eval env = extCanon sum_claim := rfl
  let ec0 := Ext4Expr.var4 0
  let ec2 := Ext4Expr.var4 4
  let esc := Ext4Expr.var4 8
  let ec1 := Ext4Expr.sub (Ext4Expr.sub esc (Ext4Expr.add ec0 ec0)) ec2
  let lhsE := Ext4Expr.add (Ext4Expr.add ⟨.const 0, .const 0, .const 0, .const 0⟩ ec0)
                (Ext4Expr.add (Ext4Expr.add ec2 ec1) ec0)
  have hl : extAdd (extAdd extZero c0)
      (extAdd (extAdd c2 (extSub (extSub sum_claim (extAdd c0 c0)) c2)) c0) = lhsE.eval env := by
    have hz : (⟨.const 0, .const 0, .const 0, .const 0⟩ : Ext4Expr).eval env = extCanon extZero := rfl
    simp only [lhsE, ec1]
    rw [← Ext4Expr.eval_add, ← Ext4Expr.eval_add, ← Ext4Expr.eval_add, ← Ext4Expr.eval_add,
      ← Ext4Expr.eval_sub, ← Ext4Expr.eval_sub, ← Ext4Expr.eval_add, hz, hc0, hc2, hsc]
    rw [extAdd_canon extZero c0, extAdd_canon c0 c0]
    have cc00 : extCanon (extAdd c0 c0) = extAdd c0 c0 := extCanon_eq_of_canonical (extAdd_canonical c0 c0)
    rw [← cc00, extSub_canon sum_claim, cc00]
    have csub1 : extCanon (extSub sum_claim (extAdd c0 c0)) = extSub sum_claim (extAdd c0 c0) :=
      extCanon_eq_of_canonical (extSub_canonical _ _)
    rw [← csub1, extSub_canon _ c2, csub1]
    have cc1 : extCanon (extSub (extSub sum_claim (extAdd c0 c0)) c2) =
        extSub (extSub sum_claim (extAdd c0 c0)) c2 := extCanon_eq_of_canonical (extSub_canonical _ _)
    rw [← cc1, extAdd_canon c2, cc1]
    have cc21 : extCanon (extAdd c2 (extSub (extSub sum_claim (extAdd c0 c0)) c2)) =
        extAdd c2 (extSub (extSub sum_claim (extAdd c0 c0)) c2) := extCanon_eq_of_canonical (extAdd_canonical _ _)
    rw [← cc21, extAdd_canon _ c0, cc21]
  rw [hl, ← eval_var4_8 (x := c0) (y := c2) hs]
  exact Ext4Expr.eq_of_norm env lhsE esc rfl rfl rfl rfl

/-- Pure affine cascade claim step `acc + w0 * eval_at_point + w1 * shifted_eval`. -/
def affineCascadeStepValue (acc w0 w1 eval_at_point shifted_eval : Ext4) : Ext4 :=
  extAdd (extAdd acc (extMul w0 eval_at_point)) (extMul w1 shifted_eval)

theorem affine_cascade_claim_step_refines
    (acc w0 w1 eval_at_point shifted_eval : Ext4) :
    affine_cascade_claim_step acc w0 w1 eval_at_point shifted_eval =
      .ok (affineCascadeStepValue acc w0 w1 eval_at_point shifted_eval) := by
  simp only [affine_cascade_claim_step, affineCascadeStepValue,
    ext_mul_refines, ext_add_refines, bind_eq_result_bind, Result.bind]

/-! ## Arbitrary-Length Horner Evaluation over `Ext4` at Base Point `z : U64` -/

/-- Exact descending-index Horner fold matching `eval_ext4_univariate_at_base_loop`. -/
@[expose] def hornerSpec (coeffs : List Ext4) (z : U64) (init : Ext4 := extZero) : Ext4 :=
  coeffs.foldr (fun c acc => extAdd (extScale acc z) c) init

/-- Textbook ascending-degree polynomial evaluation `c_0 + z * (c_1 + z * ...)`. -/
def evalPolyAscending : List Ext4 → U64 → Ext4
  | [], _ => extZero
  | c :: rest, z => extAdd c (extScale (evalPolyAscending rest z) z)

theorem hornerSpec_nil (z : U64) (init : Ext4) : hornerSpec [] z init = init := rfl

theorem hornerSpec_cons (c : Ext4) (rest : List Ext4) (z : U64) (init : Ext4) :
    hornerSpec (c :: rest) z init = extAdd (extScale (hornerSpec rest z init) z) c := rfl

theorem hornerSpec_canonical (coeffs : List Ext4) (z : U64) :
    IsCanonicalExt4 (hornerSpec coeffs z extZero) := by
  induction coeffs with
  | nil => exact ⟨by decide, by decide, by decide, by decide⟩
  | cons c rest _ => exact extAdd_canonical _ _

/-- For canonical coefficients, `hornerSpec coeffs z extZero` coincides with `evalPolyAscending coeffs z`. -/
theorem hornerSpec_eq_evalPolyAscending (coeffs : List Ext4) (z : U64)
    (_hcan : ∀ c ∈ coeffs, IsCanonicalExt4 c) :
    hornerSpec coeffs z extZero = evalPolyAscending coeffs z := by
  induction coeffs with
  | nil => rfl
  | cons c rest ih =>
    have hrest : ∀ x ∈ rest, IsCanonicalExt4 x := fun x hx => _hcan x (List.mem_cons_of_mem c hx)
    simp only [hornerSpec_cons, evalPolyAscending, ih hrest, extAdd_comm]

end qsag_whir_verified.proofs

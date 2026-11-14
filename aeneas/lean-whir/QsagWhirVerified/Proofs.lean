module
public import QsagWhirVerified.Arithmetic
import all Aeneas
import all Aeneas.Std.Types
import all Aeneas.Std.Containers
public section
open Aeneas Aeneas.Std
namespace qsag_whir_verified.proofs
attribute [local simp] UScalar.val UScalarTy.numBits
set_option linter.unusedSimpArgs false

/-! ## 1. Canonical Goldilocks & `Ext4` Wire Decoding -/

theorem decode_canonical_u64_spec (x : U64) :
    decode_canonical_u64 x = .ok (if x.val < goldilocksMod then some x else none) := by
  unfold decode_canonical_u64
  by_cases h : x < GOLDILOCKS_P
  · have hv : x.val < goldilocksMod := by
      simpa only [UScalar.lt_iff_val, goldilocks_p_val] using h
    simp [h, hv]
  · have hv : ¬ x.val < goldilocksMod := by
      simpa only [UScalar.lt_iff_val, goldilocks_p_val] using h
    simp [h, hv]

theorem decode_canonical_u64_some_iff (x y : U64) :
    decode_canonical_u64 x = .ok (some y) ↔ IsCanonical x ∧ y = x := by
  rw [decode_canonical_u64_spec]
  by_cases h : x.val < goldilocksMod
  · simp [IsCanonical, h, eq_comm]
  · simp [IsCanonical, h]

theorem decode_canonical_u64_none_iff (x : U64) :
    decode_canonical_u64 x = .ok none ↔ goldilocksMod ≤ x.val := by
  rw [decode_canonical_u64_spec]
  by_cases h : x.val < goldilocksMod
  · simp [h]; omega
  · simp [h]; omega

theorem decode_canonical_u64_rejects_noncanonical (x : U64)
    (h : GOLDILOCKS_P.val ≤ x.val) : decode_canonical_u64 x = .ok none := by
  rw [decode_canonical_u64_none_iff]
  simpa only [goldilocks_p_val] using h

theorem decode_canonical_ext4_spec (a b c d : U64) :
    decode_canonical_ext4 a b c d =
      .ok (if IsCanonical a ∧ IsCanonical b ∧ IsCanonical c ∧ IsCanonical d
           then some ⟨a, b, c, d⟩ else none) := by
  unfold decode_canonical_ext4
  by_cases ha : a < GOLDILOCKS_P
  · have ha' : IsCanonical a := by simpa only [UScalar.lt_iff_val, goldilocks_p_val] using ha
    by_cases hb : b < GOLDILOCKS_P
    · have hb' : IsCanonical b := by simpa only [UScalar.lt_iff_val, goldilocks_p_val] using hb
      by_cases hc : c < GOLDILOCKS_P
      · have hc' : IsCanonical c := by simpa only [UScalar.lt_iff_val, goldilocks_p_val] using hc
        by_cases hd : d < GOLDILOCKS_P
        · have hd' : IsCanonical d := by simpa only [UScalar.lt_iff_val, goldilocks_p_val] using hd
          simp [ha, hb, hc, hd, ha', hb', hc', hd']
        · have hd' : ¬ IsCanonical d := by simpa only [UScalar.lt_iff_val, goldilocks_p_val] using hd
          simp [ha, hb, hc, hd, ha', hb', hc', hd']
      · have hc' : ¬ IsCanonical c := by simpa only [UScalar.lt_iff_val, goldilocks_p_val] using hc
        simp [ha, hb, hc, ha', hb', hc']
    · have hb' : ¬ IsCanonical b := by simpa only [UScalar.lt_iff_val, goldilocks_p_val] using hb
      simp [ha, hb, ha', hb']
  · have ha' : ¬ IsCanonical a := by simpa only [UScalar.lt_iff_val, goldilocks_p_val] using ha
    simp [ha, ha']

theorem decode_canonical_ext4_some_iff (a b c d : U64) (out : Ext4) :
    decode_canonical_ext4 a b c d = .ok (some out) ↔
      IsCanonical a ∧ IsCanonical b ∧ IsCanonical c ∧ IsCanonical d ∧ out = ⟨a, b, c, d⟩ := by
  rw [decode_canonical_ext4_spec]
  by_cases h : IsCanonical a ∧ IsCanonical b ∧ IsCanonical c ∧ IsCanonical d
  · rcases h with ⟨ha, hb, hc, hd⟩
    simp [ha, hb, hc, hd, eq_comm]
  · simp [h]
    intro ha hb hc hd _
    exact h ⟨ha, hb, hc, hd⟩

theorem decode_canonical_ext4_none_iff (a b c d : U64) :
    decode_canonical_ext4 a b c d = .ok none ↔
      ¬ (IsCanonical a ∧ IsCanonical b ∧ IsCanonical c ∧ IsCanonical d) := by
  rw [decode_canonical_ext4_spec]
  by_cases h : IsCanonical a ∧ IsCanonical b ∧ IsCanonical c ∧ IsCanonical d
  · simp [h]
  · simp [h]

/-! ## 2. `Ext4` Equality, Duet Folding, CWYZ Folding, & Dual Bridge Soundness -/

theorem ext_eq_spec (x y : Ext4) : ext_eq x y = .ok (decide (x = y)) := by
  cases x; cases y
  simp only [ext_eq]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

theorem ext_eq_sound (x y : Ext4) : ext_eq x y = .ok true ↔ x = y := by
  rw [ext_eq_spec]
  simp

theorem verify_affine_duet_fold_step_spec (v0 v1 : Ext4) (iy it : U64)
    (alpha claimed : Ext4) :
    verify_affine_duet_fold_step v0 v1 iy it alpha claimed =
      .ok (decide (duetValue v0 v1 iy it alpha = claimed)) := by
  unfold verify_affine_duet_fold_step
  rw [duet_refines]
  simp [Result.bind, ext_eq_spec]

theorem verify_affine_duet_fold_step_sound (v0 v1 : Ext4) (iy it : U64)
    (alpha claimed : Ext4) :
    verify_affine_duet_fold_step v0 v1 iy it alpha claimed = .ok true ↔
      claimed = duetValue v0 v1 iy it alpha := by
  rw [verify_affine_duet_fold_step_spec]
  simp [eq_comm]

theorem verify_affine_duet_fold_step_coset_sound
    {even odd : Ext4} {y0 iy it : U64} (alpha claimed : Ext4)
    (he : IsCanonicalExt4 even) (ho : IsCanonicalExt4 odd)
    (hit : fieldMul 2#u64 it = 1#u64)
    (hiy : fieldMul (fieldMul 2#u64 y0) iy = 1#u64) :
    verify_affine_duet_fold_step
        (extAdd even (extScale odd y0)) (extSub even (extScale odd y0))
        iy it alpha claimed = .ok true ↔
      claimed = extAdd odd (extMul alpha even) := by
  rw [verify_affine_duet_fold_step_sound, duet_fold_algebraic_sound alpha he ho hit hiy]

theorem verify_cwyz_duet_fold_step_spec
    (v0 v1 : Ext4) (iy it yy : U64) (theta alpha beta claimed : Ext4) :
    verify_cwyz_duet_fold_step v0 v1 iy it yy theta alpha beta claimed =
      .ok (decide (cwyzValue v0 v1 iy it yy theta alpha beta = claimed)) := by
  unfold verify_cwyz_duet_fold_step
  rw [cwyz_duet_refines]
  simp [Result.bind, ext_eq_spec]

theorem verify_cwyz_duet_fold_step_sound
    (v0 v1 : Ext4) (iy it yy : U64) (theta alpha beta claimed : Ext4) :
    verify_cwyz_duet_fold_step v0 v1 iy it yy theta alpha beta claimed = .ok true ↔
      claimed = cwyzValue v0 v1 iy it yy theta alpha beta := by
  rw [verify_cwyz_duet_fold_step_spec]
  simp [eq_comm]

theorem verify_cwyz_duet_fold_step_coset_sound
    {even odd : Ext4} {y0 iy it : U64} (theta alpha beta claimed : Ext4)
    (he : IsCanonicalExt4 even) (ho : IsCanonicalExt4 odd)
    (hit : fieldMul 2#u64 it = 1#u64)
    (hiy : fieldMul (fieldMul 2#u64 y0) iy = 1#u64) :
    verify_cwyz_duet_fold_step
        (extAdd even (extScale odd y0)) (extSub even (extScale odd y0))
        iy it (fieldMul y0 y0) theta alpha beta claimed = .ok true ↔
      claimed = extAdd odd (extMul (extAdd alpha (extScale beta (fieldMul y0 y0)))
                  (extAdd even (extMul theta odd))) := by
  rw [verify_cwyz_duet_fold_step_sound, cwyz_duet_fold_algebraic_sound theta alpha beta he ho hit hiy]

theorem verify_cwyz_bridge_claim_step_spec
    (w0 w1 w2 w3 w4 claim phi theta alpha beta claimed_next : Ext4) :
    verify_cwyz_bridge_claim_step w0 w1 w2 w3 w4 claim phi theta alpha beta claimed_next =
      .ok (decide (cwyzBridgeValue w0 w1 w2 w3 w4 claim phi theta alpha beta = claimed_next)) := by
  unfold verify_cwyz_bridge_claim_step
  rw [cwyz_bridge_claim_step_refines]
  simp [Result.bind, ext_eq_spec]

theorem verify_cwyz_bridge_claim_step_sound
    (w0 w1 w2 w3 w4 claim phi theta alpha beta claimed_next : Ext4) :
    verify_cwyz_bridge_claim_step w0 w1 w2 w3 w4 claim phi theta alpha beta claimed_next = .ok true ↔
      claimed_next = cwyzBridgeValue w0 w1 w2 w3 w4 claim phi theta alpha beta := by
  rw [verify_cwyz_bridge_claim_step_spec]
  simp [eq_comm]

theorem verify_cwyz_bridge_claim_step_dual_sound
    (a0 a1 b0 b1 kn phi theta alpha beta claimed_next : Ext4) :
    verify_cwyz_bridge_claim_step
        (extMul a0 b0) (extMul a0 b1) (extMul a1 b0) (extMul a0 kn) (extMul a1 kn)
        (extAdd (extMul a0 b0) (extMul a1 b1)) phi theta alpha beta claimed_next = .ok true ↔
      claimed_next = extAdd
        (extMul (extAdd a1 (extMul alpha (extAdd a0 (extMul theta a1)))) (extAdd b0 (extMul phi b1)))
        (extMul (extMul beta (extAdd a0 (extMul theta a1))) kn) := by
  rw [verify_cwyz_bridge_claim_step_sound, cwyz_bridge_claim_step_dual_sound]

/-! ## 3. Arbitrary-Slice Horner Evaluation & Polynomial Pin Verification -/

private theorem list_take_succ_eq {α : Type} (xs : List α) (k : Nat) (hk : k < xs.length) :
    xs.take (k + 1) = xs.take k ++ [xs[k]'hk] := by
  induction xs generalizing k with
  | nil => cases hk
  | cons x rest ih =>
    cases k with
    | zero => rfl
    | succ k' =>
      have hk' : k' < rest.length := Nat.lt_of_succ_lt_succ hk
      simp [List.take, ih k' hk']

private theorem eval_ext4_univariate_loop_fuel
    (coeffs : Slice Ext4) (z : U64) (k : Nat)
    (hk : k ≤ coeffs.val.length) (acc : Ext4) (rem : Usize) (hrem : rem.val = k) :
    loopFuel (k + 1)
      (fun (acc1, rem1) => eval_ext4_univariate_at_base_loop.body coeffs z acc1 rem1)
      (acc, rem) = .ok (hornerSpec (coeffs.val.take k) z acc) := by
  induction k generalizing acc rem with
  | zero =>
    have hgt : ¬ (rem > 0#usize) := by
      simp [GT.gt, UScalar.lt_iff_val, hrem]
    simp [loopFuel_succ, eval_ext4_univariate_at_base_loop.body, hgt, hornerSpec]
  | succ k' ih =>
    have hk' : k' < coeffs.val.length := hk
    have hgt : rem > 0#usize := by
      simp [GT.gt, UScalar.lt_iff_val, hrem]
    have hsub_le : (1#usize).val ≤ rem.val := by
      change 1 ≤ rem.val
      omega
    let rem1 : Usize := ⟨rem.bv - (1#usize).bv⟩
    have hsub : (rem - 1#usize : Result Usize) = .ok rem1 := by
      simp [hSub_uscalar_eq, hsub_le, rem1]
    have hrem1 : rem1.val = k' := by
      have hv : rem1.val = rem.val - 1 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr hsub_le)
      omega
    have hidx : Slice.index_usize coeffs rem1 = .ok (coeffs.val[k']'hk') := by
      unfold Slice.index_usize
      have hlt : rem1.val < coeffs.val.length := by omega
      simp [hlt, hrem1]
    simp only [loopFuel_succ, eval_ext4_univariate_at_base_loop.body, hgt, ↓reduceIte,
      hsub, bind_eq_result_bind, result_bind_ok, hidx, ext_scale_refines, ext_add_refines]
    rw [ih (Nat.le_of_lt hk') (extAdd (extScale acc z) (coeffs.val[k']'hk')) rem1 hrem1]
    congr 1
    unfold hornerSpec
    rw [list_take_succ_eq coeffs.val k' hk', List.foldr_append]
    rfl

theorem eval_ext4_univariate_at_base_spec (coeffs : Slice Ext4) (z : U64) :
    eval_ext4_univariate_at_base coeffs z = .ok (hornerSpec coeffs.val z extZero) := by
  unfold eval_ext4_univariate_at_base eval_ext4_univariate_at_base_loop
  have hfuel : coeffs.val.length + 1 ≤ loopMaxFuel := by
    have hlen : (Slice.len coeffs).val = coeffs.val.length := Slice.len_val coeffs
    rw [← hlen]
    exact usize_lt_loopMaxFuel (Slice.len coeffs)
  have hloop := eval_ext4_univariate_loop_fuel coeffs z coeffs.val.length (Nat.le_refl _)
    extZero (Slice.len coeffs) (Slice.len_val coeffs)
  rw [List.take_length] at hloop
  exact loop_ok_of_loopFuel hfuel hloop

theorem verify_ext4_univariate_at_base_pin_spec
    (coeffs : Slice Ext4) (z : U64) (expected : Ext4) :
    verify_ext4_univariate_at_base_pin coeffs z expected =
      .ok (decide (hornerSpec coeffs.val z extZero = expected)) := by
  unfold verify_ext4_univariate_at_base_pin
  rw [eval_ext4_univariate_at_base_spec]
  simp [Result.bind, ext_eq_spec]

theorem verify_ext4_univariate_at_base_pin_sound
    (coeffs : Slice Ext4) (z : U64) (expected : Ext4) :
    verify_ext4_univariate_at_base_pin coeffs z expected = .ok true ↔
      expected = hornerSpec coeffs.val z extZero := by
  rw [verify_ext4_univariate_at_base_pin_spec]
  simp [eq_comm]

theorem verify_ext4_univariate_at_base_pin_ascending_sound
    (coeffs : Slice Ext4) (z : U64) (expected : Ext4)
    (hcan : ∀ c ∈ coeffs.val, IsCanonicalExt4 c) :
    verify_ext4_univariate_at_base_pin coeffs z expected = .ok true ↔
      expected = evalPolyAscending coeffs.val z := by
  rw [verify_ext4_univariate_at_base_pin_sound, hornerSpec_eq_evalPolyAscending coeffs.val z hcan]

/-! ## 4. Stage Proof-of-Work Mask Gate (Direct BitVec Proof, Zero Case Enumeration) -/

private theorem scalar_eq_bv (a b : U64) : a = b ↔ a.bv = b.bv :=
  ⟨congrArg UScalar.bv, UScalar.ext⟩

theorem verify_stage_pow_mask_spec (word : U64) (bits : U32) :
    verify_stage_pow_mask word bits =
      .ok (decide (bits.val ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ bits.val - 1) = 0)) := by
  by_cases hb : bits.val ≤ 32
  · have hng : ¬ (bits > 32#u32) := by
      simp only [GT.gt, UScalar.lt_iff_val]
      change ¬ (32 < bits.val)
      omega
    have hlt64 : bits.val < 64 := by omega
    let shifted : U64 := ⟨(1#u64).bv <<< bits.val⟩
    have hshl : (1#u64 <<< bits : Result U64) = .ok shifted := by
      simp [hShlU_uscalar_eq, hlt64, shifted]
    have hpow_le : 2 ^ bits.val ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hb
    have hpow_lt : 2 ^ bits.val < 2 ^ 64 := Nat.lt_of_le_of_lt hpow_le (by decide)
    have hsh_val : shifted.val = 2 ^ bits.val := by
      change ((1#u64).bv <<< bits.val).toNat = 2 ^ bits.val
      rw [BitVec.toNat_shiftLeft]
      change (1 <<< bits.val) % 2 ^ 64 = 2 ^ bits.val
      rw [Nat.one_shiftLeft, Nat.mod_eq_of_lt hpow_lt]
    have hge1 : (1#u64).val ≤ shifted.val := by
      rw [hsh_val]
      exact Nat.one_le_two_pow
    let mask : U64 := ⟨shifted.bv - (1#u64).bv⟩
    have hsub : (shifted - 1#u64 : Result U64) = .ok mask := by
      simp [hSub_uscalar_eq, hge1, mask]
    have hmask_bv : mask.bv = BitVec.ofNat 64 (2 ^ bits.val - 1) := by
      apply BitVec.eq_of_toNat_eq
      have hm : mask.bv.toNat = shifted.val - 1 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr hge1)
      rw [hm, hsh_val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [verify_stage_pow_mask, hng, ↓reduceIte, hshl, bind_eq_result_bind,
      result_bind_ok, hsub, lift_eq_ok]
    congr 1
    by_cases hw : word.bv &&& BitVec.ofNat 64 (2 ^ bits.val - 1) = 0
    · have heq : (word &&& mask) = 0#u64 := by
        rw [scalar_eq_bv, UScalar.bv_and, hmask_bv]
        exact hw
      simp [hb, hw, heq]
    · have hne : (word &&& mask) ≠ 0#u64 := by
        rw [Ne, scalar_eq_bv, UScalar.bv_and, hmask_bv]
        exact hw
      simp [hb, hw, hne]
  · have hg : bits > 32#u32 := by
      simp only [GT.gt, UScalar.lt_iff_val]
      change 32 < bits.val
      omega
    simp [verify_stage_pow_mask, hg, hb]

theorem verify_stage_pow_mask_sound (word : U64) (bits : U32) :
    verify_stage_pow_mask word bits = .ok true ↔
      bits.val ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ bits.val - 1) = 0 := by
  rw [verify_stage_pow_mask_spec]
  simp

theorem verify_stage_pow_mask_mod_sound (word : U64) (bits : U32) :
    verify_stage_pow_mask word bits = .ok true ↔
      bits.val ≤ 32 ∧ word.val % (2 ^ bits.val) = 0 := by
  rw [verify_stage_pow_mask_sound]
  constructor
  · rintro ⟨hb, hbv⟩
    refine ⟨hb, ?_⟩
    have hpow_le : 2 ^ bits.val ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hb
    have hlt : 2 ^ bits.val - 1 < 2 ^ 64 := by omega
    have hnat : (word.bv &&& BitVec.ofNat 64 (2 ^ bits.val - 1)).toNat = 0 :=
      congrArg BitVec.toNat hbv
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
      Nat.and_two_pow_sub_one_eq_mod] at hnat
    exact hnat
  · rintro ⟨hb, hmod⟩
    refine ⟨hb, ?_⟩
    apply BitVec.eq_of_toNat_eq
    have hpow_le : 2 ^ bits.val ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hb
    have hlt : 2 ^ bits.val - 1 < 2 ^ 64 := by omega
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
      Nat.and_two_pow_sub_one_eq_mod]
    exact hmod

/-! ## 5. Arbitrary-Slice OOD / Terminal Claim Equality (`verify_ood_pin_eq`) -/

private theorem list_drop_eq_cons {α : Type} (xs : List α) (k : Nat) (hk : k < xs.length) :
    xs.drop k = (xs[k]'hk) :: xs.drop (k + 1) := by
  induction xs generalizing k with
  | nil => cases hk
  | cons x rest ih =>
    cases k with
    | zero => rfl
    | succ k' =>
      have hk' : k' < rest.length := Nat.lt_of_succ_lt_succ hk
      exact ih k' hk'

private theorem verify_ood_pin_eq_loop_fuel
    (expected supplied : Slice U64)
    (hlen : expected.val.length = supplied.val.length)
    (rem : Nat) (i : Usize) (hi : i.val + rem = expected.val.length) :
    loopFuel (rem + 1)
      (fun i1 => verify_ood_pin_eq_loop.body expected supplied i1) i =
      .ok (decide (expected.val.drop i.val = supplied.val.drop i.val)) := by
  induction rem generalizing i with
  | zero =>
    have hi_eq : i.val = expected.val.length := by omega
    have hlt : ¬ (i < Slice.len expected) := by
      simp [UScalar.lt_iff_val, Slice.len_val, hi_eq]
    have hd1 : expected.val.drop i.val = [] := by
      rw [hi_eq, List.drop_length]
    have hd2 : supplied.val.drop i.val = [] := by
      rw [hi_eq, hlen, List.drop_length]
    simp [loopFuel_succ, verify_ood_pin_eq_loop.body, hlt, hd1, hd2]
  | succ rem' ih =>
    have hilt : i.val < expected.val.length := by omega
    have hslt : i.val < supplied.val.length := by omega
    have hlt_u : i < Slice.len expected := by
      simp [UScalar.lt_iff_val, Slice.len_val, hilt]
    have hidx_e : Slice.index_usize expected i = .ok (expected.val[i.val]'hilt) := by
      unfold Slice.index_usize; simp [hilt]
    have hidx_s : Slice.index_usize supplied i = .ok (supplied.val[i.val]'hslt) := by
      unfold Slice.index_usize; simp [hslt]
    have hdrop_e := list_drop_eq_cons expected.val i.val hilt
    have hdrop_s := list_drop_eq_cons supplied.val i.val hslt
    simp only [loopFuel_succ, verify_ood_pin_eq_loop.body, hlt_u, ↓reduceIte,
      hidx_e, hidx_s, bind_eq_result_bind, result_bind_ok]
    by_cases hne : (expected.val[i.val]'hilt) != (supplied.val[i.val]'hslt)
    · have hval_ne : (expected.val[i.val]'hilt) ≠ (supplied.val[i.val]'hslt) := by
        simpa [bne_iff_ne] using hne
      simp [hne, hdrop_e, hdrop_s, hval_ne]
    · have hval_eq : (expected.val[i.val]'hilt) = (supplied.val[i.val]'hslt) := by
        by_cases he : (expected.val[i.val]'hilt) = (supplied.val[i.val]'hslt)
        · exact he
        · exact False.elim (hne (bne_iff_ne.mpr he))
      have hadd_lt : i.val + (1#usize).val < 2 ^ 64 := by
        have hm := expected.property
        change i.val + 1 < 2 ^ 64
        unfold Usize.max at hm
        omega
      let i1 : Usize := ⟨i.bv + (1#usize).bv⟩
      have hadd : (i + 1#usize : Result Usize) = .ok i1 := by
        simp [hAdd_uscalar_eq, hadd_lt, i1]
      have hi1 : i1.val = i.val + 1 := by
        change (i.bv + (1#usize).bv).toNat = i.val + 1
        rw [BitVec.toNat_add, Nat.mod_eq_of_lt hadd_lt]
        rfl
      simp only [hne, ↓reduceIte, hadd, result_bind_ok]
      rw [ih i1 (by omega), hi1, hdrop_e, hdrop_s, hval_eq]
      simp

theorem verify_ood_pin_eq_spec (expected supplied : Slice U64) :
    verify_ood_pin_eq expected supplied = .ok (decide (expected.val = supplied.val)) := by
  unfold verify_ood_pin_eq
  by_cases hne : Slice.len expected != Slice.len supplied
  · have hlen_ne : expected.val.length ≠ supplied.val.length := by
      intro heq
      have hu : Slice.len expected = Slice.len supplied :=
        UScalar.eq_of_val_eq (by simp [Slice.len_val, heq])
      exact (bne_iff_ne.mp hne) hu
    have hlist_ne : expected.val ≠ supplied.val := fun h => hlen_ne (congrArg List.length h)
    simp [hne, hlist_ne]
  · have hlen_eq : expected.val.length = supplied.val.length := by
      by_cases he : Slice.len expected = Slice.len supplied
      · simpa [Slice.len_val] using congrArg UScalar.val he
      · exact False.elim (hne (bne_iff_ne.mpr he))
    simp only [hne, ↓reduceIte]
    unfold verify_ood_pin_eq_loop
    have hfuel : expected.val.length + 1 ≤ loopMaxFuel := by
      rw [← Slice.len_val expected]
      exact usize_lt_loopMaxFuel (Slice.len expected)
    have hloop := verify_ood_pin_eq_loop_fuel expected supplied hlen_eq
      expected.val.length 0#usize (by simp)
    simp only [List.drop] at hloop
    exact loop_ok_of_loopFuel hfuel hloop

theorem verify_ood_pin_eq_sound (expected supplied : Slice U64) :
    verify_ood_pin_eq expected supplied = .ok true ↔ expected.val = supplied.val := by
  rw [verify_ood_pin_eq_spec]
  simp

theorem verify_ood_pin_eq_false_iff (expected supplied : Slice U64) :
    verify_ood_pin_eq expected supplied = .ok false ↔ expected.val ≠ supplied.val := by
  rw [verify_ood_pin_eq_spec]
  simp

/-! ## 6. Canonical Query Group Reduction & Merkle Sibling Pair Ordering -/

theorem canonical_query_group_idx_spec (raw groups : U64) :
    canonical_query_group_idx raw groups =
      .ok (if groups.val = 0 then none else some (UScalar.ofNat .U64 (raw.val % groups.val))) := by
  unfold canonical_query_group_idx
  by_cases hg : groups = 0#u64
  · subst hg
    simp
  · have hnz : groups.val ≠ 0 := by
      intro hz
      exact hg (UScalar.eq_of_val_eq (by simpa using hz))
    have hmod : (raw % groups : Result U64) = .ok (UScalar.ofNat .U64 (raw.val % groups.val)) := by
      simp only [hMod_uscalar_eq, hnz, ↓reduceIte, Result.ok.injEq]
      apply UScalar.eq_of_val_eq
      have hlt : raw.val % groups.val < 2 ^ 64 :=
        Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero hnz)) groups.bv.isLt
      change (raw.bv % groups.bv).toNat = (BitVec.ofNat 64 (raw.val % groups.val)).toNat
      rw [BitVec.toNat_umod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    simp [hg, hnz, hmod, Result.bind]

theorem canonical_query_group_idx_some_iff (raw groups idx : U64) :
    canonical_query_group_idx raw groups = .ok (some idx) ↔
      0 < groups.val ∧ idx.val = raw.val % groups.val := by
  rw [canonical_query_group_idx_spec]
  by_cases hz : groups.val = 0
  · simp [hz]
  · have hpos : 0 < groups.val := Nat.pos_of_ne_zero hz
    have hlt : raw.val % groups.val < 2 ^ 64 := Nat.lt_trans (Nat.mod_lt _ hpos) groups.bv.isLt
    simp only [hz, ↓reduceIte, Result.ok.injEq, Option.some.injEq, hpos, true_and]
    constructor
    · intro h
      rw [← h, UScalar.val_ofNat]
      exact Nat.mod_eq_of_lt hlt
    · intro h
      apply UScalar.eq_of_val_eq
      rw [UScalar.val_ofNat, Nat.mod_eq_of_lt hlt]
      exact h.symm

theorem canonical_query_group_idx_none_iff (raw groups : U64) :
    canonical_query_group_idx raw groups = .ok none ↔ groups = 0#u64 := by
  rw [canonical_query_group_idx_spec]
  by_cases hz : groups.val = 0
  · refine ⟨fun _ => UScalar.eq_of_val_eq (by simpa using hz), fun _ => by simp [hz]⟩
  · simp [hz]
    intro h
    subst h
    exact hz rfl

theorem canonical_query_group_idx_lt_groups (raw groups idx : U64)
    (h : canonical_query_group_idx raw groups = .ok (some idx)) : idx.val < groups.val := by
  obtain ⟨hpos, hv⟩ := (canonical_query_group_idx_some_iff raw groups idx).mp h
  rw [hv]
  exact Nat.mod_lt _ hpos

theorem step_merkle_pair_order_spec
    (idx : U64) (level : U32) (node sibling : Array U8 32#usize) :
    step_merkle_pair_order idx level node sibling =
      .ok (if 64 ≤ level.val then none
           else if (idx.val >>> level.val) % 2 = 0
                then some { tag := 0#u8, left := node, right := sibling }
                else some { tag := 0#u8, left := sibling, right := node }) := by
  unfold step_merkle_pair_order
  by_cases hge : level >= 64#u32
  · have hge' : 64 ≤ level.val := by
      simpa only [ge_iff_le, UScalar.le_iff_val] using hge
    simp [hge, hge']
  · have hlt : level.val < 64 := by
      simp only [ge_iff_le, UScalar.le_iff_val] at hge
      change ¬ (64 ≤ level.val) at hge
      omega
    have hge' : ¬ (64 ≤ level.val) := by omega
    let shifted : U64 := ⟨idx.bv >>> level.val⟩
    have hshr : (idx >>> level : Result U64) = .ok shifted := by
      simp [hShrU_uscalar_eq, hlt, shifted]
    have hbit_val : (shifted &&& 1#u64).val = (idx.val >>> level.val) % 2 := by
      change ((idx.bv >>> level.val) &&& (1#u64).bv).toNat = (idx.val >>> level.val) % 2
      rw [BitVec.toNat_and, BitVec.toNat_ushiftRight]
      change (idx.val >>> level.val) &&& (2 ^ 1 - 1) = (idx.val >>> level.val) % 2
      exact Nat.and_two_pow_sub_one_eq_mod (idx.val >>> level.val) 1
    simp only [hge, ↓reduceIte, hshr, bind_eq_result_bind, result_bind_ok, lift_eq_ok,
      tag_canopy_merkle_internal_eq, hge']
    by_cases hb : (shifted &&& 1#u64) = 0#u64
    · have hm0 : (idx.val >>> level.val) % 2 = 0 := by
        rw [← hbit_val, hb]; rfl
      simp [hb, hm0]
    · have hmnz : (idx.val >>> level.val) % 2 ≠ 0 := by
        intro hz
        apply hb
        apply UScalar.eq_of_val_eq
        simpa [hbit_val] using hz
      simp [hb, hmnz]

theorem step_merkle_pair_order_some_iff
    (idx : U64) (level : U32) (node sibling : Array U8 32#usize) (pair : MerklePair) :
    step_merkle_pair_order idx level node sibling = .ok (some pair) ↔
      level.val < 64 ∧ pair.tag = 0#u8 ∧
      (if (idx.val >>> level.val) % 2 = 0
       then pair.left = node ∧ pair.right = sibling
       else pair.left = sibling ∧ pair.right = node) := by
  rw [step_merkle_pair_order_spec]
  by_cases hge : 64 ≤ level.val
  · simp [hge]; omega
  · have hlt : level.val < 64 := by omega
    by_cases hb : (idx.val >>> level.val) % 2 = 0
    · simp only [hge, ↓reduceIte, hb, Result.ok.injEq, Option.some.injEq, hlt, true_and]
      constructor
      · intro h; subst h; exact ⟨rfl, rfl, rfl⟩
      · rintro ⟨ht, hl, hr⟩; exact (MerklePair.ext ht hl hr).symm
    · simp only [hge, ↓reduceIte, hb, Result.ok.injEq, Option.some.injEq, hlt, true_and]
      constructor
      · intro h; subst h; exact ⟨rfl, rfl, rfl⟩
      · rintro ⟨ht, hl, hr⟩; exact (MerklePair.ext ht hl hr).symm

theorem step_merkle_pair_order_none_iff
    (idx : U64) (level : U32) (node sibling : Array U8 32#usize) :
    step_merkle_pair_order idx level node sibling = .ok none ↔ 64 ≤ level.val := by
  rw [step_merkle_pair_order_spec]
  by_cases hge : 64 ≤ level.val
  · simp [hge]
  · by_cases hb : (idx.val >>> level.val) % 2 = 0 <;> simp [hge, hb]

/-! ## 7. Overflow-Free Quorum Weight Summation (`checked_quorum_sum`) -/

@[expose] def natSumU64 (xs : List U64) : Nat :=
  xs.foldl (fun acc x => acc + x.val) 0

@[expose] def QuorumSumSpec
    (counts minimums : List U64) (minimum_global : U64) (sum : Nat) : Prop :=
  counts ≠ [] ∧
  counts.length = minimums.length ∧
  0 < minimum_global.val ∧
  (∀ j (hc : j < counts.length) (hm : j < minimums.length),
    0 < (minimums[j]'hm).val ∧ (minimums[j]'hm).val ≤ (counts[j]'hc).val) ∧
  sum = natSumU64 counts ∧
  sum ≤ 18446744073709551615 ∧
  minimum_global.val ≤ sum

private def quorumSuffixPure
    (cs ms : List U64) (minG : U64) (total minTotal : Nat) : Option U64 :=
  match cs, ms with
  | [], [] =>
    if total < minG.val then none else some (UScalar.ofNat .U64 total)
  | c :: cs', m :: ms' =>
    if m.val = 0 then none
    else if c.val < m.val then none
    else if total + c.val > 18446744073709551615 then none
    else if minTotal + m.val > 18446744073709551615 then none
    else quorumSuffixPure cs' ms' minG (total + c.val) (minTotal + m.val)
  | _, _ => none

private theorem checked_quorum_sum_loop_fuel
    (counts minimums : Slice U64) (minG : U64)
    (hlen : counts.val.length = minimums.val.length)
    (rem : Nat) (total min_total : U64) (i : Usize)
    (hi : i.val + rem = counts.val.length) :
    loopFuel (rem + 1)
      (fun (t1, mt1, i1) => checked_quorum_sum_loop.body counts minimums minG t1 mt1 i1)
      (total, min_total, i) =
      .ok (quorumSuffixPure (counts.val.drop i.val) (minimums.val.drop i.val)
            minG total.val min_total.val) := by
  induction rem generalizing total min_total i with
  | zero =>
    have hi_eq : i.val = counts.val.length := by omega
    have hlt : ¬ (i < Slice.len counts) := by
      simp [UScalar.lt_iff_val, Slice.len_val, hi_eq]
    have hdc : counts.val.drop i.val = [] := by rw [hi_eq, List.drop_length]
    have hdm : minimums.val.drop i.val = [] := by rw [hi_eq, hlen, List.drop_length]
    simp only [loopFuel_succ, checked_quorum_sum_loop.body, hlt, ↓reduceIte,
      hdc, hdm, quorumSuffixPure]
    by_cases hmin : total < minG
    · have hmin' : total.val < minG.val := by simpa [UScalar.lt_iff_val] using hmin
      simp [hmin, hmin']
    · have hmin' : ¬ (total.val < minG.val) := by simpa [UScalar.lt_iff_val] using hmin
      have htot : UScalar.ofNat .U64 total.val = total := by
        apply UScalar.eq_of_val_eq
        rw [UScalar.val_ofNat, Nat.mod_eq_of_lt total.bv.isLt]
      simp [hmin, hmin', htot]
  | succ rem' ih =>
    have hilt_c : i.val < counts.val.length := by omega
    have hilt_m : i.val < minimums.val.length := by omega
    have hlt_u : i < Slice.len counts := by
      simp [UScalar.lt_iff_val, Slice.len_val, hilt_c]
    let c := counts.val[i.val]'hilt_c
    let m := minimums.val[i.val]'hilt_m
    have hidx_c : Slice.index_usize counts i = .ok c := by
      unfold Slice.index_usize; simp [hilt_c, c]
    have hidx_m : Slice.index_usize minimums i = .ok m := by
      unfold Slice.index_usize; simp [hilt_m, m]
    have hdc := list_drop_eq_cons counts.val i.val hilt_c
    have hdm := list_drop_eq_cons minimums.val i.val hilt_m
    rw [hdc, hdm]
    simp only [loopFuel_succ, checked_quorum_sum_loop.body, hlt_u, ↓reduceIte,
      hidx_c, hidx_m, bind_eq_result_bind, result_bind_ok, quorumSuffixPure]
    by_cases hm0 : m = 0#u64
    · have hm0' : m.val = 0 := by rw [hm0]; rfl
      simp [hm0, hm0']
    · have hm0' : m.val ≠ 0 := fun hz => hm0 (UScalar.eq_of_val_eq (by simpa using hz))
      by_cases hcm : c < m
      · have hcm' : c.val < m.val := by simpa [UScalar.lt_iff_val] using hcm
        simp [hm0, hm0', hcm, hcm']
      · have hcm' : ¬ (c.val < m.val) := by simpa [UScalar.lt_iff_val] using hcm
        have hc_le_max : c.val ≤ MAX_U64_WORD.val := by
          rw [max_u64_word_val]
          have hc64 : c.val < 2 ^ 64 := c.bv.isLt
          omega
        let cap_c : U64 := ⟨MAX_U64_WORD.bv - c.bv⟩
        have hsub_c : (MAX_U64_WORD - c : Result U64) = .ok cap_c := by
          simp [hSub_uscalar_eq, hc_le_max, cap_c]
        have hcap_c_val : cap_c.val = 18446744073709551615 - c.val := by
          have hv := BitVec.toNat_sub_of_le (BitVec.le_def.mpr hc_le_max)
          simpa [cap_c, max_u64_word_val] using hv
        simp only [hm0, hm0', hcm, hcm', ↓reduceIte, hsub_c, result_bind_ok]
        by_cases htc : total > cap_c
        · have htc' : total.val + c.val > 18446744073709551615 := by
            have hv : cap_c.val < total.val := by simpa [GT.gt, UScalar.lt_iff_val] using htc
            omega
          simp [htc, htc']
        · have htc' : ¬ (total.val + c.val > 18446744073709551615) := by
            have hv : ¬ (cap_c.val < total.val) := by simpa [GT.gt, UScalar.lt_iff_val] using htc
            omega
          have htc_lt : total.val + c.val < 2 ^ 64 := by omega
          let total1 : U64 := ⟨total.bv + c.bv⟩
          have hadd_t : (total + c : Result U64) = .ok total1 := by
            simp [hAdd_uscalar_eq, htc_lt, total1]
          have htot1_val : total1.val = total.val + c.val := by
            change (total.bv + c.bv).toNat = total.val + c.val
            rw [BitVec.toNat_add, Nat.mod_eq_of_lt htc_lt]
          have hm_le_max : m.val ≤ MAX_U64_WORD.val := by
            rw [max_u64_word_val]
            have hm64 : m.val < 2 ^ 64 := m.bv.isLt
            omega
          let cap_m : U64 := ⟨MAX_U64_WORD.bv - m.bv⟩
          have hsub_m : (MAX_U64_WORD - m : Result U64) = .ok cap_m := by
            simp [hSub_uscalar_eq, hm_le_max, cap_m]
          have hcap_m_val : cap_m.val = 18446744073709551615 - m.val := by
            have hv := BitVec.toNat_sub_of_le (BitVec.le_def.mpr hm_le_max)
            simpa [cap_m, max_u64_word_val] using hv
          simp only [htc, htc', ↓reduceIte, hadd_t, result_bind_ok, hsub_m]
          by_cases htm : min_total > cap_m
          · have htm' : min_total.val + m.val > 18446744073709551615 := by
              have hv : cap_m.val < min_total.val := by simpa [GT.gt, UScalar.lt_iff_val] using htm
              omega
            simp [htm, htm']
          · have htm' : ¬ (min_total.val + m.val > 18446744073709551615) := by
              have hv : ¬ (cap_m.val < min_total.val) := by simpa [GT.gt, UScalar.lt_iff_val] using htm
              omega
            have htm_lt : min_total.val + m.val < 2 ^ 64 := by omega
            let min_total1 : U64 := ⟨min_total.bv + m.bv⟩
            have hadd_m : (min_total + m : Result U64) = .ok min_total1 := by
              simp [hAdd_uscalar_eq, htm_lt, min_total1]
            have hmt1_val : min_total1.val = min_total.val + m.val := by
              change (min_total.bv + m.bv).toNat = min_total.val + m.val
              rw [BitVec.toNat_add, Nat.mod_eq_of_lt htm_lt]
            have hi_lt : i.val + (1#usize).val < 2 ^ 64 := by
              have hm_c := counts.property
              change i.val + 1 < 2 ^ 64
              unfold Usize.max at hm_c
              omega
            let i1 : Usize := ⟨i.bv + (1#usize).bv⟩
            have hadd_i : (i + 1#usize : Result Usize) = .ok i1 := by
              simp [hAdd_uscalar_eq, hi_lt, i1]
            have hi1_val : i1.val = i.val + 1 := by
              change (i.bv + (1#usize).bv).toNat = i.val + 1
              rw [BitVec.toNat_add, Nat.mod_eq_of_lt hi_lt]
              rfl
            simp only [htm, htm', ↓reduceIte, hadd_m, hadd_i, result_bind_ok]
            rw [ih total1 min_total1 i1 (by omega), hi1_val, htot1_val, hmt1_val]

private theorem foldl_u64_ge (xs : List U64) (acc : Nat) :
    acc ≤ xs.foldl (fun a x => a + x.val) acc := by
  induction xs generalizing acc with
  | nil => exact Nat.le_refl _
  | cons x rest ih => exact Nat.le_trans (by omega) (ih (acc + x.val))

private theorem foldl_u64_shift (xs : List U64) (acc : Nat) :
    xs.foldl (fun a x => a + x.val) acc = acc + natSumU64 xs := by
  induction xs generalizing acc with
  | nil => simp [natSumU64]
  | cons x rest ih =>
    simp only [List.foldl, natSumU64]
    rw [ih (acc + x.val), ih x.val]
    omega

private theorem quorumSuffixPure_some_iff
    (cs ms : List U64) (minG : U64) (total minTotal : Nat) (out : U64)
    (hlen : cs.length = ms.length)
    (hle : minTotal ≤ total)
    (htot_max : total ≤ 18446744073709551615) :
    quorumSuffixPure cs ms minG total minTotal = some out ↔
      (∀ j (hc : j < cs.length) (hm : j < ms.length),
        0 < (ms[j]'hm).val ∧ (ms[j]'hm).val ≤ (cs[j]'hc).val) ∧
      out.val = total + natSumU64 cs ∧
      total + natSumU64 cs ≤ 18446744073709551615 ∧
      minG.val ≤ total + natSumU64 cs := by
  induction cs generalizing ms total minTotal with
  | nil =>
    cases ms with
    | cons _ _ => cases hlen
    | nil =>
      simp only [quorumSuffixPure, natSumU64, List.foldl, Nat.add_zero]
      constructor
      · intro h
        by_cases hlt : total < minG.val
        · simp [hlt] at h
        · simp [hlt] at h
          have hout : out.val = total := by
            rw [← h, UScalar.val_ofNat, Nat.mod_eq_of_lt (by omega)]
          exact ⟨fun j hc => False.elim (Nat.not_lt_zero j hc), hout, htot_max, by omega⟩
      · rintro ⟨_, hout, _, hmin⟩
        have hlt : ¬ (total < minG.val) := by omega
        simp only [hlt, ↓reduceIte, Option.some.injEq]
        apply UScalar.eq_of_val_eq
        rw [UScalar.val_ofNat, Nat.mod_eq_of_lt (by omega), hout]
  | cons c cs' ih =>
    cases ms with
    | nil => cases hlen
    | cons m ms' =>
      have hlen' : cs'.length = ms'.length := Nat.succ.inj hlen
      have hsum_cons : total + natSumU64 (c :: cs') = (total + c.val) + natSumU64 cs' := by
        simp only [natSumU64, List.foldl, Nat.zero_add]
        rw [foldl_u64_shift cs' c.val]
        omega
      simp only [quorumSuffixPure]
      constructor
      · intro h
        by_cases hm0 : m.val = 0
        · simp [hm0] at h
        · by_cases hcm : c.val < m.val
          · simp [hm0, hcm] at h
          · by_cases htc : total + c.val > 18446744073709551615
            · simp [hm0, hcm, htc] at h
            · by_cases htm : minTotal + m.val > 18446744073709551615
              · simp [hm0, hcm, htc, htm] at h
              · simp only [hm0, hcm, htc, htm, ↓reduceIte] at h
                obtain ⟨hrec_all, hout, hmax, hmin⟩ :=
                  ih ms' (total + c.val) (minTotal + m.val) hlen' (by omega) (by omega) |>.mp h
                refine ⟨?_, ?_, ?_, ?_⟩
                · intro j hc hm
                  cases j with
                  | zero => exact ⟨Nat.pos_of_ne_zero hm0, by omega⟩
                  | succ j' =>
                    exact hrec_all j' (Nat.lt_of_succ_lt_succ hc) (Nat.lt_of_succ_lt_succ hm)
                · rw [hsum_cons]; exact hout
                · rw [hsum_cons]; exact hmax
                · rw [hsum_cons]; exact hmin
      · rintro ⟨hall, hout, hmax, hmin⟩
        have h0 := hall 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
        have hm0 : m.val ≠ 0 := by omega
        have hcm : ¬ (c.val < m.val) := by omega
        have hcs_nonneg : 0 ≤ natSumU64 cs' := Nat.zero_le _
        have htc_le : total + c.val ≤ 18446744073709551615 := by omega
        have htc : ¬ (total + c.val > 18446744073709551615) := by omega
        have htm : ¬ (minTotal + m.val > 18446744073709551615) := by omega
        simp only [hm0, hcm, htc, htm, ↓reduceIte]
        apply (ih ms' (total + c.val) (minTotal + m.val) hlen' (by omega) htc_le).mpr
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro j' hc' hm'
          exact hall (j' + 1) (Nat.succ_lt_succ hc') (Nat.succ_lt_succ hm')
        · rw [← hsum_cons]; exact hout
        · rw [← hsum_cons]; exact hmax
        · rw [← hsum_cons]; exact hmin

/-- `checked_quorum_sum` is total: it never panics, overflows, or diverges on any slice inputs. -/
theorem checked_quorum_sum_total
    (counts minimums : Slice U64) (minimum_global : U64) :
    ∃ out : Option U64, checked_quorum_sum counts minimums minimum_global = .ok out := by
  unfold checked_quorum_sum core.slice.Slice.is_empty
  simp only [bind_eq_result_bind, result_bind_ok]
  by_cases hemp : counts.val.isEmpty
  · exact ⟨none, by simp [hemp]⟩
  · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
    by_cases hne : Slice.len counts != Slice.len minimums
    · exact ⟨none, by simp [hne]⟩
    · have hlen : counts.val.length = minimums.val.length := by
        by_cases he : Slice.len counts = Slice.len minimums
        · simpa [Slice.len_val] using congrArg UScalar.val he
        · exact False.elim (hne (bne_iff_ne.mpr he))
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      by_cases hg0 : minimum_global = 0#u64
      · exact ⟨none, by simp [hg0]⟩
      · simp only [hg0, ↓reduceIte]
        unfold checked_quorum_sum_loop
        have hfuel : counts.val.length + 1 ≤ loopMaxFuel := by
          rw [← Slice.len_val counts]
          exact usize_lt_loopMaxFuel (Slice.len counts)
        have hloop := checked_quorum_sum_loop_fuel counts minimums minimum_global hlen
          counts.val.length 0#u64 0#u64 0#usize (by simp)
        exact ⟨_, loop_ok_of_loopFuel hfuel hloop⟩

/-- Exact bidirectional soundness & completeness of `checked_quorum_sum`. -/
theorem checked_quorum_sum_sound
    (counts minimums : Slice U64) (minimum_global total : U64) :
    checked_quorum_sum counts minimums minimum_global = .ok (some total) ↔
      QuorumSumSpec counts.val minimums.val minimum_global total.val := by
  unfold checked_quorum_sum core.slice.Slice.is_empty
  simp only [bind_eq_result_bind, result_bind_ok]
  by_cases hemp : counts.val.isEmpty
  · have hnil : counts.val = [] := List.isEmpty_iff.mp hemp
    simp [hemp, hnil, QuorumSumSpec]
  · have hne_nil : counts.val ≠ [] := fun h => hemp (List.isEmpty_iff.mpr h)
    simp only [hemp, Bool.false_eq_true, ↓reduceIte]
    by_cases hne : Slice.len counts != Slice.len minimums
    · have hlen_ne : counts.val.length ≠ minimums.val.length := by
        intro heq
        have hu : Slice.len counts = Slice.len minimums :=
          UScalar.eq_of_val_eq (by simp [Slice.len_val, heq])
        exact (bne_iff_ne.mp hne) hu
      simp [hne, QuorumSumSpec, hlen_ne]
    · have hlen : counts.val.length = minimums.val.length := by
        by_cases he : Slice.len counts = Slice.len minimums
        · simpa [Slice.len_val] using congrArg UScalar.val he
        · exact False.elim (hne (bne_iff_ne.mpr he))
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      by_cases hg0 : minimum_global = 0#u64
      · have hg0_val : minimum_global.val = 0 := by rw [hg0]; rfl
        simp [hg0, QuorumSumSpec, hg0_val]
      · have hg_pos : 0 < minimum_global.val := by
          have hnz : minimum_global.val ≠ 0 := fun hz =>
            hg0 (UScalar.eq_of_val_eq (by simpa using hz))
          exact Nat.pos_of_ne_zero hnz
        simp only [hg0, ↓reduceIte]
        unfold checked_quorum_sum_loop
        have hfuel : counts.val.length + 1 ≤ loopMaxFuel := by
          rw [← Slice.len_val counts]
          exact usize_lt_loopMaxFuel (Slice.len counts)
        have hloop := checked_quorum_sum_loop_fuel counts minimums minimum_global hlen
          counts.val.length 0#u64 0#u64 0#usize (by simp)
        have hrun := loop_ok_of_loopFuel hfuel hloop
        simp only [List.drop] at hrun
        rw [hrun]
        simp only [Result.ok.injEq]
        rw [quorumSuffixPure_some_iff counts.val minimums.val minimum_global 0 0 total
          hlen (Nat.le_refl 0) (by decide)]
        simp only [Nat.zero_add, QuorumSumSpec, hne_nil, hlen, hg_pos, true_and]

theorem checked_quorum_sum_none_iff
    (counts minimums : Slice U64) (minimum_global : U64) :
    checked_quorum_sum counts minimums minimum_global = .ok none ↔
      ¬ ∃ s : Nat, QuorumSumSpec counts.val minimums.val minimum_global s := by
  obtain ⟨out, hout⟩ := checked_quorum_sum_total counts minimums minimum_global
  cases out with
  | none =>
    simp only [hout, true_iff]
    rintro ⟨s, hs⟩
    have hlt64 : s < 2 ^ 64 := by
      have hm := hs.2.2.2.2.2.1
      omega
    let u : U64 := UScalar.ofNat .U64 s
    have hu : u.val = s := by
      rw [UScalar.val_ofNat, Nat.mod_eq_of_lt hlt64]
    have hspec : QuorumSumSpec counts.val minimums.val minimum_global u.val := by
      simpa only [hu] using hs
    have hsome := (checked_quorum_sum_sound counts minimums minimum_global u).mpr hspec
    rw [hout] at hsome
    cases hsome
  | some v =>
    simp only [hout, Result.ok.injEq, reduceCtorEq, false_iff]
    have hv := (checked_quorum_sum_sound counts minimums minimum_global v).mp hout
    intro hnot
    exact hnot ⟨v.val, hv⟩

/-! ## 8. `#tooth` Mutation-Sensitivity & Non-Vacuity Witnesses -/

/-- `#tooth`: Unchecked `% p` aliases `0` and `p`, whereas `decode_canonical_u64` rejects `p`. -/
theorem tooth_unchecked_mod_p_accepts_aliased_field_limb :
    (0#u64) ≠ GOLDILOCKS_P ∧
    (0#u64 % GOLDILOCKS_P : Result U64) = .ok 0#u64 ∧
    (GOLDILOCKS_P % GOLDILOCKS_P : Result U64) = .ok 0#u64 ∧
    decode_canonical_u64 GOLDILOCKS_P = .ok none := by
  simp only [decode_canonical_u64, GOLDILOCKS_P]
  decide

/-- `#tooth`: `decode_canonical_ext4` rejects a non-canonical 4th limb even when limbs 0..2 are canonical,
    and accepts canonical limbs. -/
theorem tooth_decode_canonical_ext4_rejects_fourth_limb_alias :
    decode_canonical_ext4 1#u64 2#u64 3#u64 GOLDILOCKS_P = .ok none ∧
    decode_canonical_ext4 1#u64 2#u64 3#u64 4#u64 = .ok (some ⟨1#u64, 2#u64, 3#u64, 4#u64⟩) := by
  simp only [decode_canonical_ext4_none_iff, decode_canonical_ext4_some_iff,
    IsCanonical, goldilocks_p_val]
  decide

/-- `#tooth`: `verify_stage_pow_mask` rejects `pow_bits > 32`, rejects non-zero low bits, and accepts
    divisible nonces. -/
theorem tooth_pow_rejects_excessive_bits_and_nonzero_low_bits :
    verify_stage_pow_mask 0#u64 33#u32 = .ok false ∧
    verify_stage_pow_mask 8#u64 4#u32 = .ok false ∧
    verify_stage_pow_mask 16#u64 4#u32 = .ok true := by
  simp only [verify_stage_pow_mask_spec]
  decide

/-- `#tooth`: `step_merkle_pair_order` swaps `(node, sibling)` on the direction bit, pins `tag = 0#u8`,
    and rejects out-of-range shift `level = 64`. -/
theorem tooth_merkle_pair_swaps_on_direction_bit_and_rejects_shift64 :
    let z := Array.repeat 32#usize 0x11#u8
    let w := Array.repeat 32#usize 0x22#u8
    z ≠ w ∧
    step_merkle_pair_order 0#u64 0#u32 z w = .ok (some ⟨0#u8, z, w⟩) ∧
    step_merkle_pair_order 1#u64 0#u32 z w = .ok (some ⟨0#u8, w, z⟩) ∧
    step_merkle_pair_order 0#u64 64#u32 z w = .ok none := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hv := congrArg Array.val h
    simp [Array.repeat] at hv
  · rw [step_merkle_pair_order_spec]; rfl
  · rw [step_merkle_pair_order_spec]; rfl
  · rw [step_merkle_pair_order_spec]; rfl

/-- `#tooth`: `checked_quorum_sum` rejects `u64` wraparound forgery (`u64::MAX + 5`) while accepting
    valid multi-shard quorum sums. -/
theorem tooth_checked_quorum_sum_rejects_u64_wraparound_forgery :
    let overflow_counts : Slice U64 := ⟨[MAX_U64_WORD, 5#u64], by decide⟩
    let overflow_mins : Slice U64 := ⟨[1#u64, 1#u64], by decide⟩
    let honest_counts : Slice U64 := ⟨[10#u64, 15#u64], by decide⟩
    let honest_mins : Slice U64 := ⟨[8#u64, 12#u64], by decide⟩
    checked_quorum_sum overflow_counts overflow_mins 4#u64 = .ok none ∧
    checked_quorum_sum honest_counts honest_mins 20#u64 = .ok (some 25#u64) := by
  constructor
  · rw [checked_quorum_sum_none_iff]
    rintro ⟨s, _, _, _, _, hsum, hmax, _⟩
    simp [natSumU64, max_u64_word_val] at hsum
    omega
  · rw [checked_quorum_sum_sound]
    refine ⟨by decide, rfl, by decide, ?_, by rfl, by decide, by decide⟩
    intro j hc hm
    match j with
    | 0 => decide
    | 1 => decide
    | n + 2 => exfalso; revert hc; decide

/-- `#tooth`: `verify_ood_pin_eq` rejects single-limb perturbations and length mismatches while accepting
    exact slice matches. -/
theorem tooth_ood_pin_rejects_perturbation_and_length_mismatch :
    let s1 : Slice U64 := ⟨[1#u64, 2#u64, 3#u64, 4#u64], by decide⟩
    let s2 : Slice U64 := ⟨[1#u64, 2#u64, 3#u64, 5#u64], by decide⟩
    let s3 : Slice U64 := ⟨[1#u64, 2#u64, 3#u64], by decide⟩
    verify_ood_pin_eq s1 s2 = .ok false ∧
    verify_ood_pin_eq s1 s3 = .ok false ∧
    verify_ood_pin_eq s1 s1 = .ok true := by
  simp only [verify_ood_pin_eq_spec]
  decide

end qsag_whir_verified.proofs

module
public import QsagWhirVerified.Arithmetic
import all Aeneas
import all Aeneas.Std.Types
public section
open Aeneas Aeneas.Std
namespace qsag_whir_verified.proofs
attribute [local simp] UScalar.val UScalarTy.numBits
set_option linter.unusedSimpArgs false

 theorem decode_canonical_u64_rejects_noncanonical (x : U64)
    (h : GOLDILOCKS_P.val ≤ x.val) : decode_canonical_u64 x = .ok none := by
  simp [decode_canonical_u64, UScalar.lt_iff_val, Nat.not_lt.mpr h]

 theorem ext_eq_sound (x y : Ext4) : ext_eq x y = .ok true ↔ x = y := by
  cases x; cases y
  simp only [ext_eq]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- Exact MIR expression: checked evaluation of odd + alpha * even. -/
 theorem verify_affine_duet_fold_step_sound (v0 v1 : Ext4) (iy it : U64)
    (alpha claimed : Ext4) :
    verify_affine_duet_fold_step v0 v1 iy it alpha claimed = .ok true ↔
      claimed = duetValue v0 v1 iy it alpha := by
  unfold verify_affine_duet_fold_step
  rw [duet_refines]
  simp [Result.bind, ext_eq_sound, eq_comm]

 theorem canonical_query_group_idx_lt_groups (raw groups idx : U64)
    (h : canonical_query_group_idx raw groups = .ok (some idx)) : idx.val < groups.val := by
  unfold canonical_query_group_idx at h
  split at h
  · cases h
  · rename_i hn
    have hz : groups.val ≠ 0 := by
      intro hz
      apply hn
      apply UScalar.eq_of_val_eq
      simpa using hz
    simp [hMod_uscalar_eq, hz, Result.bind] at h
    subst idx
    exact Nat.mod_lt _ (Nat.pos_of_ne_zero hz)

/-- Low-bit acceptance, including rejection of unsupported work factors. -/
 theorem verify_stage_pow_mask_checked_steps (word : U64) (bits : U32) :
    verify_stage_pow_mask word bits = .ok true ↔
    bits.val ≤ 32 ∧ ∃ shifted mask : U64,
      (1#u64 <<< bits : Result U64) = .ok shifted ∧
      (shifted - 1#u64 : Result U64) = .ok mask ∧
      word.bv &&& mask.bv = 0 := by
  have hz : (32#u32).val = 32 := rfl
  by_cases hb : bits > 32#u32
  · have hb' : 32 < bits.val := by simpa only [UScalar.lt_iff_val, hz] using hb
    simp only [verify_stage_pow_mask, hb, ↓reduceIte]
    simp [show ¬ bits.val ≤ 32 by omega]
  · have hb' : bits.val ≤ 32 := by
      simp only [GT.gt, UScalar.lt_iff_val, hz] at hb
      omega
    simp only [verify_stage_pow_mask, hb, ↓reduceIte]
    cases hs : (1#u64 <<< bits : Result U64) with
    | fail e =>
      simp only [bind_eq_result_bind, Result.bind]
      constructor
      · intro h; cases h
      · rintro ⟨_, shifted, mask, h, _, _⟩; cases h
    | div =>
      simp only [bind_eq_result_bind, Result.bind]
      constructor
      · intro h; cases h
      · rintro ⟨_, shifted, mask, h, _, _⟩; cases h
    | ok shifted =>
      simp only [bind_eq_result_bind, Result.bind]
      cases hm : (shifted - 1#u64 : Result U64) with
      | fail e =>
        simp only [bind_eq_result_bind, Result.bind]
        constructor
        · intro h; cases h
        · rintro ⟨_, s, m, h, hm', _⟩
          cases h
          rw [hm] at hm'
          cases hm'
      | div =>
        simp only [bind_eq_result_bind, Result.bind]
        constructor
        · intro h; cases h
        · rintro ⟨_, s, m, h, hm', _⟩
          cases h
          rw [hm] at hm'
          cases hm'
      | ok mask =>
        simp only [bind_eq_result_bind, Result.bind, lift_eq_ok, result_bind_ok]
        constructor
        · intro h
          have he : word &&& mask = 0#u64 := by simpa only [Result.ok.injEq, decide_eq_true_eq] using h
          exact ⟨hb', shifted, mask, rfl, hm, congrArg UScalar.bv he⟩
        · rintro ⟨_, s, m, h, hm', he⟩
          cases h
          rw [hm] at hm'
          cases hm'
          have he' : word &&& mask = 0#u64 := UScalar.ext he
          simpa only [Result.ok.injEq, decide_eq_true_eq] using he'

private theorem scalar_eq_bv (a b : U64) : a = b ↔ a.bv = b.bv :=
  ⟨congrArg UScalar.bv, UScalar.ext⟩

/-- Mathematical low-mask specification, with no assumed successful intermediate operations. -/
theorem verify_stage_pow_mask_sound (word : U64) (bits : U32) :
    verify_stage_pow_mask word bits = .ok true ↔
      bits.val ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ bits.val - 1) = 0 := by
  by_cases hb : bits.val ≤ 32
  · have hc : bits.val = 0 ∨ bits.val = 1 ∨ bits.val = 2 ∨ bits.val = 3 ∨ bits.val = 4 ∨ bits.val = 5 ∨ bits.val = 6 ∨ bits.val = 7 ∨ bits.val = 8 ∨ bits.val = 9 ∨ bits.val = 10 ∨ bits.val = 11 ∨ bits.val = 12 ∨ bits.val = 13 ∨ bits.val = 14 ∨ bits.val = 15 ∨ bits.val = 16 ∨ bits.val = 17 ∨ bits.val = 18 ∨ bits.val = 19 ∨ bits.val = 20 ∨ bits.val = 21 ∨ bits.val = 22 ∨ bits.val = 23 ∨ bits.val = 24 ∨ bits.val = 25 ∨ bits.val = 26 ∨ bits.val = 27 ∨ bits.val = 28 ∨ bits.val = 29 ∨ bits.val = 30 ∨ bits.val = 31 ∨ bits.val = 32 := by omega
    rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32
    · have he : bits = 0#u32 := UScalar.eq_of_val_eq (by simpa using h0)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 0 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        0 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 0 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 1#u32 := UScalar.eq_of_val_eq (by simpa using h1)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 1 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        1 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 1 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 2#u32 := UScalar.eq_of_val_eq (by simpa using h2)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 2 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        2 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 2 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 3#u32 := UScalar.eq_of_val_eq (by simpa using h3)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 3 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        3 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 3 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 4#u32 := UScalar.eq_of_val_eq (by simpa using h4)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 4 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        4 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 4 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 5#u32 := UScalar.eq_of_val_eq (by simpa using h5)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 5 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        5 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 5 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 6#u32 := UScalar.eq_of_val_eq (by simpa using h6)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 6 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        6 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 6 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 7#u32 := UScalar.eq_of_val_eq (by simpa using h7)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 7 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        7 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 7 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 8#u32 := UScalar.eq_of_val_eq (by simpa using h8)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 8 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        8 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 8 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 9#u32 := UScalar.eq_of_val_eq (by simpa using h9)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 9 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        9 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 9 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 10#u32 := UScalar.eq_of_val_eq (by simpa using h10)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 10 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        10 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 10 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 11#u32 := UScalar.eq_of_val_eq (by simpa using h11)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 11 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        11 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 11 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 12#u32 := UScalar.eq_of_val_eq (by simpa using h12)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 12 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        12 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 12 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 13#u32 := UScalar.eq_of_val_eq (by simpa using h13)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 13 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        13 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 13 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 14#u32 := UScalar.eq_of_val_eq (by simpa using h14)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 14 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        14 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 14 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 15#u32 := UScalar.eq_of_val_eq (by simpa using h15)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 15 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        15 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 15 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 16#u32 := UScalar.eq_of_val_eq (by simpa using h16)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 16 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        16 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 16 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 17#u32 := UScalar.eq_of_val_eq (by simpa using h17)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 17 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        17 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 17 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 18#u32 := UScalar.eq_of_val_eq (by simpa using h18)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 18 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        18 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 18 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 19#u32 := UScalar.eq_of_val_eq (by simpa using h19)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 19 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        19 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 19 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 20#u32 := UScalar.eq_of_val_eq (by simpa using h20)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 20 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        20 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 20 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 21#u32 := UScalar.eq_of_val_eq (by simpa using h21)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 21 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        21 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 21 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 22#u32 := UScalar.eq_of_val_eq (by simpa using h22)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 22 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        22 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 22 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 23#u32 := UScalar.eq_of_val_eq (by simpa using h23)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 23 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        23 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 23 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 24#u32 := UScalar.eq_of_val_eq (by simpa using h24)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 24 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        24 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 24 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 25#u32 := UScalar.eq_of_val_eq (by simpa using h25)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 25 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        25 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 25 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 26#u32 := UScalar.eq_of_val_eq (by simpa using h26)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 26 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        26 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 26 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 27#u32 := UScalar.eq_of_val_eq (by simpa using h27)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 27 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        27 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 27 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 28#u32 := UScalar.eq_of_val_eq (by simpa using h28)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 28 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        28 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 28 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 29#u32 := UScalar.eq_of_val_eq (by simpa using h29)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 29 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        29 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 29 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 30#u32 := UScalar.eq_of_val_eq (by simpa using h30)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 30 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        30 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 30 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 31#u32 := UScalar.eq_of_val_eq (by simpa using h31)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 31 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        31 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 31 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
    · have he : bits = 32#u32 := UScalar.eq_of_val_eq (by simpa using h32)
      subst bits
      change (Result.ok (decide ((⟨word.bv &&& BitVec.ofNat 64 (2 ^ 32 - 1)⟩ : U64) = 0#u64)) = Result.ok true) ↔
        32 ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ 32 - 1) = 0
      simp only [Result.ok.injEq, decide_eq_true_eq, scalar_eq_bv]
      simp
  · have hg : bits > 32#u32 := by
      simp only [GT.gt, UScalar.lt_iff_val]
      change 32 < bits.val
      omega
    simp only [verify_stage_pow_mask, hg, ↓reduceIte]
    simp [hb]

/-- #tooth: modular decoding identifies two distinct wire limbs. -/
 theorem tooth_unchecked_mod_p_accepts_aliased_field_limb :
    (0#u64) ≠ GOLDILOCKS_P ∧
    (0#u64 % GOLDILOCKS_P : Result U64) = .ok 0#u64 ∧
    (GOLDILOCKS_P % GOLDILOCKS_P : Result U64) = .ok 0#u64 ∧
    decode_canonical_u64 GOLDILOCKS_P = .ok none := by
  simp only [decode_canonical_u64, GOLDILOCKS_P]
  decide
end qsag_whir_verified.proofs

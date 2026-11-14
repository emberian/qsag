module

public import QsagVerified.Proofs.Common

public section

namespace qsag_verified.proofs

open Aeneas Aeneas.Std Result ControlFlow Error
open qsag_verified

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

attribute [-simp] BitVec.getLsbD_eq_getElem
attribute [local simp] UScalar.val UScalarTy.numBits

/-! ## WOTS chain boundary behavior -/

theorem fips205_wots_chain_oob_none
    (x pk_seed : Array Std.U8 16#usize) (base_adrs : fips205.Fips205Adrs)
    (start_i steps_s : Std.U32)
    (h : start_i.val > 15 ∨ start_i.val + steps_s.val > 15) :
    fips205.fips205_wots_chain x start_i steps_s pk_seed base_adrs = .ok none := by
  unfold fips205.fips205_wots_chain
  by_cases hs : start_i > 15#u32
  · simp [hs]
  · have hb : start_i.val ≤ 15 := by
      have hn : ¬ 15 < start_i.val := fun h => hs ((UScalar.lt_iff_val _ _).mpr h)
      exact Nat.le_of_not_gt hn
    let rem : Std.U32 := ⟨(15#u32).bv - start_i.bv⟩
    have hsub : (15#u32 - start_i : Result Std.U32) = .ok rem := by
      simp [hSub_uscalar_eq, rem, hb]
    have hv : rem.val = 15 - start_i.val :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr hb)
    have hgt : steps_s > rem := (UScalar.lt_iff_val _ _).mpr (by
      change rem.val < steps_s.val
      rw [hv]
      rcases h with h | h
      · exact False.elim (Nat.not_lt_of_ge hb h)
      · exact (sub_lt_iff_lt_add_of_le hb).mpr (by simpa only [Nat.add_comm] using h))
    simp only [hs, ite_false, hsub, bind_eq_result_bind, result_bind_ok, hgt, ite_true]

theorem fips205_wots_chain_zero_steps
    (x pk_seed : Array Std.U8 16#usize) (base_adrs : fips205.Fips205Adrs)
    (start_i : Std.U32) (h : start_i.val ≤ 15) :
    fips205.fips205_wots_chain x start_i 0#u32 pk_seed base_adrs = .ok (some x) := by
  have hs : ¬ start_i > 15#u32 := by
    intro hs
    have hgt : 15 < start_i.val := (UScalar.lt_iff_val _ _).mp hs
    exact Nat.not_lt_of_ge h hgt
  let rem : Std.U32 := ⟨(15#u32).bv - start_i.bv⟩
  have hsub : (15#u32 - start_i : Result Std.U32) = .ok rem := by
    simp [hSub_uscalar_eq, rem, h]
  have hz : ¬ (0#u32 > rem) := by
    intro hh; have := (UScalar.lt_iff_val _ _).mp hh; change rem.val < 0 at this; exact Nat.not_lt_zero _ this
  have hadd : (start_i + 0#u32 : Result Std.U32) = .ok start_i := by
    have hb : start_i.val < 2 ^ 32 := start_i.bv.isLt
    simp [hAdd_uscalar_eq, hb, UScalarTy.numBits]
  have hloop : fips205.fips205_wots_chain_loop x pk_seed base_adrs start_i start_i = .ok x := by
    unfold fips205.fips205_wots_chain_loop
    apply loop_ok_of_loopFuel (fuel := 1) (by decide)
    have hn : ¬ start_i < start_i := UScalar.lt_irrefl start_i
    simp [loopFuel, fips205.fips205_wots_chain_loop.body, hn]
  simp [fips205.fips205_wots_chain, hs, hsub, hadd, hloop]

theorem tsw_canonical_target_sum_spec (w ell1 : Std.U32) :
    (w.val < 2 → fips205.tsw_canonical_target_sum w ell1 = .ok none) ∧
    (2 ≤ w.val → ∃ t, fips205.tsw_canonical_target_sum w ell1 = .ok (some t) ∧
      t.val = (ell1.val * (w.val - 1)) / 2) := by
  constructor
  · intro h
    have hw : w < 2#u32 := (UScalar.lt_iff_val _ _).mpr h
    simp [fips205.tsw_canonical_target_sum, hw]
  · intro h
    have hw : ¬ w < 2#u32 := by
      intro hh
      have hlt : w.val < 2 := (UScalar.lt_iff_val _ _).mp hh
      exact Nat.not_lt_of_ge h hlt
    let wm1 : Std.U32 := ⟨w.bv - (1#u32).bv⟩
    have hle : (1#u32).val ≤ w.val := by change 1 ≤ w.val; exact Nat.le_trans (by decide) h
    have hs : (w - 1#u32 : Result Std.U32) = .ok wm1 := by
      simp only [hSub_uscalar_eq, hle, ite_true]; rfl
    have hv : wm1.val = w.val - 1 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)
    have cast_val (a : Std.U32) : (UScalar.cast .U64 a).val = a.val := by
      have ha : a.val < 2 ^ 32 := a.bv.isLt
      change (a.bv.setWidth 64).toNat = a.val
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by change a.val < 2 ^ 64; exact Nat.lt_trans ha (by decide))]
    have hw_bound : wm1.val < 2 ^ 32 := wm1.bv.isLt
    have he_bound : ell1.val < 2 ^ 32 := ell1.bv.isLt
    have hm : ell1.val * wm1.val < 2 ^ 64 := by
      exact Nat.lt_of_le_of_lt
        (Nat.mul_le_mul_left ell1.val (Nat.le_of_lt hw_bound))
        (Nat.mul_lt_mul_of_pos_right he_bound (by decide))
    let prod : Std.U64 := ⟨(UScalar.cast .U64 ell1).bv * (UScalar.cast .U64 wm1).bv⟩
    have hp : (UScalar.cast .U64 ell1 * UScalar.cast .U64 wm1 : Result Std.U64) =
        .ok prod := by
      simp [hMul_uscalar_eq, cast_val, hm, prod]
    have vp : prod.val = ell1.val * wm1.val := by
      change ((UScalar.cast .U64 ell1).bv * (UScalar.cast .U64 wm1).bv).toNat = _
      rw [BitVec.toNat_mul]
      change ((UScalar.cast .U64 ell1).val * (UScalar.cast .U64 wm1).val) % (2 ^ 64) = _
      rw [cast_val, cast_val, Nat.mod_eq_of_lt hm]
    let t : Std.U64 := ⟨prod.bv / (2#u64).bv⟩
    refine ⟨t, ?_, ?_⟩
    · unfold fips205.tsw_canonical_target_sum
      simp only [hw, ↓reduceIte]
      rw [hs]; dsimp only [Bind.bind, Result.bind, lift]
      rw [hp]; dsimp only [Bind.bind, Result.bind]
      simp [hDiv_uscalar_eq, t]
    · change (prod.bv / (2#u64).bv).toNat = _
      rw [BitVec.toNat_udiv]
      change prod.val / 2 = _
      rw [vp, hv]

/-- Unbounded mathematical sum of the extracted 32-bit digits. -/
@[expose]
def digitsNatSum : List Std.U32 → Nat
  | [] => 0
  | d :: ds => d.val + digitsNatSum ds

private theorem tsw_sum_fuel (w : Std.U32) (target : Std.U64) (digits : Slice Std.U32)
    (suffix : List Std.U32) (idx : Std.Usize) (sum : Std.U64)
    (hi : idx.val ≤ digits.val.length) (hs : digits.val.drop idx.val = suffix) :
    ∃ b, loopFuel (suffix.length + 1)
      (fun (s, i) => fips205.tsw_check_target_sum_loop.body w target digits s i)
      (sum, idx) = .ok b ∧
      (b = true ↔ (∀ d ∈ suffix, d.val < w.val) ∧ sum.val + digitsNatSum suffix = target.val) := by
  induction suffix generalizing idx sum with
  | nil =>
    have hlen := congrArg List.length hs
    simp only [List.length_drop, List.length_nil] at hlen
    have hn : ¬ idx < Slice.len digits := by
      intro h
      have := (UScalar.lt_iff_val _ _).mp h
      rw [Slice.len_val] at this
      exact Nat.not_lt_of_ge (Nat.le_of_sub_eq_zero hlen) this
    refine ⟨decide (sum = target), ?_, ?_⟩
    · simp only [List.length_nil, Nat.zero_add, loopFuel_succ,
        fips205.tsw_check_target_sum_loop.body, hn, ite_false, bind_eq_result_bind, result_bind_ok]
    · simp only [decide_eq_true_eq, List.not_mem_nil, false_implies, implies_true,
        digitsNatSum, Nat.add_zero, true_and]
      exact ⟨fun h => congrArg UScalar.val h, UScalar.eq_of_val_eq⟩
  | cons d ds ih =>
    have hlen := congrArg List.length hs
    simp only [List.length_drop, List.length_cons] at hlen
    have hidx : idx.val < digits.val.length :=
      Nat.lt_of_sub_pos (hlen ▸ Nat.zero_lt_succ ds.length)
    have hlt : idx < Slice.len digits := (UScalar.lt_iff_val _ _).mpr (by simpa using hidx)
    have hd : digits.val[idx.val]'hidx = d := by
      have hhead := congrArg List.head? hs
      simpa only [List.head?_drop, List.getElem?_eq_getElem hidx, List.head?_cons,
        Option.some.injEq] using hhead
    have hget : Slice.index_usize digits idx = .ok d := by
      simp only [Slice.index_usize, dite_eq_left hidx, hd]
    rw [List.length_cons, loopFuel_succ]
    simp only [fips205.tsw_check_target_sum_loop.body, hlt, ite_true, hget,
      bind_eq_result_bind, result_bind_ok]
    by_cases hbad : d >= w
    · simp only [hbad, ite_true]
      refine ⟨false, rfl, ?_⟩
      have hge := (UScalar.le_iff_val _ _).mp hbad
      simp only [Bool.false_eq_true, false_iff]
      intro h
      have := h.1 d (by simp)
      exact Nat.not_lt_of_ge hge this
    · simp only [hbad, ite_false, lift_eq_ok, result_bind_ok]
      have hdw : d.val < w.val := by
        have : ¬ w.val ≤ d.val := fun h => hbad ((UScalar.le_iff_val _ _).mpr h)
        exact Nat.lt_of_not_ge this
      let d64 := UScalar.cast .U64 d
      have hd64 : d64.val = d.val := by
        change (d.bv.setWidth 64).toNat = d.bv.toNat
        rw [BitVec.toNat_setWidth]
        have hb : d.bv.toNat < 2 ^ 32 := d.bv.isLt
        exact Nat.mod_eq_of_lt (Nat.lt_trans hb (by decide))
      have hb : d64.val ≤ 18446744073709551615 := by
        have h := d.bv.isLt
        change d.val < 2 ^ 32 at h
        rw [hd64]
        exact Nat.le_trans (Nat.le_of_lt h) (by decide)
      let capacity : Std.U64 := ⟨core.num.U64.MAX.bv - d64.bv⟩
      have hsub : (core.num.U64.MAX - d64 : Result Std.U64) = .ok capacity := by
        have hb' : d64.val ≤ core.num.U64.MAX.val := hb
        simp only [hSub_uscalar_eq, hb', ite_true]
        rfl
      have hcap : capacity.val = 18446744073709551615 - d.val := by
        change (core.num.U64.MAX.bv - d64.bv).toNat = _
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hb)]
        change 18446744073709551615 - d64.val = _
        rw [hd64]
      rw [hsub, result_bind_ok]
      by_cases hov : sum > capacity
      · simp only [hov, ite_true, result_bind_ok]
        refine ⟨false, rfl, ?_⟩
        have hgt := (UScalar.lt_iff_val _ _).mp hov
        have ht : target.val < 2 ^ 64 := target.bv.isLt
        simp only [Bool.false_eq_true, false_iff]
        intro h
        simp only [digitsNatSum] at h
        have hlarge : 18446744073709551615 < sum.val + d.val := by
          rw [hcap] at hgt
          have := Nat.add_lt_add_right hgt d.val
          rw [Nat.sub_add_cancel (by simpa only [hd64] using hb)] at this
          exact this
        have htotal : 18446744073709551615 < target.val := by
          rw [← h.2, ← Nat.add_assoc]
          exact Nat.lt_of_lt_of_le hlarge (Nat.le_add_right _ _)
        exact Nat.not_lt_of_ge (Nat.le_of_lt_succ ht) htotal
      · have hsum : sum.val + d64.val < 2 ^ 64 := by
          have hle : sum.val ≤ capacity.val := by
            have : ¬ capacity.val < sum.val := fun h => hov ((UScalar.lt_iff_val _ _).mpr h)
            exact Nat.le_of_not_gt this
          rw [hd64]
          have hbound := Nat.add_le_add_right hle d.val
          rw [hcap, Nat.sub_add_cancel (by simpa only [hd64] using hb)] at hbound
          exact Nat.lt_succ_of_le hbound
        let sum' : Std.U64 := ⟨sum.bv + d64.bv⟩
        have hadd : (sum + d64 : Result Std.U64) = .ok sum' := by
          simp only [hAdd_uscalar_eq, hsum, ite_true]
          rfl
        have hsum' : sum'.val = sum.val + d.val := by
          change (sum.bv + d64.bv).toNat = _
          rw [BitVec.toNat_add, Nat.mod_eq_of_lt hsum, hd64]
        let idx' : Std.Usize := ⟨idx.bv + (1#usize).bv⟩
        have hbound : idx.val + 1 < 2 ^ 64 := by
          have h : (Slice.len digits).val < 2 ^ 64 := (Slice.len digits).bv.isLt
          rw [Slice.len_val] at h
          exact Nat.lt_of_le_of_lt hidx h
        have hinc : (idx + 1#usize : Result Std.Usize) = .ok idx' := by
          simp [hAdd_uscalar_eq, hbound, idx']
        have hidx' : idx'.val = idx.val + 1 := by
          change (idx.bv + (1#usize).bv).toNat = _
          rw [BitVec.toNat_add]
          exact Nat.mod_eq_of_lt hbound
        have hs' : digits.val.drop idx'.val = ds := by
          rw [hidx', ← List.drop_drop, hs]
          rfl
        obtain ⟨b, hb, he⟩ := ih idx' sum' (by rw [hidx']; exact hidx) hs'
        simp only [hov, ite_false]
        rw [hadd, result_bind_ok, hinc, result_bind_ok, result_bind_ok]
        refine ⟨b, hb, ?_⟩
        rw [he]
        simp only [List.mem_cons, forall_eq_or_imp, hdw, true_and, digitsNatSum, hsum', Nat.add_assoc]

theorem tsw_check_target_sum_spec (w : Std.U32) (ell1 : Std.Usize)
    (target : Std.U64) (digits : Slice Std.U32) :
    ∃ b, fips205.tsw_check_target_sum w ell1 target digits = .ok b ∧
      (b = true ↔ digits.val.length = ell1.val ∧
        (∀ d ∈ digits.val, d.val < w.val) ∧ digitsNatSum digits.val = target.val) := by
  unfold fips205.tsw_check_target_sum
  by_cases he : Slice.len digits = ell1
  · have helen : digits.val.length = ell1.val := by
      simpa only [Slice.len_val] using congrArg UScalar.val he
    simp only [he, bne_self_eq_false, Bool.false_eq_true, ite_false]
    obtain ⟨b, hb, hp⟩ := tsw_sum_fuel w target digits digits.val 0#usize 0#u64
      (Nat.zero_le _) List.drop_zero
    refine ⟨b, ?_, ?_⟩
    · unfold fips205.tsw_check_target_sum_loop
      apply loop_ok_of_loopFuel (fuel := digits.val.length + 1)
      · simpa only [Slice.len_val] using usize_lt_loopMaxFuel (Slice.len digits)
      · exact hb
    · simpa only [helen, true_and, show (0#u64).val = 0 from rfl, Nat.zero_add] using hp
  · have hne : (Slice.len digits != ell1) = true := by simp [he]
    simp only [hne, ite_true]
    refine ⟨false, rfl, ?_⟩
    simp only [Bool.false_eq_true, false_iff]
    intro h
    exact he (UScalar.eq_of_val_eq (by simpa only [Slice.len_val] using h.1))


end qsag_verified.proofs

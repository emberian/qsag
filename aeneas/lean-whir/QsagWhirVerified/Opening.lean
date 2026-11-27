module
public import QsagWhirVerified.ProtocolWeld
public import QsagWhirVerified.WireBounds
public section
open Aeneas Aeneas.Std
namespace qsag_whir_verified.proofs
set_option linter.unusedSimpArgs false

theorem block_end_spec (len off count width : Usize) :
    block_end len off count width = .ok (boundedEnd len.val off.val count.val width.val) := by
  rw [block_end.public_eqs]
  by_cases hz : width = 0#usize
  · subst width
    simp [boundedEnd, show (0#usize).val = 0 from rfl]
  have hw : 0 < width.val := Nat.pos_of_ne_zero (fun h => hz (UScalar.eq_of_val_eq h))
  simp only [hz, ↓reduceIte, GT.gt, UScalar.lt_iff_val]
  by_cases ho : len.val < off.val
  · have hn : ¬ off.val + count.val * width.val ≤ len.val := by omega
    simp [ho, boundedEnd, hn]
  have hsub := Nat.le_of_not_gt ho
  let diff : Usize := ⟨len.bv - off.bv⟩
  have hdiff : diff.val = len.val - off.val := BitVec.toNat_sub_of_le (BitVec.le_def.mpr hsub)
  let slots : Usize := ⟨diff.bv / width.bv⟩
  have hs : slots.val = (len.val - off.val) / width.val := by
    change (diff.bv / width.bv).toNat = _
    rw [BitVec.toNat_udiv]; exact congrArg (· / width.val) hdiff
  have hd : (len - off : Result Usize) = .ok diff := by simp [hSub_uscalar_eq, hsub, diff]
  have hdiv : (diff / width : Result Usize) = .ok slots := by simp [hDiv_uscalar_eq, Nat.ne_of_gt hw, slots]
  simp only [ho, ↓reduceIte, hd, bind_eq_result_bind, result_bind_ok, hdiv, GT.gt, UScalar.lt_iff_val, hs]
  by_cases hc : count.val ≤ (len.val - off.val) / width.val
  · have hp := (Nat.le_div_iff_mul_le hw).mp hc
    have hf : off.val + count.val * width.val ≤ len.val := by omega
    have hlen : len.val < 2^64 := UScalar.val_lt len
    obtain ⟨p, hm, hv⟩ := usize_mul_bounded count width (by omega)
    obtain ⟨e, ha, he⟩ := usize_add_bounded off p (by omega)
    simp only [Nat.not_lt_of_ge hc, ↓reduceIte, hm, bind_eq_result_bind, result_bind_ok,
      ha, boundedEnd, hw, hf, and_self, Result.ok.injEq, Option.some.injEq]
    apply UScalar.eq_of_val_eq
    rw [UScalar.val_ofNat, Nat.mod_eq_of_lt (by change off.val + count.val * width.val < 2^64; omega)]
    omega
  · have hn : ¬ off.val + count.val * width.val ≤ len.val :=
      fun h => hc ((Nat.le_div_iff_mul_le hw).mpr (by omega))
    simp [Nat.lt_of_not_ge hc, boundedEnd, hn]

private theorem word_run_fuel (bytes : Slice U8) (stop : Usize) (hstop : stop.val ≤ bytes.val.length)
    (n : Nat) (off : Usize) (hspan : off.val + 8*n = stop.val) :
    loopFuel (n+1) (canonical_words_between_loop.body bytes stop) off =
      .ok (fieldWordRun (fun j => (lePackU64At bytes.val j).val) Qsag.goldilocksPrime off.val n) := by
  induction n generalizing off with
  | zero =>
    have hn : ¬ off < stop := (fun h => by have := (UScalar.lt_iff_val ..).mp h; omega)
    rw [loopFuel_succ, canonical_words_between_loop.body.public_eqs]
    simp [hn, fieldWordRun]
  | succ n ih =>
    have hlt : off < stop := (UScalar.lt_iff_val ..).mpr (by omega)
    have hfit : off.val + 8 ≤ bytes.val.length := by omega
    have h8 : (8#usize).val = 8 := rfl
    have hlen := UScalar.val_lt stop
    obtain ⟨next, ha, hv⟩ := usize_add_bounded off 8#usize (by rw [h8]; change stop.val < 2^64 at hlen; omega)
    rw [h8] at hv
    rw [loopFuel_succ, canonical_words_between_loop.body.public_eqs]
    simp only [hlt, ↓reduceIte, decode_canonical_u64_at_spec, hfit, true_and, bind_eq_result_bind, result_bind_ok,
      fieldWordRun]
    by_cases h : IsCanonical (lePackU64At bytes.val off.val)
    · have hp : (lePackU64At bytes.val off.val).val < Qsag.goldilocksPrime := h
      simp only [h, ↓reduceIte, ha, bind_eq_result_bind, result_bind_ok, hp, decide_true, Bool.true_and]
      exact hv ▸ ih next (by omega)
    · have hp : ¬ (lePackU64At bytes.val off.val).val < Qsag.goldilocksPrime := h
      simp [h, hp]

theorem canonical_words_between_refines_qsag (bytes : Slice U8) (off stop : Usize) :
    canonical_words_between bytes off stop = .ok (validWordRegion
      (fun j => (lePackU64At bytes.val j).val) Qsag.goldilocksPrime bytes.val.length off.val stop.val) := by
  rw [canonical_words_between.public_eqs]
  simp only [GT.gt, UScalar.lt_iff_val, Slice.len_val]
  by_cases he : stop.val ≤ bytes.val.length
  · by_cases ho : off.val ≤ stop.val
    · let diff : Usize := ⟨stop.bv - off.bv⟩
      have hd : (stop - off : Result Usize) = .ok diff := by simp [diff, hSub_uscalar_eq, ho]
      have hv : diff.val = stop.val-off.val := BitVec.toNat_sub_of_le (BitVec.le_def.mpr ho)
      let rem : Usize := ⟨diff.bv % (8#usize).bv⟩
      have hm : (diff % 8#usize : Result Usize) = .ok rem := rfl
      have hr : rem.val = (stop.val-off.val)%8 := by
        change (diff.bv % (8#usize).bv).toNat = _
        rw [BitVec.toNat_umod]; exact congrArg (· % 8) hv
      simp only [Nat.not_lt_of_ge he, Nat.not_lt_of_ge ho, ↓reduceIte, hd, hm, bind_eq_result_bind,
        result_bind_ok, validWordRegion, ho, he, true_and]
      by_cases h : (stop.val-off.val)%8 = 0
      · have hz : rem = 0#usize := UScalar.eq_of_val_eq (hr.trans h)
        have hbe : (rem != 0#usize) = false := Bool.eq_false_iff.mpr (fun h => (bne_iff_ne.mp h) hz)
        simp only [hbe, Bool.false_eq_true, ↓reduceIte, h, decide_true, Bool.true_and,
          canonical_words_between_loop.public_eqs]
        apply loop_ok_of_loopFuel (fuel := (stop.val-off.val)/8+1)
        · exact Nat.le_trans (by omega) (usize_lt_loopMaxFuel stop)
        · exact word_run_fuel bytes stop he _ off (by omega)
      · have hn : rem ≠ 0#usize := fun e => h (hr.symm.trans (congrArg UScalar.val e))
        simp [bne_iff_ne.mpr hn, h]
    · simp [Nat.lt_of_not_ge ho, validWordRegion, ho]
  · simp [Nat.lt_of_not_ge he, validWordRegion, he]

theorem qsaghqm2_digest_block_end_refines_qsag (bytes : Slice U8) (off count : Usize) (tag : U8) :
    qsaghqm2_digest_block_end bytes off count tag =
      .ok (digestRegion (fun j => (lePackU64At bytes.val j).val) bytes.val.length off.val count.val
        (show Option Qsag.Aggregation.PublicHemQuintic128 from decodePublicHemProfileTag tag)) := by
  rw [qsaghqm2_digest_block_end.public_eqs]
  by_cases ht : tag = QSAGHQM2_PROFILE_TURBO400
  · simp only [ite_eq_left ht, decodePublicHemProfileTag, digestRegion, block_end_spec, Slice.len_val]
    rfl
  by_cases hg : tag = QSAGHQM2_PROFILE_GL24
  · simp only [decodePublicHemProfileTag, ite_eq_right ht, ite_eq_left hg, digestRegion,
      block_end_spec, Slice.len_val, bind_eq_result_bind, result_bind_ok, show (56#usize).val = 56 from rfl]
    cases h : boundedEnd bytes.val.length off.val count.val 56 with
    | none => rfl
    | some e =>
      simp only [canonical_words_between_refines_qsag, bind_eq_result_bind, result_bind_ok,
        Option.bind_eq_bind, Option.bind_some]
      split <;> rfl
  · simp only [decodePublicHemProfileTag, ite_eq_right ht, ite_eq_right hg, digestRegion]


theorem turbo_digest_block_end (bytes : Slice U8) (off count : Usize) :
    decodePublicHemProfileTag QSAGHQM2_PROFILE_TURBO400 = some Qsag.Aggregation.PublicHemQuintic128.turboShake400 ∧
    qsaghqm2_digest_block_end bytes off count QSAGHQM2_PROFILE_TURBO400 = block_end (Slice.len bytes) off count 50#usize := by
  simp [decodePublicHemProfileTag, qsaghqm2_digest_block_end.public_eqs]

theorem qsaghqm2_opening_bounds_refines_qsag (bytes : Slice U8) (off : Usize) (indices : Slice Usize)
    (depth fold : U32) (base : Bool) (tag : U8) :
    qsaghqm2_opening_bounds bytes off indices depth fold base tag =
      .ok (openingRegion (fun j => (lePackU64At bytes.val j).val) bytes.val.length off.val depth.val
        fold.val (indices.val.map UScalar.val) base
        (show Option Qsag.Aggregation.PublicHemQuintic128 from decodePublicHemProfileTag tag)) := by
  have hmax : MAX_QUINTIC_LOG_CELLS.val = 28 := by rw [max_quintic_log_cells_val]; rfl
  simp only [qsaghqm2_opening_bounds.public_eqs, GT.gt, UScalar.lt_iff_val, hmax, openingRegion]
  by_cases hf : 28 < fold.val
  · simp [hf]
  simp only [hf, ↓reduceIte, false_or, compute_steiner_multiproof_siblings_refines_qsag,
    bind_eq_result_bind, result_bind_ok]
  by_cases hv : depth.val ≤ 28 ∧ Qsag.canopyIndicesOk (2^depth.val) (indices.val.map UScalar.val)
  · have hc := steiner_count_fits_usize _ _ hv.1 hv.2
    let arity : Usize := ⟨(1#usize).bv <<< fold.val⟩
    have hs : (1#usize <<< fold : Result Usize) = .ok arity := by
      have h64 : fold.val < 64 := by omega
      simp [arity, hShlU_uscalar_eq, h64]
    have ha : arity.val = 2^fold.val := by
      have hp := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.le_of_not_gt hf)
      change ((1#usize).bv <<< fold.val).toNat = _
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      change (1 * 2^fold.val) % 2^64 = _
      rw [Nat.one_mul, Nat.mod_eq_of_lt (by omega)]
    have hcount : (UScalar.ofNat .Usize (Qsag.steinerSiblingCount depth.val (indices.val.map UScalar.val))).val =
        Qsag.steinerSiblingCount depth.val (indices.val.map UScalar.val) := (UScalar.val_ofNat ..).trans (Nat.mod_eq_of_lt hc)
    have h0 : (0#usize).val = 0 := rfl
    have h8 : (8#usize).val = 8 := rfl
    have h40 : (40#usize).val = 40 := rfl
    cases base <;>
      simp only [ite_eq_left hv, ite_eq_right (not_not_intro hv), Bool.false_eq_true, ↓reduceIte,
        hs, block_end_spec, bind_eq_result_bind, result_bind_ok, Slice.len_val, h0, h8, h40,
        ha, List.length_map, Option.bind_eq_bind]
    case' false => generalize h : boundedEnd bytes.val.length 0 (2^fold.val) 40 = wide
    case' true => generalize h : boundedEnd bytes.val.length 0 (2^fold.val) 8 = wide
    all_goals
      cases wide with
      | none => rfl
      | some w =>
        simp only [Option.bind_some]
        cases hsplit : boundedEnd bytes.val.length off.val indices.val.length w.val with
        | none => rfl
        | some e =>
          simp only [Option.bind_some]
          rw [canonical_words_between_refines_qsag]
          simp only [bind_eq_result_bind, result_bind_ok]
          split
          · simp only [qsaghqm2_digest_block_end_refines_qsag, hcount,
              bind_eq_result_bind, result_bind_ok]
            cases digestRegion (fun j => (lePackU64At bytes.val j).val) bytes.val.length e.val
                (Qsag.steinerSiblingCount depth.val (indices.val.map UScalar.val)) (decodePublicHemProfileTag tag) <;> rfl
          · rfl
  · simp [hv]

theorem tooth_digest_rejects_noncanonical_word :
    let good := Array.to_slice (Array.repeat 56#usize 0#u8)
    let bad := Array.to_slice (Array.repeat 56#usize 255#u8)
    qsaghqm2_digest_block_end good 0#usize 1#usize QSAGHQM2_PROFILE_GL24 = .ok (some 56#usize) ∧
    qsaghqm2_digest_block_end bad 0#usize 1#usize QSAGHQM2_PROFILE_GL24 = .ok none := by
  dsimp only
  rw [qsaghqm2_digest_block_end_refines_qsag, qsaghqm2_digest_block_end_refines_qsag]
  have hp : decodePublicHemProfileTag QSAGHQM2_PROFILE_GL24 = some .poseidon2Gl24 := by
    rw [decodePublicHemProfileTag, qsaghqm2_profile_gl24_val, qsaghqm2_profile_turbo400_val]
    decide
  have h0 : (0#usize).val = 0 := rfl
  have h1 : (1#usize).val = 1 := rfl
  have h56 : (56#usize).val = 56 := rfl
  have hend : boundedEnd 56 0 1 56 = some 56#usize := rfl
  have hprime : Qsag.goldilocksPrime = 18446744069414584321 := rfl
  have hseven : (56-0)/8 = 7 := rfl
  simp only [hp, digestRegion, Array.to_slice, Array.repeat, h0, h1, h56, List.length_replicate,
    hend, Option.bind_eq_bind, Option.bind_some, validWordRegion, hseven, hprime, lePackU64At, u8_cast_u64_bv]
  decide

end qsag_whir_verified.proofs
end

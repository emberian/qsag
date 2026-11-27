module
public import QsagWhirVerified.FoldPayload
public section
open Aeneas Aeneas.Std
namespace qsag_whir_verified.proofs
set_option linter.unusedSimpArgs false

private abbrev words (bytes : Slice U8) := fun j => (lePackU64At bytes.val j).val

theorem fp5_block_end_refines_qsag (bytes : Slice U8) (off count : Usize) :
    fp5_block_end bytes off count = .ok (fieldRegion
      (fun j => (lePackU64At bytes.val j).val) bytes.val.length off.val count.val Qsag.goldilocksPrime) := by
  simp only [fp5_block_end.public_eqs, block_end_spec, Slice.len_val, fieldRegion,
    show (40#usize).val = 40 from rfl, bind_eq_result_bind, result_bind_ok]
  cases boundedEnd bytes.val.length off.val count.val 40 with
  | none => rfl
  | some e =>
    simp only [Option.bind_eq_bind, Option.bind_some, canonical_words_between_refines_qsag,
      bind_eq_result_bind, result_bind_ok]
    split <;> rfl

theorem qsaghqm2_stage_end_refines_qsag (bytes : Slice U8) (off : Usize)
    (s : StageEnvelope) (base : Bool) (terminal : Usize) (tag : U8) :
    qsaghqm2_stage_end bytes off s base terminal tag = .ok (stageRegion
      (fun j => (lePackU64At bytes.val j).val) bytes.val.length off.val s base terminal.val
      (show Option Qsag.Aggregation.PublicHemQuintic128 from decodePublicHemProfileTag tag)) := by
  have hz : s.step_vars = 0#u32 ↔ s.step_vars.val = 0 := ⟨fun h => h ▸ rfl, fun h => UScalar.eq_of_val_eq h⟩
  have ht : terminal = 0#usize ↔ terminal.val = 0 := ⟨fun h => h ▸ rfl, fun h => UScalar.eq_of_val_eq h⟩
  simp only [qsaghqm2_stage_end.public_eqs, stageRegion, hz, GT.gt, UScalar.lt_iff_val,
    show (6#u32).val = 6 from rfl]
  by_cases h0 : s.step_vars.val = 0
  · simp [h0]
  by_cases h6 : 6 < s.step_vars.val
  · simp [h6, h0]
  have hw : (UScalar.cast .Usize s.step_vars).val = s.step_vars.val := by
    rw [UScalar.cast_val, Nat.mod_eq_of_lt (by change s.step_vars.val < 2^64; omega)]
  have h5 : (5#usize).val = 5 := rfl
  obtain ⟨w, hm, hv⟩ := usize_mul_bounded 5#usize (UScalar.cast .Usize s.step_vars) (by rw [hw,h5]; omega)
  rw [hw,h5] at hv
  simp only [lift_eq_ok, h0, h6, false_or, ↓reduceIte, hm, fp5_block_end_refines_qsag, hv, ht,
    bind_eq_result_bind, result_bind_ok, Option.bind_eq_bind]
  cases fieldRegion (words bytes) bytes.val.length off.val (5 * s.step_vars.val) with
  | none => rfl
  | some folds =>
    by_cases h : terminal.val = 0
    · simp only [h, ↓reduceIte, Option.bind_some, qsaghqm2_digest_block_end_refines_qsag,
        show (1#usize).val = 1 from rfl, bind_eq_result_bind, result_bind_ok]
      cases digestRegion (words bytes) bytes.val.length folds.val 1 (decodePublicHemProfileTag tag) with
      | none => rfl
      | some root =>
        simp only [Option.bind_some, fp5_block_end_refines_qsag, show (2#usize).val = 2 from rfl,
          bind_eq_result_bind, result_bind_ok]
        cases fieldRegion (words bytes) bytes.val.length root.val 2 with
        | none => rfl
        | some start =>
          simp only [Option.bind_some, qsaghqm2_opening_bounds_refines_qsag, result_bind_ok, bind_eq_result_bind]
          cases openingRegion (words bytes) bytes.val.length start.val s.log_leaves.val s.step_vars.val
            (s.indices.val.map UScalar.val) base (decodePublicHemProfileTag tag) <;> rfl
    · simp only [h, ↓reduceIte, Option.bind_some, fp5_block_end_refines_qsag,
        bind_eq_result_bind, result_bind_ok]
      cases fieldRegion (words bytes) bytes.val.length folds.val terminal.val with
      | none => rfl
      | some start =>
          simp only [Option.bind_some, qsaghqm2_opening_bounds_refines_qsag, result_bind_ok, bind_eq_result_bind]
          cases openingRegion (words bytes) bytes.val.length start.val s.log_leaves.val s.step_vars.val
            (s.indices.val.map UScalar.val) base (decodePublicHemProfileTag tag) <;> rfl

private theorem u32_add (a b : U32) (h : a.val + b.val < 2^32) :
    ∃ c : U32, (a+b : Result U32) = .ok c ∧ c.val = a.val+b.val := by
  refine ⟨⟨a.bv + b.bv⟩, ?_, ?_⟩
  · simp [hAdd_uscalar_eq,h]
  · exact (BitVec.toNat_add ..).trans (Nat.mod_eq_of_lt h)

private theorem schedule_sum (rows : Usize) (early a b c d count : U32)
    (hr : rows.val ≤ 20) (ha : a.val ≤ 6) (hb : b.val ≤ 6) (hc : c.val ≤ 6) (hd : d.val ≤ 6) :
    (do let log ← UScalar.cast .U32 rows + 8#u32
        let ab ← a + b
        let abc ← ab + c
        let total ← abc + d
        verify_quintic_schedule_envelope log early total count) =
      .ok (decide (16 ≤ rows.val+8 ∧ rows.val+8 ≤ 28 ∧ count.val = (if rows.val+8 ≤ 22 then 3 else 4) ∧
        1 ≤ early.val ∧ early.val ≤ 8 ∧ early.val + (a.val+b.val+c.val+d.val) = rows.val+8)) := by
  have hr' : (UScalar.cast .U32 rows).val = rows.val := by
    rw [UScalar.cast_val, Nat.mod_eq_of_lt (by change rows.val < 2^32; omega)]
  have h8 : (8#u32).val = 8 := rfl
  obtain ⟨log, hl, hlv⟩ := u32_add (UScalar.cast .U32 rows) 8#u32 (by rw [hr', h8]; omega)
  obtain ⟨ab, hab, habv⟩ := u32_add a b (by omega)
  obtain ⟨abc, habc, habcv⟩ := u32_add ab c (by omega)
  obtain ⟨total, ht, htv⟩ := u32_add abc d (by omega)
  simp only [hl, hab, habc, ht, bind_eq_result_bind, result_bind_ok,
    verify_quintic_schedule_envelope_spec, QuinticScheduleEnvelopeSpec, min_quintic_log_cells_val,
    max_quintic_log_cells_val, hlv, htv, habcv, habv, hr', h8]
  rfl

theorem payload_schedule_ok_refines_qsag (rows : Usize) (early a b c d count : U32) :
    payload_schedule_ok rows early a b c d count =
      .ok (decide (scheduleCounts rows.val early.val a.val b.val c.val d.val count.val)) := by
  simp only [payload_schedule_ok.public_eqs, lift_eq_ok, bind_eq_result_bind, result_bind_ok, scheduleCounts, GT.gt, UScalar.lt_iff_val,
    show (6#u32).val = 6 from rfl, show (20#usize).val = 20 from rfl]
  by_cases hr : rows.val ≤ 20 <;> by_cases ha : a.val ≤ 6 <;> by_cases hb : b.val ≤ 6 <;>
    by_cases hc : c.val ≤ 6 <;> by_cases hd : d.val ≤ 6 <;>
    simp_all only [← Nat.not_le, not_true_eq_false, not_false_eq_true, ↓reduceIte, false_and, true_and, and_false,
      decide_false, decide_true]
  exact schedule_sum _ _ _ _ _ _ _ hr ha hb hc hd

/-- The partition in the certified stage table satisfies the byte verifier's schedule gate. -/
theorem payload_schedule_ok_for_prod_stages (rows : Usize) (early a b c d count : U32)
    (hr : rows.val ≤ 20) (hlo : 16 ≤ rows.val + 8)
    (ha : a.val ≤ 6) (hb : b.val ≤ 6) (hc : c.val ≤ 6) (hd : d.val ≤ 6)
    (hf : a.val + b.val + c.val + d.val =
      ((Qsag.ZkHemV2Cert.zkHemV2ProdStages (rows.val+8)).map Qsag.ClosedWhir.WhirStage.foldK).sum)
    (hn : count.val = (Qsag.ZkHemV2Cert.zkHemV2ProdStages (rows.val+8)).length)
    (he : early.val = rows.val+8 - (a.val + b.val + c.val + d.val)) :
    payload_schedule_ok rows early a b c d count = .ok true := by
  let log := rows.val + 8
  have hl : MIN_QUINTIC_LOG_CELLS.val ≤ log := by rw [min_quintic_log_cells_val]; exact hlo
  have hh : log ≤ MAX_QUINTIC_LOG_CELLS.val := by rw [max_quintic_log_cells_val]; change rows.val+8 ≤ 28; omega
  have ok := (verify_quintic_schedule_envelope_accepts_zkHemV2ProdStages log hl hh).2
  change verify_quintic_schedule_envelope _ _ _ _ = .ok true at ok
  simp only [← hn, ← hf, ← he, log] at ok
  have env := (verify_quintic_schedule_envelope_sound ..).mp ok
  have bound (n : Nat) (h : n < 2^32) : (UScalar.ofNat .U32 n).val = n :=
    (UScalar.val_ofNat ..).trans (Nat.mod_eq_of_lt h)
  have he32 := UScalar.val_lt early
  have hn32 := UScalar.val_lt count
  simp only [QuinticScheduleEnvelopeSpec, min_quintic_log_cells_val, max_quintic_log_cells_val,
    bound _ (by omega : rows.val+8 < 2^32), bound _ he32, bound _ hn32,
    bound _ (by omega : a.val+b.val+c.val+d.val < 2^32)] at env
  rw [payload_schedule_ok_refines_qsag, decide_eq_true (show scheduleCounts _ _ _ _ _ _ _ from
    ⟨hr,ha,hb,hc,hd,env⟩)]

private theorem terminal_size (early : U32) (h : early.val ≤ 8) :
    ∃ w n : Usize, (1#usize <<< early : Result Usize) = .ok w ∧
      (w + 2#usize : Result Usize) = .ok n ∧ n.val = 2^early.val + 2 := by
  let w : Usize := ⟨(1#usize).bv <<< early.val⟩
  have hs : (1#usize <<< early : Result Usize) = .ok w := by
    simp [w, hShlU_uscalar_eq, show early.val < 64 by omega]
  have hp := Nat.pow_le_pow_right (n := 2) (by decide) h
  have hv : w.val = 2^early.val := by
    change ((1#usize).bv <<< early.val).toNat = _
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (1 * 2^early.val) % 2^64 = _
    rw [Nat.one_mul, Nat.mod_eq_of_lt (by omega)]
  have h2 : (2#usize).val = 2 := rfl
  obtain ⟨n, ha, hn⟩ := usize_add_bounded w 2#usize (by rw [hv,h2]; omega)
  exact ⟨w,n,hs,ha,by rw [hn,hv,h2]⟩

private theorem walk_bind {α β : Type} {o : Option α} {f : α → Result (Option β)} {g : α → Option β}
    (h : ∀ x, o = some x → f x = .ok (g x)) :
    Option.rec (.ok none) f o = Result.ok (o.bind g) := by
  cases o with
  | none => rfl
  | some x => exact h x rfl

theorem verify_qsaghqm2_multiproof_and_rounds_refines_qsag
    (bytes : Slice U8) (tag : U8) (rs : Slice Fp5) (early : U32) (s : PayloadStages) :
    verify_qsaghqm2_multiproof_and_rounds bytes tag rs early s = .ok
      (payloadWire (fun j => (lePackU64At bytes.val j).val)
        (fun r => if rs.val.length ≤ 20 ∧ r.val + 360 * rs.val.length ≤ bytes.val.length then
          rowChain bytes.val r.val fp5Zero rs.val else none)
        bytes.val.length rs.val.length early.val
        (show Option Qsag.Aggregation.PublicHemQuintic128 from decodePublicHemProfileTag tag) s) := by
  by_cases h : early.val ≤ 8
  · obtain ⟨w,n,hs,ha,hn⟩ := terminal_size early h
    obtain ⟨a,b,c,last⟩ := s
    cases last <;>
      simp only [verify_qsaghqm2_multiproof_and_rounds.public_eqs, payloadWire, scheduleFits,
        Option.map_none, Option.map_some, Option.getD_none, Option.getD_some, Option.isSome_none,
        Option.isSome_some, Bool.false_eq_true, ↓reduceIte, GT.gt, UScalar.lt_iff_val,
        show (8#u32).val = 8 from rfl, Nat.not_lt_of_ge h, bind_eq_result_bind, result_bind_ok,
        payload_schedule_ok_refines_qsag, Slice.len_val, show (0#u32).val = 0 from rfl,
        show (3#u32).val = 3 from rfl, show (4#u32).val = 4 from rfl, decide_eq_true_eq,
        qsaghqm2_digest_block_end_refines_qsag, verify_qsaghqm2_row_rounds_at_spec, block_end_spec,
        fp5_block_end_refines_qsag, qsaghqm2_stage_end_refines_qsag, hs, ha, hn,
        show (0#usize).val = 0 from rfl, show (1#usize).val = 1 from rfl,
        show (5#usize).val = 5 from rfl, show (256#usize).val = 256 from rfl,
        show (360#usize).val = 360 from rfl, Option.bind_eq_bind]
    all_goals
      split <;> try rfl
      try simp only [Option.bind_assoc]
      repeat' (apply walk_bind; intro x hx; try dsimp only; try simp only [hx, Option.bind_some])
      have hv (x : Usize) : x = Slice.len bytes ↔ x.val = bytes.val.length :=
        ⟨fun e => e ▸ Slice.len_val bytes, fun e => UScalar.eq_of_val_eq (e.trans (Slice.len_val bytes).symm)⟩
      simp only [hv]
      split
      · exact congrArg Result.ok (by assumption)
      · rfl
  · have hbad : ¬ scheduleFits rs.val.length early.val s := fun hs => h hs.2.2.2.2.2.2.2.2.2.1
    have he : early > 8#u32 := (UScalar.lt_iff_val ..).mpr (Nat.lt_of_not_ge h)
    rw [payload_rejects_large_terminal _ _ _ _ _ he]
    simp [payloadWire, hbad]

end qsag_whir_verified.proofs
end

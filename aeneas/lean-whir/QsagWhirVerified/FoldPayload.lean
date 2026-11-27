module
public import QsagWhirVerified.Opening
public import QsagWhirVerified.PayloadWire
public section
open Aeneas Aeneas.Std
namespace qsag_whir_verified.proofs
set_option linter.unusedSimpArgs false

private abbrev rawFold (bytes : List U8) :=
  wireFold (fp5AtBytes bytes) (fun a b d f g claim c =>
    cwyzBridgeFp5Value a b d f g claim c.phi c.theta c.alpha c.beta) bytes.length

private theorem read_fp5 (bytes : Slice U8) (off : Usize) :
    decode_canonical_fp5_at bytes off = .ok (fp5AtBytes bytes.val off.val) :=
  decode_canonical_fp5_at_spec bytes off

private theorem fold_at (bytes : Slice U8) (off : Usize) (claim : Fp5) (c : CwyzFoldChals) :
    verify_qsaghqm2_cwyz_fold_at bytes off claim c = .ok (rawFold bytes.val off.val claim c) := by
  have h200 : (200#usize).val = 200 := rfl
  simp only [verify_qsaghqm2_cwyz_fold_at.public_eqs, has_bytes_at_spec, h200, rawFold,
    wireFold, bind_eq_result_bind, result_bind_ok]
  by_cases h : off.val + 200 ≤ bytes.val.length
  · obtain ⟨j1, ha1, hv1⟩ := slice_offset bytes off 40#usize 40 rfl (by omega)
    obtain ⟨j2, ha2, hv2⟩ := slice_offset bytes off 80#usize 80 rfl (by omega)
    obtain ⟨j3, ha3, hv3⟩ := slice_offset bytes off 120#usize 120 rfl (by omega)
    obtain ⟨j4, ha4, hv4⟩ := slice_offset bytes off 160#usize 160 rfl (by omega)
    simp only [h, decide_true, ↓reduceIte, ha1, ha2, ha3, ha4, read_fp5, hv1, hv2, hv3, hv4,
      cwyz_bridge_claim_step_fp5_refines, bind_eq_result_bind, result_bind_ok, Option.bind_eq_bind]
    cases fp5AtBytes bytes.val off.val <;> try rfl
    cases fp5AtBytes bytes.val (off.val + 40) <;> try rfl
    cases fp5AtBytes bytes.val (off.val + 80) <;> try rfl
    cases fp5AtBytes bytes.val (off.val + 120) <;> try rfl
    cases fp5AtBytes bytes.val (off.val + 160) <;> rfl
  · simp [h]

private theorem map_fold (bytes : List U8) (pos : Nat) (claim : Fp5) (c : CwyzFoldChals) :
    (rawFold bytes pos claim c).map fp5Abs =
      qsagFold (fun j => (fp5AtBytes bytes j).map fp5Abs) fp5Abs bytes.length pos (fp5Abs claim) c := by
  simp only [rawFold, qsagFold, wireFold]
  split <;> try rfl
  cases fp5AtBytes bytes pos <;> try rfl
  cases fp5AtBytes bytes (pos+40) <;> try rfl
  cases fp5AtBytes bytes (pos+80) <;> try rfl
  cases fp5AtBytes bytes (pos+120) <;> try rfl
  cases fp5AtBytes bytes (pos+160) <;> try rfl
  rename_i a b d f g
  have eqn := cwyz_bridge_claim_step_fp5_refines_hemBridgeFoldClaim a b d f g claim c.phi c.theta c.alpha c.beta
  rw [cwyz_bridge_claim_step_fp5_refines] at eqn
  exact congrArg some (Result.ok.inj eqn)

theorem verify_qsaghqm2_cwyz_fold_at_refines_qsag
    (bytes : Slice U8) (off : Usize) (claim : Fp5) (c : CwyzFoldChals) :
    (Option.map fp5Abs <$> verify_qsaghqm2_cwyz_fold_at bytes off claim c) =
      .ok (qsagFold (fun j => (fp5AtBytes bytes.val j).map fp5Abs) fp5Abs bytes.val.length
        off.val (fp5Abs claim) c) := by
  rw [fold_at]
  exact congrArg Result.ok (map_fold ..)

private theorem fold_chain_fuel (bytes : Slice U8) (off : Usize) (cs : Slice CwyzFoldChals)
    (hcap : cs.val.length ≤ 28) (hfit : off.val + 200 * cs.val.length ≤ bytes.val.length)
    (n : Nat) (i : Usize) (hi : i.val + n = cs.val.length) (claim : Fp5) :
    loopFuel (n+1) (fun (v, j) => verify_qsaghqm2_cwyz_folds_at_loop.body bytes off cs v j)
      (claim, i) = .ok (foldMessages (rawFold bytes.val) (off.val + 200*i.val) claim (cs.val.drop i.val)) := by
  induction n generalizing i claim with
  | zero =>
    have hv : i.val = cs.val.length := by omega
    have hn : ¬ i < Slice.len cs := by simp [UScalar.lt_iff_val, hv]
    rw [loopFuel_succ]
    simp [verify_qsaghqm2_cwyz_folds_at_loop.body.public_eqs, hn, hv, foldMessages]
  | succ n ih =>
    have hin : i.val < cs.val.length := by omega
    have hlt : i < Slice.len cs := (UScalar.lt_iff_val ..).mpr (by simpa using hin)
    let c := cs.val[i.val]'hin
    have hidx : Slice.index_usize cs i = .ok c := by simp [Slice.index_usize, hin, c]
    have h200 : (200#usize).val = 200 := rfl
    have h1 : (1#usize).val = 1 := rfl
    obtain ⟨w, hm, hw⟩ := usize_mul_bounded 200#usize i (by rw [h200]; omega)
    rw [h200] at hw
    obtain ⟨j, ha, hj⟩ := slice_offset bytes off w _ hw (by omega)
    obtain ⟨next, hinc, hnext⟩ := usize_add_bounded i 1#usize (by rw [h1]; omega)
    rw [h1] at hnext
    have hdr : cs.val.drop i.val = c :: cs.val.drop next.val := by
      rw [hnext]; exact List.drop_eq_getElem_cons hin
    rw [hdr, foldMessages, loopFuel_succ]
    dsimp only
    have step := verify_qsaghqm2_cwyz_folds_at_loop.body.public_eqs bytes off cs claim i
    simp only [hlt, ↓reduceIte, hm, ha, hidx, copy_fp5_spec, fold_at, hj, hinc,
      bind_eq_result_bind, result_bind_ok] at step
    rw [step]
    cases he : rawFold bytes.val (off.val + 200*i.val) claim c with
    | none => rfl
    | some v =>
      have h := ih next (by omega) v
      have heq : off.val + 200 * next.val = off.val + 200 * i.val + 200 := by omega
      rw [heq] at h
      exact h

private theorem map_fold_chain (bytes : List U8) (pos : Nat) (claim : Fp5) (cs : List CwyzFoldChals) :
    (foldMessages (rawFold bytes) pos claim cs).map fp5Abs =
      foldMessages (qsagFold (fun j => (fp5AtBytes bytes j).map fp5Abs) fp5Abs bytes.length)
        pos (fp5Abs claim) cs := by
  induction cs generalizing pos claim with
  | nil => rfl
  | cons c cs ih =>
    simp only [foldMessages, ← map_fold]
    cases rawFold bytes pos claim c with
    | none => rfl
    | some v => exact ih _ _

theorem verify_qsaghqm2_cwyz_folds_at_refines_qsag
    (bytes : Slice U8) (off : Usize) (claim : Fp5) (cs : Slice CwyzFoldChals) :
    (Option.map fp5Abs <$> verify_qsaghqm2_cwyz_folds_at bytes off claim cs) =
      .ok (if cs.val.length ≤ 28 ∧ off.val + 200 * cs.val.length ≤ bytes.val.length then
        foldMessages (qsagFold (fun j => (fp5AtBytes bytes.val j).map fp5Abs) fp5Abs bytes.val.length)
          off.val (fp5Abs claim) cs.val else none) := by
  have hmax : (UScalar.cast .Usize MAX_QUINTIC_LOG_CELLS).val = 28 := by rw [max_quintic_log_cells_val, UScalar.cast_val]; rfl
  have h200 : (200#usize).val = 200 := rfl
  simp only [verify_qsaghqm2_cwyz_folds_at.public_eqs, GT.gt, UScalar.lt_iff_val, Slice.len_val,
    lift_eq_ok, hmax, block_end_spec, h200, boundedEnd, bind_eq_result_bind, result_bind_ok]
  by_cases hc : cs.val.length ≤ 28
  · by_cases hf : off.val + 200 * cs.val.length ≤ bytes.val.length
    · simp only [Nat.not_lt_of_ge hc, hc, hf, Nat.mul_comm _ 200, true_and, ↓reduceIte,
        show 0 < 200 by decide, verify_qsaghqm2_cwyz_folds_at_loop.public_eqs]
      have iter := fold_chain_fuel bytes off cs hc hf cs.val.length 0#usize (by change 0 + _ = _; omega) claim
      have h0 : (0#usize).val = 0 := rfl
      simp only [h0, Nat.mul_zero, Nat.add_zero, List.drop_zero] at iter
      rw [loop_ok_of_loopFuel (by simpa only [Slice.len_val] using usize_lt_loopMaxFuel (Slice.len cs)) iter]
      exact congrArg Result.ok (map_fold_chain ..)
    · simp [Nat.not_lt_of_ge hc, Nat.mul_comm _ 200, hf] <;> rfl
  · simp [Nat.lt_of_not_ge hc, hc] <;> rfl

set_option maxRecDepth 4096 in
theorem tooth_cwyz_fold_rejects_noncanonical_fifth_element (claim : Fp5) (c : CwyzFoldChals) :
    let bytes : Slice U8 := ⟨List.replicate 192 0#u8 ++ List.replicate 8 255#u8, by decide⟩
    verify_qsaghqm2_cwyz_fold_at bytes 0#usize claim c = .ok none := by
  dsimp only
  rw [fold_at]
  simp only [rawFold, wireFold, fp5AtBytes, lePackU64At, u8_cast_u64_bv, IsCanonicalFp5, IsCanonical]
  rfl

end qsag_whir_verified.proofs
end

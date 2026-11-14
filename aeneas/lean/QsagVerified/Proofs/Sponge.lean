module
import all QsagVerified.Funs

public import QsagVerified.Proofs.Common

public section

namespace qsag_verified.proofs

open Aeneas Aeneas.Std Result ControlFlow Error
open qsag_verified

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

attribute [-simp] BitVec.getLsbD_eq_getElem
attribute [local simp] UScalar.val UScalarTy.numBits

theorem keccak_f1600_round_total (state : Array Std.U64 25#usize) (rc : Std.U64) :
    ∃ state', keccak.keccak_f1600_round state rc = .ok state' := by
  unfold keccak.keccak_f1600_round
  repeat first
    | apply result_bind_total
    | intro _
    | exact array_index_total _ _ (by decide)
    | exact array_update_total _ _ _ (by decide)
    | exact ⟨_, rfl⟩

theorem keccak_f1600_total (state : Array Std.U64 25#usize) :
    ∃ state', keccak.keccak_f1600 state = .ok state' := by
  unfold keccak.keccak_f1600
  repeat first
    | exact keccak_f1600_round_total _ _
    | apply result_bind_total
    | intro _

private theorem u64_shift8 (d : Std.U64) : (d <<< 8#i32 : Result Std.U64) = .ok ⟨d.bv <<< 8⟩ := rfl

private theorem u64_shift16 (d : Std.U64) : (d <<< 16#i32 : Result Std.U64) = .ok ⟨d.bv <<< 16⟩ := rfl

private theorem u64_shift24 (d : Std.U64) : (d <<< 24#i32 : Result Std.U64) = .ok ⟨d.bv <<< 24⟩ := rfl

private theorem u64_shift32 (d : Std.U64) : (d <<< 32#i32 : Result Std.U64) = .ok ⟨d.bv <<< 32⟩ := rfl

private theorem u64_shift40 (d : Std.U64) : (d <<< 40#i32 : Result Std.U64) = .ok ⟨d.bv <<< 40⟩ := rfl

private theorem u64_shift48 (d : Std.U64) : (d <<< 48#i32 : Result Std.U64) = .ok ⟨d.bv <<< 48⟩ := rfl

private theorem u64_shift56 (d : Std.U64) : (d <<< 56#i32 : Result Std.U64) = .ok ⟨d.bv <<< 56⟩ := rfl

theorem rank_lt {i n k : Nat} (h : i + (n + 1) = k) : i < k := by
  rw [← h]
  exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ n)

theorem rank_succ_le {i n k : Nat} (h : i + (n + 1) = k) : i + 1 ≤ k := by
  rw [← h]
  exact Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le n)) i

theorem rank_next {i n k : Nat} (h : i + (n + 1) = k) : i + 1 + n = k := by
  simpa only [Nat.add_assoc, Nat.add_comm 1 n] using h

private theorem load_le_u64_total (block : Std.Array Std.U8 136#usize) (off : Std.Usize)
    (h : off.val + 7 < 136) : ∃ v, keccak.load_le_u64 block off = .ok v := by
  have hb (j : Nat) (hj : j ≤ 7) : off.val + j < 136 := Nat.lt_of_le_of_lt (Nat.add_le_add_left hj _) h
  obtain ⟨j1, hj1, vj1⟩ := checked_add_val off 1#usize (by change off.val + 1 < 2 ^ 64; exact Nat.lt_trans (hb 1 (by decide)) (by decide))
  obtain ⟨j2, hj2, vj2⟩ := checked_add_val off 2#usize (by change off.val + 2 < 2 ^ 64; exact Nat.lt_trans (hb 2 (by decide)) (by decide))
  obtain ⟨j3, hj3, vj3⟩ := checked_add_val off 3#usize (by change off.val + 3 < 2 ^ 64; exact Nat.lt_trans (hb 3 (by decide)) (by decide))
  obtain ⟨j4, hj4, vj4⟩ := checked_add_val off 4#usize (by change off.val + 4 < 2 ^ 64; exact Nat.lt_trans (hb 4 (by decide)) (by decide))
  obtain ⟨j5, hj5, vj5⟩ := checked_add_val off 5#usize (by change off.val + 5 < 2 ^ 64; exact Nat.lt_trans (hb 5 (by decide)) (by decide))
  obtain ⟨j6, hj6, vj6⟩ := checked_add_val off 6#usize (by change off.val + 6 < 2 ^ 64; exact Nat.lt_trans (hb 6 (by decide)) (by decide))
  obtain ⟨j7, hj7, vj7⟩ := checked_add_val off 7#usize (by change off.val + 7 < 2 ^ 64; exact Nat.lt_trans (hb 7 (by decide)) (by decide))
  obtain ⟨v0, hv0⟩ := array_index_total block off (by change off.val < 136; exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h)
  obtain ⟨v1, hv1⟩ := array_index_total block j1 (by change j1.val < 136; change j1.val = off.val + 1 at vj1; rw [vj1]; exact hb 1 (by decide))
  obtain ⟨v2, hv2⟩ := array_index_total block j2 (by change j2.val < 136; change j2.val = off.val + 2 at vj2; rw [vj2]; exact hb 2 (by decide))
  obtain ⟨v3, hv3⟩ := array_index_total block j3 (by change j3.val < 136; change j3.val = off.val + 3 at vj3; rw [vj3]; exact hb 3 (by decide))
  obtain ⟨v4, hv4⟩ := array_index_total block j4 (by change j4.val < 136; change j4.val = off.val + 4 at vj4; rw [vj4]; exact hb 4 (by decide))
  obtain ⟨v5, hv5⟩ := array_index_total block j5 (by change j5.val < 136; change j5.val = off.val + 5 at vj5; rw [vj5]; exact hb 5 (by decide))
  obtain ⟨v6, hv6⟩ := array_index_total block j6 (by change j6.val < 136; change j6.val = off.val + 6 at vj6; rw [vj6]; exact hb 6 (by decide))
  obtain ⟨v7, hv7⟩ := array_index_total block j7 (by change j7.val < 136; change j7.val = off.val + 7 at vj7; rw [vj7]; exact hb 7 (by decide))
  refine ⟨⟨(UScalar.cast .U64 v0).bv ||| ((UScalar.cast .U64 v1).bv <<< 8) ||| ((UScalar.cast .U64 v2).bv <<< 16) ||| ((UScalar.cast .U64 v3).bv <<< 24) ||| ((UScalar.cast .U64 v4).bv <<< 32) ||| ((UScalar.cast .U64 v5).bv <<< 40) ||| ((UScalar.cast .U64 v6).bv <<< 48) ||| ((UScalar.cast .U64 v7).bv <<< 56)⟩, ?_⟩
  unfold keccak.load_le_u64
  apply bind_ok_step hv0
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hj1
  apply bind_ok_step hv1
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (u64_shift8 _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hj2
  apply bind_ok_step hv2
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (u64_shift16 _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hj3
  apply bind_ok_step hv3
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (u64_shift24 _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hj4
  apply bind_ok_step hv4
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (u64_shift32 _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hj5
  apply bind_ok_step hv5
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (u64_shift40 _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hj6
  apply bind_ok_step hv6
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (u64_shift48 _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hj7
  apply bind_ok_step hv7
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (u64_shift56 _)
  rfl

theorem xor_rate_block_total (state : Std.Array Std.U64 25#usize)
    (block : Std.Array Std.U8 136#usize) : ∃ out, keccak.xor_rate_block state block = .ok out := by
  let body := fun (a, i) => keccak.xor_rate_block_loop.body block a i
  let P := fun (n : Nat) (x : Std.Array Std.U64 25#usize × Std.Usize) => x.2.val + n = 17
  have hz : ∀ x, P 0 x → ∃ y, body x = .ok (.done y) ∧ True := by
    rintro ⟨a, i⟩ hi
    have hn : ¬ i < keccak.SHAKE256_RATE_LANES := by
      unfold keccak.SHAKE256_RATE_LANES
      change ¬ i.val < 17
      change i.val + 0 = 17 at hi
      rw [← hi, Nat.add_zero]
      exact Nat.lt_irrefl _
    exact ⟨a, by simp only [body, keccak.xor_rate_block_loop.body, hn, ite_false], True.intro⟩
  have step : ∀ n x, P (n + 1) x → ∃ x', body x = .ok (.cont x') ∧ P n x' := by
    rintro n ⟨a, i⟩ hi
    change i.val + (n + 1) = 17 at hi
    have hlt : i < keccak.SHAKE256_RATE_LANES := by unfold keccak.SHAKE256_RATE_LANES; change i.val < 17; exact rank_lt hi
    obtain ⟨off, hoff, voff⟩ := checked_mul_val 8#usize i (by change 8 * i.val < 2 ^ 64; exact Nat.lt_trans (Nat.mul_lt_mul_of_pos_left (rank_lt hi) (by decide : 0 < 8)) (by decide))
    change off.val = 8 * i.val at voff
    obtain ⟨v, hv⟩ := load_le_u64_total block off (by rw [voff]; exact Nat.lt_of_le_of_lt (Nat.add_le_add_right (Nat.mul_le_mul_left 8 (Nat.le_of_lt_succ (rank_lt hi))) 7) (by decide))
    obtain ⟨lane, hlane⟩ := array_index_total a i (by change i.val < 25; exact Nat.lt_trans (rank_lt hi) (by decide))
    obtain ⟨a', ha'⟩ := array_update_total a i (lane ^^^ v) (by change i.val < 25; exact Nat.lt_trans (rank_lt hi) (by decide))
    obtain ⟨i', hi', vi'⟩ := checked_add_val i 1#usize (by change i.val + 1 < 2 ^ 64; exact Nat.lt_of_le_of_lt (rank_succ_le hi) (by decide))
    refine ⟨(a', i'), ?_, ?_⟩
    · simp only [body, keccak.xor_rate_block_loop.body, hlt, ite_true, hoff,
        hv, hlane, ha', hi', bind_eq_result_bind, result_bind_ok, lift_eq_ok]
    · change i'.val + n = 17
      change i'.val = i.val + 1 at vi'
      rw [vi']; exact rank_next hi
  obtain ⟨out, hout, _⟩ := loopFuel_total_rank body P (fun _ => True) hz step 17 (state, 0#usize) (by rfl)
  refine ⟨out, ?_⟩
  unfold keccak.xor_rate_block keccak.xor_rate_block_loop
  exact loop_ok_of_loopFuel (fuel := 18) (by decide) hout

private theorem sponge_zero_tail_total (buf : Std.Array Std.U8 136#usize) (start : Std.Usize)
    (hs : start.val ≤ 136) : ∃ out, keccak.Shake256Sponge.finalize_loop buf start = .ok out := by
  let body := fun (a, i) => keccak.Shake256Sponge.finalize_loop.body a i
  let P := fun (n : Nat) (x : Std.Array Std.U8 136#usize × Std.Usize) => x.2.val + n = 136
  have hz : ∀ x, P 0 x → ∃ y, body x = .ok (.done y) ∧ True := by
    rintro ⟨a, i⟩ hi
    have hn : ¬ i < keccak.SHAKE256_RATE_BYTES := by
      unfold keccak.SHAKE256_RATE_BYTES
      change ¬ i.val < 136
      change i.val + 0 = 136 at hi
      rw [← hi, Nat.add_zero]
      exact Nat.lt_irrefl _
    exact ⟨a, by simp only [body, keccak.Shake256Sponge.finalize_loop.body, hn, ite_false], True.intro⟩
  have step : ∀ n x, P (n + 1) x → ∃ x', body x = .ok (.cont x') ∧ P n x' := by
    rintro n ⟨a, i⟩ hi
    change i.val + (n + 1) = 136 at hi
    have hlt : i < keccak.SHAKE256_RATE_BYTES := by unfold keccak.SHAKE256_RATE_BYTES; change i.val < 136; exact rank_lt hi
    obtain ⟨a', ha'⟩ := array_update_total a i 0#u8 (by change i.val < 136; exact rank_lt hi)
    obtain ⟨i', hi', vi'⟩ := checked_add_val i 1#usize (by change i.val + 1 < 2 ^ 64; exact Nat.lt_of_le_of_lt (rank_succ_le hi) (by decide))
    refine ⟨(a', i'), ?_, ?_⟩
    · simp only [body, keccak.Shake256Sponge.finalize_loop.body, hlt, ite_true,
        ha', hi', bind_eq_result_bind, result_bind_ok]
    · change i'.val + n = 136
      change i'.val = i.val + 1 at vi'
      rw [vi']; exact rank_next hi
  obtain ⟨out, hout, _⟩ := loopFuel_total_rank body P (fun _ => True) hz step
    (136 - start.val) (buf, start) (by change start.val + (136 - start.val) = 136; exact Nat.add_sub_of_le hs)
  refine ⟨out, ?_⟩
  unfold keccak.Shake256Sponge.finalize_loop
  apply loop_ok_of_loopFuel (fuel := 136 - start.val + 1)
  · apply Nat.le_trans (show 136 - start.val + 1 ≤ 137 from Nat.add_le_add_right (Nat.sub_le _ _) 1); decide
  · exact hout

private theorem sponge_finalize_short (sp : keccak.Shake256Sponge)
    (hn : sp.squeezing = false) (hb : sp.buf_len.val < 136) :
    ∃ out, keccak.Shake256Sponge.finalize sp = .ok out ∧ out.squeeze_offset = 0#usize := by
  have hlt : ¬ sp.buf_len >= keccak.SHAKE256_RATE_BYTES := by unfold keccak.SHAKE256_RATE_BYTES; change ¬ 136 ≤ sp.buf_len.val; exact Nat.not_le_of_gt hb
  obtain ⟨buf, hbuf⟩ := sponge_zero_tail_total sp.buf sp.buf_len (Nat.le_of_lt hb)
  obtain ⟨v, hv⟩ := array_index_total buf sp.buf_len hb
  obtain ⟨buf', hbuf'⟩ := array_update_total buf sp.buf_len (v ^^^ sp.suffix) hb
  obtain ⟨last, hlast⟩ := array_index_total buf' 135#usize (by decide)
  obtain ⟨buf'', hbuf''⟩ := array_update_total buf' 135#usize (last ^^^ 128#u8) (by decide)
  obtain ⟨st, hst⟩ := xor_rate_block_total sp.state buf''
  obtain ⟨st', hst'⟩ := keccak_f1600_total st
  have hsub : (keccak.SHAKE256_RATE_BYTES - 1#usize : Result Std.Usize) = .ok 135#usize := by
    unfold keccak.SHAKE256_RATE_BYTES
    rfl
  refine ⟨{ sp with state := st', buf := buf'', buf_len := sp.buf_len, squeezing := true, squeeze_offset := 0#usize }, ?_, rfl⟩
  simp only [keccak.Shake256Sponge.finalize, hn, Bool.false_eq_true, ite_false,
    hlt, hbuf, hv, hbuf', hsub, hlast, hbuf'', hst, hst', bind_eq_result_bind,
    result_bind_ok, lift_eq_ok]

theorem sponge_absorb_short (sp : keccak.Shake256Sponge) (data : Slice Std.U8)
    (hn : sp.squeezing = false) (hb : sp.buf_len.val + data.val.length < 136) :
    ∃ out, keccak.Shake256Sponge.absorb sp data = .ok out ∧
      out.squeezing = false ∧ out.buf_len.val = sp.buf_len.val + data.val.length := by
  let finish := sp.buf_len.val + data.val.length
  let body := fun (a, buf, i, pos) => keccak.Shake256Sponge.absorb_loop.body data a buf i pos
  let P := fun (n : Nat) (x : Std.Array Std.U64 25#usize × Std.Array Std.U8 136#usize × Std.Usize × Std.Usize) =>
    x.2.2.2.val + n = data.val.length ∧ x.2.2.1.val + n = finish
  let Q := fun (x : Std.Array Std.U64 25#usize × Std.Array Std.U8 136#usize × Std.Usize) => x.2.2.val = finish
  have hz : ∀ x, P 0 x → ∃ y, body x = .ok (.done y) ∧ Q y := by
    rintro ⟨a, buf, i, pos⟩ ⟨hp, hi⟩
    have he : ¬ pos < Slice.len data := by
      change ¬ pos.val < (Slice.len data).val
      rw [Slice.len_val]
      change pos.val + 0 = data.val.length at hp
      rw [← hp, Nat.add_zero]
      exact Nat.lt_irrefl _
    exact ⟨(a, buf, i), by simp only [body, keccak.Shake256Sponge.absorb_loop.body, he, ite_false], by simpa using hi⟩
  have step : ∀ n x, P (n + 1) x → ∃ x', body x = .ok (.cont x') ∧ P n x' := by
    rintro n ⟨a, buf, i, pos⟩ ⟨hp, hi⟩
    change pos.val + (n + 1) = data.val.length at hp
    change i.val + (n + 1) = finish at hi
    have hpos : pos < Slice.len data := by
      change pos.val < (Slice.len data).val
      rw [Slice.len_val]; exact rank_lt hp
    have hib : i.val < 136 := by exact Nat.lt_trans (rank_lt hi) hb
    have hilt : i < keccak.SHAKE256_RATE_BYTES := by unfold keccak.SHAKE256_RATE_BYTES; change i.val < 136; exact hib
    obtain ⟨v, hv⟩ := slice_index_total data pos (rank_lt hp)
    obtain ⟨buf', hbuf⟩ := array_update_total buf i v hib
    obtain ⟨i', hi', vi'⟩ := checked_add_val i 1#usize (by change i.val + 1 < 2 ^ 64; exact Nat.lt_of_le_of_lt (rank_succ_le hi) (Nat.lt_trans hb (by decide)))
    obtain ⟨pos', hp', vp'⟩ := checked_add_val pos 1#usize (by
      change pos.val + 1 < 2 ^ 64
      exact Nat.lt_of_le_of_lt (rank_succ_le hp)
        (Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hb) (by decide)))
    change i'.val = i.val + 1 at vi'
    change pos'.val = pos.val + 1 at vp'
    have hne : i' ≠ keccak.SHAKE256_RATE_BYTES := by
      intro he
      have := congrArg UScalar.val he
      rw [keccak.SHAKE256_RATE_BYTES] at this
      change i'.val = 136 at this
      have hsmall : i'.val < 136 := by rw [vi']; exact Nat.lt_of_le_of_lt (rank_succ_le hi) hb
      rw [this] at hsmall
      exact Nat.lt_irrefl _ hsmall
    refine ⟨(a, buf', i', pos'), ?_, ?_⟩
    · simp only [body, keccak.Shake256Sponge.absorb_loop.body, hpos, hilt, ite_true,
        hv, hbuf, hi', hp', hne, ite_false, bind_eq_result_bind, result_bind_ok]
    · change pos'.val + n = data.val.length ∧ i'.val + n = finish
      constructor
      · rw [vp']; exact rank_next hp
      · rw [vi']; exact rank_next hi
  obtain ⟨⟨a, buf, i⟩, hloop, hi⟩ := loopFuel_total_rank body P Q hz step data.val.length
    (sp.state, sp.buf, sp.buf_len, 0#usize) (by constructor; exact Nat.zero_add _; rfl)
  have hactual : keccak.Shake256Sponge.absorb_loop sp.state sp.buf sp.buf_len data 0#usize = .ok (a, buf, i) := by
    unfold keccak.Shake256Sponge.absorb_loop
    apply loop_ok_of_loopFuel (fuel := data.val.length + 1)
    · simpa only [Slice.len_val] using usize_lt_loopMaxFuel (Slice.len data)
    · exact hloop
  refine ⟨{ sp with state := a, buf := buf, buf_len := i }, ?_, hn, hi⟩
  simp only [keccak.Shake256Sponge.absorb, hn, Bool.false_eq_true, ite_false,
    hactual, bind_eq_result_bind, result_bind_ok]

theorem sponge_squeeze_short (sp : keccak.Shake256Sponge) (out : Slice Std.U8)
    (size : Nat) (hsize : size ≤ 136)
    (hn : sp.squeezing = false) (hb : sp.buf_len.val < 136) (hlen : out.val.length = size) :
    ∃ result, keccak.Shake256Sponge.squeeze sp out = .ok result := by
  obtain ⟨sp0, hfinal, hoff⟩ := sponge_finalize_short sp hn hb
  let body := fun (st, dst, i) => keccak.Shake256Sponge.squeeze_loop.body st dst i
  let P := fun (n : Nat) (x : keccak.Shake256Sponge × Slice Std.U8 × Std.Usize) =>
    x.2.2.val + n = size ∧ x.2.1.val.length = size ∧ x.1.squeeze_offset.val = x.2.2.val
  have hz : ∀ x, P 0 x → ∃ y, body x = .ok (.done y) ∧ True := by
    rintro ⟨st, dst, i⟩ ⟨hi, hd, _⟩
    have he : ¬ i < Slice.len dst := by
      change ¬ i.val < (Slice.len dst).val
      rw [Slice.len_val, hd]
      change i.val + 0 = size at hi
      rw [← hi, Nat.add_zero]
      exact Nat.lt_irrefl _
    exact ⟨(st, dst), by simp only [body, keccak.Shake256Sponge.squeeze_loop.body, he, ite_false], True.intro⟩
  have step : ∀ n x, P (n + 1) x → ∃ x', body x = .ok (.cont x') ∧ P n x' := by
    rintro n ⟨st, dst, i⟩ ⟨hi, hd, ho⟩
    change i.val + (n + 1) = size at hi
    change dst.val.length = size at hd
    change st.squeeze_offset.val = i.val at ho
    have hlt : i < Slice.len dst := by
      change i.val < (Slice.len dst).val
      rw [Slice.len_val, hd]; exact rank_lt hi
    have hno : ¬ st.squeeze_offset >= keccak.SHAKE256_RATE_BYTES := by
      unfold keccak.SHAKE256_RATE_BYTES
      change ¬ 136 ≤ st.squeeze_offset.val
      rw [ho]
      exact Nat.not_le_of_gt (Nat.lt_of_lt_of_le (rank_lt hi) hsize)
    let lane : Std.Usize := ⟨st.squeeze_offset.bv / (8#usize).bv⟩
    let rem : Std.Usize := ⟨st.squeeze_offset.bv % (8#usize).bv⟩
    have hdiv : (st.squeeze_offset / 8#usize : Result Std.Usize) = .ok lane := rfl
    have hmod : (st.squeeze_offset % 8#usize : Result Std.Usize) = .ok rem := rfl
    have vlane : lane.val = st.squeeze_offset.val / 8 := BitVec.toNat_udiv
    have vrem : rem.val = st.squeeze_offset.val % 8 := BitVec.toNat_umod
    have hrem : rem.val < 8 := by rw [vrem]; exact Nat.mod_lt _ (by decide)
    let byte := UScalar.cast .U32 rem
    have vbyte : byte.val = rem.val := by
      change (rem.bv.setWidth 32).toNat = rem.bv.toNat
      rw [BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt (by change rem.val < 2 ^ 32; exact Nat.lt_trans hrem (by decide))
    obtain ⟨shift, hshift, vshift⟩ := checked_mul_val 8#u32 byte (by change 8 * byte.val < 2 ^ 32; rw [vbyte]; exact Nat.lt_trans (Nat.mul_lt_mul_of_pos_left hrem (by decide : 0 < 8)) (by decide))
    change shift.val = 8 * byte.val at vshift
    obtain ⟨v, hv⟩ := array_index_total st.state lane (by change lane.val < 25; rw [vlane, ho]; exact (Nat.div_lt_iff_lt_mul (by decide)).mpr (Nat.lt_of_lt_of_le (rank_lt hi) (Nat.le_trans hsize (by decide))))
    let shifted : Std.U64 := ⟨v.bv >>> shift.val⟩
    have hshifted : (v >>> shift : Result Std.U64) = .ok shifted := by
      change (if shift.val < 64 then Result.ok shifted else Result.fail .integerOverflow) = Result.ok shifted
      exact ite_eq_left (by rw [vshift, vbyte]; exact Nat.mul_lt_mul_of_pos_left hrem (by decide))
    obtain ⟨dst', hdst, vdst⟩ := slice_update_total dst i
      (UScalar.cast .U8 (shifted &&& 255#u64)) (by rw [hd]; exact rank_lt hi)
    obtain ⟨i', hi', vi'⟩ := checked_add_val i 1#usize (by change i.val + 1 < 2 ^ 64; exact Nat.lt_of_le_of_lt (Nat.le_trans (rank_succ_le hi) hsize) (by decide))
    obtain ⟨off', hoff', voff'⟩ := checked_add_val st.squeeze_offset 1#usize
      (by change st.squeeze_offset.val + 1 < 2 ^ 64; rw [ho]; exact Nat.lt_of_le_of_lt (Nat.le_trans (rank_succ_le hi) hsize) (by decide))
    change i'.val = i.val + 1 at vi'
    change off'.val = st.squeeze_offset.val + 1 at voff'
    refine ⟨({ st with squeeze_offset := off' }, dst', i'), ?_, ?_⟩
    · simp only [body, keccak.Shake256Sponge.squeeze_loop.body, hlt, ite_true, hno, ite_false,
        hdiv, hmod, hv, hi', hoff', bind_eq_result_bind, result_bind_ok, lift_eq_ok]
      rw [hshift, result_bind_ok, hshifted, result_bind_ok, hdst, result_bind_ok]
    · change i'.val + n = size ∧ dst'.val.length = size ∧ off'.val = i'.val
      exact ⟨by rw [vi']; exact rank_next hi, vdst.trans hd, by rw [voff', vi', ho]⟩
  obtain ⟨result, hloop, _⟩ := loopFuel_total_rank body P (fun _ => True) hz step size
    (sp0, out, 0#usize) ⟨Nat.zero_add _, hlen, by rw [hoff]⟩
  have hactual : keccak.Shake256Sponge.squeeze_loop sp0 out 0#usize = .ok result := by
    unfold keccak.Shake256Sponge.squeeze_loop
    exact loop_ok_of_loopFuel (fuel := size + 1) (Nat.le_trans (Nat.add_le_add_right hsize 1) (by decide)) hloop
  exact ⟨result, by simp only [keccak.Shake256Sponge.squeeze, hfinal, hactual, bind_eq_result_bind, result_bind_ok]⟩


end qsag_verified.proofs

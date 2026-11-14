module

public import QsagVerified.Proofs.Adrs
public import QsagVerified.Proofs.Sponge

public section

namespace qsag_verified.proofs

open Aeneas Aeneas.Std Result ControlFlow Error
open qsag_verified

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

attribute [-simp] BitVec.getLsbD_eq_getElem
attribute [local simp] UScalar.val UScalarTy.numBits

theorem fips205_f_total (pk_seed : Std.Array Std.U8 16#usize)
    (adrs : fips205.Fips205Adrs) (m1 : Std.Array Std.U8 16#usize) :
    ∃ out, fips205.fips205_f pk_seed adrs m1 = .ok out := by
  obtain ⟨bytes, hbytes, _⟩ := fips205_adrs_roundtrip_spec adrs
  let sp0 : keccak.Shake256Sponge :=
    ⟨Std.Array.repeat 25#usize 0#u64, Std.Array.repeat 136#usize 0#u8,
      0#usize, 31#u8, false, 0#usize⟩
  have hnew : keccak.Shake256Sponge.new_shake256 = .ok sp0 := rfl
  have hp : (Std.Array.to_slice pk_seed).val.length = 16 := pk_seed.property
  have ha : (Std.Array.to_slice bytes).val.length = 32 := bytes.property
  have hm : (Std.Array.to_slice m1).val.length = 16 := m1.property
  obtain ⟨sp1, hsp1, hn1, hv1⟩ := sponge_absorb_short sp0 (Std.Array.to_slice pk_seed) rfl
    (by change 0 + _ < 136; rw [hp]; decide)
  have hv1' : sp1.buf_len.val = 16 := by simpa only [hp, show sp0.buf_len.val = 0 from rfl, Nat.zero_add] using hv1
  obtain ⟨sp2, hsp2, hn2, hv2⟩ := sponge_absorb_short sp1 (Std.Array.to_slice bytes) hn1 (by rw [hv1', ha]; decide)
  have hv2' : sp2.buf_len.val = 48 := by simpa only [hv1', ha] using hv2
  obtain ⟨sp3, hsp3, hn3, hv3⟩ := sponge_absorb_short sp2 (Std.Array.to_slice m1) hn2 (by rw [hv2', hm]; decide)
  have hv3' : sp3.buf_len.val = 64 := by simpa only [hv2', hm] using hv3
  let out := Std.Array.repeat 16#usize 0#u8
  obtain ⟨result, hresult⟩ := sponge_squeeze_short sp3 (Std.Array.to_slice_mut out).1 16 (by decide) hn3
    (by rw [hv3']; decide) (by rfl)
  unfold fips205.fips205_f
  simp only [hbytes, hnew, hsp1, hsp2, hsp3, bind_eq_result_bind, result_bind_ok, lift_eq_ok]
  rw [hresult, result_bind_ok]
  exact ⟨_, rfl⟩

private def wotsIter (pk_seed : Std.Array Std.U8 16#usize) (adrs : fips205.Fips205Adrs)
    (start : Nat) : Nat → Std.Array Std.U8 16#usize → Result (Std.Array Std.U8 16#usize)
  | 0, x => .ok x
  | n + 1, x => do
      let y ← fips205.fips205_f pk_seed { adrs with hash := ⟨BitVec.ofNat 32 start⟩ } x
      wotsIter pk_seed adrs (start + 1) n y

private theorem wotsIter_total (pk : Std.Array Std.U8 16#usize) (a : fips205.Fips205Adrs)
    (start n : Nat) (x : Std.Array Std.U8 16#usize) : ∃ y, wotsIter pk a start n x = .ok y := by
  induction n generalizing start x with
  | zero => exact ⟨x, rfl⟩
  | succ n ih =>
    obtain ⟨mid, hm⟩ := fips205_f_total pk { a with hash := ⟨BitVec.ofNat 32 start⟩ } x
    obtain ⟨y, hy⟩ := ih (start + 1) mid
    exact ⟨y, by simp only [wotsIter, hm, hy, bind_eq_result_bind, result_bind_ok]⟩

private theorem result_bind_assoc {α β γ : Type} (x : Result α) (f : α → Result β) (g : β → Result γ) :
    Result.bind (Result.bind x f) g = Result.bind x (fun a => Result.bind (f a) g) := by
  cases x <;> rfl

private theorem wotsIter_append (pk : Std.Array Std.U8 16#usize) (a : fips205.Fips205Adrs)
    (start n m : Nat) (x : Std.Array Std.U8 16#usize) :
    wotsIter pk a start (n + m) x =
      Result.bind (wotsIter pk a start n x) (fun mid => wotsIter pk a (start + n) m mid) := by
  induction n generalizing start x with
  | zero => simp only [Nat.zero_add, Nat.add_zero, wotsIter, result_bind_ok]
  | succ n ih =>
    simp only [Nat.succ_add, wotsIter, bind_eq_result_bind, result_bind_assoc, ih]
    rfl

private theorem wots_chain_fuel (pk : Std.Array Std.U8 16#usize) (a : fips205.Fips205Adrs)
    (last j : Std.U32) (n : Nat) (x : Std.Array Std.U8 16#usize)
    (he : last.val = j.val + n) (hb : last.val ≤ 15) :
    loopFuel (n + 1) (fun (v, i) => fips205.fips205_wots_chain_loop.body pk a last v i) (x, j) =
      wotsIter pk a j.val n x := by
  induction n generalizing j x with
  | zero =>
    have hn : ¬ j < last := by change ¬ j.val < last.val; rw [he, Nat.add_zero]; exact Nat.lt_irrefl _
    simp only [loopFuel_succ, fips205.fips205_wots_chain_loop.body, hn, ite_false,
      wotsIter, bind_eq_result_bind, result_bind_ok]
  | succ n ih =>
    have hlt : j < last := by change j.val < last.val; exact rank_lt he.symm
    have hj : (⟨BitVec.ofNat 32 j.val⟩ : Std.U32) = j := by
      apply UScalar.ext
      exact (BitVec.ofNat_toNat 32 j.bv).trans (BitVec.setWidth_eq _)
    obtain ⟨mid, hm⟩ := fips205_f_total pk { a with hash := j } x
    obtain ⟨j', hj', vj'⟩ := checked_add_val j 1#u32 (by change j.val + 1 < 2 ^ 32; exact Nat.lt_of_le_of_lt (Nat.le_trans (rank_succ_le he.symm) hb) (by decide))
    change j'.val = j.val + 1 at vj'
    rw [loopFuel_succ]
    simp only [fips205.fips205_wots_chain_loop.body, hlt, ite_true, hm, hj',
      bind_eq_result_bind, result_bind_ok, wotsIter, hj]
    change loopFuel (n + 1) (fun (v, i) => fips205.fips205_wots_chain_loop.body pk a last v i) (mid, j') = wotsIter pk a (j.val + 1) n mid
    rw [ih j' mid (by rw [vj']; exact (rank_next he.symm).symm), vj']

private theorem wots_chain_run (x pk : Std.Array Std.U8 16#usize) (a : fips205.Fips205Adrs)
    (start steps : Std.U32) (h : start.val + steps.val ≤ 15) :
    ∃ out, fips205.fips205_wots_chain x start steps pk a = .ok (some out) ∧
      wotsIter pk a start.val steps.val x = .ok out := by
  have hs : start.val ≤ 15 := Nat.le_trans (Nat.le_add_right _ _) h
  have hstart : ¬ start > 15#u32 := by change ¬ 15 < start.val; exact Nat.not_lt_of_ge hs
  let capacity : Std.U32 := ⟨(15#u32).bv - start.bv⟩
  have hsub : (15#u32 - start : Result Std.U32) = .ok capacity := by
    simp [hSub_uscalar_eq, hs, capacity]
  have vcap : capacity.val = 15 - start.val := by
    exact BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change start.val ≤ 15; exact hs))
  have hsteps : ¬ steps > capacity := by change ¬ capacity.val < steps.val; rw [vcap]; exact Nat.not_lt_of_ge (Nat.le_sub_of_add_le (by simpa only [Nat.add_comm] using h))
  obtain ⟨last, hlast, vlast⟩ := checked_add_val start steps (by change start.val + steps.val < 2 ^ 32; exact Nat.lt_of_le_of_lt h (by decide))
  obtain ⟨out, hout⟩ := wotsIter_total pk a start.val steps.val x
  have hloop : fips205.fips205_wots_chain_loop x pk a last start = .ok out := by
    unfold fips205.fips205_wots_chain_loop
    apply loop_ok_of_loopFuel (fuel := steps.val + 1)
    · apply Nat.le_trans (show steps.val + 1 ≤ 16 from Nat.add_le_add_right (Nat.le_trans (Nat.le_add_left _ _) h) 1); decide
    · rw [wots_chain_fuel pk a last start steps.val x vlast (by rw [vlast]; exact h)]
      exact hout
  exact ⟨out, by simp only [fips205.fips205_wots_chain, hstart, hsteps, ite_false,
    hsub, hlast, hloop, bind_eq_result_bind, result_bind_ok], hout⟩

theorem fips205_wots_chain_compose (x pk_seed : Std.Array Std.U8 16#usize)
    (adrs : fips205.Fips205Adrs) (start_i s1 s2 : Std.U32)
    (h : start_i.val + s1.val + s2.val ≤ 15) :
    ∃ mid out,
      fips205.fips205_wots_chain x start_i s1 pk_seed adrs = .ok (some mid) ∧
      fips205.fips205_wots_chain mid ⟨start_i.bv + s1.bv⟩ s2 pk_seed adrs = .ok (some out) ∧
      fips205.fips205_wots_chain x start_i ⟨s1.bv + s2.bv⟩ pk_seed adrs = .ok (some out) := by
  have hfirst : start_i.val + s1.val ≤ 15 := Nat.le_trans (Nat.le_add_right _ _) h
  have hcombined : start_i.val + (s1.val + s2.val) ≤ 15 := by simpa only [Nat.add_assoc] using h
  have hrest : s1.val + s2.val ≤ 15 := Nat.le_trans (Nat.le_add_left _ _) hcombined
  have hstart : (⟨start_i.bv + s1.bv⟩ : Std.U32).val = start_i.val + s1.val :=
    (BitVec.toNat_add _ _).trans (Nat.mod_eq_of_lt (by change start_i.val + s1.val < 2 ^ 32; exact Nat.lt_of_le_of_lt hfirst (by decide)))
  have hsteps : (⟨s1.bv + s2.bv⟩ : Std.U32).val = s1.val + s2.val :=
    (BitVec.toNat_add _ _).trans (Nat.mod_eq_of_lt (by change s1.val + s2.val < 2 ^ 32; exact Nat.lt_of_le_of_lt hrest (by decide)))
  obtain ⟨mid, hm, hmi⟩ := wots_chain_run x pk_seed adrs start_i s1 hfirst
  obtain ⟨out, ho, hoi⟩ := wots_chain_run mid pk_seed adrs ⟨start_i.bv + s1.bv⟩ s2 (by rw [hstart]; exact h)
  obtain ⟨out', hc, hci⟩ := wots_chain_run x pk_seed adrs start_i ⟨s1.bv + s2.bv⟩ (by rw [hsteps]; exact hcombined)
  rw [hstart] at hoi
  rw [hsteps, wotsIter_append, hmi, result_bind_ok, hoi] at hci
  cases hci
  exact ⟨mid, out, hm, ho, hc⟩


end qsag_verified.proofs

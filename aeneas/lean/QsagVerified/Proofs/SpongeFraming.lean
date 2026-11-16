module
import all QsagVerified.Funs
import all QsagVerified.Proofs.Adrs
public import QsagVerified.Proofs.SpongeConformance
import all QsagVerified.Proofs.RealSpecKeccakWeld

/-!
Absorb and padding equivalence of the extracted streaming sponge with `Qsag.absorbPadded` and
`Qsag.padForRate`, for inputs of any length and any split into `absorb` calls.

`SpongeAbsorbed sp msg` says the extracted sponge is absorbing and has consumed exactly `msg`.
A fresh sponge has absorbed `[]`; `absorb` appends its argument; `finalize` leaves the state
`Qsag.absorbPadded (Qsag.padForRate msg suffix)`. `SpongeAbsorbed.canonical` restates the
relation without existentials.
-/

public section
namespace qsag_verified.proofs
open Aeneas Aeneas.Std Result ControlFlow qsag_verified
set_option maxRecDepth 4096

/-- Byte view of an extracted `u8` list. -/
@[expose] def u8Bytes (xs : List Std.U8) : List UInt8 := xs.map (fun b => UInt8.ofBitVec b.bv)

theorem u8Bytes_length (xs : List Std.U8) : (u8Bytes xs).length = xs.length :=
  List.length_map _

theorem u8Bytes_getD : ∀ (l : List Std.U8) (i : Nat),
    (u8Bytes l).getD i 0 = UInt8.ofBitVec (l.getD i 0#u8).bv
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, i + 1 => u8Bytes_getD xs i

/-! ## List helpers -/

private theorem getD_set {α : Type} (l : List α) (i j : Nat) (v d : α) (hi : i < l.length) :
    (l.set i v).getD j d = if j = i then v else l.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : j = i
  · subst h; simp [hi]
  · have h' : ¬ i = j := fun e => h e.symm
    simp [h, h']

private theorem set_eq_take_cons_drop {α : Type} : ∀ (l : List α) (i : Nat) (v : α),
    i < l.length → l.set i v = l.take i ++ v :: l.drop (i + 1)
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _, _ => rfl
  | x :: xs, i + 1, v, h => by
    simp only [List.set_cons_succ, List.take_succ_cons, List.drop_succ_cons, List.cons_append]
    rw [set_eq_take_cons_drop xs i v (Nat.lt_of_succ_lt_succ h)]

private theorem drop_all {α : Type} : ∀ (l : List α) (n : Nat), l.length ≤ n → l.drop n = []
  | [], _, _ => List.drop_nil
  | _ :: _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: xs, n + 1, h => drop_all xs n (Nat.le_of_succ_le_succ h)

private theorem getD_append_at {α : Type} (A : List α) (x d : α) (t : List α) (n : Nat)
    (h : A.length = n) : (A ++ x :: t).getD n d = x := by
  subst h
  induction A with
  | nil => rfl
  | cons a A ih => exact ih

private theorem set_append_at {α : Type} (A : List α) (x y : α) (t : List α) (n : Nat)
    (h : A.length = n) : (A ++ x :: t).set n y = A ++ y :: t := by
  subst h
  induction A with
  | nil => rfl
  | cons a A ih =>
    simp only [List.cons_append, List.length_cons, List.set_cons_succ]
    rw [ih]

private theorem take_append_at {α : Type} (A : List α) (b : α) (D : List α) (n : Nat)
    (h : A.length = n) : (A ++ b :: D).take (n + 1) = A ++ [b] := by
  subst h
  induction A with
  | nil => rfl
  | cons a A ih =>
    simp only [List.cons_append, List.length_cons, List.take_succ_cons]
    rw [ih]

private theorem take_succ_map {α β : Type} (f : α → β) : ∀ (l : List α) (n : Nat)
    (h : n < l.length), (l.map f).take (n + 1) = (l.map f).take n ++ [f (l[n]'h)]
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | x :: xs, n + 1, h => by
    have ih := take_succ_map f xs n (Nat.lt_of_succ_lt_succ h)
    simp only [List.map_cons, List.take_succ_cons, List.cons_append, List.getElem_cons_succ]
    rw [ih]

private theorem u8Bytes_take_succ (l : List Std.U8) (n : Nat) (h : n < l.length) :
    (u8Bytes l).take (n + 1) = (u8Bytes l).take n ++ [UInt8.ofBitVec (l[n]'h).bv] :=
  take_succ_map _ l n h

private theorem u8Bytes_set (l : List Std.U8) (i : Nat) (v : Std.U8) (h : i < l.length) :
    u8Bytes (l.set i v) =
      (u8Bytes l).take i ++ UInt8.ofBitVec v.bv :: (u8Bytes l).drop (i + 1) := by
  rw [set_eq_take_cons_drop l i v h]
  simp only [u8Bytes, List.map_append, List.map_cons, List.map_take, List.map_drop]

private theorem array_update_eq {α : Type} {n : Std.Usize} (a : Array α n) (i : Std.Usize)
    (v : α) (b : Array α n) (hi : i.val < n.val) (hb : b.val = a.val.set i.val v) :
    Array.update a i v = .ok b := by
  have hlt : i.val < a.val.length := by rw [a.property]; exact hi
  have h0 : Array.update a i v =
      .ok ⟨a.val.set i.val v, by rw [List.length_set]; exact a.property⟩ := dite_eq_left hlt
  rw [h0]
  exact congrArg Result.ok (Std.Array.ext hb.symm)

/-! ## Rate-block XOR -/

private theorem shl8 (d : Std.U64) : (d <<< 8#i32 : Result Std.U64) = .ok ⟨d.bv <<< 8⟩ := rfl
private theorem shl16 (d : Std.U64) : (d <<< 16#i32 : Result Std.U64) = .ok ⟨d.bv <<< 16⟩ := rfl
private theorem shl24 (d : Std.U64) : (d <<< 24#i32 : Result Std.U64) = .ok ⟨d.bv <<< 24⟩ := rfl
private theorem shl32 (d : Std.U64) : (d <<< 32#i32 : Result Std.U64) = .ok ⟨d.bv <<< 32⟩ := rfl
private theorem shl40 (d : Std.U64) : (d <<< 40#i32 : Result Std.U64) = .ok ⟨d.bv <<< 40⟩ := rfl
private theorem shl48 (d : Std.U64) : (d <<< 48#i32 : Result Std.U64) = .ok ⟨d.bv <<< 48⟩ := rfl
private theorem shl56 (d : Std.U64) : (d <<< 56#i32 : Result Std.U64) = .ok ⟨d.bv <<< 56⟩ := rfl

private theorem load_index (block : Array Std.U8 136#usize) (off c : Std.Usize) (k : Nat)
    (hc : c.val = k) (h : off.val + k < 136) :
    ∃ j, (off + c : Result Std.Usize) = .ok j ∧
      Array.index_usize block j = .ok (block.val.getD (off.val + k) 0#u8) := by
  obtain ⟨j, hj, vj⟩ := checked_add_val off c (by
    change off.val + c.val < 2 ^ 64
    rw [hc]; exact Nat.lt_trans h (by decide))
  refine ⟨j, hj, ?_⟩
  have hidx := array_index_getD block j 0#u8 (by change j.val < 136; rw [vj, hc]; exact h)
  rw [vj, hc] at hidx
  exact hidx

private theorem load_le_u64_eq (block : Array Std.U8 136#usize) (off : Std.Usize)
    (h : off.val + 7 < 136) :
    keccak.load_le_u64 block off = .ok
      ⟨(UScalar.cast .U64 (block.val.getD off.val 0#u8)).bv |||
        ((UScalar.cast .U64 (block.val.getD (off.val + 1) 0#u8)).bv <<< 8) |||
        ((UScalar.cast .U64 (block.val.getD (off.val + 2) 0#u8)).bv <<< 16) |||
        ((UScalar.cast .U64 (block.val.getD (off.val + 3) 0#u8)).bv <<< 24) |||
        ((UScalar.cast .U64 (block.val.getD (off.val + 4) 0#u8)).bv <<< 32) |||
        ((UScalar.cast .U64 (block.val.getD (off.val + 5) 0#u8)).bv <<< 40) |||
        ((UScalar.cast .U64 (block.val.getD (off.val + 6) 0#u8)).bv <<< 48) |||
        ((UScalar.cast .U64 (block.val.getD (off.val + 7) 0#u8)).bv <<< 56)⟩ := by
  have hv0 := array_index_getD block off 0#u8 (by change off.val < 136; omega)
  obtain ⟨j1, hj1, hv1⟩ := load_index block off 1#usize 1 rfl (by omega)
  obtain ⟨j2, hj2, hv2⟩ := load_index block off 2#usize 2 rfl (by omega)
  obtain ⟨j3, hj3, hv3⟩ := load_index block off 3#usize 3 rfl (by omega)
  obtain ⟨j4, hj4, hv4⟩ := load_index block off 4#usize 4 rfl (by omega)
  obtain ⟨j5, hj5, hv5⟩ := load_index block off 5#usize 5 rfl (by omega)
  obtain ⟨j6, hj6, hv6⟩ := load_index block off 6#usize 6 rfl (by omega)
  obtain ⟨j7, hj7, hv7⟩ := load_index block off 7#usize 7 rfl h
  unfold keccak.load_le_u64
  apply bind_ok_step hv0
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hj1
  apply bind_ok_step hv1
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (shl8 _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hj2
  apply bind_ok_step hv2
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (shl16 _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hj3
  apply bind_ok_step hv3
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (shl24 _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hj4
  apply bind_ok_step hv4
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (shl32 _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hj5
  apply bind_ok_step hv5
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (shl40 _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hj6
  apply bind_ok_step hv6
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (shl48 _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hj7
  apply bind_ok_step hv7
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (shl56 _)
  rfl

/-- The extracted little-endian lane load is `Qsag.loadLe64` on the same bytes. -/
theorem load_le_u64_refines (block : Array Std.U8 136#usize) (off : Std.Usize) (k : Nat)
    (hk : k < 17) (hoff : off.val = 8 * k) :
    keccak.load_le_u64 block off =
      .ok ⟨(Qsag.loadLe64 (u8Bytes block.val) k).toBitVec⟩ := by
  rw [load_le_u64_eq block off (by omega)]
  simp only [Qsag.loadLe64_eq, u8Bytes_getD, hoff]
  rfl

private def XorInv (state : Array Std.U64 25#usize) (block : Array Std.U8 136#usize)
    (a : Array Std.U64 25#usize) (n : Nat) : Prop :=
  ∀ j, a.val.getD j 0#u64 =
    if j < n then
      state.val.getD j 0#u64 ^^^ (⟨(Qsag.loadLe64 (u8Bytes block.val) j).toBitVec⟩ : Std.U64)
    else state.val.getD j 0#u64

/-- The extracted rate-block XOR is `Qsag.xorRate136` on every state and block. -/
theorem xor_rate_block_refines (state : Array Std.U64 25#usize)
    (block : Array Std.U8 136#usize) :
    keccak.xor_rate_block state block =
      .ok (keccakArrayOfState
        (Qsag.xorRate136 (keccakStateOfArray state) (u8Bytes block.val))) := by
  let body := fun (a, i) => keccak.xor_rate_block_loop.body block a i
  let P := fun (n : Nat) (x : Array Std.U64 25#usize × Std.Usize) =>
    x.2.val + n = 17 ∧ XorInv state block x.1 x.2.val
  let Q := fun (a : Array Std.U64 25#usize) => XorInv state block a 17
  have hz : ∀ x, P 0 x → ∃ y, body x = .ok (.done y) ∧ Q y := by
    rintro ⟨a, i⟩ ⟨hi, hinv⟩
    change i.val + 0 = 17 at hi
    change XorInv state block a i.val at hinv
    have h17 : i.val = 17 := by omega
    have hn : ¬ i < keccak.SHAKE256_RATE_LANES := by
      unfold keccak.SHAKE256_RATE_LANES
      change ¬ i.val < 17
      omega
    refine ⟨a, by simp only [body, keccak.xor_rate_block_loop.body, hn, ite_false], ?_⟩
    change XorInv state block a 17
    rw [h17] at hinv
    exact hinv
  have step : ∀ n x, P (n + 1) x → ∃ x', body x = .ok (.cont x') ∧ P n x' := by
    rintro n ⟨a, i⟩ ⟨hi, hinv⟩
    change i.val + (n + 1) = 17 at hi
    change XorInv state block a i.val at hinv
    have hi17 : i.val < 17 := by omega
    have hlt : i < keccak.SHAKE256_RATE_LANES := by
      unfold keccak.SHAKE256_RATE_LANES
      change i.val < 17
      exact hi17
    obtain ⟨off, hoff, voff⟩ := checked_mul_val 8#usize i (by
      change 8 * i.val < 2 ^ 64
      exact Nat.lt_trans (Nat.mul_lt_mul_of_pos_left hi17 (by decide : 0 < 8)) (by decide))
    change off.val = 8 * i.val at voff
    have hv := load_le_u64_refines block off i.val hi17 voff
    have hlane := array_index_getD a i 0#u64 (by change i.val < 25; omega)
    have hal : i.val < a.val.length := by
      have := a.property
      change a.val.length = 25 at this
      omega
    let a' : Array Std.U64 25#usize :=
      ⟨a.val.set i.val (a.val.getD i.val 0#u64 ^^^
          (⟨(Qsag.loadLe64 (u8Bytes block.val) i.val).toBitVec⟩ : Std.U64)),
        by rw [List.length_set]; exact a.property⟩
    have ha' : Array.update a i (a.val.getD i.val 0#u64 ^^^
        (⟨(Qsag.loadLe64 (u8Bytes block.val) i.val).toBitVec⟩ : Std.U64)) = .ok a' :=
      dite_eq_left hal
    obtain ⟨i', hi', vi'⟩ := checked_add_val i 1#usize (by
      change i.val + 1 < 2 ^ 64
      exact Nat.lt_trans (Nat.succ_lt_succ hi17) (by decide))
    change i'.val = i.val + 1 at vi'
    refine ⟨(a', i'), ?_, ?_, ?_⟩
    · simp only [body, keccak.xor_rate_block_loop.body, hlt, ite_true, hoff,
        hv, hlane, ha', hi', bind_eq_result_bind, result_bind_ok, lift_eq_ok]
    · change i'.val + n = 17
      omega
    · change XorInv state block a' i'.val
      intro j
      rw [vi']
      change (a.val.set i.val _).getD j 0#u64 = _
      rw [getD_set _ _ _ _ _ hal]
      have hj := hinv j
      by_cases hji : j = i.val
      · subst hji
        rw [ite_eq_left rfl, ite_eq_left (Nat.lt_succ_self _), hj, ite_eq_right (Nat.lt_irrefl _)]
      · rw [ite_eq_right hji, hj]
        by_cases hlt' : j < i.val
        · rw [ite_eq_left hlt', ite_eq_left (Nat.lt_succ_of_lt hlt')]
        · have hge : ¬ j < i.val + 1 := by omega
          rw [ite_eq_right hlt', ite_eq_right hge]
  obtain ⟨out, hout, hQ⟩ := loopFuel_total_rank body P Q hz step 17 (state, 0#usize)
    ⟨rfl, by
      change XorInv state block state 0
      intro j
      rw [ite_eq_right (Nat.not_lt_zero j)]⟩
  have hrun : keccak.xor_rate_block state block = .ok out := by
    unfold keccak.xor_rate_block keccak.xor_rate_block_loop
    exact loop_ok_of_loopFuel (fuel := 18) (by decide) hout
  have key : keccakStateOfArray out =
      Qsag.xorRate136 (keccakStateOfArray state) (u8Bytes block.val) := by
    have h0 := hQ 0; have h1 := hQ 1; have h2 := hQ 2; have h3 := hQ 3; have h4 := hQ 4
    have h5 := hQ 5; have h6 := hQ 6; have h7 := hQ 7; have h8 := hQ 8; have h9 := hQ 9
    have h10 := hQ 10; have h11 := hQ 11; have h12 := hQ 12; have h13 := hQ 13
    have h14 := hQ 14; have h15 := hQ 15; have h16 := hQ 16; have h17 := hQ 17
    have h18 := hQ 18; have h19 := hQ 19; have h20 := hQ 20; have h21 := hQ 21
    have h22 := hQ 22; have h23 := hQ 23; have h24 := hQ 24
    simp only [keccakStateOfArray, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
      h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, Qsag.xorRate136_eq]
    rfl
  rw [hrun, ← key, keccakArrayOfState_roundtrip]

/-! ## Block absorption and padding on the specification side -/

/-- Absorbing one more full block after `q` full blocks. -/
theorem absorbBlocks_append_block : ∀ (q : Nat) (s : Qsag.KState) (full blk : List UInt8),
    full.length = 136 * q → blk.length = 136 →
    Qsag.absorbBlocks (q + 1) s (full ++ blk) =
      Qsag.keccakF1600 (Qsag.xorRate136 (Qsag.absorbBlocks q s full) blk)
  | 0, s, full, blk, hf, hb => by
    have hnil : full = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    have ht : blk.take 136 = blk := List.take_of_length_le (by omega)
    rw [Qsag.absorbBlocks_succ 0 s ([] ++ blk)]
    simp only [Qsag.absorbBlocks_zero, Qsag.shake256RateBytes_eq, List.nil_append, ht]
  | q + 1, s, full, blk, hf, hb => by
    have htake : (full ++ blk).take 136 = full.take 136 :=
      List.take_append_of_le_length (by omega)
    have hdrop : (full ++ blk).drop 136 = full.drop 136 ++ blk :=
      List.drop_append_of_le_length (by omega)
    have hlen : (full.drop 136).length = 136 * q := by rw [List.length_drop]; omega
    rw [Qsag.absorbBlocks_succ (q + 1) s (full ++ blk), Qsag.absorbBlocks_succ q s full,
      Qsag.shake256RateBytes_eq, htake, hdrop,
      absorbBlocks_append_block q _ (full.drop 136) blk hlen hb]

/-- `q` full blocks never read past the first `136 * q` bytes. -/
theorem absorbBlocks_append_right : ∀ (q : Nat) (s : Qsag.KState) (full tail : List UInt8),
    full.length = 136 * q →
    Qsag.absorbBlocks q s (full ++ tail) = Qsag.absorbBlocks q s full
  | 0, s, _, _, _ => by simp only [Qsag.absorbBlocks_zero]
  | q + 1, s, full, tail, hf => by
    have htake : (full ++ tail).take 136 = full.take 136 :=
      List.take_append_of_le_length (by omega)
    have hdrop : (full ++ tail).drop 136 = full.drop 136 ++ tail :=
      List.drop_append_of_le_length (by omega)
    have hlen : (full.drop 136).length = 136 * q := by rw [List.length_drop]; omega
    rw [Qsag.absorbBlocks_succ q s (full ++ tail), Qsag.absorbBlocks_succ q s full,
      Qsag.shake256RateBytes_eq, htake, hdrop,
      absorbBlocks_append_right q _ (full.drop 136) tail hlen]

/-- Final rate block of multi-rate padding with a domain suffix, for fewer than 136
pending bytes. -/
@[expose] def spongeLastBlock (pending : List UInt8) (suffix : UInt8) : List UInt8 :=
  if pending.length = 135 then pending ++ [suffix ^^^ 0x80]
  else pending ++ [suffix] ++ List.replicate (134 - pending.length) 0 ++ [0x80]

theorem spongeLastBlock_length (pending : List UInt8) (suffix : UInt8)
    (hp : pending.length < 136) : (spongeLastBlock pending suffix).length = 136 := by
  unfold spongeLastBlock
  by_cases h : pending.length = 135
  · rw [ite_eq_left h]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · rw [ite_eq_right h]
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    omega

/-- `Qsag.padForRate` only touches the last, partial block. -/
theorem padForRate_split (full pending : List UInt8) (q : Nat) (suffix : UInt8)
    (hf : full.length = 136 * q) (hp : pending.length < 136) :
    Qsag.padForRate (full ++ pending) suffix = full ++ spongeLastBlock pending suffix := by
  have hmod : (full ++ pending).length % 136 = pending.length := by
    rw [List.length_append, hf]; omega
  rw [Qsag.padForRate_eq]
  simp only [Qsag.shake256RateBytes_eq, hmod, spongeLastBlock]
  by_cases h : pending.length = 135
  · have h1 : 136 - pending.length = 1 := by omega
    rw [ite_eq_left h1, ite_eq_left h, List.append_assoc]
  · have h1 : ¬ (136 - pending.length = 1) := by omega
    have h2 : 136 - pending.length - 2 = 134 - pending.length := by omega
    rw [ite_eq_right h1, ite_eq_right h, h2]
    simp only [List.append_assoc]

theorem absorbPadded_padForRate (full pending : List UInt8) (q : Nat) (suffix : UInt8)
    (hf : full.length = 136 * q) (hp : pending.length < 136) :
    Qsag.absorbPadded (Qsag.padForRate (full ++ pending) suffix) =
      Qsag.keccakF1600 (Qsag.xorRate136 (Qsag.absorbBlocks q Qsag.zeroKState full)
        (spongeLastBlock pending suffix)) := by
  have hlast := spongeLastBlock_length pending suffix hp
  have hlen : (full ++ spongeLastBlock pending suffix).length / 136 = q + 1 := by
    rw [List.length_append, hf, hlast]; omega
  rw [padForRate_split full pending q suffix hf hp, Qsag.absorbPadded_eq,
    Qsag.shake256RateBytes_eq, hlen]
  exact absorbBlocks_append_block q _ full _ hf hlast

/-! ## Absorb -/

/-- State, buffer and fill of an absorbing sponge that has consumed exactly `acc`: `full`
went through the permutation in `q` rate blocks and `pending` is buffered. -/
def SpongeAbsorbInv (acc : List UInt8) (a : Array Std.U64 25#usize)
    (buf : Array Std.U8 136#usize) (i : Nat) : Prop :=
  ∃ (full pending : List UInt8) (q : Nat),
    acc = full ++ pending ∧ full.length = 136 * q ∧ pending.length = i ∧ i < 136 ∧
    keccakStateOfArray a = Qsag.absorbBlocks q Qsag.zeroKState full ∧
    (u8Bytes buf.val).take i = pending

/-- The sponge is absorbing and has consumed exactly `msg`. -/
def SpongeAbsorbed (sp : keccak.Shake256Sponge) (msg : List UInt8) : Prop :=
  sp.squeezing = false ∧ SpongeAbsorbInv msg sp.state sp.buf sp.buf_len.val

/-- Existential-free reading of `SpongeAbsorbed`. -/
theorem SpongeAbsorbed.canonical {sp : keccak.Shake256Sponge} {msg : List UInt8}
    (h : SpongeAbsorbed sp msg) :
    sp.squeezing = false ∧ sp.buf_len.val = msg.length % 136 ∧
      keccakStateOfArray sp.state =
        Qsag.absorbBlocks (msg.length / 136) Qsag.zeroKState msg ∧
      (u8Bytes sp.buf.val).take sp.buf_len.val = msg.drop (136 * (msg.length / 136)) := by
  obtain ⟨hsq, full, pending, q, hmsg, hfull, hpl, hi, hstate, hbuf⟩ := h
  have hlen : msg.length = 136 * q + sp.buf_len.val := by
    rw [hmsg, List.length_append, hfull, hpl]
  have hdiv : msg.length / 136 = q := by omega
  have hmod : msg.length % 136 = sp.buf_len.val := by omega
  refine ⟨hsq, hmod.symm, ?_, ?_⟩
  · rw [hdiv, hstate, hmsg, absorbBlocks_append_right q _ full pending hfull]
  · have hd : (full ++ pending).drop (136 * q) = full.drop (136 * q) ++ pending :=
      List.drop_append_of_le_length (by omega)
    rw [hdiv, hbuf, hmsg, hd, drop_all full (136 * q) (by omega), List.nil_append]

/-- No squeezing sponge is absorbing. -/
theorem tooth_squeezing_not_absorbed (sp : keccak.Shake256Sponge) (msg : List UInt8)
    (hs : sp.squeezing = true) : ¬ SpongeAbsorbed sp msg := by
  rintro ⟨hsq, _⟩
  rw [hs] at hsq
  cases hsq

private theorem absorb_step (data : Slice Std.U8) (acc : List UInt8)
    (a : Array Std.U64 25#usize) (buf : Array Std.U8 136#usize) (i pos : Std.Usize)
    (hp : pos.val < data.val.length) (hinv : SpongeAbsorbInv acc a buf i.val) :
    ∃ a' buf' i' pos',
      keccak.Shake256Sponge.absorb_loop.body data a buf i pos =
        .ok (.cont (a', buf', i', pos')) ∧
      pos'.val = pos.val + 1 ∧
      SpongeAbsorbInv (acc ++ [UInt8.ofBitVec (data.val[pos.val]'hp).bv]) a' buf' i'.val := by
  obtain ⟨full, pending, q, hacc, hfull, hpl, hi, hstate, hbuf⟩ := hinv
  obtain ⟨buf', i', pos', hb', vi', vp', hbody⟩ := sponge_absorb_byte a buf i pos data hi hp
  have hlen : i.val < buf.val.length := by
    have := buf.property
    change buf.val.length = 136 at this
    omega
  have hbl : (u8Bytes buf.val).length = 136 := by
    rw [u8Bytes_length]; exact buf.property
  have hbytes : u8Bytes buf'.val =
      pending ++ UInt8.ofBitVec (data.val[pos.val]'hp).bv ::
        (u8Bytes buf.val).drop (i.val + 1) := by
    rw [hb', u8Bytes_set _ _ _ hlen, hbuf]
  by_cases he : i.val + 1 = 136
  · have hi' : i' = 136#usize := UScalar.eq_of_val_eq (by rw [vi']; exact he)
    have hfullblk : u8Bytes buf'.val =
        pending ++ [UInt8.ofBitVec (data.val[pos.val]'hp).bv] := by
      rw [hbytes, drop_all _ _ (by omega)]
    have hblk : (pending ++ [UInt8.ofBitVec (data.val[pos.val]'hp).bv]).length = 136 := by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    simp only [hi', ite_true, bind_eq_result_bind] at hbody
    rw [xor_rate_block_refines, result_bind_ok, keccakStateOfArray_roundtrip] at hbody
    refine ⟨_, buf', 0#usize, pos', hbody, vp',
      full ++ (pending ++ [UInt8.ofBitVec (data.val[pos.val]'hp).bv]), [], q + 1,
      ?_, ?_, rfl, by decide, ?_, rfl⟩
    · rw [hacc, List.append_nil, List.append_assoc]
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · rw [keccakStateOfArray_roundtrip, absorbBlocks_append_block q _ full _ hfull hblk,
        hstate, hfullblk]
  · have hne : ¬ i' = 136#usize := by
      intro e
      apply he
      rw [← vi', e]
      rfl
    rw [ite_eq_right hne] at hbody
    refine ⟨a, buf', i', pos', hbody, vp', full,
      pending ++ [UInt8.ofBitVec (data.val[pos.val]'hp).bv], q, ?_, hfull, ?_, ?_, hstate, ?_⟩
    · rw [hacc, List.append_assoc]
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · omega
    · rw [hbytes, vi']
      exact take_append_at _ _ _ _ hpl

/-- `absorb` appends its whole argument to the absorbed message, for any length and any
fill of the rate buffer. -/
theorem sponge_absorb_refines (sp : keccak.Shake256Sponge) (data : Slice Std.U8)
    (msg : List UInt8) (h : SpongeAbsorbed sp msg) :
    ∃ sp', keccak.Shake256Sponge.absorb sp data = .ok sp' ∧
      SpongeAbsorbed sp' (msg ++ u8Bytes data.val) ∧ sp'.suffix = sp.suffix := by
  obtain ⟨hsq, hinv⟩ := h
  let body := fun (a, buf, i, pos) => keccak.Shake256Sponge.absorb_loop.body data a buf i pos
  let P := fun (n : Nat)
      (x : Array Std.U64 25#usize × Array Std.U8 136#usize × Std.Usize × Std.Usize) =>
    x.2.2.2.val + n = data.val.length ∧
      SpongeAbsorbInv (msg ++ (u8Bytes data.val).take x.2.2.2.val) x.1 x.2.1 x.2.2.1.val
  let Q := fun (y : Array Std.U64 25#usize × Array Std.U8 136#usize × Std.Usize) =>
    SpongeAbsorbInv (msg ++ u8Bytes data.val) y.1 y.2.1 y.2.2.val
  have hz : ∀ x, P 0 x → ∃ y, body x = .ok (.done y) ∧ Q y := by
    rintro ⟨a, buf, i, pos⟩ ⟨hp, hI⟩
    change pos.val + 0 = data.val.length at hp
    change SpongeAbsorbInv (msg ++ (u8Bytes data.val).take pos.val) a buf i.val at hI
    have he : ¬ pos < Slice.len data := by
      change ¬ pos.val < (Slice.len data).val
      rw [Slice.len_val]; omega
    refine ⟨(a, buf, i),
      by simp only [body, keccak.Shake256Sponge.absorb_loop.body, he, ite_false], ?_⟩
    change SpongeAbsorbInv (msg ++ u8Bytes data.val) a buf i.val
    have ht : (u8Bytes data.val).take pos.val = u8Bytes data.val :=
      List.take_of_length_le (by rw [u8Bytes_length]; omega)
    rw [ht] at hI
    exact hI
  have step : ∀ n x, P (n + 1) x → ∃ x', body x = .ok (.cont x') ∧ P n x' := by
    rintro n ⟨a, buf, i, pos⟩ ⟨hp, hI⟩
    change pos.val + (n + 1) = data.val.length at hp
    change SpongeAbsorbInv (msg ++ (u8Bytes data.val).take pos.val) a buf i.val at hI
    have hpl : pos.val < data.val.length := by omega
    obtain ⟨a', buf', i', pos', hbody, vp', hI'⟩ := absorb_step data _ a buf i pos hpl hI
    refine ⟨(a', buf', i', pos'), hbody, ?_, ?_⟩
    · change pos'.val + n = data.val.length
      omega
    · change SpongeAbsorbInv (msg ++ (u8Bytes data.val).take pos'.val) a' buf' i'.val
      rw [vp', u8Bytes_take_succ _ _ hpl, ← List.append_assoc]
      exact hI'
  obtain ⟨⟨a, buf, i⟩, hloop, hQ⟩ := loopFuel_total_rank body P Q hz step data.val.length
    (sp.state, sp.buf, sp.buf_len, 0#usize) ⟨Nat.zero_add _, by
      change SpongeAbsorbInv (msg ++ (u8Bytes data.val).take 0) sp.state sp.buf sp.buf_len.val
      rw [List.take_zero, List.append_nil]
      exact hinv⟩
  have hactual : keccak.Shake256Sponge.absorb_loop sp.state sp.buf sp.buf_len data 0#usize =
      .ok (a, buf, i) := by
    unfold keccak.Shake256Sponge.absorb_loop
    apply loop_ok_of_loopFuel (fuel := data.val.length + 1)
    · simpa only [Slice.len_val] using usize_lt_loopMaxFuel (Slice.len data)
    · exact hloop
  refine ⟨{ sp with state := a, buf := buf, buf_len := i }, ?_, And.intro hsq hQ, rfl⟩
  simp only [keccak.Shake256Sponge.absorb, massert_not_of_eq_false hsq,
    hactual, bind_eq_result_bind, result_bind_ok]

/-- A fresh SHAKE256 sponge has absorbed nothing and carries suffix `0x1f`. -/
theorem sponge_new_shake256_absorbed :
    ∃ sp, keccak.Shake256Sponge.new_shake256 = .ok sp ∧ SpongeAbsorbed sp [] ∧
      sp.suffix = 31#u8 := by
  refine ⟨_, rfl, And.intro rfl ⟨[], [], 0, rfl, rfl, rfl, by decide, ?_, rfl⟩, rfl⟩
  rw [Qsag.absorbBlocks_zero, Qsag.zeroKState_eq]
  rfl

/-- Any sequence of `absorb` calls. -/
def spongeAbsorbAll (sp : keccak.Shake256Sponge) :
    List (Slice Std.U8) → Result keccak.Shake256Sponge
  | [] => .ok sp
  | d :: ds => Result.bind (keccak.Shake256Sponge.absorb sp d) fun sp' => spongeAbsorbAll sp' ds

/-- Absorption depends only on the concatenated input, not on how it is split into calls. -/
theorem sponge_absorb_all_refines : ∀ (chunks : List (Slice Std.U8))
    (sp : keccak.Shake256Sponge) (msg : List UInt8), SpongeAbsorbed sp msg →
    ∃ sp', spongeAbsorbAll sp chunks = .ok sp' ∧
      SpongeAbsorbed sp' (msg ++ (chunks.map fun d => u8Bytes d.val).flatten) ∧
      sp'.suffix = sp.suffix
  | [], sp, msg, h => ⟨sp, rfl, by
      simp only [List.map_nil, List.flatten_nil, List.append_nil]; exact h, rfl⟩
  | d :: ds, sp, msg, h => by
    obtain ⟨sp1, h1, habs1, hs1⟩ := sponge_absorb_refines sp d msg h
    obtain ⟨sp2, h2, habs2, hs2⟩ := sponge_absorb_all_refines ds sp1 _ habs1
    refine ⟨sp2, ?_, ?_, hs2.trans hs1⟩
    · simp only [spongeAbsorbAll, h1, result_bind_ok, h2]
    · simp only [List.map_cons, List.flatten_cons, ← List.append_assoc]
      exact habs2

/-! ## Finalize -/

private theorem finalize_loop_eq (buf : Array Std.U8 136#usize) (start : Std.Usize)
    (hs : start.val ≤ 136) :
    ∃ out, keccak.Shake256Sponge.finalize_loop buf start = .ok out ∧
      out.val = buf.val.take start.val ++ List.replicate (136 - start.val) 0#u8 := by
  have hbl : buf.val.length = 136 := buf.property
  let body := fun (a, i) => keccak.Shake256Sponge.finalize_loop.body a i
  let P := fun (n : Nat) (x : Array Std.U8 136#usize × Std.Usize) =>
    x.2.val + n = 136 ∧ start.val ≤ x.2.val ∧
      x.1.val = buf.val.take start.val ++ List.replicate (x.2.val - start.val) 0#u8 ++
        buf.val.drop x.2.val
  let Q := fun (a : Array Std.U8 136#usize) =>
    a.val = buf.val.take start.val ++ List.replicate (136 - start.val) 0#u8
  have hz : ∀ x, P 0 x → ∃ y, body x = .ok (.done y) ∧ Q y := by
    rintro ⟨a, i⟩ ⟨hi, _, ha⟩
    change i.val + 0 = 136 at hi
    change a.val = buf.val.take start.val ++ List.replicate (i.val - start.val) 0#u8 ++
      buf.val.drop i.val at ha
    have h136 : i.val = 136 := by omega
    have hn : ¬ i < keccak.SHAKE256_RATE_BYTES := by
      unfold keccak.SHAKE256_RATE_BYTES
      change ¬ i.val < 136
      omega
    refine ⟨a, by simp only [body, keccak.Shake256Sponge.finalize_loop.body, hn, ite_false], ?_⟩
    change a.val = buf.val.take start.val ++ List.replicate (136 - start.val) 0#u8
    rw [ha, h136, drop_all buf.val 136 (by omega), List.append_nil]
  have step : ∀ n x, P (n + 1) x → ∃ x', body x = .ok (.cont x') ∧ P n x' := by
    rintro n ⟨a, i⟩ ⟨hi, hsi, ha⟩
    change i.val + (n + 1) = 136 at hi
    change start.val ≤ i.val at hsi
    change a.val = buf.val.take start.val ++ List.replicate (i.val - start.val) 0#u8 ++
      buf.val.drop i.val at ha
    have hi136 : i.val < 136 := by omega
    have hlt : i < keccak.SHAKE256_RATE_BYTES := by
      unfold keccak.SHAKE256_RATE_BYTES
      change i.val < 136
      exact hi136
    have hAlen : (buf.val.take start.val ++ List.replicate (i.val - start.val) 0#u8).length =
        i.val := by
      simp only [List.length_append, List.length_take, List.length_replicate]; omega
    have hdrop : buf.val.drop i.val = buf.val[i.val]'(by omega) :: buf.val.drop (i.val + 1) :=
      List.drop_eq_getElem_cons (by omega)
    have hsucc : i.val + 1 - start.val = (i.val - start.val) + 1 := by omega
    let a' : Array Std.U8 136#usize :=
      ⟨a.val.set i.val 0#u8, by rw [List.length_set]; exact a.property⟩
    have ha' : Array.update a i 0#u8 = .ok a' := array_update_eq a i 0#u8 a' hi136 rfl
    obtain ⟨i', hi', vi'⟩ := checked_add_val i 1#usize (by
      change i.val + 1 < 2 ^ 64
      exact Nat.lt_trans (Nat.succ_lt_succ hi136) (by decide))
    change i'.val = i.val + 1 at vi'
    refine ⟨(a', i'), ?_, ?_, ?_, ?_⟩
    · simp only [body, keccak.Shake256Sponge.finalize_loop.body, hlt, ite_true,
        ha', hi', bind_eq_result_bind, result_bind_ok]
    · change i'.val + n = 136
      omega
    · change start.val ≤ i'.val
      omega
    · change a.val.set i.val 0#u8 =
        buf.val.take start.val ++ List.replicate (i'.val - start.val) 0#u8 ++
          buf.val.drop i'.val
      rw [ha, hdrop, set_append_at _ _ _ _ _ hAlen, vi', hsucc, List.replicate_succ']
      simp only [List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨out, hout, hQ⟩ := loopFuel_total_rank body P Q hz step (136 - start.val)
    (buf, start) ⟨by change start.val + (136 - start.val) = 136; omega, Nat.le_refl _, by
      change buf.val = buf.val.take start.val ++
        List.replicate (start.val - start.val) 0#u8 ++ buf.val.drop start.val
      rw [Nat.sub_self]
      simp only [List.replicate_zero, List.append_nil, List.take_append_drop]⟩
  refine ⟨out, ?_, hQ⟩
  unfold keccak.Shake256Sponge.finalize_loop
  apply loop_ok_of_loopFuel (fuel := 136 - start.val + 1)
  · apply Nat.le_trans (show 136 - start.val + 1 ≤ 137 from
      Nat.add_le_add_right (Nat.sub_le _ _) 1)
    decide
  · exact hout

private theorem finalize_buffer (buf : Array Std.U8 136#usize) (i : Std.Usize) (sfx : Std.U8)
    (hi : i.val < 136) :
    ∃ (a1 a2 a3 : Array Std.U8 136#usize) (v1 v2 : Std.U8),
      keccak.Shake256Sponge.finalize_loop buf i = .ok a1 ∧
      Array.index_usize a1 i = .ok v1 ∧ Array.update a1 i (v1 ^^^ sfx) = .ok a2 ∧
      Array.index_usize a2 135#usize = .ok v2 ∧
      Array.update a2 135#usize (v2 ^^^ 128#u8) = .ok a3 ∧
      u8Bytes a3.val =
        spongeLastBlock ((u8Bytes buf.val).take i.val) (UInt8.ofBitVec sfx.bv) := by
  have hbl : buf.val.length = 136 := buf.property
  obtain ⟨a1, hloop, ha1⟩ := finalize_loop_eq buf i (Nat.le_of_lt hi)
  have hPlen : (buf.val.take i.val).length = i.val := by rw [List.length_take]; omega
  have hPlen' : ((u8Bytes buf.val).take i.val).length = i.val := by
    rw [List.length_take, u8Bytes_length]; omega
  have hrep : 136 - i.val = (135 - i.val) + 1 := by omega
  rw [hrep, List.replicate_succ] at ha1
  have hidx1 : Array.index_usize a1 i = .ok 0#u8 := by
    have hget := array_index_getD a1 i 0#u8 hi
    rw [ha1, getD_append_at _ _ _ _ _ hPlen] at hget
    exact hget
  by_cases h135 : i.val = 135
  · have hzero : 135 - i.val = 0 := by omega
    rw [hzero, List.replicate_zero] at ha1
    let a2 : Array Std.U8 136#usize := ⟨buf.val.take i.val ++ [sfx], by
      change (buf.val.take i.val ++ [sfx]).length = 136
      simp only [List.length_append, List.length_cons, List.length_nil, hPlen]; omega⟩
    have hupd1 : Array.update a1 i (0#u8 ^^^ sfx) = .ok a2 :=
      array_update_eq a1 i _ a2 hi (by
        change buf.val.take i.val ++ [sfx] = a1.val.set i.val (0#u8 ^^^ sfx)
        rw [ha1, set_append_at _ _ _ _ _ hPlen, u8_zero_xor])
    have hidx2 : Array.index_usize a2 135#usize = .ok sfx := by
      have hget := array_index_getD a2 135#usize 0#u8 (by decide)
      change Array.index_usize a2 135#usize =
        .ok ((buf.val.take i.val ++ [sfx]).getD 135 0#u8) at hget
      rw [getD_append_at _ _ _ _ _ (hPlen.trans h135)] at hget
      exact hget
    let a3 : Array Std.U8 136#usize := ⟨buf.val.take i.val ++ [sfx ^^^ 128#u8], by
      change (buf.val.take i.val ++ [sfx ^^^ 128#u8]).length = 136
      simp only [List.length_append, List.length_cons, List.length_nil, hPlen]; omega⟩
    have hupd2 : Array.update a2 135#usize (sfx ^^^ 128#u8) = .ok a3 :=
      array_update_eq a2 135#usize _ a3 (by decide) (by
        change buf.val.take i.val ++ [sfx ^^^ 128#u8] =
          (buf.val.take i.val ++ [sfx]).set 135 (sfx ^^^ 128#u8)
        rw [set_append_at _ _ _ _ _ (hPlen.trans h135)])
    refine ⟨a1, a2, a3, 0#u8, sfx, hloop, hidx1, hupd1, hidx2, hupd2, ?_⟩
    change u8Bytes (buf.val.take i.val ++ [sfx ^^^ 128#u8]) = _
    have hlast : ((u8Bytes buf.val).take i.val).length = 135 := hPlen'.trans h135
    unfold spongeLastBlock
    rw [ite_eq_left hlast]
    simp only [u8Bytes, List.map_append, List.map_cons, List.map_nil, List.map_take]
    rfl
  · have hsplit : 135 - i.val = (134 - i.val) + 1 := by omega
    rw [hsplit, List.replicate_succ'] at ha1
    have hA2len : (buf.val.take i.val ++ sfx :: List.replicate (134 - i.val) 0#u8).length =
        135 := by
      simp only [List.length_append, List.length_cons, List.length_replicate, hPlen]; omega
    let a2 : Array Std.U8 136#usize :=
      ⟨(buf.val.take i.val ++ sfx :: List.replicate (134 - i.val) 0#u8) ++ [0#u8], by
        change ((buf.val.take i.val ++ sfx :: List.replicate (134 - i.val) 0#u8) ++
          [0#u8]).length = 136
        rw [List.length_append, hA2len]; rfl⟩
    have hupd1 : Array.update a1 i (0#u8 ^^^ sfx) = .ok a2 :=
      array_update_eq a1 i _ a2 hi (by
        change (buf.val.take i.val ++ sfx :: List.replicate (134 - i.val) 0#u8) ++ [0#u8] =
          a1.val.set i.val (0#u8 ^^^ sfx)
        rw [ha1, set_append_at _ _ _ _ _ hPlen, u8_zero_xor]
        simp only [List.append_assoc, List.cons_append])
    have hidx2 : Array.index_usize a2 135#usize = .ok 0#u8 := by
      have hget := array_index_getD a2 135#usize 0#u8 (by decide)
      change Array.index_usize a2 135#usize =
        .ok (((buf.val.take i.val ++ sfx :: List.replicate (134 - i.val) 0#u8) ++
          [0#u8]).getD 135 0#u8) at hget
      rw [getD_append_at _ _ _ _ _ hA2len] at hget
      exact hget
    let a3 : Array Std.U8 136#usize :=
      ⟨(buf.val.take i.val ++ sfx :: List.replicate (134 - i.val) 0#u8) ++
          [0#u8 ^^^ 128#u8], by
        change ((buf.val.take i.val ++ sfx :: List.replicate (134 - i.val) 0#u8) ++
          [0#u8 ^^^ 128#u8]).length = 136
        rw [List.length_append, hA2len]; rfl⟩
    have hupd2 : Array.update a2 135#usize (0#u8 ^^^ 128#u8) = .ok a3 :=
      array_update_eq a2 135#usize _ a3 (by decide) (by
        change (buf.val.take i.val ++ sfx :: List.replicate (134 - i.val) 0#u8) ++
            [0#u8 ^^^ 128#u8] =
          ((buf.val.take i.val ++ sfx :: List.replicate (134 - i.val) 0#u8) ++
            [0#u8]).set 135 (0#u8 ^^^ 128#u8)
        rw [set_append_at _ _ _ _ _ hA2len])
    refine ⟨a1, a2, a3, 0#u8, 0#u8, hloop, hidx1, hupd1, hidx2, hupd2, ?_⟩
    change u8Bytes ((buf.val.take i.val ++ sfx :: List.replicate (134 - i.val) 0#u8) ++
      [0#u8 ^^^ 128#u8]) = _
    have hlast : ¬ ((u8Bytes buf.val).take i.val).length = 135 := by rw [hPlen']; exact h135
    unfold spongeLastBlock
    rw [ite_eq_right hlast, hPlen']
    simp only [u8Bytes, List.map_append, List.map_cons, List.map_nil, List.map_take,
      List.map_replicate, List.append_assoc, List.cons_append, List.nil_append]
    rfl

/-- `finalize` applies exactly the multi-rate padding of `Qsag.padForRate` with the sponge's
domain suffix and leaves the canonical padded-absorb state, ready to squeeze. -/
theorem sponge_finalize_refines (sp : keccak.Shake256Sponge) (msg : List UInt8)
    (h : SpongeAbsorbed sp msg) :
    ∃ sp', keccak.Shake256Sponge.finalize sp = .ok sp' ∧
      keccakStateOfArray sp'.state =
        Qsag.absorbPadded (Qsag.padForRate msg (UInt8.ofBitVec sp.suffix.bv)) ∧
      sp'.squeezing = true ∧ sp'.squeeze_offset = 0#usize ∧ sp'.suffix = sp.suffix := by
  obtain ⟨hsq, full, pending, q, hmsg, hfull, hpl, hi, hstate, hbuf⟩ := h
  have hlt : ¬ sp.buf_len >= keccak.SHAKE256_RATE_BYTES := by
    unfold keccak.SHAKE256_RATE_BYTES
    change ¬ 136 ≤ sp.buf_len.val
    omega
  obtain ⟨a1, a2, a3, v1, v2, hloop, hidx1, hupd1, hidx2, hupd2, hbytes⟩ :=
    finalize_buffer sp.buf sp.buf_len sp.suffix hi
  have hsub : (keccak.SHAKE256_RATE_BYTES - 1#usize : Result Std.Usize) = .ok 135#usize := by
    unfold keccak.SHAKE256_RATE_BYTES
    rfl
  refine ⟨{ sp with
      state := keccakArrayOfState (Qsag.keccakF1600
        (Qsag.xorRate136 (keccakStateOfArray sp.state) (u8Bytes a3.val))),
      buf := a3, buf_len := sp.buf_len, squeezing := true, squeeze_offset := 0#usize },
    ?_, ?_, rfl, rfl, rfl⟩
  · simp only [keccak.Shake256Sponge.finalize, hsq, Bool.false_eq_true, ite_false, hlt,
      hloop, hidx1, hupd1, hsub, hidx2, hupd2, keccak_f1600_array_refines_qsag,
      bind_eq_result_bind, result_bind_ok, lift_eq_ok]
    rw [xor_rate_block_refines, result_bind_ok, keccakStateOfArray_roundtrip]
  · change keccakStateOfArray (keccakArrayOfState _) = _
    rw [keccakStateOfArray_roundtrip, hmsg,
      absorbPadded_padForRate full pending q _ hfull (by omega), hstate, hbytes, hbuf]

/-- SHAKE256 absorb and pad, end to end: a fresh sponge fed `chunks` in any split and then
finalized holds `Qsag.absorbPadded (Qsag.padForRate input 0x1f)` for the concatenated input. -/
theorem shake256_absorb_pad_refines (chunks : List (Slice Std.U8)) :
    ∃ sp0 sp1 sp2,
      keccak.Shake256Sponge.new_shake256 = .ok sp0 ∧
      spongeAbsorbAll sp0 chunks = .ok sp1 ∧
      keccak.Shake256Sponge.finalize sp1 = .ok sp2 ∧
      keccakStateOfArray sp2.state =
        Qsag.absorbPadded
          (Qsag.padForRate (chunks.map fun d => u8Bytes d.val).flatten 0x1f) ∧
      sp2.squeezing = true ∧ sp2.squeeze_offset = 0#usize := by
  obtain ⟨sp0, h0, habs0, hs0⟩ := sponge_new_shake256_absorbed
  obtain ⟨sp1, h1, habs1, hs1⟩ := sponge_absorb_all_refines chunks sp0 [] habs0
  obtain ⟨sp2, h2, hstate, hsq, hoff, _⟩ := sponge_finalize_refines sp1 _ habs1
  refine ⟨sp0, sp1, sp2, h0, h1, h2, ?_, hsq, hoff⟩
  rw [hstate, hs1, hs0, List.nil_append]
  rfl

/-- `Qsag.shake256Xof` squeezes from exactly the state the extracted sponge holds after
absorbing `chunks` and finalizing. -/
theorem shake256_xof_from_extracted_state (chunks : List (Slice Std.U8)) :
    ∃ sp0 sp1 sp2,
      keccak.Shake256Sponge.new_shake256 = .ok sp0 ∧
      spongeAbsorbAll sp0 chunks = .ok sp1 ∧
      keccak.Shake256Sponge.finalize sp1 = .ok sp2 ∧
      ∀ outLen, Qsag.shake256Xof outLen (chunks.map fun d => u8Bytes d.val).flatten =
        Qsag.squeezeXofAux outLen (keccakStateOfArray sp2.state) := by
  obtain ⟨sp0, sp1, sp2, h0, h1, h2, hstate, _, _⟩ := shake256_absorb_pad_refines chunks
  refine ⟨sp0, sp1, sp2, h0, h1, h2, fun outLen => ?_⟩
  unfold Qsag.shake256Xof
  rw [hstate]

/-- cSHAKE256 absorb and pad for a sponge that has absorbed the SP 800-185 customization
prefix and carries suffix `0x04`: any split of the input, then `finalize`, leaves exactly the
state `Qsag.cshake256Xof` squeezes from. `sponge_new_cshake256_nonempty_absorbed` discharges
the prefix obligation for every nonempty customization. -/
theorem cshake256_absorb_pad_refines (cust : List UInt8) (hc : cust ≠ [])
    (sp0 : keccak.Shake256Sponge)
    (hpre : SpongeAbsorbed sp0 (Qsag.customizationPrefix cust)) (hsfx : sp0.suffix = 4#u8)
    (chunks : List (Slice Std.U8)) :
    ∃ sp1 sp2,
      spongeAbsorbAll sp0 chunks = .ok sp1 ∧
      keccak.Shake256Sponge.finalize sp1 = .ok sp2 ∧
      (∀ outLen, Qsag.cshake256Xof outLen cust (chunks.map fun d => u8Bytes d.val).flatten =
        Qsag.squeezeXofAux outLen (keccakStateOfArray sp2.state)) ∧
      sp2.squeezing = true ∧ sp2.squeeze_offset = 0#usize := by
  obtain ⟨sp1, h1, habs1, hs1⟩ := sponge_absorb_all_refines chunks sp0 _ hpre
  obtain ⟨sp2, h2, hstate, hsq, hoff, _⟩ := sponge_finalize_refines sp1 _ habs1
  refine ⟨sp1, sp2, h1, h2, fun outLen => ?_, hsq, hoff⟩
  unfold Qsag.cshake256Xof
  simp only [hc, ↓reduceIte]
  rw [hstate, hs1, hsfx]
  rfl

/-- A whole short squeeze writes every byte of the initial rate block, rather than
merely terminating. The result is independent of the destination's initial contents. -/
theorem sponge_squeeze_prefix (sp : keccak.Shake256Sponge) (out : Slice Std.U8)
    (hsq : sp.squeezing = true) (hoff : sp.squeeze_offset = 0#usize)
    (hsize : out.val.length ≤ 136) :
    ∃ sp' dst, keccak.Shake256Sponge.squeeze sp out = .ok (sp', dst) ∧
      dst.val.length = out.val.length ∧
      ∀ j, j < out.val.length →
        dst.val.getD j 0#u8 = spongeRateByte sp.state j := by
  let size := out.val.length
  let body := fun (st, dst, i) => keccak.Shake256Sponge.squeeze_loop.body st dst i
  let P := fun (n : Nat) (x : keccak.Shake256Sponge × Slice Std.U8 × Std.Usize) =>
    x.2.2.val + n = size ∧ x.2.1.val.length = size ∧
    x.1.squeeze_offset.val = x.2.2.val ∧ x.1.state = sp.state ∧
    ∀ j, j < x.2.2.val → x.2.1.val.getD j 0#u8 = spongeRateByte sp.state j
  let Q := fun (x : keccak.Shake256Sponge × Slice Std.U8) =>
    x.2.val.length = size ∧ ∀ j, j < size →
      x.2.val.getD j 0#u8 = spongeRateByte sp.state j
  have hz : ∀ x, P 0 x → ∃ y, body x = .ok (.done y) ∧ Q y := by
    rintro ⟨st, dst, i⟩ ⟨hi, hd, _, _, hx⟩
    have hiv : i.val = size := by simpa using hi
    have he : ¬ i < Slice.len dst := by
      change ¬ i.val < (Slice.len dst).val
      rw [Slice.len_val, hd, hiv]
      exact Nat.lt_irrefl _
    refine ⟨(st, dst), ?_, hd, ?_⟩
    · simp only [body, keccak.Shake256Sponge.squeeze_loop.body, he, ite_false]
    · intro j hj; exact hx j (hiv ▸ hj)
  have step : ∀ n x, P (n + 1) x → ∃ x', body x = .ok (.cont x') ∧ P n x' := by
    rintro n ⟨st, dst, i⟩ ⟨hi, hd, ho, ha, hx⟩
    dsimp only at hi hd ho ha hx
    have hil : i.val < dst.val.length := by change i.val + (n + 1) = size at hi; omega
    have hol : st.squeeze_offset.val < 136 := by
      change st.squeeze_offset.val = i.val at ho
      change dst.val.length = out.val.length at hd
      omega
    obtain ⟨dst', i', off', hbody, hdst, hi', hoff'⟩ := sponge_squeeze_byte st dst i hil hol
    refine ⟨({st with squeeze_offset := off'}, dst', i'), hbody, ?_, ?_, ?_, ha, ?_⟩
    · change i'.val + n = size
      change i.val + (n + 1) = size at hi
      omega
    · change dst'.val.length = size
      rw [hdst, List.length_set]; exact hd
    · change off'.val = i'.val; omega
    · intro j hj
      change j < i'.val at hj
      change dst'.val.getD j 0#u8 = _
      rw [hdst, getD_set dst.val i.val j _ _ hil]
      by_cases he : j = i.val
      · subst j
        simp only [↓reduceIte]
        rw [ha, ho]
      · rw [ite_eq_right he]
        exact hx j (by omega)
  obtain ⟨⟨sp', dst⟩, hloop, hd, hx⟩ := loopFuel_total_rank body P Q hz step size
    (sp, out, 0#usize) ⟨Nat.zero_add _, rfl, by rw [hoff], rfl, by intro j hj; exact (Nat.not_lt_zero j hj).elim⟩
  have hactual : keccak.Shake256Sponge.squeeze_loop sp out 0#usize = .ok (sp', dst) := by
    unfold keccak.Shake256Sponge.squeeze_loop
    apply loop_ok_of_loopFuel (fuel := size + 1)
    · exact Nat.le_trans (Nat.add_le_add_right hsize 1) (by decide)
    · exact hloop
  refine ⟨sp', dst, ?_, hd, hx⟩
  simp only [keccak.Shake256Sponge.squeeze, keccak.Shake256Sponge.finalize,
    hsq, ite_true, bind_eq_result_bind, result_bind_ok, hactual]

private theorem spongeRateByte_nat (a : Array Std.U64 25#usize) (j : Nat) :
    (UInt8.ofBitVec (spongeRateByte a j).bv).toNat =
      (a.val.getD (j / 8) 0#u64).val / 2 ^ (8 * (j % 8)) % 256 := by
  simp only [spongeRateByte, UScalar.cast, UScalar.bv_and, BitVec.setWidth_and]
  change (UInt8.ofBitVec (((a.val.getD (j / 8) 0#u64).bv >>> (8 * (j % 8))).setWidth 8
    &&& BitVec.allOnes 8)).toNat = _
  rw [byte_and_allOnes]
  simp [UInt8.toNat_ofBitVec, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, UScalar.val]

set_option maxHeartbeats 2000000 in
private theorem spongeRateByte_spec32 (a : Array Std.U64 25#usize) (j : Nat)
    (hj : j < 32) :
    UInt8.ofBitVec (spongeRateByte a j).bv =
      (Qsag.rateBlockBytes (keccakStateOfArray a)).getD j 0 := by
  apply UInt8.toNat_inj.mp
  rw [spongeRateByte_nat]
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨ j = 30 ∨ j = 31 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Qsag.rateBlockBytes_eq_laneBytes, keccakStateOfArray,
    UInt64.toNat_ofBitVec, UScalar.val]

private theorem list_eq_of_getD {α : Type} (d : α) (xs ys : List α)
    (hlen : xs.length = ys.length)
    (h : ∀ i, i < xs.length → xs.getD i d = ys.getD i d) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => cases hlen
  | cons x xs ih =>
    cases ys with
    | nil => cases hlen
    | cons y ys =>
      have hxy : x = y := h 0 (Nat.zero_lt_succ _)
      have ht : xs = ys := ih ys (Nat.succ.inj hlen)
        (fun i hi => h (i + 1) (Nat.succ_lt_succ hi))
      rw [hxy, ht]

/-- The complete 32-byte squeeze agrees with the canonical XOF byte stream. -/
theorem sponge_squeeze32_refines (sp : keccak.Shake256Sponge) (out : Slice Std.U8)
    (hsq : sp.squeezing = true) (hoff : sp.squeeze_offset = 0#usize)
    (hlen : out.val.length = 32) :
    ∃ sp' dst, keccak.Shake256Sponge.squeeze sp out = .ok (sp', dst) ∧
      u8Bytes dst.val = Qsag.squeezeXofAux 32 (keccakStateOfArray sp.state) := by
  obtain ⟨sp', dst, hr, hd, hx⟩ := sponge_squeeze_prefix sp out hsq hoff (by omega)
  refine ⟨sp', dst, hr, ?_⟩
  apply list_eq_of_getD 0
  · rw [u8Bytes_length, hd, hlen, Qsag.squeezeXofAux_length]
  · intro j hj
    have hj32 : j < 32 := by rw [u8Bytes_length, hd, hlen] at hj; exact hj
    rw [u8Bytes_getD, hx j (by omega), spongeRateByte_spec32 sp.state j hj32]
    simp [Qsag.squeezeXofAux_eq, Qsag.squeezeXofFuel_succ_succ, List.getD_eq_getElem?_getD, hj32]

/-- End-to-end SHAKE256 equality: the extracted Rust entry point returns exactly the
canonical 32 bytes, for arbitrary input length. -/
theorem shake256_32_refines (input : Slice Std.U8) :
    ∃ out, keccak.shake256_32 input = .ok out ∧
      u8Bytes out.val = Qsag.shake256Xof 32 (u8Bytes input.val) := by
  obtain ⟨sp0, hnew, habs0, hsfx0⟩ := sponge_new_shake256_absorbed
  obtain ⟨sp1, habs, habs1, hsfx1⟩ := sponge_absorb_refines sp0 input [] habs0
  obtain ⟨sp2, hfinal, hstate, hsq, hoff, _⟩ := sponge_finalize_refines sp1 _ habs1
  let dst0 := Array.repeat 32#usize 0#u8
  obtain ⟨sp3, dst, hsqueeze, hbytes⟩ :=
    sponge_squeeze32_refines sp2 (Array.to_slice_mut dst0).1 hsq hoff rfl
  have hd : dst.val.length = (32#usize).val := by
    have hl := congrArg List.length hbytes
    rw [u8Bytes_length, Qsag.squeezeXofAux_length] at hl
    exact hl
  have hloop : keccak.Shake256Sponge.squeeze_loop sp2 (Array.to_slice_mut dst0).1 0#usize =
      .ok (sp3, dst) := by
    simpa only [keccak.Shake256Sponge.squeeze, keccak.Shake256Sponge.finalize,
      hsq, ite_true, bind_eq_result_bind, result_bind_ok] using hsqueeze
  dsimp only [dst0] at hloop
  refine ⟨Array.from_slice dst0 dst, ?_, ?_⟩
  · simp only [keccak.shake256_32, hnew, habs, keccak.Shake256Sponge.squeeze,
      hfinal, bind_eq_result_bind, result_bind_ok, lift_eq_ok, hloop]
    rfl
  · simp only [Array.from_slice, hd, dite_true]
    rw [hbytes, hstate, hsfx1, hsfx0, List.nil_append]
    rfl

/-- Empty customization selects SHAKE in both the extracted constructor and the spec. -/
theorem cshake256_32_empty_refines (input : Slice Std.U8) :
    ∃ out, keccak.cshake256_32 ⟨[], by decide⟩ input = .ok out ∧
      u8Bytes out.val = Qsag.cshake256Xof 32 [] (u8Bytes input.val) :=
  shake256_32_refines input

/-- cSHAKE's byte-output weld from a constructor result that has absorbed the SP 800-185
prefix. `cshake256_32_refines` discharges the prefix premises. -/
theorem cshake256_32_refines_of_prefix (customization input : Slice Std.U8)
    (hc : u8Bytes customization.val ≠ []) (sp0 : keccak.Shake256Sponge)
    (hnew : keccak.Shake256Sponge.new_cshake256 customization = .ok sp0)
    (hpre : SpongeAbsorbed sp0 (Qsag.customizationPrefix (u8Bytes customization.val)))
    (hsfx : sp0.suffix = 4#u8) :
    ∃ out, keccak.cshake256_32 customization input = .ok out ∧
      u8Bytes out.val = Qsag.cshake256Xof 32 (u8Bytes customization.val) (u8Bytes input.val) := by
  obtain ⟨sp1, habs, habs1, hsfx1⟩ := sponge_absorb_refines sp0 input _ hpre
  obtain ⟨sp2, hfinal, hstate, hsq, hoff, _⟩ := sponge_finalize_refines sp1 _ habs1
  let dst0 := Array.repeat 32#usize 0#u8
  obtain ⟨sp3, dst, hsqueeze, hbytes⟩ :=
    sponge_squeeze32_refines sp2 (Array.to_slice_mut dst0).1 hsq hoff rfl
  have hd : dst.val.length = (32#usize).val := by
    have hl := congrArg List.length hbytes
    rw [u8Bytes_length, Qsag.squeezeXofAux_length] at hl
    exact hl
  have hloop : keccak.Shake256Sponge.squeeze_loop sp2 (Array.to_slice_mut dst0).1 0#usize =
      .ok (sp3, dst) := by
    simpa only [keccak.Shake256Sponge.squeeze, keccak.Shake256Sponge.finalize,
      hsq, ite_true, bind_eq_result_bind, result_bind_ok] using hsqueeze
  dsimp only [dst0] at hloop
  refine ⟨Array.from_slice dst0 dst, ?_, ?_⟩
  · simp only [keccak.cshake256_32, hnew, habs, keccak.Shake256Sponge.squeeze,
      hfinal, bind_eq_result_bind, result_bind_ok, lift_eq_ok, hloop]
    rfl
  · simp only [Array.from_slice, hd, dite_true]
    rw [hbytes, hstate, hsfx1, hsfx]
    simp only [Qsag.cshake256Xof, hc, ↓reduceIte]
    rfl

/-! ## `new_cshake256` constructor helpers -/

private theorem u8Bytes_append (xs ys : List Std.U8) :
    u8Bytes (xs ++ ys) = u8Bytes xs ++ u8Bytes ys :=
  List.map_append

private theorem u8Bytes_take (xs : List Std.U8) (n : Nat) :
    u8Bytes (xs.take n) = (u8Bytes xs).take n :=
  List.map_take

private theorem u8Bytes_replicate_zero : ∀ n : Nat,
    u8Bytes (List.replicate n 0#u8) = List.replicate n 0
  | 0 => rfl
  | n + 1 => by
    simp only [List.replicate_succ, u8Bytes, List.map_cons]
    exact congrArg (0 :: ·) (u8Bytes_replicate_zero n)

private theorem new_cshake256_loop1_eq (buf : Array Std.U8 136#usize) (start : Std.Usize)
    (hs : start.val ≤ 136) :
    ∃ out, keccak.Shake256Sponge.new_cshake256_loop1 buf start = .ok out ∧
      out.val = buf.val.take start.val ++ List.replicate (136 - start.val) 0#u8 := by
  have hbl : buf.val.length = 136 := buf.property
  let body := fun (a, i) => keccak.Shake256Sponge.new_cshake256_loop1.body a i
  let P := fun (n : Nat) (x : Array Std.U8 136#usize × Std.Usize) =>
    x.2.val + n = 136 ∧ start.val ≤ x.2.val ∧
      x.1.val = buf.val.take start.val ++ List.replicate (x.2.val - start.val) 0#u8 ++
        buf.val.drop x.2.val
  let Q := fun (a : Array Std.U8 136#usize) =>
    a.val = buf.val.take start.val ++ List.replicate (136 - start.val) 0#u8
  have hz : ∀ x, P 0 x → ∃ y, body x = .ok (.done y) ∧ Q y := by
    rintro ⟨a, i⟩ ⟨hi, _, ha⟩
    change i.val + 0 = 136 at hi
    change a.val = buf.val.take start.val ++ List.replicate (i.val - start.val) 0#u8 ++
      buf.val.drop i.val at ha
    have h136 : i.val = 136 := by omega
    have hn : ¬ i < keccak.SHAKE256_RATE_BYTES := by
      unfold keccak.SHAKE256_RATE_BYTES
      change ¬ i.val < 136
      omega
    refine ⟨a, by simp only [body, keccak.Shake256Sponge.new_cshake256_loop1.body, hn, ite_false], ?_⟩
    change a.val = buf.val.take start.val ++ List.replicate (136 - start.val) 0#u8
    rw [ha, h136, drop_all buf.val 136 (by omega), List.append_nil]
  have step : ∀ n x, P (n + 1) x → ∃ x', body x = .ok (.cont x') ∧ P n x' := by
    rintro n ⟨a, i⟩ ⟨hi, hsi, ha⟩
    change i.val + (n + 1) = 136 at hi
    change start.val ≤ i.val at hsi
    change a.val = buf.val.take start.val ++ List.replicate (i.val - start.val) 0#u8 ++
      buf.val.drop i.val at ha
    have hi136 : i.val < 136 := by omega
    have hlt : i < keccak.SHAKE256_RATE_BYTES := by
      unfold keccak.SHAKE256_RATE_BYTES
      change i.val < 136
      exact hi136
    have hAlen : (buf.val.take start.val ++ List.replicate (i.val - start.val) 0#u8).length =
        i.val := by
      simp only [List.length_append, List.length_take, List.length_replicate]; omega
    have hdrop : buf.val.drop i.val = buf.val[i.val]'(by omega) :: buf.val.drop (i.val + 1) :=
      List.drop_eq_getElem_cons (by omega)
    have hsucc : i.val + 1 - start.val = (i.val - start.val) + 1 := by omega
    let a' : Array Std.U8 136#usize :=
      ⟨a.val.set i.val 0#u8, by rw [List.length_set]; exact a.property⟩
    have ha' : Array.update a i 0#u8 = .ok a' := array_update_eq a i 0#u8 a' hi136 rfl
    obtain ⟨i', hi', vi'⟩ := checked_add_val i 1#usize (by
      change i.val + 1 < 2 ^ 64
      exact Nat.lt_trans (Nat.succ_lt_succ hi136) (by decide))
    change i'.val = i.val + 1 at vi'
    refine ⟨(a', i'), ?_, ?_, ?_, ?_⟩
    · simp only [body, keccak.Shake256Sponge.new_cshake256_loop1.body, hlt, ite_true,
        ha', hi', bind_eq_result_bind, result_bind_ok]
    · change i'.val + n = 136
      omega
    · change start.val ≤ i'.val
      omega
    · change a.val.set i.val 0#u8 =
        buf.val.take start.val ++ List.replicate (i'.val - start.val) 0#u8 ++
          buf.val.drop i'.val
      rw [ha, hdrop, set_append_at _ _ _ _ _ hAlen, vi', hsucc, List.replicate_succ']
      simp only [List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨out, hout, hQ⟩ := loopFuel_total_rank body P Q hz step (136 - start.val)
    (buf, start) ⟨by change start.val + (136 - start.val) = 136; omega, Nat.le_refl _, by
      change buf.val = buf.val.take start.val ++
        List.replicate (start.val - start.val) 0#u8 ++ buf.val.drop start.val
      rw [Nat.sub_self]
      simp only [List.replicate_zero, List.append_nil, List.take_append_drop]⟩
  refine ⟨out, ?_, hQ⟩
  unfold keccak.Shake256Sponge.new_cshake256_loop1
  apply loop_ok_of_loopFuel (fuel := 136 - start.val + 1)
  · apply Nat.le_trans (show 136 - start.val + 1 ≤ 137 from
      Nat.add_le_add_right (Nat.sub_le _ _) 1)
    decide
  · exact hout

/-- The pad is sensitive to the domain suffix: SHAKE and cSHAKE final blocks differ. -/
theorem tooth_last_block_suffix_sensitive :
    spongeLastBlock [] 0x1f ≠ spongeLastBlock [] 0x04 := by decide

/-! ## Multi-block squeeze and arbitrary-length `SHAKE256` / `cSHAKE256` -/

/-- Local copy of the per-lane little-endian byte list used by `Qsag.rateBlockBytes`
(tied to it by `Qsag.rateBlockBytes_eq_laneBytes`). -/
private def laneBytesLE (w : UInt64) : List UInt8 :=
  [UInt8.ofNat (w.toNat % 256),
   UInt8.ofNat ((w.toNat / 256) % 256),
   UInt8.ofNat ((w.toNat / 65536) % 256),
   UInt8.ofNat ((w.toNat / 16777216) % 256),
   UInt8.ofNat ((w.toNat / 4294967296) % 256),
   UInt8.ofNat ((w.toNat / 1099511627776) % 256),
   UInt8.ofNat ((w.toNat / 281474976710656) % 256),
   UInt8.ofNat ((w.toNat / 72057594037927936) % 256)]

private theorem laneBytesLE_len (w : UInt64) : (laneBytesLE w).length = 8 := rfl

private theorem laneBytesLE_getD (w : UInt64) (r : Nat) (hr : r < 8) :
    (laneBytesLE w).getD r 0 = UInt8.ofNat (w.toNat / 2 ^ (8 * r) % 256) := by
  have h : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [laneBytesLE]

private theorem getD_append_lt {α : Type} (xs ys : List α) (d : α) (i : Nat)
    (hi : i < xs.length) : (xs ++ ys).getD i d = xs.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getD_append_ge {α : Type} (xs ys : List α) (d : α) (i : Nat)
    (hi : xs.length ≤ i) : (xs ++ ys).getD i d = ys.getD (i - xs.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

private theorem getD_take_lt {α : Type} (xs : List α) (d : α) (n j : Nat)
    (hj : j < n) : (xs.take n).getD j d = xs.getD j d := by
  induction n generalizing xs j with
  | zero => exact absurd hj (Nat.not_lt_zero j)
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      cases j with
      | zero => rfl
      | succ j => exact ih xs j (Nat.lt_of_succ_lt_succ hj)

private theorem flatMap_laneBytesLE_getD :
    ∀ (ws : List UInt64) (j : Nat),
      j < 8 * ws.length →
      (ws.flatMap laneBytesLE).getD j 0 =
        (laneBytesLE (ws.getD (j / 8) 0)).getD (j % 8) 0
  | [], j, hj => by simp at hj
  | w :: ws, j, hj => by
    simp only [List.flatMap_cons]
    by_cases hlt : j < 8
    · rw [getD_append_lt _ _ 0 j (by rw [laneBytesLE_len]; exact hlt)]
      have hdiv : j / 8 = 0 := Nat.div_eq_of_lt hlt
      have hmod : j % 8 = j := Nat.mod_eq_of_lt hlt
      rw [hdiv, hmod, List.getD_cons_zero]
    · have hge : 8 ≤ j := by omega
      rw [getD_append_ge _ _ 0 j (by rw [laneBytesLE_len]; exact hge), laneBytesLE_len]
      have hj' : j - 8 < 8 * ws.length := by simp only [List.length_cons] at hj; omega
      rw [flatMap_laneBytesLE_getD ws (j - 8) hj']
      have hdiv : j / 8 = (j - 8) / 8 + 1 := by omega
      have hmod : (j - 8) % 8 = j % 8 := by omega
      rw [hdiv, List.getD_cons_succ, hmod]

private def rateLanesList (s : Qsag.KState) : List UInt64 :=
  [s.a0, s.a1, s.a2, s.a3, s.a4, s.a5, s.a6, s.a7, s.a8,
   s.a9, s.a10, s.a11, s.a12, s.a13, s.a14, s.a15, s.a16]

private theorem rateBlockBytes_eq_flatMap (s : Qsag.KState) :
    Qsag.rateBlockBytes s = (rateLanesList s).flatMap laneBytesLE := by
  exact Qsag.rateBlockBytes_eq_laneBytes s

private theorem rateLanesList_keccakStateOfArray_getD (a : Array Std.U64 25#usize)
    (q : Nat) (hq : q < 17) :
    (rateLanesList (keccakStateOfArray a)).getD q 0 =
      UInt64.ofBitVec (a.val.getD q 0#u64).bv := by
  have h : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨
           q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12 ∨ q = 13 ∨ q = 14 ∨ q = 15 ∨ q = 16 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl

/-- Byte `j < 136` of the extracted rate block is byte `j` of `Qsag.rateBlockBytes`. -/
theorem spongeRateByte_spec136 (a : Array Std.U64 25#usize) (j : Nat) (hj : j < 136) :
    UInt8.ofBitVec (spongeRateByte a j).bv =
      (Qsag.rateBlockBytes (keccakStateOfArray a)).getD j 0 := by
  apply UInt8.toNat_inj.mp
  rw [spongeRateByte_nat, rateBlockBytes_eq_flatMap,
    flatMap_laneBytesLE_getD _ j (by simp [rateLanesList]; omega),
    rateLanesList_keccakStateOfArray_getD a (j / 8) (by omega),
    laneBytesLE_getD _ (j % 8) (Nat.mod_lt _ (by decide))]
  simp only [UInt8.toNat_ofNat', UInt64.toNat_ofBitVec, UScalar.val]
  have h256 : (2 : Nat) ^ 8 = 256 := rfl
  rw [h256, Nat.mod_mod]

/-- `k` applications of `Keccak-f[1600]`. -/
def keccakIter : Nat → Qsag.KState → Qsag.KState
  | 0, s => s
  | k + 1, s => keccakIter k (Qsag.keccakF1600 s)

theorem keccakIter_succ_right (k : Nat) (s : Qsag.KState) :
    keccakIter (k + 1) s = Qsag.keccakF1600 (keccakIter k s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact ih (Qsag.keccakF1600 s)

private theorem squeezeXofFuel_getD (fuel outLen : Nat) (s : Qsag.KState) (j : Nat)
    (hf : outLen ≤ 136 * fuel) (hj : j < outLen) :
    (Qsag.squeezeXofFuel fuel outLen s).getD j 0 =
      (Qsag.rateBlockBytes (keccakIter (j / 136) s)).getD (j % 136) 0 := by
  induction fuel generalizing outLen s j with
  | zero => omega
  | succ fuel ih =>
    cases outLen with
    | zero => omega
    | succ m =>
      rw [Qsag.squeezeXofFuel_succ_succ]
      dsimp only []
      by_cases hle : m + 1 ≤ 136
      · rw [ite_eq_left hle, getD_take_lt _ 0 (m + 1) j hj]
        have hj136 : j < 136 := by omega
        rw [Nat.div_eq_of_lt hj136, Nat.mod_eq_of_lt hj136]
        rfl
      · rw [ite_eq_right hle]
        by_cases hj136 : j < 136
        · rw [getD_append_lt _ _ 0 j (by rw [Qsag.rateBlockBytes_length]; exact hj136),
            Nat.div_eq_of_lt hj136, Nat.mod_eq_of_lt hj136]
          rfl
        · have hge136 : 136 ≤ j := by omega
          rw [getD_append_ge _ _ 0 j (by rw [Qsag.rateBlockBytes_length]; exact hge136),
            Qsag.rateBlockBytes_length]
          have hrem : m + 1 - 136 ≤ 136 * fuel := by omega
          have hjrem : j - 136 < m + 1 - 136 := by omega
          rw [ih (m + 1 - 136) (Qsag.keccakF1600 s) (j - 136) hrem hjrem]
          have hdiv : j / 136 = (j - 136) / 136 + 1 := by omega
          have hmod : (j - 136) % 136 = j % 136 := by omega
          rw [hdiv, hmod]
          rfl

theorem squeezeXofAux_getD (outLen : Nat) (s : Qsag.KState) (j : Nat) (hj : j < outLen) :
    (Qsag.squeezeXofAux outLen s).getD j 0 =
      (Qsag.rateBlockBytes (keccakIter (j / 136) s)).getD (j % 136) 0 :=
  Qsag.squeezeXofAux_eq outLen s ▸ squeezeXofFuel_getD outLen outLen s j (by omega) hj

/-- A squeeze from offset zero into a destination of any length, across any number of rate
blocks, succeeds and writes `Qsag.squeezeXofAux out.val.length (keccakStateOfArray sp.state)`. -/
theorem sponge_squeeze_refines (sp : keccak.Shake256Sponge) (out : Slice Std.U8)
    (hsq : sp.squeezing = true) (hoff : sp.squeeze_offset = 0#usize) :
    ∃ sp' dst, keccak.Shake256Sponge.squeeze sp out = .ok (sp', dst) ∧
      u8Bytes dst.val = Qsag.squeezeXofAux out.val.length (keccakStateOfArray sp.state) := by
  let size := out.val.length
  let s₀ := keccakStateOfArray sp.state
  let body := fun (st, dst, w) => keccak.Shake256Sponge.squeeze_loop.body st dst w
  let P := fun (n : Nat) (x : keccak.Shake256Sponge × Slice Std.U8 × Std.Usize) =>
    x.2.2.val + n = size ∧
    x.2.1.val.length = size ∧
    (if x.2.2.val = 0 then
       x.1.squeeze_offset.val = 0 ∧ keccakStateOfArray x.1.state = s₀
     else
       x.1.squeeze_offset.val = (x.2.2.val - 1) % 136 + 1 ∧
       keccakStateOfArray x.1.state = keccakIter ((x.2.2.val - 1) / 136) s₀) ∧
    ∀ j, j < x.2.2.val →
      UInt8.ofBitVec (x.2.1.val.getD j 0#u8).bv =
        (Qsag.rateBlockBytes (keccakIter (j / 136) s₀)).getD (j % 136) 0
  let Q := fun (x : keccak.Shake256Sponge × Slice Std.U8) =>
    x.2.val.length = size ∧
    ∀ j, j < size →
      UInt8.ofBitVec (x.2.val.getD j 0#u8).bv =
        (Qsag.rateBlockBytes (keccakIter (j / 136) s₀)).getD (j % 136) 0
  have hz : ∀ x, P 0 x → ∃ y, body x = .ok (.done y) ∧ Q y := by
    rintro ⟨st, dst, w⟩ ⟨hw, hd, _, hx⟩
    have hwv : w.val = size := by dsimp only at hw; omega
    have he : ¬ w < Slice.len dst := by
      change ¬ w.val < (Slice.len dst).val
      rw [Slice.len_val, hd, hwv]
      exact Nat.lt_irrefl _
    refine ⟨(st, dst), ?_, hd, fun j hj => hx j (hwv ▸ hj)⟩
    simp only [body, keccak.Shake256Sponge.squeeze_loop.body, he, ite_false]
  have step : ∀ n x, P (n + 1) x → ∃ x', body x = .ok (.cont x') ∧ P n x' := by
    rintro n ⟨st, dst, w⟩ ⟨hw, hd, hst, hx⟩
    dsimp only at hw hd hst hx
    have hwl : w.val < dst.val.length := by omega
    by_cases hw0 : w.val = 0
    · rw [ite_eq_left hw0] at hst
      rcases hst with ⟨ho0, ha0⟩
      obtain ⟨dst', w', off', hbody, hdst, vw', voff'⟩ :=
        sponge_squeeze_byte st dst w hwl (by omega)
      refine ⟨({st with squeeze_offset := off'}, dst', w'), hbody, ?_, ?_, ?_, ?_⟩
      · change w'.val + n = size; omega
      · change dst'.val.length = size; rw [hdst, List.length_set]; exact hd
      · change if w'.val = 0 then off'.val = 0 ∧ keccakStateOfArray st.state = s₀
          else off'.val = (w'.val - 1) % 136 + 1 ∧
            keccakStateOfArray st.state = keccakIter ((w'.val - 1) / 136) s₀
        have hwnz : ¬ w'.val = 0 := by omega
        rw [ite_eq_right hwnz]
        have hm : off'.val = (w'.val - 1) % 136 + 1 := by omega
        have hd0 : (w'.val - 1) / 136 = 0 := by omega
        refine ⟨hm, ?_⟩
        rw [hd0]; exact ha0
      · intro j hj
        change j < w'.val at hj
        have hj0 : j = 0 := by omega
        subst hj0
        change UInt8.ofBitVec (dst'.val.getD 0 0#u8).bv = _
        rw [hdst, getD_set dst.val w.val 0 _ _ hwl, ite_eq_left hw0.symm,
          ho0, spongeRateByte_spec136 st.state 0 (by decide), ha0]
        rfl
    · rw [ite_eq_right hw0] at hst
      rcases hst with ⟨ho, ha⟩
      by_cases hlt136 : (w.val - 1) % 136 + 1 < 136
      · obtain ⟨dst', w', off', hbody, hdst, vw', voff'⟩ :=
          sponge_squeeze_byte st dst w hwl (by omega)
        have hmodw : w.val % 136 = (w.val - 1) % 136 + 1 := by omega
        have hdivw : w.val / 136 = (w.val - 1) / 136 := by omega
        refine ⟨({st with squeeze_offset := off'}, dst', w'), hbody, ?_, ?_, ?_, ?_⟩
        · change w'.val + n = size; omega
        · change dst'.val.length = size; rw [hdst, List.length_set]; exact hd
        · change if w'.val = 0 then _ else _
          have hwnz : ¬ w'.val = 0 := by omega
          rw [ite_eq_right hwnz]
          have hm : (w'.val - 1) % 136 + 1 = off'.val := by omega
          have hdv : (w'.val - 1) / 136 = (w.val - 1) / 136 := by omega
          exact ⟨hm.symm, hdv ▸ ha⟩
        · intro j hj
          change j < w'.val at hj
          change UInt8.ofBitVec (dst'.val.getD j 0#u8).bv = _
          rw [hdst, getD_set dst.val w.val j _ _ hwl]
          by_cases he : j = w.val
          · subst he
            rw [ite_eq_left rfl, ho, ← hmodw,
              spongeRateByte_spec136 st.state (w.val % 136) (Nat.mod_lt _ (by decide)),
              ha, ← hdivw]
          · rw [ite_eq_right he]
            exact hx j (by omega)
      · -- Rollover boundary: `(w.val - 1) % 136 + 1 = 136`
        have ho136 : st.squeeze_offset.val = 136 := by omega
        have hmodw : w.val % 136 = 0 := by omega
        have hdivw : w.val / 136 = (w.val - 1) / 136 + 1 := by omega
        let stR : keccak.Shake256Sponge :=
          { st with
            state := keccakArrayOfState (Qsag.keccakF1600 (keccakStateOfArray st.state))
            squeeze_offset := 0#usize }
        have hroll := sponge_squeeze_rollover st dst w hwl (by omega)
        have hstR_off : stR.squeeze_offset.val < 136 := show (0#usize).val < 136 by decide
        obtain ⟨dst', w', off', hbodyR, hdst, vw', voff'⟩ :=
          sponge_squeeze_byte stR dst w hwl hstR_off
        have hstR_state : keccakStateOfArray stR.state = keccakIter (w.val / 136) s₀ := by
          change keccakStateOfArray (keccakArrayOfState _) = _
          rw [keccakStateOfArray_roundtrip, ha, hdivw, keccakIter_succ_right]
        refine ⟨({stR with squeeze_offset := off'}, dst', w'), hroll.trans hbodyR, ?_, ?_, ?_, ?_⟩
        · change w'.val + n = size; omega
        · change dst'.val.length = size; rw [hdst, List.length_set]; exact hd
        · change if w'.val = 0 then _ else _
          have hwnz : ¬ w'.val = 0 := by omega
          rw [ite_eq_right hwnz]
          have hvoff1 : off'.val = 1 := by change off'.val = 0 + 1 at voff'; exact voff'
          have hm : (w'.val - 1) % 136 + 1 = 1 := by omega
          have hdv : (w'.val - 1) / 136 = w.val / 136 := by omega
          exact ⟨hvoff1.trans hm.symm, hstR_state.trans (congrArg (keccakIter · s₀) hdv.symm)⟩
        · intro j hj
          change j < w'.val at hj
          change UInt8.ofBitVec (dst'.val.getD j 0#u8).bv = _
          rw [hdst, getD_set dst.val w.val j _ _ hwl]
          by_cases he : j = w.val
          · subst he
            change UInt8.ofBitVec (if w.val = w.val then spongeRateByte stR.state 0 else _).bv = _
            rw [ite_eq_left rfl, spongeRateByte_spec136 stR.state 0 (by decide),
              hstR_state, hmodw]
          · rw [ite_eq_right he]
            exact hx j (by omega)
  obtain ⟨⟨sp', dst⟩, hloop, hd, hx⟩ := loopFuel_total_rank body P Q hz step size
    (sp, out, 0#usize)
    ⟨Nat.zero_add _, rfl, by
      change if (0#usize).val = 0 then sp.squeeze_offset.val = 0 ∧ keccakStateOfArray sp.state = s₀
        else _
      have h0u : (0#usize).val = 0 := rfl
      rw [ite_eq_left h0u, hoff]
      exact ⟨rfl, rfl⟩,
      fun j hj => (Nat.not_lt_zero j hj).elim⟩
  have hactual : keccak.Shake256Sponge.squeeze_loop sp out 0#usize = .ok (sp', dst) := by
    unfold keccak.Shake256Sponge.squeeze_loop
    apply loop_ok_of_loopFuel (fuel := size + 1)
    · simpa only [Slice.len_val] using usize_lt_loopMaxFuel (Slice.len out)
    · exact hloop
  refine ⟨sp', dst, ?_, ?_⟩
  · simp only [keccak.Shake256Sponge.squeeze, keccak.Shake256Sponge.finalize,
      hsq, ite_true, bind_eq_result_bind, result_bind_ok, hactual]
  · apply list_eq_of_getD 0
    · rw [u8Bytes_length, hd, Qsag.squeezeXofAux_length]
    · intro j hj
      have hjs : j < size := by rw [u8Bytes_length, hd] at hj; exact hj
      rw [u8Bytes_getD, hx j hjs, squeezeXofAux_getD size s₀ j hjs]

/-- SHAKE256 end to end: absorbing `chunks` in any split and squeezing into `out` of any
length yields `Qsag.shake256Xof out.val.length` of the concatenated input. -/
theorem shake256_squeeze_refines (chunks : List (Slice Std.U8)) (out : Slice Std.U8) :
    ∃ sp0 sp1 sp3 dst,
      keccak.Shake256Sponge.new_shake256 = .ok sp0 ∧
      spongeAbsorbAll sp0 chunks = .ok sp1 ∧
      keccak.Shake256Sponge.squeeze sp1 out = .ok (sp3, dst) ∧
      u8Bytes dst.val =
        Qsag.shake256Xof out.val.length (chunks.map fun d => u8Bytes d.val).flatten := by
  obtain ⟨sp0, sp1, sp2, h0, h1, h2, hstate, hsq, hoff⟩ := shake256_absorb_pad_refines chunks
  obtain ⟨sp3, dst, hsqueeze, hbytes⟩ := sponge_squeeze_refines sp2 out hsq hoff
  have hloop : keccak.Shake256Sponge.squeeze_loop sp2 out 0#usize = .ok (sp3, dst) := by
    simpa only [keccak.Shake256Sponge.squeeze, keccak.Shake256Sponge.finalize,
      hsq, ite_true, bind_eq_result_bind, result_bind_ok] using hsqueeze
  refine ⟨sp0, sp1, sp3, dst, h0, h1, ?_, ?_⟩
  · simp only [keccak.Shake256Sponge.squeeze, h2, bind_eq_result_bind, result_bind_ok, hloop]
  · rw [hbytes, hstate]
    rfl

/-! ### SP 800-185 `left_encode` and the `new_cshake256` constructor -/

/-- Local copy of the fuel-driven little-endian digit recursion behind `Qsag.natBytesBE`
(tied to it by `natBytesBE_eq_digits`). -/
private def natBytesLEAux : Nat → Nat → List UInt8
  | 0, _ => []
  | fuel + 1, value =>
    if value = 0 then [] else UInt8.ofNat (value % 256) :: natBytesLEAux fuel (value / 256)

private theorem natBytesBE_eq_digits (value : Nat) :
    Qsag.natBytesBE value =
      (if natBytesLEAux value value = [] then [0] else natBytesLEAux value value).reverse :=
  Qsag.natBytesBE_eq_of_digits natBytesLEAux (fun _ => rfl) (fun _ _ => rfl) value

private theorem natBytesLEAux_fuel_eq :
    ∀ (f1 f2 x : Nat),
      x < 256 ^ f1 → x < 256 ^ f2 →
      natBytesLEAux f1 x = natBytesLEAux f2 x
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, x, h1, _ => by
    have hx0 : x = 0 := by simp at h1; omega
    subst hx0; rfl
  | _ + 1, 0, x, _, h2 => by
    have hx0 : x = 0 := by simp at h2; omega
    subst hx0; rfl
  | f1 + 1, f2 + 1, x, h1, h2 => by
    unfold natBytesLEAux
    by_cases hx0 : x = 0
    · simp [hx0]
    · simp only [hx0, ↓reduceIte]
      have hd1 : x / 256 < 256 ^ f1 := by rw [Nat.pow_succ] at h1; omega
      have hd2 : x / 256 < 256 ^ f2 := by rw [Nat.pow_succ] at h2; omega
      rw [natBytesLEAux_fuel_eq f1 f2 (x / 256) hd1 hd2]

private theorem lt_pow_256_self : ∀ x : Nat, x < 256 ^ x
  | 0 => by decide
  | x + 1 => by
    have ih := lt_pow_256_self x
    rw [Nat.pow_succ]
    omega

private theorem natBytesLEAux_len_le : ∀ (f x : Nat), (natBytesLEAux f x).length ≤ f
  | 0, _ => Nat.le_refl 0
  | f + 1, x => by
    unfold natBytesLEAux
    by_cases hx0 : x = 0
    · simp [hx0]
    · simp only [hx0, ↓reduceIte, List.length_cons]
      exact Nat.succ_le_succ (natBytesLEAux_len_le f (x / 256))

private theorem natBytesLEAux_nonempty_of_pos :
    ∀ (f x : Nat), 0 < f → 0 < x → natBytesLEAux f x ≠ []
  | 0, _, hf, _ => by omega
  | _ + 1, x, _, hx => by
    unfold natBytesLEAux
    have hne : ¬ x = 0 := by omega
    simp [hne]

private theorem natBytesLEAux_eq_nil_imp_zero :
    ∀ (f x : Nat), x < 256 ^ f → natBytesLEAux f x = [] → x = 0
  | 0, x, hx, _ => by simp at hx; omega
  | _ + 1, x, _, heq => by
    unfold natBytesLEAux at heq
    by_cases hx0 : x = 0
    · exact hx0
    · simp [hx0] at heq

private theorem usize_sub_ok {a b : Std.Usize} (h : b.val ≤ a.val) :
    ∃ c : Std.Usize, (a - b : Result Std.Usize) = .ok c ∧ c.val = a.val - b.val := by
  refine ⟨⟨a.bv - b.bv⟩, ?_, ?_⟩
  · simp only [hSub_uscalar_eq, h, ↓reduceIte]
  · exact BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)

private theorem getD_reverse_lt (ds : List UInt8) (i : Nat) (hi : i < ds.length) :
    ds.getD (ds.length - 1 - i) 0 = ds.reverse.getD i 0 := by
  have hir : i < ds.reverse.length := by rw [List.length_reverse]; exact hi
  have hsub : ds.length - 1 - i < ds.length := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hsub,
    List.getElem?_eq_getElem hir, Option.getD_some, List.getElem_reverse]

/-- The extracted `left_encode` returns `Qsag.leftEncode v.val` in the first `n ≤ 17` bytes
of its buffer, for every `v : Std.U128`. -/
theorem sp800_185_left_encode_u128_refines (v : Std.U128) :
    ∃ len_enc n,
      keccak.sp800_185_left_encode_u128 v = .ok (len_enc, n) ∧
      n.val ≤ 17 ∧
      u8Bytes (len_enc.val.take n.val) = Qsag.leftEncode v.val := by
  by_cases hv0 : v = 0#u128
  · subst hv0
    refine ⟨Array.make 17#usize
      [1#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
       0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8],
      2#usize, ?_, by decide, ?_⟩
    · simp only [keccak.sp800_185_left_encode_u128, ↓reduceIte]
    · rw [Qsag.leftEncode_eq, natBytesBE_eq_digits]
      decide
  · have hvpos : 0 < v.val := by
      by_cases hz : v.val = 0
      · exact False.elim (hv0 (UScalar.eq_of_val_eq hz))
      · omega
    have hv16 : v.val < 256 ^ 16 := by
      have h128 : v.val < 2 ^ 128 := v.bv.isLt
      have heq : (2 : Nat) ^ 128 = 256 ^ 16 := by decide
      omega
    let ds := natBytesLEAux 16 v.val
    let m := ds.length
    have hm_le : m ≤ 16 := natBytesLEAux_len_le 16 v.val
    have hds_ne : ds ≠ [] := natBytesLEAux_nonempty_of_pos 16 v.val (by decide) hvpos
    have hm_pos : 1 ≤ m := by
      cases hds : ds with
      | nil => exact False.elim (hds_ne hds)
      | cons _ _ => dsimp only [m]; rw [hds]; exact Nat.succ_pos _
    have hleft : Qsag.leftEncode v.val = UInt8.ofNat m :: ds.reverse := by
      rw [Qsag.leftEncode_eq, natBytesBE_eq_digits]
      have hf : natBytesLEAux v.val v.val = ds :=
        natBytesLEAux_fuel_eq v.val 16 v.val (lt_pow_256_self v.val) hv16
      simp only [hf, hds_ne, ↓reduceIte, List.length_reverse]
      rfl
    -- Loop 0: extract little-endian bytes of `v` into `tmp[0..m]`
    let tmp0 := Array.repeat 16#usize 0#u8
    let body0 := fun (t, idx, cur) => keccak.sp800_185_left_encode_u128_loop0.body t idx cur
    let P0 := fun (rem : Nat) (x : Array Std.U8 16#usize × Std.Usize × Std.U128) =>
      x.2.1.val + rem = m ∧
      x.2.2.val < 256 ^ (16 - x.2.1.val) ∧
      natBytesLEAux (16 - x.2.1.val) x.2.2.val = ds.drop x.2.1.val ∧
      u8Bytes (x.1.val.take x.2.1.val) = ds.take x.2.1.val
    let Q0 := fun (y : Array Std.U8 16#usize × Std.Usize) =>
      y.2.val = m ∧ u8Bytes (y.1.val.take m) = ds
    have hz0 : ∀ x, P0 0 x → ∃ y, body0 x = .ok (.done y) ∧ Q0 y := by
      rintro ⟨t, idx, cur⟩ ⟨hi, hbound, haux, htake⟩
      dsimp only at hi hbound haux htake
      have him : idx.val = m := by omega
      have hdrop_nil : ds.drop idx.val = [] := drop_all ds idx.val (by omega)
      have hcur0 : cur.val = 0 :=
        natBytesLEAux_eq_nil_imp_zero (16 - idx.val) cur.val hbound (haux.trans hdrop_nil)
      have hnpos : ¬ (cur > 0#u128) := by change ¬ 0 < cur.val; omega
      refine ⟨(t, idx), ?_, him, ?_⟩
      · simp only [body0, keccak.sp800_185_left_encode_u128_loop0.body, hnpos, ite_false]
      · rw [← him, htake, him, List.take_of_length_le (Nat.le_refl _)]
    have step0 : ∀ rem x, P0 (rem + 1) x → ∃ x', body0 x = .ok (.cont x') ∧ P0 rem x' := by
      rintro rem ⟨t, idx, cur⟩ ⟨hi, hbound, haux, htake⟩
      dsimp only at hi hbound haux htake
      have hidx_m : idx.val < m := by omega
      have hidx_16 : idx.val < 16 := by omega
      have hlt16 : idx < 16#usize := hidx_16
      have hf_succ : 16 - idx.val = (15 - idx.val) + 1 := by omega
      have hdrop_cons : ds.drop idx.val = ds[idx.val]'hidx_m :: ds.drop (idx.val + 1) :=
        List.drop_eq_getElem_cons hidx_m
      have hcur_pos : 0 < cur.val := by
        by_cases hc0 : cur.val = 0
        · rw [hf_succ] at haux
          unfold natBytesLEAux at haux
          rw [ite_eq_left hc0, hdrop_cons] at haux
          cases haux
        · omega
      have hcgt : cur > 0#u128 := hcur_pos
      rw [hf_succ] at haux hbound
      unfold natBytesLEAux at haux
      have hcne0 : ¬ cur.val = 0 := by omega
      simp only [hcne0, ↓reduceIte] at haux
      rw [hdrop_cons] at haux
      obtain ⟨hb_eq, htail_eq⟩ := List.cons.inj haux
      let b : Std.U8 := UScalar.cast .U8 (cur &&& 255#u128)
      have hb_u8 : UInt8.ofBitVec b.bv = UInt8.ofNat (cur.val % 256) := by
        apply UInt8.toNat_inj.mp
        change ((cur.bv &&& (255#u128).bv).setWidth 8).toNat = (UInt8.ofNat (cur.val % 256)).toNat
        rw [BitVec.toNat_setWidth, BitVec.toNat_and, UInt8.toNat_ofNat']
        have hm255 : (255#u128).bv.toNat = 2 ^ 8 - 1 := rfl
        have h256 : (2 : Nat) ^ 8 = 256 := rfl
        rw [hm255, and_mask_eq_mod, h256, Nat.mod_mod]
      let a : Array Std.U8 16#usize :=
        ⟨t.val.set idx.val b, by rw [List.length_set]; exact t.property⟩
      have hupd : Array.update t idx b = .ok a := array_update_eq t idx b a hidx_16 rfl
      dsimp only [b] at hupd
      let cur1 : Std.U128 := ⟨cur.bv >>> 8⟩
      have hshr : (cur >>> 8#i32 : Result Std.U128) = .ok cur1 := rfl
      have vcur1 : cur1.val = cur.val / 256 := by
        change (cur.bv >>> 8).toNat = cur.val / 256
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      obtain ⟨idx1, hidx1, vidx1⟩ := checked_add_val idx 1#usize
        (by change idx.val + 1 < 2 ^ 64; omega)
      change idx1.val = idx.val + 1 at vidx1
      refine ⟨(a, idx1, cur1), ?_, ?_, ?_, ?_, ?_⟩
      · simp only [body0, keccak.sp800_185_left_encode_u128_loop0.body, hcgt, hlt16, ite_true,
          hupd, hshr, hidx1, bind_eq_result_bind, result_bind_ok, lift_eq_ok]
      · change idx1.val + rem = m; omega
      · change cur1.val < 256 ^ (16 - idx1.val)
        have hsub : 16 - idx1.val = 15 - idx.val := by omega
        rw [vcur1, hsub]
        rw [Nat.pow_succ] at hbound
        omega
      · change natBytesLEAux (16 - idx1.val) cur1.val = ds.drop idx1.val
        have hsub : 16 - idx1.val = 15 - idx.val := by omega
        rw [hsub, vcur1, vidx1]
        exact htail_eq
      · change u8Bytes ((t.val.set idx.val b).take idx1.val) = ds.take idx1.val
        have htlen : idx.val < t.val.length := by rw [t.property]; exact hidx_16
        rw [set_eq_take_cons_drop t.val idx.val b htlen, vidx1,
          take_append_at _ _ _ idx.val (by rw [List.length_take]; omega),
          u8Bytes_append, htake]
        have htake_ds : ds.take (idx.val + 1) = ds.take idx.val ++ [ds[idx.val]'hidx_m] :=
          List.take_succ_eq_append_getElem hidx_m
        rw [htake_ds]
        change ds.take idx.val ++ [UInt8.ofBitVec b.bv] = _
        rw [hb_u8, hb_eq]
    obtain ⟨⟨tmp1, n1⟩, hloop0_fuel, hn1_m, htmp1_ds⟩ :=
      loopFuel_total_rank body0 P0 Q0 hz0 step0 m (tmp0, 0#usize, v)
        ⟨Nat.zero_add _, hv16, rfl, rfl⟩
    dsimp only at hn1_m htmp1_ds
    have hloop0 : keccak.sp800_185_left_encode_u128_loop0 tmp0 0#usize v = .ok (tmp1, n1) := by
      unfold keccak.sp800_185_left_encode_u128_loop0
      exact loop_ok_of_loopFuel (fuel := m + 1)
        (Nat.le_trans (show m + 1 ≤ 17 by omega) (by decide)) hloop0_fuel
    -- Loop 1: write length header `n1` at `out[0]` and reverse `tmp1[0..m]` into `out[1..1+m]`
    let out0 := Array.repeat 17#usize 0#u8
    let hdrByte : Std.U8 := UScalar.cast .U8 n1
    have hhdr_u8 : UInt8.ofBitVec hdrByte.bv = UInt8.ofNat m := by
      apply UInt8.toNat_inj.mp
      change (n1.bv.setWidth 8).toNat = (UInt8.ofNat m).toNat
      rw [BitVec.toNat_setWidth, UInt8.toNat_ofNat']
      change n1.val % 256 = m % 256
      rw [hn1_m]
    let a0 : Array Std.U8 17#usize :=
      ⟨out0.val.set 0 hdrByte, by rw [List.length_set]; exact out0.property⟩
    have hupd_a0 : Array.update out0 0#usize hdrByte = .ok a0 :=
      array_update_eq out0 0#usize hdrByte a0 (by decide) rfl
    let body1 := fun (o, i) => keccak.sp800_185_left_encode_u128_loop1.body tmp1 n1 o i
    let P1 := fun (rem : Nat) (x : Array Std.U8 17#usize × Std.Usize) =>
      x.2.val + rem = m ∧
      u8Bytes (x.1.val.take (1 + x.2.val)) = UInt8.ofNat m :: ds.reverse.take x.2.val
    let Q1 := fun (o : Array Std.U8 17#usize) =>
      u8Bytes (o.val.take (1 + m)) = UInt8.ofNat m :: ds.reverse
    have hz1 : ∀ x, P1 0 x → ∃ y, body1 x = .ok (.done y) ∧ Q1 y := by
      rintro ⟨o, i⟩ ⟨hi, htake⟩
      dsimp only at hi htake
      have him : i.val = m := by omega
      have hnlt : ¬ (i < n1) := by change ¬ i.val < n1.val; omega
      refine ⟨o, ?_, ?_⟩
      · simp only [body1, keccak.sp800_185_left_encode_u128_loop1.body, hnlt, ite_false]
      · change u8Bytes (o.val.take (1 + m)) = UInt8.ofNat m :: ds.reverse
        rw [← him, htake, him, List.take_of_length_le (by rw [List.length_reverse]; exact Nat.le_refl m)]
    have step1 : ∀ rem x, P1 (rem + 1) x → ∃ x', body1 x = .ok (.cont x') ∧ P1 rem x' := by
      rintro rem ⟨o, i⟩ ⟨hi, htake⟩
      dsimp only at hi htake
      have hi_m : i.val < m := by omega
      have hlt_n1 : i < n1 := by change i.val < n1.val; omega
      obtain ⟨i1, hi1, vi1⟩ := usize_sub_ok (a := n1) (b := 1#usize) (by change 1 ≤ n1.val; omega)
      change i1.val = n1.val - 1 at vi1
      obtain ⟨i2, hi2, vi2⟩ := usize_sub_ok (a := i1) (b := i) (by change i.val ≤ i1.val; omega)
      change i2.val = i1.val - i.val at vi2
      have hi2_16 : i2.val < 16 := by omega
      have hidx_tmp : Array.index_usize tmp1 i2 = .ok (tmp1.val.getD i2.val 0#u8) :=
        array_index_getD tmp1 i2 0#u8 hi2_16
      obtain ⟨i4, hi4, vi4⟩ := checked_add_val 1#usize i
        (by change 1 + i.val < 2 ^ 64; omega)
      change i4.val = 1 + i.val at vi4
      have hi4_17 : i4.val < 17 := by omega
      let b_rev := tmp1.val.getD i2.val 0#u8
      let o' : Array Std.U8 17#usize :=
        ⟨o.val.set i4.val b_rev, by rw [List.length_set]; exact o.property⟩
      have hupd_o : Array.update o i4 b_rev = .ok o' :=
        array_update_eq o i4 b_rev o' hi4_17 rfl
      dsimp only [b_rev] at hupd_o
      obtain ⟨i5, hi5, vi5⟩ := checked_add_val i 1#usize
        (by change i.val + 1 < 2 ^ 64; omega)
      change i5.val = i.val + 1 at vi5
      refine ⟨(o', i5), ?_, ?_, ?_⟩
      · simp only [body1, keccak.sp800_185_left_encode_u128_loop1.body, hlt_n1, ite_true,
          hi1, hi2, hidx_tmp, hi4, hupd_o, hi5, bind_eq_result_bind, result_bind_ok]
      · change i5.val + rem = m; omega
      · change u8Bytes ((o.val.set i4.val b_rev).take (1 + i5.val)) =
          UInt8.ofNat m :: ds.reverse.take i5.val
        have holen : i4.val < o.val.length := by rw [o.property]; exact hi4_17
        have h1i5 : 1 + i5.val = i4.val + 1 := by omega
        rw [h1i5, set_eq_take_cons_drop o.val i4.val b_rev holen,
          take_append_at _ _ _ i4.val (by rw [List.length_take]; omega),
          u8Bytes_append, vi4, htake]
        have hir : i.val < ds.reverse.length := by rw [List.length_reverse]; exact hi_m
        rw [vi5, List.take_succ_eq_append_getElem hir, ← List.cons_append]
        congr 2
        have hb_rev : UInt8.ofBitVec b_rev.bv = ds.reverse[i.val]'hir := by
          have h1 : UInt8.ofBitVec b_rev.bv = (u8Bytes (tmp1.val.take m)).getD i2.val 0 := by
            rw [u8Bytes_getD, getD_take_lt _ 0#u8 m i2.val (by omega)]
          rw [h1, htmp1_ds]
          have h2 : i2.val = ds.length - 1 - i.val := by dsimp only [m] at *; omega
          rw [h2, getD_reverse_lt ds i.val hi_m]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hir, Option.getD_some]
        exact congrArg (· :: []) hb_rev
    obtain ⟨out1, hloop1_fuel, hout1_q⟩ :=
      loopFuel_total_rank body1 P1 Q1 hz1 step1 m (a0, 0#usize)
        ⟨Nat.zero_add _, by
          change u8Bytes (a0.val.take 1) = [UInt8.ofNat m]
          change u8Bytes ((out0.val.set 0 hdrByte).take 1) = [UInt8.ofNat m]
          have hset0 : (out0.val.set 0 hdrByte).take 1 = [hdrByte] := rfl
          rw [hset0]
          exact congrArg (· :: []) hhdr_u8⟩
    have hloop1 : keccak.sp800_185_left_encode_u128_loop1 tmp1 n1 a0 0#usize = .ok out1 := by
      unfold keccak.sp800_185_left_encode_u128_loop1
      exact loop_ok_of_loopFuel (fuel := m + 1)
        (Nat.le_trans (show m + 1 ≤ 17 by omega) (by decide)) hloop1_fuel
    obtain ⟨total_n, htot, vtot⟩ := checked_add_val 1#usize n1
      (by change 1 + n1.val < 2 ^ 64; omega)
    change total_n.val = 1 + n1.val at vtot
    dsimp only [tmp0] at hloop0
    dsimp only [out0, hdrByte] at hupd_a0
    refine ⟨out1, total_n, ?_, by omega, ?_⟩
    · simp only [keccak.sp800_185_left_encode_u128, hv0, ite_false, hloop0, hupd_a0,
        hloop1, htot, bind_eq_result_bind, result_bind_ok, lift_eq_ok]
    · rw [vtot, hn1_m, hout1_q, hleft]

private theorem new_cshake256_loop0_refines
    (s : keccak.Shake256Sponge) (len_enc : Array Std.U8 17#usize) (n : Std.Usize)
    (msg : List UInt8) (hn : n.val ≤ 17) (habs : SpongeAbsorbed s msg) :
    ∃ s', keccak.Shake256Sponge.new_cshake256_loop0 s len_enc n 0#usize = .ok s' ∧
      SpongeAbsorbed s' (msg ++ u8Bytes (len_enc.val.take n.val)) ∧
      s'.suffix = s.suffix := by
  let body := fun (st, j) => keccak.Shake256Sponge.new_cshake256_loop0.body len_enc n st j
  let P := fun (rem : Nat) (x : keccak.Shake256Sponge × Std.Usize) =>
    x.2.val + rem = n.val ∧
    SpongeAbsorbed x.1 (msg ++ u8Bytes (len_enc.val.take x.2.val)) ∧
    x.1.suffix = s.suffix
  let Q := fun (st : keccak.Shake256Sponge) =>
    SpongeAbsorbed st (msg ++ u8Bytes (len_enc.val.take n.val)) ∧ st.suffix = s.suffix
  have hz : ∀ x, P 0 x → ∃ y, body x = .ok (.done y) ∧ Q y := by
    rintro ⟨st, j⟩ ⟨hj, hI, hsfx⟩
    dsimp only at hj hI hsfx
    have hjn : j.val = n.val := by omega
    have hnlt : ¬ (j < n) := by change ¬ j.val < n.val; omega
    refine ⟨st, ?_, hjn ▸ hI, hsfx⟩
    simp only [body, keccak.Shake256Sponge.new_cshake256_loop0.body, hnlt, ite_false]
  have step : ∀ rem x, P (rem + 1) x → ∃ x', body x = .ok (.cont x') ∧ P rem x' := by
    rintro rem ⟨st, j⟩ ⟨hj, hI, hsfx⟩
    dsimp only at hj hI hsfx
    have hj_n : j.val < n.val := by omega
    have hj_17 : j.val < 17 := by omega
    have hlt_n : j < n := hj_n
    have hj_len : j.val < len_enc.val.length := by rw [len_enc.property]; exact hj_17
    have hidx : Array.index_usize len_enc j = .ok (len_enc.val[j.val]'hj_len) := by
      have hg := array_index_getD len_enc j 0#u8 hj_17
      rw [hg]
      simp [List.getD_eq_getElem?_getD, hj_len]
    let sl := Array.to_slice (Array.make 1#usize [len_enc.val[j.val]'hj_len])
    obtain ⟨st', hst', habs', hsfx'⟩ := sponge_absorb_refines st sl _ hI
    obtain ⟨j1, hj1, vj1⟩ := checked_add_val j 1#usize (by change j.val + 1 < 2 ^ 64; omega)
    change j1.val = j.val + 1 at vj1
    dsimp only [sl] at hst'
    refine ⟨(st', j1), ?_, ?_, ?_, hsfx'.trans hsfx⟩
    · simp only [body, keccak.Shake256Sponge.new_cshake256_loop0.body, hlt_n, ite_true,
        hidx, hst', hj1, bind_eq_result_bind, result_bind_ok, lift_eq_ok]
    · change j1.val + rem = n.val; omega
    · change SpongeAbsorbed st' (msg ++ u8Bytes (len_enc.val.take j1.val))
      rw [vj1, List.take_succ_eq_append_getElem hj_len, u8Bytes_append, ← List.append_assoc]
      exact habs'
  obtain ⟨s', hloop_fuel, habs', hsfx'⟩ :=
    loopFuel_total_rank body P Q hz step n.val (s, 0#usize)
      ⟨Nat.zero_add _, by
        change SpongeAbsorbed s (msg ++ [])
        rw [List.append_nil]
        exact habs, rfl⟩
  refine ⟨s', ?_, habs', hsfx'⟩
  unfold keccak.Shake256Sponge.new_cshake256_loop0
  exact loop_ok_of_loopFuel (fuel := n.val + 1)
    (Nat.le_trans (show n.val + 1 ≤ 18 by omega) (by decide)) hloop_fuel

private theorem customizationPrefix_eq_of_z (cust : List UInt8) :
    let z := [1, 136, 1, 0] ++ Qsag.leftEncode (8 * cust.length) ++ cust
    Qsag.customizationPrefix cust =
      z ++ List.replicate ((136 - z.length % 136) % 136) 0 := by
  intro z
  have h136 : Qsag.leftEncode 136 = [1, 136] := by
    rw [Qsag.leftEncode_eq, natBytesBE_eq_digits]
    decide
  have hemp : Qsag.encodeString [] = [1, 0] := by
    rw [Qsag.encodeString_eq, Qsag.leftEncode_eq, natBytesBE_eq_digits]
    decide
  rw [Qsag.customizationPrefix_eq, Qsag.bytepad_eq]
  have hw : ¬ (136 : Nat) = 0 := by decide
  rw [ite_eq_right hw, h136, hemp, Qsag.encodeString_eq]
  dsimp only []
  have hz_eq : ([1, 136] : List UInt8) ++ ([1, 0] ++ (Qsag.leftEncode (8 * cust.length) ++ cust)) =
      z := by
    simp only [z, List.cons_append, List.nil_append, List.append_assoc]
  rw [hz_eq]

/-- For every nonempty customization, of any length, `new_cshake256` succeeds, has absorbed
exactly the `bytepad` prefix `Qsag.customizationPrefix` (which may span several rate blocks),
and carries domain suffix `0x04`. -/
theorem sponge_new_cshake256_nonempty_absorbed (customization : Slice Std.U8)
    (hLo : 1 ≤ customization.val.length) :
    ∃ sp0, keccak.Shake256Sponge.new_cshake256 customization = .ok sp0 ∧
      SpongeAbsorbed sp0 (Qsag.customizationPrefix (u8Bytes customization.val)) ∧
      sp0.suffix = 4#u8 := by
  have hne : customization.val.isEmpty = false := by
    cases h : customization.val with
    | nil => rw [h] at hLo; exact absurd hLo (by decide)
    | cons _ _ => rfl
  let initSp : keccak.Shake256Sponge :=
    { state := Array.repeat 25#usize 0#u64
      buf := Array.repeat 136#usize 0#u8
      buf_len := 0#usize
      suffix := 4#u8
      squeezing := false
      squeeze_offset := 0#usize }
  have hInit : SpongeAbsorbed initSp [] := by
    refine ⟨rfl, [], [], 0, rfl, rfl, rfl, by decide, ?_, rfl⟩
    rw [Qsag.absorbBlocks_zero, Qsag.zeroKState_eq]
    rfl
  let hdr := Array.to_slice (Array.make 4#usize [1#u8, 136#u8, 1#u8, 0#u8])
  obtain ⟨s1, hs1, habs1, hsfx1⟩ := sponge_absorb_refines initSp hdr [] hInit
  have hhdr : [] ++ u8Bytes hdr.val = [1, 136, 1, 0] := rfl
  rw [hhdr] at habs1
  let lenU := Slice.len customization
  let len128 := UScalar.cast .U128 lenU
  have hlen_lt : customization.val.length < 2 ^ 64 := by
    rw [← Slice.len_val customization]
    exact lenU.bv.isLt
  have hlen128_val : len128.val = customization.val.length := by
    have h128 : lenU.val < 2 ^ 128 := Nat.lt_trans lenU.bv.isLt (by decide)
    change (lenU.bv.setWidth 128).toNat = customization.val.length
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h128, Slice.len_val]
  obtain ⟨bit_len, hmul, vbit⟩ := checked_mul_val len128 8#u128 (by
    change len128.val * 8 < 2 ^ 128
    rw [hlen128_val]
    have hb : (2 : Nat) ^ 64 * 8 < 2 ^ 128 := by decide
    omega)
  change bit_len.val = len128.val * 8 at vbit
  have hbit_eq : bit_len.val = 8 * customization.val.length := by rw [vbit, hlen128_val]; omega
  obtain ⟨len_enc, len_enc_bytes, hle, hle_bound, hle_bytes⟩ :=
    sp800_185_left_encode_u128_refines bit_len
  rw [hbit_eq] at hle_bytes
  obtain ⟨s2, hloop0, habs2, hsfx2⟩ :=
    new_cshake256_loop0_refines s1 len_enc len_enc_bytes [1, 136, 1, 0] hle_bound habs1
  rw [hle_bytes] at habs2
  obtain ⟨s3, hs3, habs3, hsfx3⟩ := sponge_absorb_refines s2 customization _ habs2
  let custB := u8Bytes customization.val
  have hcust_len : custB.length = customization.val.length := u8Bytes_length _
  let z := [1, 136, 1, 0] ++ Qsag.leftEncode (8 * custB.length) ++ custB
  have hz_eq : ([1, 136, 1, 0] ++ Qsag.leftEncode (8 * customization.val.length)) ++
      u8Bytes customization.val = z := by
    simp only [z, custB, hcust_len]
  rw [hz_eq] at habs3
  have hcpre_eq : Qsag.customizationPrefix custB =
      z ++ List.replicate ((136 - z.length % 136) % 136) 0 :=
    customizationPrefix_eq_of_z custB
  obtain ⟨hsq3, hbl3, hst3, htake3⟩ := habs3.canonical
  dsimp only [initSp, hdr] at hs1
  dsimp only [lenU, len128] at hmul
  by_cases hrem0 : s3.buf_len.val = 0
  · -- Exact rate-block multiple (`z.length % 136 = 0`): no trailing zero pad needed
    have hng0 : ¬ (s3.buf_len > 0#usize) := by change ¬ 0 < s3.buf_len.val; omega
    have hzmod0 : z.length % 136 = 0 := hbl3.symm.trans hrem0
    have hpad0 : (136 - z.length % 136) % 136 = 0 := by rw [hzmod0]
    have hcpre_z : Qsag.customizationPrefix custB = z := by
      rw [hcpre_eq, hpad0, List.replicate_zero, List.append_nil]
    refine ⟨s3, ?_, hcpre_z ▸ habs3, hsfx3.trans (hsfx2.trans hsfx1)⟩
    simp only [keccak.Shake256Sponge.new_cshake256, core.slice.Slice.is_empty, hne,
      Bool.false_eq_true, ite_false, hs1, hmul, hle, hloop0, hs3, hng0,
      bind_eq_result_bind, result_bind_ok, lift_eq_ok]
  · -- Partial final block (`0 < z.length % 136 < 136`): zero-pad and permute once more
    have hgt0 : s3.buf_len > 0#usize := by change 0 < s3.buf_len.val; omega
    have hmod_lt : z.length % 136 < 136 := Nat.mod_lt _ (by decide)
    have hlt136 : s3.buf_len < keccak.SHAKE256_RATE_BYTES := by
      unfold keccak.SHAKE256_RATE_BYTES
      change s3.buf_len.val < 136; omega
    obtain ⟨a2, hloop1, ha2⟩ := new_cshake256_loop1_eq s3.buf s3.buf_len (by omega)
    let q := z.length / 136
    let full := z.take (136 * q)
    have hfull_len : full.length = 136 * q := by
      rw [List.length_take]
      have hle_z : 136 * q ≤ z.length := Nat.mul_div_le z.length 136
      exact Nat.min_eq_left hle_z
    have hz_split : z = full ++ z.drop (136 * q) := (List.take_append_drop (136 * q) z).symm
    have hpad_len : (136 - z.length % 136) % 136 = 136 - s3.buf_len.val := by
      rw [← hbl3]
      exact Nat.mod_eq_of_lt (by omega)
    have hu8_a2 : u8Bytes a2.val =
        z.drop (136 * q) ++ List.replicate (136 - s3.buf_len.val) 0 := by
      rw [ha2, u8Bytes_append, u8Bytes_take, htake3, u8Bytes_replicate_zero]
    have ha2_len : (u8Bytes a2.val).length = 136 := by
      rw [u8Bytes_length]; exact a2.property
    have hcpre_split : Qsag.customizationPrefix custB = full ++ u8Bytes a2.val := by
      rw [hcpre_eq, hpad_len, hu8_a2, ← List.append_assoc, ← hz_split]
    let sp0 : keccak.Shake256Sponge :=
      { s3 with
        state := keccakArrayOfState
          (Qsag.keccakF1600 (Qsag.xorRate136 (keccakStateOfArray s3.state) (u8Bytes a2.val)))
        buf := a2
        buf_len := 0#usize }
    refine ⟨sp0, ?_, ?_, hsfx3.trans (hsfx2.trans hsfx1)⟩
    · simp only [keccak.Shake256Sponge.new_cshake256, core.slice.Slice.is_empty, hne,
        Bool.false_eq_true, ite_false, hs1, hmul, hle, hloop0, hs3, hgt0, hlt136, ite_true,
        hloop1, keccak_f1600_array_refines_qsag, bind_eq_result_bind, result_bind_ok, lift_eq_ok]
      rw [xor_rate_block_refines, result_bind_ok, keccakStateOfArray_roundtrip]
    · refine ⟨hsq3, full ++ u8Bytes a2.val, [], q + 1,
        by rw [List.append_nil, hcpre_split],
        by rw [List.length_append, hfull_len, ha2_len]; omega,
        rfl, show (0#usize).val < 136 by decide, ?_, rfl⟩
      change keccakStateOfArray (keccakArrayOfState _) = _
      rw [keccakStateOfArray_roundtrip, hst3]
      have hst_full : Qsag.absorbBlocks q Qsag.zeroKState z =
          Qsag.absorbBlocks q Qsag.zeroKState full := by
        conv => lhs; rw [hz_split]
        exact absorbBlocks_append_right q Qsag.zeroKState full _ hfull_len
      rw [hst_full]
      exact (absorbBlocks_append_block q Qsag.zeroKState full (u8Bytes a2.val)
        hfull_len ha2_len).symm

/-- The extracted `cshake256_32` returns `Qsag.cshake256Xof 32`, for every customization
(empty or not) and every input. -/
theorem cshake256_32_refines (customization input : Slice Std.U8) :
    ∃ out, keccak.cshake256_32 customization input = .ok out ∧
      u8Bytes out.val = Qsag.cshake256Xof 32 (u8Bytes customization.val) (u8Bytes input.val) := by
  by_cases hemp : customization.val.isEmpty
  · have hnil : customization.val = [] := List.isEmpty_iff.mp hemp
    have hcust_eq : customization = ⟨[], by decide⟩ := by
      cases customization
      subst hnil
      rfl
    subst hcust_eq
    exact cshake256_32_empty_refines input
  · have hLo : 1 ≤ customization.val.length := by
      cases h : customization.val with
      | nil => rw [h] at hemp; exact False.elim (hemp rfl)
      | cons _ _ => exact Nat.succ_pos _
    have hc : u8Bytes customization.val ≠ [] := by
      intro e
      have hl := congrArg List.length e
      rw [u8Bytes_length, List.length_nil] at hl
      omega
    obtain ⟨sp0, hnew, hpre, hsfx⟩ := sponge_new_cshake256_nonempty_absorbed customization hLo
    exact cshake256_32_refines_of_prefix customization input hc sp0 hnew hpre hsfx

/-- cSHAKE256 end to end: for every customization, any split of the input into `chunks` and
a destination of any length, the first squeeze yields `Qsag.cshake256Xof out.val.length`. -/
theorem cshake256_squeeze_refines (customization : Slice Std.U8)
    (chunks : List (Slice Std.U8)) (out : Slice Std.U8) :
    ∃ sp0 sp1 sp3 dst,
      keccak.Shake256Sponge.new_cshake256 customization = .ok sp0 ∧
      spongeAbsorbAll sp0 chunks = .ok sp1 ∧
      keccak.Shake256Sponge.squeeze sp1 out = .ok (sp3, dst) ∧
      u8Bytes dst.val = Qsag.cshake256Xof out.val.length
        (u8Bytes customization.val) (chunks.map fun d => u8Bytes d.val).flatten := by
  by_cases hemp : customization.val.isEmpty
  · have hnil : customization.val = [] := List.isEmpty_iff.mp hemp
    have hu8_nil : u8Bytes customization.val = [] := by rw [hnil]; rfl
    obtain ⟨sp0, sp1, sp3, dst, h0, h1, hsq, hbytes⟩ := shake256_squeeze_refines chunks out
    refine ⟨sp0, sp1, sp3, dst, ?_, h1, hsq, ?_⟩
    · simp only [keccak.Shake256Sponge.new_cshake256, core.slice.Slice.is_empty, hemp,
        ite_true, bind_eq_result_bind, result_bind_ok, h0]
    · rw [hu8_nil, Qsag.cshake256Xof_empty_eq_shake256Xof]
      exact hbytes
  · have hLo : 1 ≤ customization.val.length := by
      cases h : customization.val with
      | nil => rw [h] at hemp; exact False.elim (hemp rfl)
      | cons _ _ => exact Nat.succ_pos _
    have hc : u8Bytes customization.val ≠ [] := by
      intro e
      have hl := congrArg List.length e
      rw [u8Bytes_length, List.length_nil] at hl
      omega
    obtain ⟨sp0, hnew, hpre, hsfx⟩ := sponge_new_cshake256_nonempty_absorbed customization hLo
    obtain ⟨sp1, sp2, h1, h2, hxof, hsq2, hoff2⟩ :=
      cshake256_absorb_pad_refines (u8Bytes customization.val) hc sp0 hpre hsfx chunks
    obtain ⟨sp3, dst, hsqueeze, hbytes⟩ := sponge_squeeze_refines sp2 out hsq2 hoff2
    have hloop : keccak.Shake256Sponge.squeeze_loop sp2 out 0#usize = .ok (sp3, dst) := by
      simpa only [keccak.Shake256Sponge.squeeze, keccak.Shake256Sponge.finalize,
        hsq2, ite_true, bind_eq_result_bind, result_bind_ok] using hsqueeze
    refine ⟨sp0, sp1, sp3, dst, hnew, h1, ?_, ?_⟩
    · simp only [keccak.Shake256Sponge.squeeze, h2, bind_eq_result_bind, result_bind_ok, hloop]
    · rw [hbytes, ← hxof out.val.length]

/-- Byte 136 of the stream comes from the permuted state, not from a wrap-around onto the
first rate block (`0xbd ≠ 0x00` from the zero state). -/
theorem tooth_multiblock_squeeze_permuted_beyond_136 :
    (Qsag.squeezeXofAux 137 Qsag.zeroKState).getD 136 0 ≠
      (Qsag.rateBlockBytes Qsag.zeroKState).getD 0 0 :=
  Qsag.squeezeXofAux_zero_byte136_ne_byte0

end qsag_verified.proofs

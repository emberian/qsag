module
import all QsagVerified.Funs
public import QsagVerified.Proofs.SpongeConformance
import all Qsag.Keccak
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
  simp only [Qsag.loadLe64, u8Bytes_getD, hoff]
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
  simp only [keccak.Shake256Sponge.absorb, hsq, Bool.false_eq_true, ite_false,
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
state `Qsag.cshake256Xof` squeezes from. That `new_cshake256` establishes the hypothesis
(`left_encode`, `bytepad` and the prefix flush) is not proved here. -/
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
  rw [BitVec.and_allOnes]
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
  all_goals simp [Qsag.rateBlockBytes, Qsag.laneBytesLE, keccakStateOfArray,
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
    simp [Qsag.squeezeXofAux, Qsag.squeezeXofFuel, List.getD_eq_getElem?_getD, hj32]

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

/-- cSHAKE's byte-output weld, conditional only on the constructor establishing the
SP 800-185 prefix. The constructor's encoding and bytepad proof remains separate. -/
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

/-- The pad is sensitive to the domain suffix: SHAKE and cSHAKE final blocks differ. -/
theorem tooth_last_block_suffix_sensitive :
    spongeLastBlock [] 0x1f ≠ spongeLastBlock [] 0x04 := by decide

end qsag_verified.proofs

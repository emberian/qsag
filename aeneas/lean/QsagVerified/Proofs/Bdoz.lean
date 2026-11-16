module
import all QsagVerified.Funs

public import QsagVerified.Proofs.Sponge
public import QsagVerified.Proofs.TowerBdoz

public section
namespace qsag_verified.proofs
open Aeneas Aeneas.Std Result ControlFlow Error qsag_verified
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
attribute [local simp] UScalar.val UScalarTy.numBits

private theorem sponge_absorb_block (sp : keccak.Shake256Sponge) (data : Slice Std.U8)
    (hn : sp.squeezing = false) (hbuf : sp.buf_len.val < 136)
    (hb : sp.buf_len.val + data.val.length = 136) :
    ∃ out, keccak.Shake256Sponge.absorb sp data = .ok out ∧
      out.squeezing = false ∧ out.buf_len.val = 0 := by
  let body := fun (a, buf, i, pos) => keccak.Shake256Sponge.absorb_loop.body data a buf i pos
  let P := fun (n : Nat) (x : Std.Array Std.U64 25#usize × Std.Array Std.U8 136#usize × Std.Usize × Std.Usize) =>
    x.2.2.2.val + n = data.val.length ∧
      (if n = 0 then x.2.2.1.val = 0 else x.2.2.1.val + n = 136)
  let Q := fun (x : Std.Array Std.U64 25#usize × Std.Array Std.U8 136#usize × Std.Usize) => x.2.2.val = 0
  have hz : ∀ x, P 0 x → ∃ y, body x = .ok (.done y) ∧ Q y := by
    rintro ⟨a, buf, i, pos⟩ ⟨hp, hi⟩
    have he : ¬ pos < Slice.len data := by
      change ¬ pos.val < (Slice.len data).val
      rw [Slice.len_val, ← hp, Nat.add_zero]
      exact Nat.lt_irrefl _
    exact ⟨(a, buf, i), by simp only [body, keccak.Shake256Sponge.absorb_loop.body, he, ite_false], hi⟩
  have step : ∀ n x, P (n + 1) x → ∃ x', body x = .ok (.cont x') ∧ P n x' := by
    rintro n ⟨a, buf, i, pos⟩ ⟨hp, hi⟩
    change pos.val + (n + 1) = data.val.length at hp
    change (if n + 1 = 0 then i.val = 0 else i.val + (n + 1) = 136) at hi
    simp only [Nat.add_one_ne_zero, ite_false] at hi
    have hpos : pos < Slice.len data := by
      change pos.val < (Slice.len data).val
      rw [Slice.len_val]
      exact rank_lt hp
    have hib : i.val < 136 := rank_lt hi
    have hilt : i < keccak.SHAKE256_RATE_BYTES := by
      unfold keccak.SHAKE256_RATE_BYTES
      exact hib
    obtain ⟨v, hv⟩ := slice_index_total data pos (rank_lt hp)
    obtain ⟨buf', hbuf'⟩ := array_update_total buf i v hib
    obtain ⟨i', hi', vi'⟩ := checked_add_val i 1#usize
      (by change i.val + 1 < 2 ^ 64; exact Nat.lt_of_le_of_lt (rank_succ_le hi) (by decide))
    obtain ⟨pos', hp', vp'⟩ := checked_add_val pos 1#usize (by
      change pos.val + 1 < 2 ^ 64
      exact Nat.lt_of_le_of_lt (rank_succ_le hp) (by simpa only [← Slice.len_val] using (Slice.len data).bv.isLt))
    change i'.val = i.val + 1 at vi'
    change pos'.val = pos.val + 1 at vp'
    by_cases hzero : n = 0
    · subst n
      have he : i' = keccak.SHAKE256_RATE_BYTES := by
        apply UScalar.eq_of_val_eq
        rw [vi', keccak.SHAKE256_RATE_BYTES]
        exact hi
      obtain ⟨a', ha'⟩ := xor_rate_block_total a buf'
      obtain ⟨a'', ha''⟩ := keccak_f1600_total a'
      refine ⟨(a'', buf', 0#usize, pos'), ?_, ?_⟩
      · simp only [body, keccak.Shake256Sponge.absorb_loop.body, hpos, hilt, ite_true,
          hv, hbuf', hi', hp', he, ha', ha'', bind_eq_result_bind, result_bind_ok]
      · constructor
        · change pos'.val + 0 = data.val.length
          rw [vp']; exact rank_next hp
        · rfl
    · have hsmall : i'.val < 136 := by
        rw [vi', ← rank_next hi]
        exact Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hzero)
      have he : i' ≠ keccak.SHAKE256_RATE_BYTES := by
        intro he
        have hv := congrArg UScalar.val he
        rw [keccak.SHAKE256_RATE_BYTES] at hv
        change i'.val = 136 at hv
        rw [hv] at hsmall
        exact Nat.lt_irrefl _ hsmall
      refine ⟨(a, buf', i', pos'), ?_, ?_⟩
      · simp only [body, keccak.Shake256Sponge.absorb_loop.body, hpos, hilt, ite_true,
          hv, hbuf', hi', hp', he, ite_false, bind_eq_result_bind, result_bind_ok]
      · constructor
        · change pos'.val + n = data.val.length
          rw [vp']; exact rank_next hp
        · change (if n = 0 then i'.val = 0 else i'.val + n = 136)
          rw [ite_eq_right hzero, vi']; exact rank_next hi
  have hnonempty : data.val.length ≠ 0 := by
    intro he
    rw [he, Nat.add_zero] at hb
    exact Nat.ne_of_lt hbuf hb
  obtain ⟨⟨a, buf, i⟩, hloop, hi⟩ := loopFuel_total_rank body P Q hz step data.val.length
    (sp.state, sp.buf, sp.buf_len, 0#usize)
    ⟨Nat.zero_add _, by change (if data.val.length = 0 then _ else _); rw [ite_eq_right hnonempty]; exact hb⟩
  have hactual : keccak.Shake256Sponge.absorb_loop sp.state sp.buf sp.buf_len data 0#usize = .ok (a, buf, i) := by
    unfold keccak.Shake256Sponge.absorb_loop
    apply loop_ok_of_loopFuel (fuel := data.val.length + 1)
    · simpa only [Slice.len_val] using usize_lt_loopMaxFuel (Slice.len data)
    · exact hloop
  refine ⟨{ sp with state := a, buf := buf, buf_len := i }, ?_, hn, hi⟩
  simp only [keccak.Shake256Sponge.absorb, massert_not_of_eq_false hn,
    hactual, bind_eq_result_bind, result_bind_ok]

private theorem bdoz_commit_total (sid : Std.Array Std.U8 32#usize) (round : Std.U64)
    (sum : tower.Tower128) (macs : Std.Array tower.Tower128 2#usize)
    (nonce : Std.Array Std.U8 32#usize) :
    ∃ tag, tower.bdoz_commit_masked_tag sid round sum macs nonce = .ok tag := by
  obtain ⟨roundBytes, hr⟩ : ∃ b, tower.encode_le_u64 round = .ok b := ⟨_, rfl⟩
  obtain ⟨sumBytes, hs⟩ : ∃ b, tower.encode_le_u128 sum = .ok b := ⟨_, rfl⟩
  obtain ⟨mac0, hm0⟩ := array_index_total macs 0#usize (by decide)
  obtain ⟨mac1, hm1⟩ := array_index_total macs 1#usize (by decide)
  obtain ⟨mac0Bytes, hmb0⟩ : ∃ b, tower.encode_le_u128 mac0 = .ok b := ⟨_, rfl⟩
  obtain ⟨mac1Bytes, hmb1⟩ : ∃ b, tower.encode_le_u128 mac1 = .ok b := ⟨_, rfl⟩
  let domain := Std.Array.make 16#usize [81#u8, 83#u8, 65#u8, 71#u8, 46#u8, 66#u8, 68#u8, 79#u8, 90#u8, 46#u8, 77#u8, 65#u8, 67#u8, 50#u8, 76#u8, 1#u8]
  let sp0 : keccak.Shake256Sponge :=
    ⟨Std.Array.repeat 25#usize 0#u64, Std.Array.repeat 136#usize 0#u8,
      0#usize, 31#u8, false, 0#usize⟩
  have hnew : keccak.Shake256Sponge.new_shake256 = .ok sp0 := rfl
  have hlen1 : (Std.Array.to_slice domain).val.length = 16 := domain.property
  obtain ⟨sp1, hsp1, hn1, hv1⟩ := sponge_absorb_short sp0 (Std.Array.to_slice domain) rfl (by change 0 + (Std.Array.to_slice domain).val.length < 136; rw [hlen1]; decide)
  have v1 : sp1.buf_len.val = 16 := by
    change sp1.buf_len.val = 0 + (Std.Array.to_slice domain).val.length at hv1
    simpa only [hlen1] using hv1
  have hlen2 : (Std.Array.to_slice sid).val.length = 32 := sid.property
  obtain ⟨sp2, hsp2, hn2, hv2⟩ := sponge_absorb_short sp1 (Std.Array.to_slice sid) hn1 (by rw [v1, hlen2]; decide)
  have v2 : sp2.buf_len.val = 48 := by simpa only [v1, hlen2] using hv2
  have hlen3 : (Std.Array.to_slice roundBytes).val.length = 8 := roundBytes.property
  obtain ⟨sp3, hsp3, hn3, hv3⟩ := sponge_absorb_short sp2 (Std.Array.to_slice roundBytes) hn2 (by rw [v2, hlen3]; decide)
  have v3 : sp3.buf_len.val = 56 := by simpa only [v2, hlen3] using hv3
  have hlen4 : (Std.Array.to_slice sumBytes).val.length = 16 := sumBytes.property
  obtain ⟨sp4, hsp4, hn4, hv4⟩ := sponge_absorb_short sp3 (Std.Array.to_slice sumBytes) hn3 (by rw [v3, hlen4]; decide)
  have v4 : sp4.buf_len.val = 72 := by simpa only [v3, hlen4] using hv4
  have hlen5 : (Std.Array.to_slice mac0Bytes).val.length = 16 := mac0Bytes.property
  obtain ⟨sp5, hsp5, hn5, hv5⟩ := sponge_absorb_short sp4 (Std.Array.to_slice mac0Bytes) hn4 (by rw [v4, hlen5]; decide)
  have v5 : sp5.buf_len.val = 88 := by simpa only [v4, hlen5] using hv5
  have hlen6 : (Std.Array.to_slice mac1Bytes).val.length = 16 := mac1Bytes.property
  obtain ⟨sp6, hsp6, hn6, hv6⟩ := sponge_absorb_short sp5 (Std.Array.to_slice mac1Bytes) hn5 (by rw [v5, hlen6]; decide)
  have v6 : sp6.buf_len.val = 104 := by simpa only [v5, hlen6] using hv6
  have hnlen : (Std.Array.to_slice nonce).val.length = 32 := nonce.property
  obtain ⟨sp7, hsp7, hn7, hv7⟩ := sponge_absorb_block sp6 (Std.Array.to_slice nonce) hn6
    (by rw [v6]; decide) (by rw [v6, hnlen])
  let out := Std.Array.repeat 32#usize 0#u8
  obtain ⟨result, hresult⟩ := sponge_squeeze_short sp7 (Std.Array.to_slice_mut out).1 32 (by decide) hn7
    (by rw [hv7]; decide) (by rfl)
  dsimp only [domain] at hsp1
  unfold tower.bdoz_commit_masked_tag
  simp only [hr, hs, hm0, hm1, hmb0, hmb1, hnew, hsp1, hsp2, hsp3, hsp4, hsp5, hsp6, hsp7,
    bind_eq_result_bind, result_bind_ok, lift_eq_ok]
  rw [hresult, result_bind_ok]
  exact ⟨_, rfl⟩

private theorem result_bind_ite {α β : Type} (c : Prop) [Decidable c]
    (x y : Result α) (f : α → Result β) :
    (if c then x >>= f else y >>= f) = ((if c then x else y) >>= f) :=
  (apply_ite (fun z => z >>= f) c x y).symm

set_option maxHeartbeats 100000 in
private theorem bdoz_loop_total (openings : Slice tower.BdozWireOpening2Lane)
    (weight : Std.U8) (sum key0 key1 : tower.Tower128) :
    ∃ out, tower.verify_mac_2lane_loop openings weight sum key0 key1 0#usize = .ok out := by
  let body := fun (w, s, k0, k1, i) => tower.verify_mac_2lane_loop.body openings w s k0 k1 i
  let P := fun (n : Nat) (x : Std.U8 × tower.Tower128 × tower.Tower128 × tower.Tower128 × Std.Usize) =>
    x.2.2.2.2.val + n = openings.val.length
  have hz : ∀ x, P 0 x → ∃ y, body x = .ok (.done y) ∧ True := by
    rintro ⟨w, v, k0, k1, i⟩ hi
    have hn : ¬ i < Slice.len openings := by
      change ¬ i.val < (Slice.len openings).val
      rw [Slice.len_val, ← hi, Nat.add_zero]
      exact Nat.lt_irrefl _
    exact ⟨(w, v, k0, k1), by simp only [body, tower.verify_mac_2lane_loop.body, hn, ite_false], True.intro⟩
  have step : ∀ n x, P (n + 1) x → ∃ x', body x = .ok (.cont x') ∧ P n x' := by
    rintro n ⟨w, v, k0, k1, i⟩ hi
    change i.val + (n + 1) = openings.val.length at hi
    have hlt : i < Slice.len openings := by
      change i.val < (Slice.len openings).val
      rw [Slice.len_val]; exact rank_lt hi
    obtain ⟨item, hitem⟩ := slice_index_total openings i (rank_lt hi)
    obtain ⟨vprod, hv⟩ := tower128_mul_total item.chal_weight (UScalar.cast .U128 item.opened_value)
    obtain ⟨ik0, hik0⟩ := array_index_total item.key_lanes 0#usize (by decide)
    obtain ⟨ik1, hik1⟩ := array_index_total item.key_lanes 1#usize (by decide)
    obtain ⟨kp0, hkp0⟩ := tower128_mul_total item.chal_weight ik0
    obtain ⟨kp1, hkp1⟩ := tower128_mul_total item.chal_weight ik1
    obtain ⟨i', hi', vi'⟩ := checked_add_val i 1#usize (by
      change i.val + 1 < 2 ^ 64
      exact Nat.lt_of_le_of_lt (rank_succ_le hi)
        (by simpa only [← Slice.len_val] using (Slice.len openings).bv.isLt))
    let w' := if item.chal_weight = 0#u128 then 0#u8 else w
    refine ⟨(w', v ^^^ vprod, k0 ^^^ kp0, k1 ^^^ kp1, i'), ?_, ?_⟩
    · simp only [body, tower.verify_mac_2lane_loop.body, hlt, ite_true]
      apply bind_ok_step hitem
      rw [result_bind_ite]
      have hw : (if item.chal_weight = 0#u128 then Result.ok 0#u8 else Result.ok w) = .ok w' :=
        (apply_ite Result.ok _ _ _).symm
      apply bind_ok_step hw
      apply bind_ok_step (show tower.embed_gf256_to_tower128 item.opened_value =
        .ok (UScalar.cast .U128 item.opened_value) from rfl)
      apply bind_ok_step hv
      apply bind_ok_step (show tower.tower128_add v vprod = .ok (v ^^^ vprod) from rfl)
      apply bind_ok_step hik0
      apply bind_ok_step hkp0
      apply bind_ok_step (show tower.tower128_add k0 kp0 = .ok (k0 ^^^ kp0) from rfl)
      apply bind_ok_step hik1
      apply bind_ok_step hkp1
      apply bind_ok_step (show tower.tower128_add k1 kp1 = .ok (k1 ^^^ kp1) from rfl)
      apply bind_ok_step hi'
      rfl
    · change i'.val + n = openings.val.length
      change i'.val = i.val + 1 at vi'
      rw [vi']; exact rank_next hi
  obtain ⟨out, hout, _⟩ := loopFuel_total_rank body P (fun _ => True) hz step openings.val.length
    (weight, sum, key0, key1, 0#usize) (Nat.zero_add _)
  refine ⟨out, ?_⟩
  unfold tower.verify_mac_2lane_loop
  apply loop_ok_of_loopFuel (fuel := openings.val.length + 1)
  · simpa only [Slice.len_val] using usize_lt_loopMaxFuel (Slice.len openings)
  · exact hout

private theorem bind_total_step {α β : Type} {r : Result α} {f : α → Result β}
    {v : α} (hr : r = .ok v) (hf : ∃ out, f v = .ok out) :
    ∃ out, (r >>= f) = .ok out := by
  obtain ⟨out, h⟩ := hf
  exact ⟨out, bind_ok_step hr h⟩

theorem bdoz_verify_total (alphas : Std.Array tower.Tower128 2#usize)
    (batch : tower.BdozCommittedBatchOpening2Lane) (openings : Slice tower.BdozWireOpening2Lane) :
    ∃ accepted, tower.verify_mac_2lane alphas batch openings = .ok accepted := by
  obtain ⟨mk0, hmk0⟩ := array_index_total batch.mask_key_lanes 0#usize (by decide)
  obtain ⟨mk1, hmk1⟩ := array_index_total batch.mask_key_lanes 1#usize (by decide)
  obtain ⟨⟨w, sum, k0, k1⟩, hloop⟩ := bdoz_loop_total openings 1#u8 batch.mask_value mk0 mk1
  obtain ⟨tag, htag⟩ := bdoz_commit_total batch.session_id batch.round_id sum batch.peer_masked_mac_lanes batch.open_nonce
  obtain ⟨a0, ha0⟩ := array_index_total alphas 0#usize (by decide)
  obtain ⟨a1, ha1⟩ := array_index_total alphas 1#usize (by decide)
  obtain ⟨p0, hp0⟩ := tower128_mul_total a0 sum
  obtain ⟨p1, hp1⟩ := tower128_mul_total a1 sum
  obtain ⟨m0, hm0⟩ := array_index_total batch.peer_masked_mac_lanes 0#usize (by decide)
  obtain ⟨m1, hm1⟩ := array_index_total batch.peer_masked_mac_lanes 1#usize (by decide)
  unfold tower.verify_mac_2lane
  simp only [core.slice.Slice.is_empty, bind_eq_result_bind, result_bind_ok]
  split
  · exact ⟨_, rfl⟩
  · apply bind_total_step hmk0
    apply bind_total_step hmk1
    apply bind_total_step hloop
    apply bind_total_step htag
    apply bind_total_step (ct_eq_bytes32_spec tag batch.tag_commitment)
    apply bind_total_step ha0
    apply bind_total_step hp0
    apply bind_total_step (show tower.tower128_add k0 p0 = .ok (k0 ^^^ p0) from rfl)
    apply bind_total_step ha1
    apply bind_total_step hp1
    apply bind_total_step (show tower.tower128_add k1 p1 = .ok (k1 ^^^ p1) from rfl)
    apply bind_total_step hm0
    apply bind_total_step (lift_eq_ok _)
    apply bind_total_step hm1
    apply bind_total_step (lift_eq_ok _)
    split
    · split <;> exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

theorem bdoz_authenticate_open_total (session : tower.BdozVerifierSession2Lane)
    (batch : tower.BdozCommittedBatchOpening2Lane) (openings : Slice tower.BdozWireOpening2Lane) :
    ∃ session' accepted, tower.verify_mac_2lane_with_burn session batch openings = .ok (session', accepted) := by
  obtain ⟨accepted, hr⟩ := bdoz_verify_total session.alpha_lanes batch openings
  unfold tower.verify_mac_2lane_with_burn
  rw [hr]
  cases session.burned <;> cases accepted <;> exact ⟨_, _, rfl⟩

theorem bdoz_mac_one_time_burn_spec (session : tower.BdozVerifierSession2Lane)
    (batch : tower.BdozCommittedBatchOpening2Lane) (openings : Slice tower.BdozWireOpening2Lane) :
    ∃ session' accepted,
      tower.verify_mac_2lane_with_burn session batch openings = .ok (session', accepted) ∧
      ((accepted = false ∨ session.burned = true) →
        session'.burned = true ∧ session'.alpha_lanes = Std.Array.make 2#usize [0#u128, 0#u128] ∧
        ∀ batch' openings', tower.verify_mac_2lane_with_burn session' batch' openings' =
          .ok (⟨Std.Array.make 2#usize [0#u128, 0#u128], true⟩, false)) := by
  obtain ⟨session', accepted, hr⟩ := bdoz_authenticate_open_total session batch openings
  refine ⟨session', accepted, hr, ?_⟩
  intro trigger
  have hf : session'.burned = true ∧ session'.alpha_lanes = Std.Array.make 2#usize [0#u128, 0#u128] := by
    rcases trigger with h | h
    · subst accepted
      exact (verify_mac_2lane_burn_irreversible session batch openings).2 session' hr
    · have hz := (verify_mac_2lane_burn_irreversible session batch openings).1 h
      rw [hr] at hz
      cases hz
      exact ⟨rfl, rfl⟩
  exact ⟨hf.1, hf.2, fun batch' openings' =>
    (verify_mac_2lane_burn_irreversible session' batch' openings').1 hf.1⟩

private theorem tower128_mul_eq_pure (a b : tower.Tower128) :
    tower.tower128_mul a b = .ok (pureTower128Mul a b) :=
  tower128_mul_eq_independent a b

@[expose]
def bdozMaskedSum (batch : tower.BdozCommittedBatchOpening2Lane) (item : tower.BdozWireOpening2Lane) : tower.Tower128 :=
  batch.mask_value ^^^ pureTower128Mul item.chal_weight (UScalar.cast .U128 item.opened_value)

@[expose]
def bdozFoldedKey (batch : tower.BdozCommittedBatchOpening2Lane) (item : tower.BdozWireOpening2Lane) (lane : Nat) : tower.Tower128 :=
  batch.mask_key_lanes.val.getD lane 0#u128 ^^^ pureTower128Mul item.chal_weight (item.key_lanes.val.getD lane 0#u128)

@[expose]
def bdozExpectedMacLanes (session : tower.BdozVerifierSession2Lane)
    (batch : tower.BdozCommittedBatchOpening2Lane) (item : tower.BdozWireOpening2Lane) : Std.Array tower.Tower128 2#usize :=
  Std.Array.make 2#usize [
    bdozFoldedKey batch item 0 ^^^ pureTower128Mul (session.alpha_lanes.val.getD 0 0#u128) (bdozMaskedSum batch item),
    bdozFoldedKey batch item 1 ^^^ pureTower128Mul (session.alpha_lanes.val.getD 1 0#u128) (bdozMaskedSum batch item)]

abbrev bdozOpening1 (item : tower.BdozWireOpening2Lane) : Slice tower.BdozWireOpening2Lane :=
  Std.Array.to_slice (Std.Array.make 1#usize [item])

private theorem bdoz_loop_one (item : tower.BdozWireOpening2Lane) (mask k0 k1 : tower.Tower128) :
    tower.verify_mac_2lane_loop (bdozOpening1 item) 1#u8 mask k0 k1 0#usize =
      .ok (if item.chal_weight = 0#u128 then 0#u8 else 1#u8,
        mask ^^^ pureTower128Mul item.chal_weight (UScalar.cast .U128 item.opened_value),
        k0 ^^^ pureTower128Mul item.chal_weight (item.key_lanes.val.getD 0 0#u128),
        k1 ^^^ pureTower128Mul item.chal_weight (item.key_lanes.val.getD 1 0#u128)) := by
  have hk0 := array_index_getD item.key_lanes 0#usize 0#u128 (by decide)
  have hk1 := array_index_getD item.key_lanes 1#usize 0#u128 (by decide)
  unfold tower.verify_mac_2lane_loop
  apply loop_ok_of_loopFuel (fuel := 2) (by decide)
  by_cases hw : item.chal_weight = 0#u128
  all_goals simp [bdozOpening1, Std.Array.to_slice, Std.Array.make, loopFuel, tower.verify_mac_2lane_loop.body, Slice.len, Slice.index_usize,
    hk0, hk1, tower.embed_gf256_to_tower128, tower.tower128_add, tower128_mul_eq_pure, hw]

private theorem mac_lanes_equal (macs : Std.Array tower.Tower128 2#usize) (x y : tower.Tower128) :
    (macs.val.getD 0 0#u128 ^^^ x) ||| (macs.val.getD 1 0#u128 ^^^ y) = 0#u128 ↔
      macs = Std.Array.make 2#usize [x, y] := by
  constructor
  · intro h
    obtain ⟨h0, h1⟩ := BitVec.or_eq_zero_iff.mp (congrArg UScalar.bv h)
    have hx : macs.val.getD 0 0#u128 = x := UScalar.ext (BitVec.xor_eq_zero_iff.mp h0)
    have hy : macs.val.getD 1 0#u128 = y := UScalar.ext (BitVec.xor_eq_zero_iff.mp h1)
    apply Std.Array.ext
    apply List.ext_getElem (by rw [macs.property]; rfl)
    intro i hi hj
    rw [List.getElem_eq_getD 0#u128, List.getElem_eq_getD 0#u128]
    have hb : i < 2 := by rw [macs.property] at hi; exact hi
    match i, hb with
    | 0, _ => exact hx
    | 1, _ => exact hy
    | n + 2, hn => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 2 n) hn)
  · rintro rfl
    apply UScalar.ext
    change (x.bv ^^^ x.bv) ||| (y.bv ^^^ y.bv) = 0#128
    rw [BitVec.xor_self, BitVec.xor_self]
    rfl

private theorem bdoz_verify_one_eq (session : tower.BdozVerifierSession2Lane)
    (batch : tower.BdozCommittedBatchOpening2Lane) (item : tower.BdozWireOpening2Lane)
    (tag : Std.Array Std.U8 32#usize)
    (htag : tower.bdoz_commit_masked_tag batch.session_id batch.round_id (bdozMaskedSum batch item)
      batch.peer_masked_mac_lanes batch.open_nonce = .ok tag) :
    tower.verify_mac_2lane session.alpha_lanes batch (bdozOpening1 item) =
      .ok (decide (item.chal_weight ≠ 0#u128 ∧ tag = batch.tag_commitment ∧
        batch.peer_masked_mac_lanes = bdozExpectedMacLanes session batch item)) := by
  have mk0 := array_index_getD batch.mask_key_lanes 0#usize 0#u128 (by decide)
  have mk1 := array_index_getD batch.mask_key_lanes 1#usize 0#u128 (by decide)
  have a0 := array_index_getD session.alpha_lanes 0#usize 0#u128 (by decide)
  have a1 := array_index_getD session.alpha_lanes 1#usize 0#u128 (by decide)
  have m0 := array_index_getD batch.peer_masked_mac_lanes 0#usize 0#u128 (by decide)
  have m1 := array_index_getD batch.peer_masked_mac_lanes 1#usize 0#u128 (by decide)
  dsimp only [bdozMaskedSum] at htag
  have he : (bdozOpening1 item).val.isEmpty = false := rfl
  unfold tower.verify_mac_2lane
  simp only [core.slice.Slice.is_empty, he, Bool.false_eq_true, ite_false,
    mk0, mk1, bind_eq_result_bind, result_bind_ok]
  rw [bdoz_loop_one]
  simp only [result_bind_ok]
  rw [htag]
  simp only [ct_eq_bytes32_spec, a0, a1, m0, m1, tower128_mul_eq_pure,
    tower.tower128_add, bind_eq_result_bind, result_bind_ok, lift_eq_ok]
  by_cases hw : item.chal_weight = 0#u128
  · simp only [hw, ite_true, ne_eq, not_true_eq_false, false_and, decide_false]
    rfl
  · simp only [hw, ite_false]
    by_cases ht : tag = batch.tag_commitment
    all_goals simp [ht, hw, bdozExpectedMacLanes, bdozFoldedKey, bdozMaskedSum]
    exact mac_lanes_equal _ _ _

theorem bdoz_authenticate_open_spec (session : tower.BdozVerifierSession2Lane)
    (batch : tower.BdozCommittedBatchOpening2Lane) (item : tower.BdozWireOpening2Lane) :
    ∃ committed_tag session' accepted,
      tower.bdoz_commit_masked_tag batch.session_id batch.round_id (bdozMaskedSum batch item)
        batch.peer_masked_mac_lanes batch.open_nonce = .ok committed_tag ∧
      tower.verify_mac_2lane_with_burn session batch (bdozOpening1 item) = .ok (session', accepted) ∧
      (accepted = true ↔ session.burned = false ∧ item.chal_weight ≠ 0#u128 ∧
        batch.tag_commitment = committed_tag ∧ batch.peer_masked_mac_lanes = bdozExpectedMacLanes session batch item) := by
  obtain ⟨tag, htag⟩ := bdoz_commit_total batch.session_id batch.round_id (bdozMaskedSum batch item)
    batch.peer_masked_mac_lanes batch.open_nonce
  have hv := bdoz_verify_one_eq session batch item tag htag
  unfold tower.verify_mac_2lane_with_burn
  rw [hv]
  cases hb : session.burned with
  | true => exact ⟨tag, _, false, htag, rfl, by simp⟩
  | false =>
    by_cases h : item.chal_weight ≠ 0#u128 ∧ tag = batch.tag_commitment ∧ batch.peer_masked_mac_lanes = bdozExpectedMacLanes session batch item
    · refine ⟨tag, session, true, htag, ?_, ?_⟩
      · simp [h]
      · simpa [eq_comm] using h
    · refine ⟨tag, ⟨Std.Array.make 2#usize [0#u128, 0#u128], true⟩, false, htag, ?_, ?_⟩
      · simp [h]
      · simpa [eq_comm] using h

theorem bdoz_tampered_mac_rejected (session : tower.BdozVerifierSession2Lane)
    (batch : tower.BdozCommittedBatchOpening2Lane) (item : tower.BdozWireOpening2Lane)
    (htamper : batch.peer_masked_mac_lanes ≠ bdozExpectedMacLanes session batch item) :
    ∃ session', tower.verify_mac_2lane_with_burn session batch (bdozOpening1 item) = .ok (session', false) := by
  obtain ⟨_, session', accepted, _, hr, ha⟩ := bdoz_authenticate_open_spec session batch item
  have hfalse : accepted = false := by
    cases accepted with
    | false => rfl
    | true => exact False.elim (htamper (ha.mp rfl).2.2.2)
  exact ⟨session', hfalse ▸ hr⟩

end qsag_verified.proofs




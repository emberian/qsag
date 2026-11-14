module
public import QsagVerified.Proofs.Common

/-!
The extracted session- and round-bound opening guard (`src/opening_guard.rs`).

`opening_verify_once_eq` is the total closed form of the single release decision.
`opening_round_permit_sound` and `opening_round_permit_complete` characterise a whole round
(construction, any sequence of `absorb_opening` calls, one `verify_once`): a permit is issued
exactly when the request names the provisioned session, round and binding, the expected
nonzero number of openings was folded, every opening matched its commitment, and both lane
sums are zero. `opening_verify_once_single_consumption` says no guard yields two decisions.
-/

public section
namespace qsag_verified.proofs
open Aeneas Aeneas.Std Result qsag_verified

abbrev OpeningGuard := opening_guard.ConsumingOpeningGuard2Lane
abbrev OpeningPermit := opening_guard.OpeningReleasePermit

/-- One opening as the guard sees it: frozen commitment, recomputed digest, opened lanes. -/
abbrev OpeningInput := Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U128 2#usize

/-- Post-attempt state: spent, with lane sums cleared. -/
@[expose] def openingSpent (s : OpeningGuard) : OpeningGuard :=
  { s with sum_lanes := Array.repeat 2#usize 0#u128, all_committed := false, consumed := true }

/-- The release condition, on the guard state and the request. -/
@[expose] def openingAccepts (s : OpeningGuard) (sid : Array Std.U8 32#usize) (round : Std.U64)
    (binding : Array Std.U8 32#usize) : Prop :=
  s.consumed = false ∧ s.session_id = sid ∧ s.round_id = round ∧ s.binding = binding ∧
    s.expected_openings ≠ 0#u64 ∧ s.absorbed = s.expected_openings ∧ s.all_committed = true ∧
    (s.sum_lanes.val.getD 0 0#u128 ||| s.sum_lanes.val.getD 1 0#u128) = 0#u128

instance (s : OpeningGuard) (sid : Array Std.U8 32#usize) (round : Std.U64)
    (binding : Array Std.U8 32#usize) : Decidable (openingAccepts s sid round binding) := by
  unfold openingAccepts
  exact inferInstance

/-- The permit an accepting guard issues. -/
@[expose] def openingPermit (s : OpeningGuard) : OpeningPermit :=
  { session_id := s.session_id, round_id := s.round_id, openings := s.absorbed }

private theorem lanes_index0 (a : Array Std.U128 2#usize) :
    Array.index_usize a 0#usize = .ok (a.val.getD 0 0#u128) :=
  array_index_getD a 0#usize 0#u128 (by decide)

private theorem lanes_index1 (a : Array Std.U128 2#usize) :
    Array.index_usize a 1#usize = .ok (a.val.getD 1 0#u128) :=
  array_index_getD a 1#usize 0#u128 (by decide)

/-- Total closed form of the release decision: every attempt spends the guard, and a permit
is issued exactly under `openingAccepts`. -/
theorem opening_verify_once_eq (s : OpeningGuard) (sid : Array Std.U8 32#usize)
    (round : Std.U64) (binding : Array Std.U8 32#usize) :
    opening_guard.ConsumingOpeningGuard2Lane.verify_once s sid round binding =
      .ok (openingSpent s,
        if openingAccepts s sid round binding then some (openingPermit s) else none) := by
  unfold opening_guard.ConsumingOpeningGuard2Lane.verify_once
  have h0 := lanes_index0 s.sum_lanes
  have h1 := lanes_index1 s.sum_lanes
  simp only [ct_eq_bytes32_spec, h0, h1, bind_eq_result_bind,
    result_bind_ok, lift_eq_ok, openingSpent, openingAccepts, openingPermit]
  by_cases hc : s.consumed = true
  · simp [hc]
  · have hc' : s.consumed = false := by simpa using hc
    by_cases hs : s.session_id = sid
    · by_cases hr : s.round_id = round
      · by_cases hb : s.binding = binding
        · by_cases he : s.expected_openings = 0#u64
          · simp [hc', hs, hr, hb, he]
          · by_cases ha : s.absorbed = s.expected_openings
            · by_cases hall : s.all_committed = true
              · by_cases hz :
                    (s.sum_lanes.val.getD 0 0#u128 ||| s.sum_lanes.val.getD 1 0#u128) = 0#u128
                · simp only [List.getD_eq_getElem?_getD] at hz
                  simp [hc', hs, hr, hb, he, ha, hall, hz]
                · simp only [List.getD_eq_getElem?_getD] at hz
                  simp [hc', hs, hr, hb, he, ha, hall, hz]
              · have hall' : s.all_committed = false := by simpa using hall
                simp [hc', hs, hr, hb, he, ha, hall']
            · simp [hc', hs, hr, hb, he, ha]
        · simp [hc', hs, hr, hb]
      · simp [hc', hs, hr]
    · simp [hc', hs]

/-- Reusing a spent guard refuses. -/
theorem opening_verify_once_replay (s : OpeningGuard) (sid : Array Std.U8 32#usize)
    (round : Std.U64) (binding : Array Std.U8 32#usize) (h : s.consumed = true) :
    opening_guard.ConsumingOpeningGuard2Lane.verify_once s sid round binding =
      .ok (openingSpent s, none) := by
  have hna : ¬ openingAccepts s sid round binding := by
    rintro ⟨hc, _⟩
    rw [h] at hc
    cases hc
  rw [opening_verify_once_eq, ite_eq_right hna]

/-- No guard yields two decisions: whatever the first attempt returned, any later attempt on
the returned guard refuses. -/
theorem opening_verify_once_single_consumption (s t : OpeningGuard)
    (sid sid' : Array Std.U8 32#usize) (round round' : Std.U64)
    (binding binding' : Array Std.U8 32#usize) (p : Option OpeningPermit)
    (h : opening_guard.ConsumingOpeningGuard2Lane.verify_once s sid round binding = .ok (t, p)) :
    opening_guard.ConsumingOpeningGuard2Lane.verify_once t sid' round' binding' =
      .ok (openingSpent t, none) := by
  rw [opening_verify_once_eq] at h
  have ht : t = openingSpent s := (Prod.mk.inj (Result.ok.inj h)).1.symm
  apply opening_verify_once_replay
  rw [ht]
  rfl

/-- A permit is evidence of the release condition and names the guard's own context. -/
theorem opening_verify_once_accepted (s t : OpeningGuard) (sid : Array Std.U8 32#usize)
    (round : Std.U64) (binding : Array Std.U8 32#usize) (p : OpeningPermit)
    (h : opening_guard.ConsumingOpeningGuard2Lane.verify_once s sid round binding =
      .ok (t, some p)) :
    openingAccepts s sid round binding ∧ p = openingPermit s ∧ t = openingSpent s := by
  rw [opening_verify_once_eq] at h
  have hpair := Prod.mk.inj (Result.ok.inj h)
  by_cases hacc : openingAccepts s sid round binding
  · rw [ite_eq_left hacc] at hpair
    exact ⟨hacc, (Option.some.inj hpair.2).symm, hpair.1.symm⟩
  · rw [ite_eq_right hacc] at hpair
    cases hpair.2

/-! ## Folding openings -/

/-- Pure effect of `absorb_opening`. -/
@[expose] def openingAbsorb (s : OpeningGuard) (x : OpeningInput) : OpeningGuard :=
  if s.consumed then s
  else if s.absorbed = core.num.U64.MAX then
    { s with
      sum_lanes := Array.make 2#usize
        [s.sum_lanes.val.getD 0 0#u128 ^^^ x.2.2.val.getD 0 0#u128,
         s.sum_lanes.val.getD 1 0#u128 ^^^ x.2.2.val.getD 1 0#u128],
      all_committed := false }
  else
    { s with
      absorbed := ⟨s.absorbed.bv + (1#u64).bv⟩,
      sum_lanes := Array.make 2#usize
        [s.sum_lanes.val.getD 0 0#u128 ^^^ x.2.2.val.getD 0 0#u128,
         s.sum_lanes.val.getD 1 0#u128 ^^^ x.2.2.val.getD 1 0#u128],
      all_committed := s.all_committed && decide (x.1 = x.2.1) }

private theorem u64_max_val : (core.num.U64.MAX : Std.U64).val = 2 ^ 64 - 1 := by decide

/-- `absorb_opening` is total and equals `openingAbsorb`. -/
theorem opening_absorb_eq (s : OpeningGuard) (x : OpeningInput) :
    opening_guard.ConsumingOpeningGuard2Lane.absorb_opening s x.1 x.2.1 x.2.2 =
      .ok (openingAbsorb s x) := by
  unfold opening_guard.ConsumingOpeningGuard2Lane.absorb_opening openingAbsorb
  have a0 := lanes_index0 s.sum_lanes
  have a1 := lanes_index1 s.sum_lanes
  have b0 := lanes_index0 x.2.2
  have b1 := lanes_index1 x.2.2
  simp only [ct_eq_bytes32_spec, a0, a1, b0, b1, bind_eq_result_bind,
    result_bind_ok, lift_eq_ok]
  by_cases hc : s.consumed = true
  · simp [hc]
  · have hc' : s.consumed = false := by simpa using hc
    by_cases hm : s.absorbed = core.num.U64.MAX
    · simp [hc', hm]
    · have hlt : s.absorbed.val + (1#u64).val < 2 ^ UScalarTy.U64.numBits := by
        have hne : s.absorbed.val ≠ 2 ^ 64 - 1 := fun e =>
          hm (UScalar.eq_of_val_eq (e.trans u64_max_val.symm))
        have hb : s.absorbed.val < 2 ^ 64 := s.absorbed.bv.isLt
        change s.absorbed.val + 1 < 2 ^ 64
        omega
      have hadd : (s.absorbed + 1#u64 : Result Std.U64) =
          .ok ⟨s.absorbed.bv + (1#u64).bv⟩ := by
        rw [hAdd_uscalar_eq, ite_eq_left hlt]
      cases hall : s.all_committed <;> simp [hc', hm, hadd]

/-- XOR of lane `k` over a sequence of openings. -/
@[expose] def openingLaneSum (xs : List OpeningInput) (k : Nat) : Std.U128 :=
  xs.foldl (fun acc x => acc ^^^ x.2.2.val.getD k 0#u128) 0#u128

theorem openingLaneSum_snoc (xs : List OpeningInput) (x : OpeningInput) (k : Nat) :
    openingLaneSum (xs ++ [x]) k = openingLaneSum xs k ^^^ x.2.2.val.getD k 0#u128 := by
  simp only [openingLaneSum, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- An unspent guard of the given context that has folded exactly `xs`. The count saturates,
and a saturated count is never accepted again. -/
def OpeningFolded (sid : Array Std.U8 32#usize) (round : Std.U64)
    (binding : Array Std.U8 32#usize) (n : Std.U64) (xs : List OpeningInput)
    (s : OpeningGuard) : Prop :=
  s.consumed = false ∧ s.session_id = sid ∧ s.round_id = round ∧ s.binding = binding ∧
    s.expected_openings = n ∧
    s.sum_lanes.val.getD 0 0#u128 = openingLaneSum xs 0 ∧
    s.sum_lanes.val.getD 1 0#u128 = openingLaneSum xs 1 ∧
    s.absorbed.val = min xs.length (2 ^ 64 - 1) ∧
    (s.all_committed = true ↔ (xs.length < 2 ^ 64 ∧ ∀ x ∈ xs, x.1 = x.2.1))

private theorem opening_folded_step (sid : Array Std.U8 32#usize) (round : Std.U64)
    (binding : Array Std.U8 32#usize) (n : Std.U64) (xs : List OpeningInput)
    (s : OpeningGuard) (x : OpeningInput) (h : OpeningFolded sid round binding n xs s) :
    OpeningFolded sid round binding n (xs ++ [x]) (openingAbsorb s x) := by
  obtain ⟨hc, hs, hr, hb, he, h0, h1, hcount, hall⟩ := h
  have hlen : (xs ++ [x]).length = xs.length + 1 := by
    rw [List.length_append, List.length_cons, List.length_nil]
  unfold openingAbsorb
  rw [ite_eq_right (by rw [hc]; exact Bool.false_ne_true)]
  by_cases hm : s.absorbed = core.num.U64.MAX
  · rw [ite_eq_left hm]
    have hmax : s.absorbed.val = 2 ^ 64 - 1 := by rw [hm]; exact u64_max_val
    refine ⟨hc, hs, hr, hb, he, ?_, ?_, ?_, ?_⟩
    · rw [openingLaneSum_snoc, ← h0]; rfl
    · rw [openingLaneSum_snoc, ← h1]; rfl
    · change s.absorbed.val = min (xs ++ [x]).length (2 ^ 64 - 1)
      rw [hlen]; omega
    · change false = true ↔ ((xs ++ [x]).length < 2 ^ 64 ∧ ∀ y ∈ xs ++ [x], y.1 = y.2.1)
      rw [hlen]
      constructor
      · intro hf; cases hf
      · rintro ⟨hlt, _⟩
        exfalso; omega
  · rw [ite_eq_right hm]
    have hne : s.absorbed.val ≠ 2 ^ 64 - 1 := fun e =>
      hm (UScalar.eq_of_val_eq (e.trans u64_max_val.symm))
    have hbound : s.absorbed.val < 2 ^ 64 := s.absorbed.bv.isLt
    have hval : (⟨s.absorbed.bv + (1#u64).bv⟩ : Std.U64).val = s.absorbed.val + 1 := by
      change (s.absorbed.bv + (1#u64).bv).toNat = s.absorbed.val + 1
      rw [BitVec.toNat_add]
      change (s.absorbed.val + 1) % 2 ^ 64 = s.absorbed.val + 1
      exact Nat.mod_eq_of_lt (by omega)
    refine ⟨hc, hs, hr, hb, he, ?_, ?_, ?_, ?_⟩
    · rw [openingLaneSum_snoc, ← h0]; rfl
    · rw [openingLaneSum_snoc, ← h1]; rfl
    · change (⟨s.absorbed.bv + (1#u64).bv⟩ : Std.U64).val = min (xs ++ [x]).length (2 ^ 64 - 1)
      rw [hval, hlen]; omega
    · change (s.all_committed && decide (x.1 = x.2.1)) = true ↔
        ((xs ++ [x]).length < 2 ^ 64 ∧ ∀ y ∈ xs ++ [x], y.1 = y.2.1)
      rw [hlen, Bool.and_eq_true, decide_eq_true_eq, hall]
      constructor
      · rintro ⟨⟨_, hmem⟩, hx⟩
        refine ⟨by omega, fun y hy => ?_⟩
        rcases List.mem_append.mp hy with hy | hy
        · exact hmem y hy
        · rw [List.mem_singleton.mp hy]; exact hx
      · rintro ⟨_, hmem⟩
        exact ⟨⟨by omega, fun y hy => hmem y (List.mem_append.mpr (Or.inl hy))⟩,
          hmem x (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))⟩

/-- Any sequence of `absorb_opening` calls. -/
def openingAbsorbAll (s : OpeningGuard) : List OpeningInput → Result OpeningGuard
  | [] => .ok s
  | x :: xs =>
    Result.bind (opening_guard.ConsumingOpeningGuard2Lane.absorb_opening s x.1 x.2.1 x.2.2)
      fun s' => openingAbsorbAll s' xs

theorem opening_absorb_all_folded (sid : Array Std.U8 32#usize) (round : Std.U64)
    (binding : Array Std.U8 32#usize) (n : Std.U64) :
    ∀ (rest done : List OpeningInput) (s : OpeningGuard),
      OpeningFolded sid round binding n done s →
      ∃ s', openingAbsorbAll s rest = .ok s' ∧
        OpeningFolded sid round binding n (done ++ rest) s'
  | [], done, s, h => ⟨s, rfl, by rw [List.append_nil]; exact h⟩
  | x :: rest, done, s, h => by
    obtain ⟨s', hrun, hfold⟩ := opening_absorb_all_folded sid round binding n rest
      (done ++ [x]) (openingAbsorb s x) (opening_folded_step sid round binding n done s x h)
    refine ⟨s', ?_, ?_⟩
    · simp only [openingAbsorbAll, opening_absorb_eq, result_bind_ok, hrun]
    · rw [List.append_assoc] at hfold
      exact hfold

theorem opening_new_folded (sid : Array Std.U8 32#usize) (round : Std.U64)
    (binding : Array Std.U8 32#usize) (n : Std.U64) :
    ∃ s, opening_guard.ConsumingOpeningGuard2Lane.new sid round binding n = .ok s ∧
      OpeningFolded sid round binding n [] s := by
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  constructor
  · intro _
    exact ⟨by decide, fun _ hx => absurd hx List.not_mem_nil⟩
  · intro _
    rfl

/-- One whole opening round: construction, any openings, one decision. -/
def openingRound (sid : Array Std.U8 32#usize) (round : Std.U64)
    (binding : Array Std.U8 32#usize) (n : Std.U64) (xs : List OpeningInput)
    (sid' : Array Std.U8 32#usize) (round' : Std.U64) (binding' : Array Std.U8 32#usize) :
    Result (OpeningGuard × Option OpeningPermit) :=
  Result.bind (opening_guard.ConsumingOpeningGuard2Lane.new sid round binding n) fun s0 =>
    Result.bind (openingAbsorbAll s0 xs) fun s1 =>
      opening_guard.ConsumingOpeningGuard2Lane.verify_once s1 sid' round' binding'

/-- Release condition of a whole round, on the inputs alone. -/
@[expose] def OpeningRoundValid (sid : Array Std.U8 32#usize) (round : Std.U64)
    (binding : Array Std.U8 32#usize) (n : Std.U64) (xs : List OpeningInput)
    (sid' : Array Std.U8 32#usize) (round' : Std.U64) (binding' : Array Std.U8 32#usize) :
    Prop :=
  sid' = sid ∧ round' = round ∧ binding' = binding ∧ n ≠ 0#u64 ∧ xs.length = n.val ∧
    (∀ x ∈ xs, x.1 = x.2.1) ∧
    (openingLaneSum xs 0 ||| openingLaneSum xs 1) = 0#u128

private theorem opening_round_run (sid : Array Std.U8 32#usize) (round : Std.U64)
    (binding : Array Std.U8 32#usize) (n : Std.U64) (xs : List OpeningInput)
    (sid' : Array Std.U8 32#usize) (round' : Std.U64) (binding' : Array Std.U8 32#usize) :
    ∃ s1, OpeningFolded sid round binding n xs s1 ∧
      openingRound sid round binding n xs sid' round' binding' =
        .ok (openingSpent s1,
          if openingAccepts s1 sid' round' binding' then some (openingPermit s1) else none) := by
  obtain ⟨s0, hnew, hf0⟩ := opening_new_folded sid round binding n
  obtain ⟨s1, hrun, hf1⟩ := opening_absorb_all_folded sid round binding n xs [] s0 hf0
  rw [List.nil_append] at hf1
  refine ⟨s1, hf1, ?_⟩
  simp only [openingRound, hnew, result_bind_ok, hrun, opening_verify_once_eq]

private theorem opening_accepts_iff (sid : Array Std.U8 32#usize) (round : Std.U64)
    (binding : Array Std.U8 32#usize) (n : Std.U64) (xs : List OpeningInput)
    (s : OpeningGuard) (h : OpeningFolded sid round binding n xs s)
    (sid' : Array Std.U8 32#usize) (round' : Std.U64) (binding' : Array Std.U8 32#usize) :
    openingAccepts s sid' round' binding' ↔
      OpeningRoundValid sid round binding n xs sid' round' binding' := by
  obtain ⟨hc, hs, hr, hb, he, h0, h1, hcount, hall⟩ := h
  have hnb : n.val < 2 ^ 64 := n.bv.isLt
  unfold openingAccepts OpeningRoundValid
  rw [hs, hr, hb, he, h0, h1]
  constructor
  · rintro ⟨_, hs', hr', hb', hn, ha, hcm, hz⟩
    obtain ⟨hlt, hmem⟩ := hall.mp hcm
    have hav : s.absorbed.val = n.val := by rw [ha]
    exact ⟨hs'.symm, hr'.symm, hb'.symm, hn, by omega, hmem, hz⟩
  · rintro ⟨hs', hr', hb', hn, hlen, hmem, hz⟩
    exact ⟨hc, hs'.symm, hr'.symm, hb'.symm, hn, UScalar.eq_of_val_eq (by omega),
      hall.mpr ⟨by omega, hmem⟩, hz⟩

/-- A permit from a whole round is evidence that the round was valid, and it names the
provisioned session and round. The guard returned with it is spent. -/
theorem opening_round_permit_sound (sid : Array Std.U8 32#usize) (round : Std.U64)
    (binding : Array Std.U8 32#usize) (n : Std.U64) (xs : List OpeningInput)
    (sid' : Array Std.U8 32#usize) (round' : Std.U64) (binding' : Array Std.U8 32#usize)
    (t : OpeningGuard) (p : OpeningPermit)
    (h : openingRound sid round binding n xs sid' round' binding' = .ok (t, some p)) :
    OpeningRoundValid sid round binding n xs sid' round' binding' ∧
      p.session_id = sid ∧ p.round_id = round ∧ p.openings = n ∧ t.consumed = true := by
  obtain ⟨s1, hf, hrun⟩ := opening_round_run sid round binding n xs sid' round' binding'
  rw [hrun] at h
  have hpair := Prod.mk.inj (Result.ok.inj h)
  by_cases hacc : openingAccepts s1 sid' round' binding'
  · rw [ite_eq_left hacc] at hpair
    have hp : p = openingPermit s1 := (Option.some.inj hpair.2).symm
    have hvalid :=
      (opening_accepts_iff sid round binding n xs s1 hf sid' round' binding').mp hacc
    obtain ⟨_, hs, hr, _, he, _, _, _, _⟩ := hf
    refine ⟨hvalid, ?_, ?_, ?_, ?_⟩
    · rw [hp]; exact hs
    · rw [hp]; exact hr
    · rw [hp]; exact hacc.2.2.2.2.2.1.trans he
    · rw [← hpair.1]; rfl
  · rw [ite_eq_right hacc] at hpair
    cases hpair.2

/-- Every valid round is released: the guard does not refuse vacuously. -/
theorem opening_round_permit_complete (sid : Array Std.U8 32#usize) (round : Std.U64)
    (binding : Array Std.U8 32#usize) (n : Std.U64) (xs : List OpeningInput)
    (sid' : Array Std.U8 32#usize) (round' : Std.U64) (binding' : Array Std.U8 32#usize)
    (h : OpeningRoundValid sid round binding n xs sid' round' binding') :
    ∃ t p, openingRound sid round binding n xs sid' round' binding' = .ok (t, some p) := by
  obtain ⟨s1, hf, hrun⟩ := opening_round_run sid round binding n xs sid' round' binding'
  have hacc := (opening_accepts_iff sid round binding n xs s1 hf sid' round' binding').mpr h
  exact ⟨_, _, by rw [hrun, ite_eq_left hacc]⟩

/-- An invalid round yields no permit, and still spends the guard. -/
theorem opening_round_refused (sid : Array Std.U8 32#usize) (round : Std.U64)
    (binding : Array Std.U8 32#usize) (n : Std.U64) (xs : List OpeningInput)
    (sid' : Array Std.U8 32#usize) (round' : Std.U64) (binding' : Array Std.U8 32#usize)
    (h : ¬ OpeningRoundValid sid round binding n xs sid' round' binding') :
    ∃ t, openingRound sid round binding n xs sid' round' binding' = .ok (t, none) ∧
      t.consumed = true := by
  obtain ⟨s1, hf, hrun⟩ := opening_round_run sid round binding n xs sid' round' binding'
  have hacc : ¬ openingAccepts s1 sid' round' binding' := fun ha =>
    h ((opening_accepts_iff sid round binding n xs s1 hf sid' round' binding').mp ha)
  exact ⟨_, by rw [hrun, ite_eq_right hacc], rfl⟩

end qsag_verified.proofs

module

public import QsagVerified.Funs
import all QsagVerified.Funs
public import QsagVerified.Proofs.Common

/-!
# The belt-latch transition kernel

`belt_latch_kernel::BeltLatchKernel::bind` is the decision made by production
`BeltLatch::bind` with the write-ahead log replaced by an input: `persist_ok` is what the log
answered. `tests/parity_qsag_core.rs` runs the two against each other.

Contents:
* `belt_latch_bind_eq`: the extracted `bind` never panics and equals the closed-form
  `beltLatchBindPure`, for every state and request.
* `BeltLatchRun`: executions over arbitrary request sequences, including refused requests and
  failed persists. `belt_latch_run_exists` shows every sequence has one.
* `belt_latch_epoch_binding_unique`: in any execution from a well-formed state, two accepted
  binds of one epoch carry the same message digest, retry salt and digits, and the later one
  is a replay. An epoch is therefore bound to one record for all time.
* `belt_latch_fresh_epochs_increase`, `belt_latch_poison_absorbing`,
  `belt_latch_failed_persist_binds_nothing`, `belt_latch_recover_then_replay`.

The kernel does not cover echo exchange or the log's own authentication.
-/

public section

namespace qsag_verified.proofs

open Aeneas Aeneas.Std Result
open qsag_verified
open belt_latch_kernel

/-! ## Closed form of one step -/

/-- Boolean equality of digit vectors, field by field. -/
def beltLatchDigitsEqB (a b : BeltLatchDigits) : Bool :=
  decide (a.len = b.len) && decide (a.row0 = b.row0) && decide (a.row1 = b.row1) &&
    decide (a.row2 = b.row2) && decide (a.row3 = b.row3)

theorem beltLatchDigitsEqB_iff (a b : BeltLatchDigits) :
    beltLatchDigitsEqB a b = true ↔ a = b := by
  cases a
  cases b
  simp [beltLatchDigitsEqB, and_assoc]

theorem belt_latch_digits_eq_spec (a b : BeltLatchDigits) :
    belt_latch_digits_eq a b = .ok (beltLatchDigitsEqB a b) := by
  unfold belt_latch_digits_eq
  simp only [ct_eq_bytes32_spec, bind_eq_result_bind, result_bind_ok]
  by_cases hl : a.len = b.len <;> by_cases h0 : a.row0 = b.row0 <;>
    by_cases h1 : a.row1 = b.row1 <;> by_cases h2 : a.row2 = b.row2 <;>
    simp [beltLatchDigitsEqB, hl, h0, h1, h2]

/-- The record a request asks to bind. -/
def beltLatchRecordOf (r : BeltLatchBindRequest) : BeltLatchKernelRecord :=
  { epoch := r.epoch, msg_digest := r.msg_digest, retry_salt := r.retry_salt,
    digits := r.digits }

/-- The fresh path: window checks, then the durable write. -/
def beltLatchFreshPure (s : BeltLatchKernel) (r : BeltLatchBindRequest) :
    BeltLatchKernel × core.result.Result BeltLatchBindOutcome BeltLatchKernelError :=
  if r.epoch.val < s.next_epoch.val then (s, .Err .EpochConsumed)
  else if s.capacity_limit.val ≤ r.epoch.val then (s, .Err .Exhausted)
  else if 64 < r.epoch.val - s.next_epoch.val then (s, .Err .EpochJumpTooLarge)
  else if r.persist_ok = true then
    ({ s with next_epoch := ⟨r.epoch.bv + (1#u64).bv⟩, has_in_flight := true,
              in_flight := beltLatchRecordOf r }, .Ok .Fresh)
  else ({ s with wal_poisoned := true }, .Err .WalPersistFailed)

/-- One `bind`, in closed form. -/
def beltLatchBindPure (s : BeltLatchKernel) (r : BeltLatchBindRequest) :
    BeltLatchKernel × core.result.Result BeltLatchBindOutcome BeltLatchKernelError :=
  if s.wal_poisoned = true then (s, .Err .WalPoisoned)
  else if s.has_in_flight = true ∧ s.in_flight.epoch = r.epoch then
    if s.in_flight.msg_digest ≠ r.msg_digest then (s, .Err .EpochAlreadyBound)
    else if s.in_flight.retry_salt ≠ r.retry_salt then (s, .Err .RetrySaltMismatch)
    else if beltLatchDigitsEqB s.in_flight.digits r.digits = false then
      (s, .Err .DigitsMismatch)
    else (s, .Ok .Replay)
  else beltLatchFreshPure s r

private theorem belt_latch_max_jump_eq : BELT_LATCH_MAX_EPOCH_JUMP = 64#u64 := by
  unfold BELT_LATCH_MAX_EPOCH_JUMP
  rfl

private theorem belt_latch_max_capacity_eq :
    BELT_LATCH_MAX_CAPACITY_LIMIT = .ok 4611686018427387904#u64 := by
  unfold BELT_LATCH_MAX_CAPACITY_LIMIT
  rfl

private theorem u64_sub_val {a b : Std.U64} (h : b.val ≤ a.val) :
    (⟨a.bv - b.bv⟩ : Std.U64).val = a.val - b.val :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)

private theorem u64_one_val : (1#u64 : Std.U64).val = 1 := rfl
private theorem u64_sixty_four_val : (64#u64 : Std.U64).val = 64 := rfl

/-- The fresh tail of the generated code, for either value of the in-flight flag. -/
private theorem belt_latch_fresh_tail (s : BeltLatchKernel) (r : BeltLatchBindRequest)
    (mk : Std.U64 → BeltLatchKernel)
    (hmk : mk ⟨r.epoch.bv + (1#u64).bv⟩ =
      { s with next_epoch := ⟨r.epoch.bv + (1#u64).bv⟩, has_in_flight := true,
               in_flight := beltLatchRecordOf r }) :
    (if r.epoch < s.next_epoch then
        (ok (s, core.result.Result.Err BeltLatchKernelError.EpochConsumed) :
          Result (BeltLatchKernel ×
            core.result.Result BeltLatchBindOutcome BeltLatchKernelError))
      else if r.epoch >= s.capacity_limit then
        ok (s, core.result.Result.Err BeltLatchKernelError.Exhausted)
      else
        Result.bind (r.epoch - s.next_epoch) fun i =>
          if i > BELT_LATCH_MAX_EPOCH_JUMP then
            ok (s, core.result.Result.Err BeltLatchKernelError.EpochJumpTooLarge)
          else if r.persist_ok = true then
            Result.bind (r.epoch + 1#u64) fun i1 =>
              ok (mk i1, core.result.Result.Ok BeltLatchBindOutcome.Fresh)
          else
            ok ({ s with wal_poisoned := true },
              core.result.Result.Err BeltLatchKernelError.WalPersistFailed)) =
      .ok (beltLatchFreshPure s r) := by
  unfold beltLatchFreshPure
  by_cases h1 : r.epoch.val < s.next_epoch.val
  · have h1' : r.epoch < s.next_epoch := (UScalar.lt_iff_val _ _).mpr h1
    rw [ite_eq_left_of_eq_true _ _ (eq_true h1'), ite_eq_left_of_eq_true _ _ (eq_true h1)]
  · have h1' : ¬ r.epoch < s.next_epoch := fun h => h1 ((UScalar.lt_iff_val _ _).mp h)
    rw [ite_eq_right_of_eq_false _ _ (eq_false h1'), ite_eq_right_of_eq_false _ _ (eq_false h1)]
    by_cases h2 : s.capacity_limit.val ≤ r.epoch.val
    · have h2' : r.epoch >= s.capacity_limit := (UScalar.le_iff_val _ _).mpr h2
      rw [ite_eq_left_of_eq_true _ _ (eq_true h2'), ite_eq_left_of_eq_true _ _ (eq_true h2)]
    · have h2' : ¬ r.epoch >= s.capacity_limit := fun h => h2 ((UScalar.le_iff_val _ _).mp h)
      rw [ite_eq_right_of_eq_false _ _ (eq_false h2'),
        ite_eq_right_of_eq_false _ _ (eq_false h2)]
      have hle : s.next_epoch.val ≤ r.epoch.val := Nat.le_of_not_lt h1
      have hsub : (r.epoch - s.next_epoch : Result Std.U64) =
          .ok ⟨r.epoch.bv - s.next_epoch.bv⟩ := by
        rw [hSub_uscalar_eq, ite_eq_left_of_eq_true _ _ (eq_true hle)]
      rw [hsub, result_bind_ok, belt_latch_max_jump_eq]
      by_cases h3 : 64 < r.epoch.val - s.next_epoch.val
      · have h3' : (⟨r.epoch.bv - s.next_epoch.bv⟩ : Std.U64) > 64#u64 := by
          apply (UScalar.lt_iff_val _ _).mpr
          rw [u64_sub_val hle, u64_sixty_four_val]
          exact h3
        rw [ite_eq_left_of_eq_true _ _ (eq_true h3'), ite_eq_left_of_eq_true _ _ (eq_true h3)]
      · have h3' : ¬ (⟨r.epoch.bv - s.next_epoch.bv⟩ : Std.U64) > 64#u64 := by
          intro h
          have h := (UScalar.lt_iff_val _ _).mp h
          rw [u64_sub_val hle, u64_sixty_four_val] at h
          exact h3 h
        rw [ite_eq_right_of_eq_false _ _ (eq_false h3'),
          ite_eq_right_of_eq_false _ _ (eq_false h3)]
        by_cases h4 : r.persist_ok = true
        · have hlim : s.capacity_limit.val < 2 ^ 64 := s.capacity_limit.bv.isLt
          have hadd : (r.epoch + 1#u64 : Result Std.U64) = .ok ⟨r.epoch.bv + (1#u64).bv⟩ := by
            rw [hAdd_uscalar_eq, u64_one_val]
            exact ite_eq_left_of_eq_true _ _ (eq_true (by
              show r.epoch.val + 1 < 2 ^ 64
              omega))
          rw [ite_eq_left_of_eq_true _ _ (eq_true h4), ite_eq_left_of_eq_true _ _ (eq_true h4),
            hadd, result_bind_ok, hmk]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h4),
            ite_eq_right_of_eq_false _ _ (eq_false h4)]

/-- The extracted `bind` is total and equals its closed form on every state and request. -/
theorem belt_latch_bind_eq (s : BeltLatchKernel) (r : BeltLatchBindRequest) :
    BeltLatchKernel.bind s r = .ok (beltLatchBindPure s r) := by
  unfold BeltLatchKernel.bind beltLatchBindPure
  simp only [ct_eq_bytes32_spec, belt_latch_digits_eq_spec, bind_eq_result_bind, result_bind_ok]
  by_cases hp : s.wal_poisoned = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hp), ite_eq_left_of_eq_true _ _ (eq_true hp)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hp), ite_eq_right_of_eq_false _ _ (eq_false hp)]
    by_cases hf : s.has_in_flight = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hf)]
      by_cases he : s.in_flight.epoch = r.epoch
      · rw [ite_eq_left_of_eq_true _ _ (eq_true he),
          ite_eq_left_of_eq_true _ _ (eq_true (And.intro hf he))]
        by_cases hm : s.in_flight.msg_digest = r.msg_digest
        · by_cases hs : s.in_flight.retry_salt = r.retry_salt
          · cases hd : beltLatchDigitsEqB s.in_flight.digits r.digits <;> simp [hm, hs]
          · simp [hm, hs]
        · simp [hm]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false he),
          ite_eq_right_of_eq_false _ _ (eq_false
            (fun (h : s.has_in_flight = true ∧ s.in_flight.epoch = r.epoch) => he h.2))]
        refine belt_latch_fresh_tail s r
          (fun i1 => { s with next_epoch := i1, in_flight := beltLatchRecordOf r }) ?_
        cases s
        simp only at hf
        subst hf
        rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hf),
        ite_eq_right_of_eq_false _ _ (eq_false
          (fun (h : s.has_in_flight = true ∧ s.in_flight.epoch = r.epoch) => hf h.1))]
      exact belt_latch_fresh_tail s r
        (fun i1 => { s with next_epoch := i1, has_in_flight := true,
                            in_flight := beltLatchRecordOf r }) rfl

/-! ## Facts about one step -/

/-- Well-formed latch states: the high-water mark is within the capacity and lies strictly
above the in-flight epoch. -/
def BeltLatchInv (s : BeltLatchKernel) : Prop :=
  s.next_epoch.val ≤ s.capacity_limit.val ∧
    (s.has_in_flight = true → s.in_flight.epoch.val < s.next_epoch.val)

private theorem u64_succ_val_of_lt {a b : Std.U64} (h : a.val < b.val) :
    (⟨a.bv + (1#u64).bv⟩ : Std.U64).val = a.val + 1 := by
  have hb : b.val < 2 ^ 64 := b.bv.isLt
  show (a.bv + (1#u64).bv).toNat = a.val + 1
  rw [BitVec.toNat_add]
  exact Nat.mod_eq_of_lt (by
    show a.val + 1 < 2 ^ 64
    omega)

/-- What an accepted fresh bind establishes. -/
theorem belt_latch_fresh_step {s s' : BeltLatchKernel} {r : BeltLatchBindRequest}
    (h : BeltLatchKernel.bind s r = .ok (s', .Ok .Fresh)) :
    s.wal_poisoned = false ∧ r.persist_ok = true ∧
      s.next_epoch.val ≤ r.epoch.val ∧ r.epoch.val < s.capacity_limit.val ∧
      r.epoch.val - s.next_epoch.val ≤ 64 ∧
      s'.next_epoch.val = r.epoch.val + 1 ∧ s'.has_in_flight = true ∧
      s'.in_flight = beltLatchRecordOf r ∧ s'.wal_poisoned = false ∧
      s'.capacity_limit = s.capacity_limit := by
  rw [belt_latch_bind_eq] at h
  have h := Result.ok.inj h
  unfold beltLatchBindPure at h
  by_cases hp : s.wal_poisoned = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hp)] at h
    cases h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hp)] at h
    have hpf : s.wal_poisoned = false := by
      cases hw : s.wal_poisoned
      · rfl
      · exact absurd hw hp
    by_cases hr : s.has_in_flight = true ∧ s.in_flight.epoch = r.epoch
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hr)] at h
      split at h
      · cases h
      · split at h
        · cases h
        · split at h <;> cases h
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hr)] at h
      unfold beltLatchFreshPure at h
      split at h
      · cases h
      · rename_i h1
        split at h
        · cases h
        · rename_i h2
          split at h
          · cases h
          · rename_i h3
            split at h
            · rename_i h4
              cases h
              exact ⟨hpf, h4, Nat.le_of_not_lt h1, Nat.lt_of_not_le h2, Nat.le_of_not_lt h3,
                u64_succ_val_of_lt (Nat.lt_of_not_le h2), rfl, rfl, hpf, rfl⟩
            · cases h

/-- An accepted replay changes nothing and matches the in-flight record exactly. -/
theorem belt_latch_replay_step {s s' : BeltLatchKernel} {r : BeltLatchBindRequest}
    (h : BeltLatchKernel.bind s r = .ok (s', .Ok .Replay)) :
    s' = s ∧ s.has_in_flight = true ∧ s.in_flight = beltLatchRecordOf r := by
  rw [belt_latch_bind_eq] at h
  have h := Result.ok.inj h
  unfold beltLatchBindPure at h
  by_cases hp : s.wal_poisoned = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hp)] at h
    cases h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hp)] at h
    by_cases hr : s.has_in_flight = true ∧ s.in_flight.epoch = r.epoch
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hr)] at h
      split at h
      · cases h
      · rename_i hm
        split at h
        · cases h
        · rename_i hs
          split at h
          · cases h
          · rename_i hd
            cases h
            have hm' : s.in_flight.msg_digest = r.msg_digest := Decidable.of_not_not hm
            have hs' : s.in_flight.retry_salt = r.retry_salt := Decidable.of_not_not hs
            have hd' : s.in_flight.digits = r.digits :=
              (beltLatchDigitsEqB_iff _ _).mp (by
                cases hb : beltLatchDigitsEqB s.in_flight.digits r.digits
                · exact absurd hb hd
                · rfl)
            refine ⟨rfl, hr.1, ?_⟩
            cases hrec : s.in_flight
            rw [hrec] at hm' hs' hd' hr
            simp only at hm' hs' hd'
            have he := hr.2
            simp only at he
            subst hm' hs' hd' he
            rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hr)] at h
      unfold beltLatchFreshPure at h
      split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h <;> cases h

/-- A refused bind leaves the state alone, except that a failed durable write sets the
poison flag and nothing else. -/
theorem belt_latch_rejected_step {s s' : BeltLatchKernel} {r : BeltLatchBindRequest}
    {e : BeltLatchKernelError}
    (h : BeltLatchKernel.bind s r = .ok (s', .Err e)) :
    (e ≠ .WalPersistFailed → s' = s) ∧
      (e = .WalPersistFailed →
        s' = { s with wal_poisoned := true } ∧ r.persist_ok = false ∧ s.wal_poisoned = false) := by
  rw [belt_latch_bind_eq] at h
  have h := Result.ok.inj h
  unfold beltLatchBindPure at h
  by_cases hp : s.wal_poisoned = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hp)] at h
    cases h
    exact ⟨fun _ => rfl, fun he => by cases he⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hp)] at h
    have hpf : s.wal_poisoned = false := by
      cases hw : s.wal_poisoned
      · rfl
      · exact absurd hw hp
    by_cases hr : s.has_in_flight = true ∧ s.in_flight.epoch = r.epoch
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hr)] at h
      split at h
      · cases h; exact ⟨fun _ => rfl, fun he => by cases he⟩
      · split at h
        · cases h; exact ⟨fun _ => rfl, fun he => by cases he⟩
        · split at h
          · cases h; exact ⟨fun _ => rfl, fun he => by cases he⟩
          · cases h
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hr)] at h
      unfold beltLatchFreshPure at h
      split at h
      · cases h; exact ⟨fun _ => rfl, fun he => by cases he⟩
      · split at h
        · cases h; exact ⟨fun _ => rfl, fun he => by cases he⟩
        · split at h
          · cases h; exact ⟨fun _ => rfl, fun he => by cases he⟩
          · split at h
            · cases h
            · rename_i h4
              cases h
              refine ⟨fun hne => absurd rfl hne, fun _ => ⟨rfl, ?_, hpf⟩⟩
              cases hb : r.persist_ok
              · rfl
              · exact absurd hb h4

/-- A refused bind leaves the state alone or only sets the poison flag. -/
theorem belt_latch_rejected_state {s s' : BeltLatchKernel} {r : BeltLatchBindRequest}
    {e : BeltLatchKernelError}
    (h : BeltLatchKernel.bind s r = .ok (s', .Err e)) :
    s' = s ∨ s' = { s with wal_poisoned := true } := by
  obtain ⟨hne, heq⟩ := belt_latch_rejected_step h
  cases e
  case WalPersistFailed => exact Or.inr (heq rfl).1
  all_goals exact Or.inl (hne (fun hh => by cases hh))

/-- A poisoned latch refuses every request and does not change. -/
theorem belt_latch_poisoned_step (s : BeltLatchKernel) (r : BeltLatchBindRequest)
    (hp : s.wal_poisoned = true) :
    BeltLatchKernel.bind s r = .ok (s, .Err .WalPoisoned) := by
  rw [belt_latch_bind_eq]
  unfold beltLatchBindPure
  rw [ite_eq_left_of_eq_true _ _ (eq_true hp)]

/-- A request equal to the in-flight record is confirmed without touching the log, whatever
the log would have answered. -/
theorem belt_latch_replay_accepts (s : BeltLatchKernel) (r : BeltLatchBindRequest)
    (hp : s.wal_poisoned = false) (hf : s.has_in_flight = true)
    (hrec : s.in_flight = beltLatchRecordOf r) :
    BeltLatchKernel.bind s r = .ok (s, .Ok .Replay) := by
  rw [belt_latch_bind_eq]
  unfold beltLatchBindPure
  have hd : beltLatchDigitsEqB s.in_flight.digits r.digits = true :=
    (beltLatchDigitsEqB_iff _ _).mpr (by rw [hrec]; rfl)
  have hm : s.in_flight.msg_digest = r.msg_digest := by rw [hrec]; rfl
  have hs : s.in_flight.retry_salt = r.retry_salt := by rw [hrec]; rfl
  have he : s.in_flight.epoch = r.epoch := by rw [hrec]; rfl
  simp [hp, hf, he, hm, hs, hd]

/-- Each step keeps the capacity and never lowers the high-water mark. -/
theorem belt_latch_step_monotone {s s' : BeltLatchKernel} {r : BeltLatchBindRequest}
    {res : core.result.Result BeltLatchBindOutcome BeltLatchKernelError}
    (h : BeltLatchKernel.bind s r = .ok (s', res)) :
    s'.capacity_limit = s.capacity_limit ∧ s.next_epoch.val ≤ s'.next_epoch.val := by
  cases res with
  | Ok o =>
    cases o with
    | Fresh =>
      obtain ⟨_, _, hle, _, _, hn, _, _, _, hc⟩ := belt_latch_fresh_step h
      exact ⟨hc, by omega⟩
    | Replay =>
      obtain ⟨hs, _⟩ := belt_latch_replay_step h
      subst hs
      exact ⟨rfl, Nat.le_refl _⟩
  | Err e =>
    rcases belt_latch_rejected_state h with hs | hs <;> subst hs <;> exact ⟨rfl, Nat.le_refl _⟩

/-- Well-formedness is preserved by every step. -/
theorem belt_latch_step_preserves_inv {s s' : BeltLatchKernel} {r : BeltLatchBindRequest}
    {res : core.result.Result BeltLatchBindOutcome BeltLatchKernelError}
    (hinv : BeltLatchInv s) (h : BeltLatchKernel.bind s r = .ok (s', res)) :
    BeltLatchInv s' := by
  cases res with
  | Ok o =>
    cases o with
    | Fresh =>
      obtain ⟨_, _, _, hlt, _, hn, _, hrec, _, hc⟩ := belt_latch_fresh_step h
      refine ⟨?_, fun _ => ?_⟩
      · rw [hn, hc]; omega
      · rw [hn, hrec]
        show r.epoch.val < r.epoch.val + 1
        omega
    | Replay =>
      obtain ⟨hs, _⟩ := belt_latch_replay_step h
      subst hs
      exact hinv
  | Err e =>
    rcases belt_latch_rejected_state h with hs | hs <;> subst hs <;> exact hinv

/-! ## Executions -/

/-- A request together with the verdict the latch returned. -/
abbrev BeltLatchCall :=
  BeltLatchBindRequest × core.result.Result BeltLatchBindOutcome BeltLatchKernelError

/-- Executions of the extracted `bind` over an arbitrary request sequence. Refused requests
and failed persists are steps like any other. -/
inductive BeltLatchRun : BeltLatchKernel → List BeltLatchCall → BeltLatchKernel → Prop where
  | nil (s : BeltLatchKernel) : BeltLatchRun s [] s
  | step {s s' t : BeltLatchKernel} {r : BeltLatchBindRequest}
      {res : core.result.Result BeltLatchBindOutcome BeltLatchKernelError}
      {rest : List BeltLatchCall} :
      BeltLatchKernel.bind s r = .ok (s', res) → BeltLatchRun s' rest t →
      BeltLatchRun s ((r, res) :: rest) t

/-- Every request sequence is executable: the environment is not restricted. -/
theorem belt_latch_run_exists (s : BeltLatchKernel) (reqs : List BeltLatchBindRequest) :
    ∃ calls t, BeltLatchRun s calls t ∧ calls.map Prod.fst = reqs := by
  induction reqs generalizing s with
  | nil => exact ⟨[], s, .nil s, rfl⟩
  | cons r rest ih =>
    obtain ⟨calls, t, hrun, hmap⟩ := ih (beltLatchBindPure s r).1
    exact ⟨(r, (beltLatchBindPure s r).2) :: calls, t,
      .step (belt_latch_bind_eq s r) hrun, by rw [List.map_cons, hmap]⟩

theorem belt_latch_run_append {s t : BeltLatchKernel} {a b : List BeltLatchCall}
    (h : BeltLatchRun s (a ++ b) t) : ∃ m, BeltLatchRun s a m ∧ BeltLatchRun m b t := by
  induction a generalizing s with
  | nil => exact ⟨s, .nil s, h⟩
  | cons x rest ih =>
    cases h with
    | step hstep hrest =>
      obtain ⟨m, h1, h2⟩ := ih hrest
      exact ⟨m, .step hstep h1, h2⟩

theorem belt_latch_run_preserves_inv {s t : BeltLatchKernel} {calls : List BeltLatchCall}
    (hinv : BeltLatchInv s) (h : BeltLatchRun s calls t) : BeltLatchInv t := by
  induction h with
  | nil s => exact hinv
  | step hstep _ ih => exact ih (belt_latch_step_preserves_inv hinv hstep)

/-- Along any execution the capacity is fixed and the high-water mark never decreases. -/
theorem belt_latch_run_monotone {s t : BeltLatchKernel} {calls : List BeltLatchCall}
    (h : BeltLatchRun s calls t) :
    t.capacity_limit = s.capacity_limit ∧ s.next_epoch.val ≤ t.next_epoch.val := by
  induction h with
  | nil s => exact ⟨rfl, Nat.le_refl _⟩
  | step hstep _ ih =>
    obtain ⟨hc, hn⟩ := belt_latch_step_monotone hstep
    exact ⟨ih.1.trans hc, Nat.le_trans hn ih.2⟩

/-- Poison is absorbing: a poisoned latch ends every execution unchanged, having refused
every request with `WalPoisoned`. Only recovery from the log leaves this state. -/
theorem belt_latch_poison_absorbing {s t : BeltLatchKernel} {calls : List BeltLatchCall}
    (hp : s.wal_poisoned = true) (h : BeltLatchRun s calls t) :
    t = s ∧ ∀ c ∈ calls, c.2 = .Err .WalPoisoned := by
  induction h with
  | nil s => exact ⟨rfl, fun c hc => by cases hc⟩
  | @step s s' t r res rest hstep _ ih =>
    have heq := (belt_latch_poisoned_step s r hp).symm.trans hstep
    have hpair := Result.ok.inj heq
    have hs : s = s' := congrArg Prod.fst hpair
    have hres : core.result.Result.Err BeltLatchKernelError.WalPoisoned = res :=
      congrArg Prod.snd hpair
    subst hs
    obtain ⟨ht, hall⟩ := ih hp
    refine ⟨ht, fun c hc => ?_⟩
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hres.symm
    · exact hall c hc

/-- A failed durable write binds nothing: the high-water mark and the in-flight record are
those of the state before, and every later request is refused. -/
theorem belt_latch_failed_persist_binds_nothing
    {s s' t : BeltLatchKernel} {r : BeltLatchBindRequest} {calls : List BeltLatchCall}
    (h : BeltLatchKernel.bind s r = .ok (s', .Err .WalPersistFailed))
    (hrun : BeltLatchRun s' calls t) :
    t.next_epoch = s.next_epoch ∧ t.has_in_flight = s.has_in_flight ∧
      t.in_flight = s.in_flight ∧ t.wal_poisoned = true ∧
      ∀ c ∈ calls, c.2 = .Err .WalPoisoned := by
  obtain ⟨hs, _, _⟩ := (belt_latch_rejected_step h).2 rfl
  subst hs
  obtain ⟨ht, hall⟩ := belt_latch_poison_absorbing rfl hrun
  subst ht
  exact ⟨rfl, rfl, rfl, rfl, hall⟩

/-- After `rec` was bound, the in-flight record is `rec` or belongs to a later epoch. -/
private def BeltLatchBoundAfter (rec : BeltLatchKernelRecord) (s : BeltLatchKernel) : Prop :=
  s.has_in_flight = true ∧ rec.epoch.val < s.next_epoch.val ∧
    (s.in_flight = rec ∨ rec.epoch.val < s.in_flight.epoch.val)

private theorem belt_latch_bound_after_step {rec : BeltLatchKernelRecord}
    {s s' : BeltLatchKernel} {r : BeltLatchBindRequest}
    {res : core.result.Result BeltLatchBindOutcome BeltLatchKernelError}
    (hb : BeltLatchBoundAfter rec s) (h : BeltLatchKernel.bind s r = .ok (s', res)) :
    BeltLatchBoundAfter rec s' := by
  cases res with
  | Ok o =>
    cases o with
    | Fresh =>
      obtain ⟨_, _, hle, _, _, hn, hf, hrec, _, _⟩ := belt_latch_fresh_step h
      refine ⟨hf, by rw [hn]; have := hb.2.1; omega, Or.inr ?_⟩
      rw [hrec]
      show rec.epoch.val < r.epoch.val
      have := hb.2.1
      omega
    | Replay =>
      obtain ⟨hs, _⟩ := belt_latch_replay_step h
      subst hs
      exact hb
  | Err e =>
    rcases belt_latch_rejected_state h with hs | hs <;> subst hs <;> exact hb

private theorem belt_latch_bound_after_run {rec : BeltLatchKernelRecord}
    {s t : BeltLatchKernel} {calls : List BeltLatchCall}
    (hb : BeltLatchBoundAfter rec s) (h : BeltLatchRun s calls t) :
    BeltLatchBoundAfter rec t := by
  induction h with
  | nil s => exact hb
  | step hstep _ ih => exact ih (belt_latch_bound_after_step hb hstep)

/-- Any accepted bind leaves its request as the in-flight record, below the high-water mark. -/
private theorem belt_latch_accepted_bound {s s' : BeltLatchKernel} {r : BeltLatchBindRequest}
    {o : BeltLatchBindOutcome} (hinv : BeltLatchInv s)
    (h : BeltLatchKernel.bind s r = .ok (s', .Ok o)) :
    BeltLatchBoundAfter (beltLatchRecordOf r) s' := by
  cases o with
  | Fresh =>
    obtain ⟨_, _, _, _, _, hn, hf, hrec, _, _⟩ := belt_latch_fresh_step h
    refine ⟨hf, ?_, Or.inl hrec⟩
    rw [hn]
    show r.epoch.val < r.epoch.val + 1
    omega
  | Replay =>
    obtain ⟨hs, hf, hrec⟩ := belt_latch_replay_step h
    subst hs
    refine ⟨hf, ?_, Or.inl hrec⟩
    rw [← hrec]
    exact hinv.2 hf

/-- **One record per epoch, for all time.** In any execution from a well-formed state, if two
binds of the same epoch are both accepted then they carry the same message digest, the same
retry salt and the same digits, and the later one is a replay that wrote nothing. Arbitrary
requests, refusals and failed persists may occur before, between and after them. -/
theorem belt_latch_epoch_binding_unique
    {s t : BeltLatchKernel} {pre mid post : List BeltLatchCall}
    {r1 r2 : BeltLatchBindRequest} {o1 o2 : BeltLatchBindOutcome}
    (hinv : BeltLatchInv s)
    (hrun : BeltLatchRun s (pre ++ (r1, .Ok o1) :: (mid ++ (r2, .Ok o2) :: post)) t)
    (hep : r1.epoch = r2.epoch) :
    r1.msg_digest = r2.msg_digest ∧ r1.retry_salt = r2.retry_salt ∧ r1.digits = r2.digits ∧
      o2 = .Replay := by
  obtain ⟨m1, hpre, hrest⟩ := belt_latch_run_append hrun
  have hinv1 := belt_latch_run_preserves_inv hinv hpre
  cases hrest with
  | step hstep1 hrest1 =>
    have hb1 := belt_latch_accepted_bound hinv1 hstep1
    obtain ⟨m2, hmid, hrest2⟩ := belt_latch_run_append hrest1
    have hb2 := belt_latch_bound_after_run hb1 hmid
    cases hrest2 with
    | step hstep2 _ =>
      cases o2 with
      | Fresh =>
        obtain ⟨_, _, hle, _⟩ := belt_latch_fresh_step hstep2
        have hlt : r1.epoch.val < _ := hb2.2.1
        rw [hep] at hlt
        exact absurd hle (Nat.not_le_of_lt hlt)
      | Replay =>
        obtain ⟨_, _, hrec⟩ := belt_latch_replay_step hstep2
        have hsame : beltLatchRecordOf r2 = beltLatchRecordOf r1 := by
          rcases hb2.2.2 with h | h
          · exact hrec.symm.trans h
          · rw [hrec] at h
            have h' : r1.epoch.val < r2.epoch.val := h
            rw [hep] at h'
            exact absurd h' (Nat.lt_irrefl _)
        have hm : r2.msg_digest = r1.msg_digest :=
          congrArg BeltLatchKernelRecord.msg_digest hsame
        have hs : r2.retry_salt = r1.retry_salt :=
          congrArg BeltLatchKernelRecord.retry_salt hsame
        have hd : r2.digits = r1.digits := congrArg BeltLatchKernelRecord.digits hsame
        exact ⟨hm.symm, hs.symm, hd.symm, rfl⟩

/-- Fresh bindings happen at strictly increasing epochs: no epoch is ever persisted twice.
This needs no well-formedness assumption. -/
theorem belt_latch_fresh_epochs_increase
    {s t : BeltLatchKernel} {pre mid post : List BeltLatchCall}
    {r1 r2 : BeltLatchBindRequest}
    (hrun : BeltLatchRun s
      (pre ++ (r1, .Ok .Fresh) :: (mid ++ (r2, .Ok .Fresh) :: post)) t) :
    r1.epoch.val < r2.epoch.val := by
  obtain ⟨m1, _, hrest⟩ := belt_latch_run_append hrun
  cases hrest with
  | step hstep1 hrest1 =>
    obtain ⟨_, _, _, _, _, hn1, _⟩ := belt_latch_fresh_step hstep1
    obtain ⟨m2, hmid, hrest2⟩ := belt_latch_run_append hrest1
    have hmono := (belt_latch_run_monotone hmid).2
    cases hrest2 with
    | step hstep2 _ =>
      obtain ⟨_, _, hle, _⟩ := belt_latch_fresh_step hstep2
      omega

/-! ## Construction and recovery -/

/-- `new_empty` accepts exactly the limits `2 ≤ limit ≤ 2^62` and starts well-formed. -/
theorem belt_latch_new_empty_spec (limit : Std.U64) :
    (2 ≤ limit.val ∧ limit.val ≤ 2 ^ 62 →
      ∃ s, BeltLatchKernel.new_empty limit = .ok (.Ok s) ∧ BeltLatchInv s ∧
        s.capacity_limit = limit ∧ s.next_epoch = 0#u64 ∧ s.has_in_flight = false ∧
        s.wal_poisoned = false) ∧
    (¬ (2 ≤ limit.val ∧ limit.val ≤ 2 ^ 62) →
      BeltLatchKernel.new_empty limit = .ok (.Err .InvalidCapacity)) := by
  have hmaxv : (4611686018427387904#u64 : Std.U64).val = 2 ^ 62 := rfl
  have htwo : (2#u64 : Std.U64).val = 2 := rfl
  unfold BeltLatchKernel.new_empty
  simp only [belt_latch_max_capacity_eq, bind_eq_result_bind, result_bind_ok]
  constructor
  · rintro ⟨h2, hmax⟩
    have h2' : ¬ limit < 2#u64 := fun h => by
      have := (UScalar.lt_iff_val _ _).mp h
      rw [htwo] at this
      omega
    have hmax' : ¬ limit > 4611686018427387904#u64 := fun h => by
      have := (UScalar.lt_iff_val _ _).mp h
      rw [hmaxv] at this
      omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false h2'),
      ite_eq_right_of_eq_false _ _ (eq_false hmax')]
    exact ⟨_, rfl, ⟨Nat.zero_le _, fun h => by cases h⟩, rfl, rfl, rfl, rfl⟩
  · intro hbad
    by_cases h2 : limit < 2#u64
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2)]
      have h2v : 2 ≤ limit.val := by
        have : ¬ limit.val < (2#u64 : Std.U64).val := fun h => h2 ((UScalar.lt_iff_val _ _).mpr h)
        rw [htwo] at this
        omega
      have hgt : limit > 4611686018427387904#u64 := by
        apply (UScalar.lt_iff_val _ _).mpr
        rw [hmaxv]
        exact Nat.lt_of_not_le fun hle => hbad ⟨h2v, hle⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true hgt)]

/-- Recovery from the durable part of any well-formed state within capacity succeeds and
returns that state with the poison flag cleared. -/
theorem belt_latch_recover_of_inv (s : BeltLatchKernel) (hinv : BeltLatchInv s)
    (h2 : 2 ≤ s.capacity_limit.val) (hmax : s.capacity_limit.val ≤ 2 ^ 62) :
    BeltLatchKernel.recover s.capacity_limit s.next_epoch s.has_in_flight s.in_flight =
      .ok (.Ok { s with wal_poisoned := false }) := by
  have hmaxv : (4611686018427387904#u64 : Std.U64).val = 2 ^ 62 := rfl
  have htwo : (2#u64 : Std.U64).val = 2 := rfl
  have h2' : ¬ s.capacity_limit < 2#u64 := fun h => by
    have := (UScalar.lt_iff_val _ _).mp h
    rw [htwo] at this
    omega
  have hmax' : ¬ s.capacity_limit > 4611686018427387904#u64 := fun h => by
    have := (UScalar.lt_iff_val _ _).mp h
    rw [hmaxv] at this
    omega
  have hne : ¬ s.next_epoch > s.capacity_limit := fun h => by
    have := (UScalar.lt_iff_val _ _).mp h
    have := hinv.1
    omega
  unfold BeltLatchKernel.recover
  simp only [belt_latch_max_capacity_eq, bind_eq_result_bind, result_bind_ok]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h2'),
    ite_eq_right_of_eq_false _ _ (eq_false hmax'), ite_eq_right_of_eq_false _ _ (eq_false hne)]
  by_cases hf : s.has_in_flight = true
  · have hlt : ¬ s.in_flight.epoch >= s.next_epoch := fun h => by
      have := (UScalar.le_iff_val _ _).mp h
      have := hinv.2 hf
      omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true hf), ite_eq_right_of_eq_false _ _ (eq_false hlt)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hf)]

/-- **Crash replay.** Bind a fresh epoch, then let anything happen (including a failed
persist that poisons the latch), then crash and recover from the log. Re-submitting the
same request is a replay that changes nothing, whatever the log would answer; no new salt
can be rolled for that epoch. Stated for the case that no later epoch replaced the record. -/
theorem belt_latch_recover_then_replay
    {s s' t : BeltLatchKernel} {r r' : BeltLatchBindRequest} {calls : List BeltLatchCall}
    (hinv : BeltLatchInv s) (h2 : 2 ≤ s.capacity_limit.val)
    (hmax : s.capacity_limit.val ≤ 2 ^ 62)
    (hfresh : BeltLatchKernel.bind s r = .ok (s', .Ok .Fresh))
    (hrun : BeltLatchRun s' calls t)
    (hkeep : t.in_flight = beltLatchRecordOf r)
    (hreq : beltLatchRecordOf r' = beltLatchRecordOf r) :
    ∃ u, BeltLatchKernel.recover t.capacity_limit t.next_epoch t.has_in_flight t.in_flight =
        .ok (.Ok u) ∧
      BeltLatchKernel.bind u r' = .ok (u, .Ok .Replay) := by
  have hinv' := belt_latch_step_preserves_inv hinv hfresh
  have hinvt := belt_latch_run_preserves_inv hinv' hrun
  have hcap' := (belt_latch_step_monotone hfresh).1
  have hcapt := (belt_latch_run_monotone hrun).1
  have hbound := belt_latch_bound_after_run (belt_latch_accepted_bound hinv hfresh) hrun
  have hrec := belt_latch_recover_of_inv t hinvt (by rw [hcapt, hcap']; exact h2)
    (by rw [hcapt, hcap']; exact hmax)
  refine ⟨_, hrec, ?_⟩
  exact belt_latch_replay_accepts _ r' rfl hbound.1 (hkeep.trans hreq.symm)

/-! ## Acceptance and refusal conditions -/

/-- A request inside the window binds fresh when the log accepts it. -/
theorem belt_latch_fresh_accepts (s : BeltLatchKernel) (r : BeltLatchBindRequest)
    (hp : s.wal_poisoned = false)
    (hnr : ¬ (s.has_in_flight = true ∧ s.in_flight.epoch = r.epoch))
    (h1 : s.next_epoch.val ≤ r.epoch.val) (h2 : r.epoch.val < s.capacity_limit.val)
    (h3 : r.epoch.val - s.next_epoch.val ≤ 64) (h4 : r.persist_ok = true) :
    BeltLatchKernel.bind s r =
      .ok ({ s with next_epoch := ⟨r.epoch.bv + (1#u64).bv⟩, has_in_flight := true,
                    in_flight := beltLatchRecordOf r }, .Ok .Fresh) := by
  have hp' : ¬ s.wal_poisoned = true := by rw [hp]; exact Bool.false_ne_true
  rw [belt_latch_bind_eq]
  unfold beltLatchBindPure beltLatchFreshPure
  rw [ite_eq_right_of_eq_false _ _ (eq_false hp'), ite_eq_right_of_eq_false _ _ (eq_false hnr),
    ite_eq_right_of_eq_false _ _ (eq_false (Nat.not_lt_of_le h1)),
    ite_eq_right_of_eq_false _ _ (eq_false (Nat.not_le_of_lt h2)),
    ite_eq_right_of_eq_false _ _ (eq_false (Nat.not_lt_of_le h3)),
    ite_eq_left_of_eq_true _ _ (eq_true h4)]

/-- The same request poisons the latch, and binds nothing, when the log refuses it. -/
theorem belt_latch_persist_failure (s : BeltLatchKernel) (r : BeltLatchBindRequest)
    (hp : s.wal_poisoned = false)
    (hnr : ¬ (s.has_in_flight = true ∧ s.in_flight.epoch = r.epoch))
    (h1 : s.next_epoch.val ≤ r.epoch.val) (h2 : r.epoch.val < s.capacity_limit.val)
    (h3 : r.epoch.val - s.next_epoch.val ≤ 64) (h4 : r.persist_ok = false) :
    BeltLatchKernel.bind s r =
      .ok ({ s with wal_poisoned := true }, .Err .WalPersistFailed) := by
  have hp' : ¬ s.wal_poisoned = true := by rw [hp]; exact Bool.false_ne_true
  have h4' : ¬ r.persist_ok = true := by rw [h4]; exact Bool.false_ne_true
  rw [belt_latch_bind_eq]
  unfold beltLatchBindPure beltLatchFreshPure
  rw [ite_eq_right_of_eq_false _ _ (eq_false hp'), ite_eq_right_of_eq_false _ _ (eq_false hnr),
    ite_eq_right_of_eq_false _ _ (eq_false (Nat.not_lt_of_le h1)),
    ite_eq_right_of_eq_false _ _ (eq_false (Nat.not_le_of_lt h2)),
    ite_eq_right_of_eq_false _ _ (eq_false (Nat.not_lt_of_le h3)),
    ite_eq_right_of_eq_false _ _ (eq_false h4')]

/-- An epoch more than 64 above the high-water mark is refused and nothing changes. -/
theorem belt_latch_jump_refused (s : BeltLatchKernel) (r : BeltLatchBindRequest)
    (hp : s.wal_poisoned = false)
    (hnr : ¬ (s.has_in_flight = true ∧ s.in_flight.epoch = r.epoch))
    (h1 : s.next_epoch.val ≤ r.epoch.val) (h2 : r.epoch.val < s.capacity_limit.val)
    (h3 : 64 < r.epoch.val - s.next_epoch.val) :
    BeltLatchKernel.bind s r = .ok (s, .Err .EpochJumpTooLarge) := by
  have hp' : ¬ s.wal_poisoned = true := by rw [hp]; exact Bool.false_ne_true
  rw [belt_latch_bind_eq]
  unfold beltLatchBindPure beltLatchFreshPure
  rw [ite_eq_right_of_eq_false _ _ (eq_false hp'), ite_eq_right_of_eq_false _ _ (eq_false hnr),
    ite_eq_right_of_eq_false _ _ (eq_false (Nat.not_lt_of_le h1)),
    ite_eq_right_of_eq_false _ _ (eq_false (Nat.not_le_of_lt h2)),
    ite_eq_left_of_eq_true _ _ (eq_true h3)]

/-- The in-flight epoch with the same message and a different salt is refused. -/
theorem belt_latch_salt_mismatch_refused (s : BeltLatchKernel) (r : BeltLatchBindRequest)
    (hp : s.wal_poisoned = false) (hf : s.has_in_flight = true)
    (he : s.in_flight.epoch = r.epoch) (hm : s.in_flight.msg_digest = r.msg_digest)
    (hs : s.in_flight.retry_salt ≠ r.retry_salt) :
    BeltLatchKernel.bind s r = .ok (s, .Err .RetrySaltMismatch) := by
  have hp' : ¬ s.wal_poisoned = true := by rw [hp]; exact Bool.false_ne_true
  have hm' : ¬ s.in_flight.msg_digest ≠ r.msg_digest := fun h => h hm
  rw [belt_latch_bind_eq]
  unfold beltLatchBindPure
  rw [ite_eq_right_of_eq_false _ _ (eq_false hp'),
    ite_eq_left_of_eq_true _ _ (eq_true (And.intro hf he)),
    ite_eq_right_of_eq_false _ _ (eq_false hm'), ite_eq_left_of_eq_true _ _ (eq_true hs)]

/-! ## Inhabitedness and mutation witnesses -/

private theorem belt_latch_empty_no_replay {s0 : BeltLatchKernel} (hf0 : s0.has_in_flight = false)
    (r : BeltLatchBindRequest) : ¬ (s0.has_in_flight = true ∧ s0.in_flight.epoch = r.epoch) := by
  intro h
  rw [hf0] at h
  exact Bool.false_ne_true h.1

/-- The theorems above are inhabited: from the empty latch, epoch zero binds fresh, the same
request replays even when the log would refuse a write, and the same epoch with any other
salt is refused as a salt mismatch. -/
theorem inhabited_belt_latch_fresh_replay_mismatch
    (msg salt salt' : Array Std.U8 32#usize) (digits : BeltLatchDigits) (hne : salt ≠ salt') :
    ∃ s0 s1,
      BeltLatchKernel.new_empty 8#u64 = .ok (.Ok s0) ∧
      BeltLatchRun s0
        [(⟨0#u64, msg, salt, digits, true⟩, .Ok .Fresh),
         (⟨0#u64, msg, salt, digits, false⟩, .Ok .Replay),
         (⟨0#u64, msg, salt', digits, true⟩, .Err .RetrySaltMismatch)] s1 ∧
      s1.next_epoch.val = 1 := by
  obtain ⟨s0, hnew, _, hcap, hne0, hf0, hp0⟩ :=
    (belt_latch_new_empty_spec 8#u64).1 ⟨by decide, by decide⟩
  let s1 : BeltLatchKernel :=
    { s0 with next_epoch := ⟨(0#u64 : Std.U64).bv + (1#u64).bv⟩, has_in_flight := true,
              in_flight := ⟨0#u64, msg, salt, digits⟩ }
  have hstep1 : BeltLatchKernel.bind s0 ⟨0#u64, msg, salt, digits, true⟩ =
      .ok (s1, .Ok .Fresh) :=
    belt_latch_fresh_accepts s0 _ hp0 (belt_latch_empty_no_replay hf0 _)
      (by rw [hne0]; exact Nat.le_refl _) (by rw [hcap]; dsimp only; decide)
      (by rw [hne0]; dsimp only; decide) rfl
  have hstep2 : BeltLatchKernel.bind s1 ⟨0#u64, msg, salt, digits, false⟩ =
      .ok (s1, .Ok .Replay) := belt_latch_replay_accepts s1 _ hp0 rfl rfl
  have hstep3 : BeltLatchKernel.bind s1 ⟨0#u64, msg, salt', digits, true⟩ =
      .ok (s1, .Err .RetrySaltMismatch) :=
    belt_latch_salt_mismatch_refused s1 _ hp0 rfl rfl rfl hne
  exact ⟨s0, s1, hnew, .step hstep1 (.step hstep2 (.step hstep3 (.nil s1))), rfl⟩

/-- `#tooth`: the durable-write input matters. The same fresh request binds when the log
accepts it and poisons the latch, binding nothing, when the log refuses it. -/
theorem tooth_belt_latch_persist_failure_poisons
    (msg salt : Array Std.U8 32#usize) (digits : BeltLatchDigits) :
    ∃ s0 sOk sBad,
      BeltLatchKernel.new_empty 8#u64 = .ok (.Ok s0) ∧
      BeltLatchKernel.bind s0 ⟨0#u64, msg, salt, digits, true⟩ = .ok (sOk, .Ok .Fresh) ∧
      BeltLatchKernel.bind s0 ⟨0#u64, msg, salt, digits, false⟩ =
        .ok (sBad, .Err .WalPersistFailed) ∧
      sOk.has_in_flight = true ∧ sBad.has_in_flight = false ∧ sBad.wal_poisoned = true ∧
      sBad.next_epoch = s0.next_epoch := by
  obtain ⟨s0, hnew, _, hcap, hne0, hf0, hp0⟩ :=
    (belt_latch_new_empty_spec 8#u64).1 ⟨by decide, by decide⟩
  exact ⟨s0, _, _, hnew,
    belt_latch_fresh_accepts s0 ⟨0#u64, msg, salt, digits, true⟩ hp0
      (belt_latch_empty_no_replay hf0 _) (by rw [hne0]; exact Nat.le_refl _)
      (by rw [hcap]; dsimp only; decide) (by rw [hne0]; dsimp only; decide) rfl,
    belt_latch_persist_failure s0 ⟨0#u64, msg, salt, digits, false⟩ hp0
      (belt_latch_empty_no_replay hf0 _) (by rw [hne0]; exact Nat.le_refl _)
      (by rw [hcap]; dsimp only; decide) (by rw [hne0]; dsimp only; decide) rfl,
    rfl, hf0, rfl, rfl⟩

/-- `#tooth`: the epoch window is enforced. From the empty latch, epoch 64 binds and epoch 65
is refused. -/
theorem tooth_belt_latch_epoch_window
    (msg salt : Array Std.U8 32#usize) (digits : BeltLatchDigits) :
    ∃ s0 s1,
      BeltLatchKernel.new_empty 1024#u64 = .ok (.Ok s0) ∧
      BeltLatchKernel.bind s0 ⟨64#u64, msg, salt, digits, true⟩ = .ok (s1, .Ok .Fresh) ∧
      BeltLatchKernel.bind s0 ⟨65#u64, msg, salt, digits, true⟩ =
        .ok (s0, .Err .EpochJumpTooLarge) := by
  obtain ⟨s0, hnew, _, hcap, hne0, hf0, hp0⟩ :=
    (belt_latch_new_empty_spec 1024#u64).1 ⟨by decide, by decide⟩
  exact ⟨s0, _, hnew,
    belt_latch_fresh_accepts s0 ⟨64#u64, msg, salt, digits, true⟩ hp0
      (belt_latch_empty_no_replay hf0 _) (by rw [hne0]; dsimp only; decide)
      (by rw [hcap]; dsimp only; decide) (by rw [hne0]; dsimp only; decide) rfl,
    belt_latch_jump_refused s0 ⟨65#u64, msg, salt, digits, true⟩ hp0
      (belt_latch_empty_no_replay hf0 _) (by rw [hne0]; dsimp only; decide)
      (by rw [hcap]; dsimp only; decide) (by rw [hne0]; dsimp only; decide)⟩

end qsag_verified.proofs

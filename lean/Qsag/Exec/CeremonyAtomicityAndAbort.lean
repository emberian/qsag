module
/-
# Qsag.Exec.CeremonyAtomicityAndAbort — Multi-Ledger Crash/Interleaving Ceremony Atomicity, Cut-the-Hash Selective-Abort Independence & Threshold ML-DSA-44 Joint Rejection Simulation

Constructive (`0 Classical.choice`) Lean 4.35 formalization closing:
1. **Multi-Ledger Burn-Before-Release Crash & Interleaving Composition**:
   - Models the five separate durable host ledgers (`PoisonLatch`, `PolicyWindowLedger`,
     `PreprocCursorLedger`, `LeafOrFtsBurnLedger`, and `OutboundNetworkWire`) backed by
     independent alternating two-slot authenticated snapshots (`TwoSlotWal`, mirroring
     `durable_ledger.rs`), recovered independently without atomic cross-file two-phase commit
     (2PC), across interleaved multi-ceremony executions (`ceremonyId : Nat`).
   - Recovery is FAIL-CLOSED (`recoverTwoSlotWal : Option`): the highest authenticated slot at or
     above the external checkpoint `anchorGen`, and nothing otherwise. The checkpoint is a
     separate, later write (`SaveCheckpoint`), a minimum generation rather than an exact snapshot.
   - `PowerLossCrash` may strike between ANY two individual ledger writes, with an independent
     mode per ledger file: staged write dropped, staged write torn into the inactive slot, staged
     write flushed, or the ACTIVE slot itself lost (`tornActiveSlot`), after which that ledger
     either rolls back to its checkpoint-admissible older snapshot or stops opening.
   - Formalizes the **Monotone Burn-Before-Release Protocol**: `EmitNetworkShare` is permitted
     ONLY with durable commits in strict causal order
     `(1) PoisonLatch == Clean`, `(2) PolicySpendCommitted`, `(3) PreprocBatchBurned`,
     `(4) LeafOrFtsReserved`, AND with the external checkpoints of all three burn ledgers saved
     (`ledgersCheckpointSaved`), so every release is backed by the snapshot no crash can undo.
   - Proves inductively over arbitrary multi-crash, multi-ceremony traces:
     `no_preproc_batch_reused_on_wire`, `no_leaf_double_sign_on_wire`, `wire_spend_le_policy_cap`,
     the unified `ceremony_multi_ledger_crash_interleaving_safe`, and
     `failed_closed_host_stays_closed` (a host with an unopenable ledger never emits again),
     paired with `#tooth` counterexamples `tooth_release_before_durable_burn_reuses_leaf`
     (release before the durable flush) and `tooth_release_before_checkpoint_rolls_back_leaf`
     (release after the flush but before the checkpoint).
2. **Selective-Abort Statistical Independence for Cut-the-Hash**:
   - Formalizes the 2-phase Cut-the-Hash signing transcript (`Phase 1: masked Beaver/BDOZ diffs`
     `d_i = x_i - a_i` + `COMMIT(y_share, mac_share)` -> `MAC-OK barrier` -> `Phase 2: OPEN(y_share)`)
     against a RUSHING corrupt party (`RushingCorruptStrategy`) whose contributions are chosen
     after seeing the honest openings of the same round.
   - Commitment hiding is an explicit hypothesis of the specification (`commitHiding`: for every
     committed pair the blinding mask maps bijectively onto the tag space), not a built-in pad.
   - Constructs the explicit `SimpleEquiv` mask bijection `maskBijection`: for every fixed secret
     key, message, randomizer and rushing strategy, the adversary's entire pre-`OPEN` view is
     uniform and independent of `(sk, finalSignature sk msg R)`.
   - Proves `cutTheHash_abort_conditioned_sd_zero`: for EVERY rushing strategy and EVERY abort
     predicate on the pre-`OPEN` view with non-zero survival count, the surviving signature
     distribution has exact statistical distance `0` from the standalone signer, paired with
     `#tooth` witnesses `tooth_early_open_before_mac_barrier_skews_distribution` (`y_0` opened
     early) and `tooth_unblinded_commit_skews_distribution` (commitment sent without blinding).
3. **Threshold ML-DSA-44 Rejection Independence, Both Checks**:
   - `mldsa_rejection_valid_output_uniform_in_box`: the `‖z‖_∞ < γ₁ - β` check alone leaves
     `z = y + c·s₁` uniform on the safe box, independent of `s₁` (plus vector lifting and the
     deployed `γ₁ = 131072, β = 78` instance), with `#tooth`
     `tooth_mldsa_unclipped_z_leaks_secret_shift`.
   - FIPS 204 `Decompose` / `HighBits` / `LowBits` at `q = 8380417, γ₂ = 95232`, with
     `mldsa44_highBits_shift_invariant` (`‖LowBits(r)‖ < γ₂ - β ∧ |s| ≤ β → HighBits(r + s) =
     HighBits(r)`) and `mldsa44_low_range_test_iff` (the deployed masked range test is exactly
     `HighBits = w₁ ∧ ‖LowBits‖ < γ₂ - β`).
   - `mldsa44_joint_transcript_simulation`, `mldsa44JointTranscriptEquiv` and
     `mldsa44_joint_transcript_secret_independent`: under BOTH rejection checks the accepted
     `(w₁, z)` transcript for a fixed challenge is the image of a bijection onto responses accepted
     by a simulator that reads only public `(A, c·t, z)`; in particular
     `w₁ = HighBits(A·y) = HighBits(A·z - c·t)`. Paired with `#tooth`
     `tooth_mldsa44_low_bits_margin_omitted_leaks_s2` (a bare `γ₂` bound lets `c·s₂` flip
     `HighBits`).
   - §3b works in the ring `ℤ_q[X]/(X^n + 1)` (`polyMul`, proved commutative and associative
     with unit): `mldsa44_challenge_times_secret_le_beta` derives `‖c·s‖∞ ≤ 78` from
     `c ∈ B_39`, `‖s‖∞ ≤ 2`; `mldsa44_ring_key_relation` derives the key relation from
     `t ≡ A·s₁ + s₂`; `mldsa44_ring_joint_transcript_simulation` is the simulation statement for
     ring vectors.
   - Rejected attempts: `lin_rejected_commitment_count_secret_independent` (the `w₁` published
     by an abort has the same count under any two secrets consistent with the public data).
   - `c = H(μ, w₁)` in the lazily sampled random-oracle model: `roAttempt_reprogramming_bound`
     (`|log| · M` per attempt, `M` the largest commitment fibre) and
     `multiAttempt_reprogramming_bound` (union bound over attempts and interleaved adversary
     queries).
4. **Welds and random-oracle hiding added to §1 and §2**:
   - §1 is welded onto `Qsag.PosixCrashWal`: `posix_crash_during_slot_write_refines`,
     `posix_media_damage_refines`, `posix_device_restore_below_anchor_fails_closed`. The crash
     modes gain `idleSlotDamaged`; `AdvancePolicyWindow` stages and `FlushPolicyWindowWal`
     flushes, with crashes permitted in between.
   - §2b: `cutTheHash_rom_commit_hiding_sd_bound` gives statistical distance
     `q_RO / 2^256` for `commit = RO(domain ‖ y ‖ mac ‖ blind)` against a rushing oracle
     adversary, paired with `tooth_rom_commit_without_framed_blind_exceeds_bound`.
-/

public import Qsag.Protocol.Threshold.MlDsa44Parameters
public import Qsag.Math.Digest256
public import Qsag.Math.Constructive
public import Qsag.Exec.SimulationSpine
public import Qsag.Math.Goldilocks
public import Qsag.Math.BinaryTower
public import Qsag.Oracle.UcGames
public import Qsag.Exec.PosixCrashWal
public import Qsag.Tactic.AssuranceKit

import all Qsag.Math.Constructive
import all Qsag.Exec.SimulationSpine
import all Qsag.Math.Goldilocks
import all Qsag.Math.BinaryTower
import all Qsag.Oracle.UcGames

public section
namespace Qsag

set_option autoImplicit false

/-! ## §1. Five-Ledger Crash/Interleaving Ceremony Atomicity (Zero Cross-File 2PC) -/

/-- Persistent on-disk slot of an alternating two-slot write-ahead log (`slot_a` / `slot_b`). -/
structure WalSlot (S : Type) where
  generation : Nat
  payload : S
  macValid : Bool
  deriving Repr, DecidableEq

/-- Alternating two-slot authenticated snapshot ledger (`durable_ledger.rs`):
    - `slotEven` / `slotOdd` hold generations of matching parity (`generation % 2 == slot`);
    - `anchorGen` is the independently retained external checkpoint: a MINIMUM generation kept
      outside the snapshot's rollback domain, not an exact snapshot (a durable successor whose
      checkpoint was not yet saved is still accepted on recovery);
    - `volatileStage` is an uncommitted write sitting in OS page cache;
    - `genesisPayload` is only the provisioning payload; recovery never falls back to it. -/
structure TwoSlotWal (S : Type) where
  slotEven : Option (WalSlot S)
  slotOdd : Option (WalSlot S)
  anchorGen : Nat
  genesisPayload : S
  volatileStage : Option (Nat × S)
  deriving Repr, DecidableEq

/-- Validate a single WAL slot against anti-rollback `anchor`, slot parity (`0` or `1`), and MAC tag. -/
def walSlotUsable {S : Type} (anchor parity : Nat) : Option (WalSlot S) → Option (Nat × S)
  | none => none
  | some s =>
    if s.macValid && decide (anchor ≤ s.generation) && decide (s.generation % 2 = parity) then
      some (s.generation, s.payload)
    else
      none

/-- Fail-closed recovery of the two-slot ledger (`Ledger::open`, `best.ok_or(())`): the
    highest-generation authenticated slot at or above the external checkpoint, and `none` when no
    slot qualifies. There is NO fallback to the genesis payload. -/
@[expose] def recoverTwoSlotWal {S : Type} (wal : TwoSlotWal S) : Option (Nat × S) :=
  match walSlotUsable wal.anchorGen 0 wal.slotEven, walSlotUsable wal.anchorGen 1 wal.slotOdd with
  | some (ge, pe), some (go, po) =>
    if ge ≤ go then some (go, po) else some (ge, pe)
  | some (ge, pe), none => some (ge, pe)
  | none, some (go, po) => some (go, po)
  | none, none => none

/-- Worst-case snapshot that survives damage to either single slot: the LOWEST-generation
    authenticated slot at or above the external checkpoint. Anything released to the network must
    be backed by this snapshot, because a later loss of the active slot rolls recovery back to it. -/
def rollbackFloorWal {S : Type} (wal : TwoSlotWal S) : Option (Nat × S) :=
  match walSlotUsable wal.anchorGen 0 wal.slotEven, walSlotUsable wal.anchorGen 1 wal.slotOdd with
  | some (ge, pe), some (go, po) =>
    if ge ≤ go then some (ge, pe) else some (go, po)
  | some (ge, pe), none => some (ge, pe)
  | none, some (go, po) => some (go, po)
  | none, none => none

/-- The ledger can be opened: some slot authenticates at or above the external checkpoint. -/
def walRecoverable {S : Type} (wal : TwoSlotWal S) : Bool :=
  (walSlotUsable wal.anchorGen 0 wal.slotEven).isSome ||
  (walSlotUsable wal.anchorGen 1 wal.slotOdd).isSome

/-- Active durable generation recovered from `wal`. Every host transition that reads it is gated
    on `walRecoverable`; the default is never consumed by a guarded step. -/
@[expose] def activeWalGen {S : Type} (wal : TwoSlotWal S) : Nat :=
  ((recoverTwoSlotWal wal).getD (wal.anchorGen, wal.genesisPayload)).1

/-- Active durable payload recovered from `wal` (gated on `walRecoverable` like `activeWalGen`). -/
@[expose] def activeWalPayload {S : Type} (wal : TwoSlotWal S) : S :=
  ((recoverTwoSlotWal wal).getD (wal.anchorGen, wal.genesisPayload)).2

/-- Payload of the rollback floor: what recovery still returns after the active slot is lost. -/
def checkpointedWalPayload {S : Type} (wal : TwoSlotWal S) : S :=
  ((rollbackFloorWal wal).getD (wal.anchorGen, wal.genesisPayload)).2

/-- The external checkpoint has caught up with the active generation
    ("persist outside the snapshot's rollback domain before releasing reserved material"). -/
def walCheckpointSaved {S : Type} (wal : TwoSlotWal S) : Bool :=
  walRecoverable wal && decide (wal.anchorGen = activeWalGen wal)

/-- Initialize a fresh two-slot WAL at generation `0` in `slotEven`. -/
def initTwoSlotWal {S : Type} (p0 : S) : TwoSlotWal S where
  slotEven := some { generation := 0, payload := p0, macValid := true }
  slotOdd := none
  anchorGen := 0
  genesisPayload := p0
  volatileStage := none

/-- Write generation `g` into slot `g % 2`, leaving the opposite slot `(g + 1) % 2` untouched. -/
def writeDurableWalSlot {S : Type} (wal : TwoSlotWal S) (g : Nat) (p : S) (macOk : Bool) :
    TwoSlotWal S :=
  let slot : WalSlot S := { generation := g, payload := p, macValid := macOk }
  if g % 2 = 0 then
    { wal with slotEven := some slot, volatileStage := none }
  else
    { wal with slotOdd := some slot, volatileStage := none }

/-- Stage a candidate next generation `activeWalGen wal + 1` in volatile OS page cache without
    mutating either durable disk slot yet. -/
def stageTwoSlotWal {S : Type} (wal : TwoSlotWal S) (nextPayload : S) : TwoSlotWal S :=
  { wal with volatileStage := some (activeWalGen wal + 1, nextPayload) }

/-- Durably `fsync + rename + dir_fsync` the staged write into its alternating parity slot. The
    external checkpoint does NOT move: saving it is the separate step `saveWalCheckpoint`. -/
def flushTwoSlotWal {S : Type} (wal : TwoSlotWal S) : TwoSlotWal S :=
  match wal.volatileStage with
  | none => wal
  | some (g, p) => writeDurableWalSlot wal g p true

/-- Persist the external checkpoint at the active generation. Older snapshots stop being
    acceptable recovery results from this point on. -/
def saveWalCheckpoint {S : Type} (wal : TwoSlotWal S) : TwoSlotWal S :=
  { wal with anchorGen := activeWalGen wal }

/-- A slot whose contents no longer authenticate (torn sector, lost sidecar, media damage). -/
def invalidateWalSlot {S : Type} : Option (WalSlot S) → Option (WalSlot S)
  | none => none
  | some s => some { generation := s.generation, payload := s.payload, macValid := false }

/-- Power loss damages the ACTIVE slot itself and drops the staged write. -/
def tearActiveWalSlot {S : Type} (wal : TwoSlotWal S) : TwoSlotWal S :=
  if activeWalGen wal % 2 = 0 then
    { wal with slotEven := invalidateWalSlot wal.slotEven, volatileStage := none }
  else
    { wal with slotOdd := invalidateWalSlot wal.slotOdd, volatileStage := none }

/-- Media damage to the slot that is NOT the active one (bit-rot or a bad block on the idle
    older snapshot), together with loss of anything staged. The active snapshot is untouched. -/
def damageIdleWalSlot {S : Type} (wal : TwoSlotWal S) : TwoSlotWal S :=
  if activeWalGen wal % 2 = 0 then
    { wal with slotOdd := invalidateWalSlot wal.slotOdd, volatileStage := none }
  else
    { wal with slotEven := invalidateWalSlot wal.slotEven, volatileStage := none }

/-- Per-ledger non-atomic OS crash behavior on sudden `PowerLossCrash`:
    - `dropVolatile`: uncommitted staging buffer is lost cleanly;
    - `tornInactiveWrite`: uncommitted write partially hits the inactive slot with invalid MAC;
    - `flushedBeforePowerLoss`: kernel page cache happened to flush this single file before power died
      (independently of all other ledger files — NO cross-file 2PC!);
    - `tornActiveSlot`: the active slot itself stops authenticating. Recovery then either rolls
      back to the older slot (when the external checkpoint still admits it) or fails closed. -/
inductive WalCrashBehavior where
  | dropVolatile
  | tornInactiveWrite
  | flushedBeforePowerLoss
  | tornActiveSlot
  | idleSlotDamaged
  deriving Repr, DecidableEq

/-- Independent single-ledger crash recovery on `PowerLossCrash`. -/
def crashRecoverWal {S : Type} (mode : WalCrashBehavior) (wal : TwoSlotWal S) : TwoSlotWal S :=
  match mode with
  | .dropVolatile => { wal with volatileStage := none }
  | .tornInactiveWrite =>
    match wal.volatileStage with
    | none => wal
    | some (g, p) => writeDurableWalSlot wal g p false
  | .flushedBeforePowerLoss =>
    match wal.volatileStage with
    | none => wal
    | some (g, p) => writeDurableWalSlot wal g p true
  | .tornActiveSlot => tearActiveWalSlot wal
  | .idleSlotDamaged => damageIdleWalSlot wal

/-- `walRecoverable` is exactly "fail-closed recovery returns a snapshot". -/
theorem walRecoverable_eq_isSome {S : Type} (wal : TwoSlotWal S) :
    walRecoverable wal = (recoverTwoSlotWal wal).isSome := by
  unfold walRecoverable recoverTwoSlotWal
  cases walSlotUsable wal.anchorGen 0 wal.slotEven with
  | none =>
    cases walSlotUsable wal.anchorGen 1 wal.slotOdd with
    | none => rfl
    | some o => rfl
  | some e =>
    cases walSlotUsable wal.anchorGen 1 wal.slotOdd with
    | none => rfl
    | some o =>
      dsimp only
      split <;> rfl

private theorem walSlotUsable_inv {S : Type} {a par g : Nat} {p : S} {s : Option (WalSlot S)}
    (h : walSlotUsable a par s = some (g, p)) :
    s = some { generation := g, payload := p, macValid := true } ∧ a ≤ g ∧ g % 2 = par := by
  cases s with
  | none => simp [walSlotUsable] at h
  | some x =>
    cases x with
    | mk xg xp xm =>
      simp only [walSlotUsable] at h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        injection h with h
        injection h with h1 h2
        subst h1
        subst h2
        obtain ⟨⟨hm, ha⟩, hp⟩ := hc
        subst hm
        exact ⟨rfl, ha, hp⟩
      · cases h

private theorem walSlotUsable_valid {S : Type} {a par g : Nat} (p : S)
    (ha : a ≤ g) (hp : g % 2 = par) :
    walSlotUsable a par (some { generation := g, payload := p, macValid := true }) = some (g, p) := by
  simp [walSlotUsable, ha, hp]

private theorem walSlotUsable_anchor_ge {S : Type} {a a' par g : Nat} {p : S}
    {s : Option (WalSlot S)}
    (h : walSlotUsable a par s = some (g, p)) (ha' : a' ≤ g) :
    walSlotUsable a' par s = some (g, p) := by
  obtain ⟨hs, _, hp⟩ := walSlotUsable_inv h
  rw [hs]
  exact walSlotUsable_valid p ha' hp

private theorem walSlotUsable_anchor_gt {S : Type} {a a' par g : Nat} {p : S}
    {s : Option (WalSlot S)}
    (h : walSlotUsable a par s = some (g, p)) (ha' : g < a') :
    walSlotUsable a' par s = none := by
  obtain ⟨hs, _, _⟩ := walSlotUsable_inv h
  have hNot : ¬ a' ≤ g := by omega
  rw [hs]
  simp [walSlotUsable, hNot]

private theorem walSlotUsable_none_mono {S : Type} {a a' par : Nat} {s : Option (WalSlot S)}
    (hle : a ≤ a') (h : walSlotUsable a par s = none) :
    walSlotUsable a' par s = none := by
  cases hU : walSlotUsable a' par s with
  | none => rfl
  | some x =>
    obtain ⟨g, p⟩ := x
    obtain ⟨hs, ha, hp⟩ := walSlotUsable_inv hU
    rw [hs, walSlotUsable_valid p (Nat.le_trans hle ha) hp] at h
    cases h

private theorem walSlotUsable_invalidate {S : Type} (a par : Nat) (s : Option (WalSlot S)) :
    walSlotUsable a par (invalidateWalSlot s) = none := by
  cases s with
  | none => rfl
  | some x => rfl

private theorem writeDurableWalSlot_stage_none {S : Type} (wal : TwoSlotWal S) (g : Nat) (p : S)
    (m : Bool) : (writeDurableWalSlot wal g p m).volatileStage = none := by
  unfold writeDurableWalSlot
  dsimp only
  split <;> rfl

private theorem tearActiveWalSlot_stage_none {S : Type} (wal : TwoSlotWal S) :
    (tearActiveWalSlot wal).volatileStage = none := by
  unfold tearActiveWalSlot
  split <;> rfl

/-- The older slot, when it still authenticates, is exactly one generation behind the active one
    and its payload is a `rel`-predecessor satisfying `inv`. -/
private def WalOlderOk {S : Type} (rel : S → S → Prop) (inv : S → Prop) (g : Nat) (p : S) :
    Option (Nat × S) → Prop
  | none => True
  | some (g', pp) => g' + 1 = g ∧ rel pp p ∧ inv pp

/-- A healthy ledger: one parity slot holds the active `(g, p)`, the other is `WalOlderOk`. -/
private def WalShape {S : Type} (rel : S → S → Prop) (inv : S → Prop) (wal : TwoSlotWal S)
    (g : Nat) (p : S) : Prop :=
  (walSlotUsable wal.anchorGen 0 wal.slotEven = some (g, p) ∧
    WalOlderOk rel inv g p (walSlotUsable wal.anchorGen 1 wal.slotOdd)) ∨
  (walSlotUsable wal.anchorGen 1 wal.slotOdd = some (g, p) ∧
    WalOlderOk rel inv g p (walSlotUsable wal.anchorGen 0 wal.slotEven))

private structure TwoSlotWalInv {S : Type} (rel : S → S → Prop) (inv : S → Prop)
    (wal : TwoSlotWal S) : Prop where
  shape : ∃ g p, inv p ∧ WalShape rel inv wal g p
  stage_ok :
    match wal.volatileStage with
    | none => True
    | some (gNext, pNext) =>
      gNext = activeWalGen wal + 1 ∧ rel (activeWalPayload wal) pNext ∧ inv pNext

private theorem walShape_view {S : Type} {rel : S → S → Prop} {inv : S → Prop}
    {wal : TwoSlotWal S} {g : Nat} {p : S} (hShape : WalShape rel inv wal g p) :
    recoverTwoSlotWal wal = some (g, p) ∧ walRecoverable wal = true ∧ wal.anchorGen ≤ g ∧
    (rollbackFloorWal wal = some (g, p) ∨
     ∃ pp, rollbackFloorWal wal = some (g - 1, pp) ∧ wal.anchorGen + 1 ≤ g ∧ rel pp p ∧ inv pp) := by
  rcases hShape with ⟨hE, hO⟩ | ⟨hO, hE⟩
  · obtain ⟨_, haE, _⟩ := walSlotUsable_inv hE
    cases hOdd : walSlotUsable wal.anchorGen 1 wal.slotOdd with
    | none =>
      refine ⟨?_, ?_, haE, Or.inl ?_⟩
      · simp [recoverTwoSlotWal, hE, hOdd]
      · simp [walRecoverable, hE]
      · simp [rollbackFloorWal, hE, hOdd]
    | some x =>
      obtain ⟨g', pp⟩ := x
      rw [hOdd] at hO
      obtain ⟨hg, hrel, hpp⟩ := hO
      obtain ⟨_, haO, _⟩ := walSlotUsable_inv hOdd
      have hg' : g' = g - 1 := by omega
      subst hg'
      have hNle : ¬ g ≤ g - 1 := by omega
      refine ⟨?_, ?_, haE, Or.inr ⟨pp, ?_, by omega, hrel, hpp⟩⟩
      · simp [recoverTwoSlotWal, hE, hOdd, hNle]
      · simp [walRecoverable, hE]
      · simp [rollbackFloorWal, hE, hOdd, hNle]
  · obtain ⟨_, haO, _⟩ := walSlotUsable_inv hO
    cases hEven : walSlotUsable wal.anchorGen 0 wal.slotEven with
    | none =>
      refine ⟨?_, ?_, haO, Or.inl ?_⟩
      · simp [recoverTwoSlotWal, hO, hEven]
      · simp [walRecoverable, hO]
      · simp [rollbackFloorWal, hO, hEven]
    | some x =>
      obtain ⟨g', pp⟩ := x
      rw [hEven] at hE
      obtain ⟨hg, hrel, hpp⟩ := hE
      obtain ⟨_, haE, _⟩ := walSlotUsable_inv hEven
      have hg' : g' = g - 1 := by omega
      subst hg'
      have hLe : g - 1 ≤ g := by omega
      refine ⟨?_, ?_, haO, Or.inr ⟨pp, ?_, by omega, hrel, hpp⟩⟩
      · simp [recoverTwoSlotWal, hO, hEven, hLe]
      · simp [walRecoverable, hO]
      · simp [rollbackFloorWal, hO, hEven, hLe]

private theorem walInv_of_shape {S : Type} {rel : S → S → Prop} {inv : S → Prop}
    {wal : TwoSlotWal S} {g : Nat} {p : S}
    (hShape : WalShape rel inv wal g p) (hp : inv p) (hStage : wal.volatileStage = none) :
    TwoSlotWalInv rel inv wal :=
  ⟨⟨g, p, hp, hShape⟩, by rw [hStage]; exact True.intro⟩

/-- Everything the host layer needs to know about a healthy ledger. -/
private theorem walInv_facts {S : Type} {rel : S → S → Prop} {inv : S → Prop}
    {wal : TwoSlotWal S} (hRefl : ∀ x, rel x x) (h : TwoSlotWalInv rel inv wal) :
    walRecoverable wal = true ∧ inv (activeWalPayload wal) ∧
    inv (checkpointedWalPayload wal) ∧
    rel (checkpointedWalPayload wal) (activeWalPayload wal) := by
  obtain ⟨g, p, hp, hShape⟩ := h.shape
  obtain ⟨hRec, hOk, _, hFloor⟩ := walShape_view hShape
  have hPay : activeWalPayload wal = p := by simp [activeWalPayload, hRec]
  rcases hFloor with hF | ⟨pp, hF, _, hrel, hpp⟩
  · have hC : checkpointedWalPayload wal = p := by simp [checkpointedWalPayload, hF]
    rw [hPay, hC]
    exact ⟨hOk, hp, hp, hRefl p⟩
  · have hC : checkpointedWalPayload wal = pp := by simp [checkpointedWalPayload, hF]
    rw [hPay, hC]
    exact ⟨hOk, hp, hpp, hrel⟩

private theorem walInv_active {S : Type} {rel : S → S → Prop} {inv : S → Prop}
    {wal : TwoSlotWal S} (h : TwoSlotWalInv rel inv wal) : inv (activeWalPayload wal) := by
  obtain ⟨g, p, hp, hShape⟩ := h.shape
  obtain ⟨hRec, _⟩ := walShape_view hShape
  have hPay : activeWalPayload wal = p := by simp [activeWalPayload, hRec]
  rw [hPay]
  exact hp

/-- Once the external checkpoint has caught up, the rollback floor IS the active snapshot: no
    crash mode can make recovery return anything older. -/
private theorem walInv_saved_floor {S : Type} {rel : S → S → Prop} {inv : S → Prop}
    {wal : TwoSlotWal S} (h : TwoSlotWalInv rel inv wal) (hSaved : walCheckpointSaved wal = true) :
    checkpointedWalPayload wal = activeWalPayload wal := by
  obtain ⟨g, p, hp, hShape⟩ := h.shape
  obtain ⟨hRec, _, _, hFloor⟩ := walShape_view hShape
  have hGen : activeWalGen wal = g := by simp [activeWalGen, hRec]
  have hPay : activeWalPayload wal = p := by simp [activeWalPayload, hRec]
  unfold walCheckpointSaved at hSaved
  rw [Bool.and_eq_true, decide_eq_true_iff, hGen] at hSaved
  rcases hFloor with hF | ⟨pp, _, hLag, _, _⟩
  · have hC : checkpointedWalPayload wal = p := by simp [checkpointedWalPayload, hF]
    rw [hPay, hC]
  · exfalso
    have := hSaved.2
    omega

private theorem initTwoSlotWal_inv {S : Type} (rel : S → S → Prop) {inv : S → Prop}
    {p0 : S} (hp0 : inv p0) :
    TwoSlotWalInv rel inv (initTwoSlotWal p0) :=
  ⟨⟨0, p0, hp0, Or.inl ⟨rfl, True.intro⟩⟩, True.intro⟩

private theorem stageTwoSlotWal_inv {S : Type} {rel : S → S → Prop} {inv : S → Prop}
    {wal : TwoSlotWal S} {pNext : S}
    (hWal : TwoSlotWalInv rel inv wal)
    (hRel : rel (activeWalPayload wal) pNext)
    (hNext : inv pNext) :
    TwoSlotWalInv rel inv (stageTwoSlotWal wal pNext) ∧
    checkpointedWalPayload (stageTwoSlotWal wal pNext) = checkpointedWalPayload wal :=
  ⟨⟨hWal.shape, ⟨rfl, hRel, hNext⟩⟩, rfl⟩

/-- Writing generation `g + 1` into the inactive parity slot. An authenticated write advances the
    active snapshot and keeps the old one as rollback floor; a torn write leaves the active
    snapshot in place. Either way the rollback floor becomes the previously active snapshot. -/
private theorem writeDurableWalSlot_shape {S : Type} {rel : S → S → Prop} {inv : S → Prop}
    {wal : TwoSlotWal S} {g : Nat} {p : S}
    (hShape : WalShape rel inv wal g p) (hp : inv p) (pNext : S) (mac : Bool)
    (hRel : mac = true → rel p pNext ∧ inv pNext) :
    (mac = true → WalShape rel inv (writeDurableWalSlot wal (g + 1) pNext mac) (g + 1) pNext) ∧
    (mac = false → WalShape rel inv (writeDurableWalSlot wal (g + 1) pNext mac) g p) ∧
    rollbackFloorWal (writeDurableWalSlot wal (g + 1) pNext mac) = some (g, p) := by
  rcases hShape with ⟨hE, _⟩ | ⟨hO, _⟩
  · obtain ⟨_, ha, hpar⟩ := walSlotUsable_inv hE
    have hNe : (g + 1) % 2 ≠ 0 := by omega
    have hW : writeDurableWalSlot wal (g + 1) pNext mac =
        { wal with slotOdd := some { generation := g + 1, payload := pNext, macValid := mac },
                   volatileStage := none } := by
      simp [writeDurableWalSlot, hNe]
    rw [hW]
    cases mac with
    | true =>
      have hNew : walSlotUsable wal.anchorGen 1
          (some { generation := g + 1, payload := pNext, macValid := true }) = some (g + 1, pNext) :=
        walSlotUsable_valid pNext (by omega) (by omega)
      obtain ⟨hr, _⟩ := hRel rfl
      have hOlder : WalOlderOk rel inv (g + 1) pNext (walSlotUsable wal.anchorGen 0 wal.slotEven) := by
        rw [hE]; exact ⟨rfl, hr, hp⟩
      refine ⟨fun _ => Or.inr ⟨hNew, hOlder⟩, (fun h => Bool.noConfusion h), ?_⟩
      simp [rollbackFloorWal, hE, hNew]
    | false =>
      have hNew : walSlotUsable wal.anchorGen 1
          (some { generation := g + 1, payload := pNext, macValid := false }) = none := rfl
      have hOlder : WalOlderOk rel inv g p (walSlotUsable wal.anchorGen 1
          (some { generation := g + 1, payload := pNext, macValid := false })) := by
        rw [hNew]; exact True.intro
      refine ⟨(fun h => Bool.noConfusion h), fun _ => Or.inl ⟨hE, hOlder⟩, ?_⟩
      simp [rollbackFloorWal, hE, hNew]
  · obtain ⟨_, ha, hpar⟩ := walSlotUsable_inv hO
    have hEv : (g + 1) % 2 = 0 := by omega
    have hW : writeDurableWalSlot wal (g + 1) pNext mac =
        { wal with slotEven := some { generation := g + 1, payload := pNext, macValid := mac },
                   volatileStage := none } := by
      simp [writeDurableWalSlot, hEv]
    rw [hW]
    cases mac with
    | true =>
      have hNew : walSlotUsable wal.anchorGen 0
          (some { generation := g + 1, payload := pNext, macValid := true }) = some (g + 1, pNext) :=
        walSlotUsable_valid pNext (by omega) hEv
      obtain ⟨hr, _⟩ := hRel rfl
      have hOlder : WalOlderOk rel inv (g + 1) pNext (walSlotUsable wal.anchorGen 1 wal.slotOdd) := by
        rw [hO]; exact ⟨rfl, hr, hp⟩
      have hNle : ¬ g + 1 ≤ g := by omega
      refine ⟨fun _ => Or.inl ⟨hNew, hOlder⟩, (fun h => Bool.noConfusion h), ?_⟩
      simp [rollbackFloorWal, hO, hNew, hNle]
    | false =>
      have hNew : walSlotUsable wal.anchorGen 0
          (some { generation := g + 1, payload := pNext, macValid := false }) = none := rfl
      have hOlder : WalOlderOk rel inv g p (walSlotUsable wal.anchorGen 0
          (some { generation := g + 1, payload := pNext, macValid := false })) := by
        rw [hNew]; exact True.intro
      refine ⟨(fun h => Bool.noConfusion h), fun _ => Or.inr ⟨hO, hOlder⟩, ?_⟩
      simp [rollbackFloorWal, hO, hNew]

private theorem writeDurableWalSlot_inv {S : Type} {rel : S → S → Prop} {inv : S → Prop}
    {wal : TwoSlotWal S} (hRefl : ∀ x, rel x x) (hWal : TwoSlotWalInv rel inv wal)
    (pNext : S) (mac : Bool)
    (hRel : mac = true → rel (activeWalPayload wal) pNext ∧ inv pNext) :
    TwoSlotWalInv rel inv (writeDurableWalSlot wal (activeWalGen wal + 1) pNext mac) ∧
    rel (checkpointedWalPayload wal)
      (checkpointedWalPayload (writeDurableWalSlot wal (activeWalGen wal + 1) pNext mac)) := by
  obtain ⟨g, p, hp, hShape⟩ := hWal.shape
  obtain ⟨hRec, _⟩ := walShape_view hShape
  have hGen : activeWalGen wal = g := by simp [activeWalGen, hRec]
  have hPay : activeWalPayload wal = p := by simp [activeWalPayload, hRec]
  obtain ⟨_, _, _, hFloorRel⟩ := walInv_facts hRefl hWal
  rw [hPay] at hRel hFloorRel
  rw [hGen]
  obtain ⟨hT, hF, hFloor'⟩ := writeDurableWalSlot_shape hShape hp pNext mac hRel
  have hC' : checkpointedWalPayload (writeDurableWalSlot wal (g + 1) pNext mac) = p := by
    simp [checkpointedWalPayload, hFloor']
  rw [hC']
  refine ⟨?_, hFloorRel⟩
  cases mac with
  | true =>
    exact walInv_of_shape (hT rfl) (hRel rfl).2 (writeDurableWalSlot_stage_none _ _ _ _)
  | false =>
    exact walInv_of_shape (hF rfl) hp (writeDurableWalSlot_stage_none _ _ _ _)

private theorem flushTwoSlotWal_inv {S : Type} {rel : S → S → Prop} {inv : S → Prop}
    {wal : TwoSlotWal S} (hRefl : ∀ x, rel x x) (hWal : TwoSlotWalInv rel inv wal) :
    TwoSlotWalInv rel inv (flushTwoSlotWal wal) ∧
    (flushTwoSlotWal wal).volatileStage = none ∧
    rel (checkpointedWalPayload wal) (checkpointedWalPayload (flushTwoSlotWal wal)) := by
  unfold flushTwoSlotWal
  cases hStage : wal.volatileStage with
  | none =>
    exact ⟨hWal, hStage, hRefl _⟩
  | some gp =>
    rcases gp with ⟨gNext, pNext⟩
    have hSt := hWal.stage_ok
    rw [hStage] at hSt
    rcases hSt with ⟨rfl, hRel, hNextInv⟩
    obtain ⟨hInv', hRel'⟩ :=
      writeDurableWalSlot_inv hRefl hWal pNext true (fun _ => ⟨hRel, hNextInv⟩)
    exact ⟨hInv', writeDurableWalSlot_stage_none _ _ _ _, hRel'⟩

/-- Saving the external checkpoint retires the older slot: the rollback floor rises to the active
    snapshot and the ledger stays healthy. -/
private theorem saveWalCheckpoint_inv {S : Type} {rel : S → S → Prop} {inv : S → Prop}
    {wal : TwoSlotWal S} (hRefl : ∀ x, rel x x) (hWal : TwoSlotWalInv rel inv wal)
    (hStage : wal.volatileStage = none) :
    TwoSlotWalInv rel inv (saveWalCheckpoint wal) ∧
    rel (checkpointedWalPayload wal) (checkpointedWalPayload (saveWalCheckpoint wal)) := by
  obtain ⟨g, p, hp, hShape⟩ := hWal.shape
  obtain ⟨hRec, _⟩ := walShape_view hShape
  have hGen : activeWalGen wal = g := by simp [activeWalGen, hRec]
  have hPay : activeWalPayload wal = p := by simp [activeWalPayload, hRec]
  obtain ⟨_, _, _, hFloorRel⟩ := walInv_facts hRefl hWal
  rw [hPay] at hFloorRel
  have hSave : saveWalCheckpoint wal = { wal with anchorGen := g } := by
    simp [saveWalCheckpoint, hGen]
  rw [hSave]
  have hShape' : WalShape rel inv { wal with anchorGen := g } g p := by
    rcases hShape with ⟨hE, hO⟩ | ⟨hO, hE⟩
    · obtain ⟨_, ha, _⟩ := walSlotUsable_inv hE
      have hE' : walSlotUsable g 0 wal.slotEven = some (g, p) :=
        walSlotUsable_anchor_ge hE (Nat.le_refl g)
      have hO' : walSlotUsable g 1 wal.slotOdd = none := by
        cases hOdd : walSlotUsable wal.anchorGen 1 wal.slotOdd with
        | none => exact walSlotUsable_none_mono ha hOdd
        | some x =>
          obtain ⟨g', pp⟩ := x
          rw [hOdd] at hO
          exact walSlotUsable_anchor_gt hOdd (by have := hO.1; omega)
      have hOlder : WalOlderOk rel inv g p (walSlotUsable g 1 wal.slotOdd) := by
        rw [hO']; exact True.intro
      exact Or.inl ⟨hE', hOlder⟩
    · obtain ⟨_, ha, _⟩ := walSlotUsable_inv hO
      have hO' : walSlotUsable g 1 wal.slotOdd = some (g, p) :=
        walSlotUsable_anchor_ge hO (Nat.le_refl g)
      have hE' : walSlotUsable g 0 wal.slotEven = none := by
        cases hEven : walSlotUsable wal.anchorGen 0 wal.slotEven with
        | none => exact walSlotUsable_none_mono ha hEven
        | some x =>
          obtain ⟨g', pp⟩ := x
          rw [hEven] at hE
          exact walSlotUsable_anchor_gt hEven (by have := hE.1; omega)
      have hOlder : WalOlderOk rel inv g p (walSlotUsable g 0 wal.slotEven) := by
        rw [hE']; exact True.intro
      exact Or.inr ⟨hO', hOlder⟩
  have hInv' : TwoSlotWalInv rel inv { wal with anchorGen := g } :=
    walInv_of_shape hShape' hp hStage
  obtain ⟨_, _, hA, hFloor'⟩ := walShape_view hShape'
  have hC' : checkpointedWalPayload { wal with anchorGen := g } = p := by
    rcases hFloor' with hF | ⟨pp, _, hLag, _, _⟩
    · simp [checkpointedWalPayload, hF]
    · exfalso
      have hLag' : g + 1 ≤ g := hLag
      omega
  rw [hC']
  exact ⟨hInv', hFloorRel⟩

/-- Losing the active slot: the ledger either FAILS CLOSED (no slot authenticates at or above the
    external checkpoint) or rolls back to exactly the rollback floor, never below it. -/
private theorem tearActiveWalSlot_inv {S : Type} {rel : S → S → Prop} {inv : S → Prop}
    {wal : TwoSlotWal S} (hRefl : ∀ x, rel x x) (hWal : TwoSlotWalInv rel inv wal) :
    walRecoverable (tearActiveWalSlot wal) = false ∨
    (TwoSlotWalInv rel inv (tearActiveWalSlot wal) ∧
     rel (checkpointedWalPayload wal) (checkpointedWalPayload (tearActiveWalSlot wal))) := by
  obtain ⟨g, p, hp, hShape⟩ := hWal.shape
  obtain ⟨hRec, _⟩ := walShape_view hShape
  have hGen : activeWalGen wal = g := by simp [activeWalGen, hRec]
  rcases hShape with ⟨hE, hO⟩ | ⟨hO, hE⟩
  · obtain ⟨_, _, hpar⟩ := walSlotUsable_inv hE
    have hT : tearActiveWalSlot wal =
        { wal with slotEven := invalidateWalSlot wal.slotEven, volatileStage := none } := by
      simp [tearActiveWalSlot, hGen, hpar]
    rw [hT]
    have hTorn : walSlotUsable wal.anchorGen 0 (invalidateWalSlot wal.slotEven) = none :=
      walSlotUsable_invalidate _ _ _
    cases hOdd : walSlotUsable wal.anchorGen 1 wal.slotOdd with
    | none =>
      left
      simp [walRecoverable, hTorn, hOdd]
    | some x =>
      right
      obtain ⟨g', pp⟩ := x
      rw [hOdd] at hO
      obtain ⟨hg, _, hpp⟩ := hO
      have hNle : ¬ g ≤ g' := by omega
      have hOlder : WalOlderOk rel inv g' pp
          (walSlotUsable wal.anchorGen 0 (invalidateWalSlot wal.slotEven)) := by
        rw [hTorn]; exact True.intro
      have hShape' : WalShape rel inv
          { wal with slotEven := invalidateWalSlot wal.slotEven, volatileStage := none } g' pp :=
        Or.inr ⟨hOdd, hOlder⟩
      have hC : checkpointedWalPayload wal = pp := by
        simp [checkpointedWalPayload, rollbackFloorWal, hE, hOdd, hNle]
      have hC' : checkpointedWalPayload
          { wal with slotEven := invalidateWalSlot wal.slotEven, volatileStage := none } = pp := by
        simp [checkpointedWalPayload, rollbackFloorWal, hTorn, hOdd]
      rw [hC, hC']
      exact ⟨walInv_of_shape hShape' hpp rfl, hRefl pp⟩
  · obtain ⟨_, _, hpar⟩ := walSlotUsable_inv hO
    have hNe : ¬ g % 2 = 0 := by omega
    have hT : tearActiveWalSlot wal =
        { wal with slotOdd := invalidateWalSlot wal.slotOdd, volatileStage := none } := by
      simp [tearActiveWalSlot, hGen, hNe]
    rw [hT]
    have hTorn : walSlotUsable wal.anchorGen 1 (invalidateWalSlot wal.slotOdd) = none :=
      walSlotUsable_invalidate _ _ _
    cases hEven : walSlotUsable wal.anchorGen 0 wal.slotEven with
    | none =>
      left
      simp [walRecoverable, hTorn, hEven]
    | some x =>
      right
      obtain ⟨g', pp⟩ := x
      rw [hEven] at hE
      obtain ⟨hg, _, hpp⟩ := hE
      have hLe : g' ≤ g := by omega
      have hOlder : WalOlderOk rel inv g' pp
          (walSlotUsable wal.anchorGen 1 (invalidateWalSlot wal.slotOdd)) := by
        rw [hTorn]; exact True.intro
      have hShape' : WalShape rel inv
          { wal with slotOdd := invalidateWalSlot wal.slotOdd, volatileStage := none } g' pp :=
        Or.inl ⟨hEven, hOlder⟩
      have hC : checkpointedWalPayload wal = pp := by
        simp [checkpointedWalPayload, rollbackFloorWal, hO, hEven, hLe]
      have hC' : checkpointedWalPayload
          { wal with slotOdd := invalidateWalSlot wal.slotOdd, volatileStage := none } = pp := by
        simp [checkpointedWalPayload, rollbackFloorWal, hTorn, hEven]
      rw [hC, hC']
      exact ⟨walInv_of_shape hShape' hpp rfl, hRefl pp⟩

private theorem damageIdleWalSlot_stage_none {S : Type} (wal : TwoSlotWal S) :
    (damageIdleWalSlot wal).volatileStage = none := by
  unfold damageIdleWalSlot
  split <;> rfl

/-- Damage to the idle slot never fails the ledger: the active snapshot stays the recovered one
    and becomes the rollback floor. -/
private theorem damageIdleWalSlot_inv {S : Type} {rel : S → S → Prop} {inv : S → Prop}
    {wal : TwoSlotWal S} (hRefl : ∀ x, rel x x) (hWal : TwoSlotWalInv rel inv wal) :
    TwoSlotWalInv rel inv (damageIdleWalSlot wal) ∧
    rel (checkpointedWalPayload wal) (checkpointedWalPayload (damageIdleWalSlot wal)) := by
  obtain ⟨g, p, hp, hShape⟩ := hWal.shape
  obtain ⟨hRec, _, _, hFloor⟩ := walShape_view hShape
  have hGen : activeWalGen wal = g := by simp [activeWalGen, hRec]
  have hFloorRel : rel (checkpointedWalPayload wal) p := by
    rcases hFloor with hF | ⟨pp, hF, _, hR, _⟩
    · have hC : checkpointedWalPayload wal = p := by simp [checkpointedWalPayload, hF]
      rw [hC]; exact hRefl p
    · have hC : checkpointedWalPayload wal = pp := by simp [checkpointedWalPayload, hF]
      rw [hC]; exact hR
  rcases hShape with ⟨hE, _⟩ | ⟨hO, _⟩
  · obtain ⟨_, _, hpar⟩ := walSlotUsable_inv hE
    have hT : damageIdleWalSlot wal =
        { wal with slotOdd := invalidateWalSlot wal.slotOdd, volatileStage := none } := by
      simp [damageIdleWalSlot, hGen, hpar]
    rw [hT]
    have hTorn : walSlotUsable wal.anchorGen 1 (invalidateWalSlot wal.slotOdd) = none :=
      walSlotUsable_invalidate _ _ _
    have hOlder : WalOlderOk rel inv g p
        (walSlotUsable wal.anchorGen 1 (invalidateWalSlot wal.slotOdd)) := by
      rw [hTorn]; exact True.intro
    have hShape' : WalShape rel inv
        { wal with slotOdd := invalidateWalSlot wal.slotOdd, volatileStage := none } g p :=
      Or.inl ⟨hE, hOlder⟩
    have hC' : checkpointedWalPayload
        { wal with slotOdd := invalidateWalSlot wal.slotOdd, volatileStage := none } = p := by
      simp [checkpointedWalPayload, rollbackFloorWal, hE, hTorn]
    rw [hC']
    exact ⟨walInv_of_shape hShape' hp rfl, hFloorRel⟩
  · obtain ⟨_, _, hpar⟩ := walSlotUsable_inv hO
    have hNe : ¬ g % 2 = 0 := by omega
    have hT : damageIdleWalSlot wal =
        { wal with slotEven := invalidateWalSlot wal.slotEven, volatileStage := none } := by
      simp [damageIdleWalSlot, hGen, hNe]
    rw [hT]
    have hTorn : walSlotUsable wal.anchorGen 0 (invalidateWalSlot wal.slotEven) = none :=
      walSlotUsable_invalidate _ _ _
    have hOlder : WalOlderOk rel inv g p
        (walSlotUsable wal.anchorGen 0 (invalidateWalSlot wal.slotEven)) := by
      rw [hTorn]; exact True.intro
    have hShape' : WalShape rel inv
        { wal with slotEven := invalidateWalSlot wal.slotEven, volatileStage := none } g p :=
      Or.inr ⟨hO, hOlder⟩
    have hC' : checkpointedWalPayload
        { wal with slotEven := invalidateWalSlot wal.slotEven, volatileStage := none } = p := by
      simp [checkpointedWalPayload, rollbackFloorWal, hO, hTorn]
    rw [hC']
    exact ⟨walInv_of_shape hShape' hp rfl, hFloorRel⟩

private theorem crashRecoverWal_stage_none {S : Type} (mode : WalCrashBehavior)
    (wal : TwoSlotWal S) : (crashRecoverWal mode wal).volatileStage = none := by
  cases mode with
  | dropVolatile => rfl
  | tornInactiveWrite =>
    unfold crashRecoverWal
    cases hS : wal.volatileStage with
    | none => exact hS
    | some gp => exact writeDurableWalSlot_stage_none _ _ _ _
  | flushedBeforePowerLoss =>
    unfold crashRecoverWal
    cases hS : wal.volatileStage with
    | none => exact hS
    | some gp => exact writeDurableWalSlot_stage_none _ _ _ _
  | tornActiveSlot => exact tearActiveWalSlot_stage_none wal
  | idleSlotDamaged => exact damageIdleWalSlot_stage_none wal

/-- Single-ledger crash recovery under EVERY crash mode: the ledger fails closed, or it stays
    healthy and its rollback floor only moves forward along `rel`. -/
private theorem crashRecoverWal_inv {S : Type} {rel : S → S → Prop} {inv : S → Prop}
    {wal : TwoSlotWal S} (hRefl : ∀ x, rel x x) (hWal : TwoSlotWalInv rel inv wal)
    (mode : WalCrashBehavior) :
    walRecoverable (crashRecoverWal mode wal) = false ∨
    (TwoSlotWalInv rel inv (crashRecoverWal mode wal) ∧
     rel (checkpointedWalPayload wal) (checkpointedWalPayload (crashRecoverWal mode wal))) := by
  cases mode with
  | dropVolatile =>
    exact Or.inr ⟨⟨hWal.shape, True.intro⟩, hRefl _⟩
  | tornInactiveWrite =>
    unfold crashRecoverWal
    cases hStage : wal.volatileStage with
    | none => exact Or.inr ⟨hWal, hRefl _⟩
    | some gp =>
      rcases gp with ⟨gNext, pNext⟩
      have hSt := hWal.stage_ok
      rw [hStage] at hSt
      rcases hSt with ⟨rfl, _, _⟩
      exact Or.inr (writeDurableWalSlot_inv hRefl hWal pNext false (fun h => by cases h))
  | flushedBeforePowerLoss =>
    unfold crashRecoverWal
    cases hStage : wal.volatileStage with
    | none => exact Or.inr ⟨hWal, hRefl _⟩
    | some gp =>
      rcases gp with ⟨gNext, pNext⟩
      have hSt := hWal.stage_ok
      rw [hStage] at hSt
      rcases hSt with ⟨rfl, hRel, hNextInv⟩
      exact Or.inr (writeDurableWalSlot_inv hRefl hWal pNext true (fun _ => ⟨hRel, hNextInv⟩))
  | tornActiveSlot => exact tearActiveWalSlot_inv hRefl hWal
  | idleSlotDamaged => exact Or.inr (damageIdleWalSlot_inv hRefl hWal)

private theorem walUsable_none_of_dead {S : Type} {wal : TwoSlotWal S}
    (h : walRecoverable wal = false) :
    walSlotUsable wal.anchorGen 0 wal.slotEven = none ∧
    walSlotUsable wal.anchorGen 1 wal.slotOdd = none := by
  refine ⟨?_, ?_⟩
  · cases hU : walSlotUsable wal.anchorGen 0 wal.slotEven with
    | none => rfl
    | some x => rw [walRecoverable, hU] at h; simp at h
  · cases hU : walSlotUsable wal.anchorGen 1 wal.slotOdd with
    | none => rfl
    | some x => rw [walRecoverable, hU] at h; simp at h

/-- A ledger that failed closed with nothing staged stays failed closed under every crash mode:
    no crash can resurrect a snapshot. -/
private theorem crashRecoverWal_dead_stays_dead {S : Type} (mode : WalCrashBehavior)
    (wal : TwoSlotWal S) (hDead : walRecoverable wal = false) (hStage : wal.volatileStage = none) :
    walRecoverable (crashRecoverWal mode wal) = false := by
  obtain ⟨hE, hO⟩ := walUsable_none_of_dead hDead
  cases mode with
  | dropVolatile => exact hDead
  | tornInactiveWrite =>
    have hEq : crashRecoverWal .tornInactiveWrite wal = wal := by simp [crashRecoverWal, hStage]
    rw [hEq]; exact hDead
  | flushedBeforePowerLoss =>
    have hEq : crashRecoverWal .flushedBeforePowerLoss wal = wal := by simp [crashRecoverWal, hStage]
    rw [hEq]; exact hDead
  | tornActiveSlot =>
    show walRecoverable (tearActiveWalSlot wal) = false
    unfold tearActiveWalSlot
    split
    · simp [walRecoverable, walSlotUsable_invalidate, hO]
    · simp [walRecoverable, walSlotUsable_invalidate, hE]
  | idleSlotDamaged =>
    show walRecoverable (damageIdleWalSlot wal) = false
    unfold damageIdleWalSlot
    split
    · simp [walRecoverable, walSlotUsable_invalidate, hE]
    · simp [walRecoverable, walSlotUsable_invalidate, hO]

/-- **Whole-device rollback below the external checkpoint fails closed**: if both slot files are
    replaced by ANY contents whose generations lie below `anchorGen` (a restored disk image,
    whatever it holds and however it authenticates), no slot is usable and the ledger does not
    open. The anchor is held outside the rollback domain, so it does not move. -/
theorem whole_device_rollback_below_anchor_fails_closed {S : Type} (wal : TwoSlotWal S)
    (oldEven oldOdd : Option (WalSlot S))
    (hEven : ∀ s, oldEven = some s → s.generation < wal.anchorGen)
    (hOdd : ∀ s, oldOdd = some s → s.generation < wal.anchorGen) :
    recoverTwoSlotWal
      { wal with slotEven := oldEven, slotOdd := oldOdd, volatileStage := none } = none ∧
    walRecoverable
      { wal with slotEven := oldEven, slotOdd := oldOdd, volatileStage := none } = false := by
  have hU : ∀ (par : Nat) (o : Option (WalSlot S)),
      (∀ s, o = some s → s.generation < wal.anchorGen) →
      walSlotUsable wal.anchorGen par o = none := by
    intro par o h
    cases o with
    | none => rfl
    | some s =>
      have hLt := h s rfl
      have hNle : ¬ wal.anchorGen ≤ s.generation := by omega
      simp [walSlotUsable, hNle]
  have h0 := hU 0 oldEven hEven
  have h1 := hU 1 oldOdd hOdd
  refine ⟨?_, ?_⟩
  · simp [recoverTwoSlotWal, h0, h1]
  · simp [walRecoverable, h0, h1]

/-! ### Weld Onto `PosixCrashWal`: the Two Slot Files on the Page-Cache / Drive-Cache / NAND Machine

The crash behaviors above are not postulated: they are the images, under the abstraction below,
of `CrashStep` (kernel panic, power loss with per-sector tears of in-flight writes) and of
`MediaDamageInode` (bit-rot of settled blocks) on the two slot inodes of `PosixFsState`. -/

/-- Where one ledger lives on the device. `slotView bytes` is `read_slot` of `durable_ledger.rs`:
    MAC check, parse and generation-parity check, returning the authenticated
    `(generation, payload)` or nothing. -/
structure PosixTwoSlotLayout (S : Type) where
  evenIno : InodeId
  oddIno : InodeId
  slotView : List UInt8 → Option (Nat × S)

/-- The abstract slot a recovery reads out of on-media bytes. -/
def slotBytesView {S : Type} (view : List UInt8 → Option (Nat × S)) :
    Option (List UInt8) → Option (WalSlot S)
  | none => none
  | some bs =>
    match view bs with
    | none => none
    | some (g, p) => some { generation := g, payload := p, macValid := true }

/-- Two slots that no recovery can tell apart (an unauthenticated slot equals a missing one). -/
def SlotEquiv {S : Type} (s t : Option (WalSlot S)) : Prop :=
  ∀ a par, walSlotUsable a par s = walSlotUsable a par t

/-- The abstract ledger `wal` describes the NAND contents of the two slot inodes of `fs`. -/
structure PosixRefinesWal {S : Type} (L : PosixTwoSlotLayout S) (fs : PosixFsState)
    (wal : TwoSlotWal S) : Prop where
  even_ok : SlotEquiv wal.slotEven
    (slotBytesView L.slotView (assocLookup fs.nand.fileBlocks L.evenIno))
  odd_ok : SlotEquiv wal.slotOdd
    (slotBytesView L.slotView (assocLookup fs.nand.fileBlocks L.oddIno))

/-- Recovery of the abstract ledger is recovery from the device bytes. -/
theorem posixRefines_recover {S : Type} {L : PosixTwoSlotLayout S} {fs : PosixFsState}
    {wal : TwoSlotWal S} (hRef : PosixRefinesWal L fs wal) :
    recoverTwoSlotWal wal =
      recoverTwoSlotWal
        { wal with
          slotEven := slotBytesView L.slotView (assocLookup fs.nand.fileBlocks L.evenIno)
          slotOdd := slotBytesView L.slotView (assocLookup fs.nand.fileBlocks L.oddIno) } := by
  simp only [recoverTwoSlotWal, hRef.even_ok _ _, hRef.odd_ok _ _]

private theorem slotEquiv_invalid_none {S : Type} (g : Nat) (p : S) :
    SlotEquiv (some { generation := g, payload := p, macValid := false })
      (none : Option (WalSlot S)) := by
  intro a par
  simp [walSlotUsable]

/-- A slot inode ends up holding `bytes` whose view is the slot `(g, p, macOk)`; the other slot
    inode is untouched. Then the device refines the abstract slot write. -/
theorem posixRefines_slot_write {S : Type} {L : PosixTwoSlotLayout S} {fs crashed : PosixFsState}
    {wal : TwoSlotWal S} (hRef : PosixRefinesWal L fs wal)
    (g : Nat) (p : S) (macOk : Bool) (bytes : List UInt8)
    (hSlot : SlotEquiv (some { generation := g, payload := p, macValid := macOk })
      (slotBytesView L.slotView (some bytes)))
    (hEven : assocLookup crashed.nand.fileBlocks L.evenIno =
      if g % 2 = 0 then some bytes else assocLookup fs.nand.fileBlocks L.evenIno)
    (hOdd : assocLookup crashed.nand.fileBlocks L.oddIno =
      if g % 2 = 0 then assocLookup fs.nand.fileBlocks L.oddIno else some bytes) :
    PosixRefinesWal L crashed (writeDurableWalSlot wal g p macOk) := by
  by_cases hPar : g % 2 = 0
  · simp only [hPar, ↓reduceIte] at hEven hOdd
    simp only [writeDurableWalSlot, hPar, ↓reduceIte]
    exact ⟨by rw [hEven]; exact hSlot, by rw [hOdd]; exact hRef.odd_ok⟩
  · simp only [hPar, ↓reduceIte] at hEven hOdd
    simp only [writeDurableWalSlot, hPar, ↓reduceIte]
    exact ⟨by rw [hEven]; exact hRef.even_ok, by rw [hOdd]; exact hSlot⟩

/-- **A crash during a slot write is one of the abstract crash behaviors
    (`posix_crash_during_slot_write_refines`)**: the ledger has staged `(g, p)`; on the device the
    slot inode of parity `g` holds settled bytes `old` and has an in-flight write of `new`
    (in the page cache or the drive cache) with `slotView new = (g, p)`; the other slot inode
    has nothing pending. After ANY `CrashStep` (kernel panic, or power loss under any sector tear
    mask), the device refines `crashRecoverWal mode` for `mode` one of `dropVolatile`,
    `tornInactiveWrite`, `flushedBeforePowerLoss`. The only escape is the stated physical event:
    the torn sectors form bytes different from both `old` and `new` that nevertheless pass the
    slot MAC and parity check. -/
theorem posix_crash_during_slot_write_refines {S : Type} (L : PosixTwoSlotLayout S)
    {fs crashed : PosixFsState} {wal : TwoSlotWal S} (hRef : PosixRefinesWal L fs wal)
    {g : Nat} {p : S} (hStage : wal.volatileStage = some (g, p))
    {target other : InodeId} {old new : List UInt8}
    (hLayout : (g % 2 = 0 ∧ target = L.evenIno ∧ other = L.oddIno) ∨
      (¬ g % 2 = 0 ∧ target = L.oddIno ∧ other = L.evenIno))
    (hOld : assocLookup fs.nand.fileBlocks target = some old)
    (hNewView : L.slotView new = some (g, p))
    (hOtherPage : assocLookup fs.kernel.pageCache.dirtyFiles other = none)
    (hOtherDrive : assocLookup fs.driveCache.cachedFiles other = none)
    (hCrash : CrashStep fs crashed) :
    (∃ mode, (mode = WalCrashBehavior.dropVolatile ∨ mode = WalCrashBehavior.tornInactiveWrite ∨
        mode = WalCrashBehavior.flushedBeforePowerLoss) ∧
      PosixRefinesWal L crashed (crashRecoverWal mode wal)) ∨
    (∃ torn, torn ≠ old ∧ torn ≠ new ∧
      assocLookup crashed.nand.fileBlocks target = some torn ∧
      (L.slotView torn).isSome = true) := by
  have hOtherSame := (syncedInode_immune_to_crashStep hOtherPage hOtherDrive hCrash).1
  have hClass : ∀ bytes, assocLookup crashed.nand.fileBlocks target = some bytes →
      (∃ mode, (mode = WalCrashBehavior.dropVolatile ∨
          mode = WalCrashBehavior.tornInactiveWrite ∨
          mode = WalCrashBehavior.flushedBeforePowerLoss) ∧
        PosixRefinesWal L crashed (crashRecoverWal mode wal)) ∨
      (∃ torn, torn ≠ old ∧ torn ≠ new ∧
        assocLookup crashed.nand.fileBlocks target = some torn ∧
        (L.slotView torn).isSome = true) := by
    intro bytes hT
    have hEvenOdd :
        (assocLookup crashed.nand.fileBlocks L.evenIno =
          if g % 2 = 0 then some bytes else assocLookup fs.nand.fileBlocks L.evenIno) ∧
        (assocLookup crashed.nand.fileBlocks L.oddIno =
          if g % 2 = 0 then assocLookup fs.nand.fileBlocks L.oddIno else some bytes) := by
      rcases hLayout with ⟨hPar, rfl, rfl⟩ | ⟨hPar, rfl, rfl⟩
      · simp only [hPar, ↓reduceIte]
        exact ⟨hT, hOtherSame⟩
      · simp only [hPar, ↓reduceIte]
        exact ⟨hOtherSame, hT⟩
    by_cases hNew : bytes = new
    · left
      refine ⟨.flushedBeforePowerLoss, Or.inr (Or.inr rfl), ?_⟩
      have hSlot : SlotEquiv (some { generation := g, payload := p, macValid := true })
          (slotBytesView L.slotView (some bytes)) := by
        intro a par
        simp only [slotBytesView, hNew, hNewView]
      simp only [crashRecoverWal, hStage]
      exact posixRefines_slot_write hRef g p true bytes hSlot hEvenOdd.1 hEvenOdd.2
    · cases hV : L.slotView bytes with
      | none =>
        left
        refine ⟨.tornInactiveWrite, Or.inr (Or.inl rfl), ?_⟩
        have hSlot : SlotEquiv (some { generation := g, payload := p, macValid := false })
            (slotBytesView L.slotView (some bytes)) := by
          intro a par
          simp only [slotBytesView, hV]
          exact slotEquiv_invalid_none g p a par
        simp only [crashRecoverWal, hStage]
        exact posixRefines_slot_write hRef g p false bytes hSlot hEvenOdd.1 hEvenOdd.2
      | some v =>
        by_cases hOldEq : bytes = old
        · left
          refine ⟨.dropVolatile, Or.inl rfl, ?_⟩
          show PosixRefinesWal L crashed { wal with volatileStage := none }
          rcases hLayout with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩
          · exact ⟨by rw [hT, hOldEq, ← hOld]; exact hRef.even_ok,
              by rw [hOtherSame]; exact hRef.odd_ok⟩
          · exact ⟨by rw [hOtherSame]; exact hRef.even_ok,
              by rw [hT, hOldEq, ← hOld]; exact hRef.odd_ok⟩
        · right
          exact ⟨bytes, hOldEq, hNew, hT, by rw [hV]; rfl⟩
  rcases crashStep_inode_outcome hOld hCrash with h1 | ⟨dc, _, h2⟩ | ⟨pending, mask, _, h3⟩
  · exact hClass old h1
  · exact hClass dc h2
  · exact hClass _ h3

/-- **Bit-rot of a settled slot is `idleSlotDamaged` or `tornActiveSlot`
    (`posix_media_damage_refines`)**: replacing the NAND bytes of the idle (non-active) slot
    inode by bytes that do not authenticate refines `idleSlotDamaged`, which never fails the
    ledger; doing so to the active slot inode refines `tornActiveSlot`. -/
theorem posix_media_damage_refines {S : Type} (L : PosixTwoSlotLayout S) {fs : PosixFsState}
    {wal : TwoSlotWal S} (hRef : PosixRefinesWal L fs wal) (hDistinct : L.evenIno ≠ L.oddIno)
    (garbage : List UInt8) (hView : L.slotView garbage = none) :
    PosixRefinesWal L
      (MediaDamageInode fs (if activeWalGen wal % 2 = 0 then L.oddIno else L.evenIno) garbage)
      (crashRecoverWal .idleSlotDamaged wal) ∧
    PosixRefinesWal L
      (MediaDamageInode fs (if activeWalGen wal % 2 = 0 then L.evenIno else L.oddIno) garbage)
      (crashRecoverWal .tornActiveSlot wal) := by
  have hInvalid : ∀ s : Option (WalSlot S),
      SlotEquiv (invalidateWalSlot s) (slotBytesView L.slotView (some garbage)) := by
    intro s a par
    rw [walSlotUsable_invalidate]
    simp only [slotBytesView, hView]
    rfl
  have hNe' : L.oddIno ≠ L.evenIno := fun h => hDistinct h.symm
  by_cases hPar : activeWalGen wal % 2 = 0
  · simp only [crashRecoverWal, damageIdleWalSlot, tearActiveWalSlot, hPar, ↓reduceIte]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simp only [mediaDamageInode_lookup, hDistinct, ↓reduceIte]; exact hRef.even_ok
    · simp only [mediaDamageInode_lookup, ↓reduceIte]; exact hInvalid _
    · simp only [mediaDamageInode_lookup, ↓reduceIte]; exact hInvalid _
    · simp only [mediaDamageInode_lookup, hNe', ↓reduceIte]; exact hRef.odd_ok
  · simp only [crashRecoverWal, damageIdleWalSlot, tearActiveWalSlot, hPar, ↓reduceIte]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simp only [mediaDamageInode_lookup, ↓reduceIte]; exact hInvalid _
    · simp only [mediaDamageInode_lookup, hNe', ↓reduceIte]; exact hRef.odd_ok
    · simp only [mediaDamageInode_lookup, hDistinct, ↓reduceIte]; exact hRef.even_ok
    · simp only [mediaDamageInode_lookup, ↓reduceIte]; exact hInvalid _

/-- **Whole-device snapshot restore below the anchor (`posix_device_restore_below_anchor_fails_closed`)**:
    replace the ENTIRE filesystem state by an image whose two slot files authenticate only to
    generations below the externally held `anchorGen`. The ledger read from that image does not
    open. (A restore to a generation at or above the anchor is the lagging-checkpoint case and
    is not excluded by the anchor; see the limits in the summary.) -/
theorem posix_device_restore_below_anchor_fails_closed {S : Type} (L : PosixTwoSlotLayout S)
    (image : PosixFsState) (wal : TwoSlotWal S)
    (hEven : ∀ bs g p, assocLookup image.nand.fileBlocks L.evenIno = some bs →
      L.slotView bs = some (g, p) → g < wal.anchorGen)
    (hOdd : ∀ bs g p, assocLookup image.nand.fileBlocks L.oddIno = some bs →
      L.slotView bs = some (g, p) → g < wal.anchorGen) :
    PosixRefinesWal L image
      { wal with
        slotEven := slotBytesView L.slotView (assocLookup image.nand.fileBlocks L.evenIno)
        slotOdd := slotBytesView L.slotView (assocLookup image.nand.fileBlocks L.oddIno)
        volatileStage := none } ∧
    walRecoverable
      { wal with
        slotEven := slotBytesView L.slotView (assocLookup image.nand.fileBlocks L.evenIno)
        slotOdd := slotBytesView L.slotView (assocLookup image.nand.fileBlocks L.oddIno)
        volatileStage := none } = false := by
  have hGen : ∀ (ino : InodeId),
      (∀ bs g p, assocLookup image.nand.fileBlocks ino = some bs →
        L.slotView bs = some (g, p) → g < wal.anchorGen) →
      ∀ s, slotBytesView L.slotView (assocLookup image.nand.fileBlocks ino) = some s →
        s.generation < wal.anchorGen := by
    intro ino h s hs
    cases hLk : assocLookup image.nand.fileBlocks ino with
    | none => rw [hLk] at hs; cases hs
    | some bs =>
      rw [hLk] at hs
      cases hV : L.slotView bs with
      | none => simp only [slotBytesView, hV] at hs; cases hs
      | some gp =>
        obtain ⟨g, p⟩ := gp
        simp only [slotBytesView, hV, Option.some.injEq] at hs
        rw [← hs]
        exact h bs g p hLk hV
  exact ⟨⟨fun _ _ => rfl, fun _ _ => rfl⟩,
    (whole_device_rollback_below_anchor_fails_closed wal _ _ (hGen _ hEven) (hGen _ hOdd)).2⟩

/-! ### Durable Payloads of the Five Host Ledgers -/

/-- Ledger (1): Sticky quarantine/poison latch (`poison_journal.rs`). -/
inductive PoisonStatus where
  | clean
  | poisoned (reasonCode : UInt64)
  deriving Repr, DecidableEq

/-- Durable payload of Ledger (1): `PoisonLatch`. -/
structure PoisonLatch where
  status : PoisonStatus
  faultCount : Nat
  deriving Repr, DecidableEq

/-- Durable spend record inside Ledger (2): `PolicyWindowLedger`. -/
structure PolicySpendEntry where
  ceremonyId : Nat
  windowId : Nat
  amount : Nat
  intentDigest : Digest256
  deriving Repr, DecidableEq

/-- Durable payload of Ledger (2): `PolicyWindowLedger` (`qsag-policy`). -/
structure PolicyWindowLedger where
  currentWindow : Nat
  policyCap : Nat
  committedSpends : List PolicySpendEntry
  deriving Repr, DecidableEq

/-- Durable preprocessing burn record inside Ledger (3): `PreprocCursorLedger`. -/
structure PreprocBurnEntry where
  ceremonyId : Nat
  batchIdx : Nat
  deriving Repr, DecidableEq

/-- Durable payload of Ledger (3): `PreprocCursorLedger` (`preprocessing.rs`). -/
structure PreprocCursorLedger where
  nextBatchCursor : Nat
  burnedBatches : List PreprocBurnEntry
  deriving Repr, DecidableEq

/-- Durable leaf/FTS antichain reservation inside Ledger (4): `LeafOrFtsBurnLedger`. -/
structure LeafBurnEntry where
  ceremonyId : Nat
  epochOrIndex : Nat
  msgDigest : Digest256
  deriving Repr, DecidableEq

/-- Durable payload of Ledger (4): `LeafOrFtsBurnLedger` (`belt_latch.rs` / `baggy.rs`). -/
structure LeafOrFtsBurnLedger where
  nextEpochCursor : Nat
  reservedLeaves : List LeafBurnEntry
  deriving Repr, DecidableEq

/-- Emitted outbound signing share recorded on Ledger (5): `OutboundNetworkWire`. -/
structure WireEmission where
  ceremonyId : Nat
  windowId : Nat
  amount : Nat
  batchIdx : Nat
  epochOrIndex : Nat
  msgDigest : Digest256
  party : Nat
  share : Digest256
  deriving Repr, DecidableEq

/-- Ledger (5): Append-only external `OutboundNetworkWire`. -/
abbrev OutboundNetworkWire := List WireEmission

/-- Causal burn-before-release receipt witnessing durable persisted commits across all four
    local ledgers in strict causal order `(1) -> (2) -> (3) -> (4)`. -/
structure CeremonyReceipt where
  ceremonyId : Nat
  poisonCleanGen : Nat
  policyCommitGen : Nat
  preprocBurnGen : Nat
  leafReserveGen : Nat
  windowId : Nat
  amount : Nat
  intentDigest : Digest256
  batchIdx : Nat
  epochOrIndex : Nat
  msgDigest : Digest256
  deriving Repr, DecidableEq

/-- Per-ceremony volatile RAM causal progress wiped to `[]` on every `PowerLossCrash`. -/
inductive CeremonyVolatilePhase where
  | cleanObserved (poisonGen : Nat)
  | policyStaged (poisonGen : Nat) (windowId amount : Nat) (intentDigest : Digest256)
  | policyCommitted (poisonGen policyGen : Nat) (windowId amount : Nat) (intentDigest : Digest256)
  | preprocStaged (poisonGen policyGen : Nat) (windowId amount : Nat) (intentDigest : Digest256) (batchIdx : Nat)
  | preprocBurned (poisonGen policyGen preprocGen : Nat) (windowId amount : Nat) (intentDigest : Digest256) (batchIdx : Nat)
  | leafStaged (poisonGen policyGen preprocGen : Nat) (windowId amount : Nat) (intentDigest : Digest256) (batchIdx epochOrIndex : Nat) (msgDigest : Digest256)
  | receiptIssued (ceremonyReceipt : CeremonyReceipt)
  deriving Repr, DecidableEq

/-- Composite multi-ledger host state with four independent two-slot WALs, volatile RAM causal
    progress table, and the append-only external `OutboundNetworkWire`. -/
structure MultiLedgerHostState where
  poisonLatch : TwoSlotWal PoisonLatch
  policyWindowLedger : TwoSlotWal PolicyWindowLedger
  preprocCursorLedger : TwoSlotWal PreprocCursorLedger
  leafOrFtsBurnLedger : TwoSlotWal LeafOrFtsBurnLedger
  volatileCeremonies : List (Nat × CeremonyVolatilePhase)
  outboundWire : OutboundNetworkWire
  deriving Repr, DecidableEq

/-- Total durably committed spend inside window `win` on `PolicyWindowLedger`. -/
def windowCommittedSpend (win : Nat) : List PolicySpendEntry → Nat
  | [] => 0
  | e :: rest => (if e.windowId == win then e.amount else 0) + windowCommittedSpend win rest

private def dedupWireByCidAux : List Nat → OutboundNetworkWire → OutboundNetworkWire
  | _, [] => []
  | seen, e :: rest =>
    if e.ceremonyId ∈ seen then
      dedupWireByCidAux seen rest
    else
      e :: dedupWireByCidAux (e.ceremonyId :: seen) rest

/-- Deduplicated ceremony emissions on `OutboundNetworkWire` inside policy window `win`. -/
def releasedCeremoniesInWindow (win : Nat) (wire : OutboundNetworkWire) : OutboundNetworkWire :=
  dedupWireByCidAux [] (wire.filter (fun e => e.windowId == win))

/-- Total amount of all released ceremonies on `OutboundNetworkWire` inside policy window `win`. -/
@[expose] def wireWindowSpend (win : Nat) (wire : OutboundNetworkWire) : Nat :=
  (releasedCeremoniesInWindow win wire).foldr (fun e acc => e.amount + acc) 0

/-- Canonical Genesis host state for a given per-window `policyCap`. -/
def initMultiLedgerHostState (policyCap : Nat) : MultiLedgerHostState where
  poisonLatch := initTwoSlotWal { status := .clean, faultCount := 0 }
  policyWindowLedger := initTwoSlotWal { currentWindow := 0, policyCap := policyCap, committedSpends := [] }
  preprocCursorLedger := initTwoSlotWal { nextBatchCursor := 0, burnedBatches := [] }
  leafOrFtsBurnLedger := initTwoSlotWal { nextEpochCursor := 0, reservedLeaves := [] }
  volatileCeremonies := []
  outboundWire := []

private def lookupVolatilePhase (cid : Nat) : List (Nat × CeremonyVolatilePhase) → Option CeremonyVolatilePhase
  | [] => none
  | (k, ph) :: rest => if k == cid then some ph else lookupVolatilePhase cid rest

private def upsertVolatilePhase (cid : Nat) (ph : CeremonyVolatilePhase) :
    List (Nat × CeremonyVolatilePhase) → List (Nat × CeremonyVolatilePhase)
  | [] => [(cid, ph)]
  | (k, old) :: rest =>
    if k == cid then (cid, ph) :: rest else (k, old) :: upsertVolatilePhase cid ph rest

/-- Check whether durable ledgers currently validate a `CeremonyReceipt` prior to wire release. -/
def ceremonyReceiptDurableValid (host : MultiLedgerHostState) (cid : Nat) (r : CeremonyReceipt) : Bool :=
  (r.ceremonyId == cid) &&
  ((activeWalPayload host.poisonLatch).status == .clean) &&
  host.poisonLatch.volatileStage.isNone &&
  decide (PolicySpendEntry.mk cid r.windowId r.amount r.intentDigest ∈
    (activeWalPayload host.policyWindowLedger).committedSpends) &&
  decide (PreprocBurnEntry.mk cid r.batchIdx ∈
    (activeWalPayload host.preprocCursorLedger).burnedBatches) &&
  decide (LeafBurnEntry.mk cid r.epochOrIndex r.msgDigest ∈
    (activeWalPayload host.leafOrFtsBurnLedger).reservedLeaves)

/-- The external checkpoints of all four ledgers have caught up with their active
    generations, so no crash mode can roll any of them back below what is about to be released. -/
def ledgersCheckpointSaved (host : MultiLedgerHostState) : Bool :=
  walCheckpointSaved host.poisonLatch &&
  walCheckpointSaved host.policyWindowLedger &&
  walCheckpointSaved host.preprocCursorLedger &&
  walCheckpointSaved host.leafOrFtsBurnLedger

/-- All four local ledgers open. A host with any unrecoverable ledger refuses every transition
    except a further crash (`Ledger::open` returning `Err` aborts the process before signing). -/
def hostOperational (host : MultiLedgerHostState) : Bool :=
  walRecoverable host.poisonLatch &&
  walRecoverable host.policyWindowLedger &&
  walRecoverable host.preprocCursorLedger &&
  walRecoverable host.leafOrFtsBurnLedger

/-- Fail-closed host: some ledger no longer opens and no write is in flight on any ledger. -/
structure HostFailedClosed (host : MultiLedgerHostState) : Prop where
  notOperational : hostOperational host = false
  poisonIdle : host.poisonLatch.volatileStage = none
  policyIdle : host.policyWindowLedger.volatileStage = none
  preprocIdle : host.preprocCursorLedger.volatileStage = none
  leafIdle : host.leafOrFtsBurnLedger.volatileStage = none

/-- The four local durable ledgers of the host. -/
inductive HostLedgerId where
  | poison
  | policy
  | preproc
  | leaf
  deriving Repr, DecidableEq

/-- Interleaved multi-ceremony and multi-crash host events (zero cross-file 2PC). -/
inductive MultiLedgerEvent where
  | ObserveCleanPoisonLatch (ceremonyId : Nat)
  | StagePolicySpend (ceremonyId : Nat) (amount : Nat) (intentDigest : Digest256)
  | FlushPolicyWal (ceremonyId : Nat)
  | StagePreprocBurn (ceremonyId : Nat) (batchIdx : Nat)
  | FlushPreprocWal (ceremonyId : Nat)
  | StageLeafOrFtsReserve (ceremonyId : Nat) (epochOrIndex : Nat) (msgDigest : Digest256)
  | FlushLeafWal (ceremonyId : Nat)
  | AdvancePolicyWindow (nextWindow : Nat)
  | FlushPolicyWindowWal
  | LatchPoisonFault (reasonCode : UInt64)
  | FlushPoisonWal
  | SaveCheckpoint (ledger : HostLedgerId)
  | EmitNetworkShare (ceremonyId : Nat) (party : Nat) (share : Digest256)
  | PowerLossCrash
      (poisonCrash : WalCrashBehavior)
      (policyCrash : WalCrashBehavior)
      (preprocCrash : WalCrashBehavior)
      (leafCrash : WalCrashBehavior)
  deriving Repr, DecidableEq

/-- Deterministic Monotone Burn-Before-Release transitions of an OPERATIONAL host over the 5
    ledgers. `EmitNetworkShare` additionally requires `ledgersCheckpointSaved`: reserved material
    is released only after the external checkpoints of all three burn ledgers are persisted. -/
def stepOperationalHost (host : MultiLedgerHostState) (ev : MultiLedgerEvent) :
    Option MultiLedgerHostState :=
  match ev with
  | .ObserveCleanPoisonLatch cid =>
    if (lookupVolatilePhase cid host.volatileCeremonies).isNone &&
       ((activeWalPayload host.poisonLatch).status == .clean) &&
       host.poisonLatch.volatileStage.isNone then
      some { host with
        volatileCeremonies := upsertVolatilePhase cid (.cleanObserved (activeWalGen host.poisonLatch)) host.volatileCeremonies }
    else
      none
  | .StagePolicySpend cid amount intentDigest =>
    match lookupVolatilePhase cid host.volatileCeremonies with
    | some (.cleanObserved pGen) =>
      let pol := activeWalPayload host.policyWindowLedger
      if ((activeWalPayload host.poisonLatch).status == .clean) &&
         host.poisonLatch.volatileStage.isNone &&
         host.policyWindowLedger.volatileStage.isNone &&
         decide (∀ e ∈ pol.committedSpends, e.ceremonyId ≠ cid ∧ e.intentDigest ≠ intentDigest) &&
         decide (windowCommittedSpend pol.currentWindow pol.committedSpends + amount ≤ pol.policyCap) then
        let newEntry : PolicySpendEntry :=
          { ceremonyId := cid, windowId := pol.currentWindow, amount := amount, intentDigest := intentDigest }
        let nextPol : PolicyWindowLedger :=
          { pol with committedSpends := newEntry :: pol.committedSpends }
        some { host with
          policyWindowLedger := stageTwoSlotWal host.policyWindowLedger nextPol
          volatileCeremonies := upsertVolatilePhase cid
            (.policyStaged pGen pol.currentWindow amount intentDigest) host.volatileCeremonies }
      else
        none
    | _ => none
  | .FlushPolicyWal cid =>
    match lookupVolatilePhase cid host.volatileCeremonies with
    | some (.policyStaged pGen win amount intentDigest) =>
      if host.policyWindowLedger.volatileStage.isSome then
        let flushed := flushTwoSlotWal host.policyWindowLedger
        if decide (PolicySpendEntry.mk cid win amount intentDigest ∈ (activeWalPayload flushed).committedSpends) then
          some { host with
            policyWindowLedger := flushed
            volatileCeremonies := upsertVolatilePhase cid
              (.policyCommitted pGen (activeWalGen flushed) win amount intentDigest) host.volatileCeremonies }
        else
          none
      else
        none
    | _ => none
  | .StagePreprocBurn cid batchIdx =>
    match lookupVolatilePhase cid host.volatileCeremonies with
    | some (.policyCommitted pGen polGen win amount intentDigest) =>
      let pre := activeWalPayload host.preprocCursorLedger
      if ((activeWalPayload host.poisonLatch).status == .clean) &&
         host.poisonLatch.volatileStage.isNone &&
         host.preprocCursorLedger.volatileStage.isNone &&
         decide (PolicySpendEntry.mk cid win amount intentDigest ∈
           (activeWalPayload host.policyWindowLedger).committedSpends) &&
         decide (pre.nextBatchCursor ≤ batchIdx) &&
         decide (∀ e ∈ pre.burnedBatches, e.ceremonyId ≠ cid ∧ e.batchIdx ≠ batchIdx) then
        let newBurn : PreprocBurnEntry := { ceremonyId := cid, batchIdx := batchIdx }
        let nextPre : PreprocCursorLedger :=
          { nextBatchCursor := batchIdx + 1, burnedBatches := newBurn :: pre.burnedBatches }
        some { host with
          preprocCursorLedger := stageTwoSlotWal host.preprocCursorLedger nextPre
          volatileCeremonies := upsertVolatilePhase cid
            (.preprocStaged pGen polGen win amount intentDigest batchIdx) host.volatileCeremonies }
      else
        none
    | _ => none
  | .FlushPreprocWal cid =>
    match lookupVolatilePhase cid host.volatileCeremonies with
    | some (.preprocStaged pGen polGen win amount intentDigest batchIdx) =>
      if host.preprocCursorLedger.volatileStage.isSome then
        let flushed := flushTwoSlotWal host.preprocCursorLedger
        if decide (PreprocBurnEntry.mk cid batchIdx ∈ (activeWalPayload flushed).burnedBatches) then
          some { host with
            preprocCursorLedger := flushed
            volatileCeremonies := upsertVolatilePhase cid
              (.preprocBurned pGen polGen (activeWalGen flushed) win amount intentDigest batchIdx)
              host.volatileCeremonies }
        else
          none
      else
        none
    | _ => none
  | .StageLeafOrFtsReserve cid epochOrIndex msgDigest =>
    match lookupVolatilePhase cid host.volatileCeremonies with
    | some (.preprocBurned pGen polGen preGen win amount intentDigest batchIdx) =>
      let lf := activeWalPayload host.leafOrFtsBurnLedger
      if ((activeWalPayload host.poisonLatch).status == .clean) &&
         host.poisonLatch.volatileStage.isNone &&
         host.leafOrFtsBurnLedger.volatileStage.isNone &&
         decide (PolicySpendEntry.mk cid win amount intentDigest ∈
           (activeWalPayload host.policyWindowLedger).committedSpends) &&
         decide (PreprocBurnEntry.mk cid batchIdx ∈
           (activeWalPayload host.preprocCursorLedger).burnedBatches) &&
         decide (lf.nextEpochCursor ≤ epochOrIndex) &&
         decide (∀ e ∈ lf.reservedLeaves, e.ceremonyId ≠ cid ∧ e.epochOrIndex ≠ epochOrIndex) then
        let newLeaf : LeafBurnEntry :=
          { ceremonyId := cid, epochOrIndex := epochOrIndex, msgDigest := msgDigest }
        let nextLf : LeafOrFtsBurnLedger :=
          { nextEpochCursor := epochOrIndex + 1, reservedLeaves := newLeaf :: lf.reservedLeaves }
        some { host with
          leafOrFtsBurnLedger := stageTwoSlotWal host.leafOrFtsBurnLedger nextLf
          volatileCeremonies := upsertVolatilePhase cid
            (.leafStaged pGen polGen preGen win amount intentDigest batchIdx epochOrIndex msgDigest)
            host.volatileCeremonies }
      else
        none
    | _ => none
  | .FlushLeafWal cid =>
    match lookupVolatilePhase cid host.volatileCeremonies with
    | some (.leafStaged pGen polGen preGen win amount intentDigest batchIdx epochOrIndex msgDigest) =>
      if host.leafOrFtsBurnLedger.volatileStage.isSome then
        let flushed := flushTwoSlotWal host.leafOrFtsBurnLedger
        if decide (LeafBurnEntry.mk cid epochOrIndex msgDigest ∈ (activeWalPayload flushed).reservedLeaves) then
          let rcpt : CeremonyReceipt := {
            ceremonyId := cid
            poisonCleanGen := pGen
            policyCommitGen := polGen
            preprocBurnGen := preGen
            leafReserveGen := activeWalGen flushed
            windowId := win
            amount := amount
            intentDigest := intentDigest
            batchIdx := batchIdx
            epochOrIndex := epochOrIndex
            msgDigest := msgDigest
          }
          some { host with
            leafOrFtsBurnLedger := flushed
            volatileCeremonies := upsertVolatilePhase cid (.receiptIssued rcpt) host.volatileCeremonies }
        else
          none
      else
        none
    | _ => none
  | .AdvancePolicyWindow nextWin =>
    let pol := activeWalPayload host.policyWindowLedger
    if host.policyWindowLedger.volatileStage.isNone && decide (pol.currentWindow < nextWin) then
      let nextPol : PolicyWindowLedger := { pol with currentWindow := nextWin }
      some { host with policyWindowLedger := stageTwoSlotWal host.policyWindowLedger nextPol }
    else
      none
  | .FlushPolicyWindowWal =>
    if host.policyWindowLedger.volatileStage.isSome then
      some { host with policyWindowLedger := flushTwoSlotWal host.policyWindowLedger }
    else
      none
  | .LatchPoisonFault reasonCode =>
    if host.poisonLatch.volatileStage.isNone then
      let cur := activeWalPayload host.poisonLatch
      let nextPoison : PoisonLatch := { status := .poisoned reasonCode, faultCount := cur.faultCount + 1 }
      some { host with poisonLatch := stageTwoSlotWal host.poisonLatch nextPoison }
    else
      none
  | .FlushPoisonWal =>
    if host.poisonLatch.volatileStage.isSome then
      some { host with poisonLatch := saveWalCheckpoint (flushTwoSlotWal host.poisonLatch) }
    else
      none
  | .EmitNetworkShare cid party share =>
    match lookupVolatilePhase cid host.volatileCeremonies with
    | some (.receiptIssued ceremonyReceipt) =>
      if ceremonyReceiptDurableValid host cid ceremonyReceipt &&
         ledgersCheckpointSaved host &&
         decide (∀ w ∈ host.outboundWire, ¬ (w.ceremonyId = cid ∧ w.party = party)) then
        let emitted : WireEmission := {
          ceremonyId := cid
          windowId := ceremonyReceipt.windowId
          amount := ceremonyReceipt.amount
          batchIdx := ceremonyReceipt.batchIdx
          epochOrIndex := ceremonyReceipt.epochOrIndex
          msgDigest := ceremonyReceipt.msgDigest
          party := party
          share := share
        }
        some { host with outboundWire := host.outboundWire ++ [emitted] }
      else
        none
    | _ => none
  | .SaveCheckpoint ledger =>
    match ledger with
    | .poison =>
      if host.poisonLatch.volatileStage.isNone then
        some { host with poisonLatch := saveWalCheckpoint host.poisonLatch }
      else
        none
    | .policy =>
      if host.policyWindowLedger.volatileStage.isNone then
        some { host with policyWindowLedger := saveWalCheckpoint host.policyWindowLedger }
      else
        none
    | .preproc =>
      if host.preprocCursorLedger.volatileStage.isNone then
        some { host with preprocCursorLedger := saveWalCheckpoint host.preprocCursorLedger }
      else
        none
    | .leaf =>
      if host.leafOrFtsBurnLedger.volatileStage.isNone then
        some { host with leafOrFtsBurnLedger := saveWalCheckpoint host.leafOrFtsBurnLedger }
      else
        none
  | .PowerLossCrash _ _ _ _ => none

/-- Host state after a `PowerLossCrash`: every ledger file recovers on its own, under its own
    crash mode, and all volatile RAM ceremony progress is gone. -/
def crashHostState (host : MultiLedgerHostState)
    (cPoison cPolicy cPreproc cLeaf : WalCrashBehavior) : MultiLedgerHostState where
  poisonLatch := crashRecoverWal cPoison host.poisonLatch
  policyWindowLedger := crashRecoverWal cPolicy host.policyWindowLedger
  preprocCursorLedger := crashRecoverWal cPreproc host.preprocCursorLedger
  leafOrFtsBurnLedger := crashRecoverWal cLeaf host.leafOrFtsBurnLedger
  volatileCeremonies := []
  outboundWire := host.outboundWire

/-- Host transition function. A `PowerLossCrash` can strike in ANY state, between any two
    individual ledger writes, with an independent crash mode per ledger file. Every other event is
    refused once some ledger no longer opens (fail closed). -/
def stepMultiLedgerHost (host : MultiLedgerHostState) (ev : MultiLedgerEvent) :
    Option MultiLedgerHostState :=
  match ev with
  | .PowerLossCrash cPoison cPolicy cPreproc cLeaf =>
    some (crashHostState host cPoison cPolicy cPreproc cLeaf)
  | _ => if hostOperational host then stepOperationalHost host ev else none

/-- Inductive multi-crash, multi-ceremony execution trace over `stepMultiLedgerHost`. -/
inductive ValidMultiLedgerTrace :
    MultiLedgerHostState → List MultiLedgerEvent → MultiLedgerHostState → Prop where
  | nil (s : MultiLedgerHostState) : ValidMultiLedgerTrace s [] s
  | cons {s₁ s₂ s₃ : MultiLedgerHostState} {ev : MultiLedgerEvent} {rest : List MultiLedgerEvent} :
      stepMultiLedgerHost s₁ ev = some s₂ →
      ValidMultiLedgerTrace s₂ rest s₃ →
      ValidMultiLedgerTrace s₁ (ev :: rest) s₃

/-- Canonical `PartyMachine` packaging of `stepMultiLedgerHost` on `SimulationSpine`. -/
def ceremonyHostMachine : PartyMachine MultiLedgerHostState MultiLedgerEvent OutboundNetworkWire :=
  PartyMachine.ofOption (fun s ev =>
    match stepMultiLedgerHost s ev with
    | some s' => some (s', s'.outboundWire)
    | none => none)

/-! ### Monotone Lattice Relations & Inductive Safety Invariants Across Crashes -/

private def poisonRel (a b : PoisonLatch) : Prop :=
  (a.status ≠ .clean → b.status ≠ .clean) ∧ a.faultCount ≤ b.faultCount

private def poisonInv (_ : PoisonLatch) : Prop := True

private def policyRel (a b : PolicyWindowLedger) : Prop :=
  b.policyCap = a.policyCap ∧
  a.currentWindow ≤ b.currentWindow ∧
  (∀ e ∈ a.committedSpends, e ∈ b.committedSpends)

private def policyInv (p : PolicyWindowLedger) : Prop :=
  (p.committedSpends.map (·.ceremonyId)).Nodup ∧
  (∀ win : Nat, windowCommittedSpend win p.committedSpends ≤ p.policyCap)

private def preprocRel (a b : PreprocCursorLedger) : Prop :=
  a.nextBatchCursor ≤ b.nextBatchCursor ∧
  (∀ e ∈ a.burnedBatches, e ∈ b.burnedBatches)

private def preprocInv (p : PreprocCursorLedger) : Prop :=
  (∀ e ∈ p.burnedBatches, e.batchIdx < p.nextBatchCursor) ∧
  (∀ a ∈ p.burnedBatches, ∀ b ∈ p.burnedBatches, a.ceremonyId ≠ b.ceremonyId → a.batchIdx ≠ b.batchIdx)

private def leafRel (a b : LeafOrFtsBurnLedger) : Prop :=
  a.nextEpochCursor ≤ b.nextEpochCursor ∧
  (∀ e ∈ a.reservedLeaves, e ∈ b.reservedLeaves)

private def leafInv (l : LeafOrFtsBurnLedger) : Prop :=
  (∀ e ∈ l.reservedLeaves, e.epochOrIndex < l.nextEpochCursor) ∧
  (∀ a ∈ l.reservedLeaves, ∀ b ∈ l.reservedLeaves,
    a.epochOrIndex = b.epochOrIndex → a = b)

private def WireBackedByDurableLedgers
    (pol : PolicyWindowLedger) (pre : PreprocCursorLedger) (lf : LeafOrFtsBurnLedger)
    (w : WireEmission) : Prop :=
  (∃ intent : Digest256,
    PolicySpendEntry.mk w.ceremonyId w.windowId w.amount intent ∈ pol.committedSpends) ∧
  PreprocBurnEntry.mk w.ceremonyId w.batchIdx ∈ pre.burnedBatches ∧
  LeafBurnEntry.mk w.ceremonyId w.epochOrIndex w.msgDigest ∈ lf.reservedLeaves

private structure HostGlobalInvariant (policyCap : Nat) (host : MultiLedgerHostState) : Prop where
  poison_wal : TwoSlotWalInv poisonRel poisonInv host.poisonLatch
  policy_wal : TwoSlotWalInv policyRel policyInv host.policyWindowLedger
  preproc_wal : TwoSlotWalInv preprocRel preprocInv host.preprocCursorLedger
  leaf_wal : TwoSlotWalInv leafRel leafInv host.leafOrFtsBurnLedger
  cap_fixed : (checkpointedWalPayload host.policyWindowLedger).policyCap = policyCap
  wire_backed : ∀ w ∈ host.outboundWire,
    WireBackedByDurableLedgers
      (checkpointedWalPayload host.policyWindowLedger)
      (checkpointedWalPayload host.preprocCursorLedger)
      (checkpointedWalPayload host.leafOrFtsBurnLedger) w

private theorem poisonRel_refl (x : PoisonLatch) : poisonRel x x :=
  ⟨fun h => h, Nat.le_refl _⟩

private theorem policyRel_refl (x : PolicyWindowLedger) : policyRel x x :=
  ⟨rfl, Nat.le_refl _, fun _ h => h⟩

private theorem preprocRel_refl (x : PreprocCursorLedger) : preprocRel x x :=
  ⟨Nat.le_refl _, fun _ h => h⟩

private theorem leafRel_refl (x : LeafOrFtsBurnLedger) : leafRel x x :=
  ⟨Nat.le_refl _, fun _ h => h⟩

private theorem wireBacked_mono
    {pol₁ pol₂ : PolicyWindowLedger} {pre₁ pre₂ : PreprocCursorLedger} {lf₁ lf₂ : LeafOrFtsBurnLedger}
    (hPol : policyRel pol₁ pol₂) (hPre : preprocRel pre₁ pre₂) (hLf : leafRel lf₁ lf₂)
    {w : WireEmission} (hw : WireBackedByDurableLedgers pol₁ pre₁ lf₁ w) :
    WireBackedByDurableLedgers pol₂ pre₂ lf₂ w := by
  rcases hw with ⟨⟨intent, hP⟩, hB, hL⟩
  exact ⟨⟨intent, hPol.2.2 _ hP⟩, hPre.2 _ hB, hLf.2 _ hL⟩

private theorem initMultiLedgerHostState_inv (policyCap : Nat) :
    HostGlobalInvariant policyCap (initMultiLedgerHostState policyCap) := by
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_⟩
  · exact initTwoSlotWal_inv poisonRel trivial
  · apply initTwoSlotWal_inv policyRel
    refine ⟨List.Pairwise.nil, fun win => ?_⟩
    simp [windowCommittedSpend]
  · apply initTwoSlotWal_inv preprocRel
    exact ⟨(fun _ h => nomatch h), (fun _ h _ _ _ => nomatch h)⟩
  · apply initTwoSlotWal_inv leafRel
    exact ⟨(fun _ h => nomatch h), (fun _ h _ _ _ => nomatch h)⟩
  · intro _ h; nomatch h

private theorem stepOperationalHost_preserves_inv {policyCap : Nat}
    {s s' : MultiLedgerHostState} {ev : MultiLedgerEvent}
    (hInv : HostGlobalInvariant policyCap s)
    (hStep : stepOperationalHost s ev = some s') :
    HostGlobalInvariant policyCap s' := by
  cases ev with
  | ObserveCleanPoisonLatch cid =>
    simp only [stepOperationalHost] at hStep
    split at hStep
    · injection hStep with hEq; subst hEq
      exact ⟨hInv.poison_wal, hInv.policy_wal, hInv.preproc_wal, hInv.leaf_wal, hInv.cap_fixed, hInv.wire_backed⟩
    · cases hStep
  | StagePolicySpend cid amount intentDigest =>
    simp only [stepOperationalHost] at hStep
    cases hPh : lookupVolatilePhase cid s.volatileCeremonies <;> simp only [hPh] at hStep
    · cases hStep
    · rename_i ph
      cases ph <;> simp only at hStep <;> try cases hStep
      rename_i pGen
      split at hStep
      · rename_i hCond
        injection hStep with hEq; subst hEq
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hCond
        rcases hCond with ⟨⟨⟨⟨_, _⟩, _⟩, hFresh⟩, hBudget⟩
        let pol := activeWalPayload s.policyWindowLedger
        let newEntry : PolicySpendEntry :=
          { ceremonyId := cid, windowId := pol.currentWindow, amount := amount, intentDigest := intentDigest }
        let nextPol : PolicyWindowLedger := { pol with committedSpends := newEntry :: pol.committedSpends }
        have hPolRel : policyRel pol nextPol := ⟨rfl, Nat.le_refl _, fun _ hm => .tail _ hm⟩
        have hNextPolInv : policyInv nextPol := by
          obtain ⟨hNodup, hAllWins⟩ := walInv_active hInv.policy_wal
          refine ⟨?_, ?_⟩
          · simp only [nextPol, List.map_cons, List.nodup_cons]
            refine ⟨?_, hNodup⟩
            intro hIn
            rcases List.mem_map.mp hIn with ⟨e, heMem, heCid⟩
            exact (hFresh e heMem).1 heCid
          · intro win
            simp only [nextPol, newEntry, windowCommittedSpend]
            by_cases hWin : pol.currentWindow == win
            · have hWinEq : pol.currentWindow = win := eq_of_beq hWin
              subst hWinEq
              simp only [hWin, ↓reduceIte]
              dsimp only [pol]
              omega
            · simp only [hWin, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
              exact hAllWins win
        obtain ⟨hStInv, hPayEq⟩ := stageTwoSlotWal_inv hInv.policy_wal hPolRel hNextPolInv
        refine ⟨hInv.poison_wal, hStInv, hInv.preproc_wal, hInv.leaf_wal, ?_, ?_⟩
        · dsimp only; rw [hPayEq]; exact hInv.cap_fixed
        · intro w hw
          dsimp only
          rw [hPayEq]
          exact hInv.wire_backed w hw
      · cases hStep
  | FlushPolicyWal cid =>
    simp only [stepOperationalHost] at hStep
    cases hPh : lookupVolatilePhase cid s.volatileCeremonies <;> simp only [hPh] at hStep
    · cases hStep
    · rename_i ph
      cases ph <;> simp only at hStep <;> try cases hStep
      split at hStep
      · split at hStep
        · injection hStep with hEq; subst hEq
          obtain ⟨hFlInv, _, hPolRel⟩ := flushTwoSlotWal_inv policyRel_refl hInv.policy_wal
          refine ⟨hInv.poison_wal, hFlInv, hInv.preproc_wal, hInv.leaf_wal, ?_, ?_⟩
          · exact hPolRel.1.trans hInv.cap_fixed
          · intro w hw
            exact wireBacked_mono hPolRel (preprocRel_refl _) (leafRel_refl _) (hInv.wire_backed w hw)
        · cases hStep
      · cases hStep
  | StagePreprocBurn cid batchIdx =>
    simp only [stepOperationalHost] at hStep
    cases hPh : lookupVolatilePhase cid s.volatileCeremonies <;> simp only [hPh] at hStep
    · cases hStep
    · rename_i ph
      cases ph <;> simp only at hStep <;> try cases hStep
      split at hStep
      · rename_i hCond
        injection hStep with hEq; subst hEq
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hCond
        rcases hCond with ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hCursorLe⟩, hDisj⟩
        let pre := activeWalPayload s.preprocCursorLedger
        let newBurn : PreprocBurnEntry := { ceremonyId := cid, batchIdx := batchIdx }
        let nextPre : PreprocCursorLedger :=
          { nextBatchCursor := batchIdx + 1, burnedBatches := newBurn :: pre.burnedBatches }
        have hPreRel : preprocRel pre nextPre := by
          dsimp only [preprocRel, pre, nextPre]
          exact ⟨by omega, fun _ hm => .tail _ hm⟩
        have hNextPreInv : preprocInv nextPre := by
          obtain ⟨hLt, hPairDisj⟩ := walInv_active hInv.preproc_wal
          refine ⟨?_, ?_⟩
          · intro e he
            rcases List.mem_cons.mp he with rfl | hOld
            · dsimp only [newBurn, nextPre]; omega
            · have := hLt e hOld; dsimp only [nextPre]; omega
          · intro a ha b hb hCidNe
            rcases List.mem_cons.mp ha with rfl | haOld
            · rcases List.mem_cons.mp hb with rfl | hbOld
              · exact False.elim (hCidNe rfl)
              · exact fun hB => (hDisj b hbOld).2 hB.symm
            · rcases List.mem_cons.mp hb with rfl | hbOld
              · exact (hDisj a haOld).2
              · exact hPairDisj a haOld b hbOld hCidNe
        obtain ⟨hStInv, hPayEq⟩ := stageTwoSlotWal_inv hInv.preproc_wal hPreRel hNextPreInv
        refine ⟨hInv.poison_wal, hInv.policy_wal, hStInv, hInv.leaf_wal, hInv.cap_fixed, ?_⟩
        intro w hw
        dsimp only
        rw [hPayEq]
        exact hInv.wire_backed w hw
      · cases hStep
  | FlushPreprocWal cid =>
    simp only [stepOperationalHost] at hStep
    cases hPh : lookupVolatilePhase cid s.volatileCeremonies <;> simp only [hPh] at hStep
    · cases hStep
    · rename_i ph
      cases ph <;> simp only at hStep <;> try cases hStep
      split at hStep
      · split at hStep
        · injection hStep with hEq; subst hEq
          obtain ⟨hFlInv, _, hPreRel⟩ := flushTwoSlotWal_inv preprocRel_refl hInv.preproc_wal
          refine ⟨hInv.poison_wal, hInv.policy_wal, hFlInv, hInv.leaf_wal, hInv.cap_fixed, ?_⟩
          intro w hw
          exact wireBacked_mono (policyRel_refl _) hPreRel (leafRel_refl _) (hInv.wire_backed w hw)
        · cases hStep
      · cases hStep
  | StageLeafOrFtsReserve cid epochOrIndex msgDigest =>
    simp only [stepOperationalHost] at hStep
    cases hPh : lookupVolatilePhase cid s.volatileCeremonies <;> simp only [hPh] at hStep
    · cases hStep
    · rename_i ph
      cases ph <;> simp only at hStep <;> try cases hStep
      split at hStep
      · rename_i hCond
        injection hStep with hEq; subst hEq
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hCond
        rcases hCond with ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, hEpochLe⟩, hLeafDisj⟩
        let lf := activeWalPayload s.leafOrFtsBurnLedger
        let newLeaf : LeafBurnEntry :=
          { ceremonyId := cid, epochOrIndex := epochOrIndex, msgDigest := msgDigest }
        let nextLf : LeafOrFtsBurnLedger :=
          { nextEpochCursor := epochOrIndex + 1, reservedLeaves := newLeaf :: lf.reservedLeaves }
        have hLfRel : leafRel lf nextLf := by
          dsimp only [leafRel, lf, nextLf]
          exact ⟨by omega, fun _ hm => .tail _ hm⟩
        have hNextLfInv : leafInv nextLf := by
          obtain ⟨hLt, hUniq⟩ := walInv_active hInv.leaf_wal
          refine ⟨?_, ?_⟩
          · intro e he
            rcases List.mem_cons.mp he with rfl | hOld
            · dsimp only [newLeaf, nextLf]; omega
            · have := hLt e hOld; dsimp only [nextLf]; omega
          · intro a ha b hb hEpEq
            rcases List.mem_cons.mp ha with rfl | haOld
            · rcases List.mem_cons.mp hb with rfl | hbOld
              · rfl
              · exact False.elim ((hLeafDisj b hbOld).2 hEpEq.symm)
            · rcases List.mem_cons.mp hb with rfl | hbOld
              · exact False.elim ((hLeafDisj a haOld).2 hEpEq)
              · exact hUniq a haOld b hbOld hEpEq
        obtain ⟨hStInv, hPayEq⟩ := stageTwoSlotWal_inv hInv.leaf_wal hLfRel hNextLfInv
        refine ⟨hInv.poison_wal, hInv.policy_wal, hInv.preproc_wal, hStInv, hInv.cap_fixed, ?_⟩
        intro w hw
        dsimp only
        rw [hPayEq]
        exact hInv.wire_backed w hw
      · cases hStep
  | FlushLeafWal cid =>
    simp only [stepOperationalHost] at hStep
    cases hPh : lookupVolatilePhase cid s.volatileCeremonies <;> simp only [hPh] at hStep
    · cases hStep
    · rename_i ph
      cases ph <;> simp only at hStep <;> try cases hStep
      split at hStep
      · split at hStep
        · injection hStep with hEq; subst hEq
          obtain ⟨hFlInv, _, hLfRel⟩ := flushTwoSlotWal_inv leafRel_refl hInv.leaf_wal
          refine ⟨hInv.poison_wal, hInv.policy_wal, hInv.preproc_wal, hFlInv, hInv.cap_fixed, ?_⟩
          intro w hw
          exact wireBacked_mono (policyRel_refl _) (preprocRel_refl _) hLfRel (hInv.wire_backed w hw)
        · cases hStep
      · cases hStep
  | AdvancePolicyWindow nextWin =>
    simp only [stepOperationalHost] at hStep
    split at hStep
    · rename_i hCond
      injection hStep with hEq; subst hEq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hCond
      let pol := activeWalPayload s.policyWindowLedger
      let nextPol : PolicyWindowLedger := { pol with currentWindow := nextWin }
      have hPolRel : policyRel pol nextPol := ⟨rfl, Nat.le_of_lt hCond.2, fun _ hm => hm⟩
      have hNextInv : policyInv nextPol := walInv_active hInv.policy_wal
      obtain ⟨hStInv, hPaySt⟩ := stageTwoSlotWal_inv hInv.policy_wal hPolRel hNextInv
      refine ⟨hInv.poison_wal, hStInv, hInv.preproc_wal, hInv.leaf_wal, ?_, ?_⟩
      · dsimp only; rw [hPaySt]; exact hInv.cap_fixed
      · intro w hw
        dsimp only
        rw [hPaySt]
        exact hInv.wire_backed w hw
    · cases hStep
  | FlushPolicyWindowWal =>
    simp only [stepOperationalHost] at hStep
    split at hStep
    · injection hStep with hEq; subst hEq
      obtain ⟨hFlInv, _, hFlRel⟩ := flushTwoSlotWal_inv policyRel_refl hInv.policy_wal
      refine ⟨hInv.poison_wal, hFlInv, hInv.preproc_wal, hInv.leaf_wal, ?_, ?_⟩
      · exact hFlRel.1.trans hInv.cap_fixed
      · intro w hw
        exact wireBacked_mono hFlRel (preprocRel_refl _) (leafRel_refl _) (hInv.wire_backed w hw)
    · cases hStep
  | LatchPoisonFault reasonCode =>
    simp only [stepOperationalHost] at hStep
    split at hStep
    · injection hStep with hEq; subst hEq
      let cur := activeWalPayload s.poisonLatch
      let nextPoison : PoisonLatch := { status := .poisoned reasonCode, faultCount := cur.faultCount + 1 }
      have hPRel : poisonRel cur nextPoison := ⟨fun _ => by simp [nextPoison], by simp [nextPoison]⟩
      obtain ⟨hStInv, _⟩ := stageTwoSlotWal_inv hInv.poison_wal hPRel trivial
      exact ⟨hStInv, hInv.policy_wal, hInv.preproc_wal, hInv.leaf_wal, hInv.cap_fixed, hInv.wire_backed⟩
    · cases hStep
  | FlushPoisonWal =>
    simp only [stepOperationalHost] at hStep
    split at hStep
    · injection hStep with hEq; subst hEq
      obtain ⟨hFlInv, hIdle, _⟩ := flushTwoSlotWal_inv poisonRel_refl hInv.poison_wal
      obtain ⟨hSaved, _⟩ := saveWalCheckpoint_inv poisonRel_refl hFlInv hIdle
      exact ⟨hSaved, hInv.policy_wal, hInv.preproc_wal, hInv.leaf_wal, hInv.cap_fixed, hInv.wire_backed⟩
    · cases hStep
  | SaveCheckpoint ledger =>
    cases ledger with
    | poison =>
      simp only [stepOperationalHost] at hStep
      split at hStep
      · rename_i hIdle
        injection hStep with hEq; subst hEq
        obtain ⟨hSv, _⟩ := saveWalCheckpoint_inv poisonRel_refl hInv.poison_wal
          (Option.isNone_iff_eq_none.mp hIdle)
        exact ⟨hSv, hInv.policy_wal, hInv.preproc_wal, hInv.leaf_wal, hInv.cap_fixed, hInv.wire_backed⟩
      · cases hStep
    | policy =>
      simp only [stepOperationalHost] at hStep
      split at hStep
      · rename_i hIdle
        injection hStep with hEq; subst hEq
        obtain ⟨hSv, hRel⟩ := saveWalCheckpoint_inv policyRel_refl hInv.policy_wal
          (Option.isNone_iff_eq_none.mp hIdle)
        exact ⟨hInv.poison_wal, hSv, hInv.preproc_wal, hInv.leaf_wal, hRel.1.trans hInv.cap_fixed,
          fun w hw => wireBacked_mono hRel (preprocRel_refl _) (leafRel_refl _) (hInv.wire_backed w hw)⟩
      · cases hStep
    | preproc =>
      simp only [stepOperationalHost] at hStep
      split at hStep
      · rename_i hIdle
        injection hStep with hEq; subst hEq
        obtain ⟨hSv, hRel⟩ := saveWalCheckpoint_inv preprocRel_refl hInv.preproc_wal
          (Option.isNone_iff_eq_none.mp hIdle)
        exact ⟨hInv.poison_wal, hInv.policy_wal, hSv, hInv.leaf_wal, hInv.cap_fixed,
          fun w hw => wireBacked_mono (policyRel_refl _) hRel (leafRel_refl _) (hInv.wire_backed w hw)⟩
      · cases hStep
    | leaf =>
      simp only [stepOperationalHost] at hStep
      split at hStep
      · rename_i hIdle
        injection hStep with hEq; subst hEq
        obtain ⟨hSv, hRel⟩ := saveWalCheckpoint_inv leafRel_refl hInv.leaf_wal
          (Option.isNone_iff_eq_none.mp hIdle)
        exact ⟨hInv.poison_wal, hInv.policy_wal, hInv.preproc_wal, hSv, hInv.cap_fixed,
          fun w hw => wireBacked_mono (policyRel_refl _) (preprocRel_refl _) hRel (hInv.wire_backed w hw)⟩
      · cases hStep
  | EmitNetworkShare cid party share =>
    simp only [stepOperationalHost] at hStep
    cases hPh : lookupVolatilePhase cid s.volatileCeremonies <;> simp only [hPh] at hStep
    · cases hStep
    · rename_i ph
      cases ph <;> simp only at hStep <;> try cases hStep
      rename_i rcpt
      split at hStep
      · rename_i hCond
        injection hStep with hEq; subst hEq
        simp only [Bool.and_eq_true, ceremonyReceiptDurableValid, ledgersCheckpointSaved,
          decide_eq_true_eq] at hCond
        rcases hCond with
          ⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hPolMem⟩, hPreMem⟩, hLfMem⟩, ⟨⟨⟨_, hPolSaved⟩, hPreSaved⟩, hLfSaved⟩⟩, _⟩
        rw [← walInv_saved_floor hInv.policy_wal hPolSaved] at hPolMem
        rw [← walInv_saved_floor hInv.preproc_wal hPreSaved] at hPreMem
        rw [← walInv_saved_floor hInv.leaf_wal hLfSaved] at hLfMem
        refine ⟨hInv.poison_wal, hInv.policy_wal, hInv.preproc_wal, hInv.leaf_wal, hInv.cap_fixed, ?_⟩
        intro w hw
        rcases List.mem_append.mp hw with hOld | hNew
        · exact hInv.wire_backed w hOld
        · rcases List.mem_singleton.mp hNew with rfl
          exact ⟨⟨rcpt.intentDigest, hPolMem⟩, hPreMem, hLfMem⟩
      · cases hStep
  | PowerLossCrash cPoison cPolicy cPreproc cLeaf =>
    simp [stepOperationalHost] at hStep


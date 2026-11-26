module
public import Qsag.Math.GoldilocksBase
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
public import Qsag.Spec.Encoding
public import Qsag.Tactic.Prelude
public import Qsag.Exec.SimulationSpine
public import Qsag.Math.Goldilocks
public import Qsag.Math.Gf2Pow128
public import Qsag.Protocol.Aggregation.UcGames
public import Qsag.Exec.PosixCrashWal
public import Qsag.Tactic.AssuranceKit

public import Qsag.Math.Counting

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

/-! ### Constructive Deduplicated Spend Accounting Lemmas -/

private def findSpendEntryByCid (cid : Nat) : List PolicySpendEntry → Option PolicySpendEntry
  | [] => none
  | e :: rest => if e.ceremonyId == cid then some e else findSpendEntryByCid cid rest

private theorem findSpendEntryByCid_of_mem_nodup {cid win amt : Nat} {intent : Digest256}
    {entries : List PolicySpendEntry}
    (hNodup : (entries.map (·.ceremonyId)).Nodup)
    (hMem : PolicySpendEntry.mk cid win amt intent ∈ entries) :
    findSpendEntryByCid cid entries = some (PolicySpendEntry.mk cid win amt intent) := by
  induction entries with
  | nil => cases hMem
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hNodup
    rcases hNodup with ⟨hNotInTl, hTlNodup⟩
    rcases List.mem_cons.mp hMem with rfl | hInTl
    · simp [findSpendEntryByCid]
    · have hNe : (hd.ceremonyId == cid) = false := by
        cases hEq : hd.ceremonyId == cid
        · rfl
        · exfalso
          have hCidEq : hd.ceremonyId = cid := eq_of_beq hEq
          apply hNotInTl
          rw [hCidEq]
          exact List.mem_map.mpr ⟨PolicySpendEntry.mk cid win amt intent, hInTl, rfl⟩
      simp only [findSpendEntryByCid, hNe, Bool.false_eq_true, ↓reduceIte]
      exact ih hTlNodup hInTl

private def eraseSpendByCid (cid : Nat) : List PolicySpendEntry → List PolicySpendEntry
  | [] => []
  | e :: rest => if e.ceremonyId == cid then rest else e :: eraseSpendByCid cid rest

private theorem mem_of_mem_eraseSpendByCid {cid : Nat} {x : PolicySpendEntry} :
    ∀ {entries : List PolicySpendEntry}, x ∈ eraseSpendByCid cid entries → x ∈ entries
  | [], h => nomatch h
  | e :: rest, h => by
    simp only [eraseSpendByCid] at h
    by_cases he : e.ceremonyId == cid
    · simp only [he, ↓reduceIte] at h
      exact .tail _ h
    · simp only [he, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | hMore
      · exact .head _
      · exact .tail _ (mem_of_mem_eraseSpendByCid hMore)

private theorem eraseSpendByCid_nodup (cid : Nat) :
    ∀ {entries : List PolicySpendEntry},
      (entries.map (·.ceremonyId)).Nodup →
      ((eraseSpendByCid cid entries).map (·.ceremonyId)).Nodup
  | [], _ => List.Pairwise.nil
  | e :: rest, hNd => by
    simp only [List.map_cons, List.nodup_cons] at hNd
    rcases hNd with ⟨hNotIn, hRestNd⟩
    simp only [eraseSpendByCid]
    by_cases hEq : e.ceremonyId == cid
    · simp only [hEq, ↓reduceIte]; exact hRestNd
    · simp only [hEq, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.nodup_cons]
      refine ⟨?_, eraseSpendByCid_nodup cid hRestNd⟩
      intro hInSub
      rcases List.mem_map.mp hInSub with ⟨x, hxSub, hxCid⟩
      exact hNotIn (List.mem_map.mpr ⟨x, mem_of_mem_eraseSpendByCid hxSub, hxCid⟩)

private theorem mem_eraseSpendByCid_of_ne {cid : Nat} {x : PolicySpendEntry}
    (hNe : x.ceremonyId ≠ cid) :
    ∀ {entries : List PolicySpendEntry}, x ∈ entries → x ∈ eraseSpendByCid cid entries
  | [], h => nomatch h
  | e :: rest, h => by
    simp only [eraseSpendByCid]
    rcases List.mem_cons.mp h with rfl | hRest
    · have hFalse : (x.ceremonyId == cid) = false := beq_false_of_ne hNe
      simp [hFalse]
    · by_cases he : e.ceremonyId == cid
      · simp [he, hRest]
      · simp [he, mem_eraseSpendByCid_of_ne hNe hRest]

private theorem windowCommittedSpend_split_found {cid win : Nat} {pe : PolicySpendEntry} :
    ∀ {entries : List PolicySpendEntry},
      findSpendEntryByCid cid entries = some pe →
      pe.windowId = win →
      pe.amount + windowCommittedSpend win (eraseSpendByCid cid entries) =
        windowCommittedSpend win entries
  | [], hFind, _ => nomatch hFind
  | e :: rest, hFind, hWin => by
    simp only [findSpendEntryByCid] at hFind
    simp only [eraseSpendByCid, windowCommittedSpend]
    by_cases hEq : e.ceremonyId == cid
    · simp only [hEq, ↓reduceIte] at hFind ⊢
      injection hFind with hPe; subst hPe
      simp [hWin]
    · simp only [hEq, Bool.false_eq_true, ↓reduceIte] at hFind ⊢
      have ih := windowCommittedSpend_split_found hFind hWin
      simp only [windowCommittedSpend]
      omega

private theorem dedupWireByCidAux_props (seen : List Nat) (wire : OutboundNetworkWire) :
    (∀ w ∈ dedupWireByCidAux seen wire, w ∈ wire ∧ w.ceremonyId ∉ seen) ∧
    ((dedupWireByCidAux seen wire).map (·.ceremonyId)).Nodup := by
  induction wire generalizing seen with
  | nil =>
    exact ⟨(fun _ h => nomatch h), List.Pairwise.nil⟩
  | cons e rest ih =>
    simp only [dedupWireByCidAux]
    by_cases hIn : e.ceremonyId ∈ seen
    · simp only [hIn, ↓reduceIte]
      obtain ⟨hSub, hNd⟩ := ih seen
      exact ⟨fun w hw => ⟨.tail _ (hSub w hw).1, (hSub w hw).2⟩, hNd⟩
    · simp only [hIn, ↓reduceIte]
      obtain ⟨hSub, hNd⟩ := ih (e.ceremonyId :: seen)
      refine ⟨?_, ?_⟩
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hTail
        · exact ⟨.head _, hIn⟩
        · obtain ⟨hMemRest, hNotInCons⟩ := hSub w hTail
          exact ⟨.tail _ hMemRest, fun hs => hNotInCons (.tail _ hs)⟩
      · simp only [List.map_cons, List.nodup_cons]
        refine ⟨?_, hNd⟩
        intro hDup
        rcases List.mem_map.mp hDup with ⟨w, hwTail, hwCid⟩
        exact (hSub w hwTail).2 (by rw [hwCid]; exact .head _)

private theorem sum_dedup_wire_le_committed (win : Nat) :
    ∀ (L : OutboundNetworkWire) (entries : List PolicySpendEntry),
      (L.map (·.ceremonyId)).Nodup →
      (entries.map (·.ceremonyId)).Nodup →
      (∀ w ∈ L, w.windowId = win ∧
        ∃ intent : Digest256, PolicySpendEntry.mk w.ceremonyId w.windowId w.amount intent ∈ entries) →
      L.foldr (fun e acc => e.amount + acc) 0 ≤ windowCommittedSpend win entries
  | [], _, _, _, _ => Nat.zero_le _
  | w :: rest, entries, hLNd, hENd, hBacked => by
    simp only [List.map_cons, List.nodup_cons] at hLNd
    rcases hLNd with ⟨hWNotInRest, hRestNd⟩
    obtain ⟨hWWin, ⟨intent0, hWMem⟩⟩ := hBacked w (.head _)
    have hFound := findSpendEntryByCid_of_mem_nodup hENd hWMem
    have hSplit := windowCommittedSpend_split_found (win := win) hFound hWWin
    dsimp only at hSplit
    have hSubENd := eraseSpendByCid_nodup w.ceremonyId hENd
    have hRestBacked : ∀ u ∈ rest, u.windowId = win ∧
        ∃ intent : Digest256,
          PolicySpendEntry.mk u.ceremonyId u.windowId u.amount intent ∈ eraseSpendByCid w.ceremonyId entries := by
      intro u hu
      obtain ⟨huWin, ⟨iu, huMem⟩⟩ := hBacked u (.tail _ hu)
      have hNeCid : u.ceremonyId ≠ w.ceremonyId := by
        intro hEq
        apply hWNotInRest
        exact List.mem_map.mpr ⟨u, hu, hEq⟩
      exact ⟨huWin, ⟨iu, mem_eraseSpendByCid_of_ne hNeCid huMem⟩⟩
    have ih := sum_dedup_wire_le_committed win rest (eraseSpendByCid w.ceremonyId entries)
      hRestNd hSubENd hRestBacked
    simp only [List.foldr_cons]
    omega


/-! ### Crash-Closed Safety Invariant: Live Ledgers or Fail-Closed Host -/

/-- The three wire-level safety facts, stated on `OutboundNetworkWire` alone. -/
private structure WireSafe (policyCap : Nat) (wire : OutboundNetworkWire) : Prop where
  batch_disjoint : ∀ e₁ ∈ wire, ∀ e₂ ∈ wire,
    e₁.ceremonyId ≠ e₂.ceremonyId → e₁.batchIdx ≠ e₂.batchIdx
  leaf_unique : ∀ e₁ ∈ wire, ∀ e₂ ∈ wire,
    e₁.epochOrIndex = e₂.epochOrIndex →
    e₁.msgDigest = e₂.msgDigest ∧ e₁.ceremonyId = e₂.ceremonyId
  spend_le : ∀ win : Nat, wireWindowSpend win wire ≤ policyCap

private theorem wireSpend_le_checkpointed {policyCap : Nat} {host : MultiLedgerHostState}
    (hInv : HostGlobalInvariant policyCap host) (win : Nat) :
    wireWindowSpend win host.outboundWire ≤
      windowCommittedSpend win (checkpointedWalPayload host.policyWindowLedger).committedSpends := by
  let relList := releasedCeremoniesInWindow win host.outboundWire
  obtain ⟨hSub, hRelNd⟩ :=
    dedupWireByCidAux_props [] (host.outboundWire.filter (fun e => e.windowId == win))
  obtain ⟨hPolNd, _⟩ := (walInv_facts policyRel_refl hInv.policy_wal).2.2.1
  apply sum_dedup_wire_le_committed win relList
    (checkpointedWalPayload host.policyWindowLedger).committedSpends hRelNd hPolNd
  intro w hw
  have hwFilt : w ∈ host.outboundWire.filter (fun e => e.windowId == win) := (hSub w hw).1
  obtain ⟨hwWire, hwWinB⟩ := List.mem_filter.mp hwFilt
  exact ⟨eq_of_beq hwWinB, (hInv.wire_backed w hwWire).1⟩

private theorem wireSafe_of_globalInv {policyCap : Nat} {host : MultiLedgerHostState}
    (hInv : HostGlobalInvariant policyCap host) : WireSafe policyCap host.outboundWire := by
  refine ⟨?_, ?_, ?_⟩
  · intro e₁ he₁ e₂ he₂ hCidNe
    have hb₁ := (hInv.wire_backed e₁ he₁).2.1
    have hb₂ := (hInv.wire_backed e₂ he₂).2.1
    exact (walInv_facts preprocRel_refl hInv.preproc_wal).2.2.1.2 _ hb₁ _ hb₂ hCidNe
  · intro e₁ he₁ e₂ he₂ hEpEq
    have hl₁ := (hInv.wire_backed e₁ he₁).2.2
    have hl₂ := (hInv.wire_backed e₂ he₂).2.2
    have hEntryEq := (walInv_facts leafRel_refl hInv.leaf_wal).2.2.1.2 _ hl₁ _ hl₂ hEpEq
    injection hEntryEq with hCid hEp hMsg
    exact ⟨hMsg, hCid⟩
  · intro win
    obtain ⟨_, hCapAll⟩ := (walInv_facts policyRel_refl hInv.policy_wal).2.2.1
    have hCapBound := hCapAll win
    rw [hInv.cap_fixed] at hCapBound
    exact Nat.le_trans (wireSpend_le_checkpointed hInv win) hCapBound

/-- Every accepted step is a crash, or an operational transition of a host whose ledgers all open. -/
private theorem stepMultiLedgerHost_cases {s s' : MultiLedgerHostState} {ev : MultiLedgerEvent}
    (hStep : stepMultiLedgerHost s ev = some s') :
    (∃ a b c d, ev = .PowerLossCrash a b c d ∧ s' = crashHostState s a b c d) ∨
    (hostOperational s = true ∧ stepOperationalHost s ev = some s') := by
  cases ev with
  | PowerLossCrash a b c d =>
    left
    simp only [stepMultiLedgerHost] at hStep
    injection hStep with hEq
    exact ⟨a, b, c, d, rfl, hEq.symm⟩
  | _ =>
    right
    simp only [stepMultiLedgerHost] at hStep
    split at hStep
    · rename_i hOp
      exact ⟨hOp, hStep⟩
    · cases hStep

/-- A crash of a healthy host leaves every ledger healthy, or the host fails closed. -/
private theorem crashHostState_inv {policyCap : Nat} {s : MultiLedgerHostState}
    (hInv : HostGlobalInvariant policyCap s) (a b c d : WalCrashBehavior) :
    HostGlobalInvariant policyCap (crashHostState s a b c d) ∨
    HostFailedClosed (crashHostState s a b c d) := by
  have hDeadOf : hostOperational (crashHostState s a b c d) = false →
      HostFailedClosed (crashHostState s a b c d) := fun h =>
    ⟨h, crashRecoverWal_stage_none _ _, crashRecoverWal_stage_none _ _,
      crashRecoverWal_stage_none _ _, crashRecoverWal_stage_none _ _⟩
  rcases crashRecoverWal_inv poisonRel_refl hInv.poison_wal a with hD | ⟨hPo, _⟩
  · exact Or.inr (hDeadOf (by simp [hostOperational, crashHostState, hD]))
  rcases crashRecoverWal_inv policyRel_refl hInv.policy_wal b with hD | ⟨hPl, hPlRel⟩
  · exact Or.inr (hDeadOf (by simp [hostOperational, crashHostState, hD]))
  rcases crashRecoverWal_inv preprocRel_refl hInv.preproc_wal c with hD | ⟨hPr, hPrRel⟩
  · exact Or.inr (hDeadOf (by simp [hostOperational, crashHostState, hD]))
  rcases crashRecoverWal_inv leafRel_refl hInv.leaf_wal d with hD | ⟨hLf, hLfRel⟩
  · exact Or.inr (hDeadOf (by simp [hostOperational, crashHostState, hD]))
  exact Or.inl ⟨hPo, hPl, hPr, hLf, hPlRel.1.trans hInv.cap_fixed,
    fun w hw => wireBacked_mono hPlRel hPrRel hLfRel (hInv.wire_backed w hw)⟩

/-- A fail-closed host stays fail-closed across every further crash. -/
private theorem crashHostState_failedClosed {s : MultiLedgerHostState}
    (hDead : HostFailedClosed s) (a b c d : WalCrashBehavior) :
    HostFailedClosed (crashHostState s a b c d) := by
  refine ⟨?_, crashRecoverWal_stage_none _ _, crashRecoverWal_stage_none _ _,
    crashRecoverWal_stage_none _ _, crashRecoverWal_stage_none _ _⟩
  have hOp := hDead.notOperational
  unfold hostOperational at hOp
  cases hP : walRecoverable s.poisonLatch with
  | false =>
    have h := crashRecoverWal_dead_stays_dead a _ hP hDead.poisonIdle
    simp [hostOperational, crashHostState, h]
  | true =>
    cases hQ : walRecoverable s.policyWindowLedger with
    | false =>
      have h := crashRecoverWal_dead_stays_dead b _ hQ hDead.policyIdle
      simp [hostOperational, crashHostState, h]
    | true =>
      cases hR : walRecoverable s.preprocCursorLedger with
      | false =>
        have h := crashRecoverWal_dead_stays_dead c _ hR hDead.preprocIdle
        simp [hostOperational, crashHostState, h]
      | true =>
        cases hS : walRecoverable s.leafOrFtsBurnLedger with
        | false =>
          have h := crashRecoverWal_dead_stays_dead d _ hS hDead.leafIdle
          simp [hostOperational, crashHostState, h]
        | true =>
          rw [hP, hQ, hR, hS] at hOp
          simp at hOp

/-- Inductive safety invariant across arbitrary crashes: the wire facts hold, and the host is
    either healthy on all four ledgers or has failed closed. -/
private structure HostCrashInvariant (policyCap : Nat) (host : MultiLedgerHostState) : Prop where
  wire_safe : WireSafe policyCap host.outboundWire
  live_or_dead : HostGlobalInvariant policyCap host ∨ HostFailedClosed host

private theorem initMultiLedgerHostState_crashInv (policyCap : Nat) :
    HostCrashInvariant policyCap (initMultiLedgerHostState policyCap) :=
  ⟨wireSafe_of_globalInv (initMultiLedgerHostState_inv policyCap),
    Or.inl (initMultiLedgerHostState_inv policyCap)⟩

private theorem stepMultiLedgerHost_preserves_crashInv {policyCap : Nat}
    {s s' : MultiLedgerHostState} {ev : MultiLedgerEvent}
    (hInv : HostCrashInvariant policyCap s)
    (hStep : stepMultiLedgerHost s ev = some s') :
    HostCrashInvariant policyCap s' := by
  rcases stepMultiLedgerHost_cases hStep with ⟨a, b, c, d, _, rfl⟩ | ⟨hOp, hStep'⟩
  · refine ⟨hInv.wire_safe, ?_⟩
    rcases hInv.live_or_dead with hG | hD
    · exact crashHostState_inv hG a b c d
    · exact Or.inr (crashHostState_failedClosed hD a b c d)
  · rcases hInv.live_or_dead with hG | hD
    · have hG' := stepOperationalHost_preserves_inv hG hStep'
      exact ⟨wireSafe_of_globalInv hG', Or.inl hG'⟩
    · rw [hD.notOperational] at hOp
      cases hOp

private theorem validMultiLedgerTrace_preserves_crashInv {policyCap : Nat}
    {s₁ s₂ : MultiLedgerHostState} {trace : List MultiLedgerEvent}
    (hInv : HostCrashInvariant policyCap s₁)
    (hTrace : ValidMultiLedgerTrace s₁ trace s₂) :
    HostCrashInvariant policyCap s₂ := by
  induction hTrace with
  | nil _ => exact hInv
  | cons hStep _ ih => exact ih (stepMultiLedgerHost_preserves_crashInv hInv hStep)

/-! ### Flagship Theorems for Section 1 -/

/-- **Zero One-Time Pad / Beaver / SPCOT Reuse (`no_preproc_batch_reused_on_wire`)**:
    Across arbitrary interleaved multi-ceremony steps and arbitrary independent non-2PC
    `PowerLossCrash` events (including loss of an ACTIVE ledger slot), distinct emitted network
    ceremonies NEVER consume overlapping preprocessing `batchIdx`. -/
theorem no_preproc_batch_reused_on_wire
    (policyCap : Nat) (trace : List MultiLedgerEvent) (finalState : MultiLedgerHostState)
    (hTrace : ValidMultiLedgerTrace (initMultiLedgerHostState policyCap) trace finalState) :
    ∀ e₁ ∈ finalState.outboundWire, ∀ e₂ ∈ finalState.outboundWire,
      e₁.ceremonyId ≠ e₂.ceremonyId → e₁.batchIdx ≠ e₂.batchIdx :=
  (validMultiLedgerTrace_preserves_crashInv
    (initMultiLedgerHostState_crashInv policyCap) hTrace).wire_safe.batch_disjoint

/-- **Zero Stateful Leaf / FTS Antichain Reuse (`no_leaf_double_sign_on_wire`)**:
    Across arbitrary interleaved ceremonies and mid-ceremony `PowerLossCrash` events (crashes
    between `PolicySpendCommitted` and `LeafOrFtsReserved`, torn inactive writes, and loss of the
    active leaf slot with rollback to the checkpointed snapshot), distinct messages NEVER appear on
    `OutboundNetworkWire` under the same `epochOrIndex`. -/
theorem no_leaf_double_sign_on_wire
    (policyCap : Nat) (trace : List MultiLedgerEvent) (finalState : MultiLedgerHostState)
    (hTrace : ValidMultiLedgerTrace (initMultiLedgerHostState policyCap) trace finalState) :
    ∀ e₁ ∈ finalState.outboundWire, ∀ e₂ ∈ finalState.outboundWire,
      e₁.epochOrIndex = e₂.epochOrIndex →
      e₁.msgDigest = e₂.msgDigest ∧ e₁.ceremonyId = e₂.ceremonyId :=
  (validMultiLedgerTrace_preserves_crashInv
    (initMultiLedgerHostState_crashInv policyCap) hTrace).wire_safe.leaf_unique

/-- **Monotone Spend-Cap Conservation (`wire_spend_le_policy_cap`)**:
    In every policy window `win`, the total amount of all released ceremonies on
    `OutboundNetworkWire` never exceeds `policyCap`; and while the host is operational it is
    bounded by the CHECKPOINTED committed spend of `win`, the snapshot no crash can roll back
    (crashed half-ceremonies burn budget conservatively and NEVER recycle or double-spend). -/
theorem wire_spend_le_policy_cap
    (policyCap : Nat) (trace : List MultiLedgerEvent) (finalState : MultiLedgerHostState)
    (hTrace : ValidMultiLedgerTrace (initMultiLedgerHostState policyCap) trace finalState)
    (win : Nat) :
    wireWindowSpend win finalState.outboundWire ≤ policyCap ∧
    (hostOperational finalState = true →
      wireWindowSpend win finalState.outboundWire ≤
        windowCommittedSpend win
          (checkpointedWalPayload finalState.policyWindowLedger).committedSpends) := by
  have hInv := validMultiLedgerTrace_preserves_crashInv
    (initMultiLedgerHostState_crashInv policyCap) hTrace
  refine ⟨hInv.wire_safe.spend_le win, fun hOp => ?_⟩
  rcases hInv.live_or_dead with hG | hD
  · exact wireSpend_le_checkpointed hG win
  · rw [hD.notOperational] at hOp
    cases hOp

/-- **Multi-Ledger Burn-Before-Release Crash & Interleaving Composition
    (`ceremony_multi_ledger_crash_interleaving_safe`)**:
    Unifies zero preprocessing batch reuse, zero stateful leaf/FTS double-signing, monotone
    per-window spend-cap conservation, and checkpointed poison-latch persistence across arbitrary
    multi-ceremony interleavings and non-atomic per-file `PowerLossCrash` restarts. The poison
    clause covers EVERY crash mode on every ledger: a checkpointed poison either is still read as
    poisoned after the crash, or the host has failed closed. -/
theorem ceremony_multi_ledger_crash_interleaving_safe
    (policyCap : Nat) (trace : List MultiLedgerEvent) (finalState : MultiLedgerHostState)
    (hTrace : ValidMultiLedgerTrace (initMultiLedgerHostState policyCap) trace finalState) :
    (∀ e₁ ∈ finalState.outboundWire, ∀ e₂ ∈ finalState.outboundWire,
      e₁.ceremonyId ≠ e₂.ceremonyId → e₁.batchIdx ≠ e₂.batchIdx) ∧
    (∀ e₁ ∈ finalState.outboundWire, ∀ e₂ ∈ finalState.outboundWire,
      e₁.epochOrIndex = e₂.epochOrIndex →
      e₁.msgDigest = e₂.msgDigest ∧ e₁.ceremonyId = e₂.ceremonyId) ∧
    (∀ win : Nat, wireWindowSpend win finalState.outboundWire ≤ policyCap) ∧
    (hostOperational finalState = true →
      (checkpointedWalPayload finalState.poisonLatch).status ≠ .clean →
      ∀ cPoison cPolicy cPreproc cLeaf,
        stepMultiLedgerHost finalState (.PowerLossCrash cPoison cPolicy cPreproc cLeaf) =
          some (crashHostState finalState cPoison cPolicy cPreproc cLeaf) ∧
        (hostOperational (crashHostState finalState cPoison cPolicy cPreproc cLeaf) = false ∨
         (activeWalPayload
            (crashHostState finalState cPoison cPolicy cPreproc cLeaf).poisonLatch).status ≠
              .clean)) := by
  have hInv := validMultiLedgerTrace_preserves_crashInv
    (initMultiLedgerHostState_crashInv policyCap) hTrace
  refine ⟨hInv.wire_safe.batch_disjoint, hInv.wire_safe.leaf_unique, hInv.wire_safe.spend_le, ?_⟩
  intro hOp hPoisoned cPoison cPolicy cPreproc cLeaf
  refine ⟨rfl, ?_⟩
  rcases hInv.live_or_dead with hG | hD
  · rcases crashRecoverWal_inv poisonRel_refl hG.poison_wal cPoison with hDead | ⟨hPo, hRel⟩
    · exact Or.inl (by simp [hostOperational, crashHostState, hDead])
    · exact Or.inr ((walInv_facts poisonRel_refl hPo).2.2.2.1 (hRel.1 hPoisoned))
  · rw [hD.notOperational] at hOp
    cases hOp

/-- **Fail-Closed Is Absorbing (`failed_closed_host_stays_closed`)**:
    Once some ledger no longer opens, NO continuation of the trace (any events, any further
    crashes, any crash modes) reopens the host or adds a single emission to the wire. -/
theorem failed_closed_host_stays_closed
    {s s' : MultiLedgerHostState} {trace : List MultiLedgerEvent}
    (hTrace : ValidMultiLedgerTrace s trace s') (hDead : HostFailedClosed s) :
    HostFailedClosed s' ∧ s'.outboundWire = s.outboundWire := by
  induction hTrace with
  | nil _ => exact ⟨hDead, rfl⟩
  | cons hStep _ ih =>
    rcases stepMultiLedgerHost_cases hStep with ⟨a, b, c, d, _, rfl⟩ | ⟨hOp, _⟩
    · exact ih (crashHostState_failedClosed hDead a b c d)
    · rw [hDead.notOperational] at hOp
      cases hOp

/-! ### Buggy Release Machines & `#tooth` Counterexamples -/

/-- Multi-step execution of an arbitrary host step function. -/
def runTraceWith (step : MultiLedgerHostState → MultiLedgerEvent → Option MultiLedgerHostState) :
    MultiLedgerHostState → List MultiLedgerEvent → Option MultiLedgerHostState
  | s, [] => some s
  | s, ev :: rest =>
    match step s ev with
    | none => none
    | some s' => runTraceWith step s' rest

/-- Broken variant of `stepMultiLedgerHost` that swaps step (4) (`FlushLeafWal`) AFTER
    `EmitNetworkShare`, permitting share transmission as soon as `StageLeafOrFtsReserve` is
    buffered in volatile RAM prior to durable disk flush. -/
def stepBuggyReleaseBeforeLeafFlush (host : MultiLedgerHostState) (ev : MultiLedgerEvent) :
    Option MultiLedgerHostState :=
  match ev with
  | .EmitNetworkShare cid party share =>
    match lookupVolatilePhase cid host.volatileCeremonies with
    | some (.leafStaged _ _ _ win amount _ batchIdx epochOrIndex msgDigest) =>
      let emitted : WireEmission := {
        ceremonyId := cid
        windowId := win
        amount := amount
        batchIdx := batchIdx
        epochOrIndex := epochOrIndex
        msgDigest := msgDigest
        party := party
        share := share
      }
      some { host with outboundWire := host.outboundWire ++ [emitted] }
    | _ => stepMultiLedgerHost host ev
  | _ => stepMultiLedgerHost host ev

private def buggyDoubleSignAttackTrace : List MultiLedgerEvent := [
  .ObserveCleanPoisonLatch 1,
  .StagePolicySpend 1 30 (BitVec.ofNat 256 0x1111),
  .FlushPolicyWal 1,
  .StagePreprocBurn 1 0,
  .FlushPreprocWal 1,
  .StageLeafOrFtsReserve 1 7 (BitVec.ofNat 256 0xAA01),
  .EmitNetworkShare 1 0 (BitVec.ofNat 256 0x5001),
  .PowerLossCrash .dropVolatile .dropVolatile .dropVolatile .tornInactiveWrite,
  .ObserveCleanPoisonLatch 2,
  .StagePolicySpend 2 40 (BitVec.ofNat 256 0x2222),
  .FlushPolicyWal 2,
  .StagePreprocBurn 2 1,
  .FlushPreprocWal 2,
  .StageLeafOrFtsReserve 2 7 (BitVec.ofNat 256 0xBB02),
  .EmitNetworkShare 2 0 (BitVec.ofNat 256 0x5002)
]

/-- **`#tooth` Counterexample (`tooth_release_before_durable_burn_reuses_leaf`)**:
    Swapping step (4) (`FlushLeafWal` / durable `LeafOrFtsReserved`) after `EmitNetworkShare`
    allows a `PowerLossCrash` (dropping or tearing the uncommitted leaf-burn write while retaining
    prior policy/preprocessing commits) followed by a post-reboot ceremony on a distinct message
    `msg₂ ≠ msg₁` to sign on `OutboundNetworkWire` under the **exact same `epochOrIndex`**! -/
theorem tooth_release_before_durable_burn_reuses_leaf :
    ∃ (trace : List MultiLedgerEvent) (finalState : MultiLedgerHostState)
      (e₁ e₂ : WireEmission),
      runTraceWith stepBuggyReleaseBeforeLeafFlush (initMultiLedgerHostState 100) trace =
        some finalState ∧
      e₁ ∈ finalState.outboundWire ∧
      e₂ ∈ finalState.outboundWire ∧
      e₁.epochOrIndex = e₂.epochOrIndex ∧
      e₁.msgDigest ≠ e₂.msgDigest := by
  cases hRun : runTraceWith stepBuggyReleaseBeforeLeafFlush (initMultiLedgerHostState 100)
      buggyDoubleSignAttackTrace with
  | none =>
    exfalso
    revert hRun
    decide
  | some sFinal =>
    refine ⟨buggyDoubleSignAttackTrace, sFinal,
      { ceremonyId := 1, windowId := 0, amount := 30, batchIdx := 0, epochOrIndex := 7,
        msgDigest := BitVec.ofNat 256 0xAA01, party := 0, share := BitVec.ofNat 256 0x5001 },
      { ceremonyId := 2, windowId := 0, amount := 40, batchIdx := 1, epochOrIndex := 7,
        msgDigest := BitVec.ofNat 256 0xBB02, party := 0, share := BitVec.ofNat 256 0x5002 },
      hRun, ?_, ?_, rfl, by decide⟩
    · decide +revert
    · decide +revert

/-- Broken variant of `stepMultiLedgerHost` whose `EmitNetworkShare` checks the durable receipt
    but NOT `ledgersCheckpointSaved`: reserved material is released while an older snapshot is
    still an acceptable recovery result. -/
def stepBuggyReleaseBeforeCheckpoint (host : MultiLedgerHostState) (ev : MultiLedgerEvent) :
    Option MultiLedgerHostState :=
  match ev with
  | .EmitNetworkShare cid party share =>
    match lookupVolatilePhase cid host.volatileCeremonies with
    | some (.receiptIssued ceremonyReceipt) =>
      if hostOperational host && ceremonyReceiptDurableValid host cid ceremonyReceipt then
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
  | _ => stepMultiLedgerHost host ev

private def uncheckpointedRollbackAttackTrace : List MultiLedgerEvent := [
  .ObserveCleanPoisonLatch 1,
  .StagePolicySpend 1 30 (BitVec.ofNat 256 0x1111),
  .FlushPolicyWal 1,
  .SaveCheckpoint .policy,
  .StagePreprocBurn 1 0,
  .FlushPreprocWal 1,
  .SaveCheckpoint .preproc,
  .StageLeafOrFtsReserve 1 7 (BitVec.ofNat 256 0xAA01),
  .FlushLeafWal 1,
  .EmitNetworkShare 1 0 (BitVec.ofNat 256 0x5001),
  .PowerLossCrash .dropVolatile .dropVolatile .dropVolatile .tornActiveSlot,
  .ObserveCleanPoisonLatch 2,
  .StagePolicySpend 2 40 (BitVec.ofNat 256 0x2222),
  .FlushPolicyWal 2,
  .SaveCheckpoint .policy,
  .StagePreprocBurn 2 1,
  .FlushPreprocWal 2,
  .SaveCheckpoint .preproc,
  .StageLeafOrFtsReserve 2 7 (BitVec.ofNat 256 0xBB02),
  .FlushLeafWal 2,
  .SaveCheckpoint .leaf,
  .EmitNetworkShare 2 0 (BitVec.ofNat 256 0x5002)
]

/-- **`#tooth` Counterexample (`tooth_release_before_checkpoint_rolls_back_leaf`)**:
    The leaf reservation of ceremony 1 is DURABLY flushed before release, yet its external
    checkpoint is not saved. Power loss damages the active leaf slot; recovery legitimately
    accepts the older snapshot (the checkpoint is only a minimum generation), the reservation is
    gone, and a second ceremony signs a distinct message under the **same `epochOrIndex`**. A
    durable flush alone does not make a burn irrevocable. -/
theorem tooth_release_before_checkpoint_rolls_back_leaf :
    ∃ (trace : List MultiLedgerEvent) (finalState : MultiLedgerHostState)
      (e₁ e₂ : WireEmission),
      runTraceWith stepBuggyReleaseBeforeCheckpoint (initMultiLedgerHostState 100) trace =
        some finalState ∧
      e₁ ∈ finalState.outboundWire ∧
      e₂ ∈ finalState.outboundWire ∧
      e₁.epochOrIndex = e₂.epochOrIndex ∧
      e₁.msgDigest ≠ e₂.msgDigest := by
  cases hRun : runTraceWith stepBuggyReleaseBeforeCheckpoint (initMultiLedgerHostState 100)
      uncheckpointedRollbackAttackTrace with
  | none =>
    exfalso
    revert hRun
    decide
  | some sFinal =>
    refine ⟨uncheckpointedRollbackAttackTrace, sFinal,
      { ceremonyId := 1, windowId := 0, amount := 30, batchIdx := 0, epochOrIndex := 7,
        msgDigest := BitVec.ofNat 256 0xAA01, party := 0, share := BitVec.ofNat 256 0x5001 },
      { ceremonyId := 2, windowId := 0, amount := 40, batchIdx := 1, epochOrIndex := 7,
        msgDigest := BitVec.ofNat 256 0xBB02, party := 0, share := BitVec.ofNat 256 0x5002 },
      hRun, ?_, ?_, rfl, by decide⟩
    · decide +revert
    · decide +revert

private theorem validMultiLedgerTrace_of_runTraceWith :
    ∀ (s : MultiLedgerHostState) (evs : List MultiLedgerEvent) (sFinal : MultiLedgerHostState),
      runTraceWith stepMultiLedgerHost s evs = some sFinal →
      ValidMultiLedgerTrace s evs sFinal
  | s, [], sFinal, h => by
    injection h with hEq
    subst hEq
    exact .nil s
  | s, ev :: rest, sFinal, h => by
    unfold runTraceWith at h
    cases hStep : stepMultiLedgerHost s ev with
    | none =>
      rw [hStep] at h
      cases h
    | some sNext =>
      rw [hStep] at h
      exact .cons hStep (validMultiLedgerTrace_of_runTraceWith sNext rest sFinal h)

private def sampleCeremonyPrefix : List MultiLedgerEvent := [
  .ObserveCleanPoisonLatch 10,
  .ObserveCleanPoisonLatch 20,
  .StagePolicySpend 10 25 (BitVec.ofNat 256 101),
  .FlushPolicyWal 10,
  .SaveCheckpoint .policy,
  .StagePreprocBurn 10 0,
  .FlushPreprocWal 10,
  .SaveCheckpoint .preproc,
  .StageLeafOrFtsReserve 10 0 (BitVec.ofNat 256 9001),
  .FlushLeafWal 10,
  .SaveCheckpoint .leaf,
  .EmitNetworkShare 10 0 (BitVec.ofNat 256 7001)
]

private def sampleInterleavedCrashTrace : List MultiLedgerEvent :=
  sampleCeremonyPrefix ++ [
  .StagePolicySpend 20 15 (BitVec.ofNat 256 202),
  .PowerLossCrash .dropVolatile .flushedBeforePowerLoss .dropVolatile .dropVolatile,
  .ObserveCleanPoisonLatch 30,
  .StagePolicySpend 30 30 (BitVec.ofNat 256 303),
  .FlushPolicyWal 30,
  .SaveCheckpoint .policy,
  .StagePreprocBurn 30 1,
  .FlushPreprocWal 30,
  .SaveCheckpoint .preproc,
  .StageLeafOrFtsReserve 30 1 (BitVec.ofNat 256 9003),
  .FlushLeafWal 30,
  .PowerLossCrash .dropVolatile .dropVolatile .dropVolatile .tornActiveSlot,
  .ObserveCleanPoisonLatch 40,
  .StagePolicySpend 40 30 (BitVec.ofNat 256 404),
  .FlushPolicyWal 40,
  .SaveCheckpoint .policy,
  .StagePreprocBurn 40 2,
  .FlushPreprocWal 40,
  .SaveCheckpoint .preproc,
  .StageLeafOrFtsReserve 40 1 (BitVec.ofNat 256 9004),
  .FlushLeafWal 40,
  .SaveCheckpoint .leaf,
  .EmitNetworkShare 40 0 (BitVec.ofNat 256 7004)
]

private def sampleInterleavedFinalState : MultiLedgerHostState :=
  (runTraceWith stepMultiLedgerHost (initMultiLedgerHostState 100) sampleInterleavedCrashTrace).getD
    (initMultiLedgerHostState 100)

/-- Non-vacuous multi-ceremony, multi-crash reachable trace witness: interleaved ceremonies, an
    asymmetric per-file flush at power loss, and loss of the ACTIVE leaf slot holding a flushed but
    un-checkpointed reservation. Recovery rolls the leaf ledger back one generation; the reservation
    was never released, so the host stays operational and legitimately reuses that `epochOrIndex`
    for a later ceremony. Two emissions complete. -/
theorem witness_multi_ledger_crash_trace_inhabited :
    ∃ (trace : List MultiLedgerEvent) (finalState : MultiLedgerHostState),
      ValidMultiLedgerTrace (initMultiLedgerHostState 100) trace finalState ∧
      hostOperational finalState = true ∧
      finalState.outboundWire.length = 2 ∧
      wireWindowSpend 0 finalState.outboundWire = 55 := by
  have hRun : runTraceWith stepMultiLedgerHost (initMultiLedgerHostState 100)
      sampleInterleavedCrashTrace = some sampleInterleavedFinalState := by decide
  have hOp : hostOperational sampleInterleavedFinalState = true := by decide
  have hLen : sampleInterleavedFinalState.outboundWire.length = 2 := by decide
  have hSpend : wireWindowSpend 0 sampleInterleavedFinalState.outboundWire = 55 := by decide
  exact ⟨sampleInterleavedCrashTrace, sampleInterleavedFinalState,
    validMultiLedgerTrace_of_runTraceWith _ _ _ hRun, hOp, hLen, hSpend⟩

private def sampleFailClosedTrace : List MultiLedgerEvent :=
  sampleCeremonyPrefix ++ [
  .PowerLossCrash .dropVolatile .dropVolatile .dropVolatile .tornActiveSlot
]

private def sampleFailClosedFinalState : MultiLedgerHostState :=
  (runTraceWith stepMultiLedgerHost (initMultiLedgerHostState 100) sampleFailClosedTrace).getD
    (initMultiLedgerHostState 100)

/-- Reachable fail-closed witness: after a RELEASED ceremony (leaf checkpoint saved), loss of the
    active leaf slot leaves no snapshot at or above the checkpoint. The host is `HostFailedClosed`,
    refuses to start a new ceremony, and its single emission stays on the wire. -/
theorem witness_torn_checkpointed_leaf_fails_closed :
    ∃ (trace : List MultiLedgerEvent) (finalState : MultiLedgerHostState),
      ValidMultiLedgerTrace (initMultiLedgerHostState 100) trace finalState ∧
      HostFailedClosed finalState ∧
      finalState.outboundWire.length = 1 ∧
      stepMultiLedgerHost finalState (.ObserveCleanPoisonLatch 50) = none := by
  have hRun : runTraceWith stepMultiLedgerHost (initMultiLedgerHostState 100)
      sampleFailClosedTrace = some sampleFailClosedFinalState := by decide
  have hDead : HostFailedClosed sampleFailClosedFinalState :=
    ⟨by decide, by decide, by decide, by decide, by decide⟩
  have hLen : sampleFailClosedFinalState.outboundWire.length = 1 := by decide
  have hRefuse : stepMultiLedgerHost sampleFailClosedFinalState (.ObserveCleanPoisonLatch 50) =
      none := by decide
  exact ⟨sampleFailClosedTrace, sampleFailClosedFinalState,
    validMultiLedgerTrace_of_runTraceWith _ _ _ hRun, hDead, hLen, hRefuse⟩

private def sampleWindowRotationCrashTrace : List MultiLedgerEvent := [
  .AdvancePolicyWindow 1,
  .PowerLossCrash .dropVolatile .tornInactiveWrite .dropVolatile .idleSlotDamaged,
  .AdvancePolicyWindow 1,
  .FlushPolicyWindowWal
]

private def sampleWindowRotationMidState : MultiLedgerHostState :=
  (runTraceWith stepMultiLedgerHost (initMultiLedgerHostState 100)
    (sampleWindowRotationCrashTrace.take 2)).getD (initMultiLedgerHostState 100)

private def sampleWindowRotationFinalState : MultiLedgerHostState :=
  (runTraceWith stepMultiLedgerHost (initMultiLedgerHostState 100)
    sampleWindowRotationCrashTrace).getD (initMultiLedgerHostState 100)

/-- **Crash inside a policy-window rotation.** `AdvancePolicyWindow` only stages the new window;
    `FlushPolicyWindowWal` makes it durable. A power loss between the two that tears the staged
    write (while bit-rot hits the idle slot of the leaf ledger) leaves the host operational in
    the OLD window; repeating the rotation completes it. -/
theorem witness_policy_window_rotation_crash_mid_step :
    ∃ (trace : List MultiLedgerEvent) (midState finalState : MultiLedgerHostState),
      ValidMultiLedgerTrace (initMultiLedgerHostState 100) (trace.take 2) midState ∧
      hostOperational midState = true ∧
      (activeWalPayload midState.policyWindowLedger).currentWindow = 0 ∧
      ValidMultiLedgerTrace (initMultiLedgerHostState 100) trace finalState ∧
      hostOperational finalState = true ∧
      (activeWalPayload finalState.policyWindowLedger).currentWindow = 1 := by
  have hMid : runTraceWith stepMultiLedgerHost (initMultiLedgerHostState 100)
      (sampleWindowRotationCrashTrace.take 2) = some sampleWindowRotationMidState := by decide
  have hRun : runTraceWith stepMultiLedgerHost (initMultiLedgerHostState 100)
      sampleWindowRotationCrashTrace = some sampleWindowRotationFinalState := by decide
  exact ⟨sampleWindowRotationCrashTrace, sampleWindowRotationMidState,
    sampleWindowRotationFinalState,
    validMultiLedgerTrace_of_runTraceWith _ _ _ hMid, by decide, by decide,
    validMultiLedgerTrace_of_runTraceWith _ _ _ hRun, by decide, by decide⟩

/-- The premises of `posix_crash_during_slot_write_refines` are jointly satisfiable: a device
    whose odd slot inode has an in-flight write of an authenticating generation-`1` snapshot,
    and a power loss that tears it. -/
theorem witness_posix_slot_write_crash_inhabited :
    ∃ (L : PosixTwoSlotLayout Unit) (fs crashed : PosixFsState) (wal : TwoSlotWal Unit),
      PosixRefinesWal L fs wal ∧ wal.volatileStage = some (1, ()) ∧
      assocLookup fs.nand.fileBlocks L.oddIno = some [] ∧
      assocLookup fs.kernel.pageCache.dirtyFiles L.oddIno = some [0x01] ∧
      L.slotView [0x01] = some (1, ()) ∧
      ((1 % 2 = 0 ∧ L.oddIno = L.evenIno ∧ L.evenIno = L.oddIno) ∨
       (¬ 1 % 2 = 0 ∧ L.oddIno = L.oddIno ∧ L.evenIno = L.evenIno)) ∧
      assocLookup fs.kernel.pageCache.dirtyFiles L.evenIno = none ∧
      assocLookup fs.driveCache.cachedFiles L.evenIno = none ∧ CrashStep fs crashed :=
  ⟨{ evenIno := 1, oddIno := 2, slotView := fun bs => if bs = [0x01] then some (1, ()) else none },
   { kernel := { pageCache := { dirtyFiles := [(2, [0x01])] } }
     nand := { fileBlocks := [(1, []), (2, [])], nextInode := 3 } },
   _,
   { slotEven := none, slotOdd := none, anchorGen := 0, genesisPayload := (),
     volatileStage := some (1, ()) },
   ⟨fun _ _ => rfl, fun _ _ => rfl⟩, rfl, rfl, rfl, rfl,
   Or.inr ⟨by decide, rfl, rfl⟩, rfl, rfl,
   CrashStep.powerLoss .revertToNand (fun _ => SectorTearMask.dropAllVolatile) _⟩

/-! ## §2. Cut-the-Hash 2-Phase Transcript & Selective-Abort Statistical Independence -/

/-- Constructive modular subtraction `x - y mod Q` on `Fin Q` (`0 < Q`), modeling additive Beaver/BDOZ
    masked wire openings `d_i = x_i - a_i mod Q`. -/
def subModFinQ (Q : Nat) (hQ : 0 < Q) (x y : Fin Q) : Fin Q :=
  ⟨(x.val + Q - y.val) % Q, Nat.mod_lt _ hQ⟩

theorem subModFinQ_involutive (Q : Nat) (hQ : 0 < Q) (x a : Fin Q) :
    subModFinQ Q hQ x (subModFinQ Q hQ x a) = a := by
  apply Fin.ext
  simp only [subModFinQ]
  have hx : x.val < Q := x.isLt
  have ha : a.val < Q := a.isLt
  by_cases hle : a.val ≤ x.val
  · have h1 : (x.val + Q - a.val) % Q = x.val - a.val := by
      have hEq : x.val + Q - a.val = (x.val - a.val) + 1 * Q := by omega
      rw [hEq, Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1]
    have h2 : x.val + Q - (x.val - a.val) = a.val + 1 * Q := by omega
    rw [h2, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt ha
  · have h1 : (x.val + Q - a.val) % Q = x.val + Q - a.val :=
      Nat.mod_eq_of_lt (by omega)
    rw [h1]
    have h2 : x.val + Q - (x.val + Q - a.val) = a.val := by omega
    rw [h2]
    exact Nat.mod_eq_of_lt ha

/-- Uniform Beaver mask bijection over `Fin Q` (`d = x - a mod Q`). -/
@[expose] def maskBijectionFinQ (Q : Nat) (hQ : 0 < Q) (wireSecret : Fin Q) :
    SimpleEquiv (Fin Q) (Fin Q) where
  toFun a := subModFinQ Q hQ wireSecret a
  invFun d := subModFinQ Q hQ wireSecret d
  left_inv a := subModFinQ_involutive Q hQ wireSecret a
  right_inv d := subModFinQ_involutive Q hQ wireSecret d

/-- Uniform XOR Beaver/commitment mask bijection over `BitVec w` (`d = x ^^^ a`). -/
@[expose] def maskBijectionBitVec (w : Nat) (wireSecret : BitVec w) :
    SimpleEquiv (BitVec w) (BitVec w) where
  toFun a := wireSecret ^^^ a
  invFun d := wireSecret ^^^ d
  left_inv a := by bv_xor_cancel
  right_inv d := by bv_xor_cancel

/-- Honest Phase-1 randomness in Cut-the-Hash prior to the `MAC-OK` barrier:
    1. `beaverRingMask : Fin Q` (additive Beaver/BDOZ wire mask `a_i`),
    2. `beaverXorMask : BitVec w` (boolean/sponge Beaver wire mask),
    3. `commitBlindMask : BitVec w` (hiding pad blinding `COMMIT(y_share, mac_share)`). -/
structure HonestPreOpenMasks (Q w : Nat) where
  beaverRingMask : Fin Q
  beaverXorMask : BitVec w
  commitBlindMask : BitVec w
  deriving Repr, DecidableEq

/-- Malicious adversary's complete pre-`OPEN` view in Phase 1 prior to the `MAC-OK` barrier:
    masked Beaver differences `(dRing, dXor)` plus hiding commitment `commitTag` to `(y_share, mac_share)`. -/
structure AdvPreOpenView (Q w : Nat) where
  maskedDiffRing : Fin Q
  maskedDiffXor : BitVec w
  commitTag : BitVec w
  deriving Repr, DecidableEq

/-- Rushing corrupt party. Its Phase-1 contributions are chosen AFTER it has seen the honest
    messages of the same round: `reactToRingOpen` is its input to the boolean layer, picked after
    the honest masked ring opening; `reactToAllOpens` is its complete corrupt contribution (its
    shares, its MAC material, any injected additive error), picked after every honest masked
    opening and before the honest commitment is formed. -/
structure RushingCorruptStrategy (CorruptIn : Type) (Q w : Nat) where
  reactToRingOpen : Fin Q → CorruptIn
  reactToAllOpens : Fin Q → BitVec w → CorruptIn

/-- A non-adaptive corrupt party with one fixed contribution. -/
def RushingCorruptStrategy.const {CorruptIn : Type} {Q w : Nat} (c : CorruptIn) :
    RushingCorruptStrategy CorruptIn Q w where
  reactToRingOpen := fun _ => c
  reactToAllOpens := fun _ _ => c

/-- The corrupt party's complete Phase-1 contribution, replayed from the view it reacted to. -/
def corruptContribution {CorruptIn : Type} {Q w : Nat}
    (adv : RushingCorruptStrategy CorruptIn Q w) (view : AdvPreOpenView Q w) : CorruptIn :=
  adv.reactToAllOpens view.maskedDiffRing view.maskedDiffXor

/-- Parameterized Cut-the-Hash 2-phase signing specification (`Phase 1` masked Beaver + `COMMIT` ->
    `MAC-OK` barrier -> `Phase 2` `OPEN(y_share)` reconstructing `finalSignature sk msg R`).

    - The honest ring wire is opened first and cannot depend on corrupt input; the boolean wire and
      both output shares may depend on what the rushing corrupt party contributed.
    - `commitHiding` is the PERFECT-HIDING hypothesis on the commitment, stated explicitly: for
      every committed pair `(y_share, mac_share)` the map `blind ↦ COMMIT(y_share, mac_share; blind)`
      is a bijection of `BitVec w`, so a uniformly blinded tag is uniform whatever was committed.
      A hash commitment is only computationally hiding and does not inhabit this field.
    - `reconstruct_eq` is correctness of every run that passes the `MAC-OK` barrier, for every
      corrupt contribution (binding of the commitment and soundness of the MAC check are assumed
      here, not derived). -/
structure CutTheHashProtocolSpec (SK Msg Rand CorruptIn : Type) (Q w : Nat) where
  wireRingSecret : SK → Msg → Rand → Fin Q
  wireXorSecret : SK → Msg → Rand → CorruptIn → BitVec w
  yShareHonest : SK → Msg → Rand → CorruptIn → BitVec w
  yShareCorrupt : SK → Msg → Rand → CorruptIn → BitVec w
  macShareHonest : SK → Msg → Rand → CorruptIn → BitVec w
  commitHiding : BitVec w → BitVec w → SimpleEquiv (BitVec w) (BitVec w)
  finalSignature : SK → Msg → Rand → BitVec w
  reconstruct_eq : ∀ sk msg R cIn,
    yShareHonest sk msg R cIn ^^^ yShareCorrupt sk msg R cIn = finalSignature sk msg R

/-- Phase-1 pre-`OPEN` adversary view induced by `(sk, msg, R)`, the rushing strategy `adv` and
    honest masks `m`, in protocol order: honest masked ring opening, corrupt reaction, honest
    masked boolean opening, corrupt reaction, honest blinded commitment. -/
def evalPreOpenView {SK Msg Rand CorruptIn : Type} {Q w : Nat}
    (spec : CutTheHashProtocolSpec SK Msg Rand CorruptIn Q w)
    (sk : SK) (msg : Msg) (R : Rand) (adv : RushingCorruptStrategy CorruptIn Q w) (hQ : 0 < Q)
    (m : HonestPreOpenMasks Q w) : AdvPreOpenView Q w :=
  let dRing := subModFinQ Q hQ (spec.wireRingSecret sk msg R) m.beaverRingMask
  let dXor := spec.wireXorSecret sk msg R (adv.reactToRingOpen dRing) ^^^ m.beaverXorMask
  let cAll := adv.reactToAllOpens dRing dXor
  { maskedDiffRing := dRing
    maskedDiffXor := dXor
    commitTag :=
      (spec.commitHiding (spec.yShareHonest sk msg R cAll)
        (spec.macShareHonest sk msg R cAll)).toFun m.commitBlindMask }

/-- **Uniform Mask Bijection (`maskBijection`)**:
    For EVERY fixed `(sk, msg, R)` and EVERY rushing corrupt strategy `adv`, the Phase-1 transcript
    map `evalPreOpenView` is an explicit `SimpleEquiv` bijection from `HonestPreOpenMasks Q w` onto
    `AdvPreOpenView Q w`. The inverse peels the rounds in order, replaying the adversary's own
    reactions, so the view is uniform and independent of `(sk, finalSignature sk msg R)` even
    though later honest messages depend on adaptively chosen corrupt input. -/
@[expose] def maskBijection {SK Msg Rand CorruptIn : Type} {Q w : Nat}
    (spec : CutTheHashProtocolSpec SK Msg Rand CorruptIn Q w)
    (sk : SK) (msg : Msg) (R : Rand) (adv : RushingCorruptStrategy CorruptIn Q w) (hQ : 0 < Q) :
    SimpleEquiv (HonestPreOpenMasks Q w) (AdvPreOpenView Q w) where
  toFun m := evalPreOpenView spec sk msg R adv hQ m
  invFun v :=
    let cAll := corruptContribution adv v
    { beaverRingMask := subModFinQ Q hQ (spec.wireRingSecret sk msg R) v.maskedDiffRing
      beaverXorMask :=
        spec.wireXorSecret sk msg R (adv.reactToRingOpen v.maskedDiffRing) ^^^ v.maskedDiffXor
      commitBlindMask :=
        (spec.commitHiding (spec.yShareHonest sk msg R cAll)
          (spec.macShareHonest sk msg R cAll)).invFun v.commitTag }
  left_inv m := by
    cases m with
    | mk mr mx mc =>
      have hx : ∀ a : BitVec w, a ^^^ (a ^^^ mx) = mx := fun a => by bv_xor_cancel
      simp only [evalPreOpenView, corruptContribution, subModFinQ_involutive, hx, SimpleEquiv.left_inv]
  right_inv v := by
    cases v with
    | mk vr vx vc =>
      have hx : ∀ a : BitVec w, a ^^^ (a ^^^ vx) = vx := fun a => by bv_xor_cancel
      simp only [evalPreOpenView, corruptContribution, subModFinQ_involutive, hx, SimpleEquiv.right_inv]

/-- Two-phase Cut-the-Hash execution with `MAC-OK` barrier:
    - Phase 1 computes `view := evalPreOpenView ...` against the rushing strategy `adv`.
    - At the `MAC-OK` barrier, if the selective-abort adversary outputs `abortPred view = true`,
      the ceremony halts cleanly (`none`) BEFORE `OPEN(y_share)`.
    - Otherwise (`abortPred view = false`), Phase 2 opens `y_H` and outputs
      `some (y_H ^^^ y_C) = some (finalSignature sk msg R)`. -/
def execCutTheHashWithBarrier {SK Msg Rand CorruptIn : Type} {Q w : Nat}
    (spec : CutTheHashProtocolSpec SK Msg Rand CorruptIn Q w)
    (sk : SK) (msg : Msg) (R : Rand) (adv : RushingCorruptStrategy CorruptIn Q w) (hQ : 0 < Q)
    (m : HonestPreOpenMasks Q w)
    (abortPred : AdvPreOpenView Q w → Bool) : Option (BitVec w) :=
  if abortPred (evalPreOpenView spec sk msg R adv hQ m) then
    none
  else
    some (spec.yShareHonest sk msg R (corruptContribution adv (evalPreOpenView spec sk msg R adv hQ m)) ^^^
      spec.yShareCorrupt sk msg R (corruptContribution adv (evalPreOpenView spec sk msg R adv hQ m)))

/-! ### Constructive Finite Sample-Space Enumerations for `HonestPreOpenMasks` & `AdvPreOpenView` -/

/-- Constructive enumeration of `BitVec w` by `Fin (2 ^ w)`. -/
def enumBitVec (w : Nat) : SimpleEquiv (Fin (2 ^ w)) (BitVec w) where
  toFun i := BitVec.ofNat w i.val
  invFun bv := ⟨bv.toNat, bv.isLt⟩
  left_inv i := by
    apply Fin.ext
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt i.isLt
  right_inv bv := BitVec.eq_of_toNat_eq (by simp)

private theorem prod_idx_lt {n m : Nat} (a : Fin n) (b : Fin m) :
    a.val * m + b.val < n * m := by
  have ha1 : a.val + 1 ≤ n := a.isLt
  have hMul : (a.val + 1) * m ≤ n * m := Nat.mul_le_mul_right m ha1
  rw [Nat.add_mul, Nat.one_mul] at hMul
  have hb : b.val < m := b.isLt
  omega

private theorem div_lt_of_lt_mul {n m k : Nat} (_hm : 0 < m) (hk : k < n * m) :
    k / m < n := by
  by_cases hLt : k / m < n
  · exact hLt
  · exfalso
    have hGe : n ≤ k / m := Nat.le_of_not_lt hLt
    have hMul : n * m ≤ (k / m) * m := Nat.mul_le_mul_right m hGe
    have hDivMod := Nat.div_add_mod k m
    rw [Nat.mul_comm] at hDivMod
    omega

/-- Constructive product enumeration `SimpleEquiv (Fin (n * m)) (A × B)` for `0 < m`. -/
def enumProd {A B : Type} {n m : Nat} (hm : 0 < m)
    (ea : SimpleEquiv (Fin n) A) (eb : SimpleEquiv (Fin m) B) :
    SimpleEquiv (Fin (n * m)) (A × B) where
  toFun k :=
    (ea.toFun ⟨k.val / m, div_lt_of_lt_mul hm k.isLt⟩,
     eb.toFun ⟨k.val % m, Nat.mod_lt k.val hm⟩)
  invFun p :=
    ⟨(ea.invFun p.1).val * m + (eb.invFun p.2).val, prod_idx_lt (ea.invFun p.1) (eb.invFun p.2)⟩
  left_inv k := by
    simp only [ea.left_inv, eb.left_inv]
    apply Fin.ext
    have hDivMod := Nat.div_add_mod k.val m
    rw [Nat.mul_comm] at hDivMod
    exact hDivMod
  right_inv p := by
    rcases p with ⟨a, b⟩
    let ia := ea.invFun a
    let ib := eb.invFun b
    have hComm : ia.val * m + ib.val = ib.val + m * ia.val := by
      rw [Nat.mul_comm ia.val m, Nat.add_comm]
    have hDiv : (ia.val * m + ib.val) / m = ia.val := by
      rw [hComm, Nat.add_mul_div_left ib.val ia.val hm, Nat.div_eq_of_lt ib.isLt, Nat.zero_add]
    have hMod : (ia.val * m + ib.val) % m = ib.val := by
      rw [hComm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ib.isLt]
    have hFst : (⟨(ia.val * m + ib.val) / m, div_lt_of_lt_mul hm (prod_idx_lt ia ib)⟩ : Fin n) = ia :=
      Fin.ext hDiv
    have hSnd : (⟨(ia.val * m + ib.val) % m, Nat.mod_lt _ hm⟩ : Fin m) = ib :=
      Fin.ext hMod
    exact Prod.ext
      (by change ea.toFun _ = a; rw [hFst]; exact ea.right_inv a)
      (by change eb.toFun _ = b; rw [hSnd]; exact eb.right_inv b)

/-- Total mask-space cardinality `Q * 2^w * 2^w`. -/
abbrev preOpenMaskCard (Q w : Nat) : Nat := Q * 2 ^ w * 2 ^ w

/-- Constructive enumeration of `HonestPreOpenMasks Q w`. -/
def enumHonestPreOpenMasks (Q w : Nat) :
    SimpleEquiv (Fin (preOpenMaskCard Q w)) (HonestPreOpenMasks Q w) :=
  let eqv12 := enumProd (Nat.two_pow_pos w)
    { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    (enumBitVec w)
  let eqv123 := enumProd (Nat.two_pow_pos w) eqv12 (enumBitVec w)
  { toFun := fun k =>
      let ((mr, mx), mc) := eqv123.toFun k
      ⟨mr, mx, mc⟩
    invFun := fun ⟨mr, mx, mc⟩ => eqv123.invFun ((mr, mx), mc)
    left_inv := fun k => eqv123.left_inv k
    right_inv := fun ⟨mr, mx, mc⟩ => by
      have h := eqv123.right_inv ((mr, mx), mc)
      exact congrArg (fun p => HonestPreOpenMasks.mk p.1.1 p.1.2 p.2) h }

/-- Constructive enumeration of `AdvPreOpenView Q w`. -/
def enumAdvPreOpenViews (Q w : Nat) :
    SimpleEquiv (Fin (preOpenMaskCard Q w)) (AdvPreOpenView Q w) :=
  let base := enumHonestPreOpenMasks Q w
  { toFun := fun k =>
      let m := base.toFun k
      ⟨m.beaverRingMask, m.beaverXorMask, m.commitBlindMask⟩
    invFun := fun v => base.invFun ⟨v.maskedDiffRing, v.maskedDiffXor, v.commitTag⟩
    left_inv := fun k => base.left_inv k
    right_inv := fun ⟨vr, vx, vc⟩ => by
      have h := base.right_inv ⟨vr, vx, vc⟩
      exact congrArg (fun m => AdvPreOpenView.mk m.beaverRingMask m.beaverXorMask m.commitBlindMask) h }

/-- Secret-independent count of pre-`OPEN` views accepted (`abortPred v = false`) by the adversary. -/
def viewMaskSurviveCount {Q w : Nat} (abortPred : AdvPreOpenView Q w → Bool) : Nat :=
  qsum (preOpenMaskCard Q w) (fun idx =>
    if abortPred ((enumAdvPreOpenViews Q w).toFun idx) then 0 else 1)

/-- Standalone FIPS 205 / Baggy / Jorts / QS-B signature output count over randomizer space `Fin cardR`. -/
def idealStandaloneSigCount {SK Msg Rand CorruptIn : Type} {Q w : Nat}
    (spec : CutTheHashProtocolSpec SK Msg Rand CorruptIn Q w)
    (sk : SK) (msg : Msg) (cardR : Nat) (decodeRand : Fin cardR → Rand)
    (targetSig : BitVec w) : Nat :=
  qsum cardR (fun rIdx =>
    if spec.finalSignature sk msg (decodeRand rIdx) = targetSig then 1 else 0)

/-- Surviving emitted signature count for `targetSig` under selective abort `abortPred`. -/
def survivingRealSigCount {SK Msg Rand CorruptIn : Type} {Q w : Nat}
    (spec : CutTheHashProtocolSpec SK Msg Rand CorruptIn Q w)
    (sk : SK) (msg : Msg) (cardR : Nat) (decodeRand : Fin cardR → Rand)
    (adv : RushingCorruptStrategy CorruptIn Q w) (hQ : 0 < Q)
    (abortPred : AdvPreOpenView Q w → Bool) (targetSig : BitVec w) : Nat :=
  qsum cardR (fun rIdx =>
    qsum (preOpenMaskCard Q w) (fun mIdx =>
      if execCutTheHashWithBarrier spec sk msg (decodeRand rIdx) adv hQ
          ((enumHonestPreOpenMasks Q w).toFun mIdx) abortPred = some targetSig then 1 else 0))

/-- Constructive `{0, 1}` indicator of `Option.isSome` avoiding per-declaration `_match` duplication. -/
def optSomeIndicator {α : Type} : Option α → Nat
  | some _ => 1
  | none => 0

/-- Total non-aborted executions across `(Fin cardR × Fin (preOpenMaskCard Q w))`. -/
def totalSurvivingRuns {SK Msg Rand CorruptIn : Type} {Q w : Nat}
    (spec : CutTheHashProtocolSpec SK Msg Rand CorruptIn Q w)
    (sk : SK) (msg : Msg) (cardR : Nat) (decodeRand : Fin cardR → Rand)
    (adv : RushingCorruptStrategy CorruptIn Q w) (hQ : 0 < Q)
    (abortPred : AdvPreOpenView Q w → Bool) : Nat :=
  qsum cardR (fun rIdx =>
    qsum (preOpenMaskCard Q w) (fun mIdx =>
      optSomeIndicator (execCutTheHashWithBarrier spec sk msg (decodeRand rIdx) adv hQ
        ((enumHonestPreOpenMasks Q w).toFun mIdx) abortPred)))

/-- Cross-multiplied L1 statistical distance numerator over all `2^w` possible `w`-bit signatures
    comparing the abort-conditioned surviving Cut-the-Hash output distribution against the
    standalone signer. -/
def abortConditionedStatDistNum {SK Msg Rand CorruptIn : Type} {Q w : Nat}
    (spec : CutTheHashProtocolSpec SK Msg Rand CorruptIn Q w)
    (sk : SK) (msg : Msg) (cardR : Nat) (decodeRand : Fin cardR → Rand)
    (adv : RushingCorruptStrategy CorruptIn Q w) (hQ : 0 < Q)
    (abortPred : AdvPreOpenView Q w → Bool) : Nat :=
  let totalSurv := totalSurvivingRuns spec sk msg cardR decodeRand adv hQ abortPred
  qsum (2 ^ w) (fun sIdx =>
    let sig := (enumBitVec w).toFun sIdx
    natAbsDiff
      (survivingRealSigCount spec sk msg cardR decodeRand adv hQ abortPred sig * cardR)
      (idealStandaloneSigCount spec sk msg cardR decodeRand sig * totalSurv))

private theorem qsum_two (f : Fin 2 → Nat) :
    qsum 2 f = f ⟨0, Nat.zero_lt_succ 1⟩ + f ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩ := by
  simp [qsum]

private theorem natAbsDiff_zero_left (n : Nat) : natAbsDiff 0 n = n := by
  simp [natAbsDiff_eq]

private theorem optSomeIndicator_ite {α : Type} (b : Bool) (x : α) :
    optSomeIndicator (if b then none else some x) = if b then 0 else 1 := by
  cases b <;> rfl

private theorem indicator_ite_none_some {α : Type} [DecidableEq α] (b : Bool) (x y : α) :
    (if (if b then none else some x) = some y then 1 else 0) =
      if b then 0 else (if x = y then 1 else 0) := by
  cases b
  · change (if (some x : Option α) = some y then 1 else 0) = if x = y then 1 else 0
    by_cases h : x = y
    · subst h; simp only [↓reduceIte]
    · have hNe : (some x : Option α) ≠ some y := fun he => h (Option.some.inj he)
      simp only [hNe, h, ↓reduceIte]
  · rfl

private theorem preOpenView_sum_invariant {SK Msg Rand CorruptIn : Type} {Q w : Nat}
    (spec : CutTheHashProtocolSpec SK Msg Rand CorruptIn Q w)
    (sk : SK) (msg : Msg) (R : Rand) (adv : RushingCorruptStrategy CorruptIn Q w) (hQ : 0 < Q)
    (weight : AdvPreOpenView Q w → Nat) :
    qsum (preOpenMaskCard Q w) (fun mIdx =>
      weight (evalPreOpenView spec sk msg R adv hQ ((enumHonestPreOpenMasks Q w).toFun mIdx))) =
    qsum (preOpenMaskCard Q w) (fun vIdx =>
      weight ((enumAdvPreOpenViews Q w).toFun vIdx)) := by
  let bij := maskBijection spec sk msg R adv hQ
  let enumM := enumHonestPreOpenMasks Q w
  let enumV := enumAdvPreOpenViews Q w
  let π : Fin (preOpenMaskCard Q w) → Fin (preOpenMaskCard Q w) :=
    fun mIdx => enumV.invFun (bij.toFun (enumM.toFun mIdx))
  let πinv : Fin (preOpenMaskCard Q w) → Fin (preOpenMaskCard Q w) :=
    fun vIdx => enumM.invFun (bij.invFun (enumV.toFun vIdx))
  have hPerm := qsum_perm_invariant π πinv
    (fun i => by simp [π, πinv, enumV.right_inv, bij.left_inv, enumM.left_inv])
    (fun j => by simp [π, πinv, enumM.right_inv, bij.right_inv, enumV.left_inv])
    (fun vIdx => weight (enumV.toFun vIdx))
  have hCong :
      qsum (preOpenMaskCard Q w) (fun mIdx =>
        weight (evalPreOpenView spec sk msg R adv hQ (enumM.toFun mIdx))) =
      qsum (preOpenMaskCard Q w) (fun i => weight (enumV.toFun (π i))) := by
    apply qsum_congr
    intro i
    dsimp only [π, bij, maskBijection]
    rw [enumV.right_inv]
  exact hCong.trans hPerm

/-- **Exact Fiber Uniformity of Pre-`OPEN` View**:
    For every `(sk, msg, R)`, every rushing corrupt strategy `adv` and every target
    `targetView : AdvPreOpenView Q w`, there is
    exact honest-mask multiplicity `1` producing `targetView`, completely independent of
    `(sk, finalSignature sk msg R)`. -/
theorem preOpenView_exact_fiber_one {SK Msg Rand CorruptIn : Type} {Q w : Nat}
    (spec : CutTheHashProtocolSpec SK Msg Rand CorruptIn Q w)
    (sk : SK) (msg : Msg) (R : Rand) (adv : RushingCorruptStrategy CorruptIn Q w) (hQ : 0 < Q)
    (targetView : AdvPreOpenView Q w) :
    qsum (preOpenMaskCard Q w) (fun mIdx =>
      if evalPreOpenView spec sk msg R adv hQ ((enumHonestPreOpenMasks Q w).toFun mIdx) = targetView
      then 1 else 0) = 1 := by
  rw [preOpenView_sum_invariant spec sk msg R adv hQ (fun v => if v = targetView then 1 else 0)]
  let enumV := enumAdvPreOpenViews Q w
  let iStar := enumV.invFun targetView
  have hCongr :
      qsum (preOpenMaskCard Q w) (fun vIdx => if enumV.toFun vIdx = targetView then 1 else 0) =
      qsum (preOpenMaskCard Q w) (fun vIdx => if vIdx = iStar then 1 else 0) := by
    apply qsum_congr
    intro vIdx
    by_cases hEq : vIdx = iStar
    · subst hEq
      simp [iStar, enumV.right_inv]
    · have hNeV : enumV.toFun vIdx ≠ targetView := by
        intro hv
        apply hEq
        have := congrArg enumV.invFun hv
        simpa [iStar, enumV.left_inv] using this
      simp [hEq, hNeV]
  rw [hCongr, qsum_eq_indicator]

/-- Total surviving executions factor unconditionally as `cardR * viewMaskSurviveCount abortPred`. -/
theorem totalSurvivingRuns_eq {SK Msg Rand CorruptIn : Type} {Q w : Nat}
    (spec : CutTheHashProtocolSpec SK Msg Rand CorruptIn Q w)
    (sk : SK) (msg : Msg) (cardR : Nat) (decodeRand : Fin cardR → Rand)
    (adv : RushingCorruptStrategy CorruptIn Q w) (hQ : 0 < Q)
    (abortPred : AdvPreOpenView Q w → Bool) :
    totalSurvivingRuns spec sk msg cardR decodeRand adv hQ abortPred =
      cardR * viewMaskSurviveCount abortPred := by
  have hInnerSurv : ∀ rIdx : Fin cardR,
      qsum (preOpenMaskCard Q w) (fun mIdx =>
        optSomeIndicator (execCutTheHashWithBarrier spec sk msg (decodeRand rIdx) adv hQ
          ((enumHonestPreOpenMasks Q w).toFun mIdx) abortPred)) = viewMaskSurviveCount abortPred := by
    intro rIdx
    have hPoint :
        qsum (preOpenMaskCard Q w) (fun mIdx =>
          optSomeIndicator (execCutTheHashWithBarrier spec sk msg (decodeRand rIdx) adv hQ
            ((enumHonestPreOpenMasks Q w).toFun mIdx) abortPred)) =
        qsum (preOpenMaskCard Q w) (fun mIdx =>
          if abortPred (evalPreOpenView spec sk msg (decodeRand rIdx) adv hQ
              ((enumHonestPreOpenMasks Q w).toFun mIdx)) then 0 else 1) := by
      apply qsum_congr
      intro mIdx
      unfold execCutTheHashWithBarrier
      exact optSomeIndicator_ite _ _
    rw [hPoint]
    exact preOpenView_sum_invariant spec sk msg (decodeRand rIdx) adv hQ
      (fun v => if abortPred v then 0 else 1)
  unfold totalSurvivingRuns
  rw [qsum_congr hInnerSurv, qsum_const]

/-- Positive survival-count precondition (`0 < totalSurvivingRuns ...`) for selective-abort
    conditioning. -/
abbrev NonZeroSurvivingRuns {SK Msg Rand CorruptIn : Type} {Q w : Nat}
    (spec : CutTheHashProtocolSpec SK Msg Rand CorruptIn Q w)
    (sk : SK) (msg : Msg) (cardR : Nat) (decodeRand : Fin cardR → Rand)
    (adv : RushingCorruptStrategy CorruptIn Q w) (hQ : 0 < Q)
    (abortPred : AdvPreOpenView Q w → Bool) : Prop :=
  0 < totalSurvivingRuns spec sk msg cardR decodeRand adv hQ abortPred

/-- **Selective-Abort Statistical Independence for Cut-the-Hash
    (`cutTheHash_abort_conditioned_sd_zero`)**:
    For EVERY fixed secret key `sk`, message `msg`, rushing corrupt strategy `adv` (corrupt
    contributions chosen adaptively from the honest Phase-1 openings), randomizer space
    `decodeRand : Fin cardR → Rand`, and ANY malicious pre-`OPEN` selective-abort predicate
    `abortPred : AdvPreOpenView Q w → Bool` with non-zero survival count (`0 < totalSurvive`):
    1. Pre-`OPEN` mask survival count per randomizer `R` is `viewMaskSurviveCount abortPred`,
       independent of `(sk, msg, R)`.
    2. Total surviving runs factor cleanly as `totalSurvive = cardR * viewMaskSurviveCount abortPred`.
    3. For every `targetSig : BitVec w`, cross-multiplied conditional probability matches the
       standalone FIPS 205 / Baggy / Jorts / QS-B signer **with zero bias**:
       `survivingRealSigCount ... targetSig * cardR = idealStandaloneSigCount ... targetSig * totalSurvive`.
    4. Exact L1 statistical distance numerator across all `2^w` signatures is identically `0`:
       `abortConditionedStatDistNum ... = 0`. -/
theorem cutTheHash_abort_conditioned_sd_zero {SK Msg Rand CorruptIn : Type} {Q w : Nat}
    (spec : CutTheHashProtocolSpec SK Msg Rand CorruptIn Q w)
    (sk : SK) (msg : Msg) (cardR : Nat) (decodeRand : Fin cardR → Rand)
    (adv : RushingCorruptStrategy CorruptIn Q w) (hQ : 0 < Q)
    (abortPred : AdvPreOpenView Q w → Bool)
    (hSurvivePos : NonZeroSurvivingRuns spec sk msg cardR decodeRand adv hQ abortPred) :
    let totalSurvive := totalSurvivingRuns spec sk msg cardR decodeRand adv hQ abortPred
    (0 < cardR ∧ 0 < viewMaskSurviveCount abortPred) ∧
    totalSurvive = cardR * viewMaskSurviveCount abortPred ∧
    (∀ targetSig : BitVec w,
      survivingRealSigCount spec sk msg cardR decodeRand adv hQ abortPred targetSig * cardR =
        idealStandaloneSigCount spec sk msg cardR decodeRand targetSig * totalSurvive) ∧
    abortConditionedStatDistNum spec sk msg cardR decodeRand adv hQ abortPred = 0 := by
  intro totalSurvive
  have hTotalEq : totalSurvive = cardR * viewMaskSurviveCount abortPred :=
    totalSurvivingRuns_eq spec sk msg cardR decodeRand adv hQ abortPred
  have hPosBoth : 0 < cardR ∧ 0 < viewMaskSurviveCount abortPred := by
    have hPosProd : 0 < cardR * viewMaskSurviveCount abortPred := by
      simpa [totalSurvive, hTotalEq] using hSurvivePos
    refine ⟨?_, ?_⟩
    · cases cardR with
      | zero => simp at hPosProd
      | succ k => exact Nat.zero_lt_succ k
    · cases hv : viewMaskSurviveCount abortPred with
      | zero => rw [hv, Nat.mul_zero] at hPosProd; exact False.elim (Nat.lt_irrefl 0 hPosProd)
      | succ k => exact Nat.zero_lt_succ k
  have hSigFactor : ∀ targetSig : BitVec w,
      survivingRealSigCount spec sk msg cardR decodeRand adv hQ abortPred targetSig =
        idealStandaloneSigCount spec sk msg cardR decodeRand targetSig * viewMaskSurviveCount abortPred := by
    intro targetSig
    unfold survivingRealSigCount
    have hPerR : ∀ rIdx : Fin cardR,
        qsum (preOpenMaskCard Q w) (fun mIdx =>
          if execCutTheHashWithBarrier spec sk msg (decodeRand rIdx) adv hQ
              ((enumHonestPreOpenMasks Q w).toFun mIdx) abortPred = some targetSig then 1 else 0) =
        (if spec.finalSignature sk msg (decodeRand rIdx) = targetSig then 1 else 0) *
          viewMaskSurviveCount abortPred := by
      intro rIdx
      have hRec := spec.reconstruct_eq sk msg (decodeRand rIdx)
      by_cases hMatch : spec.finalSignature sk msg (decodeRand rIdx) = targetSig
      · simp only [hMatch, ↓reduceIte, Nat.one_mul]
        have hEqSurv :
            qsum (preOpenMaskCard Q w) (fun mIdx =>
              if execCutTheHashWithBarrier spec sk msg (decodeRand rIdx) adv hQ
                  ((enumHonestPreOpenMasks Q w).toFun mIdx) abortPred = some targetSig then 1 else 0) =
            qsum (preOpenMaskCard Q w) (fun mIdx =>
              if abortPred (evalPreOpenView spec sk msg (decodeRand rIdx) adv hQ
                  ((enumHonestPreOpenMasks Q w).toFun mIdx)) then 0 else 1) := by
          apply qsum_congr
          intro mIdx
          unfold execCutTheHashWithBarrier
          rw [hRec, hMatch, indicator_ite_none_some]
          simp only [↓reduceIte]
        rw [hEqSurv]
        exact preOpenView_sum_invariant spec sk msg (decodeRand rIdx) adv hQ
          (fun v => if abortPred v then 0 else 1)
      · simp only [hMatch, ↓reduceIte, Nat.zero_mul]
        have hZero :
            qsum (preOpenMaskCard Q w) (fun mIdx =>
              if execCutTheHashWithBarrier spec sk msg (decodeRand rIdx) adv hQ
                  ((enumHonestPreOpenMasks Q w).toFun mIdx) abortPred = some targetSig then 1 else 0) =
            qsum (preOpenMaskCard Q w) (fun _ => 0) := by
          apply qsum_congr
          intro mIdx
          unfold execCutTheHashWithBarrier
          rw [hRec, indicator_ite_none_some]
          simp only [hMatch, ↓reduceIte]
          cases abortPred (evalPreOpenView spec sk msg (decodeRand rIdx) adv hQ ((enumHonestPreOpenMasks Q w).toFun mIdx)) <;> rfl
        rw [hZero, qsum_const, Nat.mul_zero]
    rw [qsum_congr hPerR, qsum_mul_right]
    rfl
  have hCrossEq : ∀ targetSig : BitVec w,
      survivingRealSigCount spec sk msg cardR decodeRand adv hQ abortPred targetSig * cardR =
        idealStandaloneSigCount spec sk msg cardR decodeRand targetSig * totalSurvive := by
    intro targetSig
    rw [hSigFactor targetSig, hTotalEq]
    rw [Nat.mul_assoc, Nat.mul_comm (viewMaskSurviveCount abortPred) cardR, ← Nat.mul_assoc]
  refine ⟨hPosBoth, hTotalEq, hCrossEq, ?_⟩
  unfold abortConditionedStatDistNum
  dsimp only
  have hAllZero :
      qsum (2 ^ w) (fun sIdx =>
        let sig := (enumBitVec w).toFun sIdx
        natAbsDiff
          (survivingRealSigCount spec sk msg cardR decodeRand adv hQ abortPred sig * cardR)
          (idealStandaloneSigCount spec sk msg cardR decodeRand sig * totalSurvive)) =
      qsum (2 ^ w) (fun _ => 0) := by
    apply qsum_congr
    intro sIdx
    dsimp only
    rw [hCrossEq ((enumBitVec w).toFun sIdx)]
    simp [natAbsDiff_eq]
  rw [hAllZero, qsum_const, Nat.mul_zero]

/-! ### Leaky Pre-`OPEN` Protocols & `#tooth` Distribution-Skew Witnesses -/

/-- Adversary view in a broken protocol that hands the corrupt party one extra `w`-bit word
    correlated with the honest output share BEFORE the `MAC-OK` barrier. -/
structure LeakyPreOpenView (Q w : Nat) where
  preOpen : AdvPreOpenView Q w
  leakedWord : BitVec w
  deriving Repr, DecidableEq

/-- Leak (a): Party 0 opens `y_0` itself before the `MAC-OK` barrier. -/
def earlyOpenLeak {SK Msg Rand CorruptIn : Type} {Q w : Nat}
    (spec : CutTheHashProtocolSpec SK Msg Rand CorruptIn Q w) :
    SK → Msg → Rand → CorruptIn → BitVec w :=
  spec.yShareHonest

/-- Leak (b): the Phase-1 commitment goes out WITHOUT its blinding mask, so the tag is a
    deterministic function `body` of the committed pair `(y_share, mac_share)`. -/
def unblindedCommitLeak {SK Msg Rand CorruptIn : Type} {Q w : Nat}
    (spec : CutTheHashProtocolSpec SK Msg Rand CorruptIn Q w)
    (body : BitVec w → BitVec w → BitVec w) :
    SK → Msg → Rand → CorruptIn → BitVec w :=
  fun sk msg R cIn => body (spec.yShareHonest sk msg R cIn) (spec.macShareHonest sk msg R cIn)

/-- Execution of a leaky protocol: the corrupt party additionally sees `leak sk msg R cAll`
    before deciding whether to abort. -/
def execLeakyPreOpen {SK Msg Rand CorruptIn : Type} {Q w : Nat}
    (spec : CutTheHashProtocolSpec SK Msg Rand CorruptIn Q w)
    (sk : SK) (msg : Msg) (R : Rand) (adv : RushingCorruptStrategy CorruptIn Q w) (hQ : 0 < Q)
    (m : HonestPreOpenMasks Q w)
    (leak : SK → Msg → Rand → CorruptIn → BitVec w)
    (leakyAbortPred : LeakyPreOpenView Q w → Bool) : Option (BitVec w) :=
  if leakyAbortPred
      { preOpen := evalPreOpenView spec sk msg R adv hQ m
        leakedWord := leak sk msg R (corruptContribution adv (evalPreOpenView spec sk msg R adv hQ m)) }
  then
    none
  else
    some (spec.yShareHonest sk msg R (corruptContribution adv (evalPreOpenView spec sk msg R adv hQ m)) ^^^
      spec.yShareCorrupt sk msg R (corruptContribution adv (evalPreOpenView spec sk msg R adv hQ m)))

/-- Total surviving executions of a leaky protocol. -/
def leakyTotalSurvivingRuns {SK Msg Rand CorruptIn : Type} {Q w : Nat}
    (spec : CutTheHashProtocolSpec SK Msg Rand CorruptIn Q w)
    (sk : SK) (msg : Msg) (cardR : Nat) (decodeRand : Fin cardR → Rand)
    (adv : RushingCorruptStrategy CorruptIn Q w) (hQ : 0 < Q)
    (leak : SK → Msg → Rand → CorruptIn → BitVec w)
    (leakyAbortPred : LeakyPreOpenView Q w → Bool) : Nat :=
  qsum cardR (fun rIdx =>
    qsum (preOpenMaskCard Q w) (fun mIdx =>
      optSomeIndicator (execLeakyPreOpen spec sk msg (decodeRand rIdx) adv hQ
        ((enumHonestPreOpenMasks Q w).toFun mIdx) leak leakyAbortPred)))

/-- Surviving signature count for `targetSig` under a leaky protocol. -/
def leakySurvivingSigCount {SK Msg Rand CorruptIn : Type} {Q w : Nat}
    (spec : CutTheHashProtocolSpec SK Msg Rand CorruptIn Q w)
    (sk : SK) (msg : Msg) (cardR : Nat) (decodeRand : Fin cardR → Rand)
    (adv : RushingCorruptStrategy CorruptIn Q w) (hQ : 0 < Q)
    (leak : SK → Msg → Rand → CorruptIn → BitVec w)
    (leakyAbortPred : LeakyPreOpenView Q w → Bool) (targetSig : BitVec w) : Nat :=
  qsum cardR (fun rIdx =>
    qsum (preOpenMaskCard Q w) (fun mIdx =>
      if execLeakyPreOpen spec sk msg (decodeRand rIdx) adv hQ
          ((enumHonestPreOpenMasks Q w).toFun mIdx) leak leakyAbortPred = some targetSig
      then 1 else 0))

private def concreteSk0 : BitVec 8 := BitVec.ofNat 8 0x42
private def concreteMsg0 : BitVec 8 := BitVec.ofNat 8 0x99
private def concreteCIn0 : BitVec 8 := BitVec.ofNat 8 0x17

private abbrev fin2Zero : Fin 2 := ⟨0, Nat.zero_lt_succ 1⟩
private abbrev fin2One : Fin 2 := ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩

private def toySigOf (r : Fin 2) : BitVec 8 :=
  if r.val = 0 then BitVec.ofNat 8 0 else BitVec.ofNat 8 1

/-- Toy two-signature scheme: the randomizer bit `r` selects the signature; the corrupt share is
    a value the corrupt party itself holds; the MAC share is message-derived. -/
private def toyCutSpec (Q : Nat) (hQ : 0 < Q) :
    CutTheHashProtocolSpec (BitVec 8) (BitVec 8) (Fin 2) (BitVec 8) Q 8 where
  wireRingSecret := fun _ _ r => ⟨r.val % Q, Nat.mod_lt _ hQ⟩
  wireXorSecret := fun sk msg _ cIn => sk ^^^ msg ^^^ cIn
  yShareHonest := fun sk msg r cIn => toySigOf r ^^^ sk ^^^ msg ^^^ cIn
  yShareCorrupt := fun sk msg _ cIn => sk ^^^ msg ^^^ cIn
  macShareHonest := fun _ msg _ _ => msg
  commitHiding := fun y mac => maskBijectionBitVec 8 (y ^^^ mac)
  finalSignature := fun _ _ r => toySigOf r
  reconstruct_eq := fun sk msg r cIn => by bv_xor_cancel

private def toyConstAdv (Q : Nat) : RushingCorruptStrategy (BitVec 8) Q 8 :=
  RushingCorruptStrategy.const concreteCIn0

/-- The corrupt party's own output share in the toy run: a value it knows. -/
private def toyCorruptShare : BitVec 8 := concreteSk0 ^^^ concreteMsg0 ^^^ concreteCIn0

private def toyHonestShare (r : Fin 2) : BitVec 8 :=
  toySigOf r ^^^ concreteSk0 ^^^ concreteMsg0 ^^^ concreteCIn0

/-- Abort whenever bit 0 of `leaked y_0 ^^^ y_C` is set. -/
private def earlyOpenLsbAbortPred {Q : Nat} (v : LeakyPreOpenView Q 8) : Bool :=
  (v.leakedWord ^^^ toyCorruptShare).getLsbD 0

/-- Abort whenever bit 0 of `tag ^^^ mac ^^^ y_C` is set, for the unblinded tag `y_0 ^^^ mac`. -/
private def unblindedTagLsbAbortPred {Q : Nat} (v : LeakyPreOpenView Q 8) : Bool :=
  (v.leakedWord ^^^ concreteMsg0 ^^^ toyCorruptShare).getLsbD 0

private theorem toyEarlyOpen_closed_zero :
    (if ((toyHonestShare fin2Zero) ^^^ toyCorruptShare).getLsbD 0 then none
     else some (toyHonestShare fin2Zero ^^^ toyCorruptShare)) = some (BitVec.ofNat 8 0) := by
  decide

private theorem toyEarlyOpen_closed_one :
    (if ((toyHonestShare fin2One) ^^^ toyCorruptShare).getLsbD 0 then none
     else some (toyHonestShare fin2One ^^^ toyCorruptShare)) = (none : Option (BitVec 8)) := by
  decide

private theorem toyUnblinded_closed_zero :
    (if ((toyHonestShare fin2Zero ^^^ concreteMsg0) ^^^ concreteMsg0 ^^^ toyCorruptShare).getLsbD 0
     then none
     else some (toyHonestShare fin2Zero ^^^ toyCorruptShare)) = some (BitVec.ofNat 8 0) := by
  decide

private theorem toyUnblinded_closed_one :
    (if ((toyHonestShare fin2One ^^^ concreteMsg0) ^^^ concreteMsg0 ^^^ toyCorruptShare).getLsbD 0
     then none
     else some (toyHonestShare fin2One ^^^ toyCorruptShare)) = (none : Option (BitVec 8)) := by
  decide

private theorem toySomeZero_ne_someOne :
    (if (some (BitVec.ofNat 8 0) : Option (BitVec 8)) = some (BitVec.ofNat 8 1) then 1 else 0) =
      0 := by
  decide

private theorem toyIdealOdd_closed :
    ((if toySigOf fin2Zero = BitVec.ofNat 8 1 then 1 else 0) +
     (if toySigOf fin2One = BitVec.ofNat 8 1 then 1 else 0)) = 1 := by
  decide

/-- Any leak that lets the corrupt party keep every `r = 0` run and abort every `r = 1` run skews
    the surviving distribution: signature `1` has ideal weight `1/2` and surviving weight `0`. -/
private theorem toyLeakySkew (Q : Nat) (hQ : 0 < Q)
    (leak : BitVec 8 → BitVec 8 → Fin 2 → BitVec 8 → BitVec 8)
    (pred : LeakyPreOpenView Q 8 → Bool)
    (h0 : ∀ m : HonestPreOpenMasks Q 8,
      execLeakyPreOpen (toyCutSpec Q hQ) concreteSk0 concreteMsg0 fin2Zero (toyConstAdv Q) hQ m
        leak pred = some (BitVec.ofNat 8 0))
    (h1 : ∀ m : HonestPreOpenMasks Q 8,
      execLeakyPreOpen (toyCutSpec Q hQ) concreteSk0 concreteMsg0 fin2One (toyConstAdv Q) hQ m
        leak pred = none) :
    0 < leakyTotalSurvivingRuns (toyCutSpec Q hQ) concreteSk0 concreteMsg0 2 id (toyConstAdv Q) hQ
          leak pred ∧
    0 < natAbsDiff
          (leakySurvivingSigCount (toyCutSpec Q hQ) concreteSk0 concreteMsg0 2 id (toyConstAdv Q) hQ
            leak pred (BitVec.ofNat 8 1) * 2)
          (idealStandaloneSigCount (toyCutSpec Q hQ) concreteSk0 concreteMsg0 2 id
            (BitVec.ofNat 8 1) *
           leakyTotalSurvivingRuns (toyCutSpec Q hQ) concreteSk0 concreteMsg0 2 id (toyConstAdv Q) hQ
             leak pred) := by
  have hCardPos : 0 < preOpenMaskCard Q 8 :=
    Nat.mul_pos (Nat.mul_pos hQ (Nat.two_pow_pos 8)) (Nat.two_pow_pos 8)
  have hSurv0 :
      qsum (preOpenMaskCard Q 8) (fun mIdx =>
        optSomeIndicator (execLeakyPreOpen (toyCutSpec Q hQ) concreteSk0 concreteMsg0
          fin2Zero (toyConstAdv Q) hQ ((enumHonestPreOpenMasks Q 8).toFun mIdx) leak pred)) =
      preOpenMaskCard Q 8 := by
    have hCong :
        qsum (preOpenMaskCard Q 8) (fun mIdx =>
          optSomeIndicator (execLeakyPreOpen (toyCutSpec Q hQ) concreteSk0 concreteMsg0
            fin2Zero (toyConstAdv Q) hQ ((enumHonestPreOpenMasks Q 8).toFun mIdx) leak pred)) =
        qsum (preOpenMaskCard Q 8) (fun _ => 1) := by
      apply qsum_congr
      intro mIdx
      rw [h0]
      rfl
    rw [hCong, qsum_const, Nat.mul_one]
  have hSurv1 :
      qsum (preOpenMaskCard Q 8) (fun mIdx =>
        optSomeIndicator (execLeakyPreOpen (toyCutSpec Q hQ) concreteSk0 concreteMsg0
          fin2One (toyConstAdv Q) hQ ((enumHonestPreOpenMasks Q 8).toFun mIdx) leak pred)) = 0 := by
    have hCong :
        qsum (preOpenMaskCard Q 8) (fun mIdx =>
          optSomeIndicator (execLeakyPreOpen (toyCutSpec Q hQ) concreteSk0 concreteMsg0
            fin2One (toyConstAdv Q) hQ ((enumHonestPreOpenMasks Q 8).toFun mIdx) leak pred)) =
        qsum (preOpenMaskCard Q 8) (fun _ => 0) := by
      apply qsum_congr
      intro mIdx
      rw [h1]
      rfl
    rw [hCong, qsum_const, Nat.mul_zero]
  have hTotal :
      leakyTotalSurvivingRuns (toyCutSpec Q hQ) concreteSk0 concreteMsg0 2 id (toyConstAdv Q) hQ
        leak pred = preOpenMaskCard Q 8 := by
    unfold leakyTotalSurvivingRuns
    rw [qsum_two]
    dsimp only [id]
    rw [hSurv0, hSurv1, Nat.add_zero]
  have hNoneNeOne :
      (if (none : Option (BitVec 8)) = some (BitVec.ofNat 8 1) then 1 else 0) = 0 := rfl
  have hOdd0 :
      qsum (preOpenMaskCard Q 8) (fun mIdx =>
        if execLeakyPreOpen (toyCutSpec Q hQ) concreteSk0 concreteMsg0 fin2Zero (toyConstAdv Q)
            hQ ((enumHonestPreOpenMasks Q 8).toFun mIdx) leak pred = some (BitVec.ofNat 8 1)
        then 1 else 0) = 0 := by
    have hCong :
        qsum (preOpenMaskCard Q 8) (fun mIdx =>
          if execLeakyPreOpen (toyCutSpec Q hQ) concreteSk0 concreteMsg0 fin2Zero (toyConstAdv Q)
              hQ ((enumHonestPreOpenMasks Q 8).toFun mIdx) leak pred = some (BitVec.ofNat 8 1)
          then 1 else 0) =
        qsum (preOpenMaskCard Q 8) (fun _ => 0) := by
      apply qsum_congr
      intro mIdx
      rw [h0]
      exact toySomeZero_ne_someOne
    rw [hCong, qsum_const, Nat.mul_zero]
  have hOdd1 :
      qsum (preOpenMaskCard Q 8) (fun mIdx =>
        if execLeakyPreOpen (toyCutSpec Q hQ) concreteSk0 concreteMsg0 fin2One (toyConstAdv Q)
            hQ ((enumHonestPreOpenMasks Q 8).toFun mIdx) leak pred = some (BitVec.ofNat 8 1)
        then 1 else 0) = 0 := by
    have hCong :
        qsum (preOpenMaskCard Q 8) (fun mIdx =>
          if execLeakyPreOpen (toyCutSpec Q hQ) concreteSk0 concreteMsg0 fin2One (toyConstAdv Q)
              hQ ((enumHonestPreOpenMasks Q 8).toFun mIdx) leak pred = some (BitVec.ofNat 8 1)
          then 1 else 0) =
        qsum (preOpenMaskCard Q 8) (fun _ => 0) := by
      apply qsum_congr
      intro mIdx
      rw [h1]
      exact hNoneNeOne
    rw [hCong, qsum_const, Nat.mul_zero]
  have hLeakyOdd :
      leakySurvivingSigCount (toyCutSpec Q hQ) concreteSk0 concreteMsg0 2 id (toyConstAdv Q) hQ
        leak pred (BitVec.ofNat 8 1) = 0 := by
    unfold leakySurvivingSigCount
    rw [qsum_two]
    dsimp only [id]
    rw [hOdd0, hOdd1]
  have hIdealOdd :
      idealStandaloneSigCount (toyCutSpec Q hQ) concreteSk0 concreteMsg0 2 id
        (BitVec.ofNat 8 1) = 1 := by
    unfold idealStandaloneSigCount
    rw [qsum_two]
    exact toyIdealOdd_closed
  rw [hTotal, hLeakyOdd, hIdealOdd, Nat.zero_mul, Nat.one_mul, natAbsDiff_zero_left]
  exact ⟨hCardPos, hCardPos⟩

/-- **`#tooth` Witness (`tooth_early_open_before_mac_barrier_skews_distribution`)**:
    If Party 0 opens `y_0` BEFORE the `MAC-OK` barrier, a selective-abort adversary (aborting
    whenever bit 0 of `y_0 ^^^ y_1` equals `1`) strictly biases the surviving byte distribution
    away from the standalone signer (`SD > 0`, with non-zero survival count!). -/
theorem tooth_early_open_before_mac_barrier_skews_distribution :
    ∃ (spec : CutTheHashProtocolSpec (BitVec 8) (BitVec 8) (Fin 2) (BitVec 8) 2 8)
      (sk msg : BitVec 8) (adv : RushingCorruptStrategy (BitVec 8) 2 8)
      (earlyAbortPred : LeakyPreOpenView 2 8 → Bool),
      0 < leakyTotalSurvivingRuns spec sk msg 2 id adv (Nat.zero_lt_succ 1)
            (earlyOpenLeak spec) earlyAbortPred ∧
      0 < natAbsDiff
            (leakySurvivingSigCount spec sk msg 2 id adv (Nat.zero_lt_succ 1)
              (earlyOpenLeak spec) earlyAbortPred (BitVec.ofNat 8 1) * 2)
            (idealStandaloneSigCount spec sk msg 2 id (BitVec.ofNat 8 1) *
             leakyTotalSurvivingRuns spec sk msg 2 id adv (Nat.zero_lt_succ 1)
               (earlyOpenLeak spec) earlyAbortPred) :=
  ⟨toyCutSpec 2 (Nat.zero_lt_succ 1), concreteSk0, concreteMsg0, toyConstAdv 2,
    earlyOpenLsbAbortPred,
    toyLeakySkew 2 (Nat.zero_lt_succ 1) (earlyOpenLeak (toyCutSpec 2 (Nat.zero_lt_succ 1)))
      earlyOpenLsbAbortPred (fun _ => toyEarlyOpen_closed_zero) (fun _ => toyEarlyOpen_closed_one)⟩

/-- **`#tooth` Witness (`tooth_unblinded_commit_skews_distribution`)**:
    `commitHiding` is load-bearing. With the SAME honest masks, wires and `MAC-OK` barrier, sending
    the Phase-1 commitment without its blinding mask (tag `= y_0 ^^^ mac_0`, a deterministic
    function of the committed pair) lets a selective-abort adversary strip the public MAC share and
    its own output share, read bit 0 of the signature, and bias the surviving distribution
    (`SD > 0`, with non-zero survival count). -/
theorem tooth_unblinded_commit_skews_distribution :
    ∃ (spec : CutTheHashProtocolSpec (BitVec 8) (BitVec 8) (Fin 2) (BitVec 8) 2 8)
      (sk msg : BitVec 8) (adv : RushingCorruptStrategy (BitVec 8) 2 8)
      (body : BitVec 8 → BitVec 8 → BitVec 8)
      (tagAbortPred : LeakyPreOpenView 2 8 → Bool),
      0 < leakyTotalSurvivingRuns spec sk msg 2 id adv (Nat.zero_lt_succ 1)
            (unblindedCommitLeak spec body) tagAbortPred ∧
      0 < natAbsDiff
            (leakySurvivingSigCount spec sk msg 2 id adv (Nat.zero_lt_succ 1)
              (unblindedCommitLeak spec body) tagAbortPred (BitVec.ofNat 8 1) * 2)
            (idealStandaloneSigCount spec sk msg 2 id (BitVec.ofNat 8 1) *
             leakyTotalSurvivingRuns spec sk msg 2 id adv (Nat.zero_lt_succ 1)
               (unblindedCommitLeak spec body) tagAbortPred) :=
  ⟨toyCutSpec 2 (Nat.zero_lt_succ 1), concreteSk0, concreteMsg0, toyConstAdv 2,
    (fun y mac => y ^^^ mac), unblindedTagLsbAbortPred,
    toyLeakySkew 2 (Nat.zero_lt_succ 1)
      (unblindedCommitLeak (toyCutSpec 2 (Nat.zero_lt_succ 1)) (fun y mac => y ^^^ mac))
      unblindedTagLsbAbortPred
      (fun _ => toyUnblinded_closed_zero) (fun _ => toyUnblinded_closed_one)⟩

private def sampleSelectiveAbortPred (v : AdvPreOpenView 2 8) : Bool :=
  decide (v.maskedDiffRing.val = 1)

/-- A genuinely rushing corrupt party: its inputs are functions of the honest openings it saw. -/
private def sampleRushingAdv : RushingCorruptStrategy (BitVec 8) 2 8 where
  reactToRingOpen := fun d => BitVec.ofNat 8 d.val
  reactToAllOpens := fun d x => x ^^^ BitVec.ofNat 8 d.val

private def witnessZeroViewIdx : Fin (preOpenMaskCard 2 8) :=
  ⟨0, Nat.mul_pos (Nat.mul_pos (Nat.zero_lt_succ 1) (Nat.two_pow_pos 8)) (Nat.two_pow_pos 8)⟩

/-- Inhabitedness witness for `cutTheHash_abort_conditioned_sd_zero` with a rushing corrupt
    strategy and a genuine selective abort predicate rejecting half of all pre-`OPEN` views
    (`0 < totalSurvive < totalRuns`). -/
theorem witness_cutTheHash_selective_abort_inhabited :
    ∃ (spec : CutTheHashProtocolSpec (BitVec 8) (BitVec 8) (Fin 2) (BitVec 8) 2 8)
      (sk msg : BitVec 8) (adv : RushingCorruptStrategy (BitVec 8) 2 8)
      (abortPred : AdvPreOpenView 2 8 → Bool),
      NonZeroSurvivingRuns spec sk msg 2 id adv (Nat.zero_lt_succ 1) abortPred := by
  refine ⟨toyCutSpec 2 (Nat.zero_lt_succ 1), concreteSk0, concreteMsg0, sampleRushingAdv,
    sampleSelectiveAbortPred, ?_⟩
  unfold NonZeroSurvivingRuns
  rw [totalSurvivingRuns_eq]
  have hSurvGe1 : 1 ≤ viewMaskSurviveCount sampleSelectiveAbortPred := by
    unfold viewMaskSurviveCount
    have hGe : ∀ vIdx : Fin (preOpenMaskCard 2 8),
        (if vIdx = witnessZeroViewIdx then 1 else 0) ≤
        (if sampleSelectiveAbortPred ((enumAdvPreOpenViews 2 8).toFun vIdx) then 0 else 1) := by
      intro vIdx
      by_cases hv : vIdx = witnessZeroViewIdx
      · subst hv
        simp only [↓reduceIte]
        have hAccept : sampleSelectiveAbortPred ((enumAdvPreOpenViews 2 8).toFun witnessZeroViewIdx) = false := by
          decide
        rw [hAccept]
        exact Nat.le_refl 1
      · simp only [hv, ↓reduceIte]
        exact Nat.zero_le _
    have hLe := qsum_le_qsum hGe
    rwa [qsum_eq_indicator] at hLe
  omega


/-! ### §2b. Random-Oracle Commitments: `q_RO / 2^256` Hiding Against a Rushing Oracle Adversary

`commit(y, mac; blind) = RO(domain ‖ y ‖ mac ‖ blind)` does not inhabit `commitHiding`: it is not
a bijection of the blind. This subsection proves the statistical bound instead. The random oracle
is the LAZILY SAMPLED oracle (a log of answered points plus a tape of fresh answers); the
adversary is an arbitrary deterministic oracle algorithm (`RoTree`) in all three of its moves
(reaction to the ring opening, reaction to all openings, abort decision), so every query it makes
before Round 2 counts, including queries made before the commitment exists. -/

/-- A deterministic oracle algorithm: a decision tree whose internal nodes are oracle queries. -/
inductive RoTree (X T Out : Type) where
  | done (out : Out) : RoTree X T Out
  | ask (x : X) (k : T → RoTree X T Out) : RoTree X T Out

/-- `t.DepthLe q`: `t` asks at most `q` oracle queries on every path. -/
def RoTree.DepthLe {X T Out : Type} : RoTree X T Out → Nat → Prop
  | .done _, _ => True
  | .ask _ _, 0 => False
  | .ask _ k, q + 1 => ∀ a, (k a).DepthLe q

/-- Lookup in the oracle log (most recent binding first). -/
def roLookup {X T : Type} [DecidableEq X] : List (X × T) → X → Option T
  | [], _ => none
  | (k, v) :: rest, x => if x = k then some v else roLookup rest x

/-- Run an oracle algorithm against the lazily sampled oracle: a logged point is answered from
    the log, a new point consumes the next tape cell and is logged. Returns the output, the final
    log, and the number of tape cells consumed. -/
def runRo {X T Out : Type} [DecidableEq X] (tape : Nat → T) :
    RoTree X T Out → List (X × T) → Nat → Out × List (X × T) × Nat
  | .done o, log, n => (o, log, n)
  | .ask x k, log, n =>
    match roLookup log x with
    | some a => runRo tape (k a) log n
    | none => runRo tape (k (tape n)) ((x, tape n) :: log) (n + 1)

/-- The points queried during `runRo`, in order (repeats included). -/
def askedRo {X T Out : Type} [DecidableEq X] (tape : Nat → T) :
    RoTree X T Out → List (X × T) → Nat → List X
  | .done _, _, _ => []
  | .ask x k, log, n =>
    match roLookup log x with
    | some a => x :: askedRo tape (k a) log n
    | none => x :: askedRo tape (k (tape n)) ((x, tape n) :: log) (n + 1)

theorem askedRo_length_le {X T Out : Type} [DecidableEq X] (tape : Nat → T)
    (t : RoTree X T Out) :
    ∀ (q : Nat) (log : List (X × T)) (n : Nat),
      t.DepthLe q → (askedRo tape t log n).length ≤ q := by
  induction t with
  | done o => intro q log n _; exact Nat.zero_le q
  | ask x k ih =>
    intro q log n hD
    cases q with
    | zero => exact False.elim hD
    | succ q =>
      have hD' : ∀ a, (k a).DepthLe q := hD
      unfold askedRo
      cases hL : roLookup log x with
      | some a => exact Nat.succ_le_succ (ih a q log n (hD' a))
      | none => exact Nat.succ_le_succ (ih (tape n) q _ _ (hD' (tape n)))

/-- A point that is neither logged nor queried stays unlogged. -/
theorem runRo_lookup_none {X T Out : Type} [DecidableEq X] (tape : Nat → T) (p : X)
    (t : RoTree X T Out) :
    ∀ (log : List (X × T)) (n : Nat),
      roLookup log p = none → p ∉ askedRo tape t log n →
      roLookup (runRo tape t log n).2.1 p = none := by
  induction t with
  | done o => intro log n hNone _; exact hNone
  | ask x k ih =>
    intro log n hNone hNot
    unfold askedRo at hNot
    unfold runRo
    cases hL : roLookup log x with
    | some a =>
      rw [hL] at hNot
      exact ih a log n hNone (fun h => hNot (List.mem_cons_of_mem _ h))
    | none =>
      rw [hL] at hNot
      have hpx : p ≠ x := fun h => hNot (h ▸ List.mem_cons_self)
      have hNone' : roLookup ((x, tape n) :: log) p = none := by
        simp only [roLookup, hpx, ↓reduceIte]
        exact hNone
      exact ih (tape n) _ _ hNone' (fun h => hNot (List.mem_cons_of_mem _ h))

/-- **Identical-until-queried**: two logs that agree away from `p` give the same run as long as
    the run never asks `p`. -/
theorem runRo_agree_off {X T Out : Type} [DecidableEq X] (tape : Nat → T) (p : X)
    (t : RoTree X T Out) :
    ∀ (log log' : List (X × T)) (n : Nat),
      (∀ x, x ≠ p → roLookup log' x = roLookup log x) →
      p ∉ askedRo tape t log n →
      (runRo tape t log' n).1 = (runRo tape t log n).1 := by
  induction t with
  | done o => intro log log' n _ _; rfl
  | ask x k ih =>
    intro log log' n hAgree hNot
    unfold askedRo at hNot
    have hxp : x ≠ p := by
      intro h
      apply hNot
      cases hL : roLookup log x <;> exact h ▸ List.mem_cons_self
    have hLk := hAgree x hxp
    unfold runRo
    rw [hLk]
    cases hL : roLookup log x with
    | some a =>
      rw [hL] at hNot
      exact ih a log log' n hAgree (fun h => hNot (List.mem_cons_of_mem _ h))
    | none =>
      rw [hL] at hNot
      have hAgree' : ∀ y, y ≠ p →
          roLookup ((x, tape n) :: log') y = roLookup ((x, tape n) :: log) y := by
        intro y hy
        simp only [roLookup]
        split
        · rfl
        · exact hAgree y hy
      exact ih (tape n) _ _ (n + 1) hAgree' (fun h => hNot (List.mem_cons_of_mem _ h))

/-- Cut-the-Hash with a random-oracle commitment. `commitPoint y mac blind` is the oracle input
    `domain ‖ y ‖ mac ‖ blind`; `blindOf` reads the blind back out of an oracle input. -/
structure CutTheHashRomSpec (SK Msg Rand CorruptIn X : Type) (Q w bw : Nat) where
  wireRingSecret : SK → Msg → Rand → Fin Q
  wireXorSecret : SK → Msg → Rand → CorruptIn → BitVec w
  yShareHonest : SK → Msg → Rand → CorruptIn → BitVec w
  macShareHonest : SK → Msg → Rand → CorruptIn → BitVec w
  commitPoint : BitVec w → BitVec w → BitVec bw → X
  blindOf : X → BitVec bw

/-- The blind is length-framed inside the hashed input, so it can be read back. A commitment
    whose input drops the blind fails this and is exactly the `#tooth` below. -/
def CutTheHashRomSpec.BlindFramed {SK Msg Rand CorruptIn X : Type} {Q w bw : Nat}
    (spec : CutTheHashRomSpec SK Msg Rand CorruptIn X Q w bw) : Prop :=
  ∀ y mac b, spec.blindOf (spec.commitPoint y mac b) = b

/-- A rushing corrupt party with oracle access in every move. `St1`, `St2` are its private
    states carried between moves; `Out` is whatever it finally outputs (its abort decision
    together with any function of its whole view). -/
structure RushingRoAdversary (CorruptIn X T St1 St2 Out : Type) (Q w : Nat) where
  reactToRingOpen : Fin Q → RoTree X T (CorruptIn × St1)
  reactToAllOpens : St1 → BitVec w → RoTree X T (CorruptIn × St2)
  decideAbort : St2 → T → RoTree X T Out

/-- Per-move oracle query budgets; `q_RO = q1 + q2 + q3`. -/
def RushingRoAdversary.QueryBound {CorruptIn X T St1 St2 Out : Type} {Q w : Nat}
    (adv : RushingRoAdversary CorruptIn X T St1 St2 Out Q w) (q1 q2 q3 : Nat) : Prop :=
  (∀ d, (adv.reactToRingOpen d).DepthLe q1) ∧
  (∀ s x, (adv.reactToAllOpens s x).DepthLe q2) ∧
  (∀ s t, (adv.decideAbort s t).DepthLe q3)

/-- The first two adversary moves, given the two opened masked differences. -/
def romPhaseAB {CorruptIn X T St1 St2 Out : Type} {Q w : Nat} [DecidableEq X]
    (adv : RushingRoAdversary CorruptIn X T St1 St2 Out Q w) (tape : Nat → T)
    (d1 : Fin Q) (d2 : BitVec w) : (CorruptIn × St2) × List (X × T) × Nat :=
  runRo tape
    (adv.reactToAllOpens (runRo tape (adv.reactToRingOpen d1) [] 0).1.2 d2)
    (runRo tape (adv.reactToRingOpen d1) [] 0).2.1
    (runRo tape (adv.reactToRingOpen d1) [] 0).2.2

/-- **Secret-free simulation**: the adversary is handed uniform masked differences and a FRESH
    tag; the oracle is never programmed. No secret key, message or randomizer enters. -/
def romIdealRun {CorruptIn X T St1 St2 Out : Type} {Q w : Nat} [DecidableEq X]
    (adv : RushingRoAdversary CorruptIn X T St1 St2 Out Q w) (tape : Nat → T)
    (d1 : Fin Q) (d2 : BitVec w) (tag : T) : Out :=
  (runRo tape (adv.decideAbort (romPhaseAB adv tape d1 d2).1.2 tag)
    (romPhaseAB adv tape d1 d2).2.1 (romPhaseAB adv tape d1 d2).2.2).1

/-- Every oracle point the simulated adversary queries, over all three moves. -/
def romIdealAsked {CorruptIn X T St1 St2 Out : Type} {Q w : Nat} [DecidableEq X]
    (adv : RushingRoAdversary CorruptIn X T St1 St2 Out Q w) (tape : Nat → T)
    (d1 : Fin Q) (d2 : BitVec w) (tag : T) : List X :=
  askedRo tape (adv.reactToRingOpen d1) [] 0 ++
    (askedRo tape
        (adv.reactToAllOpens (runRo tape (adv.reactToRingOpen d1) [] 0).1.2 d2)
        (runRo tape (adv.reactToRingOpen d1) [] 0).2.1
        (runRo tape (adv.reactToRingOpen d1) [] 0).2.2 ++
     askedRo tape (adv.decideAbort (romPhaseAB adv tape d1 d2).1.2 tag)
        (romPhaseAB adv tape d1 d2).2.1 (romPhaseAB adv tape d1 d2).2.2)

theorem romIdealAsked_length_le {CorruptIn X T St1 St2 Out : Type} {Q w : Nat} [DecidableEq X]
    (adv : RushingRoAdversary CorruptIn X T St1 St2 Out Q w) (tape : Nat → T)
    {q1 q2 q3 : Nat} (hQry : adv.QueryBound q1 q2 q3) (d1 : Fin Q) (d2 : BitVec w) (tag : T) :
    (romIdealAsked adv tape d1 d2 tag).length ≤ q1 + q2 + q3 := by
  unfold romIdealAsked
  rw [List.length_append, List.length_append]
  have h1 := askedRo_length_le tape (adv.reactToRingOpen d1) q1 [] 0 (hQry.1 d1)
  have h2 := askedRo_length_le tape
    (adv.reactToAllOpens (runRo tape (adv.reactToRingOpen d1) [] 0).1.2 d2) q2
    (runRo tape (adv.reactToRingOpen d1) [] 0).2.1
    (runRo tape (adv.reactToRingOpen d1) [] 0).2.2 (hQry.2.1 _ _)
  have h3 := askedRo_length_le tape (adv.decideAbort (romPhaseAB adv tape d1 d2).1.2 tag) q3
    (romPhaseAB adv tape d1 d2).2.1 (romPhaseAB adv tape d1 d2).2.2 (hQry.2.2 _ _)
  omega

/-- The masked ring difference the adversary sees. -/
def romViewRing {SK Msg Rand CorruptIn X : Type} {Q w bw : Nat}
    (spec : CutTheHashRomSpec SK Msg Rand CorruptIn X Q w bw)
    (sk : SK) (msg : Msg) (R : Rand) (hQ : 0 < Q) (mr : Fin Q) : Fin Q :=
  subModFinQ Q hQ (spec.wireRingSecret sk msg R) mr

/-- The boolean wire secret, which depends on the adversary's rushing reaction to the ring
    opening (and through it on the oracle). -/
def romXorPad {SK Msg Rand CorruptIn X T St1 St2 Out : Type} {Q w bw : Nat} [DecidableEq X]
    (spec : CutTheHashRomSpec SK Msg Rand CorruptIn X Q w bw)
    (adv : RushingRoAdversary CorruptIn X T St1 St2 Out Q w)
    (sk : SK) (msg : Msg) (R : Rand) (hQ : 0 < Q) (tape : Nat → T) (mr : Fin Q) : BitVec w :=
  spec.wireXorSecret sk msg R
    (runRo tape (adv.reactToRingOpen (romViewRing spec sk msg R hQ mr)) [] 0).1.1

/-- The masked boolean difference the adversary sees. -/
def romViewXor {SK Msg Rand CorruptIn X T St1 St2 Out : Type} {Q w bw : Nat} [DecidableEq X]
    (spec : CutTheHashRomSpec SK Msg Rand CorruptIn X Q w bw)
    (adv : RushingRoAdversary CorruptIn X T St1 St2 Out Q w)
    (sk : SK) (msg : Msg) (R : Rand) (hQ : 0 < Q) (tape : Nat → T) (mr : Fin Q)
    (mx : BitVec w) : BitVec w :=
  romXorPad spec adv sk msg R hQ tape mr ^^^ mx

/-- The oracle input of the honest commitment in the real execution. -/
def romCommitPoint {SK Msg Rand CorruptIn X T St1 St2 Out : Type} {Q w bw : Nat} [DecidableEq X]
    (spec : CutTheHashRomSpec SK Msg Rand CorruptIn X Q w bw)
    (adv : RushingRoAdversary CorruptIn X T St1 St2 Out Q w)
    (sk : SK) (msg : Msg) (R : Rand) (hQ : 0 < Q) (tape : Nat → T) (mr : Fin Q)
    (mx : BitVec w) (b : BitVec bw) : X :=
  spec.commitPoint
    (spec.yShareHonest sk msg R
      (romPhaseAB adv tape (romViewRing spec sk msg R hQ mr)
        (romViewXor spec adv sk msg R hQ tape mr mx)).1.1)
    (spec.macShareHonest sk msg R
      (romPhaseAB adv tape (romViewRing spec sk msg R hQ mr)
        (romViewXor spec adv sk msg R hQ tape mr mx)).1.1)
    b

/-- **Real execution** against the lazily sampled oracle. The commitment tag is the oracle's
    value at `commitPoint`: the logged answer if the adversary already queried that point, the
    fresh `tagFresh` otherwise; the point is then logged, so later queries return the tag. -/
def romRealRun {SK Msg Rand CorruptIn X T St1 St2 Out : Type} {Q w bw : Nat} [DecidableEq X]
    (spec : CutTheHashRomSpec SK Msg Rand CorruptIn X Q w bw)
    (adv : RushingRoAdversary CorruptIn X T St1 St2 Out Q w)
    (sk : SK) (msg : Msg) (R : Rand) (hQ : 0 < Q) (tape : Nat → T) (mr : Fin Q)
    (mx : BitVec w) (b : BitVec bw) (tagFresh : T) : Out :=
  (runRo tape
    (adv.decideAbort
      (romPhaseAB adv tape (romViewRing spec sk msg R hQ mr)
        (romViewXor spec adv sk msg R hQ tape mr mx)).1.2
      ((roLookup
        (romPhaseAB adv tape (romViewRing spec sk msg R hQ mr)
          (romViewXor spec adv sk msg R hQ tape mr mx)).2.1
        (romCommitPoint spec adv sk msg R hQ tape mr mx b)).getD tagFresh))
    ((romCommitPoint spec adv sk msg R hQ tape mr mx b,
      (roLookup
        (romPhaseAB adv tape (romViewRing spec sk msg R hQ mr)
          (romViewXor spec adv sk msg R hQ tape mr mx)).2.1
        (romCommitPoint spec adv sk msg R hQ tape mr mx b)).getD tagFresh) ::
      (romPhaseAB adv tape (romViewRing spec sk msg R hQ mr)
        (romViewXor spec adv sk msg R hQ tape mr mx)).2.1)
    (romPhaseAB adv tape (romViewRing spec sk msg R hQ mr)
      (romViewXor spec adv sk msg R hQ tape mr mx)).2.2).1

/-- **Real = simulation unless the blind is queried**: if no oracle query of the simulated run
    carries the blind `b`, the real execution's output equals the secret-free simulation's. -/
theorem romReal_eq_ideal_of_blind_unqueried
    {SK Msg Rand CorruptIn X T St1 St2 Out : Type} {Q w bw : Nat} [DecidableEq X]
    (spec : CutTheHashRomSpec SK Msg Rand CorruptIn X Q w bw) (hFramed : spec.BlindFramed)
    (adv : RushingRoAdversary CorruptIn X T St1 St2 Out Q w)
    (sk : SK) (msg : Msg) (R : Rand) (hQ : 0 < Q) (tape : Nat → T) (mr : Fin Q)
    (mx : BitVec w) (b : BitVec bw) (tagFresh : T)
    (hFresh : b ∉ (romIdealAsked adv tape (romViewRing spec sk msg R hQ mr)
        (romViewXor spec adv sk msg R hQ tape mr mx) tagFresh).map spec.blindOf) :
    romRealRun spec adv sk msg R hQ tape mr mx b tagFresh =
      romIdealRun adv tape (romViewRing spec sk msg R hQ mr)
        (romViewXor spec adv sk msg R hQ tape mr mx) tagFresh := by
  have hPt : romCommitPoint spec adv sk msg R hQ tape mr mx b ∉
      romIdealAsked adv tape (romViewRing spec sk msg R hQ mr)
        (romViewXor spec adv sk msg R hQ tape mr mx) tagFresh :=
    fun hMem => hFresh (List.mem_map.mpr ⟨_, hMem, hFramed _ _ _⟩)
  unfold romIdealAsked at hPt
  have hPt1 := fun h => hPt (List.mem_append_left _ h)
  have hPt2 := fun h => hPt (List.mem_append_right _ (List.mem_append_left _ h))
  have hPt3 := fun h => hPt (List.mem_append_right _ (List.mem_append_right _ h))
  have hL1 := runRo_lookup_none tape (romCommitPoint spec adv sk msg R hQ tape mr mx b)
    (adv.reactToRingOpen (romViewRing spec sk msg R hQ mr)) [] 0 rfl hPt1
  have hL2 : roLookup
      (romPhaseAB adv tape (romViewRing spec sk msg R hQ mr)
        (romViewXor spec adv sk msg R hQ tape mr mx)).2.1
      (romCommitPoint spec adv sk msg R hQ tape mr mx b) = none :=
    runRo_lookup_none tape _ _ _ _ hL1 hPt2
  unfold romRealRun romIdealRun
  rw [hL2]
  refine runRo_agree_off tape (romCommitPoint spec adv sk msg R hQ tape mr mx b) _ _ _ _ ?_ hPt3
  intro x hx
  simp only [roLookup, hx, ↓reduceIte]

private theorem natAbsDiff_qsum_le_const {n : Nat} (f g : Fin n → Nat) (c : Nat)
    (h : ∀ i, natAbsDiff (f i) (g i) ≤ c) :
    natAbsDiff (qsum n f) (qsum n g) ≤ n * c :=
  Nat.le_trans (natAbsDiff_qsum_le f g)
    (Nat.le_trans (qsum_le_qsum h) (Nat.le_of_eq (qsum_const n c)))

private theorem natAbsDiff_comm (a b : Nat) : natAbsDiff a b = natAbsDiff b a := by
  simp only [natAbsDiff_eq]
  split <;> split <;> omega

private theorem ite_decide_eq_ite {p : Prop} (i₁ i₂ : Decidable p) (a b : Nat) :
    (if @decide p i₁ = true then a else b) = @ite Nat p i₂ a b := by
  cases i₁ with
  | isTrue h =>
    cases i₂ with
    | isTrue _ => rfl
    | isFalse h' => exact absurd h h'
  | isFalse h =>
    cases i₂ with
    | isTrue h' => exact absurd h' h
    | isFalse _ => rfl

/-- **Blind-guessing bound, one mask assignment**: for fixed Beaver masks, fresh tag and tape,
    at most `q1 + q2 + q3` of the `2^bw` blinds make the real output differ from the simulation,
    for every distinguishing predicate `D` on the adversary's output. -/
theorem romCommit_blind_count_bound
    {SK Msg Rand CorruptIn X T St1 St2 Out : Type} {Q w bw : Nat} [DecidableEq X]
    (spec : CutTheHashRomSpec SK Msg Rand CorruptIn X Q w bw) (hFramed : spec.BlindFramed)
    (adv : RushingRoAdversary CorruptIn X T St1 St2 Out Q w)
    {q1 q2 q3 : Nat} (hQry : adv.QueryBound q1 q2 q3)
    (sk : SK) (msg : Msg) (R : Rand) (hQ : 0 < Q) (tape : Nat → T) (D : Out → Bool)
    (tagFresh : T) (mr : Fin Q) (mx : BitVec w) :
    natAbsDiff
      (qsum (2 ^ bw) (fun bi =>
        if D (romRealRun spec adv sk msg R hQ tape mr mx ((enumBitVec bw).toFun bi) tagFresh)
        then 1 else 0))
      (2 ^ bw *
        (if D (romIdealRun adv tape (romViewRing spec sk msg R hQ mr)
            (romViewXor spec adv sk msg R hQ tape mr mx) tagFresh) then 1 else 0)) ≤
      q1 + q2 + q3 := by
  have hConst : 2 ^ bw *
      (if D (romIdealRun adv tape (romViewRing spec sk msg R hQ mr)
          (romViewXor spec adv sk msg R hQ tape mr mx) tagFresh) then 1 else 0) =
      qsum (2 ^ bw) (fun _ =>
        if D (romIdealRun adv tape (romViewRing spec sk msg R hQ mr)
          (romViewXor spec adv sk msg R hQ tape mr mx) tagFresh) then 1 else 0) :=
    (qsum_const _ _).symm
  rw [hConst]
  have hDiff := qsum_indicator_diff_le
    (fun bi : Fin (2 ^ bw) =>
      D (romRealRun spec adv sk msg R hQ tape mr mx ((enumBitVec bw).toFun bi) tagFresh))
    (fun _ => D (romIdealRun adv tape (romViewRing spec sk msg R hQ mr)
      (romViewXor spec adv sk msg R hQ tape mr mx) tagFresh))
    (fun bi => @decide (bi ∈
      ((romIdealAsked adv tape (romViewRing spec sk msg R hQ mr)
        (romViewXor spec adv sk msg R hQ tape mr mx) tagFresh).map spec.blindOf).map
        (enumBitVec bw).invFun)
      (@List.instDecidableMemOfLawfulBEq (Fin (2 ^ bw))
        (@instBEqOfDecidableEq _ (instDecidableEqFin (2 ^ bw)))
        (@instLawfulBEq _ (instDecidableEqFin (2 ^ bw))) bi _))
    (by
      intro bi hBad
      have hNot := of_decide_eq_false hBad
      exact congrArg D (romReal_eq_ideal_of_blind_unqueried spec hFramed adv sk msg R hQ tape
        mr mx _ tagFresh
        (fun hMem => hNot (List.mem_map.mpr ⟨_, hMem, (enumBitVec bw).left_inv bi⟩))))
  refine Nat.le_trans hDiff ?_
  have hCount := qsum_mem_list_le (2 ^ bw)
    (((romIdealAsked adv tape (romViewRing spec sk msg R hQ mr)
      (romViewXor spec adv sk msg R hQ tape mr mx) tagFresh).map spec.blindOf).map
      (enumBitVec bw).invFun)
  rw [List.length_map, List.length_map] at hCount
  refine Nat.le_trans (Nat.le_trans (Nat.le_of_eq (qsum_congr (fun bi => ?_))) hCount)
    (romIdealAsked_length_le adv tape hQry _ _ _)
  exact ite_decide_eq_ite _ _ _ _

/-- Number of honest mask assignments `(ring mask, boolean mask, 2^bw-blind)` on which the real
    adversary output satisfies `D`. -/
def romRealCount {SK Msg Rand CorruptIn X T St1 St2 Out : Type} {Q w bw : Nat} [DecidableEq X]
    (spec : CutTheHashRomSpec SK Msg Rand CorruptIn X Q w bw)
    (adv : RushingRoAdversary CorruptIn X T St1 St2 Out Q w)
    (sk : SK) (msg : Msg) (R : Rand) (hQ : 0 < Q) (tape : Nat → T) (D : Out → Bool)
    (tagFresh : T) : Nat :=
  qsum Q (fun mr => qsum (2 ^ w) (fun xi => qsum (2 ^ bw) (fun bi =>
    if D (romRealRun spec adv sk msg R hQ tape mr ((enumBitVec w).toFun xi)
      ((enumBitVec bw).toFun bi) tagFresh) then 1 else 0)))

/-- Number of uniform view prefixes `(d1, d2)` on which the secret-free simulation satisfies
    `D`. -/
def romIdealCount {CorruptIn X T St1 St2 Out : Type} {Q w : Nat} [DecidableEq X]
    (adv : RushingRoAdversary CorruptIn X T St1 St2 Out Q w) (tape : Nat → T) (D : Out → Bool)
    (tagFresh : T) : Nat :=
  qsum Q (fun d1 => qsum (2 ^ w) (fun xi =>
    if D (romIdealRun adv tape d1 ((enumBitVec w).toFun xi) tagFresh) then 1 else 0))

/-- **Random-Oracle Commitment Hiding With Rushing Selective Abort
    (`cutTheHash_rom_commit_hiding_sd_bound`)**: for every secret, every rushing adversary making
    at most `q1 + q2 + q3` oracle queries over its three moves, every distinguishing predicate `D`
    on its output (in particular its abort decision), every fresh tag and every oracle tape,

      `| #real(D) - 2^bw · #sim(D) |  ≤  Q · 2^w · (q1 + q2 + q3)`.

    The real sample space has `Q · 2^w · 2^bw` points and the simulation `Q · 2^w`, so dividing
    by `Q · 2^w · 2^bw` reads `|Pr_real[D] - Pr_sim[D]| ≤ (q1 + q2 + q3) / 2^bw`: the adversary's
    pre-`OPEN` view and abort decision are within statistical distance `q_RO / 2^bw` of a
    simulation that reads no secret. The bound holds pointwise in the tag and tape, hence for the
    uniform ones. -/
theorem cutTheHash_rom_commit_hiding_sd_bound
    {SK Msg Rand CorruptIn X T St1 St2 Out : Type} {Q w bw : Nat} [DecidableEq X]
    (spec : CutTheHashRomSpec SK Msg Rand CorruptIn X Q w bw) (hFramed : spec.BlindFramed)
    (adv : RushingRoAdversary CorruptIn X T St1 St2 Out Q w)
    {q1 q2 q3 : Nat} (hQry : adv.QueryBound q1 q2 q3)
    (sk : SK) (msg : Msg) (R : Rand) (hQ : 0 < Q) (tape : Nat → T) (D : Out → Bool)
    (tagFresh : T) :
    natAbsDiff (romRealCount spec adv sk msg R hQ tape D tagFresh)
      (2 ^ bw * romIdealCount adv tape D tagFresh) ≤ Q * (2 ^ w * (q1 + q2 + q3)) := by
  have hStep : natAbsDiff
      (qsum Q (fun mr => qsum (2 ^ w) (fun xi => qsum (2 ^ bw) (fun bi =>
        if D (romRealRun spec adv sk msg R hQ tape mr ((enumBitVec w).toFun xi)
          ((enumBitVec bw).toFun bi) tagFresh) then 1 else 0))))
      (qsum Q (fun mr => qsum (2 ^ w) (fun xi => 2 ^ bw *
        (if D (romIdealRun adv tape (romViewRing spec sk msg R hQ mr)
          (romViewXor spec adv sk msg R hQ tape mr ((enumBitVec w).toFun xi)) tagFresh)
         then 1 else 0)))) ≤ Q * (2 ^ w * (q1 + q2 + q3)) :=
    natAbsDiff_qsum_le_const _ _ _ (fun mr =>
      natAbsDiff_qsum_le_const _ _ _ (fun xi =>
        romCommit_blind_count_bound spec hFramed adv hQry sk msg R hQ tape D tagFresh mr
          ((enumBitVec w).toFun xi)))
  have hInner : ∀ mr : Fin Q,
      qsum (2 ^ w) (fun xi => 2 ^ bw *
        (if D (romIdealRun adv tape (romViewRing spec sk msg R hQ mr)
          (romViewXor spec adv sk msg R hQ tape mr ((enumBitVec w).toFun xi)) tagFresh)
         then 1 else 0)) =
      2 ^ bw * qsum (2 ^ w) (fun xi =>
        if D (romIdealRun adv tape (romViewRing spec sk msg R hQ mr) ((enumBitVec w).toFun xi)
          tagFresh) then 1 else 0) := by
    intro mr
    rw [qsum_mul_left]
    exact congrArg (fun s => 2 ^ bw * s)
      (qsum_bijection_invariant (enumBitVec w)
        (maskBijectionBitVec w (romXorPad spec adv sk msg R hQ tape mr))
        (fun d2 => if D (romIdealRun adv tape (romViewRing spec sk msg R hQ mr) d2 tagFresh)
          then 1 else 0))
  have hOuter : qsum Q (fun mr => qsum (2 ^ w) (fun xi =>
        if D (romIdealRun adv tape (romViewRing spec sk msg R hQ mr) ((enumBitVec w).toFun xi)
          tagFresh) then 1 else 0)) = romIdealCount adv tape D tagFresh :=
    qsum_perm_invariant
      (fun mr => subModFinQ Q hQ (spec.wireRingSecret sk msg R) mr)
      (fun d => subModFinQ Q hQ (spec.wireRingSecret sk msg R) d)
      (fun i => subModFinQ_involutive Q hQ _ i) (fun j => subModFinQ_involutive Q hQ _ j)
      (fun d1 => qsum (2 ^ w) (fun xi =>
        if D (romIdealRun adv tape d1 ((enumBitVec w).toFun xi) tagFresh) then 1 else 0))
  have hMid : qsum Q (fun mr => qsum (2 ^ w) (fun xi => 2 ^ bw *
        (if D (romIdealRun adv tape (romViewRing spec sk msg R hQ mr)
          (romViewXor spec adv sk msg R hQ tape mr ((enumBitVec w).toFun xi)) tagFresh)
         then 1 else 0))) = 2 ^ bw * romIdealCount adv tape D tagFresh := by
    rw [qsum_congr hInner, qsum_mul_left, hOuter]
  rw [← hMid]
  exact hStep

/-- **Secret independence up to `2 · q_RO / 2^bw`**: the real adversary-output counts under any
    two secrets, messages and randomizers differ by at most twice the hiding bound. -/
theorem cutTheHash_rom_view_secret_independent
    {SK Msg Rand CorruptIn X T St1 St2 Out : Type} {Q w bw : Nat} [DecidableEq X]
    (spec : CutTheHashRomSpec SK Msg Rand CorruptIn X Q w bw) (hFramed : spec.BlindFramed)
    (adv : RushingRoAdversary CorruptIn X T St1 St2 Out Q w)
    {q1 q2 q3 : Nat} (hQry : adv.QueryBound q1 q2 q3)
    (sk sk' : SK) (msg msg' : Msg) (R R' : Rand) (hQ : 0 < Q) (tape : Nat → T) (D : Out → Bool)
    (tagFresh : T) :
    natAbsDiff (romRealCount spec adv sk msg R hQ tape D tagFresh)
      (romRealCount spec adv sk' msg' R' hQ tape D tagFresh) ≤
      2 * (Q * (2 ^ w * (q1 + q2 + q3))) := by
  have h1 := cutTheHash_rom_commit_hiding_sd_bound spec hFramed adv hQry sk msg R hQ tape D
    tagFresh
  have h2 := cutTheHash_rom_commit_hiding_sd_bound spec hFramed adv hQry sk' msg' R' hQ tape D
    tagFresh
  rw [natAbsDiff_comm] at h2
  have hTri := natAbsDiff_triangle (romRealCount spec adv sk msg R hQ tape D tagFresh)
    (2 ^ bw * romIdealCount adv tape D tagFresh)
    (romRealCount spec adv sk' msg' R' hQ tape D tagFresh)
  omega

/-- The deployed width: a 256-bit blind gives `q_RO / 2^256`. -/
theorem cutTheHash_rom_commit_hiding_sd_bound_256
    {SK Msg Rand CorruptIn X T St1 St2 Out : Type} {Q w : Nat} [DecidableEq X]
    (spec : CutTheHashRomSpec SK Msg Rand CorruptIn X Q w 256) (hFramed : spec.BlindFramed)
    (adv : RushingRoAdversary CorruptIn X T St1 St2 Out Q w)
    {q1 q2 q3 : Nat} (hQry : adv.QueryBound q1 q2 q3)
    (sk : SK) (msg : Msg) (R : Rand) (hQ : 0 < Q) (tape : Nat → T) (D : Out → Bool)
    (tagFresh : T) :
    natAbsDiff (romRealCount spec adv sk msg R hQ tape D tagFresh)
      (2 ^ 256 * romIdealCount adv tape D tagFresh) ≤ Q * (2 ^ w * (q1 + q2 + q3)) :=
  cutTheHash_rom_commit_hiding_sd_bound spec hFramed adv hQry sk msg R hQ tape D tagFresh

/-! ## §3. Threshold ML-DSA-44 Rejection Independence: `z` Box, `LowBits` Margin & `HighBits` -/

/-- Cardinality `2 * gamma1 - 1` of the integer mask interval `[-gamma1 + 1, gamma1 - 1]`. -/
def mldsaMaskIntervalCard (gamma1 : Nat) : Nat := 2 * gamma1 - 1

/-- Cardinality `2 * (gamma1 - beta) - 1` of the safe output box
    `[-gamma1 + beta + 1, gamma1 - beta - 1]`. -/
def mldsaSafeBoxCard (gamma1 beta : Nat) : Nat := 2 * (gamma1 - beta) - 1

/-- Mask interval membership `y ∈ [-gamma1 + 1, gamma1 - 1]` (`‖y‖_∞ < gamma1`). -/
abbrev inMldsaMaskInterval (gamma1 : Nat) (y : Int) : Prop :=
  (-(gamma1 : Int) + 1 ≤ y) ∧ (y ≤ (gamma1 : Int) - 1)

/-- Secret shift bound `‖c_s1‖_∞ ≤ beta` (`-beta ≤ c_s1 ≤ beta`). -/
abbrev inMldsaSecretBound (beta : Nat) (c_s1 : Int) : Prop :=
  (-(beta : Int) ≤ c_s1) ∧ (c_s1 ≤ (beta : Int))

/-- Safe rejection output box `z ∈ [-gamma1 + beta + 1, gamma1 - beta - 1]` (`‖z‖_∞ < gamma1 - beta`). -/
abbrev inMldsaSafeBox (gamma1 beta : Nat) (z : Int) : Prop :=
  (-(gamma1 : Int) + (beta : Int) + 1 ≤ z) ∧ (z ≤ (gamma1 : Int) - (beta : Int) - 1)

theorem inMldsaSecretBound_iff_natAbs_le (beta : Nat) (c_s1 : Int) :
    inMldsaSecretBound beta c_s1 ↔ c_s1.natAbs ≤ beta := by
  unfold inMldsaSecretBound
  exact ⟨fun h => by omega, fun h => ⟨by omega, by omega⟩⟩

theorem inMldsaSafeBox_iff_natAbs_lt {gamma1 beta : Nat} (_hLt : beta < gamma1) (z : Int) :
    inMldsaSafeBox gamma1 beta z ↔ z.natAbs < gamma1 - beta := by
  unfold inMldsaSafeBox
  exact ⟨fun h => by omega, fun h => ⟨by omega, by omega⟩⟩

/-- Constructive decoding of `Fin (2 * gamma1 - 1)` onto `[-gamma1 + 1, gamma1 - 1]`. -/
def decodeMldsaMask (gamma1 : Nat) (i : Fin (mldsaMaskIntervalCard gamma1)) : Int :=
  (i.val : Int) - ((gamma1 : Int) - 1)

/-- Constructive encoding of `y ∈ [-gamma1 + 1, gamma1 - 1]` into `Fin (2 * gamma1 - 1)`. -/
def encodeMldsaMask {gamma1 : Nat} (_hPos : 0 < gamma1) (y : Int)
    (hy : inMldsaMaskInterval gamma1 y) : Fin (mldsaMaskIntervalCard gamma1) :=
  ⟨(y + ((gamma1 : Int) - 1)).toNat, by
    unfold inMldsaMaskInterval at hy
    unfold mldsaMaskIntervalCard
    omega⟩

theorem decode_encodeMldsaMask {gamma1 : Nat} (hPos : 0 < gamma1) (y : Int)
    (hy : inMldsaMaskInterval gamma1 y) :
    decodeMldsaMask gamma1 (encodeMldsaMask hPos y hy) = y := by
  unfold decodeMldsaMask encodeMldsaMask inMldsaMaskInterval at *
  dsimp only
  omega

theorem encode_decodeMldsaMask {gamma1 : Nat} (hPos : 0 < gamma1)
    (i : Fin (mldsaMaskIntervalCard gamma1)) :
    inMldsaMaskInterval gamma1 (decodeMldsaMask gamma1 i) ∧
    encodeMldsaMask hPos (decodeMldsaMask gamma1 i)
      ⟨by unfold decodeMldsaMask mldsaMaskIntervalCard at *; omega,
       by unfold decodeMldsaMask mldsaMaskIntervalCard at *; omega⟩ = i := by
  refine ⟨⟨by unfold decodeMldsaMask mldsaMaskIntervalCard at *; omega,
           by unfold decodeMldsaMask mldsaMaskIntervalCard at *; omega⟩, ?_⟩
  apply Fin.ext
  unfold encodeMldsaMask decodeMldsaMask mldsaMaskIntervalCard at *
  dsimp only
  omega

/-- Constructive decoding of `Fin (2 * (gamma1 - beta) - 1)` onto `[-gamma1 + beta + 1, gamma1 - beta - 1]`. -/
def decodeMldsaSafeBox (gamma1 beta : Nat) (j : Fin (mldsaSafeBoxCard gamma1 beta)) : Int :=
  (j.val : Int) - ((gamma1 : Int) - (beta : Int) - 1)

/-- Constructive encoding of `z ∈ [-gamma1 + beta + 1, gamma1 - beta - 1]` into `Fin (2 * (gamma1 - beta) - 1)`. -/
def encodeMldsaSafeBox {gamma1 beta : Nat} (_hLt : beta < gamma1) (z : Int)
    (hz : inMldsaSafeBox gamma1 beta z) : Fin (mldsaSafeBoxCard gamma1 beta) :=
  ⟨(z + ((gamma1 : Int) - (beta : Int) - 1)).toNat, by
    unfold inMldsaSafeBox at hz
    unfold mldsaSafeBoxCard
    omega⟩

theorem decode_encodeMldsaSafeBox {gamma1 beta : Nat} (hLt : beta < gamma1) (z : Int)
    (hz : inMldsaSafeBox gamma1 beta z) :
    decodeMldsaSafeBox gamma1 beta (encodeMldsaSafeBox hLt z hz) = z := by
  unfold decodeMldsaSafeBox encodeMldsaSafeBox inMldsaSafeBox at *
  dsimp only
  omega

theorem encode_decodeMldsaSafeBox {gamma1 beta : Nat} (hLt : beta < gamma1)
    (j : Fin (mldsaSafeBoxCard gamma1 beta)) :
    inMldsaSafeBox gamma1 beta (decodeMldsaSafeBox gamma1 beta j) ∧
    encodeMldsaSafeBox hLt (decodeMldsaSafeBox gamma1 beta j)
      ⟨by unfold decodeMldsaSafeBox mldsaSafeBoxCard at *; omega,
       by unfold decodeMldsaSafeBox mldsaSafeBoxCard at *; omega⟩ = j := by
  refine ⟨⟨by unfold decodeMldsaSafeBox mldsaSafeBoxCard at *; omega,
           by unfold decodeMldsaSafeBox mldsaSafeBoxCard at *; omega⟩, ?_⟩
  apply Fin.ext
  unfold encodeMldsaSafeBox decodeMldsaSafeBox mldsaSafeBoxCard at *
  dsimp only
  omega

/-- Key shift-containment lemma: for every `z` in `[-gamma1 + beta + 1, gamma1 - beta - 1]` and
    every `c_s1` with `|c_s1| ≤ beta`, the unique preimage `y = z - c_s1` lies inside
    `[-gamma1 + 1, gamma1 - 1]`. -/
theorem safeBox_sub_secret_in_maskInterval {gamma1 beta : Nat} {c_s1 z : Int}
    (hSecret : inMldsaSecretBound beta c_s1)
    (hSafe : inMldsaSafeBox gamma1 beta z) :
    inMldsaMaskInterval gamma1 (z - c_s1) := by
  unfold inMldsaSecretBound inMldsaSafeBox inMldsaMaskInterval at *
  exact ⟨by omega, by omega⟩

/-- Constructive `0 Classical.choice` integer equality check (`Int.decEq`, avoiding `Int.instBEq`
    which goes through `Std.LinearOrderPackage.ofLE`). -/
def intEqBool (x y : Int) : Bool := decide (x = y)

private theorem intEqBool_true (x : Int) : intEqBool x x = true :=
  decide_eq_true rfl

private theorem intEqBool_false {x y : Int} (h : x ≠ y) : intEqBool x y = false :=
  decide_eq_false h

/-- Executable Boolean checker for `inMldsaSafeBox` (`0 Classical.choice`). -/
def inMldsaSafeBoxBool (gamma1 beta : Nat) (z : Int) : Bool :=
  decide (-(gamma1 : Int) + (beta : Int) + 1 ≤ z) &&
  decide (z ≤ (gamma1 : Int) - (beta : Int) - 1)

theorem inMldsaSafeBoxBool_eq_true_iff (gamma1 beta : Nat) (z : Int) :
    inMldsaSafeBoxBool gamma1 beta z = true ↔ inMldsaSafeBox gamma1 beta z := by
  unfold inMldsaSafeBoxBool inMldsaSafeBox
  rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]

theorem inMldsaSafeBoxBool_eq_false_iff (gamma1 beta : Nat) (z : Int) :
    inMldsaSafeBoxBool gamma1 beta z = false ↔ ¬ inMldsaSafeBox gamma1 beta z := by
  cases h : inMldsaSafeBoxBool gamma1 beta z
  · exact ⟨fun _ hSafe => Bool.noConfusion (h.symm.trans ((inMldsaSafeBoxBool_eq_true_iff gamma1 beta z).mpr hSafe)),
           fun _ => rfl⟩
  · exact ⟨fun hF => Bool.noConfusion hF,
           fun hNot => False.elim (hNot ((inMldsaSafeBoxBool_eq_true_iff gamma1 beta z).mp h))⟩

/-- Surviving mask preimage multiplicity for `zTarget` when `y` ranges uniformly over
    `[-gamma1 + 1, gamma1 - 1]` and outputs `z = y + c_s1` conditioned on `z ∈ SafeBox`. -/
def mldsaSurvivingPreimageCount (gamma1 beta : Nat) (c_s1 zTarget : Int) : Nat :=
  qsum (mldsaMaskIntervalCard gamma1) (fun i =>
    let z := decodeMldsaMask gamma1 i + c_s1
    if inMldsaSafeBoxBool gamma1 beta z && intEqBool z zTarget then 1 else 0)

/-- Total number of masks `y ∈ [-gamma1 + 1, gamma1 - 1]` surviving `y + c_s1 ∈ SafeBox`. -/
def mldsaTotalSurvivingMasks (gamma1 beta : Nat) (c_s1 : Int) : Nat :=
  qsum (mldsaMaskIntervalCard gamma1) (fun i =>
    if inMldsaSafeBoxBool gamma1 beta (decodeMldsaMask gamma1 i + c_s1) then 1 else 0)

/-- Explicit `SimpleEquiv` bijection between the safe output box `Fin (2*(gamma1 - beta) - 1)`
    and the subtype of surviving masks `y ∈ [-gamma1 + 1, gamma1 - 1]` for any `c_s1` with
    `‖c_s1‖_∞ ≤ beta`. -/
def mldsaSurvivingMaskEquiv {gamma1 beta : Nat} (hLt : beta < gamma1)
    (c_s1 : Int) (hSecret : inMldsaSecretBound beta c_s1) :
    SimpleEquiv (Fin (mldsaSafeBoxCard gamma1 beta))
      { i : Fin (mldsaMaskIntervalCard gamma1) //
        inMldsaSafeBox gamma1 beta (decodeMldsaMask gamma1 i + c_s1) } where
  toFun j :=
    let z := decodeMldsaSafeBox gamma1 beta j
    let hz := (encode_decodeMldsaSafeBox hLt j).1
    let hy := safeBox_sub_secret_in_maskInterval hSecret hz
    let i := encodeMldsaMask (by omega) (z - c_s1) hy
    ⟨i, by
      have hDec := decode_encodeMldsaMask (by omega) (z - c_s1) hy
      have hAdd : decodeMldsaMask gamma1 i + c_s1 = z := by
        change decodeMldsaMask gamma1 (encodeMldsaMask _ (z - c_s1) hy) + c_s1 = z
        rw [hDec]; omega
      rwa [hAdd]⟩
  invFun sub := encodeMldsaSafeBox hLt (decodeMldsaMask gamma1 sub.1 + c_s1) sub.2
  left_inv j := by
    apply Fin.ext
    dsimp only [encodeMldsaSafeBox]
    let z := decodeMldsaSafeBox gamma1 beta j
    let hz := (encode_decodeMldsaSafeBox hLt j).1
    let hy := safeBox_sub_secret_in_maskInterval hSecret hz
    have hDec := decode_encodeMldsaMask (by omega) (z - c_s1) hy
    have hAdd : decodeMldsaMask gamma1 (encodeMldsaMask (by omega) (z - c_s1) hy) + c_s1 = z := by
      rw [hDec]; omega
    rw [hAdd]
    exact congrArg Fin.val (encode_decodeMldsaSafeBox hLt j).2
  right_inv sub := by
    rcases sub with ⟨i, hi⟩
    apply Subtype.ext
    apply Fin.ext
    dsimp only [encodeMldsaMask]
    have hDecSafe := decode_encodeMldsaSafeBox hLt (decodeMldsaMask gamma1 i + c_s1) hi
    have hSubEq : decodeMldsaSafeBox gamma1 beta (encodeMldsaSafeBox hLt (decodeMldsaMask gamma1 i + c_s1) hi) - c_s1 =
        decodeMldsaMask gamma1 i := by
      rw [hDecSafe]; omega
    rw [hSubEq]
    exact congrArg Fin.val (encode_decodeMldsaMask (by omega) i).2

/-- **Threshold ML-DSA Bounded-Attempt Rejection Independence
    (`mldsa_rejection_valid_output_uniform_in_box`)**:
    Over finite integer interval `[-gamma1 + 1, gamma1 - 1]`, for ANY secret `c_s1` satisfying
    `‖c_s1‖_∞ ≤ beta` (`inMldsaSecretBound beta c_s1`, with `beta < gamma1`):
    1. Every point `zTarget` inside the safe box `[-gamma1 + beta + 1, gamma1 - beta - 1]` has
       **exact preimage multiplicity `1`** (`mldsaSurvivingPreimageCount gamma1 beta c_s1 zTarget = 1`).
    2. Every point `zTarget` outside `[-gamma1 + beta + 1, gamma1 - beta - 1]` has
       **exact preimage multiplicity `0`**.
    3. Total surviving mask count is identically `2 * (gamma1 - beta) - 1` (`mldsaSafeBoxCard gamma1 beta`),
       completely independent of `c_s1`.
    4. For ANY second valid secret `c_s1'` (`inMldsaSecretBound beta c_s1'`), the surviving output
       counts coincide pointwise at EVERY integer `z : Int` (`SD = 0`, zero secret leakage!). -/
theorem mldsa_rejection_valid_output_uniform_in_box
    {gamma1 beta : Nat} (hLt : beta < gamma1)
    (c_s1 : Int) (hSecret : inMldsaSecretBound beta c_s1) :
    (∀ zTarget : Int,
      inMldsaSafeBox gamma1 beta zTarget →
      mldsaSurvivingPreimageCount gamma1 beta c_s1 zTarget = 1) ∧
    (∀ zOutside : Int,
      ¬ inMldsaSafeBox gamma1 beta zOutside →
      mldsaSurvivingPreimageCount gamma1 beta c_s1 zOutside = 0) ∧
    mldsaTotalSurvivingMasks gamma1 beta c_s1 = mldsaSafeBoxCard gamma1 beta ∧
    (∀ c_s1' : Int, inMldsaSecretBound beta c_s1' →
      ∀ z : Int,
        mldsaSurvivingPreimageCount gamma1 beta c_s1 z =
          mldsaSurvivingPreimageCount gamma1 beta c_s1' z) := by
  have hGammaPos : 0 < gamma1 := by omega
  have hInsideGen : ∀ (cs : Int), inMldsaSecretBound beta cs → ∀ zTarget : Int,
      inMldsaSafeBox gamma1 beta zTarget →
      mldsaSurvivingPreimageCount gamma1 beta cs zTarget = 1 := by
    intro cs hSecCs zTarget hzSafe
    unfold mldsaSurvivingPreimageCount
    have hyStar := safeBox_sub_secret_in_maskInterval hSecCs hzSafe
    let iStar := encodeMldsaMask hGammaPos (zTarget - cs) hyStar
    have hDecStar := decode_encodeMldsaMask hGammaPos (zTarget - cs) hyStar
    have hCong :
        qsum (mldsaMaskIntervalCard gamma1) (fun i =>
          if inMldsaSafeBoxBool gamma1 beta (decodeMldsaMask gamma1 i + cs) &&
              intEqBool (decodeMldsaMask gamma1 i + cs) zTarget then 1 else 0) =
        qsum (mldsaMaskIntervalCard gamma1) (fun i => if i = iStar then 1 else 0) := by
      apply qsum_congr
      intro i
      by_cases hEq : i = iStar
      · subst hEq
        have hSum : decodeMldsaMask gamma1 iStar + cs = zTarget := by
          change decodeMldsaMask gamma1 (encodeMldsaMask hGammaPos (zTarget - cs) hyStar) + cs = zTarget
          rw [hDecStar]; omega
        have hSafeB : inMldsaSafeBoxBool gamma1 beta zTarget = true :=
          (inMldsaSafeBoxBool_eq_true_iff gamma1 beta zTarget).mpr hzSafe
        have hBeq : intEqBool zTarget zTarget = true := intEqBool_true zTarget
        rw [hSum, hSafeB, hBeq]
        simp only [Bool.and_self, ↓reduceIte]
      · have hNeSum : decodeMldsaMask gamma1 i + cs ≠ zTarget := by
          intro hSumEq
          apply hEq
          have hYEq : decodeMldsaMask gamma1 i = zTarget - cs := by omega
          have hEncI := (encode_decodeMldsaMask hGammaPos i).2
          apply Fin.ext
          have hValEq : (encodeMldsaMask hGammaPos (decodeMldsaMask gamma1 i)
              (encode_decodeMldsaMask hGammaPos i).1).val = iStar.val := by
            simp only [iStar, encodeMldsaMask, hYEq]
          exact (congrArg Fin.val hEncI).symm.trans hValEq
        have hBeqF : intEqBool (decodeMldsaMask gamma1 i + cs) zTarget = false := intEqBool_false hNeSum
        rw [hBeqF, Bool.and_false]
        simp only [hEq, ↓reduceIte]
        rfl
    rw [hCong, qsum_eq_indicator]
  have hOutsideGen : ∀ (cs : Int) (zOutside : Int),
      ¬ inMldsaSafeBox gamma1 beta zOutside →
      mldsaSurvivingPreimageCount gamma1 beta cs zOutside = 0 := by
    intro cs zOutside hzNot
    unfold mldsaSurvivingPreimageCount
    have hCong :
        qsum (mldsaMaskIntervalCard gamma1) (fun i =>
          if inMldsaSafeBoxBool gamma1 beta (decodeMldsaMask gamma1 i + cs) &&
              intEqBool (decodeMldsaMask gamma1 i + cs) zOutside then 1 else 0) =
        qsum (mldsaMaskIntervalCard gamma1) (fun _ => 0) := by
      apply qsum_congr
      intro i
      match Int.decEq (decodeMldsaMask gamma1 i + cs) zOutside with
      | isTrue hEqZ =>
        have hSafeF : inMldsaSafeBoxBool gamma1 beta zOutside = false :=
          (inMldsaSafeBoxBool_eq_false_iff gamma1 beta zOutside).mpr hzNot
        rw [hEqZ, hSafeF, Bool.false_and]
        rfl
      | isFalse hNeZ =>
        have hBeqF : intEqBool (decodeMldsaMask gamma1 i + cs) zOutside = false := intEqBool_false hNeZ
        rw [hBeqF, Bool.and_false]
        rfl
    rw [hCong, qsum_const, Nat.mul_zero]
  have hInside := hInsideGen c_s1 hSecret
  have hOutside := hOutsideGen c_s1
  have hTotal : mldsaTotalSurvivingMasks gamma1 beta c_s1 = mldsaSafeBoxCard gamma1 beta := by
    unfold mldsaTotalSurvivingMasks
    have hExpand :
        qsum (mldsaMaskIntervalCard gamma1) (fun i =>
          if inMldsaSafeBoxBool gamma1 beta (decodeMldsaMask gamma1 i + c_s1) then 1 else 0) =
        qsum (mldsaMaskIntervalCard gamma1) (fun i =>
          qsum (mldsaSafeBoxCard gamma1 beta) (fun j =>
            if inMldsaSafeBoxBool gamma1 beta (decodeMldsaMask gamma1 i + c_s1) &&
                intEqBool (decodeMldsaMask gamma1 i + c_s1) (decodeMldsaSafeBox gamma1 beta j) then 1 else 0)) := by
      apply qsum_congr
      intro i
      let z := decodeMldsaMask gamma1 i + c_s1
      change (if inMldsaSafeBoxBool gamma1 beta z then 1 else 0) =
        qsum (mldsaSafeBoxCard gamma1 beta) (fun j =>
          if inMldsaSafeBoxBool gamma1 beta z && intEqBool z (decodeMldsaSafeBox gamma1 beta j) then 1 else 0)
      cases hSafeB : inMldsaSafeBoxBool gamma1 beta z
      · have hZero :
            qsum (mldsaSafeBoxCard gamma1 beta) (fun j =>
              if false && intEqBool z (decodeMldsaSafeBox gamma1 beta j) then 1 else 0) =
            qsum (mldsaSafeBoxCard gamma1 beta) (fun _ => 0) :=
          qsum_congr (fun _ => rfl)
        rw [hZero, qsum_const, Nat.mul_zero]
        rfl
      · have hz : inMldsaSafeBox gamma1 beta z :=
          (inMldsaSafeBoxBool_eq_true_iff gamma1 beta z).mp hSafeB
        let jStar := encodeMldsaSafeBox hLt z hz
        have hDecJ := decode_encodeMldsaSafeBox hLt z hz
        have hInner :
            qsum (mldsaSafeBoxCard gamma1 beta) (fun j =>
              if true && intEqBool z (decodeMldsaSafeBox gamma1 beta j) then 1 else 0) =
            qsum (mldsaSafeBoxCard gamma1 beta) (fun j => if j = jStar then 1 else 0) := by
          apply qsum_congr
          intro j
          by_cases hj : j = jStar
          · subst hj
            have hBeq : intEqBool z (decodeMldsaSafeBox gamma1 beta jStar) = true := by
              change intEqBool z (decodeMldsaSafeBox gamma1 beta (encodeMldsaSafeBox hLt z hz)) = true
              rw [hDecJ]
              exact intEqBool_true z
            rw [hBeq]
            simp only [Bool.true_and, ↓reduceIte]
          · have hNeZ : z ≠ decodeMldsaSafeBox gamma1 beta j := by
              intro hZEq
              apply hj
              have hEncJ := (encode_decodeMldsaSafeBox hLt j).2
              apply Fin.ext
              have hVal : jStar.val = (encodeMldsaSafeBox hLt (decodeMldsaSafeBox gamma1 beta j)
                  (encode_decodeMldsaSafeBox hLt j).1).val := by
                simp only [jStar, encodeMldsaSafeBox, hZEq]
              exact (congrArg Fin.val hEncJ).symm.trans hVal.symm
            have hBeqF : intEqBool z (decodeMldsaSafeBox gamma1 beta j) = false := intEqBool_false hNeZ
            rw [hBeqF]
            simp only [Bool.true_and, hj, ↓reduceIte]
            rfl
        rw [hInner, qsum_eq_indicator]
        rfl
    rw [hExpand, qsum_comm]
    have hInnerOne :
        qsum (mldsaSafeBoxCard gamma1 beta) (fun j =>
          qsum (mldsaMaskIntervalCard gamma1) (fun i =>
            if inMldsaSafeBoxBool gamma1 beta (decodeMldsaMask gamma1 i + c_s1) &&
                intEqBool (decodeMldsaMask gamma1 i + c_s1) (decodeMldsaSafeBox gamma1 beta j) then 1 else 0)) =
        qsum (mldsaSafeBoxCard gamma1 beta) (fun _ => 1) := by
      apply qsum_congr
      intro j
      exact hInside (decodeMldsaSafeBox gamma1 beta j) (encode_decodeMldsaSafeBox hLt j).1
    rw [hInnerOne, qsum_const, Nat.mul_one]
  refine ⟨hInside, hOutside, hTotal, ?_⟩
  intro c_s1' hSecret' z
  cases hSafeB : inMldsaSafeBoxBool gamma1 beta z
  · have hzNot : ¬ inMldsaSafeBox gamma1 beta z :=
      (inMldsaSafeBoxBool_eq_false_iff gamma1 beta z).mp hSafeB
    rw [hOutside z hzNot, hOutsideGen c_s1' z hzNot]
  · have hzIn : inMldsaSafeBox gamma1 beta z :=
      (inMldsaSafeBoxBool_eq_true_iff gamma1 beta z).mp hSafeB
    rw [hInside z hzIn, hInsideGen c_s1' hSecret' z hzIn]

/-- Deployed FIPS 204 `ML-DSA-44` (`γ₁ = 131072, β = 78`) rejection uniformity specialization. -/
theorem mldsa44_rejection_valid_output_uniform_in_box
    (c_s1 : Int) (hSecret : inMldsaSecretBound mldsa44Beta c_s1) :
    (∀ zTarget : Int,
      inMldsaSafeBox mldsa44Gamma1 mldsa44Beta zTarget →
      mldsaSurvivingPreimageCount mldsa44Gamma1 mldsa44Beta c_s1 zTarget = 1) ∧
    (∀ zOutside : Int,
      ¬ inMldsaSafeBox mldsa44Gamma1 mldsa44Beta zOutside →
      mldsaSurvivingPreimageCount mldsa44Gamma1 mldsa44Beta c_s1 zOutside = 0) ∧
    mldsaTotalSurvivingMasks mldsa44Gamma1 mldsa44Beta c_s1 = 261987 := by
  have hLt : mldsa44Beta < mldsa44Gamma1 := by decide
  obtain ⟨hIn, hOut, hTot, _⟩ := mldsa_rejection_valid_output_uniform_in_box hLt c_s1 hSecret
  refine ⟨hIn, hOut, ?_⟩
  rw [hTot]
  rfl

/-- Coordinatewise `∞`-norm polynomial/vector bijection lifting `mldsaSurvivingMaskEquiv` to
    `dim`-coefficient ML-DSA vectors `Fin dim → Int`. -/
def mldsaVecSurvivingMaskEquiv {dim gamma1 beta : Nat} (hLt : beta < gamma1)
    (c_s1_vec : Fin dim → Int) (hSecretVec : ∀ k : Fin dim, inMldsaSecretBound beta (c_s1_vec k)) :
    SimpleEquiv (Fin dim → Fin (mldsaSafeBoxCard gamma1 beta))
      { yVec : Fin dim → Fin (mldsaMaskIntervalCard gamma1) //
        ∀ k : Fin dim, inMldsaSafeBox gamma1 beta (decodeMldsaMask gamma1 (yVec k) + c_s1_vec k) } where
  toFun jVec :=
    ⟨fun k => ((mldsaSurvivingMaskEquiv hLt (c_s1_vec k) (hSecretVec k)).toFun (jVec k)).1,
     fun k => ((mldsaSurvivingMaskEquiv hLt (c_s1_vec k) (hSecretVec k)).toFun (jVec k)).2⟩
  invFun subVec :=
    fun k => (mldsaSurvivingMaskEquiv hLt (c_s1_vec k) (hSecretVec k)).invFun ⟨subVec.1 k, subVec.2 k⟩
  left_inv jVec := by
    funext k
    exact (mldsaSurvivingMaskEquiv hLt (c_s1_vec k) (hSecretVec k)).left_inv (jVec k)
  right_inv subVec := by
    rcases subVec with ⟨yVec, hSafe⟩
    apply Subtype.ext
    funext k
    exact congrArg Subtype.val
      ((mldsaSurvivingMaskEquiv hLt (c_s1_vec k) (hSecretVec k)).right_inv ⟨yVec k, hSafe k⟩)

/-! ### Unclipped ML-DSA Output `#tooth` Secret-Leakage Witness -/

/-- Unclipped preimage multiplicity when a broken signer omits the `< gamma1 - beta` rejection
    check and outputs `z = y + c_s1` directly. -/
def mldsaUnclippedPreimageCount (gamma1 : Nat) (c_s1 zTarget : Int) : Nat :=
  qsum (mldsaMaskIntervalCard gamma1) (fun i =>
    if intEqBool (decodeMldsaMask gamma1 i + c_s1) zTarget then 1 else 0)

/-- Deployed `ML-DSA-44` (`gamma1 = 131072, beta = 78`) boundary leakage equality without the
    `< gamma1 - beta` rejection filter: `z = 131072` occurs with multiplicity `1` under valid
    secret `c_s1 = 1` and multiplicity `0` under valid secret `c_s1' = 0`. -/
theorem tooth_mldsa44_unclipped_boundary_counts :
    inMldsaSecretBound mldsa44Beta 1 ∧
    inMldsaSecretBound mldsa44Beta 0 ∧
    mldsaUnclippedPreimageCount mldsa44Gamma1 1 (mldsa44Gamma1 : Int) = 1 ∧
    mldsaUnclippedPreimageCount mldsa44Gamma1 0 (mldsa44Gamma1 : Int) = 0 ∧
    mldsaUnclippedPreimageCount mldsa44Gamma1 1 (mldsa44Gamma1 : Int) ≠
      mldsaUnclippedPreimageCount mldsa44Gamma1 0 (mldsa44Gamma1 : Int) := by
  have hPos : 0 < mldsa44Gamma1 := by decide
  have hB1 : inMldsaSecretBound mldsa44Beta 1 := by decide
  have hB0 : inMldsaSecretBound mldsa44Beta 0 := by decide
  have hOne : mldsaUnclippedPreimageCount mldsa44Gamma1 1 (mldsa44Gamma1 : Int) = 1 := by
    unfold mldsaUnclippedPreimageCount
    have hyMax : inMldsaMaskInterval mldsa44Gamma1 ((mldsa44Gamma1 : Int) - 1) := by decide
    let iMax := encodeMldsaMask hPos ((mldsa44Gamma1 : Int) - 1) hyMax
    have hDecMax := decode_encodeMldsaMask hPos ((mldsa44Gamma1 : Int) - 1) hyMax
    have hCong :
        qsum (mldsaMaskIntervalCard mldsa44Gamma1) (fun i =>
          if intEqBool (decodeMldsaMask mldsa44Gamma1 i + 1) (mldsa44Gamma1 : Int) then 1 else 0) =
        qsum (mldsaMaskIntervalCard mldsa44Gamma1) (fun i => if i = iMax then 1 else 0) := by
      apply qsum_congr
      intro i
      by_cases hEq : i = iMax
      · subst hEq
        have hVal : decodeMldsaMask mldsa44Gamma1 iMax + 1 = (mldsa44Gamma1 : Int) := by
          change decodeMldsaMask mldsa44Gamma1 (encodeMldsaMask hPos ((mldsa44Gamma1 : Int) - 1) hyMax) + 1 = _
          rw [hDecMax]; omega
        have hBeq : intEqBool (mldsa44Gamma1 : Int) (mldsa44Gamma1 : Int) = true := intEqBool_true _
        rw [hVal, hBeq]
        simp only [↓reduceIte]
      · have hNe : decodeMldsaMask mldsa44Gamma1 i + 1 ≠ (mldsa44Gamma1 : Int) := by
          intro hSum
          apply hEq
          have hY : decodeMldsaMask mldsa44Gamma1 i = (mldsa44Gamma1 : Int) - 1 := by omega
          have hEncI := (encode_decodeMldsaMask hPos i).2
          apply Fin.ext
          have hV : (encodeMldsaMask hPos (decodeMldsaMask mldsa44Gamma1 i)
              (encode_decodeMldsaMask hPos i).1).val = iMax.val := by
            simp only [iMax, encodeMldsaMask, hY]
          exact (congrArg Fin.val hEncI).symm.trans hV
        have hBeqF : intEqBool (decodeMldsaMask mldsa44Gamma1 i + 1) (mldsa44Gamma1 : Int) = false :=
          intEqBool_false hNe
        rw [hBeqF]
        simp only [hEq, ↓reduceIte]
        rfl
    rw [hCong, qsum_eq_indicator]
  have hZero : mldsaUnclippedPreimageCount mldsa44Gamma1 0 (mldsa44Gamma1 : Int) = 0 := by
    unfold mldsaUnclippedPreimageCount
    have hCong :
        qsum (mldsaMaskIntervalCard mldsa44Gamma1) (fun i =>
          if intEqBool (decodeMldsaMask mldsa44Gamma1 i + 0) (mldsa44Gamma1 : Int) then 1 else 0) =
        qsum (mldsaMaskIntervalCard mldsa44Gamma1) (fun _ => 0) := by
      apply qsum_congr
      intro i
      have hiBound := (encode_decodeMldsaMask hPos i).1
      have hNe : decodeMldsaMask mldsa44Gamma1 i + 0 ≠ (mldsa44Gamma1 : Int) := by
        unfold inMldsaMaskInterval at hiBound
        omega
      have hBeqF : intEqBool (decodeMldsaMask mldsa44Gamma1 i + 0) (mldsa44Gamma1 : Int) = false :=
        intEqBool_false hNe
      rw [hBeqF]
      rfl
    rw [hCong, qsum_const, Nat.mul_zero]
  refine ⟨hB1, hB0, hOne, hZero, ?_⟩
  rw [hOne, hZero]
  decide

/-- **`#tooth` Witness (`tooth_mldsa_unclipped_z_leaks_secret_shift`)**:
    Omitting the `‖z‖_∞ < gamma1 - beta` rejection filter leaks `c_s1` immediately at the boundary
    `z = gamma1` (instantiated at deployed `ML-DSA-44` parameters `gamma1 = 131072, beta = 78`):
    valid secrets `c_s1, c_s1'` satisfying `‖c_s1‖_∞ ≤ beta` yield strictly unequal preimage
    multiplicities at `z`! -/
theorem tooth_mldsa_unclipped_z_leaks_secret_shift :
    ∃ (gamma1 beta : Nat) (c_s1 c_s1' z : Int),
      gamma1 = mldsa44Gamma1 ∧
      beta = mldsa44Beta ∧
      beta < gamma1 ∧
      inMldsaSecretBound beta c_s1 ∧
      inMldsaSecretBound beta c_s1' ∧
      mldsaUnclippedPreimageCount gamma1 c_s1 z ≠
        mldsaUnclippedPreimageCount gamma1 c_s1' z := by
  obtain ⟨hB1, hB0, _, _, hNe⟩ := tooth_mldsa44_unclipped_boundary_counts
  exact ⟨mldsa44Gamma1, mldsa44Beta, 1, 0, (mldsa44Gamma1 : Int), rfl, rfl, by decide, hB1, hB0, hNe⟩

/-- Reachable inhabitedness witness for `mldsa_rejection_valid_output_uniform_in_box` at deployed
    `ML-DSA-44` parameters (`c_s1 = -78`, extreme boundary secret shift!). -/
theorem witness_mldsa44_secret_bound_inhabited :
    ∃ (c_s1 : Int),
      inMldsaSecretBound mldsa44Beta c_s1 ∧
      inMldsaSafeBox mldsa44Gamma1 mldsa44Beta 0 ∧ mldsa44Beta < mldsa44Gamma1 :=
  ⟨-78, by decide, by decide, by decide⟩


/-! ### FIPS 204 Joint `(z, r₀)` Rejection: `HighBits` Invariance & `(w₁, z)` Transcript Simulation

The `z`-box theorem above covers only the first of the two secret-dependent rejection checks of
FIPS 204 `ML-DSA.Sign`. The signer ALSO rejects unless `‖LowBits(w - c·s₂)‖_∞ < γ₂ - β`, and the
published commitment is `w₁ = HighBits(w)` with `w = A·y`. This subsection models both checks and
the commitment at the deployed `ML-DSA-44` parameters
(`q = 8380417`, `γ₂ = (q - 1)/88 = 95232`, `α = 2γ₂ = 190464`, `β = 78`, `γ₂ - β = 95154`).

Vectors are coefficient vectors over `ℤ` read modulo `q`. A public matrix `A` over `R_q` acting on
polynomial vectors, and multiplication by the challenge `c`, are both `ℤ_q`-linear on coefficient
vectors, so the scheme is the special case `m = 256·ℓ`, `kk = 256·k` of the integer-matrix model
below, with the challenge already folded into `cs₁ = c·s₁`, `cs₂ = c·s₂` and `ct = c·t`. -/

/-- Centered remainder `x mod± α` in `(-γ₂, γ₂]` for `α = 190464`, `γ₂ = 95232`. -/
def mldsa44CenteredRem (x : Int) : Int :=
  if x % 190464 > 95232 then x % 190464 - 190464 else x % 190464

/-- FIPS 204 Algorithm 37 `HighBits` at `ML-DSA-44` (first component of Algorithm 36 `Decompose`,
    including the corner `r⁺ - r₀ = q - 1 ↦ r₁ = 0`), on `r mod q`. Mirrors `decompose_ct`. -/
def mldsa44HighBits (r : Int) : Int :=
  if r % 8380417 - mldsa44CenteredRem (r % 8380417) = 8380416 then 0
  else (r % 8380417 - mldsa44CenteredRem (r % 8380417)) / 190464

/-- FIPS 204 Algorithm 38 `LowBits` at `ML-DSA-44` (second component of `Decompose`, including
    the corner `r₀ ↦ r₀ - 1`), on `r mod q`. -/
def mldsa44LowBits (r : Int) : Int :=
  if r % 8380417 - mldsa44CenteredRem (r % 8380417) = 8380416 then
    mldsa44CenteredRem (r % 8380417) - 1
  else mldsa44CenteredRem (r % 8380417)

/-- The second rejection check with its `β` margin: `|r₀| < γ₂ - β = 95154`. -/
abbrev mldsa44LowBitsOk (r0 : Int) : Prop := -95154 < r0 ∧ r0 < 95154

/-- The same check WITHOUT the `β` margin: `|r₀| < γ₂ = 95232`. -/
abbrev mldsa44LowBitsOkNoMargin (r0 : Int) : Prop := -95232 < r0 ∧ r0 < 95232

theorem mldsa44HighBits_congr {r r' : Int} (h : r % 8380417 = r' % 8380417) :
    mldsa44HighBits r = mldsa44HighBits r' := by
  simp only [mldsa44HighBits, h]

theorem mldsa44LowBits_congr {r r' : Int} (h : r % 8380417 = r' % 8380417) :
    mldsa44LowBits r = mldsa44LowBits r' := by
  simp only [mldsa44LowBits, h]

/-- **`HighBits` Invariance Under a `β`-Bounded Shift (`mldsa44_highBits_shift_invariant`)**:
    if `‖LowBits(r)‖ < γ₂ - β` and `|s| ≤ β`, then `HighBits(r + s) = HighBits(r)`. The `β` margin
    keeps `r + s` on the same side of every `HighBits` carry boundary, including the wrap of
    `r + s` around `q` at the `r₁ = 0` corner. -/
theorem mldsa44_highBits_shift_invariant (r s : Int)
    (hs : -78 ≤ s ∧ s ≤ 78) (hLow : mldsa44LowBitsOk (mldsa44LowBits r)) :
    mldsa44HighBits (r + s) = mldsa44HighBits r := by
  unfold mldsa44LowBitsOk mldsa44LowBits mldsa44CenteredRem at hLow
  unfold mldsa44HighBits mldsa44CenteredRem
  have hx : 0 ≤ r % 8380417 ∧ r % 8380417 < 8380417 := ⟨by omega, by omega⟩
  have hx' : 0 ≤ (r + s) % 8380417 ∧ (r + s) % 8380417 < 8380417 := ⟨by omega, by omega⟩
  have hWrap : (r + s) % 8380417 = r % 8380417 + s ∨
      (r + s) % 8380417 = r % 8380417 + s - 8380417 ∨
      (r + s) % 8380417 = r % 8380417 + s + 8380417 := by omega
  generalize (r + s) % 8380417 = x' at hx' hWrap ⊢
  generalize r % 8380417 = x at hx hWrap hLow ⊢
  by_cases c1 : x % 190464 > 95232
  · by_cases c3 : x' % 190464 > 95232
    · simp only [c1, c3, ↓reduceIte] at hLow ⊢
      split at hLow <;> split <;> omega
    · simp only [c1, c3, ↓reduceIte] at hLow ⊢
      split at hLow <;> split <;> omega
  · by_cases c3 : x' % 190464 > 95232
    · simp only [c1, c3, ↓reduceIte] at hLow ⊢
      split at hLow <;> split <;> omega
    · simp only [c1, c3, ↓reduceIte] at hLow ⊢
      split at hLow <;> split <;> omega

/-- **Deployed Range Test Refines The Spec (`mldsa44_low_range_test_iff`)**:
    the threshold signer never materialises `LowBits`. It tests the hidden value
    `(w - c·s₂ - w₁·α) + (γ₂ - β - 1) mod q` for membership in `[0, 2(γ₂ - β) - 1)`
    (`rejection_verdict` / `masked_range_test`). For every candidate `w₁ ∈ [0, 44)` that test holds
    exactly when `HighBits(w - c·s₂) = w₁` AND `‖LowBits(w - c·s₂)‖ < γ₂ - β`. -/
theorem mldsa44_low_range_test_iff (r w1 : Int) (hw1 : 0 ≤ w1 ∧ w1 < 44) :
    ((r - w1 * 190464 + 95153) % 8380417 < 190307) ↔
    (mldsa44HighBits r = w1 ∧ mldsa44LowBitsOk (mldsa44LowBits r)) := by
  unfold mldsa44LowBitsOk mldsa44HighBits mldsa44LowBits mldsa44CenteredRem
  have hx : 0 ≤ r % 8380417 ∧ r % 8380417 < 8380417 := ⟨by omega, by omega⟩
  have ht : 0 ≤ (r - w1 * 190464 + 95153) % 8380417 ∧
      (r - w1 * 190464 + 95153) % 8380417 < 8380417 := ⟨by omega, by omega⟩
  have hWrap : (r - w1 * 190464 + 95153) % 8380417 = r % 8380417 - w1 * 190464 + 95153 ∨
      (r - w1 * 190464 + 95153) % 8380417 = r % 8380417 - w1 * 190464 + 95153 + 8380417 ∨
      (r - w1 * 190464 + 95153) % 8380417 = r % 8380417 - w1 * 190464 + 95153 - 8380417 := by
    omega
  generalize (r - w1 * 190464 + 95153) % 8380417 = t at ht hWrap ⊢
  generalize r % 8380417 = x at hx hWrap ⊢
  by_cases c1 : x % 190464 > 95232
  · simp only [c1, ↓reduceIte]
    split
    · constructor
      · intro h; refine ⟨?_, ?_, ?_⟩ <;> omega
      · intro h; omega
    · constructor
      · intro h; refine ⟨?_, ?_, ?_⟩ <;> omega
      · intro h; omega
  · simp only [c1, ↓reduceIte]
    split
    · constructor
      · intro h; refine ⟨?_, ?_, ?_⟩ <;> omega
      · intro h; omega
    · constructor
      · intro h; refine ⟨?_, ?_, ?_⟩ <;> omega
      · intro h; omega

/-- Integer dot product `Σ_j a_j · u_j`. -/
def intDot : (n : Nat) → (Fin n → Int) → (Fin n → Int) → Int
  | 0, _, _ => 0
  | n + 1, a, u =>
    a ⟨0, Nat.zero_lt_succ n⟩ * u ⟨0, Nat.zero_lt_succ n⟩ +
      intDot n (fun j => a ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
        (fun j => u ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)

theorem intDot_add : ∀ (n : Nat) (a u v : Fin n → Int),
    intDot n a (fun j => u j + v j) = intDot n a u + intDot n a v
  | 0, _, _, _ => by simp [intDot]
  | n + 1, a, u, v => by
    have ih := intDot_add n (fun j => a ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
      (fun j => u ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩) (fun j => v ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
    simp only [intDot]
    rw [ih, Int.mul_add]
    omega

/-- Public data of one signing attempt for a fixed challenge `c`: the matrix `A` (as a
    `ℤ_q`-linear map on coefficient vectors) and `ct = c·t`. -/
structure MldsaPublicInstance (m kk : Nat) where
  A : Fin kk → Fin m → Int
  ct : Fin kk → Int

/-- Secret data of the attempt: `cs₁ = c·s₁` and `cs₂ = c·s₂`. -/
structure MldsaSecretShift (m kk : Nat) where
  cs1 : Fin m → Int
  cs2 : Fin kk → Int

/-- The public-key relation `t = A·s₁ + s₂ (mod q)` multiplied by the challenge, together with
    the FIPS 204 bounds `‖c·s₁‖_∞ ≤ β` and `‖c·s₂‖_∞ ≤ β`. -/
def MldsaKeyRelation {m kk : Nat} (pub : MldsaPublicInstance m kk) (sec : MldsaSecretShift m kk) :
    Prop :=
  (∀ j, inMldsaSecretBound mldsa44Beta (sec.cs1 j)) ∧
  (∀ i, inMldsaSecretBound mldsa44Beta (sec.cs2 i)) ∧
  (∀ i, pub.ct i % 8380417 = (intDot m (pub.A i) sec.cs1 + sec.cs2 i) % 8380417)

/-- Real signer response `z = y + c·s₁`. -/
def mldsaRealZ {m kk : Nat} (sec : MldsaSecretShift m kk) (y : Fin m → Int) : Fin m → Int :=
  fun j => y j + sec.cs1 j

/-- Real signer commitment `w₁ = HighBits(A·y)`: computed from the secret mask alone. -/
def mldsa44RealW1 {m kk : Nat} (pub : MldsaPublicInstance m kk) (y : Fin m → Int) : Fin kk → Int :=
  fun i => mldsa44HighBits (intDot m (pub.A i) y)

/-- Both secret-dependent rejection checks of the real signer:
    `‖z‖_∞ < γ₁ - β` and `‖LowBits(A·y - c·s₂)‖_∞ < γ₂ - β`. -/
def mldsa44RealAccept {m kk : Nat} (pub : MldsaPublicInstance m kk) (sec : MldsaSecretShift m kk)
    (y : Fin m → Int) : Prop :=
  (∀ j, inMldsaSafeBox mldsa44Gamma1 mldsa44Beta (y j + sec.cs1 j)) ∧
  (∀ i, mldsa44LowBitsOk (mldsa44LowBits (intDot m (pub.A i) y - sec.cs2 i)))

/-- Simulator commitment `w₁ = HighBits(A·z - c·t)`: a function of PUBLIC `(A, c·t, z)` only. -/
def mldsa44SimW1 {m kk : Nat} (pub : MldsaPublicInstance m kk) (z : Fin m → Int) : Fin kk → Int :=
  fun i => mldsa44HighBits (intDot m (pub.A i) z - pub.ct i)

/-- Simulator acceptance: `z` in the safe box and `‖LowBits(A·z - c·t)‖_∞ < γ₂ - β`, again a
    function of PUBLIC `(A, c·t, z)` only. -/
def mldsa44SimAccept {m kk : Nat} (pub : MldsaPublicInstance m kk) (z : Fin m → Int) : Prop :=
  (∀ j, inMldsaSafeBox mldsa44Gamma1 mldsa44Beta (z j)) ∧
  (∀ i, mldsa44LowBitsOk (mldsa44LowBits (intDot m (pub.A i) z - pub.ct i)))

/-- `A·y - c·s₂ ≡ A·z - c·t (mod q)` for `z = y + c·s₁`: the hidden value whose low bits are
    tested is computable from the public transcript. -/
theorem mldsa_commit_shift_congr {m kk : Nat} (pub : MldsaPublicInstance m kk)
    (sec : MldsaSecretShift m kk) (hKey : MldsaKeyRelation pub sec) (y : Fin m → Int) (i : Fin kk) :
    (intDot m (pub.A i) (mldsaRealZ sec y) - pub.ct i) % 8380417 =
      (intDot m (pub.A i) y - sec.cs2 i) % 8380417 := by
  have hK := hKey.2.2 i
  unfold mldsaRealZ
  rw [intDot_add]
  omega

/-- **FIPS 204 Joint `(w₁, z)` Transcript Simulation (`mldsa44_joint_transcript_simulation`)**:
    for every public instance, every secret satisfying the key relation, and every mask `y`:
    1. the real signer's JOINT accept bit (both rejection checks) equals the simulator's accept
       bit computed from public `(A, c·t, z)`;
    2. on acceptance the real commitment `w₁ = HighBits(A·y)` equals the publicly computable
       `HighBits(A·z - c·t)` in every coefficient;
    3. every simulator-accepted `z` has its unique preimage mask `y = z - c·s₁` inside the mask
       interval.
    Hence the accepted `(w₁, z)` transcript is a function of public data and the uniform `z`
    alone: `(s₁, s₂)` enter neither its support nor its values. -/
theorem mldsa44_joint_transcript_simulation {m kk : Nat} (pub : MldsaPublicInstance m kk)
    (sec : MldsaSecretShift m kk) (hKey : MldsaKeyRelation pub sec) :
    (∀ y : Fin m → Int,
      (mldsa44RealAccept pub sec y ↔ mldsa44SimAccept pub (mldsaRealZ sec y)) ∧
      (mldsa44RealAccept pub sec y →
        ∀ i, mldsa44RealW1 pub y i = mldsa44SimW1 pub (mldsaRealZ sec y) i)) ∧
    (∀ z : Fin m → Int, mldsa44SimAccept pub z →
      ∀ j, inMldsaMaskInterval mldsa44Gamma1 (z j - sec.cs1 j)) := by
  have hLowEq : ∀ (y : Fin m → Int) (i : Fin kk),
      mldsa44LowBits (intDot m (pub.A i) (mldsaRealZ sec y) - pub.ct i) =
        mldsa44LowBits (intDot m (pub.A i) y - sec.cs2 i) :=
    fun y i => mldsa44LowBits_congr (mldsa_commit_shift_congr pub sec hKey y i)
  refine ⟨fun y => ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro hReal
    refine ⟨hReal.1, fun i => ?_⟩
    rw [hLowEq y i]
    exact hReal.2 i
  · intro hSim
    refine ⟨hSim.1, fun i => ?_⟩
    rw [← hLowEq y i]
    exact hSim.2 i
  · intro hReal i
    have hs : -78 ≤ sec.cs2 i ∧ sec.cs2 i ≤ 78 := by
      have h := hKey.2.1 i
      unfold inMldsaSecretBound mldsa44Beta at h
      exact ⟨by omega, by omega⟩
    have hInv := mldsa44_highBits_shift_invariant
      (intDot m (pub.A i) y - sec.cs2 i) (sec.cs2 i) hs (hReal.2 i)
    have hSum : intDot m (pub.A i) y - sec.cs2 i + sec.cs2 i = intDot m (pub.A i) y := by omega
    rw [hSum] at hInv
    unfold mldsa44RealW1 mldsa44SimW1
    rw [hInv]
    exact (mldsa44HighBits_congr (mldsa_commit_shift_congr pub sec hKey y i)).symm
  · intro z hSim j
    exact safeBox_sub_secret_in_maskInterval (hKey.1 j) (hSim.1 j)

/-- **Joint Transcript Bijection (`mldsa44JointTranscriptEquiv`)**: `y ↦ z = y + c·s₁` is an
    explicit bijection from the masks the REAL signer accepts (both checks) onto the responses the
    public SIMULATOR accepts. -/
def mldsa44JointTranscriptEquiv {m kk : Nat} (pub : MldsaPublicInstance m kk)
    (sec : MldsaSecretShift m kk) (hKey : MldsaKeyRelation pub sec) :
    SimpleEquiv
      { y : Fin m → Int //
        (∀ j, inMldsaMaskInterval mldsa44Gamma1 (y j)) ∧ mldsa44RealAccept pub sec y }
      { z : Fin m → Int // mldsa44SimAccept pub z } where
  toFun y :=
    ⟨mldsaRealZ sec y.1, ((mldsa44_joint_transcript_simulation pub sec hKey).1 y.1).1.mp y.2.2⟩
  invFun z :=
    ⟨fun j => z.1 j - sec.cs1 j,
     (mldsa44_joint_transcript_simulation pub sec hKey).2 z.1 z.2,
     ((mldsa44_joint_transcript_simulation pub sec hKey).1 (fun j => z.1 j - sec.cs1 j)).1.mpr (by
       have hEq : mldsaRealZ sec (fun j => z.1 j - sec.cs1 j) = z.1 := by
         funext j
         simp only [mldsaRealZ]
         omega
       rw [hEq]
       exact z.2)⟩
  left_inv y := by
    apply Subtype.ext
    funext j
    show y.1 j + sec.cs1 j - sec.cs1 j = y.1 j
    omega
  right_inv z := by
    apply Subtype.ext
    funext j
    show z.1 j - sec.cs1 j + sec.cs1 j = z.1 j
    omega

/-- The bijection carries the whole real transcript `(w₁, z)` to the simulated one. -/
theorem mldsa44JointTranscriptEquiv_preserves_transcript {m kk : Nat}
    (pub : MldsaPublicInstance m kk) (sec : MldsaSecretShift m kk)
    (hKey : MldsaKeyRelation pub sec)
    (y : { y : Fin m → Int //
      (∀ j, inMldsaMaskInterval mldsa44Gamma1 (y j)) ∧ mldsa44RealAccept pub sec y }) :
    ((mldsa44JointTranscriptEquiv pub sec hKey).toFun y).1 = mldsaRealZ sec y.1 ∧
    (∀ i, mldsa44SimW1 pub ((mldsa44JointTranscriptEquiv pub sec hKey).toFun y).1 i =
      mldsa44RealW1 pub y.1 i) :=
  ⟨rfl, fun i => (((mldsa44_joint_transcript_simulation pub sec hKey).1 y.1).2 y.2.2 i).symm⟩

/-- **Secret Independence Of The Accepted Joint Transcript
    (`mldsa44_joint_transcript_secret_independent`)**: two secrets consistent with the SAME public
    data produce the same accepted transcripts. Every mask `y` accepted under `sec` is matched by
    the mask `y' = y + c·s₁ - c·s₁'` accepted under `sec'`, with identical `z` and identical `w₁`. -/
theorem mldsa44_joint_transcript_secret_independent {m kk : Nat}
    (pub : MldsaPublicInstance m kk) (sec sec' : MldsaSecretShift m kk)
    (hKey : MldsaKeyRelation pub sec) (hKey' : MldsaKeyRelation pub sec')
    (y : Fin m → Int) (hAcc : mldsa44RealAccept pub sec y) :
    (∀ j, inMldsaMaskInterval mldsa44Gamma1 (y j + sec.cs1 j - sec'.cs1 j)) ∧
    mldsa44RealAccept pub sec' (fun j => y j + sec.cs1 j - sec'.cs1 j) ∧
    mldsaRealZ sec' (fun j => y j + sec.cs1 j - sec'.cs1 j) = mldsaRealZ sec y ∧
    (∀ i, mldsa44RealW1 pub (fun j => y j + sec.cs1 j - sec'.cs1 j) i = mldsa44RealW1 pub y i) := by
  obtain ⟨hFwd, _⟩ := mldsa44_joint_transcript_simulation pub sec hKey
  obtain ⟨hFwd', hBack'⟩ := mldsa44_joint_transcript_simulation pub sec' hKey'
  have hZ : mldsaRealZ sec' (fun j => y j + sec.cs1 j - sec'.cs1 j) = mldsaRealZ sec y := by
    funext j
    simp only [mldsaRealZ]
    omega
  have hSim : mldsa44SimAccept pub (mldsaRealZ sec y) := (hFwd y).1.mp hAcc
  have hAcc' : mldsa44RealAccept pub sec' (fun j => y j + sec.cs1 j - sec'.cs1 j) :=
    (hFwd' _).1.mpr (by rw [hZ]; exact hSim)
  refine ⟨fun j => hBack' (mldsaRealZ sec y) hSim j, hAcc', hZ, fun i => ?_⟩
  rw [(hFwd' _).2 hAcc' i, hZ, (hFwd y).2 hAcc i]

/-! ### `γ₂ - β` Margin `#tooth`: A Bare `γ₂` Bound Leaks `s₂` Through `HighBits` -/

/-- Broken joint acceptance that keeps the `z` check but tests the low bits against `γ₂` instead
    of `γ₂ - β`. -/
def mldsa44RealAcceptNoMargin {m kk : Nat} (pub : MldsaPublicInstance m kk)
    (sec : MldsaSecretShift m kk) (y : Fin m → Int) : Prop :=
  (∀ j, inMldsaSafeBox mldsa44Gamma1 mldsa44Beta (y j + sec.cs1 j)) ∧
  (∀ i, mldsa44LowBitsOkNoMargin (mldsa44LowBits (intDot m (pub.A i) y - sec.cs2 i)))

private def toothMldsaPub : MldsaPublicInstance 1 1 where
  A := fun _ _ => 1
  ct := fun _ => 78

private def toothMldsaSecA : MldsaSecretShift 1 1 where
  cs1 := fun _ => 0
  cs2 := fun _ => 78

private def toothMldsaSecB : MldsaSecretShift 1 1 where
  cs1 := fun _ => 78
  cs2 := fun _ => 0

private theorem toothMldsa_keyA : MldsaKeyRelation toothMldsaPub toothMldsaSecA :=
  ⟨fun _ => (by decide : inMldsaSecretBound mldsa44Beta 0),
   fun _ => (by decide : inMldsaSecretBound mldsa44Beta 78),
   fun _ => (by decide :
     (78 : Int) % 8380417 = (intDot 1 (fun _ => 1) (fun _ => 0) + 78) % 8380417)⟩

private theorem toothMldsa_keyB : MldsaKeyRelation toothMldsaPub toothMldsaSecB :=
  ⟨fun _ => (by decide : inMldsaSecretBound mldsa44Beta 78),
   fun _ => (by decide : inMldsaSecretBound mldsa44Beta 0),
   fun _ => (by decide :
     (78 : Int) % 8380417 = (intDot 1 (fun _ => 1) (fun _ => 78) + 0) % 8380417)⟩

private theorem toothMldsa_acceptA :
    mldsa44RealAcceptNoMargin toothMldsaPub toothMldsaSecA (fun _ => 95309) :=
  ⟨fun _ => (by decide : inMldsaSafeBox mldsa44Gamma1 mldsa44Beta (95309 + 0)),
   fun _ => (by decide : mldsa44LowBitsOkNoMargin
     (mldsa44LowBits (intDot 1 (fun _ => 1) (fun _ => 95309) - 78)))⟩

private theorem toothMldsa_acceptB :
    mldsa44RealAcceptNoMargin toothMldsaPub toothMldsaSecB (fun _ => 95231) :=
  ⟨fun _ => (by decide : inMldsaSafeBox mldsa44Gamma1 mldsa44Beta (95231 + 78)),
   fun _ => (by decide : mldsa44LowBitsOkNoMargin
     (mldsa44LowBits (intDot 1 (fun _ => 1) (fun _ => 95231) - 0)))⟩

/-- **`#tooth` Witness (`tooth_mldsa44_low_bits_margin_omitted_leaks_s2`)**:
    with `A = (1)` and `c·t = 78`, the secrets `(c·s₁, c·s₂) = (0, 78)` and `(78, 0)` share the
    public key data. For the public response `z = 95309` both pass the `z` check and the
    margin-free low-bits check (`LowBits(A·z - c·t) = 95231 < γ₂`), yet the published commitment
    is `HighBits(A·y) = 1` under the first secret and `0` under the second: `r₀ = 95231` sits
    within `β` of the carry boundary, so adding `c·s₂ = 78` flips `HighBits`. The transcript
    `(w₁, z)` then distinguishes the two secrets, and `w₁` is no longer a function of public data. -/
theorem tooth_mldsa44_low_bits_margin_omitted_leaks_s2 :
    ∃ (pub : MldsaPublicInstance 1 1) (sec sec' : MldsaSecretShift 1 1) (y y' : Fin 1 → Int),
      MldsaKeyRelation pub sec ∧ MldsaKeyRelation pub sec' ∧
      (∀ j, inMldsaMaskInterval mldsa44Gamma1 (y j)) ∧
      (∀ j, inMldsaMaskInterval mldsa44Gamma1 (y' j)) ∧
      mldsa44RealAcceptNoMargin pub sec y ∧ mldsa44RealAcceptNoMargin pub sec' y' ∧
      (∀ j, mldsaRealZ sec y j = mldsaRealZ sec' y' j) ∧
      mldsa44RealW1 pub y ⟨0, Nat.zero_lt_succ 0⟩ ≠ mldsa44RealW1 pub y' ⟨0, Nat.zero_lt_succ 0⟩ :=
  ⟨toothMldsaPub, toothMldsaSecA, toothMldsaSecB, (fun _ => 95309), (fun _ => 95231),
    toothMldsa_keyA, toothMldsa_keyB,
    (fun _ => (by decide : inMldsaMaskInterval mldsa44Gamma1 95309)),
    (fun _ => (by decide : inMldsaMaskInterval mldsa44Gamma1 95231)),
    toothMldsa_acceptA, toothMldsa_acceptB,
    (fun _ => (by decide : (95309 : Int) + 0 = 95231 + 78)), by decide⟩

/-- Reachable inhabitedness witness for the joint theorem: a real accepted attempt whose hidden
    value `A·y - c·s₂ = -73` lies in the `r₁ = 0` wrap-around corner of `Decompose`. -/
theorem witness_mldsa44_joint_accept_inhabited :
    ∃ (pub : MldsaPublicInstance 1 1) (sec : MldsaSecretShift 1 1) (y : Fin 1 → Int),
      MldsaKeyRelation pub sec ∧
      (∀ j, inMldsaMaskInterval mldsa44Gamma1 (y j)) ∧
      mldsa44RealAccept pub sec y :=
  ⟨toothMldsaPub, toothMldsaSecA, (fun _ => 5), toothMldsa_keyA,
    (fun _ => (by decide : inMldsaMaskInterval mldsa44Gamma1 5)),
    ⟨fun _ => (by decide : inMldsaSafeBox mldsa44Gamma1 mldsa44Beta (5 + 0)),
     fun _ => (by decide : mldsa44LowBitsOk
       (mldsa44LowBits (intDot 1 (fun _ => 1) (fun _ => 5) - 78)))⟩⟩


/-! ## §3b. The Cyclotomic Ring `ℤ_q[X]/(X^n + 1)`, Challenge Ball, Rejected Attempts & ROM Reprogramming

§3 takes `c·s₁`, `c·s₂`, `c·t` as given integer vectors. This section derives them: polynomial
multiplication in `ℤ[X]/(X^n + 1)` (coefficients reduced mod `q = 8380417` only where FIPS 204
compares them), the bound `‖c·s‖∞ ≤ ‖c‖₁ · ‖s‖∞` (so `τ = 39`, `η = 2` give `β = 78`), the key
relation `A·(y + c·s₁) - c·t ≡ A·y - c·s₂` from `t ≡ A·s₁ + s₂`, the transcript of a REJECTED
attempt (which publishes `w₁`), and the random-oracle reprogramming bound for `c = H(μ, w₁)`. -/

theorem intDot_congr {n : Nat} (a : Fin n → Int) {u v : Fin n → Int} (h : ∀ j, u j = v j) :
    intDot n a u = intDot n a v :=
  congrArg (intDot n a) (funext h)

theorem intDot_zero : ∀ (n : Nat) (a : Fin n → Int), intDot n a (fun _ => 0) = 0
  | 0, _ => rfl
  | n + 1, a => by
    have ih := intDot_zero n (fun j => a ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
    simp only [intDot]
    rw [ih, Int.mul_zero, Int.add_zero]

theorem intDot_mul_const : ∀ (n : Nat) (a : Fin n → Int) (x : Int) (u : Fin n → Int),
    intDot n a (fun j => x * u j) = x * intDot n a u
  | 0, _, _, _ => by simp [intDot]
  | n + 1, a, x, u => by
    have ih := intDot_mul_const n (fun j => a ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩) x
      (fun j => u ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
    simp only [intDot]
    rw [ih, Int.mul_add, Int.mul_left_comm]

theorem intDot_neg (n : Nat) (a u : Fin n → Int) :
    intDot n a (fun j => - u j) = - intDot n a u := by
  have hc : intDot n a (fun j => - u j) = intDot n a (fun j => -1 * u j) :=
    intDot_congr a (fun j => (Int.neg_one_mul (u j)).symm)
  rw [hc, intDot_mul_const, Int.neg_one_mul]

theorem intDot_sub (n : Nat) (a u v : Fin n → Int) :
    intDot n a (fun j => u j - v j) = intDot n a u - intDot n a v := by
  have hc : intDot n a (fun j => u j - v j) = intDot n a (fun j => u j + - v j) :=
    intDot_congr a (fun j => Int.sub_eq_add_neg)
  rw [hc, intDot_add n a u (fun j => - v j), intDot_neg, ← Int.sub_eq_add_neg]

/-- Exchange of two finite integer sums. -/
theorem intDot_swap : ∀ (n m : Nat) (a : Fin n → Int) (c : Fin m → Int)
    (F : Fin m → Fin n → Int),
    intDot n a (fun j => intDot m c (fun i => F i j)) =
      intDot m c (fun i => intDot n a (fun j => F i j))
  | 0, m, _, c, _ => by
    simp only [intDot]
    exact (intDot_zero m c).symm
  | n + 1, m, a, c, F => by
    have ih := intDot_swap n m (fun j => a ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩) c
      (fun i j => F i ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
    have h1 := intDot_add m c
      (fun i => a ⟨0, Nat.zero_lt_succ n⟩ * F i ⟨0, Nat.zero_lt_succ n⟩)
      (fun i => intDot n (fun j => a ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
        (fun j => F i ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩))
    have h2 := intDot_mul_const m c (a ⟨0, Nat.zero_lt_succ n⟩)
      (fun i => F i ⟨0, Nat.zero_lt_succ n⟩)
    simp only [intDot]
    rw [h1, h2, ih]

/-- `‖a‖₁`. -/
def l1Norm (n : Nat) (a : Fin n → Int) : Nat := qsum n (fun j => (a j).natAbs)

theorem intDot_natAbs_le : ∀ (n : Nat) (a u : Fin n → Int) (B : Nat),
    (∀ j, (u j).natAbs ≤ B) → (intDot n a u).natAbs ≤ l1Norm n a * B
  | 0, _, _, _, _ => by simp [intDot]
  | n + 1, a, u, B, h => by
    have ih := intDot_natAbs_le n (fun j => a ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
      (fun j => u ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩) B (fun j => h _)
    have h0 := h ⟨0, Nat.zero_lt_succ n⟩
    have hL : l1Norm (n + 1) a = (a ⟨0, Nat.zero_lt_succ n⟩).natAbs +
        l1Norm n (fun j => a ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩) := rfl
    rw [hL, Nat.add_mul]
    simp only [intDot]
    refine Nat.le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add ?_ ih)
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul_left _ h0

theorem intDot_dvd : ∀ (n : Nat) (a u : Fin n → Int) (q : Int),
    (∀ j, q ∣ u j) → q ∣ intDot n a u
  | 0, _, _, q, _ => by simp [intDot]
  | n + 1, a, u, q, h => by
    simp only [intDot]
    exact Int.dvd_add (Int.dvd_trans (h _) (Int.dvd_mul_left _ _))
      (intDot_dvd n _ _ q (fun j => h _))

theorem emod_eq_of_dvd_sub {a b q : Int} (h : q ∣ a - b) : a % q = b % q := by
  obtain ⟨m, hm⟩ := h
  have hab : a = b + q * m := by omega
  rw [hab]
  exact Int.add_mul_emod_self_left b q m

/-! ### Multiplication in `ℤ[X]/(X^n + 1)` -/

/-- Multiplication by `X` in `ℤ[X]/(X^n + 1)`: the negacyclic shift (`X · X^(n-1) = -1`). -/
def negShift {n : Nat} (s : Fin n → Int) : Fin n → Int :=
  fun k =>
    if k.val = 0 then - s ⟨n - 1, by have := k.isLt; omega⟩
    else s ⟨k.val - 1, by have := k.isLt; omega⟩

/-- Multiplication by `X^i`. -/
def shiftPow {n : Nat} : Nat → (Fin n → Int) → Fin n → Int
  | 0, s => s
  | i + 1, s => negShift (shiftPow i s)

/-- The product `c · s = Σ_i c_i · (X^i · s)` in `ℤ[X]/(X^n + 1)`. -/
def polyMul {n : Nat} (c s : Fin n → Int) : Fin n → Int :=
  fun k => intDot n c (fun i => shiftPow i.val s k)

/-- The constant polynomial `1`. -/
def polyOne {n : Nat} : Fin n → Int := fun k => if k.val = 0 then 1 else 0

theorem negShift_add {n : Nat} (u v : Fin n → Int) :
    negShift (fun k => u k + v k) = fun k => negShift u k + negShift v k := by
  funext k
  by_cases h : k.val = 0
  · simp only [negShift, h, ↓reduceIte]; omega
  · simp only [negShift, h, ↓reduceIte]

theorem negShift_smul {n : Nat} (x : Int) (u : Fin n → Int) :
    negShift (fun k => x * u k) = fun k => x * negShift u k := by
  funext k
  by_cases h : k.val = 0
  · simp only [negShift, h, ↓reduceIte, Int.mul_neg]
  · simp only [negShift, h, ↓reduceIte]

theorem negShift_zero {n : Nat} : negShift (fun _ : Fin n => (0 : Int)) = fun _ => 0 := by
  funext k
  by_cases h : k.val = 0
  · simp only [negShift, h, ↓reduceIte, Int.neg_zero]
  · simp only [negShift, h, ↓reduceIte]

theorem shiftPow_add {n : Nat} (i : Nat) (u v : Fin n → Int) :
    shiftPow i (fun k => u k + v k) = fun k => shiftPow i u k + shiftPow i v k := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show negShift (shiftPow i (fun k => u k + v k)) =
      fun k => negShift (shiftPow i u) k + negShift (shiftPow i v) k
    rw [ih, negShift_add]

theorem shiftPow_smul {n : Nat} (i : Nat) (x : Int) (u : Fin n → Int) :
    shiftPow i (fun k => x * u k) = fun k => x * shiftPow i u k := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show negShift (shiftPow i (fun k => x * u k)) = fun k => x * negShift (shiftPow i u) k
    rw [ih, negShift_smul]

theorem shiftPow_zero {n : Nat} (i : Nat) :
    shiftPow i (fun _ : Fin n => (0 : Int)) = fun _ => 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show negShift (shiftPow i (fun _ : Fin n => (0 : Int))) = fun _ => 0
    rw [ih, negShift_zero]

theorem shiftPow_negShift {n : Nat} (i : Nat) (s : Fin n → Int) :
    shiftPow i (negShift s) = negShift (shiftPow i s) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show negShift (shiftPow i (negShift s)) = negShift (negShift (shiftPow i s))
    rw [ih]

theorem shiftPow_comm {n : Nat} (i j : Nat) (s : Fin n → Int) :
    shiftPow i (shiftPow j s) = shiftPow j (shiftPow i s) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show negShift (shiftPow i (shiftPow j s)) = shiftPow j (negShift (shiftPow i s))
    rw [ih, shiftPow_negShift]

theorem negShift_polyMul {n : Nat} (c s : Fin n → Int) :
    negShift (polyMul c s) = polyMul c (negShift s) := by
  funext k
  have hR : polyMul c (negShift s) k = intDot n c (fun i => negShift (shiftPow i.val s) k) :=
    intDot_congr c (fun i => congrFun (shiftPow_negShift i.val s) k)
  rw [hR]
  by_cases h : k.val = 0
  · simp only [negShift, h, ↓reduceIte, polyMul]
    exact (intDot_neg n c _).symm
  · simp only [negShift, h, ↓reduceIte, polyMul]

theorem shiftPow_polyMul {n : Nat} (j : Nat) (c s : Fin n → Int) :
    shiftPow j (polyMul c s) = polyMul c (shiftPow j s) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show negShift (shiftPow j (polyMul c s)) = polyMul c (negShift (shiftPow j s))
    rw [ih, negShift_polyMul]

theorem polyMul_add_right {n : Nat} (c u v : Fin n → Int) :
    polyMul c (fun k => u k + v k) = fun k => polyMul c u k + polyMul c v k := by
  funext k
  exact (intDot_congr c (fun i => congrFun (shiftPow_add i.val u v) k)).trans
    (intDot_add n c _ _)

theorem polyMul_smul_right {n : Nat} (c : Fin n → Int) (x : Int) (u : Fin n → Int) :
    polyMul c (fun k => x * u k) = fun k => x * polyMul c u k := by
  funext k
  exact (intDot_congr c (fun i => congrFun (shiftPow_smul i.val x u) k)).trans
    (intDot_mul_const n c x _)

theorem polyMul_zero_right {n : Nat} (c : Fin n → Int) :
    polyMul c (fun _ => 0) = fun _ => 0 := by
  funext k
  exact (intDot_congr c (fun i => congrFun (shiftPow_zero i.val) k)).trans (intDot_zero n c)

/-- `c · (Σ_j a_j · F_j) = Σ_j a_j · (c · F_j)`. -/
theorem polyMul_intDot_right {n : Nat} (c : Fin n → Int) : ∀ (m : Nat) (a : Fin m → Int)
    (F : Fin m → Fin n → Int),
    polyMul c (fun k => intDot m a (fun j => F j k)) =
      fun k => intDot m a (fun j => polyMul c (F j) k)
  | 0, _, _ => polyMul_zero_right c
  | m + 1, a, F => by
    have ih := polyMul_intDot_right c m (fun j => a ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
      (fun j => F ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
    have h1 := polyMul_add_right c
      (fun k => a ⟨0, Nat.zero_lt_succ m⟩ * F ⟨0, Nat.zero_lt_succ m⟩ k)
      (fun k => intDot m (fun j => a ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
        (fun j => F ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ k))
    have h2 := polyMul_smul_right c (a ⟨0, Nat.zero_lt_succ m⟩) (F ⟨0, Nat.zero_lt_succ m⟩)
    simp only [intDot]
    rw [h1, h2, ih]

/-- **Multiplications commute as operators**: `a · (c · s) = c · (a · s)`. -/
theorem polyMul_comm_action {n : Nat} (a c s : Fin n → Int) :
    polyMul a (polyMul c s) = polyMul c (polyMul a s) := by
  funext k
  have hL : polyMul a (polyMul c s) k =
      intDot n a (fun j => intDot n c (fun i => shiftPow i.val (shiftPow j.val s) k)) :=
    intDot_congr a (fun j => congrFun (shiftPow_polyMul j.val c s) k)
  have hR : polyMul c (polyMul a s) k =
      intDot n c (fun i => intDot n a (fun j => shiftPow i.val (shiftPow j.val s) k)) :=
    intDot_congr c (fun i =>
      (congrFun (shiftPow_polyMul i.val a s) k).trans
        (intDot_congr a (fun j => congrFun (shiftPow_comm j.val i.val s) k)))
  rw [hL, hR]
  exact intDot_swap n n a c (fun i j => shiftPow i.val (shiftPow j.val s) k)

theorem intDot_delta : ∀ (n : Nat) (c : Fin n → Int) (k : Fin n),
    intDot n c (fun i => if k.val = i.val then 1 else 0) = c k
  | 0, _, k => Fin.elim0 k
  | n + 1, c, ⟨0, hk⟩ => by
    have hz : intDot n (fun j => c ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
        (fun j => if (0 : Nat) = j.1 + 1 then (1 : Int) else 0) = 0 :=
      (intDot_congr _ (fun j => ite_eq_right (Nat.succ_ne_zero j.1).symm)).trans (intDot_zero n _)
    show c ⟨0, Nat.zero_lt_succ n⟩ * (if (0 : Nat) = 0 then 1 else 0) +
      intDot n (fun j => c ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
        (fun j => if (0 : Nat) = j.1 + 1 then (1 : Int) else 0) = c ⟨0, hk⟩
    rw [hz, ite_eq_left rfl, Int.mul_one, Int.add_zero]
  | n + 1, c, ⟨k + 1, hk⟩ => by
    have ih : intDot n (fun j => c ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
        (fun j => if k = j.1 then (1 : Int) else 0) = c ⟨k + 1, hk⟩ :=
      intDot_delta n (fun j => c ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩) ⟨k, Nat.lt_of_succ_lt_succ hk⟩
    have hc : intDot n (fun j => c ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
        (fun j => if k + 1 = j.1 + 1 then (1 : Int) else 0) =
        intDot n (fun j => c ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
        (fun j => if k = j.1 then (1 : Int) else 0) :=
      intDot_congr _ (fun j => by
        by_cases h : k = j.1
        · rw [ite_eq_left h, ite_eq_left (congrArg (· + 1) h)]
        · rw [ite_eq_right h, ite_eq_right (fun e => h (Nat.succ.inj e))])
    show c ⟨0, Nat.zero_lt_succ n⟩ * (if k + 1 = 0 then 1 else 0) +
      intDot n (fun j => c ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
        (fun j => if k + 1 = j.1 + 1 then (1 : Int) else 0) = c ⟨k + 1, hk⟩
    rw [hc, ih, ite_eq_right (Nat.succ_ne_zero k), Int.mul_zero, Int.zero_add]

theorem shiftPow_one_apply {n : Nat} : ∀ (i : Nat), i < n → ∀ k : Fin n,
    shiftPow i (polyOne : Fin n → Int) k = if k.val = i then 1 else 0
  | 0, _, _ => rfl
  | i + 1, hi, k => by
    have ih := shiftPow_one_apply i (Nat.lt_of_succ_lt hi)
    show negShift (shiftPow i polyOne) k = _
    by_cases hk : k.val = 0
    · simp only [negShift, hk, ↓reduceIte]
      rw [ih]
      have h1 : ¬ (n - 1 = i) := by omega
      have h2 : ¬ (0 = i + 1) := by omega
      simp only [h1, h2, ↓reduceIte, Int.neg_zero]
    · simp only [negShift, hk, ↓reduceIte]
      rw [ih]
      by_cases h : k.val = i + 1
      · have h2 : k.val - 1 = i := by omega
        simp only [h2, ↓reduceIte]
        rw [ite_eq_left h]
      · have h2 : ¬ (k.val - 1 = i) := by omega
        simp only [h2, h, ↓reduceIte]

/-- `c · 1 = c`. -/
theorem polyMul_one {n : Nat} (c : Fin n → Int) : polyMul c polyOne = c := by
  funext k
  exact (intDot_congr c (fun i => shiftPow_one_apply i.val i.isLt k)).trans (intDot_delta n c k)

/-- The ring is commutative. -/
theorem polyMul_comm {n : Nat} (a c : Fin n → Int) : polyMul a c = polyMul c a := by
  have h := polyMul_comm_action a c polyOne
  rw [polyMul_one, polyMul_one] at h
  exact h

/-- The ring is associative. -/
theorem polyMul_assoc {n : Nat} (a b c : Fin n → Int) :
    polyMul (polyMul a b) c = polyMul a (polyMul b c) := by
  rw [polyMul_comm (polyMul a b) c, polyMul_comm_action c a b, polyMul_comm c b]

/-- Coefficientwise bound `‖s‖∞ ≤ B`. -/
def PolyBound {n : Nat} (B : Nat) (s : Fin n → Int) : Prop := ∀ k, (s k).natAbs ≤ B

theorem negShift_bound {n : Nat} {B : Nat} {s : Fin n → Int} (h : PolyBound B s) :
    PolyBound B (negShift s) := by
  intro k
  by_cases hk : k.val = 0
  · simp only [negShift, hk, ↓reduceIte, Int.natAbs_neg]
    exact h _
  · simp only [negShift, hk, ↓reduceIte]
    exact h _

theorem shiftPow_bound {n : Nat} {B : Nat} {s : Fin n → Int} (h : PolyBound B s) :
    ∀ i, PolyBound B (shiftPow i s)
  | 0 => h
  | i + 1 => negShift_bound (shiftPow_bound h i)

/-- **`‖c · s‖∞ ≤ ‖c‖₁ · ‖s‖∞`** in `ℤ[X]/(X^n + 1)`. -/
theorem polyMul_bound {n : Nat} {B : Nat} (c : Fin n → Int) {s : Fin n → Int}
    (h : PolyBound B s) : PolyBound (l1Norm n c * B) (polyMul c s) :=
  fun k => intDot_natAbs_le n c _ B (fun i => shiftPow_bound h i.val k)

/-- The FIPS 204 challenge set `B_τ`: coefficients in `{-1, 0, 1}`, exactly `τ` of them non-zero
    (equivalently `‖c‖∞ ≤ 1` and `‖c‖₁ = τ`). This is the range of `SampleInBall`. -/
def InChallengeBall {n : Nat} (τ : Nat) (c : Fin n → Int) : Prop :=
  (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) ∧ l1Norm n c = τ

/-- **`β = τ · η` is a theorem (`mldsa44_challenge_times_secret_le_beta`)**: for a challenge in
    `B_39` and a secret polynomial with `‖s‖∞ ≤ η = 2`, every coefficient of `c · s` in
    `ℤ[X]/(X^256 + 1)` has absolute value at most `78`. -/
theorem mldsa44_challenge_times_secret_le_beta {c s : Fin 256 → Int}
    (hc : InChallengeBall 39 c) (hs : PolyBound 2 s) : PolyBound 78 (polyMul c s) := by
  intro k
  have h := polyMul_bound c hs k
  rw [hc.2] at h
  exact h

theorem negShift_sub_dvd {n : Nat} {q : Int} {u v : Fin n → Int}
    (h : ∀ k, q ∣ u k - v k) : ∀ k, q ∣ negShift u k - negShift v k := by
  intro k
  by_cases hk : k.val = 0
  · simp only [negShift, hk, ↓reduceIte]
    have h0 := h ⟨n - 1, by have := k.isLt; omega⟩
    rw [show - u ⟨n - 1, by have := k.isLt; omega⟩ - - v ⟨n - 1, by have := k.isLt; omega⟩ =
      -(u ⟨n - 1, by have := k.isLt; omega⟩ - v ⟨n - 1, by have := k.isLt; omega⟩) by omega]
    exact Int.dvd_neg.mpr h0
  · simp only [negShift, hk, ↓reduceIte]
    exact h _

theorem shiftPow_sub_dvd {n : Nat} {q : Int} {u v : Fin n → Int}
    (h : ∀ k, q ∣ u k - v k) : ∀ i k, q ∣ shiftPow i u k - shiftPow i v k
  | 0 => h
  | i + 1 => negShift_sub_dvd (shiftPow_sub_dvd h i)

/-- Multiplication respects coefficientwise congruence mod `q`: `polyMul` descends to
    `ℤ_q[X]/(X^n + 1)`. -/
theorem polyMul_sub_dvd {n : Nat} (c u v : Fin n → Int) (q : Int)
    (h : ∀ k, q ∣ u k - v k) : ∀ k, q ∣ polyMul c u k - polyMul c v k := by
  intro k
  have hEq : polyMul c u k - polyMul c v k =
      intDot n c (fun i => shiftPow i.val u k - shiftPow i.val v k) :=
    (intDot_sub n c _ _).symm
  rw [hEq]
  exact intDot_dvd n c _ q (fun i => shiftPow_sub_dvd h i.val k)

/-- `A · y` for a `k × l` matrix of ring elements. -/
def ringMatVec {k l n : Nat} (A : Fin k → Fin l → Fin n → Int) (y : Fin l → Fin n → Int) :
    Fin k → Fin n → Int :=
  fun r m => intDot l (fun _ => 1) (fun j => polyMul (A r j) (y j) m)

theorem ringMatVec_add {k l n : Nat} (A : Fin k → Fin l → Fin n → Int)
    (u v : Fin l → Fin n → Int) (r : Fin k) (m : Fin n) :
    ringMatVec A (fun j i => u j i + v j i) r m = ringMatVec A u r m + ringMatVec A v r m :=
  (intDot_congr _ (fun j => congrFun (polyMul_add_right (A r j) (u j) (v j)) m)).trans
    (intDot_add l _ _ _)

/-- `A · (c · s) = c · (A · s)`: the challenge commutes with the public matrix. -/
theorem ringMatVec_challenge_comm {k l n : Nat} (A : Fin k → Fin l → Fin n → Int)
    (c : Fin n → Int) (s : Fin l → Fin n → Int) (r : Fin k) :
    ringMatVec A (fun j => polyMul c (s j)) r = polyMul c (ringMatVec A s r) := by
  funext m
  have hR := congrFun (polyMul_intDot_right c l (fun _ => 1)
    (fun j => polyMul (A r j) (s j))) m
  have hL : ringMatVec A (fun j => polyMul c (s j)) r m =
      intDot l (fun _ => 1) (fun j => polyMul c (polyMul (A r j) (s j)) m) :=
    intDot_congr _ (fun j => congrFun (polyMul_comm_action (A r j) c (s j)) m)
  exact hL.trans hR.symm

/-! ### Both Rejection Checks Over an Arbitrary `ℤ`-Linear Commitment Map -/

/-- Public data of one signing attempt: a `ℤ`-linear commitment map `W` (for ML-DSA, `y ↦ A·y`
    in the ring) and `ct = c·t`. `J` indexes mask coefficients, `I` commitment coefficients. -/
structure LinCommitInstance (J I : Type) where
  W : (J → Int) → I → Int
  W_add : ∀ (u v : J → Int) (i : I), W (fun j => u j + v j) i = W u i + W v i
  ct : I → Int

/-- Secret-dependent shifts `c·s₁`, `c·s₂`. -/
structure LinSecretShift (J I : Type) where
  cs1 : J → Int
  cs2 : I → Int

def LinKeyRelation {J I : Type} (pub : LinCommitInstance J I) (sec : LinSecretShift J I) : Prop :=
  (∀ j, inMldsaSecretBound mldsa44Beta (sec.cs1 j)) ∧
  (∀ i, inMldsaSecretBound mldsa44Beta (sec.cs2 i)) ∧
  (∀ i, pub.ct i % 8380417 = (pub.W sec.cs1 i + sec.cs2 i) % 8380417)

def linRealZ {J I : Type} (sec : LinSecretShift J I) (y : J → Int) : J → Int :=
  fun j => y j + sec.cs1 j

def linRealW1 {J I : Type} (pub : LinCommitInstance J I) (y : J → Int) : I → Int :=
  fun i => mldsa44HighBits (pub.W y i)

def linRealAccept {J I : Type} (pub : LinCommitInstance J I) (sec : LinSecretShift J I)
    (y : J → Int) : Prop :=
  (∀ j, inMldsaSafeBox mldsa44Gamma1 mldsa44Beta (y j + sec.cs1 j)) ∧
  (∀ i, mldsa44LowBitsOk (mldsa44LowBits (pub.W y i - sec.cs2 i)))

def linSimW1 {J I : Type} (pub : LinCommitInstance J I) (z : J → Int) : I → Int :=
  fun i => mldsa44HighBits (pub.W z i - pub.ct i)

def linSimAccept {J I : Type} (pub : LinCommitInstance J I) (z : J → Int) : Prop :=
  (∀ j, inMldsaSafeBox mldsa44Gamma1 mldsa44Beta (z j)) ∧
  (∀ i, mldsa44LowBitsOk (mldsa44LowBits (pub.W z i - pub.ct i)))

theorem lin_commit_shift_congr {J I : Type} (pub : LinCommitInstance J I)
    (sec : LinSecretShift J I) (hKey : LinKeyRelation pub sec) (y : J → Int) (i : I) :
    (pub.W (linRealZ sec y) i - pub.ct i) % 8380417 = (pub.W y i - sec.cs2 i) % 8380417 := by
  have hK := hKey.2.2 i
  unfold linRealZ
  rw [pub.W_add]
  omega

/-- Joint `(w₁, z)` simulation over any linear commitment map (the statement of
    `mldsa44_joint_transcript_simulation`, with `A·y` no longer required to be a flat matrix). -/
theorem lin_joint_transcript_simulation {J I : Type} (pub : LinCommitInstance J I)
    (sec : LinSecretShift J I) (hKey : LinKeyRelation pub sec) :
    (∀ y : J → Int,
      (linRealAccept pub sec y ↔ linSimAccept pub (linRealZ sec y)) ∧
      (linRealAccept pub sec y → ∀ i, linRealW1 pub y i = linSimW1 pub (linRealZ sec y) i)) ∧
    (∀ z : J → Int, linSimAccept pub z →
      ∀ j, inMldsaMaskInterval mldsa44Gamma1 (z j - sec.cs1 j)) := by
  have hLowEq : ∀ (y : J → Int) (i : I),
      mldsa44LowBits (pub.W (linRealZ sec y) i - pub.ct i) =
        mldsa44LowBits (pub.W y i - sec.cs2 i) :=
    fun y i => mldsa44LowBits_congr (lin_commit_shift_congr pub sec hKey y i)
  refine ⟨fun y => ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro hReal
    refine ⟨hReal.1, fun i => ?_⟩
    rw [hLowEq y i]
    exact hReal.2 i
  · intro hSim
    refine ⟨hSim.1, fun i => ?_⟩
    rw [← hLowEq y i]
    exact hSim.2 i
  · intro hReal i
    have hs : -78 ≤ sec.cs2 i ∧ sec.cs2 i ≤ 78 := by
      have h := hKey.2.1 i
      unfold inMldsaSecretBound mldsa44Beta at h
      exact ⟨by omega, by omega⟩
    have hInv := mldsa44_highBits_shift_invariant (pub.W y i - sec.cs2 i) (sec.cs2 i) hs
      (hReal.2 i)
    have hSum : pub.W y i - sec.cs2 i + sec.cs2 i = pub.W y i := by omega
    rw [hSum] at hInv
    unfold linRealW1 linSimW1
    rw [hInv]
    exact (mldsa44HighBits_congr (lin_commit_shift_congr pub sec hKey y i)).symm
  · intro z hSim j
    exact safeBox_sub_secret_in_maskInterval (hKey.1 j) (hSim.1 j)

/-- Two secrets consistent with the same public data: an accepted mask of one maps to an accepted
    mask of the other with the same `(w₁, z)`. -/
theorem lin_joint_transcript_secret_independent {J I : Type} (pub : LinCommitInstance J I)
    (sec sec' : LinSecretShift J I) (hKey : LinKeyRelation pub sec)
    (hKey' : LinKeyRelation pub sec') (y : J → Int) (hAcc : linRealAccept pub sec y) :
    (∀ j, inMldsaMaskInterval mldsa44Gamma1 (y j + sec.cs1 j - sec'.cs1 j)) ∧
    linRealAccept pub sec' (fun j => y j + sec.cs1 j - sec'.cs1 j) ∧
    linRealZ sec' (fun j => y j + sec.cs1 j - sec'.cs1 j) = linRealZ sec y ∧
    (∀ i, linRealW1 pub (fun j => y j + sec.cs1 j - sec'.cs1 j) i = linRealW1 pub y i) := by
  obtain ⟨hFwd, _⟩ := lin_joint_transcript_simulation pub sec hKey
  obtain ⟨hFwd', hBack'⟩ := lin_joint_transcript_simulation pub sec' hKey'
  have hZ : linRealZ sec' (fun j => y j + sec.cs1 j - sec'.cs1 j) = linRealZ sec y := by
    funext j
    simp only [linRealZ]
    omega
  have hSim : linSimAccept pub (linRealZ sec y) := (hFwd y).1.mp hAcc
  have hAcc' : linRealAccept pub sec' (fun j => y j + sec.cs1 j - sec'.cs1 j) :=
    (hFwd' _).1.mpr (by rw [hZ]; exact hSim)
  refine ⟨fun j => hBack' (linRealZ sec y) hSim j, hAcc', hZ, fun i => ?_⟩
  rw [(hFwd' _).2 hAcc' i, hZ, (hFwd y).2 hAcc i]

/-! ### The Ring Instance: `t ≡ A·s₁ + s₂` Gives the Key Relation -/

/-- The ML-DSA instance over `ℤ[X]/(X^n + 1)` for a challenge `c`: `W y = A·y`, `ct = c·t`. -/
def mldsaRingInstance {k l n : Nat} (A : Fin k → Fin l → Fin n → Int)
    (t : Fin k → Fin n → Int) (c : Fin n → Int) :
    LinCommitInstance (Fin l × Fin n) (Fin k × Fin n) where
  W := fun y i => ringMatVec A (fun j m => y (j, m)) i.1 i.2
  W_add := fun u v i => ringMatVec_add A (fun j m => u (j, m)) (fun j m => v (j, m)) i.1 i.2
  ct := fun i => polyMul c (t i.1) i.2

/-- The shifts `c·s₁`, `c·s₂` computed in the ring. -/
def mldsaRingShift {k l n : Nat} (c : Fin n → Int) (s1 : Fin l → Fin n → Int)
    (s2 : Fin k → Fin n → Int) : LinSecretShift (Fin l × Fin n) (Fin k × Fin n) where
  cs1 := fun j => polyMul c (s1 j.1) j.2
  cs2 := fun i => polyMul c (s2 i.1) i.2

/-- **ML-DSA-44 Key Relation in `ℤ_q[X]/(X^256 + 1)` (`mldsa44_ring_key_relation`)**: for a
    public key `t ≡ A·s₁ + s₂ (mod q)` with `‖s₁‖∞, ‖s₂‖∞ ≤ η = 2` and a challenge `c ∈ B_39`,
    the shifts `c·s₁`, `c·s₂` are `β`-bounded and `c·t ≡ A·(c·s₁) + c·s₂ (mod q)`. Nothing about
    `c·s₁`, `c·s₂`, `c·t` is assumed. -/
theorem mldsa44_ring_key_relation {k l : Nat} (A : Fin k → Fin l → Fin 256 → Int)
    (s1 : Fin l → Fin 256 → Int) (s2 t : Fin k → Fin 256 → Int) (c : Fin 256 → Int)
    (hBall : InChallengeBall 39 c)
    (hS1 : ∀ j, PolyBound 2 (s1 j)) (hS2 : ∀ r, PolyBound 2 (s2 r))
    (hT : ∀ r m, (8380417 : Int) ∣ t r m - (ringMatVec A s1 r m + s2 r m)) :
    LinKeyRelation (mldsaRingInstance A t c) (mldsaRingShift c s1 s2) := by
  refine ⟨fun j => ?_, fun i => ?_, fun i => ?_⟩
  · exact (inMldsaSecretBound_iff_natAbs_le mldsa44Beta _).mpr
      (mldsa44_challenge_times_secret_le_beta hBall (hS1 j.1) j.2)
  · exact (inMldsaSecretBound_iff_natAbs_le mldsa44Beta _).mpr
      (mldsa44_challenge_times_secret_le_beta hBall (hS2 i.1) i.2)
  · obtain ⟨r, m⟩ := i
    have hW : (mldsaRingInstance A t c).W (mldsaRingShift c s1 s2).cs1 (r, m) =
        polyMul c (ringMatVec A s1 r) m :=
      congrFun (ringMatVec_challenge_comm A c s1 r) m
    have hSum : polyMul c (ringMatVec A s1 r) m + polyMul c (s2 r) m =
        polyMul c (fun m' => ringMatVec A s1 r m' + s2 r m') m :=
      (congrFun (polyMul_add_right c (ringMatVec A s1 r) (s2 r)) m).symm
    have hDvd := polyMul_sub_dvd c (t r) (fun m' => ringMatVec A s1 r m' + s2 r m') 8380417
      (hT r) m
    show polyMul c (t r) m % 8380417 =
      ((mldsaRingInstance A t c).W (mldsaRingShift c s1 s2).cs1 (r, m) +
        polyMul c (s2 r) m) % 8380417
    rw [hW, hSum]
    exact emod_eq_of_dvd_sub hDvd

/-- **Ring-Level Joint Transcript Simulation (`mldsa44_ring_joint_transcript_simulation`)**: the
    statement of `mldsa44_joint_transcript_simulation` for the actual scheme: masks, secrets and
    public key are vectors over `ℤ_q[X]/(X^256 + 1)`, the challenge is any element of `B_39`. -/
theorem mldsa44_ring_joint_transcript_simulation {k l : Nat}
    (A : Fin k → Fin l → Fin 256 → Int)
    (s1 : Fin l → Fin 256 → Int) (s2 t : Fin k → Fin 256 → Int) (c : Fin 256 → Int)
    (hBall : InChallengeBall 39 c)
    (hS1 : ∀ j, PolyBound 2 (s1 j)) (hS2 : ∀ r, PolyBound 2 (s2 r))
    (hT : ∀ r m, (8380417 : Int) ∣ t r m - (ringMatVec A s1 r m + s2 r m)) :
    (∀ y : Fin l × Fin 256 → Int,
      (linRealAccept (mldsaRingInstance A t c) (mldsaRingShift c s1 s2) y ↔
        linSimAccept (mldsaRingInstance A t c) (linRealZ (mldsaRingShift c s1 s2) y)) ∧
      (linRealAccept (mldsaRingInstance A t c) (mldsaRingShift c s1 s2) y →
        ∀ i, linRealW1 (mldsaRingInstance A t c) y i =
          linSimW1 (mldsaRingInstance A t c) (linRealZ (mldsaRingShift c s1 s2) y) i)) ∧
    (∀ z : Fin l × Fin 256 → Int, linSimAccept (mldsaRingInstance A t c) z →
      ∀ j, inMldsaMaskInterval mldsa44Gamma1 (z j - (mldsaRingShift c s1 s2).cs1 j)) :=
  lin_joint_transcript_simulation _ _ (mldsa44_ring_key_relation A s1 s2 t c hBall hS1 hS2 hT)

/-! ### Rejected Attempts: the Published `w₁` of an Abort Is Distributed Independently of the Secret -/

/-- Counting through a bijection between two decidable subsets of two enumerated spaces. -/
theorem qsum_subset_bij {n m : Nat} (P : Fin n → Bool) (Q : Fin m → Bool)
    (f : Fin n → Fin m) (g : Fin m → Fin n)
    (hf : ∀ i, P i = true → Q (f i) = true ∧ g (f i) = i)
    (hg : ∀ j, Q j = true → P (g j) = true ∧ f (g j) = j) :
    qsum n (fun i => if P i then 1 else 0) = qsum m (fun j => if Q j then 1 else 0) := by
  have h1 : qsum n (fun i => if P i then 1 else 0) =
      qsum n (fun i => qsum m (fun j => if j = f i then (if P i then 1 else 0) else 0)) :=
    qsum_congr (fun i => (qsum_ite_eq _ (f i) (if P i then 1 else 0)).symm)
  have h2 : ∀ j : Fin m, qsum n (fun i => if j = f i then (if P i then 1 else 0) else 0) =
      (if Q j then 1 else 0) := by
    intro j
    cases hQ : Q j with
    | true =>
      obtain ⟨hPg, hfg⟩ := hg j hQ
      have h3 : qsum n (fun i => if j = f i then (if P i then 1 else 0) else 0) =
          qsum n (fun i => if i = g j then 1 else 0) := by
        apply qsum_congr
        intro i
        by_cases hi : i = g j
        · rw [hi, hfg, hPg]
          simp
        · by_cases hj : j = f i
          · cases hP : P i with
            | true => exact absurd (by rw [hj]; exact (hf i hP).2.symm) hi
            | false => simp [hi]
          · simp [hj, hi]
      rw [h3, qsum_eq_indicator]
      simp
    | false =>
      have h3 : qsum n (fun i => if j = f i then (if P i then 1 else 0) else 0) =
          qsum n (fun _ => 0) := by
        apply qsum_congr
        intro i
        by_cases hj : j = f i
        · cases hP : P i with
          | true =>
            have hQf := (hf i hP).1
            rw [← hj, hQ] at hQf
            cases hQf
          | false => simp
        · simp [hj]
      rw [h3, qsum_const]
      simp
  rw [h1, qsum_comm]
  exact qsum_congr h2

/-- The mask box `(-γ₁, γ₁)^J`. -/
abbrev LinMaskBox (J : Type) :=
  { y : J → Int // ∀ j, inMldsaMaskInterval mldsa44Gamma1 (y j) }

/-- Index of the mask `y_i + c·s₁ - c·s₁'` (the mask that produces, under the second secret, the
    response the first secret produces from `y_i`), when it lies in the box. -/
def linReindex {J I : Type} {N : Nat} (enumY : SimpleEquiv (Fin N) (LinMaskBox J))
    [inst : ∀ y : J → Int, Decidable (∀ j, inMldsaMaskInterval mldsa44Gamma1 (y j))]
    (a b : LinSecretShift J I) (i : Fin N) : Fin N :=
  if h : ∀ j, inMldsaMaskInterval mldsa44Gamma1 ((enumY.toFun i).1 j + a.cs1 j - b.cs1 j) then
    enumY.invFun ⟨fun j => (enumY.toFun i).1 j + a.cs1 j - b.cs1 j, h⟩
  else i

theorem linReindex_spec {J I : Type} {N : Nat} (pub : LinCommitInstance J I)
    (a b : LinSecretShift J I) (hKa : LinKeyRelation pub a) (hKb : LinKeyRelation pub b)
    (enumY : SimpleEquiv (Fin N) (LinMaskBox J))
    [inst : ∀ y : J → Int, Decidable (∀ j, inMldsaMaskInterval mldsa44Gamma1 (y j))]
    (i : Fin N) (hAcc : linRealAccept pub a (enumY.toFun i).1) :
    linRealAccept pub b (enumY.toFun (linReindex enumY a b i)).1 ∧
    linRealW1 pub (enumY.toFun (linReindex enumY a b i)).1 = linRealW1 pub (enumY.toFun i).1 ∧
    linRealZ b (enumY.toFun (linReindex enumY a b i)).1 = linRealZ a (enumY.toFun i).1 ∧
    linReindex enumY b a (linReindex enumY a b i) = i := by
  obtain ⟨hBox, hAcc', hZ, hW⟩ :=
    lin_joint_transcript_secret_independent pub a b hKa hKb (enumY.toFun i).1 hAcc
  have hr : linReindex enumY a b i =
      enumY.invFun ⟨fun j => (enumY.toFun i).1 j + a.cs1 j - b.cs1 j, hBox⟩ := dite_eq_left hBox
  have hy : (enumY.toFun (linReindex enumY a b i)).1 =
      fun j => (enumY.toFun i).1 j + a.cs1 j - b.cs1 j := by
    rw [hr, enumY.right_inv]
  have hBox2 : ∀ j, inMldsaMaskInterval mldsa44Gamma1
      ((enumY.toFun (linReindex enumY a b i)).1 j + b.cs1 j - a.cs1 j) := by
    intro j
    have h1 := congrFun hy j
    have h2 := (enumY.toFun i).2 j
    rw [show (enumY.toFun (linReindex enumY a b i)).1 j + b.cs1 j - a.cs1 j =
      (enumY.toFun i).1 j by omega]
    exact h2
  refine ⟨by rw [hy]; exact hAcc', by rw [hy]; exact funext hW, by rw [hy]; exact hZ, ?_⟩
  have hBack : linReindex enumY b a (linReindex enumY a b i) =
      enumY.invFun ⟨fun j => (enumY.toFun (linReindex enumY a b i)).1 j + b.cs1 j - a.cs1 j,
        hBox2⟩ := dite_eq_left hBox2
  have hSub : (⟨fun j => (enumY.toFun (linReindex enumY a b i)).1 j + b.cs1 j - a.cs1 j,
      hBox2⟩ : LinMaskBox J) = enumY.toFun i := by
    apply Subtype.ext
    funext j
    have h1 := congrFun hy j
    show (enumY.toFun (linReindex enumY a b i)).1 j + b.cs1 j - a.cs1 j = (enumY.toFun i).1 j
    omega
  rw [hBack, hSub, enumY.left_inv]

/-- **Accepted attempts**: for every event `D` on `(w₁, z)`, the number of masks that are
    accepted and whose transcript satisfies `D` is the same under any two secrets consistent with
    the public data. -/
theorem lin_accepted_transcript_count_secret_independent {J I : Type} {N : Nat}
    (pub : LinCommitInstance J I) (sec sec' : LinSecretShift J I)
    (hKey : LinKeyRelation pub sec) (hKey' : LinKeyRelation pub sec')
    (enumY : SimpleEquiv (Fin N) (LinMaskBox J))
    [inst : ∀ y : J → Int, Decidable (∀ j, inMldsaMaskInterval mldsa44Gamma1 (y j))]
    [DecidablePred (linRealAccept pub sec)] [DecidablePred (linRealAccept pub sec')]
    (D : (I → Int) → (J → Int) → Bool) :
    qsum N (fun i =>
      if decide (linRealAccept pub sec (enumY.toFun i).1) &&
          D (linRealW1 pub (enumY.toFun i).1) (linRealZ sec (enumY.toFun i).1) then 1 else 0) =
    qsum N (fun i =>
      if decide (linRealAccept pub sec' (enumY.toFun i).1) &&
          D (linRealW1 pub (enumY.toFun i).1) (linRealZ sec' (enumY.toFun i).1) then 1 else 0) := by
  refine qsum_subset_bij _ _ (linReindex enumY sec sec') (linReindex enumY sec' sec) ?_ ?_
  · intro i hP
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
    obtain ⟨hA, hW, hZ, hBack⟩ := linReindex_spec pub sec sec' hKey hKey' enumY i hP.1
    refine ⟨?_, hBack⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hA, by rw [hW, hZ]; exact hP.2⟩
  · intro i hP
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
    obtain ⟨hA, hW, hZ, hBack⟩ := linReindex_spec pub sec' sec hKey' hKey enumY i hP.1
    refine ⟨?_, hBack⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hA, by rw [hW, hZ]; exact hP.2⟩

private theorem qsum_split_bool {n : Nat} (p q : Fin n → Bool) :
    qsum n (fun i => if p i then 1 else 0) =
      qsum n (fun i => if q i && p i then 1 else 0) +
      qsum n (fun i => if !q i && p i then 1 else 0) := by
  rw [← qsum_add]
  apply qsum_congr
  intro i
  cases q i <;> cases p i <;> rfl

/-- **Rejected attempts (`lin_rejected_commitment_count_secret_independent`)**: an aborted
    attempt publishes `w₁ = HighBits(A·y)` and nothing else. For every event `D` on `w₁`, the
    number of masks that are REJECTED and whose `w₁` satisfies `D` is the same under any two
    secrets consistent with the public data: it is the number of all masks with `D(w₁)` minus the
    accepted ones, and both terms are secret-independent. -/
theorem lin_rejected_commitment_count_secret_independent {J I : Type} {N : Nat}
    (pub : LinCommitInstance J I) (sec sec' : LinSecretShift J I)
    (hKey : LinKeyRelation pub sec) (hKey' : LinKeyRelation pub sec')
    (enumY : SimpleEquiv (Fin N) (LinMaskBox J))
    [inst : ∀ y : J → Int, Decidable (∀ j, inMldsaMaskInterval mldsa44Gamma1 (y j))]
    [DecidablePred (linRealAccept pub sec)] [DecidablePred (linRealAccept pub sec')]
    (D : (I → Int) → Bool) :
    qsum N (fun i =>
      if !decide (linRealAccept pub sec (enumY.toFun i).1) &&
          D (linRealW1 pub (enumY.toFun i).1) then 1 else 0) =
    qsum N (fun i =>
      if !decide (linRealAccept pub sec' (enumY.toFun i).1) &&
          D (linRealW1 pub (enumY.toFun i).1) then 1 else 0) := by
  have hAcc := lin_accepted_transcript_count_secret_independent pub sec sec' hKey hKey' enumY
    (fun w _ => D w)
  have hS := qsum_split_bool (fun i => D (linRealW1 pub (enumY.toFun i).1))
    (fun i => decide (linRealAccept pub sec (enumY.toFun i).1))
  have hS' := qsum_split_bool (fun i => D (linRealW1 pub (enumY.toFun i).1))
    (fun i => decide (linRealAccept pub sec' (enumY.toFun i).1))
  omega

/-! ### `c = H(μ, w₁)` in the Random-Oracle Model: Reprogramming Bound Per Attempt -/

theorem roLookup_none_of_not_mem {X T : Type} [DecidableEq X] :
    ∀ (log : List (X × T)) (x : X), x ∉ log.map Prod.fst → roLookup log x = none
  | [], _, _ => rfl
  | (k, v) :: rest, x, h => by
    have hx : x ≠ k := fun e => h (by
      show x ∈ k :: rest.map Prod.fst
      rw [e]
      exact List.mem_cons_self)
    have hr : x ∉ rest.map Prod.fst := fun e => h (by
      show x ∈ k :: rest.map Prod.fst
      exact List.mem_cons_of_mem _ e)
    simp only [roLookup, hx, ↓reduceIte]
    exact roLookup_none_of_not_mem rest x hr

/-- Commitment min-entropy as a count: every commitment value has at most `M` of the `N` masks
    as preimages (min-entropy `log₂(N / M)`). For ML-DSA this is a property of the public matrix
    `A` (the fibres of `y ↦ HighBits(A·y)`); it is a hypothesis here, not derived. -/
def CommitFiberBound {N : Nat} {X : Type} [DecidableEq X] (cp : Fin N → X) (M : Nat) : Prop :=
  ∀ x, qsum N (fun i => if cp i = x then 1 else 0) ≤ M

/-- Masks whose commitment point lies in a given key set. -/
theorem qsum_fiber_mem_le {N : Nat} {X : Type} [DecidableEq X] (cp : Fin N → X) (M : Nat)
    (hFib : CommitFiberBound cp M) :
    ∀ keys : List X, qsum N (fun i => if cp i ∈ keys then 1 else 0) ≤ keys.length * M
  | [] => by
    have h0 : qsum N (fun i => if cp i ∈ ([] : List X) then 1 else 0) = qsum N (fun _ => 0) :=
      qsum_congr (fun _ => by simp)
    rw [h0, qsum_const]
    simp
  | a :: keys => by
    have hPoint : ∀ i : Fin N, (if cp i ∈ a :: keys then 1 else 0) ≤
        (if cp i = a then 1 else 0) + (if cp i ∈ keys then 1 else 0) := by
      intro i
      by_cases hia : cp i = a
      · simp [hia]
      · by_cases his : cp i ∈ keys <;> simp [hia, his]
    have hLe := qsum_le_qsum hPoint
    rw [qsum_add] at hLe
    have ih := qsum_fiber_mem_le cp M hFib keys
    have ha := hFib a
    simp only [List.length_cons, Nat.succ_mul]
    omega

/-- One signing attempt with mask index `i` in the REAL lazily sampled oracle: the challenge is
    the oracle's value at the commitment point `cp i = (μ, w₁)`: the logged value if the point
    was already queried (by the adversary or an earlier attempt), the fresh `c` otherwise. -/
def roAttemptReal {N : Nat} {X Ch Out : Type} [DecidableEq X] (cp : Fin N → X)
    (outcome : Fin N → Ch → Out) (log : List (X × Ch)) (i : Fin N) (c : Ch) :
    Out × List (X × Ch) :=
  match roLookup log (cp i) with
  | some c' => (outcome i c', log)
  | none => (outcome i c, (cp i, c) :: log)

/-- The same attempt with the oracle REPROGRAMMED: the challenge is always the fresh `c`, and
    `H(μ, w₁) := c` overrides any earlier value. Here `c` is independent of the mask. -/
def roAttemptProg {N : Nat} {X Ch Out : Type} (cp : Fin N → X)
    (outcome : Fin N → Ch → Out) (log : List (X × Ch)) (i : Fin N) (c : Ch) :
    Out × List (X × Ch) :=
  (outcome i c, (cp i, c) :: log)

theorem roAttempt_real_eq_prog_of_fresh {N : Nat} {X Ch Out : Type} [DecidableEq X]
    (cp : Fin N → X) (outcome : Fin N → Ch → Out) (log : List (X × Ch)) (i : Fin N) (c : Ch)
    (h : roLookup log (cp i) = none) :
    roAttemptReal cp outcome log i c = roAttemptProg cp outcome log i c := by
  unfold roAttemptReal roAttemptProg
  rw [h]

/-- **Reprogramming bound for one attempt (`roAttempt_reprogramming_bound`)**: against ANY prior
    oracle log (all queries of the adversary and of earlier attempts), for every event `D` on the
    attempt's output and resulting oracle state,

      `| #real(D) - #programmed(D) |  ≤  |log| · M`

    over the `N` masks, where `M` bounds the number of masks sharing a commitment. Dividing by
    `N`: statistical distance at most `|log| · 2^(-α)` for commitment min-entropy `α`. -/
theorem roAttempt_reprogramming_bound {N : Nat} {X Ch Out : Type} [DecidableEq X]
    (cp : Fin N → X) (outcome : Fin N → Ch → Out) (M : Nat)
    (hFib : CommitFiberBound cp M)
    (log : List (X × Ch)) (c : Ch) (D : Out × List (X × Ch) → Bool) :
    natAbsDiff
      (qsum N (fun i => if D (roAttemptReal cp outcome log i c) then 1 else 0))
      (qsum N (fun i => if D (roAttemptProg cp outcome log i c) then 1 else 0)) ≤
      log.length * M := by
  have hDiff := qsum_indicator_diff_le
    (fun i : Fin N => D (roAttemptReal cp outcome log i c))
    (fun i => D (roAttemptProg cp outcome log i c))
    (fun i => decide (cp i ∈ log.map Prod.fst))
    (fun i hBad => congrArg D (roAttempt_real_eq_prog_of_fresh cp outcome log i c
      (roLookup_none_of_not_mem log (cp i) (of_decide_eq_false hBad))))
  have hCount := qsum_fiber_mem_le cp M hFib (log.map Prod.fst)
  rw [List.length_map] at hCount
  refine Nat.le_trans hDiff (Nat.le_trans (Nat.le_of_eq (qsum_congr (fun i => ?_))) hCount)
  simp only [decide_eq_true_eq]

/-! ### Multi-Attempt Signing: Union Bound Over Attempts and Interleaved Adversary Queries -/

/-- Sum over all `k`-tuples of mask indices. -/
def tupleSum (N : Nat) : (k : Nat) → (List (Fin N) → Nat) → Nat
  | 0, F => F []
  | k + 1, F => qsum N (fun i => tupleSum N k (fun is => F (i :: is)))

theorem tupleSum_indicator_le (N : Nat) : ∀ (k : Nat) (p : List (Fin N) → Bool),
    tupleSum N k (fun is => if p is then 1 else 0) ≤ N ^ k
  | 0, p => by
    show (if p [] then 1 else 0) ≤ 1
    cases p [] <;> decide
  | k + 1, p => by
    have h : ∀ i : Fin N, tupleSum N k (fun is => if p (i :: is) then 1 else 0) ≤ N ^ k :=
      fun i => tupleSum_indicator_le N k (fun is => p (i :: is))
    have hLe := qsum_le_qsum h
    rw [qsum_const] at hLe
    rw [Nat.pow_succ, Nat.mul_comm]
    exact hLe

/-- A run of signing attempts. After each attempt the adversary sees every transcript so far and
    extends the oracle log by its own queries (`advStep`). -/
def signAttemptLoop {N : Nat} {X Ch Out : Type}
    (attempt : List (X × Ch) → Fin N → Ch → Out × List (X × Ch))
    (advStep : List Out → List (X × Ch) → List (X × Ch)) :
    List (X × Ch) → List Out → List (Fin N) → List Ch → List Out
  | log, acc, i :: is, c :: cs =>
    signAttemptLoop attempt advStep
      (advStep (acc ++ [(attempt log i c).1]) (attempt log i c).2)
      (acc ++ [(attempt log i c).1]) is cs
  | _, acc, [], _ => acc
  | _, acc, _ :: _, [] => acc

/-- Total oracle-log exposure of `k` attempts starting from a log of size `ℓ`, when the adversary
    adds at most `qH` queries after each attempt: `Σ_{a<k} (ℓ + a·(qH + 1))`. -/
def reprogCollisionBudget (qH : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, ℓ => ℓ + reprogCollisionBudget qH k (ℓ + 1 + qH)

/-- The continuation count after a first attempt with result `r`. -/
def loopTailCount {N : Nat} {X Ch Out : Type}
    (attempt : List (X × Ch) → Fin N → Ch → Out × List (X × Ch))
    (advStep : List Out → List (X × Ch) → List (X × Ch)) (D : List Out → Bool)
    (k : Nat) (cs : List Ch) (acc : List Out) (r : Out × List (X × Ch)) : Nat :=
  tupleSum N k (fun is =>
    if D (signAttemptLoop attempt advStep (advStep (acc ++ [r.1]) r.2) (acc ++ [r.1]) is cs)
    then 1 else 0)

private theorem natAbsDiff_le_of_le {a b c : Nat} (ha : a ≤ c) (hb : b ≤ c) :
    natAbsDiff a b ≤ c := by
  simp only [natAbsDiff_eq]
  split <;> omega

private theorem natAbsDiff_self (a : Nat) : natAbsDiff a a = 0 := by
  simp only [natAbsDiff_eq]
  split <;> omega

/-- **Multi-attempt ROM reprogramming bound (`multiAttempt_reprogramming_bound`)**: for `k`
    signing attempts with independent uniform masks, fresh challenges `cs`, and an adversary that
    adaptively adds at most `qH` oracle queries after each attempt, every event `D` on the list
    of transcripts satisfies

      `| #real(D) - #programmed(D) | · N  ≤  M · (Σ_{a<k} (ℓ + a·(qH+1))) · N^k`

    over the `N^k` mask tuples: statistical distance at most
    `(Σ_a |log_a|) · M / N`, the sum over attempts of the per-attempt collision probability. -/
theorem multiAttempt_reprogramming_bound {N : Nat} {X Ch Out : Type} [DecidableEq X]
    (cp : Fin N → X) (outcome : Fin N → Ch → Out) (M : Nat)
    (hFib : CommitFiberBound cp M)
    (advStep : List Out → List (X × Ch) → List (X × Ch)) (qH : Nat)
    (hAdv : ∀ ts log, (advStep ts log).length ≤ log.length + qH) (D : List Out → Bool) :
    ∀ (k : Nat) (cs : List Ch) (log : List (X × Ch)) (acc : List Out) (ℓ : Nat),
      log.length ≤ ℓ →
      natAbsDiff
        (tupleSum N k (fun is =>
          if D (signAttemptLoop (roAttemptReal cp outcome) advStep log acc is cs) then 1 else 0))
        (tupleSum N k (fun is =>
          if D (signAttemptLoop (roAttemptProg cp outcome) advStep log acc is cs) then 1 else 0))
        * N ≤ M * reprogCollisionBudget qH k ℓ * N ^ k
  | 0, cs, log, acc, ℓ, _ => by
    have hEq : ∀ att : List (X × Ch) → Fin N → Ch → Out × List (X × Ch),
        tupleSum N 0 (fun is =>
          if D (signAttemptLoop att advStep log acc is cs) then 1 else 0) =
        (if D acc then 1 else 0) := by
      intro att
      show (if D (signAttemptLoop att advStep log acc [] cs) then 1 else 0) = _
      cases cs <;> rfl
    rw [hEq, hEq, natAbsDiff_self]
    simp
  | k + 1, [], log, acc, ℓ, _ => by
    have hEq : ∀ att : List (X × Ch) → Fin N → Ch → Out × List (X × Ch),
        tupleSum N (k + 1) (fun is =>
          if D (signAttemptLoop att advStep log acc is []) then 1 else 0) =
        tupleSum N (k + 1) (fun _ => if D acc then 1 else 0) := by
      intro att
      show qsum N (fun i => tupleSum N k (fun is =>
        if D (signAttemptLoop att advStep log acc (i :: is) []) then 1 else 0)) = _
      rfl
    rw [hEq, hEq, natAbsDiff_self]
    simp
  | k + 1, c :: cs, log, acc, ℓ, hLen => by
    have hUnf : ∀ att : List (X × Ch) → Fin N → Ch → Out × List (X × Ch),
        tupleSum N (k + 1) (fun is =>
          if D (signAttemptLoop att advStep log acc is (c :: cs)) then 1 else 0) =
        qsum N (fun i => loopTailCount att advStep D k cs acc (att log i c)) :=
      fun _ => rfl
    rw [hUnf, hUnf]
    have hPer : ∀ i : Fin N,
        natAbsDiff
          (loopTailCount (roAttemptReal cp outcome) advStep D k cs acc
            (roAttemptReal cp outcome log i c))
          (loopTailCount (roAttemptProg cp outcome) advStep D k cs acc
            (roAttemptProg cp outcome log i c)) * N ≤
        (if cp i ∈ log.map Prod.fst then 1 else 0) * (N ^ k * N) +
          M * reprogCollisionBudget qH k (ℓ + 1 + qH) * N ^ k := by
      intro i
      by_cases hMem : cp i ∈ log.map Prod.fst
      · rw [ite_eq_left hMem, Nat.one_mul]
        have ha : loopTailCount (roAttemptReal cp outcome) advStep D k cs acc
            (roAttemptReal cp outcome log i c) ≤ N ^ k := tupleSum_indicator_le N k _
        have hb : loopTailCount (roAttemptProg cp outcome) advStep D k cs acc
            (roAttemptProg cp outcome log i c) ≤ N ^ k := tupleSum_indicator_le N k _
        exact Nat.le_trans (Nat.mul_le_mul_right N (natAbsDiff_le_of_le ha hb))
          (Nat.le_add_right _ _)
      · rw [ite_eq_right hMem, Nat.zero_mul, Nat.zero_add]
        rw [roAttempt_real_eq_prog_of_fresh cp outcome log i c
          (roLookup_none_of_not_mem log (cp i) hMem)]
        exact multiAttempt_reprogramming_bound cp outcome M hFib advStep qH hAdv D k cs
          (advStep (acc ++ [(roAttemptProg cp outcome log i c).1])
            (roAttemptProg cp outcome log i c).2)
          (acc ++ [(roAttemptProg cp outcome log i c).1]) (ℓ + 1 + qH)
          (Nat.le_trans (hAdv _ _) (by
            show ((cp i, c) :: log).length + qH ≤ ℓ + 1 + qH
            simp only [List.length_cons]
            omega))
    have h1 : natAbsDiff
        (qsum N (fun i => loopTailCount (roAttemptReal cp outcome) advStep D k cs acc
          (roAttemptReal cp outcome log i c)))
        (qsum N (fun i => loopTailCount (roAttemptProg cp outcome) advStep D k cs acc
          (roAttemptProg cp outcome log i c))) * N ≤
        qsum N (fun i => natAbsDiff
          (loopTailCount (roAttemptReal cp outcome) advStep D k cs acc
            (roAttemptReal cp outcome log i c))
          (loopTailCount (roAttemptProg cp outcome) advStep D k cs acc
            (roAttemptProg cp outcome log i c)) * N) := by
      rw [qsum_mul_right]
      exact Nat.mul_le_mul_right _ (natAbsDiff_qsum_le _ _)
    have h2' : qsum N (fun i =>
        (if cp i ∈ log.map Prod.fst then 1 else 0) * (N ^ k * N) +
          M * reprogCollisionBudget qH k (ℓ + 1 + qH) * N ^ k) =
        qsum N (fun i => if cp i ∈ log.map Prod.fst then 1 else 0) * (N ^ k * N) +
          N * (M * reprogCollisionBudget qH k (ℓ + 1 + qH) * N ^ k) := by
      rw [qsum_add, qsum_mul_right, qsum_const]
    have h2 := Nat.le_trans (qsum_le_qsum hPer) (Nat.le_of_eq h2')
    have hS := qsum_fiber_mem_le cp M hFib (log.map Prod.fst)
    rw [List.length_map] at hS
    have hS' : qsum N (fun i => if cp i ∈ log.map Prod.fst then 1 else 0) ≤ ℓ * M :=
      Nat.le_trans hS (Nat.mul_le_mul_right M hLen)
    have e3 := Nat.mul_le_mul_right (N ^ k * N) hS'
    have e1 : N * (M * reprogCollisionBudget qH k (ℓ + 1 + qH) * N ^ k) =
        M * reprogCollisionBudget qH k (ℓ + 1 + qH) * (N ^ k * N) := by ac_rfl
    have e2 : M * (ℓ + reprogCollisionBudget qH k (ℓ + 1 + qH)) * (N ^ k * N) =
        ℓ * M * (N ^ k * N) +
          M * reprogCollisionBudget qH k (ℓ + 1 + qH) * (N ^ k * N) := by
      rw [Nat.mul_add, Nat.add_mul, Nat.mul_comm M ℓ]
    show _ ≤ M * (ℓ + reprogCollisionBudget qH k (ℓ + 1 + qH)) * N ^ (k + 1)
    rw [Nat.pow_succ]
    omega

/-! ### `#tooth` and Inhabitedness Witnesses for §2b and §3b -/

/-- The hypotheses of the hiding bound are inhabited: a framed 256-bit blind and a one-query
    adversary. -/
theorem witness_rom_commit_hiding_inhabited :
    ∃ (spec : CutTheHashRomSpec Unit Unit Unit Unit (BitVec 8 × BitVec 8 × BitVec 256) 2 8 256)
      (adv : RushingRoAdversary Unit (BitVec 8 × BitVec 8 × BitVec 256) (BitVec 256)
        Unit Unit Bool 2 8),
      spec.BlindFramed ∧ adv.QueryBound 0 0 1 :=
  ⟨{ wireRingSecret := fun _ _ _ => ⟨0, Nat.zero_lt_succ 1⟩
     wireXorSecret := fun _ _ _ _ => 0
     yShareHonest := fun _ _ _ _ => 0
     macShareHonest := fun _ _ _ _ => 0
     commitPoint := fun y mac b => (y, mac, b)
     blindOf := fun x => x.2.2 },
   { reactToRingOpen := fun _ => .done ((), ())
     reactToAllOpens := fun _ _ => .done ((), ())
     decideAbort := fun _ t => .ask (0, 0, 0) (fun a => .done (a == t)) },
   fun _ _ _ => rfl, fun _ => True.intro, fun _ _ => True.intro, fun _ _ _ => True.intro⟩

private def toothRomSpec : CutTheHashRomSpec Unit Unit Unit Unit (BitVec 1 × BitVec 1) 1 1 1 where
  wireRingSecret := fun _ _ _ => ⟨0, Nat.zero_lt_succ 0⟩
  wireXorSecret := fun _ _ _ _ => 0
  yShareHonest := fun _ _ _ _ => 1
  macShareHonest := fun _ _ _ _ => 0
  commitPoint := fun y mac _ => (y, mac)
  blindOf := fun _ => 0

private def toothRomAdv :
    RushingRoAdversary Unit (BitVec 1 × BitVec 1) Bool Unit Unit Bool 1 1 where
  reactToRingOpen := fun _ => .done ((), ())
  reactToAllOpens := fun _ _ => .done ((), ())
  decideAbort := fun _ t => .ask (1, 0) (fun a => .done (a == t))

/-- **`#tooth` (`tooth_rom_commit_without_framed_blind_exceeds_bound`)**: hash only `y ‖ mac`,
    leaving the blind out of the oracle input. One query at the guessed `(y, mac)` then equals
    the tag in EVERY real execution and in no simulated one: the gap is the whole sample space
    (`4`), above the `Q · 2^w · q_RO = 2` allowed by the bound. -/
theorem tooth_rom_commit_without_framed_blind_exceeds_bound :
    ∃ (spec : CutTheHashRomSpec Unit Unit Unit Unit (BitVec 1 × BitVec 1) 1 1 1)
      (adv : RushingRoAdversary Unit (BitVec 1 × BitVec 1) Bool Unit Unit Bool 1 1)
      (tape : Nat → Bool) (tagFresh : Bool),
      adv.QueryBound 0 0 1 ∧
      1 * (2 ^ 1 * (0 + 0 + 1)) <
        natAbsDiff
          (romRealCount spec adv () () () (Nat.zero_lt_succ 0) tape (fun out => out) tagFresh)
          (2 ^ 1 * romIdealCount adv tape (fun out => out) tagFresh) :=
  ⟨toothRomSpec, toothRomAdv, fun _ => true, false,
   ⟨fun _ => True.intro, fun _ _ => True.intro, fun _ _ _ => True.intro⟩, by rw [natAbsDiff_eq]; decide⟩

theorem l1Norm_prefix_ones : ∀ (n t : Nat), t ≤ n →
    l1Norm n (fun i : Fin n => if i.val < t then (1 : Int) else 0) = t
  | 0, t, h => by
    have ht : t = 0 := by omega
    subst ht
    rfl
  | n + 1, 0, _ => by
    show qsum (n + 1) (fun j : Fin (n + 1) => ((if j.val < 0 then (1 : Int) else 0)).natAbs) = 0
    have hz : qsum (n + 1)
        (fun j : Fin (n + 1) => ((if j.val < 0 then (1 : Int) else 0)).natAbs) =
        qsum (n + 1) (fun _ => 0) := qsum_congr (fun j => by simp)
    rw [hz, qsum_const, Nat.mul_zero]
  | n + 1, t + 1, h => by
    have ih : qsum n (fun j : Fin n => ((if j.val < t then (1 : Int) else 0)).natAbs) = t :=
      l1Norm_prefix_ones n t (by omega)
    have hc : qsum n (fun j : Fin n => ((if j.val + 1 < t + 1 then (1 : Int) else 0)).natAbs) =
        qsum n (fun j : Fin n => ((if j.val < t then (1 : Int) else 0)).natAbs) :=
      qsum_congr (fun j => by simp)
    have h0 : ((if (0 : Nat) < t + 1 then (1 : Int) else 0)).natAbs = 1 := by simp
    show ((if (0 : Nat) < t + 1 then (1 : Int) else 0)).natAbs +
      qsum n (fun j : Fin n => ((if j.val + 1 < t + 1 then (1 : Int) else 0)).natAbs) = t + 1
    rw [h0, hc, ih]
    omega

/-- `B_39` is inhabited in degree `256`. -/
theorem witness_mldsa44_challenge_ball_inhabited :
    ∃ c : Fin 256 → Int, InChallengeBall 39 c :=
  ⟨fun i => if i.val < 39 then 1 else 0,
   fun i => by by_cases h : i.val < 39 <;> simp [h],
   l1Norm_prefix_ones 256 39 (by decide)⟩

/-- **`#tooth` (`tooth_challenge_bound_is_attained`)**: `‖c‖₁ · ‖s‖∞` cannot be lowered. A
    ternary challenge of weight `2` times a secret with `‖s‖∞ = η = 2` has a coefficient of
    absolute value exactly `4 = ‖c‖₁ · η`, so a bound one below it fails; a challenge heavier
    than `τ` therefore breaks `β = τ · η`. -/
theorem tooth_challenge_bound_is_attained :
    ∃ (c s : Fin 2 → Int),
      (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) ∧ PolyBound 2 s ∧
      ¬ PolyBound (l1Norm 2 c * 2 - 1) (polyMul c s) :=
  ⟨fun _ => 1, fun _ => 2, fun _ => Or.inr (Or.inr rfl),
   fun _ => by show (2 : Int).natAbs ≤ 2; decide,
   fun h => absurd (h ⟨1, by decide⟩) (by decide)⟩

/-- A key relation exists (so the simulation theorems are not vacuous). -/
theorem witness_lin_key_relation_inhabited :
    ∃ (pub : LinCommitInstance Unit Unit) (sec : LinSecretShift Unit Unit),
      LinKeyRelation pub sec :=
  ⟨{ W := fun _ _ => 0, W_add := fun _ _ _ => rfl, ct := fun _ => 0 },
   { cs1 := fun _ => 0, cs2 := fun _ => 0 },
   fun _ => (inMldsaSecretBound_iff_natAbs_le mldsa44Beta 0).mpr (Nat.zero_le _),
   fun _ => (inMldsaSecretBound_iff_natAbs_le mldsa44Beta 0).mpr (Nat.zero_le _),
   fun _ => rfl⟩

/-- A commitment map with one mask per commitment value satisfies `CommitFiberBound _ 1`. -/
theorem witness_commit_fiber_bound_inhabited :
    ∃ (cp : Fin 2 → Fin 2), CommitFiberBound cp 1 :=
  ⟨fun i => i, fun x => Nat.le_of_eq (qsum_eq_indicator 2 x)⟩

/-- **`#tooth` (`tooth_reprogramming_needs_commitment_entropy`)**: if every mask yields the same
    commitment (zero min-entropy) and the adversary has queried it, the real and reprogrammed
    attempts differ on EVERY mask: the gap `2` exceeds `|log| · 1`, so the per-attempt bound is
    false with `M` understated. -/
theorem tooth_reprogramming_needs_commitment_entropy :
    ∃ (cp : Fin 2 → Unit) (outcome : Fin 2 → Bool → Bool) (log : List (Unit × Bool)) (c : Bool)
      (D : Bool × List (Unit × Bool) → Bool),
      log.length * 1 <
        natAbsDiff
          (qsum 2 (fun i => if D (roAttemptReal cp outcome log i c) then 1 else 0))
          (qsum 2 (fun i => if D (roAttemptProg cp outcome log i c) then 1 else 0)) :=
  ⟨fun _ => (), fun _ c => c, [((), true)], false, fun r => r.1, by rw [natAbsDiff_eq]; decide⟩

/-- The ML-DSA transcript of one attempt under challenge `c`: the published `w₁`, and `z` when
    both rejection checks pass. A rejected attempt publishes `w₁` alone. -/
def linAttemptOutcome {Ch J I : Type} (pubOf : Ch → LinCommitInstance J I)
    (secOf : Ch → LinSecretShift J I)
    [∀ c y, Decidable (linRealAccept (pubOf c) (secOf c) y)]
    (y : J → Int) (c : Ch) : (I → Int) × Option (J → Int) :=
  (linRealW1 (pubOf c) y,
   if linRealAccept (pubOf c) (secOf c) y then some (linRealZ (secOf c) y) else none)

/-- **ML-DSA attempt with `c = H(μ, w₁)` (`mldsa_attempt_rom_reprogramming_bound`)**: the
    per-attempt reprogramming bound instantiated at the ML-DSA transcript. `encPoint` encodes
    `(μ, w₁)` as an oracle input; `M` bounds the number of masks sharing a `w₁`. -/
theorem mldsa_attempt_rom_reprogramming_bound {Ch J I X : Type} {N : Nat} [DecidableEq X]
    (pubOf : Ch → LinCommitInstance J I) (secOf : Ch → LinSecretShift J I)
    [∀ c y, Decidable (linRealAccept (pubOf c) (secOf c) y)]
    (enumY : SimpleEquiv (Fin N) (LinMaskBox J)) (encPoint : Fin N → X) (M : Nat)
    (hFib : CommitFiberBound encPoint M)
    (log : List (X × Ch)) (c : Ch)
    (D : ((I → Int) × Option (J → Int)) × List (X × Ch) → Bool) :
    natAbsDiff
      (qsum N (fun i => if D (roAttemptReal encPoint
        (fun i c => linAttemptOutcome pubOf secOf (enumY.toFun i).1 c) log i c) then 1 else 0))
      (qsum N (fun i => if D (roAttemptProg encPoint
        (fun i c => linAttemptOutcome pubOf secOf (enumY.toFun i).1 c) log i c) then 1 else 0)) ≤
      log.length * M :=
  roAttempt_reprogramming_bound encPoint _ M hFib log c D

/-! ## §4. Mechanical Constructive, `#tooth_pair` & `#verify_inhabited` Gates -/

#verify_constructive
  walRecoverable_eq_isSome
  no_preproc_batch_reused_on_wire
  no_leaf_double_sign_on_wire
  wire_spend_le_policy_cap
  ceremony_multi_ledger_crash_interleaving_safe
  failed_closed_host_stays_closed
  tooth_release_before_durable_burn_reuses_leaf
  tooth_release_before_checkpoint_rolls_back_leaf
  witness_multi_ledger_crash_trace_inhabited
  witness_torn_checkpointed_leaf_fails_closed
  subModFinQ_involutive
  preOpenView_exact_fiber_one
  cutTheHash_abort_conditioned_sd_zero
  tooth_early_open_before_mac_barrier_skews_distribution
  tooth_unblinded_commit_skews_distribution
  witness_cutTheHash_selective_abort_inhabited
  mldsa_rejection_valid_output_uniform_in_box
  mldsa44_rejection_valid_output_uniform_in_box
  tooth_mldsa_unclipped_z_leaks_secret_shift
  witness_mldsa44_secret_bound_inhabited
  mldsa44HighBits_congr
  mldsa44LowBits_congr
  mldsa44_highBits_shift_invariant
  mldsa44_low_range_test_iff
  intDot_add
  mldsa_commit_shift_congr
  mldsa44_joint_transcript_simulation
  mldsa44JointTranscriptEquiv_preserves_transcript
  mldsa44_joint_transcript_secret_independent
  tooth_mldsa44_low_bits_margin_omitted_leaks_s2
  witness_mldsa44_joint_accept_inhabited

#verify_constructive whole_device_rollback_below_anchor_fails_closed
#verify_constructive posixRefines_recover
#verify_constructive posixRefines_slot_write
#verify_constructive posix_crash_during_slot_write_refines
#verify_constructive posix_media_damage_refines
#verify_constructive posix_device_restore_below_anchor_fails_closed
#verify_constructive witness_policy_window_rotation_crash_mid_step
#verify_constructive witness_posix_slot_write_crash_inhabited
#verify_constructive askedRo_length_le
#verify_constructive runRo_lookup_none
#verify_constructive runRo_agree_off
#verify_constructive romReal_eq_ideal_of_blind_unqueried
#verify_constructive romCommit_blind_count_bound
#verify_constructive cutTheHash_rom_commit_hiding_sd_bound
#verify_constructive cutTheHash_rom_view_secret_independent
#verify_constructive cutTheHash_rom_commit_hiding_sd_bound_256
#verify_constructive witness_rom_commit_hiding_inhabited
#verify_constructive tooth_rom_commit_without_framed_blind_exceeds_bound
#verify_constructive intDot_swap
#verify_constructive intDot_natAbs_le
#verify_constructive polyMul_comm_action
#verify_constructive polyMul_one
#verify_constructive polyMul_comm
#verify_constructive polyMul_assoc
#verify_constructive polyMul_bound
#verify_constructive polyMul_sub_dvd
#verify_constructive mldsa44_challenge_times_secret_le_beta
#verify_constructive ringMatVec_challenge_comm
#verify_constructive lin_joint_transcript_simulation
#verify_constructive lin_joint_transcript_secret_independent
#verify_constructive mldsa44_ring_key_relation
#verify_constructive mldsa44_ring_joint_transcript_simulation
#verify_constructive qsum_subset_bij
#verify_constructive lin_accepted_transcript_count_secret_independent
#verify_constructive lin_rejected_commitment_count_secret_independent
#verify_constructive roAttempt_reprogramming_bound
#verify_constructive multiAttempt_reprogramming_bound
#verify_constructive mldsa_attempt_rom_reprogramming_bound
#verify_constructive witness_mldsa44_challenge_ball_inhabited
#verify_constructive tooth_challenge_bound_is_attained
#verify_constructive witness_lin_key_relation_inhabited
#verify_constructive witness_commit_fiber_bound_inhabited
#verify_constructive tooth_reprogramming_needs_commitment_entropy

#tooth_pair cutTheHash_rom_commit_hiding_sd_bound vs tooth_rom_commit_without_framed_blind_exceeds_bound
#tooth_pair cutTheHash_rom_commit_hiding_sd_bound_256 vs tooth_rom_commit_without_framed_blind_exceeds_bound
#tooth_pair polyMul_bound vs tooth_challenge_bound_is_attained
#tooth_pair mldsa44_challenge_times_secret_le_beta vs tooth_challenge_bound_is_attained
#tooth_pair roAttempt_reprogramming_bound vs tooth_reprogramming_needs_commitment_entropy
#tooth_pair multiAttempt_reprogramming_bound vs tooth_reprogramming_needs_commitment_entropy
#tooth_pair no_leaf_double_sign_on_wire vs tooth_release_before_durable_burn_reuses_leaf
#tooth_pair no_leaf_double_sign_on_wire vs tooth_release_before_checkpoint_rolls_back_leaf
#tooth_pair ceremony_multi_ledger_crash_interleaving_safe vs tooth_release_before_durable_burn_reuses_leaf
#tooth_pair ceremony_multi_ledger_crash_interleaving_safe vs tooth_release_before_checkpoint_rolls_back_leaf
#tooth_pair cutTheHash_abort_conditioned_sd_zero vs tooth_early_open_before_mac_barrier_skews_distribution
#tooth_pair cutTheHash_abort_conditioned_sd_zero vs tooth_unblinded_commit_skews_distribution
#tooth_pair mldsa_rejection_valid_output_uniform_in_box vs tooth_mldsa_unclipped_z_leaks_secret_shift
#tooth_pair mldsa44_rejection_valid_output_uniform_in_box vs tooth_mldsa_unclipped_z_leaks_secret_shift
#tooth_pair mldsa44_joint_transcript_simulation vs tooth_mldsa44_low_bits_margin_omitted_leaks_s2
#tooth_pair mldsa44_joint_transcript_secret_independent vs tooth_mldsa44_low_bits_margin_omitted_leaks_s2

/-- A nonempty ring instance supplies all secret bounds and the public-key equation. -/
theorem witness_mldsa44_ring_premises :
    ∃ (A : Fin 1 → Fin 1 → Fin 256 → Int)
      (s1 s2 t : Fin 1 → Fin 256 → Int) (c : Fin 256 → Int),
      InChallengeBall 39 c ∧ (∀ j, PolyBound 2 (s1 j)) ∧
      (∀ r, PolyBound 2 (s2 r)) ∧
      (∀ r m, (8380417 : Int) ∣ t r m - (ringMatVec A s1 r m + s2 r m)) := by
  refine ⟨fun _ _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0,
    (fun i => if i.val < 39 then 1 else 0),
    ⟨(fun i => by by_cases h : i.val < 39 <;> simp [h]),
      l1Norm_prefix_ones 256 39 (by decide)⟩,
    fun _ _ => Nat.zero_le 2, fun _ _ => Nat.zero_le 2, ?_⟩
  intro r m
  simp only [ringMatVec, polyMul_zero_right, intDot_zero, Int.add_zero, Int.sub_zero]
  exact ⟨0, rfl⟩

/-- Enumeration of the full one-coordinate mask interval. -/
def unitLinMaskEnum : SimpleEquiv (Fin (mldsaMaskIntervalCard mldsa44Gamma1)) (LinMaskBox Unit) where
  toFun i := ⟨fun _ => decodeMldsaMask mldsa44Gamma1 i,
    fun _ => (encode_decodeMldsaMask (by decide) i).1⟩
  invFun y := encodeMldsaMask (by decide) (y.1 ()) (y.2 ())
  left_inv i := (encode_decodeMldsaMask (by decide) i).2
  right_inv y := by
    apply Subtype.ext
    funext u
    cases u
    exact decode_encodeMldsaMask (by decide) _ _

theorem witness_lin_enumerated_key_relation :
    ∃ (pub : LinCommitInstance Unit Unit) (sec : LinSecretShift Unit Unit)
      (_enumY : SimpleEquiv (Fin (mldsaMaskIntervalCard mldsa44Gamma1)) (LinMaskBox Unit)),
      LinKeyRelation pub sec := by
  obtain ⟨pub, sec, h⟩ := witness_lin_key_relation_inhabited
  exact ⟨pub, sec, unitLinMaskEnum, h⟩

/-- A dead host has a valid continuation starting from that same dead state. -/
theorem witness_failed_closed_continuation :
    ∃ s : MultiLedgerHostState, HostFailedClosed s ∧ ValidMultiLedgerTrace s [] s := by
  obtain ⟨_, s, _, hd, _, _⟩ := witness_torn_checkpointed_leaf_fails_closed
  exact ⟨s, hd, .nil s⟩

/-- Joint witness includes the adaptive query-budget condition. -/
theorem witness_multi_attempt_budget :
    ∃ (cp : Fin 2 → Fin 2) (adv : List Unit → List (Fin 2 × Unit) → List (Fin 2 × Unit)),
      CommitFiberBound cp 1 ∧ ∀ ts log, (adv ts log).length ≤ log.length + 0 := by
  obtain ⟨cp, hcp⟩ := witness_commit_fiber_bound_inhabited
  exact ⟨cp, fun _ log => log, hcp, fun _ _ => Nat.le_refl _⟩

local instance unitForallDecidable (p : Unit → Prop) [DecidablePred p] : Decidable (∀ u, p u) :=
  if h : p () then .isTrue (fun u => by cases u; exact h)
  else .isFalse (fun hall => h (hall ()))

local instance unitLinAcceptDecidable (pub : LinCommitInstance Unit Unit)
    (sec : LinSecretShift Unit Unit) : DecidablePred (linRealAccept pub sec) := by
  intro y
  exact inferInstanceAs (Decidable
    ((∀ j : Unit, inMldsaSafeBox mldsa44Gamma1 mldsa44Beta (y j + sec.cs1 j)) ∧
     (∀ i : Unit, mldsa44LowBitsOk (mldsa44LowBits (pub.W y i - sec.cs2 i)))))

#verify_inhabited ceremony_multi_ledger_crash_interleaving_safe witness_multi_ledger_crash_trace_inhabited
#verify_inhabited posix_crash_during_slot_write_refines witness_posix_slot_write_crash_inhabited
#verify_inhabited cutTheHash_rom_commit_hiding_sd_bound witness_rom_commit_hiding_inhabited
#verify_inhabited mldsa44_ring_key_relation witness_mldsa44_ring_premises
#verify_inhabited mldsa44_ring_joint_transcript_simulation witness_mldsa44_ring_premises
#verify_inhabited lin_joint_transcript_simulation witness_lin_key_relation_inhabited
#verify_inhabited lin_rejected_commitment_count_secret_independent witness_lin_enumerated_key_relation
#verify_inhabited roAttempt_reprogramming_bound witness_commit_fiber_bound_inhabited
#verify_inhabited multiAttempt_reprogramming_bound witness_multi_attempt_budget
#verify_inhabited failed_closed_host_stays_closed witness_failed_closed_continuation
set_option maxRecDepth 65536 in
#verify_inhabited cutTheHash_abort_conditioned_sd_zero witness_cutTheHash_selective_abort_inhabited
#verify_inhabited mldsa_rejection_valid_output_uniform_in_box witness_mldsa44_secret_bound_inhabited
#verify_inhabited mldsa44_rejection_valid_output_uniform_in_box witness_mldsa44_secret_bound_inhabited
#verify_inhabited mldsa44_joint_transcript_simulation witness_mldsa44_joint_accept_inhabited
#verify_inhabited mldsa44_joint_transcript_secret_independent witness_mldsa44_joint_accept_inhabited


/-! ## §4. Implemented reservation authority and separately supplied external CAS

The earlier five-ledger and unified-resource models are conditional specifications. The
Rust v2 journal stores reservations plus epoch/retry metadata; it does not allocate a policy
budget or an MPC nonce slot. `JournalStep` models its fresh-unbound subprotocol only.
The retry-aware validator and binding-preservation results retain repeated identical bindings. Capabilities are transition-owned:
constructing a Lean record is never evidence that a Rust permit was issued or consumed.
The external service below is an additional deployment contract, not code implemented by
`LedgerCheckpoint`. It must be authenticated, linearizable, and outside disk rollback.
`anchoredJournal_released_resources_unique`: with it, released tickets never share a
codeword/leaf epoch or a ceremony id, under arbitrary replacement of the local disk.
In `JournalStep` and `RetryJournalStep` the field `entries` IS the durable history: a crash
never shortens it. That is the acknowledged-write contract stated above, and whole-disk
rollback is outside it; only the anchored machine survives rollback.
-/
namespace RustDurability

/-- Newest journal entry is last, exactly as in the Rust Vec. -/
structure JournalState where
  keyId : Bytes
  lockSeal : Bytes
  entries : List Reservation
  staged : Option Reservation := none
  permit : Option Reservation := none
  pc : ReplacePc := .done
  poisoned : Bool := false
  released : List Reservation := []
  deriving Repr, DecidableEq

/-- Crash cuts after temp fsync may publish the staged complete replacement. Earlier cuts
retain the prior record or fail closed. This is an explicit filesystem contract: it excludes
silent rollback of acknowledged directory syncs. Arbitrary accepted corrupt bytes instead
require the candidate-specific MAC bad event; neither case is a universal POSIX guarantee. -/
def mayPublishAfterCrash (pc : ReplacePc) : Prop :=
  pc = .checkAfter ∨ pc = .rename ∨ pc = .syncParent ∨ pc = .done

/-- Successful syscall order, including both identity/type checks. A failed check takes
`ioError`; the environment cannot select `advance` unless that syscall succeeded. -/
def nextReplacePc : ReplacePc → ReplacePc
  | .checkBefore => .checkTypes
  | .checkTypes => .createTemp
  | .createTemp => .writeMagic
  | .writeMagic => .writeSeal
  | .writeSeal => .writePayload
  | .writePayload => .syncTemp
  | .syncTemp => .checkAfter
  | .checkAfter => .rename
  | .rename => .syncParent
  | .syncParent => .done
  | .done => .done
  | .poisoned => .poisoned

/-- Owned permit lifecycle. `readMatches` is the concrete current-record check performed at
consume; its bytes are supplied by the filesystem read, not by a caller-created receipt.
Crashes occur at every program counter, including between each write and sync. -/
inductive JournalStep (macKey : Bytes) : JournalState → JournalState → Prop where
  | begin (s : JournalState) (r : Reservation)
      (healthy : s.poisoned = false) (idle : s.staged = none)
      (wf : r.WellFormed) (valid : reservationValid s.keyId s.entries r = true) :
      JournalStep macKey s { s with staged := some r, permit := none, pc := .checkBefore }
  | advance (s : JournalState) (r : Reservation)
      (healthy : s.poisoned = false) (staged : s.staged = some r) :
      JournalStep macKey s { s with pc := nextReplacePc s.pc }
  | committed (s : JournalState) (r : Reservation)
      (healthy : s.poisoned = false) (staged : s.staged = some r) (synced : s.pc = .done)
      (valid : reservationValid s.keyId s.entries r = true) :
      JournalStep macKey s { s with entries := s.entries ++ [r], staged := none, permit := some r }
  | consume (s : JournalState) (r : Reservation) (readBack : Bytes)
      (healthy : s.poisoned = false) (owned : s.permit = some r)
      (current : s.entries.getLast? = some r)
      (readMatches : readBack = ceremonyBytes macKey s.lockSeal s.keyId s.entries) :
      JournalStep macKey s { s with permit := none, released := s.released ++ [r] }
  | ioError (s : JournalState) :
      JournalStep macKey s { s with poisoned := true, pc := .poisoned, permit := none }
  | crash (s : JournalState) :
      JournalStep macKey s { s with staged := none, permit := none, pc := .done }
  | crashPublishes (s : JournalState) (r : Reservation)
      (staged : s.staged = some r) (cut : mayPublishAfterCrash s.pc)
      (valid : reservationValid s.keyId s.entries r = true) :
      JournalStep macKey s { s with entries := s.entries ++ [r], staged := none, permit := none, pc := .done }
  | reopen (s : JournalState) (readBack : Bytes)
      (readMatches : readBack = ceremonyBytes macKey s.lockSeal s.keyId s.entries) :
      JournalStep macKey s { s with poisoned := false, staged := none, permit := none, pc := .done }

/-- Lost permits burn resources; they never delete entries. No output constructor grants
release authority. These invariants concern reachable executions, not arbitrary Lean values. -/
def JournalInv (s : JournalState) : Prop :=
  (s.released.map (·.ceremonyId)).Nodup ∧
  (s.released.map (·.epochOrCodeword)).Nodup ∧
  (∀ r ∈ s.released, r ∈ s.entries) ∧
  (∀ r, s.permit = some r → r ∈ s.entries ∧
    ∀ e ∈ s.released, e.ceremonyId ≠ r.ceremonyId ∧ e.epochOrCodeword ≠ r.epochOrCodeword)

private theorem journal_nodup_snoc {α : Type} {xs : List α} {x : α}
    (hNodup : xs.Nodup) (hFresh : ∀ y ∈ xs, y ≠ x) : (xs ++ [x]).Nodup := by
  induction xs with
  | nil => simp [List.Nodup]
  | cons a rest ih =>
    rw [List.cons_append, List.Nodup, List.pairwise_cons] at *
    refine ⟨?_, ih hNodup.2 (fun y hy => hFresh y (by simp [hy]))⟩
    intro y hy
    rcases List.mem_append.mp hy with h | h
    · exact hNodup.1 y h
    · obtain rfl := List.mem_singleton.mp h
      exact hFresh a (by simp)

private theorem released_snoc_nodup (rs : List Reservation) (r : Reservation)
    (field : Reservation → Bytes) (h : (rs.map field).Nodup)
    (fresh : ∀ e ∈ rs, field e ≠ field r) : ((rs ++ [r]).map field).Nodup := by
  rw [List.map_append]
  apply journal_nodup_snoc h
  intro v hv
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
  exact fresh e he

theorem journalStep_preserves (key : Bytes) {s t : JournalState}
    (step : JournalStep key s t) (inv : JournalInv s) : JournalInv t := by
  obtain ⟨hId, hEpoch, hMem, hPermit⟩ := inv
  cases step with
  | begin r healthy idle wf valid =>
    exact ⟨hId, hEpoch, hMem, by intro r h; simp at h⟩
  | advance r healthy staged => exact ⟨hId, hEpoch, hMem, hPermit⟩
  | committed r healthy staged synced valid =>
    refine ⟨hId, hEpoch, ?_, ?_⟩
    · intro e he; exact List.mem_append_left _ (hMem e he)
    · intro e he
      have eq : r = e := Option.some.inj he
      subst e
      exact ⟨List.mem_append_right _ (List.mem_singleton_self _),
        fun e he => reservationValid_fresh valid e (hMem e he)⟩
  | consume r readBack healthy owned current readMatches =>
    obtain ⟨hr, hf⟩ := hPermit r owned
    refine ⟨released_snoc_nodup _ _ _ hId (fun e he => (hf e he).1),
      released_snoc_nodup _ _ _ hEpoch (fun e he => (hf e he).2), ?_, ?_⟩
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact hMem e he
      · obtain rfl := List.mem_singleton.mp he; exact hr
    · intro e he; simp at he
  | ioError => exact ⟨hId, hEpoch, hMem, by intro r h; simp at h⟩
  | crash => exact ⟨hId, hEpoch, hMem, by intro r h; simp at h⟩
  | crashPublishes r staged cut valid =>
    exact ⟨hId, hEpoch, fun e he => List.mem_append_left _ (hMem e he),
      by intro r h; simp at h⟩
  | reopen readBack readMatches =>
    exact ⟨hId, hEpoch, hMem, by intro r h; simp at h⟩

inductive JournalRun (key : Bytes) : JournalState → JournalState → Prop where
  | refl (s) : JournalRun key s s
  | next {s t u} : JournalRun key s t → JournalStep key t u → JournalRun key s u

def initialJournal (keyId lockSeal : Bytes) : JournalState :=
  { keyId, lockSeal, entries := [] }

/-- Non-reuse covers mid-reservation crashes and poisoned handles. Successful recovery is
conditional on the explicit storage contract above; malformed recovery is refusal. -/
theorem journal_trace_no_reuse (key keyId lockSeal : Bytes) {s : JournalState}
    (run : JournalRun key (initialJournal keyId lockSeal) s) : JournalInv s := by
  have init : JournalInv (initialJournal keyId lockSeal) := by
    simp [JournalInv, initialJournal]
  induction run with
  | refl => exact init
  | next run step ih => exact journalStep_preserves key step ih

/-- Receipt with evidence of actual issuance in a reachable state. It conveys no linearity
by itself; only `JournalStep.consume`, which clears `permit`, authorizes an output. -/
structure IssuedReceipt (key keyId lockSeal : Bytes) (s : JournalState) where
  reservation : Reservation
  reachable : JournalRun key (initialJournal keyId lockSeal) s
  issued : s.permit = some reservation

theorem issuedReceipt_is_durable (key keyId lockSeal : Bytes) (s : JournalState)
    (receipt : IssuedReceipt key keyId lockSeal s) : receipt.reservation ∈ s.entries :=
  (journal_trace_no_reuse key keyId lockSeal receipt.reachable).2.2.2 _ receipt.issued |>.1

theorem consumed_permit_cannot_replay (s : JournalState) (r : Reservation) :
    ({ s with permit := none, released := s.released ++ [r] } : JournalState).permit ≠ some r := by
  simp

/-- A real external authority must serialize contenders; equal checkpoint comparisons do not.
Key scoping is explicit. Tickets bind both the reservation context and the contender identity. -/
structure AnchorTicket where
  epoch : Nat
  owner : Nat
  context : Reservation
  deriving Repr, DecidableEq

structure AnchorService where
  keyId : Bytes
  nextEpoch : Nat
  tickets : List AnchorTicket := []
  spent : List Nat := []
  deriving Repr, DecidableEq

/-- Linearizable authenticated compare-and-advance, durable in an independent failure domain.
This is the additional external service contract a deployment must supply. -/
def anchorCAS (s : AnchorService) (expected owner : Nat) (r : Reservation) :
    AnchorService × Option AnchorTicket :=
  if expected = s.nextEpoch ∧ r.keyId = s.keyId ∧
      reservationValid s.keyId (s.tickets.map (·.context)) r = true then
    let t : AnchorTicket := ⟨expected, owner, r⟩
    ({ s with nextEpoch := expected + 1, tickets := s.tickets ++ [t] }, some t)
  else (s, none)

theorem anchorCAS_success {s s' : AnchorService} {expected owner : Nat}
    {r : Reservation} {t : AnchorTicket} (h : anchorCAS s expected owner r = (s', some t)) :
    s'.nextEpoch = s.nextEpoch + 1 ∧ t.epoch = s.nextEpoch ∧
    t.owner = owner ∧ t.context = r ∧ r.keyId = s.keyId := by
  unfold anchorCAS at h
  split at h
  · next hg => cases h; simp [hg.1, hg.2.1]
  · cases h

/-- Two disk clones with the same observed generation cannot both reserve it, even when
both possess valid local MACs and the same checkpoint. -/
theorem anchorCAS_fences_clone {s s' : AnchorService} {expected owner : Nat}
    {r : Reservation} {t : AnchorTicket} (h : anchorCAS s expected owner r = (s', some t))
    (otherOwner : Nat) (otherContext : Reservation) :
    (anchorCAS s' expected otherOwner otherContext).2 = none := by
  have hs := anchorCAS_success h
  have he : expected = s.nextEpoch := by
    unfold anchorCAS at h
    split at h
    · next hg => exact hg.1
    · cases h
  have hn : expected ≠ s'.nextEpoch := by omega
  simp [anchorCAS, hn]

/-- Consuming the server ticket fences even a clone of client memory made after issuance.
A deployment that only advances on reserve but copies live permits across clones lacks this
protection. Consumption must itself be authenticated and durably linearized by the service. -/
def anchorConsume (s : AnchorService) (ticket : AnchorTicket) : Option AnchorService :=
  if ticket ∈ s.tickets ∧ ticket.epoch ∉ s.spent then
    some { s with spent := ticket.epoch :: s.spent }
  else none

theorem anchorConsume_preserves_next {s s' : AnchorService} {ticket : AnchorTicket}
    (h : anchorConsume s ticket = some s') : s'.nextEpoch = s.nextEpoch := by
  unfold anchorConsume at h
  split at h
  · cases h; rfl
  · cases h

theorem anchorConsume_once {s s' : AnchorService} {ticket : AnchorTicket}
    (h : anchorConsume s ticket = some s') : anchorConsume s' ticket = none := by
  unfold anchorConsume at h
  split at h
  · cases h; simp [anchorConsume]
  · cases h

/-- The CAS history check rejects reuse of the reserved resource, even with a fresh serial. -/
theorem anchorCAS_no_duplicate_context {s s' : AnchorService} {expected owner : Nat}
    {r : Reservation} {t : AnchorTicket} (h : anchorCAS s expected owner r = (s', some t)) :
    ∀ old ∈ s.tickets, old.context.ceremonyId ≠ r.ceremonyId ∧
      old.context.epochOrCodeword ≠ r.epochOrCodeword := by
  unfold anchorCAS at h
  split at h
  · next hg =>
    intro old ho
    exact reservationValid_fresh hg.2.2 _ (List.mem_map.mpr ⟨old, ho, rfl⟩)
  · cases h

theorem anchorCAS_tickets {s s' : AnchorService} {expected owner : Nat}
    {r : Reservation} {t : AnchorTicket} (h : anchorCAS s expected owner r = (s', some t)) :
    s'.tickets = s.tickets ++ [t] := by
  unfold anchorCAS at h
  split at h
  · cases h; rfl
  · cases h

theorem anchorConsume_tickets {s s' : AnchorService} {ticket : AnchorTicket}
    (h : anchorConsume s ticket = some s') : s'.tickets = s.tickets := by
  unfold anchorConsume at h
  split at h
  · cases h; rfl
  · cases h

private theorem nodup_map_of_injOn {α β γ : Type} (f : α → β) (g : α → γ) :
    ∀ xs : List α, (xs.map g).Nodup →
      (∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b) → (xs.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: rest, hg, hInj => by
    rw [List.map_cons, List.Nodup, List.pairwise_cons] at hg ⊢
    refine ⟨?_, nodup_map_of_injOn f g rest hg.2
      (fun x hx y hy => hInj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))⟩
    intro y hy hEq
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
    have hab : a = b := hInj a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb) hEq
    exact hg.1 (g b) (List.mem_map_of_mem hb) (by rw [hab])

/-- Local stages are rollbackable; the external service is not. No ticket is issued by a disk
restore, a crash, a local write, or a caller-created output record. -/
structure AnchoredJournal where
  service : AnchorService
  localBytes : Bytes
  localDurable : Option Reservation := none
  staged : Option Reservation := none
  pending : Option AnchorTicket := none
  released : List AnchorTicket := []

inductive AnchoredJournalStep : AnchoredJournal → AnchoredJournal → Prop where
  | stage (s : AnchoredJournal) (r : Reservation) :
      AnchoredJournalStep s { s with staged := some r, pending := none, localDurable := none }
  | localCommit (s : AnchoredJournal) (bytes : Bytes) (r : Reservation)
      (staged : s.staged = some r) :
      AnchoredJournalStep s { s with localBytes := bytes, localDurable := some r }
  | reserve (s : AnchoredJournal) (r : Reservation) (owner expected : Nat)
      (service : AnchorService) (ticket : AnchorTicket)
      (staged : s.staged = some r) (durable : s.localDurable = some r)
      (cas : anchorCAS s.service expected owner r = (service, some ticket)) :
      AnchoredJournalStep s { s with service, pending := some ticket, staged := none }
  | release (s : AnchoredJournal) (t : AnchorTicket) (service : AnchorService)
      (owned : s.pending = some t) (durable : s.localDurable = some t.context)
      (consumed : anchorConsume s.service t = some service) :
      AnchoredJournalStep s { s with service, pending := none, released := s.released ++ [t] }
  | crash (s : AnchoredJournal) :
      AnchoredJournalStep s { s with staged := none, pending := none }
  | restoreDisk (s : AnchoredJournal) (bytes : Bytes) :
      AnchoredJournalStep s { s with localBytes := bytes, localDurable := none }

/-- Ticket serials are released at most once, and everything released or pending is a ticket
the service actually issued; the service never issued two tickets for one codeword/leaf or one
ceremony id. -/
def AnchoredJournalInv (s : AnchoredJournal) : Prop :=
  (s.released.map (·.epoch)).Nodup ∧
  (∀ t ∈ s.released, t.epoch < s.service.nextEpoch) ∧
  (∀ t, s.pending = some t → t.epoch < s.service.nextEpoch ∧
    ∀ u ∈ s.released, u.epoch ≠ t.epoch) ∧
  (s.service.tickets.map (·.context.epochOrCodeword)).Nodup ∧
  (s.service.tickets.map (·.context.ceremonyId)).Nodup ∧
  (∀ t ∈ s.released, t ∈ s.service.tickets) ∧
  (∀ t, s.pending = some t → t ∈ s.service.tickets)

theorem anchoredJournalStep_preserves {s t : AnchoredJournal}
    (step : AnchoredJournalStep s t) (inv : AnchoredJournalInv s) : AnchoredJournalInv t := by
  obtain ⟨hn, hl, hp, hCw, hCid, hRel, hPend⟩ := inv
  cases step with
  | stage r => exact ⟨hn, hl, by intro t h; simp at h, hCw, hCid, hRel, by intro t h; simp at h⟩
  | localCommit bytes r staged => exact ⟨hn, hl, hp, hCw, hCid, hRel, hPend⟩
  | restoreDisk bytes => exact ⟨hn, hl, hp, hCw, hCid, hRel, hPend⟩
  | crash => exact ⟨hn, hl, by intro t h; simp at h, hCw, hCid, hRel, by intro t h; simp at h⟩
  | reserve r owner expected service ticket staged durable cas =>
    obtain ⟨hs, ht, _, hCtx, _⟩ := anchorCAS_success cas
    have hT := anchorCAS_tickets cas
    have hFresh := anchorCAS_no_duplicate_context cas
    refine ⟨hn, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t hm; have := hl t hm; dsimp; omega
    · intro t he
      have heq := Option.some.inj he
      subst t
      refine ⟨by dsimp; omega, ?_⟩
      intro u hu; have := hl u hu; omega
    · dsimp only
      rw [hT, List.map_append]
      apply journal_nodup_snoc hCw
      intro v hv
      obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hv
      show old.context.epochOrCodeword ≠ ticket.context.epochOrCodeword
      rw [hCtx]
      exact (hFresh old ho).2
    · dsimp only
      rw [hT, List.map_append]
      apply journal_nodup_snoc hCid
      intro v hv
      obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hv
      show old.context.ceremonyId ≠ ticket.context.ceremonyId
      rw [hCtx]
      exact (hFresh old ho).1
    · intro t hm
      dsimp only
      rw [hT]
      exact List.mem_append_left _ (hRel t hm)
    · intro t he
      have heq := Option.some.inj he
      subst t
      dsimp only
      rw [hT]
      exact List.mem_append_right _ (List.mem_singleton_self _)
  | release t service owned durable consumed =>
    have hepoch := anchorConsume_preserves_next consumed
    have hT := anchorConsume_tickets consumed
    obtain ⟨ht, hf⟩ := hp t owned
    refine ⟨?_, ?_, by intro u h; simp at h, ?_, ?_, ?_, by intro u h; simp at h⟩
    · rw [List.map_append]
      apply journal_nodup_snoc hn
      intro e he
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp he
      exact hf u hu
    · intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · dsimp; rw [hepoch]; exact hl u hu
      · obtain rfl := List.mem_singleton.mp hu; dsimp; rw [hepoch]; exact ht
    · dsimp only; rw [hT]; exact hCw
    · dsimp only; rw [hT]; exact hCid
    · intro u hu
      dsimp only
      rw [hT]
      rcases List.mem_append.mp hu with hu | hu
      · exact hRel u hu
      · obtain rfl := List.mem_singleton.mp hu; exact hPend _ owned

/-- **Anchored release never reuses a resource**: the released tickets carry pairwise distinct
codewords/leaf epochs and pairwise distinct ceremony ids, whatever happened to the local disk
(`restoreDisk` replaces it by arbitrary bytes at any time). -/
theorem anchoredJournal_released_resources_unique {s : AnchoredJournal}
    (inv : AnchoredJournalInv s) :
    (s.released.map (·.context.epochOrCodeword)).Nodup ∧
    (s.released.map (·.context.ceremonyId)).Nodup := by
  obtain ⟨hn, _, _, hCw, hCid, hRel, _⟩ := inv
  exact ⟨nodup_map_of_injOn _ (·.epoch) s.released hn
      (fun a ha b hb h => eq_of_mem_of_map_nodup hCw (hRel a ha) (hRel b hb) h),
    nodup_map_of_injOn _ (·.epoch) s.released hn
      (fun a ha b hb h => eq_of_mem_of_map_nodup hCid (hRel a ha) (hRel b hb) h)⟩

theorem anchoredJournal_initial_inv (keyId localBytes : Bytes) (nextEpoch : Nat) :
    AnchoredJournalInv { service := { keyId, nextEpoch }, localBytes } :=
  ⟨List.nodup_nil, fun _ h => (by cases h), fun _ h => (by cases h), List.nodup_nil,
    List.nodup_nil, fun _ h => (by cases h), fun _ h => (by cases h)⟩

inductive AnchoredJournalRun : AnchoredJournal → AnchoredJournal → Prop where
  | refl (s) : AnchoredJournalRun s s
  | next {s t u} : AnchoredJournalRun s t → AnchoredJournalStep t u → AnchoredJournalRun s u

theorem anchoredJournal_trace_no_reuse {s t : AnchoredJournal}
    (run : AnchoredJournalRun s t) (inv : AnchoredJournalInv s) : AnchoredJournalInv t := by
  induction run with
  | refl => exact inv
  | next run step ih => exact anchoredJournalStep_preserves step ih

private def advancePc : Nat → ReplacePc → ReplacePc
  | 0, pc => pc
  | n+1, pc => nextReplacePc (advancePc n pc)

private theorem advanceJournal (key : Bytes) (s : JournalState) (r : Reservation)
    (healthy : s.poisoned = false) (staged : s.staged = some r) (n : Nat) :
    JournalRun key s { s with pc := advancePc n s.pc } := by
  induction n with
  | zero => simpa [advancePc] using JournalRun.refl (key := key) s
  | succ n ih =>
    exact JournalRun.next ih (JournalStep.advance _ r healthy staged)

private theorem journalRun_trans {key : Bytes} {s t u : JournalState}
    (a : JournalRun key s t) (b : JournalRun key t u) : JournalRun key s u := by
  induction b with
  | refl => exact a
  | next run step ih => exact JournalRun.next ih step

/-- Non-vacuity: an actual ten-syscall reservation path issues a permit and releases exactly
one reservation. The MAC is the concrete cSHAKE encoder in the read-back guard. The proof
never substitutes an insecure test MAC or assumes a forged receipt. -/
theorem journal_successful_release (key keyId lockSeal : Bytes) (r : Reservation)
    (wf : r.WellFormed) (valid : reservationValid keyId [] r = true) :
    ∃ s, JournalRun key (initialJournal keyId lockSeal) s ∧ s.released = [r] := by
  let start := initialJournal keyId lockSeal
  let staging : JournalState := { start with staged := some r, permit := none, pc := .checkBefore }
  have hbegin : JournalRun key start staging :=
    JournalRun.next (.refl _) (.begin start r rfl rfl wf valid)
  have hsync := advanceJournal key staging r rfl rfl 10
  let synced : JournalState := { staging with pc := .done }
  have hd : JournalRun key staging synced := by
    simpa only [advancePc, nextReplacePc, staging] using hsync
  let committed : JournalState := { synced with entries := [r], staged := none, permit := some r }
  have hc : JournalRun key start committed :=
    JournalRun.next (journalRun_trans hbegin hd) (.committed synced r rfl rfl rfl valid)
  let released : JournalState := { committed with permit := none, released := [r] }
  refine ⟨released, ?_, rfl⟩
  exact JournalRun.next hc (.consume committed r
    (ceremonyBytes key lockSeal keyId [r]) rfl rfl rfl rfl)

theorem witness_real_cshake_journal_release :
    let keyId : Bytes := List.replicate 32 4
    let r : Reservation := ⟨List.replicate 32 1, keyId, List.replicate 32 2, 1, 1⟩
    ∃ s, JournalRun (List.replicate 32 5)
      (initialJournal keyId (List.replicate 8 6)) s ∧ s.released = [r] := by
  dsimp only
  apply journal_successful_release
  · exact reservation_fixture_wellFormed
  · change reservationValid (List.replicate 32 4) [] _ = true
    exact reservationValid_empty_self ⟨List.replicate 32 1, List.replicate 32 4, List.replicate 32 2, 1, 1⟩

/-- Full v3 attempt machine, including explicit retries. Unlike the fresh-only machine,
codeword repetitions are legal; the theorem tracks fresh attempt identities and durable history. -/
structure RetryJournalState where
  keyId : Bytes
  macKey : Bytes := []
  lockSeal : Bytes := []
  entries : List JournalEntry := []
  staged : Option JournalEntry := none
  permit : Option JournalEntry := none
  pc : ReplacePc := .done
  poisoned : Bool := false
  released : List JournalEntry := []

inductive RetryJournalStep : RetryJournalState → RetryJournalState → Prop where
  | begin (s : RetryJournalState) (e : JournalEntry)
      (healthy : s.poisoned = false) (idle : s.staged = none)
      (valid : journalEntryValid s.keyId s.entries e = true) :
      RetryJournalStep s { s with staged := some e, permit := none, pc := .checkBefore }
  | advance (s : RetryJournalState) (e : JournalEntry)
      (healthy : s.poisoned = false) (staged : s.staged = some e) :
      RetryJournalStep s { s with pc := nextReplacePc s.pc }
  | committed (s : RetryJournalState) (e : JournalEntry)
      (healthy : s.poisoned = false) (staged : s.staged = some e) (synced : s.pc = .done)
      (valid : journalEntryValid s.keyId s.entries e = true) :
      RetryJournalStep s { s with entries := s.entries ++ [e], staged := none, permit := some e }
  | consume (s : RetryJournalState) (e : JournalEntry) (readBack : Bytes) (expected : CeremonyContext)
      (healthy : s.poisoned = false) (owned : s.permit = some e)
      (current : s.entries.getLast? = some e)
      (verified : verifyCurrentPermitWithContext s.macKey s.lockSeal s.keyId s.entries
        ⟨s.entries.length + 1, ceremonyTag s.macKey s.lockSeal (ceremonyBodyV3 s.keyId s.entries)⟩
        readBack ⟨e, s.entries.length + 1, s.lockSeal⟩ expected = true) :
      RetryJournalStep s { s with permit := none, released := s.released ++ [e] }
  | ioError (s : RetryJournalState) :
      RetryJournalStep s { s with poisoned := true, pc := .poisoned, permit := none }
  | crash (s : RetryJournalState) :
      RetryJournalStep s { s with staged := none, permit := none, pc := .done }
  | crashPublishes (s : RetryJournalState) (e : JournalEntry)
      (staged : s.staged = some e) (cut : mayPublishAfterCrash s.pc)
      (valid : journalEntryValid s.keyId s.entries e = true) :
      RetryJournalStep s { s with entries := s.entries ++ [e], staged := none, permit := none, pc := .done }
  | reopen (s : RetryJournalState) (readBack : Bytes)
      (verified : openCeremonyBytesV3 s.macKey s.lockSeal s.keyId readBack
        ⟨s.entries.length + 1, ceremonyTag s.macKey s.lockSeal (ceremonyBodyV3 s.keyId s.entries)⟩
        = some (s.entries.length + 1, s.entries)) :
      RetryJournalStep s { s with poisoned := false, staged := none, permit := none, pc := .done }

def RetryJournalInv (s : RetryJournalState) : Prop :=
  (s.released.map (·.reservation.ceremonyId)).Nodup ∧
  (∀ e ∈ s.released, e ∈ s.entries) ∧
  (∀ e, s.permit = some e → e ∈ s.entries ∧
    ∀ old ∈ s.released, old.reservation.ceremonyId ≠ e.reservation.ceremonyId)

theorem retryJournalStep_preserves {s t : RetryJournalState}
    (step : RetryJournalStep s t) (inv : RetryJournalInv s) : RetryJournalInv t := by
  obtain ⟨hn, hm, hp⟩ := inv
  cases step with
  | begin e healthy idle valid => exact ⟨hn, hm, by intro e h; simp at h⟩
  | advance e healthy staged => exact ⟨hn, hm, hp⟩
  | committed e healthy staged synced valid =>
    refine ⟨hn, fun old ho => List.mem_append_left _ (hm old ho), ?_⟩
    intro r he
    obtain rfl := Option.some.inj he
    exact ⟨List.mem_append_right _ (List.mem_singleton_self _),
      fun old ho => journalEntryValid_fresh_attempt valid old (hm old ho)⟩
  | consume e readBack expected healthy owned current verified =>
    obtain ⟨he, hf⟩ := hp e owned
    refine ⟨?_, ?_, by intro e h; simp at h⟩
    · rw [List.map_append]
      apply journal_nodup_snoc hn
      intro x hx
      obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hx
      exact hf old ho
    · intro old ho
      rcases List.mem_append.mp ho with ho | ho
      · exact hm old ho
      · obtain rfl := List.mem_singleton.mp ho; exact he
  | ioError => exact ⟨hn, hm, by intro e h; simp at h⟩
  | crash => exact ⟨hn, hm, by intro e h; simp at h⟩
  | crashPublishes e staged cut valid =>
    exact ⟨hn, fun old ho => List.mem_append_left _ (hm old ho), by intro e h; simp at h⟩
  | reopen readBack verified => exact ⟨hn, hm, by intro e h; simp at h⟩

inductive RetryJournalRun : RetryJournalState → RetryJournalState → Prop where
  | refl (s) : RetryJournalRun s s
  | next {s t u} : RetryJournalRun s t → RetryJournalStep t u → RetryJournalRun s u

theorem retryJournal_trace_no_attempt_reuse {s t : RetryJournalState}
    (run : RetryJournalRun s t) (inv : RetryJournalInv s) : RetryJournalInv t := by
  induction run with
  | refl => exact inv
  | next run step ih => exact retryJournalStep_preserves step ih

end RustDurability


/-- Exact 16-byte ASCII domain tag `"QSAG.R_COMMIT/v1"` matching `R_COMMIT_DOMAIN_V1` in
    `crates/qsag-core/src/fips205.rs`. -/
def rCommitDomainV1 : List Nat :=
  [81, 83, 65, 71, 46, 82, 95, 67, 79, 77, 77, 73, 84, 47, 118, 49]

/-- Structured input to a Round-1 `QSAG.R_COMMIT/v1` randomizer commitment of width `rw` bits. -/
structure HedgedRCommitInput (rw : Nat) where
  sid : BitVec 256
  partyId : BitVec 64
  rShare : BitVec rw
  openSalt : BitVec 256
  deriving Repr, DecidableEq

/-- Length-framed preimage encoding `"QSAG.R_COMMIT/v1" || sid || partyId || rw || rShare || openSalt`. -/
def encodeHedgedRCommitV1 {rw : Nat} (inp : HedgedRCommitInput rw) : List Nat :=
  rCommitDomainV1 ++ [inp.sid.toNat, inp.partyId.toNat, rw, inp.rShare.toNat, inp.openSalt.toNat]

/-- Evaluate the `QSAG.R_COMMIT/v1` commitment under a 256-bit hash function `H`. -/
def evalHedgedRCommitV1 {rw : Nat} (H : List Nat → Digest256) (inp : HedgedRCommitInput rw) :
    Digest256 :=
  H (encodeHedgedRCommitV1 inp)

/-- Concrete hash collision witness (`x₁ ≠ x₂ ∧ H x₁ = H x₂`). -/
def RCommitHashCollision (H : List Nat → Digest256) : Prop :=
  ∃ x₁ x₂ : List Nat, x₁ ≠ x₂ ∧ H x₁ = H x₂

/-- Length-framed `encodeHedgedRCommitV1` is strictly injective across all fields. -/
theorem encodeHedgedRCommitV1_injective {rw : Nat}
    {a b : HedgedRCommitInput rw}
    (hEq : encodeHedgedRCommitV1 a = encodeHedgedRCommitV1 b) : a = b := by
  unfold encodeHedgedRCommitV1 at hEq
  have hTail := List.append_cancel_left hEq
  injection hTail with hSid t1
  injection t1 with hPid t2
  injection t2 with _ t3
  injection t3 with hR t4
  injection t4 with hSalt _
  cases a; cases b
  dsimp only at hSid hPid hR hSalt
  congr
  · exact BitVec.eq_of_toNat_eq hSid
  · exact BitVec.eq_of_toNat_eq hPid
  · exact BitVec.eq_of_toNat_eq hR
  · exact BitVec.eq_of_toNat_eq hSalt

/-- **Binding of `QSAG.R_COMMIT/v1`**: any two valid openings matching the same Round-1 commitment
    digest either agree on every field (`sid`, `partyId`, `rShare`, `openSalt`) or yield an explicit
    hash collision for `H`. -/
theorem rCommitV1_binding_or_collision {rw : Nat}
    (H : List Nat → Digest256) (inp₁ inp₂ : HedgedRCommitInput rw)
    (hDigest : evalHedgedRCommitV1 H inp₁ = evalHedgedRCommitV1 H inp₂) :
    inp₁ = inp₂ ∨ RCommitHashCollision H := by
  by_cases hSame : inp₁ = inp₂
  · exact Or.inl hSame
  · refine Or.inr ⟨encodeHedgedRCommitV1 inp₁, encodeHedgedRCommitV1 inp₂, ?_, hDigest⟩
    intro hEnc
    exact hSame (encodeHedgedRCommitV1_injective hEnc)

/-- Unbiased uniform randomizer enumeration over `BitVec rw`. -/
def decodeUniformRand (rw : Nat) : Fin (2 ^ rw) → BitVec rw :=
  (enumBitVec rw).toFun

/-- Coin-tossed hedged randomizer `R = rHonest ^^^ rCorrupt` indexed by honest share `i : Fin (2 ^ rw)`
    for a Round-1 committed corrupt share `rCorrupt : BitVec rw`. -/
def decodeCoinTossRand {rw : Nat} (rCorrupt : BitVec rw) : Fin (2 ^ rw) → BitVec rw :=
  fun i => (enumBitVec rw).toFun i ^^^ rCorrupt

/-- **Coin-Toss Uniformity Invariance**: for any fixed (Round-1 committed) `rCorrupt : BitVec rw`
    and any weight `weight : BitVec rw → Nat`, XORing with `rCorrupt` permutes `BitVec rw`
    bijectively, preserving all finite sums and every bit marginal. -/
theorem coinTossRand_sum_invariant {rw : Nat} (rCorrupt : BitVec rw)
    (weight : BitVec rw → Nat) :
    qsum (2 ^ rw) (fun i => weight (decodeCoinTossRand rCorrupt i)) =
      qsum (2 ^ rw) (fun i => weight (decodeUniformRand rw i)) := by
  let enumR := enumBitVec rw
  let bij := maskBijectionBitVec rw rCorrupt
  let π : Fin (2 ^ rw) → Fin (2 ^ rw) := fun i => enumR.invFun (bij.toFun (enumR.toFun i))
  have hInv : ∀ i : Fin (2 ^ rw), π (π i) = i := by
    intro i
    dsimp only [π]
    have hBijInv : ∀ x : BitVec rw, bij.toFun (bij.toFun x) = x := bij.left_inv
    rw [enumR.right_inv, hBijInv, enumR.left_inv]
  have hPerm := qsum_perm_invariant π π hInv hInv (fun j => weight (enumR.toFun j))
  have hCong :
      qsum (2 ^ rw) (fun i => weight (decodeCoinTossRand rCorrupt i)) =
      qsum (2 ^ rw) (fun i => weight (enumR.toFun (π i))) := by
    apply qsum_congr
    intro i
    dsimp only [decodeCoinTossRand, π, bij, maskBijectionBitVec]
    rw [enumR.right_inv, BitVec.xor_comm]
  exact hCong.trans hPerm

/-- Every target `w`-bit randomizer `targetR` has exact honest-share fiber cardinality `1` under
    committed coin-tossing `R = rHonest ^^^ rCorrupt`. -/
theorem coinTossRand_exact_fiber_one {rw : Nat} (rCorrupt targetR : BitVec rw) :
    qsum (2 ^ rw) (fun i => if decodeCoinTossRand rCorrupt i = targetR then 1 else 0) = 1 := by
  rw [coinTossRand_sum_invariant rCorrupt (fun r => if r = targetR then 1 else 0)]
  let iStar := (enumBitVec rw).invFun targetR
  have hCong :
      qsum (2 ^ rw) (fun i => if decodeUniformRand rw i = targetR then 1 else 0) =
      qsum (2 ^ rw) (fun i => if i = iStar then 1 else 0) := by
    apply qsum_congr
    intro i
    dsimp only [decodeUniformRand]
    by_cases hEq : i = iStar
    · subst hEq
      have hR : (enumBitVec rw).toFun ((enumBitVec rw).invFun targetR) = targetR :=
        (enumBitVec rw).right_inv targetR
      simp only [iStar, hR, ↓reduceIte]
    · have hNe : (enumBitVec rw).toFun i ≠ targetR := by
        intro hv
        apply hEq
        have := congrArg (enumBitVec rw).invFun hv
        simpa [iStar, (enumBitVec rw).left_inv] using this
      simp only [hEq, hNe, ↓reduceIte]
  rw [hCong, qsum_eq_indicator]


def execDetPostRound3Rushing {SK Msg CorruptIn : Type} {Q w : Nat}
    (spec : CutTheHashProtocolSpec SK Msg Unit CorruptIn Q w)
    (sk : SK) (msg : Msg) (adv : RushingCorruptStrategy CorruptIn Q w) (hQ : 0 < Q)
    (m : HonestPreOpenMasks Q w)
    (abortPostRound3 : AdvPreOpenView Q w → BitVec w → Bool) : Option (BitVec w) :=
  if abortPostRound3
      (evalPreOpenView spec sk msg () adv hQ m)
      (spec.yShareHonest sk msg () (corruptContribution adv (evalPreOpenView spec sk msg () adv hQ m)) ^^^
       spec.yShareCorrupt sk msg () (corruptContribution adv (evalPreOpenView spec sk msg () adv hQ m)))
  then none
  else
    some (spec.yShareHonest sk msg () (corruptContribution adv (evalPreOpenView spec sk msg () adv hQ m)) ^^^
      spec.yShareCorrupt sk msg () (corruptContribution adv (evalPreOpenView spec sk msg () adv hQ m)))

/-- Total surviving runs under post-Round-3 signature-inspecting selective abort. -/
def detPostRound3SurviveCount {SK Msg CorruptIn : Type} {Q w : Nat}
    (spec : CutTheHashProtocolSpec SK Msg Unit CorruptIn Q w)
    (sk : SK) (msg : Msg) (adv : RushingCorruptStrategy CorruptIn Q w) (hQ : 0 < Q)
    (abortPostRound3 : AdvPreOpenView Q w → BitVec w → Bool) : Nat :=
  qsum (preOpenMaskCard Q w) (fun mIdx =>
    optSomeIndicator (execDetPostRound3Rushing spec sk msg adv hQ
      ((enumHonestPreOpenMasks Q w).toFun mIdx) abortPostRound3))

/-- Surviving signature count for `targetSig` under post-Round-3 rushing abort. -/
def detPostRound3SigCount {SK Msg CorruptIn : Type} {Q w : Nat}
    (spec : CutTheHashProtocolSpec SK Msg Unit CorruptIn Q w)
    (sk : SK) (msg : Msg) (adv : RushingCorruptStrategy CorruptIn Q w) (hQ : 0 < Q)
    (abortPostRound3 : AdvPreOpenView Q w → BitVec w → Bool)
    (targetSig : BitVec w) : Nat :=
  qsum (preOpenMaskCard Q w) (fun mIdx =>
    if execDetPostRound3Rushing spec sk msg adv hQ
        ((enumHonestPreOpenMasks Q w).toFun mIdx) abortPostRound3 = some targetSig
    then 1 else 0)

/-- Cross-multiplied L1 statistical distance numerator comparing surviving post-Round-3 runs against
    the deterministic standalone signature `spec.finalSignature sk msg ()`. -/
def detPostRound3StatDistNum {SK Msg CorruptIn : Type} {Q w : Nat}
    (spec : CutTheHashProtocolSpec SK Msg Unit CorruptIn Q w)
    (sk : SK) (msg : Msg) (adv : RushingCorruptStrategy CorruptIn Q w) (hQ : 0 < Q)
    (abortPostRound3 : AdvPreOpenView Q w → BitVec w → Bool) : Nat :=
  let survive := detPostRound3SurviveCount spec sk msg adv hQ abortPostRound3
  qsum (2 ^ w) (fun sIdx =>
    let sig := (enumBitVec w).toFun sIdx
    natAbsDiff
      (detPostRound3SigCount spec sk msg adv hQ abortPostRound3 sig)
      ((if spec.finalSignature sk msg () = sig then 1 else 0) * survive))

/-- **Post-Round-3 Rushing Selective-Abort Unbiasedness (`post_round3_rushing_abort_unbiased`)**:
    1. **Round-1 `QSAG.R_COMMIT/v1` Binding**: Any rushing opening `inp'` matching the Round-1
       commitment `evalHedgedRCommitV1 H inp` satisfies `inp'.rShare = inp.rShare` unless
       `RCommitHashCollision H`.
    2. **Hedged Coin-Toss + Cut-the-Hash Zero Bias (`Δ = 0`)**: With `inp.rShare` bound in Round 1,
       coin-tossed `R = rHonest ^^^ inp.rShare` has exact fiber `1` per `targetR : BitVec rw`,
       surviving runs factor as `2 ^ rw * viewMaskSurviveCount abortPreOpen` (independent of `R`),
       and surviving signatures match the **unbiased** uniform-`R` standalone signer (`decodeUniformRand rw`)
       with `abortConditionedStatDistNum = 0`.
    3. **Deterministic Pre-Fixed `R` Post-Round-3 Signature-Dependent Abort (`Δ = 0`)**: When `R` is
       uniquely fixed prior to Round-3 share opening, even an arbitrary post-Round-3 rushing abort
       predicate `abortPostRound3 : AdvPreOpenView Q w → BitVec w → Bool` inspecting the
       reconstructed signature scales acceptance rate `survive = viewMaskSurviveCount (fun v => abortPostRound3 v (singleSign sk msg))`
       while keeping conditional signature distance **identically zero** (`detPostRound3StatDistNum = 0`,
       and every surviving output equals `spec.finalSignature sk msg ()`). -/
theorem post_round3_rushing_abort_unbiased
    {SK Msg CorruptIn : Type} {Q w rw : Nat}
    (H : List Nat → Digest256)
    (inp : HedgedRCommitInput rw)
    (hedgedSpec : CutTheHashProtocolSpec SK Msg (BitVec rw) CorruptIn Q w)
    (detSpec : CutTheHashProtocolSpec SK Msg Unit CorruptIn Q w)
    (sk : SK) (msg : Msg)
    (adv : RushingCorruptStrategy CorruptIn Q w) (hQ : 0 < Q)
    (abortPreOpen : AdvPreOpenView Q w → Bool)
    (hSurviveHedged : NonZeroSurvivingRuns hedgedSpec sk msg (2 ^ rw)
      (decodeCoinTossRand inp.rShare) adv hQ abortPreOpen)
    (abortPostRound3 : AdvPreOpenView Q w → BitVec w → Bool) :
    let totalHedged := totalSurvivingRuns hedgedSpec sk msg (2 ^ rw)
      (decodeCoinTossRand inp.rShare) adv hQ abortPreOpen
    (∀ inp' : HedgedRCommitInput rw,
      evalHedgedRCommitV1 H inp = evalHedgedRCommitV1 H inp' →
        inp'.rShare = inp.rShare ∨ RCommitHashCollision H) ∧
    (∀ targetR : BitVec rw,
      qsum (2 ^ rw) (fun i => if decodeCoinTossRand inp.rShare i = targetR then 1 else 0) = 1) ∧
    totalHedged = 2 ^ rw * viewMaskSurviveCount abortPreOpen ∧
    (∀ targetSig : BitVec w,
      survivingRealSigCount hedgedSpec sk msg (2 ^ rw) (decodeCoinTossRand inp.rShare)
          adv hQ abortPreOpen targetSig * 2 ^ rw =
        idealStandaloneSigCount hedgedSpec sk msg (2 ^ rw) (decodeUniformRand rw) targetSig *
          totalHedged) ∧
    abortConditionedStatDistNum hedgedSpec sk msg (2 ^ rw) (decodeCoinTossRand inp.rShare)
        adv hQ abortPreOpen = 0 ∧
    detPostRound3SurviveCount detSpec sk msg adv hQ abortPostRound3 =
      viewMaskSurviveCount (fun v => abortPostRound3 v (detSpec.finalSignature sk msg ())) ∧
    detPostRound3StatDistNum detSpec sk msg adv hQ abortPostRound3 = 0 := by
  intro totalHedged
  have hCut := cutTheHash_abort_conditioned_sd_zero hedgedSpec sk msg (2 ^ rw)
    (decodeCoinTossRand inp.rShare) adv hQ abortPreOpen hSurviveHedged
  obtain ⟨_, hTotEq, hCrossCoin, hSdZero⟩ := hCut
  have hBind : ∀ inp' : HedgedRCommitInput rw,
      evalHedgedRCommitV1 H inp = evalHedgedRCommitV1 H inp' →
        inp'.rShare = inp.rShare ∨ RCommitHashCollision H := by
    intro inp' hDig
    rcases rCommitV1_binding_or_collision H inp inp' hDig with hEq | hColl
    · exact Or.inl (congrArg HedgedRCommitInput.rShare hEq.symm)
    · exact Or.inr hColl
  have hIdealUnbiased : ∀ targetSig : BitVec w,
      idealStandaloneSigCount hedgedSpec sk msg (2 ^ rw) (decodeCoinTossRand inp.rShare) targetSig =
        idealStandaloneSigCount hedgedSpec sk msg (2 ^ rw) (decodeUniformRand rw) targetSig := by
    intro targetSig
    unfold idealStandaloneSigCount
    exact coinTossRand_sum_invariant inp.rShare
      (fun r => if hedgedSpec.finalSignature sk msg r = targetSig then 1 else 0)
  have hCrossUnbiased : ∀ targetSig : BitVec w,
      survivingRealSigCount hedgedSpec sk msg (2 ^ rw) (decodeCoinTossRand inp.rShare)
          adv hQ abortPreOpen targetSig * 2 ^ rw =
        idealStandaloneSigCount hedgedSpec sk msg (2 ^ rw) (decodeUniformRand rw) targetSig *
          totalHedged := by
    intro targetSig
    rw [← hIdealUnbiased targetSig]
    exact hCrossCoin targetSig
  have hDetSurv : detPostRound3SurviveCount detSpec sk msg adv hQ abortPostRound3 =
      viewMaskSurviveCount (fun v => abortPostRound3 v (detSpec.finalSignature sk msg ())) := by
    unfold detPostRound3SurviveCount
    have hCong :
        qsum (preOpenMaskCard Q w) (fun mIdx =>
          optSomeIndicator (execDetPostRound3Rushing detSpec sk msg adv hQ
            ((enumHonestPreOpenMasks Q w).toFun mIdx) abortPostRound3)) =
        qsum (preOpenMaskCard Q w) (fun mIdx =>
          if abortPostRound3
              (evalPreOpenView detSpec sk msg () adv hQ ((enumHonestPreOpenMasks Q w).toFun mIdx))
              (detSpec.finalSignature sk msg ()) then 0 else 1) := by
      apply qsum_congr
      intro mIdx
      unfold execDetPostRound3Rushing
      rw [detSpec.reconstruct_eq, optSomeIndicator_ite]
    rw [hCong]
    exact preOpenView_sum_invariant detSpec sk msg () adv hQ
      (fun v => if abortPostRound3 v (detSpec.finalSignature sk msg ()) then 0 else 1)
  have hDetSig : ∀ targetSig : BitVec w,
      detPostRound3SigCount detSpec sk msg adv hQ abortPostRound3 targetSig =
        (if detSpec.finalSignature sk msg () = targetSig then 1 else 0) *
          detPostRound3SurviveCount detSpec sk msg adv hQ abortPostRound3 := by
    intro targetSig
    unfold detPostRound3SigCount detPostRound3SurviveCount
    by_cases hMatch : detSpec.finalSignature sk msg () = targetSig
    · simp only [hMatch, ↓reduceIte, Nat.one_mul]
      apply qsum_congr
      intro mIdx
      unfold execDetPostRound3Rushing
      rw [detSpec.reconstruct_eq, hMatch, indicator_ite_none_some, optSomeIndicator_ite]
      simp only [↓reduceIte]
    · simp only [hMatch, ↓reduceIte, Nat.zero_mul]
      have hZero :
          qsum (preOpenMaskCard Q w) (fun mIdx =>
            if execDetPostRound3Rushing detSpec sk msg adv hQ
                ((enumHonestPreOpenMasks Q w).toFun mIdx) abortPostRound3 = some targetSig
            then 1 else 0) =
          qsum (preOpenMaskCard Q w) (fun _ => 0) := by
        apply qsum_congr
        intro mIdx
        unfold execDetPostRound3Rushing
        rw [detSpec.reconstruct_eq, indicator_ite_none_some]
        simp only [hMatch, ↓reduceIte]
        cases abortPostRound3
          (evalPreOpenView detSpec sk msg () adv hQ ((enumHonestPreOpenMasks Q w).toFun mIdx))
          (detSpec.finalSignature sk msg ()) <;> rfl
      rw [hZero, qsum_const, Nat.mul_zero]
  have hDetSdZero : detPostRound3StatDistNum detSpec sk msg adv hQ abortPostRound3 = 0 := by
    unfold detPostRound3StatDistNum
    dsimp only
    have hAllZ :
        qsum (2 ^ w) (fun sIdx =>
          let sig := (enumBitVec w).toFun sIdx
          natAbsDiff
            (detPostRound3SigCount detSpec sk msg adv hQ abortPostRound3 sig)
            ((if detSpec.finalSignature sk msg () = sig then 1 else 0) *
              detPostRound3SurviveCount detSpec sk msg adv hQ abortPostRound3)) =
        qsum (2 ^ w) (fun _ => 0) := by
      apply qsum_congr
      intro sIdx
      dsimp only
      rw [hDetSig ((enumBitVec w).toFun sIdx)]
      simp [natAbsDiff_eq]
    rw [hAllZ, qsum_const, Nat.mul_zero]
  exact ⟨hBind, coinTossRand_exact_fiber_one inp.rShare, hTotEq, hCrossUnbiased, hSdZero,
    hDetSurv, hDetSdZero⟩

/-- `#tooth`: Without a binding Round-1 `QSAG.R_COMMIT/v1` commitment (`decodeCoinTossRand`), a
    rushing corrupt party that chooses `rCorrupt : BitVec 4 → BitVec 4` *after* observing the
    honest share `rHonest` (`rCorrupt rH := rH`) forces the least-significant bit `getLsbD 0` of
    `R = rHonest ^^^ rCorrupt rHonest` to `false` on **all `16 / 16` honest inputs**, whereas
    every Round-1 committed `rCommitted : BitVec 4` yields `getLsbD 0 = false` on **exactly
    `8 / 16` inputs** (a full 1-bit bias of `8 / 16 = 1 / 2`). -/
theorem tooth_uncommitted_round3_randomizer_biases_bit :
    ∃ corruptChooseR : BitVec 4 → BitVec 4,
      qsum (2 ^ 4) (fun i =>
        let rH := (enumBitVec 4).toFun i
        if (rH ^^^ corruptChooseR rH).getLsbD 0 = false then 1 else 0) = 16 ∧
      (∀ rCommitted : BitVec 4,
        qsum (2 ^ 4) (fun i =>
          if (decodeCoinTossRand rCommitted i).getLsbD 0 = false then 1 else 0) = 8) := by
  refine ⟨fun rH => rH, ?_, ?_⟩
  · have hAllOne :
        qsum (2 ^ 4) (fun i =>
          let rH := (enumBitVec 4).toFun i
          if (rH ^^^ rH).getLsbD 0 = false then 1 else 0) =
        qsum (2 ^ 4) (fun _ => 1) := by
      apply qsum_congr
      intro i
      dsimp only
      rw [BitVec.xor_self]
      rfl
    rw [hAllOne, qsum_const]
  · intro rCommitted
    rw [coinTossRand_sum_invariant rCommitted (fun r => if r.getLsbD 0 = false then 1 else 0)]
    decide

theorem witness_post_round3_rushing_abort_inhabited :
    ∃ (H : List Nat → Digest256)
      (inp : HedgedRCommitInput 2)
      (hedgedSpec : CutTheHashProtocolSpec (BitVec 2) (BitVec 2) (BitVec 2) (BitVec 2) 1 2)
      (detSpec : CutTheHashProtocolSpec (BitVec 2) (BitVec 2) Unit (BitVec 2) 1 2)
      (sk msg : BitVec 2)
      (adv : RushingCorruptStrategy (BitVec 2) 1 2)
      (hQ : 0 < 1)
      (abortPreOpen : AdvPreOpenView 1 2 → Bool),
      evalHedgedRCommitV1 H inp = 0#256 ∧
      detSpec.finalSignature sk msg () = sk ^^^ msg ∧
      NonZeroSurvivingRuns hedgedSpec sk msg (2 ^ 2) (decodeCoinTossRand inp.rShare)
        adv hQ abortPreOpen := by
  let hSpec : CutTheHashProtocolSpec (BitVec 2) (BitVec 2) (BitVec 2) (BitVec 2) 1 2 := {
    wireRingSecret := fun _ _ _ => ⟨0, Nat.zero_lt_one⟩
    wireXorSecret := fun sk _ _ cIn => sk ^^^ cIn
    yShareHonest := fun sk msg r cIn => (sk ^^^ msg ^^^ r) ^^^ cIn
    yShareCorrupt := fun _ _ _ cIn => cIn
    macShareHonest := fun _ msg _ _ => msg
    commitHiding := fun y mac => maskBijectionBitVec 2 (y ^^^ mac)
    finalSignature := fun sk msg r => sk ^^^ msg ^^^ r
    reconstruct_eq := fun sk msg r cIn => by bv_xor_cancel
  }
  let dSpec : CutTheHashProtocolSpec (BitVec 2) (BitVec 2) Unit (BitVec 2) 1 2 := {
    wireRingSecret := fun _ _ _ => ⟨0, Nat.zero_lt_one⟩
    wireXorSecret := fun sk _ _ cIn => sk ^^^ cIn
    yShareHonest := fun sk msg _ cIn => (sk ^^^ msg) ^^^ cIn
    yShareCorrupt := fun _ _ _ cIn => cIn
    macShareHonest := fun _ msg _ _ => msg
    commitHiding := fun y mac => maskBijectionBitVec 2 (y ^^^ mac)
    finalSignature := fun sk msg _ => sk ^^^ msg
    reconstruct_eq := fun sk msg _ cIn => by bv_xor_cancel
  }
  let inp0 : HedgedRCommitInput 2 := ⟨0#256, 1#64, 1#2, 0#256⟩
  let adv0 : RushingCorruptStrategy (BitVec 2) 1 2 := RushingCorruptStrategy.const (0#2)
  refine ⟨(fun _ => 0#256), inp0, hSpec, dSpec, 1#2, 2#2, adv0, Nat.zero_lt_one,
    (fun _ => false), rfl, rfl, ?_⟩
  unfold NonZeroSurvivingRuns
  rw [totalSurvivingRuns_eq]
  have hMaskPos : 0 < viewMaskSurviveCount (fun (_ : AdvPreOpenView 1 2) => false) := by
    unfold viewMaskSurviveCount
    rw [qsum_const]
    decide
  exact Nat.mul_pos (Nat.two_pow_pos 2) hMaskPos

#verify_constructive encodeHedgedRCommitV1_injective
#verify_constructive rCommitV1_binding_or_collision
#verify_constructive coinTossRand_sum_invariant
#verify_constructive coinTossRand_exact_fiber_one
#verify_constructive post_round3_rushing_abort_unbiased
#verify_constructive tooth_uncommitted_round3_randomizer_biases_bit
#verify_constructive witness_post_round3_rushing_abort_inhabited
#tooth_pair post_round3_rushing_abort_unbiased vs tooth_uncommitted_round3_randomizer_biases_bit
#verify_inhabited post_round3_rushing_abort_unbiased witness_post_round3_rushing_abort_inhabited

end Qsag
end

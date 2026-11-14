module
/-
# Qsag.InteractiveUcEngine — Multi-Round, Multi-Session Rushing-Adversary UC Execution Engine

Self-contained Lean 4.35 interactive Universal Composability execution engine (`0` proof gaps,
`0` custom axioms, `0 Classical.choice`, `≤ 12` `@[expose]`):
1. **Persistent Cross-Session `WalLatchState` & Non-Cloneable Custody (`HonestCustodyVault`)**:
   Models crash-idempotent monotonic epoch latching, enrolled public-key digest pinning, sticky
   active-fault quarantine (`walPoisonVault` irreversibly sets `poisoned = true` and wipes the
   in-memory secret key share), and strictly monotonic per-session mask-tape cursors.
2. **True Multi-Round, Multi-Session Rushing-Adversary Network Execution
   (`RealProtocolExec` vs `IdealFunctionalityExec`)**:
   In every round `k ∈ {1, 2, 3}` across `Q_s` adaptively scheduled signing sessions, an arbitrary
   stateful rushing adversary `A : UcRushingAdversary AdvState` inspects **all honest round-`k` wire
   `ByteArray` messages** before choosing corrupt-party round-`k` wire `ByteArray` messages,
   subject to a mandatory pre-cut consistency barrier prior to Round 3 and atomic WAL advance
   prior to `SignOk(sigBytes)` release.
3. **Zero-`Classical.choice` Game-Hopping & Compositional UC Combinators**:
   - `bad_event_fundamental_lemma`: Shoup's bad-event bound combined with measure-preserving
     random-tape bijections (`SimpleEquiv (Fin card) (Fin card)`).
   - `hybrid_multi_session_le`: Heterogeneous and homogeneous `Q_s`-session hybrid telescope.
   - `uc_transitive_composition`: Exact cross-cardinality rational statistical distance triangle
     inequality (`rationalAcceptDiff` / `ratAdd`) + contextual calling-protocol UC composition.
-/

public import Qsag.Constructive
public import Qsag.Goldilocks
public import Qsag.BinaryTower
public import Qsag.Keccak
public import Qsag.UcGames
public import Qsag.ThresholdApproval
public import Qsag.IdealTsig
import all Qsag.UcGames

public section
namespace Qsag

set_option autoImplicit false

/-! ## 1. Constructive `ByteArray` Wire Envelopes & Canonical `UcStepOutcome` -/

/-- Pack a byte list into a wire `ByteArray` with zero classical overhead. -/
@[expose] def packWire (bs : List UInt8) : ByteArray :=
  ByteArray.mk (Array.mk bs)

/-- Unpack a wire `ByteArray` into its underlying `List UInt8`. -/
@[expose] def unpackWire (w : ByteArray) : List UInt8 :=
  w.data.toList

@[simp] theorem unpackWire_packWire (bs : List UInt8) :
    unpackWire (packWire bs) = bs := rfl

@[simp] theorem packWire_unpackWire (w : ByteArray) :
    packWire (unpackWire w) = w := by
  cases w with
  | mk d =>
    cases d with
    | mk l => rfl

theorem packWire_injective {a b : List UInt8} (h : packWire a = packWire b) : a = b :=
  congrArg unpackWire h

theorem unpackWire_injective {a b : ByteArray} (h : unpackWire a = unpackWire b) : a = b := by
  rw [← packWire_unpackWire a, ← packWire_unpackWire b, h]

/-- Priority-2000 `0 Classical.choice` decidable equality for `ByteArray` via `unpackWire`. -/
instance (priority := 2000) constructiveByteArrayDecidableEq : DecidableEq ByteArray :=
  fun a b =>
    match decEq (unpackWire a) (unpackWire b) with
    | .isTrue h => .isTrue (unpackWire_injective h)
    | .isFalse h => .isFalse (fun hab => h (congrArg unpackWire hab))

/-- Canonical deterministic state-transition outcome supporting stateful quarantine on error. -/
inductive UcStepOutcome (S Out Err : Type) where
  | ok (nextState : S) (output : Out)
  | err (quarantinedState : S) (reason : Err)
  deriving DecidableEq, Repr

/-- Lift a partial `Option (S × Out)` transition into `UcStepOutcome` preserving state on `none`. -/
@[expose] def liftOptionStep {S In Out : Type} (step : S → In → Option (S × Out))
    (s : S) (inp : In) : UcStepOutcome S Out Unit :=
  match step s inp with
  | some (s', out) => .ok s' out
  | none => .err s ()

/-! ## 2. Persistent Cross-Session `WalLatchState` & Non-Cloneable Share Custody -/

/-- Persistent cross-session Write-Ahead-Log (`WAL`) latch state held by honest parties:
    1. `enrolledPkDigest`: 32-byte SHAKE256 digest pinning the enrolled public key,
    2. `nextEpoch`: strictly monotonic signing epoch counter,
    3. `latchedRecord`: optional `(epoch, msgDigest, cachedSigBytes)` for crash-retry idempotency,
    4. `poisoned`: sticky quarantine bit set irreversibly upon any active consistency/MAC fault. -/
structure WalLatchState where
  enrolledPkDigest : List UInt8
  nextEpoch        : Nat
  latchedRecord    : Option (Nat × List UInt8 × ByteArray)
  poisoned         : Bool
  deriving DecidableEq

/-- Exact reason a `WalLatchState` pre-sign or commit check refused a signing request. -/
inductive WalRejectReason where
  | poisonedQuarantine
  | pkDigestMismatch
  | staleOrOutOfOrderEpoch
  deriving DecidableEq, Repr

/-- Authorization result of `walPreSignStep`: either idempotent cached replay or fresh epoch grant. -/
inductive WalReserveOut where
  | replayCached (sigBytes : ByteArray)
  | authorizedFresh (reservedEpoch : Nat)
  deriving DecidableEq

/-- Well-formedness invariant on `WalLatchState`: 32-byte key digest and strictly bounded cache epoch. -/
def WalLatchState.WellFormed (st : WalLatchState) : Prop :=
  st.enrolledPkDigest.length = 32 ∧
  ∀ ep md sig, st.latchedRecord = some (ep, md, sig) → ep < st.nextEpoch

/-- Initialize a clean `WalLatchState` for an enrolled 32-byte public-key digest. -/
@[expose] def initWalLatchState (enrolledPkDigest : List UInt8) : WalLatchState :=
  { enrolledPkDigest := enrolledPkDigest
    nextEpoch        := 0
    latchedRecord    := none
    poisoned         := false }

/-- Irreversibly quarantine a `WalLatchState` upon detecting an active consistency or MAC fault. -/
@[expose] def walQuarantine (st : WalLatchState) : WalLatchState :=
  { st with poisoned := true }

/-- Pre-signing WAL gate: enforces `!poisoned`, `enrolledPkDigest` match, crash-idempotent replay,
    and monotonic `reqEpoch == nextEpoch` ordering. -/
def walPreSignStep (st : WalLatchState) (pkDigest : List UInt8)
    (reqEpoch : Nat) (msgDigest : List UInt8) :
    UcStepOutcome WalLatchState WalReserveOut WalRejectReason :=
  if st.poisoned then
    .err st .poisonedQuarantine
  else if !(decide (pkDigest = st.enrolledPkDigest)) then
    .err st .pkDigestMismatch
  else
    match st.latchedRecord with
    | some (ep, prevMd, prevSig) =>
      if reqEpoch == ep && decide (msgDigest = prevMd) then
        .ok st (.replayCached prevSig)
      else if reqEpoch == st.nextEpoch then
        .ok st (.authorizedFresh reqEpoch)
      else
        .err st .staleOrOutOfOrderEpoch
    | none =>
      if reqEpoch == st.nextEpoch then
        .ok st (.authorizedFresh reqEpoch)
      else
        .err st .staleOrOutOfOrderEpoch

theorem walPreSignStep_eq (st : WalLatchState) (pkDigest : List UInt8)
    (reqEpoch : Nat) (msgDigest : List UInt8) :
    walPreSignStep st pkDigest reqEpoch msgDigest =
      (if st.poisoned then .err st .poisonedQuarantine
       else if !(decide (pkDigest = st.enrolledPkDigest)) then .err st .pkDigestMismatch
       else match st.latchedRecord with
         | some (ep, prevMd, prevSig) =>
           if reqEpoch == ep && decide (msgDigest = prevMd) then .ok st (.replayCached prevSig)
           else if reqEpoch == st.nextEpoch then .ok st (.authorizedFresh reqEpoch)
           else .err st .staleOrOutOfOrderEpoch
         | none =>
           if reqEpoch == st.nextEpoch then .ok st (.authorizedFresh reqEpoch)
           else .err st .staleOrOutOfOrderEpoch) := by rfl

/-- Canonical post-authorization WAL commit transition shared identically by `walCommitBeforeRelease`,
    `execRealSession`, and `execIdealSession`: advances `nextEpoch := ep + 1` and persists
    `(ep, msgDigest, sigBytes)` strictly before signature release. -/
@[expose] def walCommitAuthorized (st : WalLatchState) (ep : Nat) (msgDigest : List UInt8)
    (sigBytes : ByteArray) : WalLatchState :=
  { st with
    nextEpoch     := ep + 1
    latchedRecord := some (ep, msgDigest, sigBytes) }

/-- Atomic pre-release WAL commit: advances `nextEpoch := reqEpoch + 1` and persists
    `(reqEpoch, msgDigest, freshSig)` strictly before returning the released `ByteArray`. -/
def walCommitBeforeRelease (st : WalLatchState) (pkDigest : List UInt8)
    (reqEpoch : Nat) (msgDigest : List UInt8) (freshSig : ByteArray) :
    UcStepOutcome WalLatchState ByteArray WalRejectReason :=
  match walPreSignStep st pkDigest reqEpoch msgDigest with
  | .err st' r => .err st' r
  | .ok st' (.replayCached cached) => .ok st' cached
  | .ok st' (.authorizedFresh ep) =>
    .ok (walCommitAuthorized st' ep msgDigest freshSig) freshSig

theorem walCommitAuthorized_eq_walCommitBeforeRelease
    {st wal' : WalLatchState} {pkDigest : List UInt8}
    {reqEpoch ep : Nat} {msgDigest : List UInt8} (sigBytes : ByteArray)
    (hAuth : walPreSignStep st pkDigest reqEpoch msgDigest = .ok wal' (.authorizedFresh ep)) :
    walCommitBeforeRelease st pkDigest reqEpoch msgDigest sigBytes =
      .ok (walCommitAuthorized wal' ep msgDigest sigBytes) sigBytes := by
  unfold walCommitBeforeRelease
  rw [hAuth]

theorem walCommitBeforeRelease_eq (st : WalLatchState) (pkDigest : List UInt8)
    (reqEpoch : Nat) (msgDigest : List UInt8) (freshSig : ByteArray) :
    walCommitBeforeRelease st pkDigest reqEpoch msgDigest freshSig =
      match walPreSignStep st pkDigest reqEpoch msgDigest with
      | .err st' r => .err st' r
      | .ok st' (.replayCached cached) => .ok st' cached
      | .ok st' (.authorizedFresh ep) =>
        .ok { st' with nextEpoch := ep + 1, latchedRecord := some (ep, msgDigest, freshSig) } freshSig := by rfl

/-- **Sticky Quarantine Theorem (`walLatch_poison_sticky`)**:
    Once `st.poisoned = true`, both `walPreSignStep` and `walCommitBeforeRelease` unconditionally
    refuse with `.poisonedQuarantine` and preserve `poisoned = true`. -/
theorem walLatch_poison_sticky (st : WalLatchState) (hPoison : st.poisoned = true)
    (pkDigest : List UInt8) (reqEpoch : Nat) (msgDigest : List UInt8) (freshSig : ByteArray) :
    walPreSignStep st pkDigest reqEpoch msgDigest = .err st .poisonedQuarantine ∧
    walCommitBeforeRelease st pkDigest reqEpoch msgDigest freshSig = .err st .poisonedQuarantine ∧
    (walQuarantine st).poisoned = true := by
  simp [walPreSignStep, walCommitBeforeRelease, walQuarantine, hPoison]

/-- **Monotonic Epoch & Anti-Equivocation Theorem (`walCommitBeforeRelease_preserves_wellFormed`)**:
    `walCommitBeforeRelease` preserves `WellFormed`, never decreases `nextEpoch`, replays identical
    `(ep, msgDigest)` idempotently, and strictly rejects any equivocating `msgDigest' ≠ msgDigest`
    at an already committed epoch `ep`. -/
theorem walCommitBeforeRelease_preserves_wellFormed
    {st st' : WalLatchState} {pkDigest : List UInt8}
    {reqEpoch : Nat} {msgDigest : List UInt8} {freshSig outSig : ByteArray}
    (hWf : st.WellFormed)
    (hOk : walCommitBeforeRelease st pkDigest reqEpoch msgDigest freshSig = .ok st' outSig) :
    st'.WellFormed ∧
    st.nextEpoch ≤ st'.nextEpoch ∧
    st'.poisoned = false ∧
    (∀ msgDigest' freshSig', msgDigest' ≠ msgDigest →
      walPreSignStep st' pkDigest reqEpoch msgDigest' = .err st' .staleOrOutOfOrderEpoch ∧
      walCommitBeforeRelease st' pkDigest reqEpoch msgDigest' freshSig' =
        .err st' .staleOrOutOfOrderEpoch) := by
  unfold walCommitBeforeRelease walCommitAuthorized walPreSignStep at hOk
  cases hp : st.poisoned
  · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hOk
    cases hPk : decide (pkDigest = st.enrolledPkDigest)
    · simp [hPk] at hOk
    · simp only [hPk, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
      have hPkEq : pkDigest = st.enrolledPkDigest := of_decide_eq_true hPk
      cases hLat : st.latchedRecord with
      | none =>
        rw [hLat] at hOk
        cases hEp : (reqEpoch == st.nextEpoch)
        · simp [hEp] at hOk
        · simp only [hEp, ↓reduceIte, UcStepOutcome.ok.injEq] at hOk
          rcases hOk with ⟨rfl, rfl⟩
          have hEpEq : reqEpoch = st.nextEpoch := Nat.eq_of_beq_eq_true hEp
          refine ⟨⟨hWf.1, ?_⟩, by dsimp only; omega, hp, ?_⟩
          · intro ep' md' sig' hSome
            injection hSome with hTup
            rcases Prod.mk.inj hTup with ⟨rfl, _⟩
            dsimp only; omega
          · intro md' fs' hNe
            have hMdF : decide (md' = msgDigest) = false := decide_eq_false hNe
            have hEpNextF : (reqEpoch == reqEpoch + 1) = false := beq_false_of_ne (by omega)
            simp [walCommitBeforeRelease, walPreSignStep, hp, hPkEq, hMdF, hEpNextF]
      | some rec0 =>
        rcases rec0 with ⟨ep0, prevMd, prevSig⟩
        rw [hLat] at hOk
        cases hHit : (reqEpoch == ep0 && decide (msgDigest = prevMd))
        · simp only [hHit, Bool.false_eq_true, ↓reduceIte] at hOk
          cases hEp : (reqEpoch == st.nextEpoch)
          · simp [hEp] at hOk
          · simp only [hEp, ↓reduceIte, UcStepOutcome.ok.injEq] at hOk
            rcases hOk with ⟨rfl, rfl⟩
            have hEpEq : reqEpoch = st.nextEpoch := Nat.eq_of_beq_eq_true hEp
            refine ⟨⟨hWf.1, ?_⟩, by dsimp only; omega, hp, ?_⟩
            · intro ep' md' sig' hSome
              injection hSome with hTup
              rcases Prod.mk.inj hTup with ⟨rfl, _⟩
              dsimp only; omega
            · intro md' fs' hNe
              have hMdF : decide (md' = msgDigest) = false := decide_eq_false hNe
              have hEpNextF : (reqEpoch == reqEpoch + 1) = false := beq_false_of_ne (by omega)
              simp [walCommitBeforeRelease, walPreSignStep, hp, hPkEq, hMdF, hEpNextF]
        · simp only [hHit, ↓reduceIte, UcStepOutcome.ok.injEq] at hOk
          rcases hOk with ⟨rfl, rfl⟩
          rcases Bool.and_eq_true_iff.mp hHit with ⟨hEp0B, hMd0B⟩
          have hEp0 : reqEpoch = ep0 := Nat.eq_of_beq_eq_true hEp0B
          have hMd0 : msgDigest = prevMd := of_decide_eq_true hMd0B
          subst hEp0 hMd0
          have hLtNext : reqEpoch < st.nextEpoch := hWf.2 reqEpoch msgDigest prevSig hLat
          refine ⟨hWf, Nat.le_refl _, hp, ?_⟩
          intro md' fs' hNe
          have hMdF : decide (md' = msgDigest) = false := decide_eq_false hNe
          have hEpNextF : (reqEpoch == st.nextEpoch) = false := beq_false_of_ne (by omega)
          simp [walCommitBeforeRelease, walPreSignStep, hp, hPkEq, hLat, hMdF, hEpNextF]
  · simp [hp] at hOk

/-- Honest party custody vault pairing persistent `WalLatchState`, strictly monotonic session
    mask-tape cursor `maskSessionCursor`, and an erasable in-memory secret share slot `shareSlot`. -/
structure HonestCustodyVault (ShareT : Type) where
  partyId           : Nat
  wal               : WalLatchState
  maskSessionCursor : Nat
  shareSlot         : Option ShareT

/-- Enroll an honest party's custody vault with initial secret share `sh` and clean WAL state. -/
def enrollHonestVault {ShareT : Type} (partyId : Nat)
    (enrolledPkDigest : List UInt8) (sh : ShareT) : HonestCustodyVault ShareT :=
  { partyId           := partyId
    wal               := initWalLatchState enrolledPkDigest
    maskSessionCursor := 0
    shareSlot         := some sh }

theorem enrollHonestVault_eq {ShareT : Type} (partyId : Nat)
    (enrolledPkDigest : List UInt8) (sh : ShareT) :
    enrollHonestVault partyId enrolledPkDigest sh =
      { partyId := partyId
        wal := initWalLatchState enrolledPkDigest
        maskSessionCursor := 0
        shareSlot := some sh } := by rfl

/-- Quarantine an honest custody vault on active fault: sets `wal.poisoned := true` AND erases
    `shareSlot := none` so zero secret key material remains in memory for future sessions. -/
@[expose] def walPoisonVault {ShareT : Type} (v : HonestCustodyVault ShareT) : HonestCustodyVault ShareT :=
  { v with
    wal       := walQuarantine v.wal
    shareSlot := none }

/-- Consume one monotonic mask-tape cursor slot from an unpoisoned vault to run a round-1 share
    computation, advancing `maskSessionCursor := maskSessionCursor + 1` so the slot cannot repeat. -/
def consumeVaultMaskSlot {ShareT Out : Type}
    (v : HonestCustodyVault ShareT) (f : Nat → ShareT → Out) :
    Option (Out × HonestCustodyVault ShareT) :=
  if v.wal.poisoned then none
  else
    match v.shareSlot with
    | none => none
    | some sh =>
      let out := f v.maskSessionCursor sh
      some (out, { v with maskSessionCursor := v.maskSessionCursor + 1 })

theorem consumeVaultMaskSlot_strictly_advances {ShareT Out : Type}
    {v v' : HonestCustodyVault ShareT} {f : Nat → ShareT → Out} {out : Out}
    (h : consumeVaultMaskSlot v f = some (out, v')) :
    v.wal.poisoned = false ∧
    v'.maskSessionCursor = v.maskSessionCursor + 1 ∧
    v'.shareSlot = v.shareSlot ∧
    v'.wal = v.wal := by
  unfold consumeVaultMaskSlot at h
  cases hp : v.wal.poisoned
  · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
    cases hs : v.shareSlot with
    | none => simp [hs] at h
    | some sh =>
      simp only [hs, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl⟩
      exact ⟨rfl, rfl, rfl, rfl⟩
  · simp [hp] at h

/-- **`#tooth` Poisoned Custody Vault Blocks All Future Signing (`tooth_poisoned_vault_erases_share_and_blocks`)**:
    Once `walPoisonVault` executes on an active fault, `shareSlot` is physically wiped (`none`),
    `consumeVaultMaskSlot` refuses every subsequent call, and `walCommitBeforeRelease` refuses
    every subsequent epoch! -/
theorem tooth_poisoned_vault_erases_share_and_blocks {ShareT Out : Type}
    (v : HonestCustodyVault ShareT) (f : Nat → ShareT → Out)
    (pkDigest : List UInt8) (reqEpoch : Nat) (msgDigest : List UInt8) (sig : ByteArray) :
    let vQuarantined := walPoisonVault v
    vQuarantined.shareSlot = none ∧
    vQuarantined.wal.poisoned = true ∧
    consumeVaultMaskSlot vQuarantined f = none ∧
    walCommitBeforeRelease vQuarantined.wal pkDigest reqEpoch msgDigest sig =
      .err vQuarantined.wal .poisonedQuarantine := by
  simp [walPoisonVault, walQuarantine, consumeVaultMaskSlot, walCommitBeforeRelease, walPreSignStep]

/-! ## 3. Multi-Round, Multi-Session Rushing-Adversary Network Execution -/

/-- Exact observable abort classification emitted by real and ideal threshold signing sessions. -/
inductive AbortReason where
  | quorumRejected
  | walPoisoned
  | walPkMismatch
  | walEpochRejected
  | round1CommitMismatch (culprit : Nat)
  | activeConsistencyFailed
  | cutOpenMismatch (culprit : Nat)
  deriving DecidableEq, Repr

/-- Exact observable outcome of a signing session delivered to the rushing adversary. -/
inductive SessionOutcome where
  | signOk (sigBytes : ByteArray)
  | abort (reason : AbortReason)
  deriving DecidableEq

/-- Adaptive session scheduling directive chosen by `UcRushingAdversary`. -/
structure SessionScheduleReq where
  sessionId       : Nat
  reqEpoch        : Nat
  msg             : List UInt8
  optRand         : List UInt8
  honestApprovers : List Nat
  deriving DecidableEq, Repr

/-- Wire-level multi-round transcript recorded for a single scheduled session. -/
structure SessionWireRecord where
  request        : SessionScheduleReq
  honestRound1   : List (Nat × ByteArray)
  corruptRound1  : List (Nat × ByteArray)
  honestRound2   : List (Nat × ByteArray)
  corruptRound2  : List (Nat × ByteArray)
  honestRound3   : List (Nat × ByteArray)
  corruptRound3  : List (Nat × ByteArray)
  outcome        : SessionOutcome
  deriving DecidableEq

/-- Complete multi-session view seen by a distinguisher at the end of a `Q_s`-session execution. -/
structure ExecTranscript (AdvState : Type) where
  finalAdvState : AdvState
  sessions      : List SessionWireRecord
  deriving DecidableEq

/-- Arbitrary stateful rushing adversary `A` scheduling `Q_s` threshold signing sessions and
    inspecting **all honest round-`k` wire `ByteArray` messages** prior to choosing corrupt
    round-`k` wire `ByteArray` messages in each round `k ∈ {1, 2, 3}`. -/
structure UcRushingAdversary (AdvState : Type) where
  scheduleSession : AdvState → SessionScheduleReq × AdvState
  rushRound1      : AdvState → List (Nat × ByteArray) → (Nat → ByteArray) × AdvState
  rushRound2      : AdvState → List (Nat × ByteArray) → (Nat → ByteArray) × AdvState
  rushRound3      : AdvState → List (Nat × ByteArray) → (Nat → ByteArray) × AdvState
  observeOutcome  : AdvState → SessionOutcome → AdvState

/-- Map `walPreSignStep` rejection reasons to network-observable `AbortReason`s. -/
@[expose] def mapWalRejectReason : WalRejectReason → AbortReason
  | .poisonedQuarantine  => .walPoisoned
  | .pkDigestMismatch    => .walPkMismatch
  | .staleOrOutOfOrderEpoch => .walEpochRejected

/-- Specification of a 3-round interactive threshold signing protocol with persistent honest custody,
    mandatory pre-cut consistency barrier prior to Round 3, and atomic WAL advance prior to release. -/
structure InteractiveThresholdProtocol (PK ShareT SessionTape R1St R2St R3St : Type) where
  pkDigestOf        : PK → List UInt8
  msgDigestOf       : SessionScheduleReq → List UInt8
  /-- Honest Round 1 (hedged mask / nonce commitment) consuming 1 monotonic mask slot. -/
  honestRound1      : PK → List Nat → SessionScheduleReq → Nat → (Nat → Option ShareT) → SessionTape →
                        List (Nat × ByteArray) × R1St
  /-- Verify Round 1 wire messages (`PSum.inl (reason, poisonFlag)` aborts before Round 2). -/
  verifyRound1      : PK → SessionScheduleReq → R1St → List (Nat × ByteArray) → List (Nat × ByteArray) →
                        PSum (AbortReason × Bool) R2St
  /-- Honest Round 2 (masked S-box / Beaver shares + `GF(2^128)` active consistency shares). -/
  honestRound2      : PK → List Nat → SessionScheduleReq → R2St → (Nat → Option ShareT) → SessionTape →
                        List (Nat × ByteArray) × R2St
  /-- **Mandatory Pre-Cut Consistency Barrier**: must pass strictly BEFORE `honestRound3` runs!
      Any failure poisons honest `WalLatchState` and wipes `shareSlot` immediately. -/
  preCutBarrier     : PK → SessionScheduleReq → R2St → List (Nat × ByteArray) → List (Nat × ByteArray) →
                        PSum AbortReason R3St
  /-- Honest Round 3 (cut-boundary opening shares — never invoked if `preCutBarrier` aborts!). -/
  honestRound3      : PK → List Nat → SessionScheduleReq → R3St → (Nat → Option ShareT) → SessionTape →
                        List (Nat × ByteArray) × R3St
  /-- Cross-check Round 3 cut shares and assemble verified signature `ByteArray`. -/
  finalizeCutOpen   : PK → SessionScheduleReq → R3St → List (Nat × ByteArray) → List (Nat × ByteArray) →
                        PSum AbortReason ByteArray

/-- Persistent multi-party real-world execution state: `IdealTsigState` public parameters/quorum log,
    shared honest `WalLatchState` + `maskSessionCursor`, and honest party `shareSlot` map. -/
structure RealClusterState (PK ShareT : Type) where
  tsig              : IdealTsigState PK (List UInt8)
  honestWal         : WalLatchState
  maskSessionCursor : Nat
  honestShares      : Nat → Option ShareT

/-- Quarantine an entire `RealClusterState`: poisons `honestWal` AND wipes all `honestShares`. -/
def poisonRealCluster {PK ShareT : Type} (cl : RealClusterState PK ShareT) : RealClusterState PK ShareT :=
  { cl with
    honestWal    := walQuarantine cl.honestWal
    honestShares := fun _ => none }

/-- Execute one interactive 3-round session against rushing adversary `A` in the real protocol. -/
def execRealSession {PK ShareT SessionTape R1St R2St R3St AdvState : Type}
    (proto : InteractiveThresholdProtocol PK ShareT SessionTape R1St R2St R3St)
    (A : UcRushingAdversary AdvState)
    (cl : RealClusterState PK ShareT) (advSt : AdvState) (tape : SessionTape) :
    RealClusterState PK ShareT × AdvState × SessionWireRecord :=
  let (req, advSt1) := A.scheduleSession advSt
  if !(validThresholdApproval cl.tsig req.honestApprovers) then
    let out := SessionOutcome.abort .quorumRejected
    let advStF := A.observeOutcome advSt1 out
    (cl, advStF, ⟨req, [], [], [], [], [], [], out⟩)
  else
    let pkDig := proto.pkDigestOf cl.tsig.pk
    let msgDig := proto.msgDigestOf req
    match walPreSignStep cl.honestWal pkDig req.reqEpoch msgDig with
    | .err wal' rej =>
      let out := SessionOutcome.abort (mapWalRejectReason rej)
      let advStF := A.observeOutcome advSt1 out
      ({ cl with honestWal := wal' }, advStF, ⟨req, [], [], [], [], [], [], out⟩)
    | .ok wal' (.replayCached cachedSig) =>
      let out := SessionOutcome.signOk cachedSig
      let advStF := A.observeOutcome advSt1 out
      ({ cl with honestWal := wal' }, advStF, ⟨req, [], [], [], [], [], [], out⟩)
    | .ok wal' (.authorizedFresh _) =>
      -- Consume monotonic mask cursor BEFORE Round 1 so this session's mask slot never repeats.
      let cursorUsed := cl.maskSessionCursor
      let clAfterCursor : RealClusterState PK ShareT :=
        { cl with honestWal := wal', maskSessionCursor := cursorUsed + 1 }
      let (honR1, r1St) :=
        proto.honestRound1 cl.tsig.pk cl.tsig.corruptParties req cursorUsed cl.honestShares tape
      let (corrR1Fn, advSt2) := A.rushRound1 advSt1 honR1
      let corrR1 := cl.tsig.corruptParties.map (fun c => (c, corrR1Fn c))
      match proto.verifyRound1 cl.tsig.pk req r1St honR1 corrR1 with
      | .inl (r1Err, doPoison) =>
        let clErr := if doPoison then poisonRealCluster clAfterCursor else clAfterCursor
        let out := SessionOutcome.abort r1Err
        let advStF := A.observeOutcome advSt2 out
        (clErr, advStF, ⟨req, honR1, corrR1, [], [], [], [], out⟩)
      | .inr r2Init =>
        let (honR2, r2St) :=
          proto.honestRound2 cl.tsig.pk cl.tsig.corruptParties req r2Init cl.honestShares tape
        let (corrR2Fn, advSt3) := A.rushRound2 advSt2 honR2
        let corrR2 := cl.tsig.corruptParties.map (fun c => (c, corrR2Fn c))
        -- MANDATORY PRE-CUT BARRIER: aborts and poisons BEFORE `honestRound3` can ever run!
        match proto.preCutBarrier cl.tsig.pk req r2St honR2 corrR2 with
        | .inl barrierErr =>
          let clPoisoned := poisonRealCluster clAfterCursor
          let out := SessionOutcome.abort barrierErr
          let advStF := A.observeOutcome advSt3 out
          (clPoisoned, advStF, ⟨req, honR1, corrR1, honR2, corrR2, [], [], out⟩)
        | .inr r3Init =>
          let (honR3, r3St) :=
            proto.honestRound3 cl.tsig.pk cl.tsig.corruptParties req r3Init cl.honestShares tape
          let (corrR3Fn, advSt4) := A.rushRound3 advSt3 honR3
          let corrR3 := cl.tsig.corruptParties.map (fun c => (c, corrR3Fn c))
          match proto.finalizeCutOpen cl.tsig.pk req r3St honR3 corrR3 with
          | .inl cutErr =>
            let clPoisoned := poisonRealCluster clAfterCursor
            let out := SessionOutcome.abort cutErr
            let advStF := A.observeOutcome advSt4 out
            (clPoisoned, advStF, ⟨req, honR1, corrR1, honR2, corrR2, honR3, corrR3, out⟩)
          | .inr sigBytes =>
            -- ATOMIC WAL COMMIT BEFORE SIGNATURE RELEASE + `IdealTsig.approvedMsgs` log update!
            let committedWal := walCommitAuthorized wal' req.reqEpoch msgDig sigBytes
            let tsigNext := { cl.tsig with approvedMsgs := req.msg :: cl.tsig.approvedMsgs }
            let clOk : RealClusterState PK ShareT :=
              { clAfterCursor with tsig := tsigNext, honestWal := committedWal }
            let out := SessionOutcome.signOk sigBytes
            let advStF := A.observeOutcome advSt4 out
            (clOk, advStF, ⟨req, honR1, corrR1, honR2, corrR2, honR3, corrR3, out⟩)

/-- Run `Q_s` adaptively scheduled interactive rushing sessions of `RealProtocolExec`. -/
def RealProtocolExec {PK ShareT SessionTape R1St R2St R3St AdvState : Type}
    (proto : InteractiveThresholdProtocol PK ShareT SessionTape R1St R2St R3St)
    (A : UcRushingAdversary AdvState) :
    (numSessions : Nat) → (Nat → SessionTape) →
    RealClusterState PK ShareT → AdvState →
    RealClusterState PK ShareT × ExecTranscript AdvState
  | 0, _, cl, advSt => (cl, ⟨advSt, []⟩)
  | s + 1, tapes, cl, advSt =>
    let (cl1, advSt1, rec1) := execRealSession proto A cl advSt (tapes 0)
    let (clF, trRest) := RealProtocolExec proto A s (fun i => tapes (i + 1)) cl1 advSt1
    (clF, ⟨trRest.finalAdvState, rec1 :: trRest.sessions⟩)

theorem RealProtocolExec_zero {PK ShareT SessionTape R1St R2St R3St AdvState : Type}
    (proto : InteractiveThresholdProtocol PK ShareT SessionTape R1St R2St R3St)
    (A : UcRushingAdversary AdvState) (tapes : Nat → SessionTape)
    (cl : RealClusterState PK ShareT) (advSt : AdvState) :
    RealProtocolExec proto A 0 tapes cl advSt = (cl, ⟨advSt, []⟩) := by rfl

theorem RealProtocolExec_succ {PK ShareT SessionTape R1St R2St R3St AdvState : Type}
    (proto : InteractiveThresholdProtocol PK ShareT SessionTape R1St R2St R3St)
    (A : UcRushingAdversary AdvState) (s : Nat) (tapes : Nat → SessionTape)
    (cl : RealClusterState PK ShareT) (advSt : AdvState) :
    RealProtocolExec proto A (s + 1) tapes cl advSt =
      let (cl1, advSt1, rec1) := execRealSession proto A cl advSt (tapes 0)
      let (clF, trRest) := RealProtocolExec proto A s (fun i => tapes (i + 1)) cl1 advSt1
      (clF, ⟨trRest.finalAdvState, rec1 :: trRest.sessions⟩) := by rfl

/-- **Explicit Black-Box UC Simulator (`BlackBoxUcSimulator`)**:
    Notice that `ShareT` and `SK` DO NOT APPEAR anywhere in `BlackBoxUcSimulator`'s type!
    In each quorum-approved, WAL-authorized session, `IdealFunctionalityExec` queries the ideal
    functionality's `idealSignOracle` for `idealSigBytes : ByteArray` and hands ONLY
    `(pk, corruptParties, req, cursor, idealSigBytes, simTape)` to `Sim`! -/
structure BlackBoxUcSimulator (PK SimTape SimR1 SimR2 SimR3 : Type) where
  pkDigestOf      : PK → List UInt8
  msgDigestOf     : SessionScheduleReq → List UInt8
  simRound1       : PK → List Nat → SessionScheduleReq → Nat → SimTape →
                      List (Nat × ByteArray) × SimR1
  simVerifyRound1 : PK → SessionScheduleReq → SimR1 → List (Nat × ByteArray) → List (Nat × ByteArray) →
                      PSum (AbortReason × Bool) SimR2
  simRound2       : PK → List Nat → SessionScheduleReq → SimR2 → SimTape →
                      List (Nat × ByteArray) × SimR2
  simPreCutBarrier : PK → SessionScheduleReq → SimR2 → List (Nat × ByteArray) → List (Nat × ByteArray) →
                      PSum AbortReason SimR3
  /-- Programs Round-3 honest cut-opening shares solely from public `(pk, req, idealSigBytes)`! -/
  simRound3       : PK → List Nat → SessionScheduleReq → SimR3 → ByteArray → SimTape →
                      List (Nat × ByteArray) × SimR3
  simFinalizeCut  : PK → SessionScheduleReq → SimR3 → ByteArray →
                      List (Nat × ByteArray) → List (Nat × ByteArray) →
                      PSum AbortReason ByteArray

/-- Strictly `sk`-free ideal-world state (`IdealTsigState` + public `WalLatchState` + session cursor). -/

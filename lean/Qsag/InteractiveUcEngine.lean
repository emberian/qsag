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
     inequality (`rationalAcceptDiff` / `ratAdd`) under a post-processing function of the
     transcript. It is not an interactive composition theorem: sessions run sequentially to
     completion and the outer context cannot interleave with them.
   - `forgery_count_transfer`: `Pr[win in real] ≤ Pr[win in ideal] + eps` for any Boolean event.
4. **Signing-Oracle Locality (`IdealFunctionalityExec_oracle_congr`)**: for every simulator with a
   non-empty Round-3 message list, the ideal result is determined by the oracle's values on the
   requests of the sessions that reached Round 3.
5. **Hypertree Weld (`uc_emulation_forgery_to_hypertree_hash_game`)**: for the ideal functionality
   instantiated with the checked stateless hypertree signer, any protocol within `eps` of it for the
   forgery event transfers real forgeries to ideal ones, and every ideal forgery yields a
   `HypertreeForgeryBreak` through `checked_stateless_hypertree_euf_cma_extract`. The `eps` bound is
   a premise: no concrete threshold protocol for that signer is proved in this module.
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
          -- Approval is recorded before any opening becomes visible to the adversary.
          -- A later cut-finalization failure must not make this signing query fresh again.
          let clApproved := { clAfterCursor with
            tsig := { cl.tsig with approvedMsgs := req.msg :: cl.tsig.approvedMsgs } }
          let (honR3, r3St) :=
            proto.honestRound3 cl.tsig.pk cl.tsig.corruptParties req r3Init cl.honestShares tape
          let (corrR3Fn, advSt4) := A.rushRound3 advSt3 honR3
          let corrR3 := cl.tsig.corruptParties.map (fun c => (c, corrR3Fn c))
          match proto.finalizeCutOpen cl.tsig.pk req r3St honR3 corrR3 with
          | .inl cutErr =>
            let clPoisoned := poisonRealCluster clApproved
            let out := SessionOutcome.abort cutErr
            let advStF := A.observeOutcome advSt4 out
            (clPoisoned, advStF, ⟨req, honR1, corrR1, honR2, corrR2, honR3, corrR3, out⟩)
          | .inr sigBytes =>
            -- Commit the successful result before releasing SignOk; approval is already recorded.
            let committedWal := walCommitAuthorized wal' req.reqEpoch msgDig sigBytes
            let clOk : RealClusterState PK ShareT :=
              { clApproved with honestWal := committedWal }
            let out := SessionOutcome.signOk sigBytes
            let advStF := A.observeOutcome advSt4 out
            (clOk, advStF, ⟨req, honR1, corrR1, honR2, corrR2, honR3, corrR3, out⟩)

/-- Any session exposing honest Round-3 bytes records the approved message, even if
    the corrupt party makes finalization abort after receiving those bytes. -/
theorem execRealSession_opening_records_approval
    {PK ShareT SessionTape R1St R2St R3St AdvState : Type}
    (proto : InteractiveThresholdProtocol PK ShareT SessionTape R1St R2St R3St)
    (A : UcRushingAdversary AdvState) (cl : RealClusterState PK ShareT)
    (advSt : AdvState) (tape : SessionTape)
    (hOpen : (execRealSession proto A cl advSt tape).2.2.honestRound3 ≠ []) :
    (execRealSession proto A cl advSt tape).2.2.request.msg ∈
      (execRealSession proto A cl advSt tape).1.tsig.approvedMsgs := by
  revert hOpen
  unfold execRealSession
  dsimp only
  cases validThresholdApproval cl.tsig (A.scheduleSession advSt).1.honestApprovers
  · intro hOpen; exact False.elim (hOpen rfl)
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases walPreSignStep cl.honestWal _ _ _ with
    | err _ _ => intro hOpen; exact False.elim (hOpen rfl)
    | ok _ auth =>
      cases auth with
      | replayCached _ => intro hOpen; exact False.elim (hOpen rfl)
      | authorizedFresh _ =>
        dsimp only
        cases proto.verifyRound1 _ _ _ _ _ with
        | inl _ => intro hOpen; exact False.elim (hOpen rfl)
        | inr _ =>
          dsimp only
          cases proto.preCutBarrier _ _ _ _ _ with
          | inl _ => intro hOpen; exact False.elim (hOpen rfl)
          | inr _ =>
            dsimp only
            cases proto.finalizeCutOpen _ _ _ _ _ <;> intro _ <;> exact List.mem_cons_self

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
structure IdealClusterState (PK : Type) where
  tsig              : IdealTsigState PK (List UInt8)
  honestWal         : WalLatchState
  maskSessionCursor : Nat

/-- Quarantine the ideal-world WAL state upon simulated active consistency / MAC fault. -/
def poisonIdealCluster {PK : Type} (icl : IdealClusterState PK) : IdealClusterState PK :=
  { icl with honestWal := walQuarantine icl.honestWal }

/-- Execute one session of `IdealFunctionalityExec` coupling `IdealTsig` with black-box `Sim`.
    `idealSignOracle` is invoked **ONLY** when `validThresholdApproval = true` AND `walPreSignStep`
    grants `.authorizedFresh`! -/
def execIdealSession {PK SimTape SimR1 SimR2 SimR3 AdvState : Type}
    (idealSignOracle : SessionScheduleReq → ByteArray)
    (sim : BlackBoxUcSimulator PK SimTape SimR1 SimR2 SimR3)
    (A : UcRushingAdversary AdvState)
    (icl : IdealClusterState PK) (advSt : AdvState) (tape : SimTape) :
    IdealClusterState PK × AdvState × SessionWireRecord :=
  let (req, advSt1) := A.scheduleSession advSt
  if !(validThresholdApproval icl.tsig req.honestApprovers) then
    let out := SessionOutcome.abort .quorumRejected
    let advStF := A.observeOutcome advSt1 out
    (icl, advStF, ⟨req, [], [], [], [], [], [], out⟩)
  else
    let pkDig := sim.pkDigestOf icl.tsig.pk
    let msgDig := sim.msgDigestOf req
    match walPreSignStep icl.honestWal pkDig req.reqEpoch msgDig with
    | .err wal' rej =>
      let out := SessionOutcome.abort (mapWalRejectReason rej)
      let advStF := A.observeOutcome advSt1 out
      ({ icl with honestWal := wal' }, advStF, ⟨req, [], [], [], [], [], [], out⟩)
    | .ok wal' (.replayCached cachedSig) =>
      let out := SessionOutcome.signOk cachedSig
      let advStF := A.observeOutcome advSt1 out
      ({ icl with honestWal := wal' }, advStF, ⟨req, [], [], [], [], [], [], out⟩)
    | .ok wal' (.authorizedFresh _) =>
      let cursorUsed := icl.maskSessionCursor
      let iclAfterCursor : IdealClusterState PK :=
        { icl with honestWal := wal', maskSessionCursor := cursorUsed + 1 }
      let (honR1, sR1) := sim.simRound1 icl.tsig.pk icl.tsig.corruptParties req cursorUsed tape
      let (corrR1Fn, advSt2) := A.rushRound1 advSt1 honR1
      let corrR1 := icl.tsig.corruptParties.map (fun c => (c, corrR1Fn c))
      match sim.simVerifyRound1 icl.tsig.pk req sR1 honR1 corrR1 with
      | .inl (r1Err, doPoison) =>
        let iclErr := if doPoison then poisonIdealCluster iclAfterCursor else iclAfterCursor
        let out := SessionOutcome.abort r1Err
        let advStF := A.observeOutcome advSt2 out
        (iclErr, advStF, ⟨req, honR1, corrR1, [], [], [], [], out⟩)
      | .inr sR2Init =>
        let (honR2, sR2) := sim.simRound2 icl.tsig.pk icl.tsig.corruptParties req sR2Init tape
        let (corrR2Fn, advSt3) := A.rushRound2 advSt2 honR2
        let corrR2 := icl.tsig.corruptParties.map (fun c => (c, corrR2Fn c))
        match sim.simPreCutBarrier icl.tsig.pk req sR2 honR2 corrR2 with
        | .inl barrierErr =>
          let iclPoisoned := poisonIdealCluster iclAfterCursor
          let out := SessionOutcome.abort barrierErr
          let advStF := A.observeOutcome advSt3 out
          (iclPoisoned, advStF, ⟨req, honR1, corrR1, honR2, corrR2, [], [], out⟩)
        | .inr sR3Init =>
          -- Pre-cut barrier succeeded under valid `t`-quorum approval: `IdealTsig` hands
          -- `idealSigBytes ← idealSignOracle req` to `sim.simRound3`. Record this query
          -- before releasing openings, including when the adversary subsequently aborts.
          let iclApproved := { iclAfterCursor with
            tsig := { icl.tsig with approvedMsgs := req.msg :: icl.tsig.approvedMsgs } }
          let idealSigBytes := idealSignOracle req
          let (honR3, sR3) :=
            sim.simRound3 icl.tsig.pk icl.tsig.corruptParties req sR3Init idealSigBytes tape
          let (corrR3Fn, advSt4) := A.rushRound3 advSt3 honR3
          let corrR3 := icl.tsig.corruptParties.map (fun c => (c, corrR3Fn c))
          match sim.simFinalizeCut icl.tsig.pk req sR3 idealSigBytes honR3 corrR3 with
          | .inl cutErr =>
            let iclPoisoned := poisonIdealCluster iclApproved
            let out := SessionOutcome.abort cutErr
            let advStF := A.observeOutcome advSt4 out
            (iclPoisoned, advStF, ⟨req, honR1, corrR1, honR2, corrR2, honR3, corrR3, out⟩)
          | .inr outSigBytes =>
            let committedWal := walCommitAuthorized wal' req.reqEpoch msgDig outSigBytes
            let iclOk : IdealClusterState PK :=
              { iclApproved with honestWal := committedWal }
            let out := SessionOutcome.signOk outSigBytes
            let advStF := A.observeOutcome advSt4 out
            (iclOk, advStF, ⟨req, honR1, corrR1, honR2, corrR2, honR3, corrR3, out⟩)

/-- Any session exposing honest Round-3 bytes records the approved message, even if
    the corrupt party makes finalization abort after receiving those bytes. -/
theorem execIdealSession_opening_records_approval
    {PK SimTape SimR1 SimR2 SimR3 AdvState : Type}
    (idealSignOracle : SessionScheduleReq → ByteArray)
    (sim : BlackBoxUcSimulator PK SimTape SimR1 SimR2 SimR3)
    (A : UcRushingAdversary AdvState) (cl : IdealClusterState PK)
    (advSt : AdvState) (tape : SimTape)
    (hOpen : (execIdealSession idealSignOracle sim A cl advSt tape).2.2.honestRound3 ≠ []) :
    (execIdealSession idealSignOracle sim A cl advSt tape).2.2.request.msg ∈
      (execIdealSession idealSignOracle sim A cl advSt tape).1.tsig.approvedMsgs := by
  revert hOpen
  unfold execIdealSession
  dsimp only
  cases validThresholdApproval cl.tsig (A.scheduleSession advSt).1.honestApprovers
  · intro hOpen; exact False.elim (hOpen rfl)
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases walPreSignStep cl.honestWal _ _ _ with
    | err _ _ => intro hOpen; exact False.elim (hOpen rfl)
    | ok _ auth =>
      cases auth with
      | replayCached _ => intro hOpen; exact False.elim (hOpen rfl)
      | authorizedFresh _ =>
        dsimp only
        cases sim.simVerifyRound1 _ _ _ _ _ with
        | inl _ => intro hOpen; exact False.elim (hOpen rfl)
        | inr _ =>
          dsimp only
          cases sim.simPreCutBarrier _ _ _ _ _ with
          | inl _ => intro hOpen; exact False.elim (hOpen rfl)
          | inr _ =>
            dsimp only
            cases sim.simFinalizeCut _ _ _ _ _ _ <;> intro _ <;> exact List.mem_cons_self

/-- Run `Q_s` adaptively scheduled interactive rushing sessions of `IdealFunctionalityExec`. -/
def IdealFunctionalityExec {PK SimTape SimR1 SimR2 SimR3 AdvState : Type}
    (idealSignOracle : SessionScheduleReq → ByteArray)
    (sim : BlackBoxUcSimulator PK SimTape SimR1 SimR2 SimR3)
    (A : UcRushingAdversary AdvState) :
    (numSessions : Nat) → (Nat → SimTape) →
    IdealClusterState PK → AdvState →
    IdealClusterState PK × ExecTranscript AdvState
  | 0, _, icl, advSt => (icl, ⟨advSt, []⟩)
  | s + 1, tapes, icl, advSt =>
    let (icl1, advSt1, rec1) := execIdealSession idealSignOracle sim A icl advSt (tapes 0)
    let (iclF, trRest) := IdealFunctionalityExec idealSignOracle sim A s (fun i => tapes (i + 1)) icl1 advSt1
    (iclF, ⟨trRest.finalAdvState, rec1 :: trRest.sessions⟩)

theorem IdealFunctionalityExec_zero {PK SimTape SimR1 SimR2 SimR3 AdvState : Type}
    (idealSignOracle : SessionScheduleReq → ByteArray)
    (sim : BlackBoxUcSimulator PK SimTape SimR1 SimR2 SimR3)
    (A : UcRushingAdversary AdvState) (tapes : Nat → SimTape)
    (icl : IdealClusterState PK) (advSt : AdvState) :
    IdealFunctionalityExec idealSignOracle sim A 0 tapes icl advSt = (icl, ⟨advSt, []⟩) := by rfl

theorem IdealFunctionalityExec_succ {PK SimTape SimR1 SimR2 SimR3 AdvState : Type}
    (idealSignOracle : SessionScheduleReq → ByteArray)
    (sim : BlackBoxUcSimulator PK SimTape SimR1 SimR2 SimR3)
    (A : UcRushingAdversary AdvState) (s : Nat) (tapes : Nat → SimTape)
    (icl : IdealClusterState PK) (advSt : AdvState) :
    IdealFunctionalityExec idealSignOracle sim A (s + 1) tapes icl advSt =
      let (icl1, advSt1, rec1) := execIdealSession idealSignOracle sim A icl advSt (tapes 0)
      let (iclF, trRest) := IdealFunctionalityExec idealSignOracle sim A s (fun i => tapes (i + 1)) icl1 advSt1
      (iclF, ⟨trRest.finalAdvState, rec1 :: trRest.sessions⟩) := by rfl

/-- **Quorum Provenance Invariant on `RealProtocolExec` (`realProtocolExec_approvedMsgs_provenance`)**:
    Across any `Q_s`-session rushing execution against `< threshold` corrupt parties, every newly
    recorded message in `tsig.approvedMsgs` came from an actual scheduled session where at least
    one non-corrupt honest party approved (`validThresholdApproval = true`). -/
theorem realProtocolExec_approvedMsgs_provenance
    {PK ShareT SessionTape R1St R2St R3St AdvState : Type}
    (proto : InteractiveThresholdProtocol PK ShareT SessionTape R1St R2St R3St)
    (A : UcRushingAdversary AdvState) :
    ∀ (numSessions : Nat) (tapes : Nat → SessionTape)
      (cl : RealClusterState PK ShareT) (advSt : AdvState),
      cl.tsig.corruptParties.length + 1 ≤ cl.tsig.threshold →
      let (clF, tr) := RealProtocolExec proto A numSessions tapes cl advSt
      clF.tsig.pk = cl.tsig.pk ∧
      clF.tsig.corruptParties = cl.tsig.corruptParties ∧
      clF.tsig.threshold = cl.tsig.threshold ∧
      clF.tsig.numParties = cl.tsig.numParties ∧
      (∀ m ∈ clF.tsig.approvedMsgs,
        m ∈ cl.tsig.approvedMsgs ∨
        ∃ rec ∈ tr.sessions,
          rec.request.msg = m ∧
          validThresholdApproval cl.tsig rec.request.honestApprovers = true ∧
          ∃ h ∈ rec.request.honestApprovers, h < cl.tsig.numParties ∧ h ∉ cl.tsig.corruptParties)
  | 0, _, cl, _, _ => ⟨rfl, rfl, rfl, rfl, fun _ hm => .inl hm⟩
  | s + 1, tapes, cl, advSt, hDishonest => by
    have hCheat1 : (execRealSession proto A cl advSt (tapes 0)).1.tsig.identifiedCheaters =
        cl.tsig.identifiedCheaters := by
      unfold execRealSession poisonRealCluster
      dsimp only
      cases validThresholdApproval cl.tsig (A.scheduleSession advSt).1.honestApprovers
      · rfl
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases walPreSignStep cl.honestWal _ _ _ with
        | err _ _ => rfl
        | ok _ resOut =>
          cases resOut with
          | replayCached _ => rfl
          | authorizedFresh _ =>
            dsimp only
            cases proto.verifyRound1 _ _ _ _ _ with
            | inl p1 => rcases p1 with ⟨_, b⟩; cases b <;> rfl
            | inr _ =>
              dsimp only
              cases proto.preCutBarrier _ _ _ _ _ with
              | inl _ => rfl
              | inr _ =>
                dsimp only
                cases proto.finalizeCutOpen _ _ _ _ _ <;> rfl
    simp only [RealProtocolExec]
    have hStep :
        let (cl1, _, rec1) := execRealSession proto A cl advSt (tapes 0)
        cl1.tsig.pk = cl.tsig.pk ∧
        cl1.tsig.corruptParties = cl.tsig.corruptParties ∧
        cl1.tsig.threshold = cl.tsig.threshold ∧
        cl1.tsig.numParties = cl.tsig.numParties ∧
        (∀ m ∈ cl1.tsig.approvedMsgs,
          m ∈ cl.tsig.approvedMsgs ∨
          (rec1.request.msg = m ∧ validThresholdApproval cl.tsig rec1.request.honestApprovers = true)) := by
      unfold execRealSession poisonRealCluster
      dsimp only
      cases hQuorum : validThresholdApproval cl.tsig (A.scheduleSession advSt).1.honestApprovers
      · exact ⟨rfl, rfl, rfl, rfl, fun _ hm => .inl hm⟩
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases walPreSignStep cl.honestWal _ _ _ with
        | err _ _ => exact ⟨rfl, rfl, rfl, rfl, fun _ hm => .inl hm⟩
        | ok wal' resOut =>
          cases resOut with
          | replayCached _ => exact ⟨rfl, rfl, rfl, rfl, fun _ hm => .inl hm⟩
          | authorizedFresh _ =>
            dsimp only
            cases proto.verifyRound1 _ _ _ _ _ with
            | inl p1 =>
              rcases p1 with ⟨r1Err, doPoison⟩
              cases doPoison <;> exact ⟨rfl, rfl, rfl, rfl, fun _ hm => .inl hm⟩
            | inr r2Init =>
              dsimp only
              cases proto.preCutBarrier _ _ _ _ _ with
              | inl _ => exact ⟨rfl, rfl, rfl, rfl, fun _ hm => .inl hm⟩
              | inr r3Init =>
                dsimp only
                cases proto.finalizeCutOpen _ _ _ _ _ <;> refine ⟨rfl, rfl, rfl, rfl, ?_⟩
                all_goals
                  intro m hm
                  rcases List.mem_cons.mp hm with rfl | hOld
                  · exact .inr ⟨rfl, hQuorum⟩
                  · exact .inl hOld
    rcases h1Eq : execRealSession proto A cl advSt (tapes 0) with ⟨cl1, advSt1, rec1⟩
    rw [h1Eq] at hStep hCheat1
    obtain ⟨hPk1, hCorr1, hTh1, hNp1, hMsgs1⟩ := hStep
    have hDishonest1 : cl1.tsig.corruptParties.length + 1 ≤ cl1.tsig.threshold := by
      rw [hCorr1, hTh1]; exact hDishonest
    have ih := realProtocolExec_approvedMsgs_provenance proto A s (fun i => tapes (i + 1)) cl1 advSt1 hDishonest1
    rcases hRestEq : RealProtocolExec proto A s (fun i => tapes (i + 1)) cl1 advSt1 with ⟨clF, trRest⟩
    rw [hRestEq] at ih
    obtain ⟨hPkF, hCorrF, hThF, hNpF, hMsgsF⟩ := ih
    have hValEq : ∀ apps, validThresholdApproval cl1.tsig apps = validThresholdApproval cl.tsig apps := by
      intro apps
      unfold validThresholdApproval
      rw [hTh1, hNp1, hCorr1, hCheat1]
    refine ⟨hPkF.trans hPk1, hCorrF.trans hCorr1, hThF.trans hTh1, hNpF.trans hNp1, ?_⟩
    intro m hm
    rcases hMsgsF m hm with hm1 | ⟨recR, hMemR, hEqR, hValR, hHonR⟩
    · rcases hMsgs1 m hm1 with hm0 | ⟨hEq0, hVal0⟩
      · exact .inl hm0
      · exact .inr ⟨rec1, .head _, hEq0, hVal0,
          thresholdApproval_requires_honest_party cl.tsig rec1.request.honestApprovers hDishonest hVal0⟩
    · rw [hValEq] at hValR
      rw [hNp1, hCorr1] at hHonR
      exact .inr ⟨recR, .tail _ hMemR, hEqR, hValR, hHonR⟩

/-! ## 4. Compositional Game-Hopping & Hybrid-Argument Combinators (`0 Classical.choice`) -/

/-- Exact acceptance count of distinguisher `D : View → Bool` over finite random-tape space `Fin card`. -/
@[expose] def distAcceptCount {View : Type} (card : Nat)
    (exec : Fin card → View) (D : View → Bool) : Nat :=
  finSum card (fun ω => if D (exec ω) then 1 else 0)

/-- Exact cross-denominator rational addition `a.1 / a.2 + b.1 / b.2 = (a.1*b.2 + b.1*a.2) / (a.2*b.2)`. -/
@[expose] def ratAdd (a b : Nat × Nat) : Nat × Nat :=
  (a.1 * b.2 + b.1 * a.2, a.2 * b.2)

/-- Exact rational distinguishing advantage `|Pr[D(exec₁)=1] - Pr[D(exec₂)=1]|` across arbitrary
    positive finite sample-space cardinalities `card₁, card₂`. -/
@[expose] def rationalAcceptDiff {View : Type}
    (card₁ : Nat) (exec₁ : Fin card₁ → View)
    (card₂ : Nat) (exec₂ : Fin card₂ → View)
    (D : View → Bool) : Nat × Nat :=
  (natAbsDiff (distAcceptCount card₁ exec₁ D * card₂)
              (distAcceptCount card₂ exec₂ D * card₁),
   card₁ * card₂)

private theorem finSum_mul_right : ∀ (n c : Nat) (f : Fin n → Nat),
    finSum n (fun i => f i * c) = finSum n f * c
  | 0, _, _ => by simp [finSum]
  | n + 1, c, f => by
    simp only [finSum, finSum_mul_right n c, Nat.add_mul]

private theorem finSum_swap : ∀ (m n : Nat) (g : Fin m → Fin n → Nat),
    finSum m (fun i => finSum n (fun j => g i j)) =
      finSum n (fun j => finSum m (fun i => g i j))
  | 0, n, _ => by
    simp only [finSum]
    have h0 : finSum n (fun _ => 0) = 0 := by rw [finSum_const]; omega
    exact h0.symm
  | m + 1, n, g => by
    simp only [finSum]
    rw [finSum_swap m n (fun i j => g ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ j), ← finSum_add]

private theorem finSum_point_decomp (n : Nat) (f : Fin n → Nat) (x : Fin n) :
    finSum n (fun j => (if j = x then 1 else 0) * f j) = f x := by
  have hCongr :
      finSum n (fun j => (if j = x then 1 else 0) * f j) =
      finSum n (fun j => (if j = x then 1 else 0) * f x) := by
    apply finSum_congr
    intro j
    by_cases hj : j = x
    · subst hj; rfl
    · simp [hj]
  rw [hCongr, finSum_mul_right, finSum_eq_indicator, Nat.one_mul]

/-- **Constructive Measure-Preserving Bijection Invariance (`finSum_equiv_eq`)**:
    Any `SimpleEquiv (Fin n) (Fin n)` preserves exact finite sums with `0 Classical.choice`. -/
theorem finSum_equiv_eq {n : Nat} (bij : SimpleEquiv (Fin n) (Fin n)) (f : Fin n → Nat) :
    finSum n (fun ω => f (bij.toFun ω)) = finSum n f := by
  have hExpand :
      finSum n (fun ω => f (bij.toFun ω)) =
      finSum n (fun ω => finSum n (fun j => (if j = bij.toFun ω then 1 else 0) * f j)) :=
    finSum_congr (fun ω => (finSum_point_decomp n f (bij.toFun ω)).symm)
  rw [hExpand, finSum_swap]
  apply finSum_congr
  intro j
  have hSwapCond :
      finSum n (fun ω => (if j = bij.toFun ω then 1 else 0) * f j) =
      finSum n (fun ω => (if ω = bij.invFun j then 1 else 0) * f j) := by
    apply finSum_congr
    intro ω
    by_cases h1 : j = bij.toFun ω
    · have h2 : ω = bij.invFun j := by rw [h1, bij.left_inv]
      rw [ite_eq_left h1, ite_eq_left h2]
    · have h2 : ω ≠ bij.invFun j := fun he => h1 (by rw [he, bij.right_inv])
      rw [ite_eq_right h1, ite_eq_right h2]
  rw [hSwapCond, finSum_mul_right, finSum_eq_indicator, Nat.one_mul]

/-- **Combinator 1: Fundamental Lemma of Game-Playing with Measure-Preserving Bijection
    (`bad_event_fundamental_lemma`)**:
    Suppose `realExec` and `idealExec` over `Fin card` (`0 < card`) agree up to a random-tape
    bijection `bij : SimpleEquiv (Fin card) (Fin card)` outside `bad : Fin card → Bool`, i.e.,
    `∀ ω, bad ω = false → realExec ω = idealExec (bij.toFun ω)`.
    Then for EVERY distinguisher `D : View → Bool` (including `OracleComp`-driven interactive
    adversaries), the acceptance count difference is bounded by `badCount`, and both `(adv, card)`
    and `rationalAcceptDiff` satisfy `ratLe ... (badCount, card)`. -/
theorem bad_event_fundamental_lemma {View : Type}
    (card : Nat) (hCardPos : 0 < card)
    (realExec idealExec : Fin card → View)
    (bij : SimpleEquiv (Fin card) (Fin card))
    (bad : Fin card → Bool)
    (hAgreeUnlessBad : ∀ ω : Fin card, bad ω = false → realExec ω = idealExec (bij.toFun ω))
    (D : View → Bool) :
    let badCount := finSum card (fun ω => if bad ω then 1 else 0)
    let advCount := natAbsDiff (distAcceptCount card realExec D) (distAcceptCount card idealExec D)
    advCount ≤ badCount ∧
    ratLe (advCount, card) (badCount, card) ∧
    ratLe (rationalAcceptDiff card realExec card idealExec D) (badCount, card) := by
  intro badCount advCount
  have hBijEq :
      distAcceptCount card idealExec D =
      finSum card (fun ω => if D (idealExec (bij.toFun ω)) then 1 else 0) := by
    unfold distAcceptCount
    exact (finSum_equiv_eq bij (fun ω => if D (idealExec ω) then 1 else 0)).symm
  have hLe : advCount ≤ badCount := by
    dsimp only [advCount, badCount]
    rw [hBijEq]
    exact finSum_indicator_diff_le
      (fun ω => D (realExec ω))
      (fun ω => D (idealExec (bij.toFun ω)))
      bad
      (fun ω hFalse => congrArg D (hAgreeUnlessBad ω hFalse))
  have hMulAbs : ∀ (x y k : Nat), natAbsDiff (x * k) (y * k) = natAbsDiff x y * k := by
    intro x y k
    unfold natAbsDiff
    by_cases hxy : x ≤ y
    · have hxkyk : x * k ≤ y * k := Nat.mul_le_mul_right k hxy
      simp [hxy, hxkyk, Nat.sub_mul]
    · have hyx : y ≤ x := by omega
      have hykxk : y * k ≤ x * k := Nat.mul_le_mul_right k hyx
      by_cases hEq : x * k ≤ y * k
      · have hk0 : x * k = y * k := Nat.le_antisymm hEq hykxk
        have hSub0 : (x - y) * k = 0 := by rw [Nat.sub_mul, hk0, Nat.sub_self]
        simp [hxy, hk0, hSub0]
      · simp [hxy, hEq, Nat.sub_mul]
  refine ⟨hLe, ⟨hCardPos, hCardPos, Nat.mul_le_mul_right card hLe⟩, ?_⟩
  unfold ratLe rationalAcceptDiff
  dsimp only
  have hProdPos : 0 < card * card := Nat.mul_pos hCardPos hCardPos
  refine ⟨hProdPos, hCardPos, ?_⟩
  rw [hMulAbs]
  change (advCount * card) * card ≤ badCount * (card * card)
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_right (card * card) hLe

private theorem finSum_snoc : ∀ (k : Nat) (g : Nat → Nat),
    finSum (k + 1) (fun i => g i.1) = finSum k (fun i => g i.1) + g k
  | 0, g => by simp [finSum]
  | k + 1, g => by
    conv => lhs; rw [finSum]
    dsimp only
    rw [finSum_snoc k (fun j => g (j + 1))]
    conv => rhs; rw [finSum]
    dsimp only
    omega

/-- **Combinator 2: Multi-Session Hybrid-Argument Telescope (`hybrid_multi_session_le`)**:
    Given `Q_s + 1` hybrid games `hybrids 0, ..., hybrids Q_s` over `Fin card` (`0 < card`),
    where each adjacent session hop `i → i + 1` has distinguishing count bounded by `hopBound i`:
    1. Total advantage between `hybrids 0` and `hybrids Q_s` is `≤ finSum Q_s hopBound`;
    2. `ratLe` holds against `(finSum Q_s hopBound, card)`; and
    3. Under any per-session cap `∀ i, hopBound i ≤ eps`, `ratLe` holds against `(Q_s * eps, card)`. -/
theorem hybrid_multi_session_le {View : Type}
    (card Q_s : Nat) (hCardPos : 0 < card)
    (hybrids : (i : Nat) → i ≤ Q_s → Fin card → View)
    (hopBound : Fin Q_s → Nat)
    (D : View → Bool)
    (hHops : ∀ idx : Fin Q_s,
      natAbsDiff (distAcceptCount card (hybrids idx.val (Nat.le_of_lt idx.isLt)) D)
                 (distAcceptCount card (hybrids (idx.val + 1) idx.isLt) D) ≤ hopBound idx) :
    let totalAdv := natAbsDiff (distAcceptCount card (hybrids 0 (Nat.zero_le Q_s)) D)
                               (distAcceptCount card (hybrids Q_s (Nat.le_refl Q_s)) D)
    totalAdv ≤ finSum Q_s hopBound ∧
    ratLe (totalAdv, card) (finSum Q_s hopBound, card) ∧
    (∀ eps : Nat, (∀ idx : Fin Q_s, hopBound idx ≤ eps) →
      ratLe (totalAdv, card) (Q_s * eps, card)) := by
  let g : Nat → Nat := fun i => if h : i < Q_s then hopBound ⟨i, h⟩ else 0
  have hFinEq : ∀ (m : Nat) (hm : m ≤ Q_s),
      finSum m (fun i => hopBound ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩) =
      finSum m (fun i => g i.val) := by
    intro m hm
    apply finSum_congr
    intro i
    have hi : i.val < Q_s := Nat.lt_of_lt_of_le i.isLt hm
    simp [g, hi]
  have hTel :
      ∀ (k : Nat) (hk : k ≤ Q_s),
        natAbsDiff (distAcceptCount card (hybrids 0 (Nat.zero_le Q_s)) D)
                   (distAcceptCount card (hybrids k hk) D) ≤
          finSum k (fun i => hopBound ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [finSum, natAbsDiff]
    | succ k ih =>
      intro hkSucc
      have hkLt : k < Q_s := hkSucc
      have hkLe : k ≤ Q_s := Nat.le_of_lt hkLt
      have ihK := ih hkLe
      have hLast := hHops ⟨k, hkLt⟩
      dsimp only at hLast
      have hTri := natAbsDiff_triangle
        (distAcceptCount card (hybrids 0 (Nat.zero_le Q_s)) D)
        (distAcceptCount card (hybrids k hkLe) D)
        (distAcceptCount card (hybrids (k + 1) hkSucc) D)
      have hGk : g k = hopBound ⟨k, hkLt⟩ := by simp [g, hkLt]
      rw [hFinEq (k + 1) hkSucc, finSum_snoc k g, ← hFinEq k hkLe, hGk]
      omega
  intro totalAdv
  have hMain : totalAdv ≤ finSum Q_s hopBound := hTel Q_s (Nat.le_refl Q_s)
  refine ⟨hMain, ⟨hCardPos, hCardPos, Nat.mul_le_mul_right card hMain⟩, ?_⟩
  intro eps hCap
  have hLeConst : finSum Q_s hopBound ≤ Q_s * eps := by
    rw [← finSum_const Q_s eps]
    exact finSum_le_finSum hCap
  exact ⟨hCardPos, hCardPos, Nat.mul_le_mul_right card (Nat.le_trans hMain hLeConst)⟩

theorem ratLe_trans {a b c : Nat × Nat} (h1 : ratLe a b) (h2 : ratLe b c) : ratLe a c := by
  rcases h1 with ⟨ha2, hb2, hab⟩
  rcases h2 with ⟨_, hc2, hbc⟩
  refine ⟨ha2, hc2, ?_⟩
  have hMul1 : a.1 * b.2 * c.2 ≤ b.1 * a.2 * c.2 := Nat.mul_le_mul_right c.2 hab
  have hMul2 : b.1 * c.2 * a.2 ≤ c.1 * b.2 * a.2 := Nat.mul_le_mul_right a.2 hbc
  have hRearr1 : b.1 * a.2 * c.2 = b.1 * c.2 * a.2 := by ac_rfl
  have hRearr2 : c.1 * b.2 * a.2 = c.1 * a.2 * b.2 := by ac_rfl
  have hRearr0 : a.1 * b.2 * c.2 = a.1 * c.2 * b.2 := by ac_rfl
  rw [hRearr0, hRearr1] at hMul1
  rw [hRearr2] at hMul2
  exact Nat.le_of_mul_le_mul_right (Nat.le_trans hMul1 hMul2) hb2

private theorem natAbsDiff_mul_right (x y k : Nat) :
    natAbsDiff (x * k) (y * k) = natAbsDiff x y * k := by
  unfold natAbsDiff
  by_cases hxy : x ≤ y
  · simp [hxy, Nat.mul_le_mul_right k hxy, Nat.sub_mul]
  · have hyx : y ≤ x := by omega
    have hykxk : y * k ≤ x * k := Nat.mul_le_mul_right k hyx
    by_cases hEq : x * k ≤ y * k
    · have hk0 : x * k = y * k := Nat.le_antisymm hEq hykxk
      have hSub0 : (x - y) * k = 0 := by rw [Nat.sub_mul, hk0, Nat.sub_self]
      simp [hxy, hk0, hSub0]
    · simp [hxy, hEq, Nat.sub_mul]

/-- A post-processing function from the inner multi-session `ExecTranscript` to a higher-level
    view `OuterView`. It reads a finished transcript; it cannot interact with a running execution
    or interleave other sessions. -/
structure OuterCallingContext (InnerView OuterView : Type) where
  postProcess : InnerView → OuterView

/-- **Combinator 3: triangle inequality under post-processing (`uc_transitive_composition`)**:
    For any three executions `(N₁, realExec)`, `(N₂, hybridExec)`, `(N₃, idealExec)` (over possibly
    distinct finite random-tape cardinalities `N₁, N₂, N₃ > 0`), any post-processing
    `ctx : OuterCallingContext InnerView OuterView` and distinguisher `D : OuterView → Bool`:
    if `realExec ≈_{eps₁} hybridExec` and `hybridExec ≈_{eps₂} idealExec` under `D ∘ ctx.postProcess`,
    then `realExec ≈_{ratAdd eps₁ eps₂} idealExec`. The name is historical; this is not a
    composition theorem for interleaved protocol executions. -/
theorem uc_transitive_composition {InnerView OuterView : Type}
    (N₁ N₂ N₃ : Nat) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hN₃ : 0 < N₃)
    (realExec : Fin N₁ → InnerView)
    (hybridExec : Fin N₂ → InnerView)
    (idealExec : Fin N₃ → InnerView)
    (ctx : OuterCallingContext InnerView OuterView)
    (D : OuterView → Bool)
    (eps₁ eps₂ : Nat × Nat)
    (hStep₁ : ratLe (rationalAcceptDiff N₁ (fun ω => ctx.postProcess (realExec ω))
                                        N₂ (fun ω => ctx.postProcess (hybridExec ω)) D) eps₁)
    (hStep₂ : ratLe (rationalAcceptDiff N₂ (fun ω => ctx.postProcess (hybridExec ω))
                                        N₃ (fun ω => ctx.postProcess (idealExec ω)) D) eps₂) :
    ratLe (rationalAcceptDiff N₁ (fun ω => ctx.postProcess (realExec ω))
                              N₃ (fun ω => ctx.postProcess (idealExec ω)) D)
          (ratAdd eps₁ eps₂) := by
  let D_in : InnerView → Bool := fun v => D (ctx.postProcess v)
  let A₁ := distAcceptCount N₁ realExec D_in
  let A₂ := distAcceptCount N₂ hybridExec D_in
  let A₃ := distAcceptCount N₃ idealExec D_in
  rcases hStep₁ with ⟨_, he₁Pos, hLe₁⟩
  rcases hStep₂ with ⟨_, he₂Pos, hLe₂⟩
  change natAbsDiff (A₁ * N₂) (A₂ * N₁) * eps₁.2 ≤ eps₁.1 * (N₁ * N₂) at hLe₁
  change natAbsDiff (A₂ * N₃) (A₃ * N₂) * eps₂.2 ≤ eps₂.1 * (N₂ * N₃) at hLe₂
  unfold ratLe rationalAcceptDiff ratAdd
  refine ⟨Nat.mul_pos hN₁ hN₃, Nat.mul_pos he₁Pos he₂Pos, ?_⟩
  change natAbsDiff (A₁ * N₃) (A₃ * N₁) * (eps₁.2 * eps₂.2) ≤
    (eps₁.1 * eps₂.2 + eps₂.1 * eps₁.2) * (N₁ * N₃)
  have hTri := natAbsDiff_triangle (A₁ * N₃ * N₂) (A₂ * N₁ * N₃) (A₃ * N₁ * N₂)
  have hTerm13 : natAbsDiff (A₁ * N₃ * N₂) (A₃ * N₁ * N₂) = natAbsDiff (A₁ * N₃) (A₃ * N₁) * N₂ := by
    have hR : A₃ * N₁ * N₂ = A₃ * N₁ * N₂ := rfl
    rw [← natAbsDiff_mul_right]
  have hTerm12 : natAbsDiff (A₁ * N₃ * N₂) (A₂ * N₁ * N₃) = natAbsDiff (A₁ * N₂) (A₂ * N₁) * N₃ := by
    have hL : A₁ * N₃ * N₂ = A₁ * N₂ * N₃ := by ac_rfl
    rw [hL, ← natAbsDiff_mul_right]
  have hTerm23 : natAbsDiff (A₂ * N₁ * N₃) (A₃ * N₁ * N₂) = natAbsDiff (A₂ * N₃) (A₃ * N₂) * N₁ := by
    have hL : A₂ * N₁ * N₃ = A₂ * N₃ * N₁ := by ac_rfl
    have hR : A₃ * N₁ * N₂ = A₃ * N₂ * N₁ := by ac_rfl
    rw [hL, hR, ← natAbsDiff_mul_right]
  rw [hTerm13, hTerm12, hTerm23] at hTri
  have hScaled := Nat.mul_le_mul_right (eps₁.2 * eps₂.2) hTri
  rw [Nat.add_mul] at hScaled
  have hB1 : natAbsDiff (A₁ * N₂) (A₂ * N₁) * N₃ * (eps₁.2 * eps₂.2) ≤
      eps₁.1 * eps₂.2 * (N₁ * N₃) * N₂ := by
    have hRearrL : natAbsDiff (A₁ * N₂) (A₂ * N₁) * N₃ * (eps₁.2 * eps₂.2) =
        (natAbsDiff (A₁ * N₂) (A₂ * N₁) * eps₁.2) * (N₃ * eps₂.2) := by ac_rfl
    have hRearrR : eps₁.1 * eps₂.2 * (N₁ * N₃) * N₂ =
        (eps₁.1 * (N₁ * N₂)) * (N₃ * eps₂.2) := by ac_rfl
    rw [hRearrL, hRearrR]
    exact Nat.mul_le_mul_right (N₃ * eps₂.2) hLe₁
  have hB2 : natAbsDiff (A₂ * N₃) (A₃ * N₂) * N₁ * (eps₁.2 * eps₂.2) ≤
      eps₂.1 * eps₁.2 * (N₁ * N₃) * N₂ := by
    have hRearrL : natAbsDiff (A₂ * N₃) (A₃ * N₂) * N₁ * (eps₁.2 * eps₂.2) =
        (natAbsDiff (A₂ * N₃) (A₃ * N₂) * eps₂.2) * (N₁ * eps₁.2) := by ac_rfl
    have hRearrR : eps₂.1 * eps₁.2 * (N₁ * N₃) * N₂ =
        (eps₂.1 * (N₂ * N₃)) * (N₁ * eps₁.2) := by ac_rfl
    rw [hRearrL, hRearrR]
    exact Nat.mul_le_mul_right (N₁ * eps₁.2) hLe₂
  have hComb : natAbsDiff (A₁ * N₃) (A₃ * N₁) * (eps₁.2 * eps₂.2) * N₂ ≤
      (eps₁.1 * eps₂.2 + eps₂.1 * eps₁.2) * (N₁ * N₃) * N₂ := by
    have hL : natAbsDiff (A₁ * N₃) (A₃ * N₁) * N₂ * (eps₁.2 * eps₂.2) =
        natAbsDiff (A₁ * N₃) (A₃ * N₁) * (eps₁.2 * eps₂.2) * N₂ := by ac_rfl
    rw [← hL]
    have hSum := Nat.add_le_add hB1 hB2
    have hR : eps₁.1 * eps₂.2 * (N₁ * N₃) * N₂ + eps₂.1 * eps₁.2 * (N₁ * N₃) * N₂ =
        (eps₁.1 * eps₂.2 + eps₂.1 * eps₁.2) * (N₁ * N₃) * N₂ := by
      rw [Nat.add_mul, Nat.add_mul]
    rw [hR] at hSum
    exact Nat.le_trans hScaled hSum
  exact Nat.le_of_mul_le_mul_right hComb hN₂

/-- **Inhabitedness & Tightness Witness (`inhabited_interactive_uc_combinators`)**:
    Exhibits concrete non-trivial `SimpleEquiv` XOR-bijection over `Fin 4`, non-zero bad-event bound,
    and 2-hop heterogeneous `uc_transitive_composition` (`N₁ = 2, N₂ = 4, N₃ = 2`). -/
theorem inhabited_interactive_uc_combinators :
    ∃ (bij : SimpleEquiv (Fin 4) (Fin 4)) (realE idealE : Fin 4 → Bool) (bad : Fin 4 → Bool),
      bij.toFun ⟨0, by decide⟩ ≠ ⟨0, by decide⟩ ∧
      (∀ ω, bad ω = false → realE ω = idealE (bij.toFun ω)) ∧
      ratLe (rationalAcceptDiff 4 realE 4 idealE id) (1, 4) := by
  let flip : Fin 4 → Fin 4 := fun i => ⟨3 - i.1, by omega⟩
  have hInv : ∀ i : Fin 4, flip (flip i) = i := fun i => Fin.ext (by dsimp [flip]; omega)
  let bij : SimpleEquiv (Fin 4) (Fin 4) := ⟨flip, flip, hInv, hInv⟩
  let idealE : Fin 4 → Bool := fun i => i.1 == 3
  let realE : Fin 4 → Bool := fun i => (i.1 == 0) || (i.1 == 1)
  let bad : Fin 4 → Bool := fun i => i.1 == 1
  have hAgree : ∀ ω : Fin 4, bad ω = false → realE ω = idealE (bij.toFun ω) := by
    intro ⟨v, hv⟩ hBad
    dsimp [bad] at hBad
    dsimp [realE, idealE, bij, flip]
    match v with
    | 0 => rfl
    | 1 => cases hBad
    | 2 => rfl
    | 3 => rfl
    | n + 4 => omega
  have hMain := (bad_event_fundamental_lemma 4 (by decide) realE idealE bij bad hAgree id).2.2
  have hBadCount : finSum 4 (fun ω : Fin 4 => if bad ω then 1 else 0) = 1 := rfl
  have hNe0 : bij.toFun ⟨0, by decide⟩ ≠ ⟨0, by decide⟩ := by
    intro hEq
    have hVal : (bij.toFun ⟨0, by decide⟩).val = 0 := congrArg Fin.val hEq
    dsimp [bij, flip] at hVal
    omega
  rw [hBadCount] at hMain
  exact ⟨bij, realE, idealE, bad, hNe0, hAgree, hMain⟩

/-! ## 5. Signing-Oracle Locality of the Ideal World & Forgery-Count Transfer -/

theorem IdealFunctionalityExec_succ_eq {PK SimTape SimR1 SimR2 SimR3 AdvState : Type}
    (idealSignOracle : SessionScheduleReq → ByteArray)
    (sim : BlackBoxUcSimulator PK SimTape SimR1 SimR2 SimR3)
    (A : UcRushingAdversary AdvState) (s : Nat) (tapes : Nat → SimTape)
    (icl : IdealClusterState PK) (advSt : AdvState) :
    IdealFunctionalityExec idealSignOracle sim A (s + 1) tapes icl advSt =
      ((IdealFunctionalityExec idealSignOracle sim A s (fun i => tapes (i + 1))
          (execIdealSession idealSignOracle sim A icl advSt (tapes 0)).1
          (execIdealSession idealSignOracle sim A icl advSt (tapes 0)).2.1).1,
       ⟨(IdealFunctionalityExec idealSignOracle sim A s (fun i => tapes (i + 1))
          (execIdealSession idealSignOracle sim A icl advSt (tapes 0)).1
          (execIdealSession idealSignOracle sim A icl advSt (tapes 0)).2.1).2.finalAdvState,
        (execIdealSession idealSignOracle sim A icl advSt (tapes 0)).2.2 ::
          (IdealFunctionalityExec idealSignOracle sim A s (fun i => tapes (i + 1))
            (execIdealSession idealSignOracle sim A icl advSt (tapes 0)).1
            (execIdealSession idealSignOracle sim A icl advSt (tapes 0)).2.1).2.sessions⟩) := by
  rfl

/-- The wire record of an ideal session always carries the request the adversary scheduled. -/
theorem execIdealSession_request {PK SimTape SimR1 SimR2 SimR3 AdvState : Type}
    (idealSignOracle : SessionScheduleReq → ByteArray)
    (sim : BlackBoxUcSimulator PK SimTape SimR1 SimR2 SimR3)
    (A : UcRushingAdversary AdvState)
    (icl : IdealClusterState PK) (advSt : AdvState) (tape : SimTape) :
    (execIdealSession idealSignOracle sim A icl advSt tape).2.2.request =
      (A.scheduleSession advSt).1 := by
  unfold execIdealSession
  dsimp only
  cases validThresholdApproval icl.tsig (A.scheduleSession advSt).1.honestApprovers
  · rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases walPreSignStep icl.honestWal _ _ _ with
    | err _ _ => rfl
    | ok _ resOut =>
      cases resOut with
      | replayCached _ => rfl
      | authorizedFresh _ =>
        dsimp only
        cases sim.simVerifyRound1 _ _ _ _ _ with
        | inl p1 => rcases p1 with ⟨_, b⟩; cases b <;> rfl
        | inr _ =>
          dsimp only
          cases sim.simPreCutBarrier _ _ _ _ _ with
          | inl _ => rfl
          | inr _ =>
            dsimp only
            cases sim.simFinalizeCut _ _ _ _ _ _ <;> rfl

/-- **Single-Session Signing-Oracle Locality (`execIdealSession_oracle_congr`)**:
    an ideal session reads `idealSignOracle` at most at its own scheduled request, and only when the
    session reaches Round 3. Two oracles that agree there produce the same cluster state, adversary
    state and wire record, for every simulator whose Round-3 message list is never empty. -/
theorem execIdealSession_oracle_congr {PK SimTape SimR1 SimR2 SimR3 AdvState : Type}
    (O O' : SessionScheduleReq → ByteArray)
    (sim : BlackBoxUcSimulator PK SimTape SimR1 SimR2 SimR3)
    (hR3 : ∀ pk corr req s3 sigB tape, (sim.simRound3 pk corr req s3 sigB tape).1 ≠ [])
    (A : UcRushingAdversary AdvState)
    (icl : IdealClusterState PK) (advSt : AdvState) (tape : SimTape)
    (hAgree : (execIdealSession O sim A icl advSt tape).2.2.honestRound3 ≠ [] →
      O' (A.scheduleSession advSt).1 = O (A.scheduleSession advSt).1) :
    execIdealSession O' sim A icl advSt tape = execIdealSession O sim A icl advSt tape := by
  revert hAgree
  unfold execIdealSession
  dsimp only
  cases validThresholdApproval icl.tsig (A.scheduleSession advSt).1.honestApprovers
  · intro _; rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases walPreSignStep icl.honestWal _ _ _ with
    | err _ _ => intro _; rfl
    | ok _ resOut =>
      cases resOut with
      | replayCached _ => intro _; rfl
      | authorizedFresh _ =>
        dsimp only
        cases sim.simVerifyRound1 _ _ _ _ _ with
        | inl p1 => intro _; rfl
        | inr _ =>
          dsimp only
          cases sim.simPreCutBarrier _ _ _ _ _ with
          | inl _ => intro _; rfl
          | inr _ =>
            dsimp only
            intro hAgree
            have hEq : O' (A.scheduleSession advSt).1 = O (A.scheduleSession advSt).1 := by
              apply hAgree
              cases sim.simFinalizeCut _ _ _ _ _ _ <;> exact hR3 _ _ _ _ _ _
            rw [hEq]

/-- **Multi-Session Signing-Oracle Locality (`IdealFunctionalityExec_oracle_congr`)**:
    across any number of adaptively scheduled sessions, the whole ideal-world result (final cluster
    state and complete transcript) is determined by the values of the signing oracle on the requests
    of the sessions that reached Round 3. Nothing else about the signing key can influence what the
    adversary sees. -/
theorem IdealFunctionalityExec_oracle_congr {PK SimTape SimR1 SimR2 SimR3 AdvState : Type}
    (O O' : SessionScheduleReq → ByteArray)
    (sim : BlackBoxUcSimulator PK SimTape SimR1 SimR2 SimR3)
    (hR3 : ∀ pk corr req s3 sigB tape, (sim.simRound3 pk corr req s3 sigB tape).1 ≠ [])
    (A : UcRushingAdversary AdvState) :
    ∀ (s : Nat) (tapes : Nat → SimTape) (icl : IdealClusterState PK) (advSt : AdvState),
      (∀ rec ∈ (IdealFunctionalityExec O sim A s tapes icl advSt).2.sessions,
        rec.honestRound3 ≠ [] → O' rec.request = O rec.request) →
      IdealFunctionalityExec O' sim A s tapes icl advSt =
        IdealFunctionalityExec O sim A s tapes icl advSt
  | 0, _, _, _, _ => rfl
  | s + 1, tapes, icl, advSt, hAgree => by
    rw [IdealFunctionalityExec_succ_eq O sim A s tapes icl advSt] at hAgree
    rw [IdealFunctionalityExec_succ_eq O' sim A s tapes icl advSt,
        IdealFunctionalityExec_succ_eq O sim A s tapes icl advSt]
    have hHead : execIdealSession O' sim A icl advSt (tapes 0) =
        execIdealSession O sim A icl advSt (tapes 0) := by
      apply execIdealSession_oracle_congr O O' sim hR3
      intro hNe
      have h := hAgree _ (List.Mem.head _) hNe
      rwa [execIdealSession_request] at h
    rw [hHead]
    have hTail := IdealFunctionalityExec_oracle_congr O O' sim hR3 A s (fun i => tapes (i + 1))
      (execIdealSession O sim A icl advSt (tapes 0)).1
      (execIdealSession O sim A icl advSt (tapes 0)).2.1
      (fun rec hMem hNe => hAgree rec (List.Mem.tail _ hMem) hNe)
    rw [hTail]

private theorem nat_count_transfer (R I c e1 e2 : Nat) (hc : 0 < c)
    (h : natAbsDiff (R * c) (I * c) * e2 ≤ e1 * (c * c)) :
    R * e2 ≤ I * e2 + e1 * c := by
  rw [natAbsDiff_mul_right] at h
  have hL : natAbsDiff R I * c * e2 = natAbsDiff R I * e2 * c := by ac_rfl
  have hR : e1 * (c * c) = e1 * c * c := by ac_rfl
  rw [hL, hR] at h
  have h3 : natAbsDiff R I * e2 ≤ e1 * c := Nat.le_of_mul_le_mul_right h hc
  have h4 : R ≤ I + natAbsDiff R I := by
    unfold natAbsDiff
    split <;> omega
  have h5 : R * e2 ≤ (I + natAbsDiff R I) * e2 := Nat.mul_le_mul_right e2 h4
  rw [Nat.add_mul] at h5
  exact Nat.le_trans h5 (Nat.add_le_add_left h3 _)

/-- **Combinator 4: Forgery-Count Transfer (`forgery_count_transfer`)**:
    if two executions over the same tape space are within `eps` for the Boolean event `win`, then
    `Pr[win in real] ≤ Pr[win in ideal] + eps`, stated as an exact cross-multiplied count inequality. -/
theorem forgery_count_transfer {View : Type} (card : Nat)
    (realExec idealExec : Fin card → View) (win : View → Bool) (eps : Nat × Nat)
    (hUc : ratLe (rationalAcceptDiff card realExec card idealExec win) eps) :
    distAcceptCount card realExec win * eps.2 ≤
      distAcceptCount card idealExec win * eps.2 + eps.1 * card := by
  obtain ⟨hDen, _, hLe⟩ := hUc
  have hCard : 0 < card := by
    rcases Nat.eq_zero_or_pos card with h0 | hPos
    · have hDen' : 0 < card * card := hDen
      rw [h0] at hDen'
      exact absurd hDen' (by decide)
    · exact hPos
  exact nat_count_transfer _ _ card eps.1 eps.2 hCard hLe

/-- If no tape lets the ideal execution win, the real winning count is bounded by `eps` alone. -/
theorem forgery_count_le_of_ideal_never_wins {View : Type} (card : Nat)
    (realExec idealExec : Fin card → View) (win : View → Bool) (eps : Nat × Nat)
    (hUc : ratLe (rationalAcceptDiff card realExec card idealExec win) eps)
    (hNever : ∀ ω : Fin card, win (idealExec ω) = false) :
    distAcceptCount card realExec win * eps.2 ≤ eps.1 * card := by
  have hT := forgery_count_transfer card realExec idealExec win eps hUc
  have hZero : distAcceptCount card idealExec win = 0 := by
    unfold distAcceptCount
    have hC : finSum card (fun ω => if win (idealExec ω) then 1 else 0) = finSum card (fun _ => 0) :=
      finSum_congr (fun ω => by rw [hNever ω]; rfl)
    rw [hC, finSum_const, Nat.mul_zero]
  rw [hZero, Nat.zero_mul, Nat.zero_add] at hT
  exact hT

/-! ## 6. `F_tsig` over the Checked Stateless Hypertree Signer: UC Emulation ⇒ Concrete Hash-Game Witness -/

/-- Signing oracle of the ideal functionality instantiated with the checked stateless hypertree
    signer. `ser` is an arbitrary wire encoding of the (possibly failed) signing result. -/
def hypertreeIdealSignOracle (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (grindLimit : Nat) (ser : Option PqHashSig → ByteArray) : SessionScheduleReq → ByteArray :=
  fun req => ser (evalStatelessCheckedSign suite params sk req.msg req.optRand grindLimit)

/-- Signing queries visible in a transcript: exactly the requests of sessions that reached Round 3. -/
def transcriptHypertreeQueries {AdvState : Type} (grindLimit : Nat)
    (tr : ExecTranscript AdvState) : List CheckedStatelessQuery :=
  (tr.sessions.filter (fun rec => !rec.honestRound3.isEmpty)).map
    (fun rec => ⟨rec.request.msg, rec.request.optRand, grindLimit⟩)

/-- EUF-CMA winning predicate on a transcript: the forger's output verifies under the checked
    stateless verifier and its message was never the request of a session that reached Round 3. -/
def hypertreeForgeryWins {AdvState : Type} (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (forgeOut : ExecTranscript AdvState → List UInt8 × PqHashSig)
    (tr : ExecTranscript AdvState) : Bool :=
  verifyStatelessChecked suite params pk (forgeOut tr).1 (forgeOut tr).2 &&
  tr.sessions.all (fun rec => rec.honestRound3.isEmpty || decide (rec.request.msg ≠ (forgeOut tr).1))

private theorem list_isEmpty_false_of_ne_nil {α : Type} : ∀ {l : List α}, l ≠ [] → l.isEmpty = false
  | [], h => absurd rfl h
  | _ :: _, _ => rfl

private theorem list_ne_nil_of_isEmpty_false {α : Type} : ∀ {l : List α}, l.isEmpty = false → l ≠ []
  | [], h => by cases h
  | _ :: _, _ => fun hNil => by cases hNil

/-- Constructive extraction of a `HypertreeForgeryBreak` from any transcript on which
    `hypertreeForgeryWins` holds. The query log is read off the transcript, and no upper-layer oracle
    premise is left to the caller. -/
def hypertreeForgeryBreak_of_wins {AdvState : Type}
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey) (grindLimit : Nat)
    (hGeom : (params.w = 4 ∧ params.ell1 = 128) ∨ (params.w = 16 ∧ params.ell1 = 64))
    (hLayers : params.numLayers ≤ 2 ^ 32)
    (forgeOut : ExecTranscript AdvState → List UInt8 × PqHashSig)
    (tr : ExecTranscript AdvState)
    (hWin : hypertreeForgeryWins suite params (derivePublicKey suite params sk) forgeOut tr = true) :
    HypertreeForgeryBreak suite params sk (forgeOut tr).1 (forgeOut tr).2
      ((signingOracleLog suite params sk
          (toLegacyStatelessQueries suite params sk (transcriptHypertreeQueries grindLimit tr))).flatMap fun e =>
        (List.range params.forsTrees).map fun j =>
          (UInt64.ofNat (e.2.leafGlobalIdx / 2 ^ params.subtreeHeight),
           e.2.leafGlobalIdx % 2 ^ params.subtreeHeight,
           sigForsLeafIdx suite params (derivePublicKey suite params sk) e.1 e.2 j)) :=
  checked_stateless_hypertree_euf_cma_extract_of_fresh_queries suite params sk
    (transcriptHypertreeQueries grindLimit tr) (forgeOut tr).1 (forgeOut tr).2 hGeom hLayers
    (fun q hq => by
      unfold hypertreeForgeryWins at hWin
      have hAll := (Bool.and_eq_true_iff.mp hWin).2
      unfold transcriptHypertreeQueries at hq
      obtain ⟨rec, hRecF, hQEq⟩ := List.mem_map.mp hq
      obtain ⟨hRecMem, hR3⟩ := List.mem_filter.mp hRecF
      have hRecOk := List.all_eq_true.mp hAll rec hRecMem
      have hNotEmpty : rec.honestRound3.isEmpty = false := by
        cases hE : rec.honestRound3.isEmpty
        · rfl
        · rw [hE] at hR3; cases hR3
      rw [hNotEmpty, Bool.false_or] at hRecOk
      rw [← hQEq]
      exact of_decide_eq_true hRecOk)
    (Bool.and_eq_true_iff.mp (by unfold hypertreeForgeryWins at hWin; exact hWin)).1

/-- **UC Emulation of `F_tsig[hypertree]` ⇒ Concrete Hash-Game Witness
    (`uc_emulation_forgery_to_hypertree_hash_game`)**:
    Let `proto` be ANY 3-round interactive threshold protocol, `sim` ANY black-box simulator with a
    non-empty Round-3 message list, and `A` ANY rushing adversary scheduling `Q_s` sessions. Suppose
    the real execution and the ideal execution (ideal functionality instantiated with the checked
    stateless hypertree signer) are within `eps` for the forgery event `hypertreeForgeryWins`
    (premise `hUc`, the UC-emulation bound of the protocol at hand). Then:
    1. `Pr[A forges in the real protocol] ≤ Pr[A forges in the ideal world] + eps`
       (exact cross-multiplied count inequality);
    2. every tape on which the forger wins in the ideal world yields a `HypertreeForgeryBreak`
       (WOTS backward inversion, FORS preimage, raw-hash collision, or FORS subset cover) whose
       revealed-FORS index list is computed from the transcript's own Round-3 requests; and
    3. the ideal transcript is unchanged by replacing the signing oracle with any oracle that agrees
       on the Round-3 requests of that transcript, so the forger's input depends on the signing key
       only through those signing queries.
    No upper-layer oracle premise and no abstract EUF-CMA hypothesis appears. -/
theorem uc_emulation_forgery_to_hypertree_hash_game
    {PK ShareT SessionTape R1St R2St R3St SimTape SimR1 SimR2 SimR3 AdvState : Type}
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (grindLimit : Nat) (ser : Option PqHashSig → ByteArray)
    (hGeom : (params.w = 4 ∧ params.ell1 = 128) ∨ (params.w = 16 ∧ params.ell1 = 64))
    (hLayers : params.numLayers ≤ 2 ^ 32)
    (proto : InteractiveThresholdProtocol PK ShareT SessionTape R1St R2St R3St)
    (sim : BlackBoxUcSimulator PK SimTape SimR1 SimR2 SimR3)
    (hR3 : ∀ pk corr req s3 sigB tape, (sim.simRound3 pk corr req s3 sigB tape).1 ≠ [])
    (A : UcRushingAdversary AdvState) (Q_s card : Nat)
    (realTapes : Fin card → Nat → SessionTape) (simTapes : Fin card → Nat → SimTape)
    (cl : RealClusterState PK ShareT) (icl : IdealClusterState PK) (advSt : AdvState)
    (forgeOut : ExecTranscript AdvState → List UInt8 × PqHashSig)
    (eps : Nat × Nat)
    (hUc : ratLe
      (rationalAcceptDiff card
        (fun ω => (RealProtocolExec proto A Q_s (realTapes ω) cl advSt).2)
        card
        (fun ω => (IdealFunctionalityExec (hypertreeIdealSignOracle suite params sk grindLimit ser)
          sim A Q_s (simTapes ω) icl advSt).2)
        (hypertreeForgeryWins suite params (derivePublicKey suite params sk) forgeOut)) eps) :
    let O := hypertreeIdealSignOracle suite params sk grindLimit ser
    let win := hypertreeForgeryWins suite params (derivePublicKey suite params sk) forgeOut
    let realView : Fin card → ExecTranscript AdvState := fun ω =>
      (RealProtocolExec proto A Q_s (realTapes ω) cl advSt).2
    let idealView : Fin card → ExecTranscript AdvState := fun ω =>
      (IdealFunctionalityExec O sim A Q_s (simTapes ω) icl advSt).2
    distAcceptCount card realView win * eps.2 ≤
      distAcceptCount card idealView win * eps.2 + eps.1 * card ∧
    (∀ ω : Fin card, win (idealView ω) = true →
      Nonempty (HypertreeForgeryBreak suite params sk (forgeOut (idealView ω)).1 (forgeOut (idealView ω)).2
        ((signingOracleLog suite params sk
            (toLegacyStatelessQueries suite params sk
              (transcriptHypertreeQueries grindLimit (idealView ω)))).flatMap fun e =>
          (List.range params.forsTrees).map fun j =>
            (UInt64.ofNat (e.2.leafGlobalIdx / 2 ^ params.subtreeHeight),
             e.2.leafGlobalIdx % 2 ^ params.subtreeHeight,
             sigForsLeafIdx suite params (derivePublicKey suite params sk) e.1 e.2 j)))) ∧
    (∀ (ω : Fin card) (O' : SessionScheduleReq → ByteArray),
      (∀ rec ∈ (idealView ω).sessions, rec.honestRound3 ≠ [] → O' rec.request = O rec.request) →
      (IdealFunctionalityExec O' sim A Q_s (simTapes ω) icl advSt).2 = idealView ω) := by
  intro O win realView idealView
  refine ⟨forgery_count_transfer card realView idealView win eps hUc, ?_, ?_⟩
  · intro ω hWin
    exact ⟨hypertreeForgeryBreak_of_wins suite params sk grindLimit hGeom hLayers forgeOut
      (idealView ω) hWin⟩
  · intro ω O' hAgree
    exact congrArg Prod.snd
      (IdealFunctionalityExec_oracle_congr O O' sim hR3 A Q_s (simTapes ω) icl advSt hAgree)

end Qsag
end

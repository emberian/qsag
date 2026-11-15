module
/-
# Qsag.Exec.InteractiveUcEngine — Multi-Round, Multi-Session Rushing-Adversary UC Execution Engine

Lean 4.35 cluster-callback execution model with constructive finite-game simulations.
The callbacks receive the complete honest-share map; party-network refinement is separate:
1. **Persistent Cross-Session `WalLatchState` & Modeled Custody (`HonestCustodyVault`)**:
   Models crash-idempotent monotonic epoch latching, enrolled public-key digest pinning, sticky
   active-fault quarantine (`walPoisonVault` sets `poisoned = true` and clears the modeled
   share field), and strictly monotonic per-session mask-tape cursors. Physical erasure and
   exclusion of copies of earlier pure states require an implementation refinement.
2. **Multi-Round, Multi-Session Rushing-Adversary Cluster Execution
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
   `uc_production_threshold_forgery_transfer` additionally uses `verifyProductionPqHashSig`
   and the `ThresholdMpc` production signing oracle, with an explicit emulation premise.
-/

public import Qsag.Math.Constructive
public import Qsag.Math.Goldilocks
public import Qsag.Math.BinaryTower
public import Qsag.Oracle.Keccak
public import Qsag.Oracle.UcGames
public import Qsag.Protocol.Threshold.ThresholdApproval
public import Qsag.Protocol.Threshold.ThresholdMpc
public import Qsag.Protocol.Threshold.IdealTsig
import all Qsag.Oracle.UcGames
import all Qsag.Protocol.Threshold.ThresholdMpc

import Qsag.Tactic.AssuranceKit

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

/-- Complete, domain-separated WAL intent. There is no profile field in
    `SessionScheduleReq`; the version tag identifies this encoding, not a profile.
    `optRand` is included as supplied. No hash truncation discards message suffixes. -/
def encodeUcSigningRequest (req : SessionScheduleReq) : List UInt8 :=
  encodeMultiFrame ["QSAG.UC.SIGNING-REQUEST/v1".toUTF8.data.toList,
    leb128 req.sessionId, leb128 req.reqEpoch, req.msg, req.optRand,
    encodeMultiFrame (req.honestApprovers.map leb128)]

/-- Full public-key binding preimage. Including both components prevents a common
    32-byte seed from masking changes to the public root. Hash collision resistance
    remains an explicit obligation when the digest, rather than this preimage, is used. -/
def encodeUcPqPublicKey (pk : PqPublicKey) : List UInt8 :=
  encodeMultiFrame ["QSAG.UC.PQ-PUBLIC-KEY/v1".toUTF8.data.toList, pk.pkSeed, pk.pkRoot]

def ucPqPublicKeyDigest (pk : PqPublicKey) : List UInt8 :=
  shake256Xof 32 (encodeUcPqPublicKey pk)

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

/-- Simulator callback interface. Rounds 1 and 2 receive public request data and
    the simulation tape; Round 3 additionally receives the ideal signing result.
    There is no explicit secret-share argument. A callback can nevertheless capture
    secrets in its closure, so secret independence is a concrete-constructor proof
    obligation, not a consequence of this interface's type. -/
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
  /-- Legacy wire reconstruction callback. Its abort choice is observed, but its
      proposed success bytes are replaced by the ideal oracle result at delivery. -/
  simFinalizeCut  : PK → SessionScheduleReq → SimR3 → ByteArray →
                      List (Nat × ByteArray) → List (Nat × ByteArray) →
                      PSum AbortReason ByteArray

/-- The simulator controls delivery or abort, never the functionality's signature.
    The legacy callback's success payload is a wire-reconstruction proposal; it has no
    authority to replace the result returned by the ideal signing oracle. Both sequential
    and concurrent ideal executions use this boundary. -/
def BlackBoxUcSimulator.finalizeIdealCut {PK SimTape SimR1 SimR2 SimR3 : Type}
    (sim : BlackBoxUcSimulator PK SimTape SimR1 SimR2 SimR3)
    (pk : PK) (req : SessionScheduleReq) (st : SimR3) (idealSig : ByteArray)
    (honest corrupt : List (Nat × ByteArray)) : PSum AbortReason ByteArray :=
  match sim.simFinalizeCut pk req st idealSig honest corrupt with
  | .inl err => .inl err
  | .inr _ => .inr idealSig

/-- Successful delivery cannot substitute a simulator-chosen signature. -/
theorem BlackBoxUcSimulator.finalizeIdealCut_output
    {PK SimTape SimR1 SimR2 SimR3 : Type}
    (sim : BlackBoxUcSimulator PK SimTape SimR1 SimR2 SimR3)
    (pk : PK) (req : SessionScheduleReq) (st : SimR3) (idealSig out : ByteArray)
    (honest corrupt : List (Nat × ByteArray))
    (h : sim.finalizeIdealCut pk req st idealSig honest corrupt = .inr out) :
    out = idealSig := by
  unfold finalizeIdealCut at h
  cases hf : sim.simFinalizeCut pk req st idealSig honest corrupt with
  | inl err => rw [hf] at h; cases h
  | inr proposal => rw [hf] at h; cases h; rfl

/-- Output enforcement preserves every simulator-selected abort and its reason. -/
theorem BlackBoxUcSimulator.finalizeIdealCut_abort_iff
    {PK SimTape SimR1 SimR2 SimR3 : Type}
    (sim : BlackBoxUcSimulator PK SimTape SimR1 SimR2 SimR3)
    (pk : PK) (req : SessionScheduleReq) (st : SimR3) (idealSig : ByteArray)
    (honest corrupt : List (Nat × ByteArray)) (err : AbortReason) :
    sim.finalizeIdealCut pk req st idealSig honest corrupt = .inl err ↔
      sim.simFinalizeCut pk req st idealSig honest corrupt = .inl err := by
  unfold finalizeIdealCut
  cases hf : sim.simFinalizeCut pk req st idealSig honest corrupt with
  | inl reason => rfl
  | inr proposal => constructor <;> intro h <;> cases h

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
          match sim.finalizeIdealCut icl.tsig.pk req sR3 idealSigBytes honR3 corrR3 with
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
            cases sim.finalizeIdealCut _ _ _ _ _ _ <;> intro _ <;> exact List.mem_cons_self

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
            cases sim.finalizeIdealCut _ _ _ _ _ _ <;> rfl

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
              cases sim.finalizeIdealCut _ _ _ _ _ _ <;> exact hR3 _ _ _ _ _ _
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

/-- A released opening has an actual successful barrier execution on the recorded
request and Round-2 messages. This records the verifier equation, not a trusted
Boolean label attached by a caller. -/
def SessionBarrierJustified {PK ShareT SessionTape R1St R2St R3St : Type}
    (proto : InteractiveThresholdProtocol PK ShareT SessionTape R1St R2St R3St)
    (rec : SessionWireRecord) : Prop :=
  rec.honestRound3 ≠ [] → ∃ (pk : PK) (r2 : R2St) (r3 : R3St),
    proto.preCutBarrier pk rec.request r2 rec.honestRound2 rec.corruptRound2 = .inr r3

theorem execRealSession_opening_has_barrier_witness
    {PK ShareT SessionTape R1St R2St R3St AdvState : Type}
    (proto : InteractiveThresholdProtocol PK ShareT SessionTape R1St R2St R3St)
    (A : UcRushingAdversary AdvState) (cl : RealClusterState PK ShareT)
    (advSt : AdvState) (tape : SessionTape) :
    SessionBarrierJustified proto (execRealSession proto A cl advSt tape).2.2 := by
  unfold SessionBarrierJustified execRealSession
  dsimp only
  cases validThresholdApproval cl.tsig (A.scheduleSession advSt).1.honestApprovers
  · intro h; exact False.elim (h rfl)
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases walPreSignStep cl.honestWal _ _ _ with
    | err _ _ => intro h; exact False.elim (h rfl)
    | ok _ auth =>
      cases auth with
      | replayCached _ => intro h; exact False.elim (h rfl)
      | authorizedFresh _ =>
        dsimp only
        cases proto.verifyRound1 _ _ _ _ _ with
        | inl _ => intro h; exact False.elim (h rfl)
        | inr _ =>
          dsimp only
          cases hb : proto.preCutBarrier _ _ _ _ _ with
          | inl _ => intro h; exact False.elim (h rfl)
          | inr r3 =>
            dsimp only
            cases proto.finalizeCutOpen _ _ _ _ _ <;> intro _ <;>
              exact ⟨cl.tsig.pk, _, r3, hb⟩

/-- Every opening in every adaptively scheduled session is justified by the
actual pre-cut verifier. Replayed signatures expose no new Round-3 messages. -/
theorem RealProtocolExec_openings_have_barrier_witnesses
    {PK ShareT SessionTape R1St R2St R3St AdvState : Type}
    (proto : InteractiveThresholdProtocol PK ShareT SessionTape R1St R2St R3St)
    (A : UcRushingAdversary AdvState) (numSessions : Nat)
    (tapes : Nat → SessionTape) (cl : RealClusterState PK ShareT) (advSt : AdvState) :
    ∀ rec ∈ (RealProtocolExec proto A numSessions tapes cl advSt).2.sessions,
      SessionBarrierJustified proto rec := by
  induction numSessions generalizing tapes cl advSt with
  | zero => intro rec h; cases h
  | succ n ih =>
    rw [RealProtocolExec_succ]
    dsimp only
    intro rec h
    rcases List.mem_cons.mp h with he | hr
    · subst rec
      exact execRealSession_opening_has_barrier_witness proto A cl advSt (tapes 0)
    · exact ih _ _ _ rec hr


/-- A nonempty enrolled custody vault can consume a real mask slot. -/
theorem witness_custody_mask_consumption :
    ∃ (v v' : HonestCustodyVault Nat) (out : Nat),
      consumeVaultMaskSlot v (fun cursor share => cursor + share) = some (out, v') := by
  exact ⟨enrollHonestVault 1 [1] 7,
    { enrollHonestVault 1 [1] 7 with maskSessionCursor := 1 }, 7, rfl⟩

theorem tooth_quarantined_mask_consumption (v v' : HonestCustodyVault Nat) (out : Nat) :
    consumeVaultMaskSlot (walPoisonVault v) (fun cursor share => cursor + share) ≠ some (out, v') := by
  simp [consumeVaultMaskSlot, walPoisonVault, walQuarantine]

#tooth_pair Qsag.consumeVaultMaskSlot_strictly_advances vs Qsag.tooth_quarantined_mask_consumption
#verify_inhabited Qsag.consumeVaultMaskSlot_strictly_advances Qsag.witness_custody_mask_consumption

/-- Production threshold signing oracle, using the Rust-exact MPC signer. -/
def productionThresholdSignOracle (suite : TweakableHashSuite) (params : PqHashParams)
    (o : ProductionPqHashMpcOracles) (pkSeed : List UInt8) (grindLimit : Nat)
    (ser : Option PqHashSig → ByteArray) : SessionScheduleReq → ByteArray :=
  fun req => ser (mpcEvalProductionStatelessSign suite params o pkSeed req.msg req.optRand grindLimit)

theorem productionThresholdSignOracle_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (o : ProductionPqHashMpcOracles) (sk : PqSecretKey) (hm : o.MatchesKey suite sk)
    (grindLimit : Nat) (ser : Option PqHashSig → ByteArray) :
    productionThresholdSignOracle suite params o sk.pkSeed grindLimit ser =
      fun req => ser (evalProductionStatelessSign suite params sk req.msg req.optRand grindLimit) := by
  funext req
  exact congrArg ser (thresholdProductionStatelessSign_eq_evalProductionStatelessSign
    suite params o sk hm req.msg req.optRand grindLimit)

/-- The production reduction reads its query log from actual Round-3 requests. -/
def productionTranscriptQueries {AdvState : Type} (grindLimit : Nat)
    (tr : ExecTranscript AdvState) : List ProdSigningQuery :=
  (tr.sessions.filter (fun rec => !rec.honestRound3.isEmpty)).map
    (fun rec => ⟨rec.request.msg, rec.request.optRand, rec.request.reqEpoch, grindLimit⟩)

def productionForgeryWins {AdvState : Type} (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (forgeOut : ExecTranscript AdvState → List UInt8 × PqHashSig)
    (tr : ExecTranscript AdvState) : Bool :=
  verifyProductionPqHashSig suite params pk (forgeOut tr).1 (forgeOut tr).2 &&
  tr.sessions.all (fun rec => rec.honestRound3.isEmpty || decide (rec.request.msg ≠ (forgeOut tr).1))

def ProductionTranscriptBreak {AdvState : Type} (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) (grindLimit : Nat)
    (forgeOut : ExecTranscript AdvState → List UInt8 × PqHashSig)
    (tr : ExecTranscript AdvState) : Prop :=
  let log := productionSigningLog suite params sk (productionTranscriptQueries grindLimit tr)
  ProdForsItsrBreak suite params (derivePublicKey suite params sk) log (forgeOut tr).1 (forgeOut tr).2 ∨
    ProdSmTcrBreak suite params sk log ∨
    ProdPreimageBreak suite params sk log (forgeOut tr).1 (forgeOut tr).2

theorem productionForgeryBreak_of_wins {AdvState : Type}
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey) (grindLimit : Nat)
    (hw : params.w = 4 ∨ params.w = 16) (hStateless : params.statefulJorts = false)
    (forgeOut : ExecTranscript AdvState → List UInt8 × PqHashSig) (tr : ExecTranscript AdvState)
    (hWin : productionForgeryWins suite params (derivePublicKey suite params sk) forgeOut tr = true) :
    ProductionTranscriptBreak suite params sk grindLimit forgeOut tr := by
  have hwins := Bool.and_eq_true_iff.mp hWin
  apply production_stateless_forgery_break suite params sk
    (productionTranscriptQueries grindLimit tr) (forgeOut tr).1 (forgeOut tr).2 hw hStateless
  · intro e he
    obtain ⟨q, hq, heq, _⟩ := productionSigningLog_generated suite params sk _ e he
    obtain ⟨rec, hrec, hqeq⟩ := List.mem_map.mp hq
    obtain ⟨hm, hr3⟩ := List.mem_filter.mp hrec
    have hf := List.all_eq_true.mp hwins.2 rec hm
    have hn : rec.honestRound3.isEmpty = false := by
      cases hh : rec.honestRound3.isEmpty
      · rfl
      · rw [hh] at hr3; cases hr3
    rw [hn, Bool.false_or] at hf
    rw [heq, ← hqeq]
    exact of_decide_eq_true hf
  · exact hwins.1

/-- UC transfer for the production verifier and the threshold production signing oracle.
The emulation bound remains an explicit premise; the oracle equality is discharged by
`ThresholdMpc`, and hash-game extraction uses the production verifier directly. -/
theorem uc_production_threshold_forgery_transfer
    {PK ShareT SessionTape R1St R2St R3St SimTape SimR1 SimR2 SimR3 AdvState : Type}
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (o : ProductionPqHashMpcOracles) (hm : o.MatchesKey suite sk)
    (grindLimit : Nat) (ser : Option PqHashSig → ByteArray)
    (hw : params.w = 4 ∨ params.w = 16) (hStateless : params.statefulJorts = false)
    (proto : InteractiveThresholdProtocol PK ShareT SessionTape R1St R2St R3St)
    (sim : BlackBoxUcSimulator PK SimTape SimR1 SimR2 SimR3)
    (A : UcRushingAdversary AdvState) (Q_s card : Nat)
    (realTapes : Fin card → Nat → SessionTape) (simTapes : Fin card → Nat → SimTape)
    (cl : RealClusterState PK ShareT) (icl : IdealClusterState PK) (advSt : AdvState)
    (forgeOut : ExecTranscript AdvState → List UInt8 × PqHashSig) (eps : Nat × Nat)
    (hUc : ratLe (rationalAcceptDiff card
      (fun ω => (RealProtocolExec proto A Q_s (realTapes ω) cl advSt).2) card
      (fun ω => (IdealFunctionalityExec
        (productionThresholdSignOracle suite params o sk.pkSeed grindLimit ser)
        sim A Q_s (simTapes ω) icl advSt).2)
      (productionForgeryWins suite params (derivePublicKey suite params sk) forgeOut)) eps) :
    let oracle := productionThresholdSignOracle suite params o sk.pkSeed grindLimit ser
    let win := productionForgeryWins suite params (derivePublicKey suite params sk) forgeOut
    let realView := fun ω => (RealProtocolExec proto A Q_s (realTapes ω) cl advSt).2
    let idealView := fun ω => (IdealFunctionalityExec oracle sim A Q_s (simTapes ω) icl advSt).2
    (oracle = fun req => ser (evalProductionStatelessSign suite params sk req.msg req.optRand grindLimit)) ∧
    distAcceptCount card realView win * eps.2 ≤
      distAcceptCount card idealView win * eps.2 + eps.1 * card ∧
    (∀ ω : Fin card, win (idealView ω) = true →
      ProductionTranscriptBreak suite params sk grindLimit forgeOut (idealView ω)) := by
  intro oracle win realView idealView
  exact ⟨productionThresholdSignOracle_eq suite params o sk hm grindLimit ser,
    forgery_count_transfer card realView idealView win eps hUc,
    fun ω h => productionForgeryBreak_of_wins suite params sk grindLimit hw hStateless
      forgeOut (idealView ω) h⟩

/-! ## 7. Concurrently Interleaved Multi-Session UC Execution & Hybrid Reduction -/

/-- Domain-separating concurrent session identifier. -/
abbrev SessionId := Nat

/-- Adversary-driven concurrent round-interleaving command across live sessions. -/
inductive ConcurrentScheduleStep where
  | startRound1 (req : SessionScheduleReq)
  | stepRound2  (sid : SessionId)
  | stepRound3  (sid : SessionId)
  deriving DecidableEq, Repr

/-- Arbitrary stateful rushing adversary interleaving Round 1 / Round 2 / Round 3 steps
    across up to `Q_s` live concurrent threshold signing sessions. -/
structure ConcurrentUcAdversary (AdvState : Type) where
  chooseNextStep : AdvState → ConcurrentScheduleStep × AdvState
  rushRound1     : AdvState → SessionId → List (Nat × ByteArray) → (Nat → ByteArray) × AdvState
  rushRound2     : AdvState → SessionId → List (Nat × ByteArray) → (Nat → ByteArray) × AdvState
  rushRound3     : AdvState → SessionId → List (Nat × ByteArray) → (Nat → ByteArray) × AdvState
  observeOutcome : AdvState → SessionId → SessionOutcome → AdvState

/-- Per-slot phase state for concurrently interleaved sessions. -/
inductive ConcurrentSlotPhase (SlotR2 SlotR3 : Type) where
  | unallocated
  | afterR1 (ep : Nat) (msgDig : List UInt8) (req : SessionScheduleReq)
      (honR1 corrR1 : List (Nat × ByteArray)) (r2St : SlotR2)
  | afterR2 (ep : Nat) (msgDig : List UInt8) (req : SessionScheduleReq)
      (honR1 corrR1 honR2 corrR2 : List (Nat × ByteArray)) (r3St : SlotR3)
  | closed

/-- Update slot `idx` in a `Q_s`-slot table. -/
def updateConcurrentSlot {Q_s : Nat} {α : Type}
    (slots : Fin Q_s → α) (idx : Fin Q_s) (v : α) : Fin Q_s → α :=
  fun j => if j = idx then v else slots j

theorem updateConcurrentSlot_same {Q_s : Nat} {α : Type}
    (slots : Fin Q_s → α) (idx : Fin Q_s) (v : α) :
    updateConcurrentSlot slots idx v idx = v := by
  unfold updateConcurrentSlot
  rw [ite_eq_left rfl]

theorem updateConcurrentSlot_ne {Q_s : Nat} {α : Type}
    (slots : Fin Q_s → α) (idx j : Fin Q_s) (v : α) (hNe : j ≠ idx) :
    updateConcurrentSlot slots idx v j = slots j := by
  unfold updateConcurrentSlot
  rw [ite_eq_right hNe]

/-- Look up the allocated slot for `sid` in `sidMap`. -/
def lookupSidSlot {Q_s : Nat} (sid : SessionId) : List (SessionId × Fin Q_s) → Option (Fin Q_s)
  | [] => none
  | (s, slot) :: rest => if s = sid then some slot else lookupSidSlot sid rest

/-- Polymorphic slot handler unifying real, ideal, and `h`-hybrid concurrent execution. -/
structure ConcurrentSlotEngine (PK : Type) (Q_s : Nat) (SlotR1 SlotR2 SlotR3 : Type) where
  pkDigestOf   : PK → List UInt8
  msgDigestOf  : SessionScheduleReq → List UInt8
  slotRound1   : Fin Q_s → PK → List Nat → SessionScheduleReq → Nat →
                   List (Nat × ByteArray) × SlotR1
  slotVerify1  : Fin Q_s → PK → SessionScheduleReq → SlotR1 →
                   List (Nat × ByteArray) → List (Nat × ByteArray) →
                   PSum (AbortReason × Bool) SlotR2
  slotRound2   : Fin Q_s → PK → List Nat → SessionScheduleReq → SlotR2 →
                   List (Nat × ByteArray) × SlotR2
  slotPreCut   : Fin Q_s → PK → SessionScheduleReq → SlotR2 →
                   List (Nat × ByteArray) → List (Nat × ByteArray) →
                   PSum AbortReason SlotR3
  slotRound3   : Fin Q_s → PK → List Nat → SessionScheduleReq → SlotR3 →
                   List (Nat × ByteArray) × SlotR3
  slotFinalize : Fin Q_s → PK → SessionScheduleReq → SlotR3 →
                   List (Nat × ByteArray) → List (Nat × ByteArray) →
                   PSum AbortReason ByteArray

/-- Live concurrent cluster + session table state. -/
structure ConcurrentExecState (PK : Type) (Q_s : Nat) (SlotR2 SlotR3 : Type) where
  tsig              : IdealTsigState PK (List UInt8)
  honestWal         : WalLatchState
  maskSessionCursor : Nat
  seenSids          : List SessionId
  allocatedSlots    : Nat
  sidMap            : List (SessionId × Fin Q_s)
  slots             : Fin Q_s → ConcurrentSlotPhase SlotR2 SlotR3
  completed         : List SessionWireRecord

def initConcurrentExecState {PK : Type} (Q_s : Nat) (SlotR2 SlotR3 : Type)
    (tsig : IdealTsigState PK (List UInt8)) (wal : WalLatchState) (cursor : Nat) :
    ConcurrentExecState PK Q_s SlotR2 SlotR3 :=
  { tsig              := tsig
    honestWal         := wal
    maskSessionCursor := cursor
    seenSids          := []
    allocatedSlots    := 0
    sidMap            := []
    slots             := fun _ => .unallocated
    completed         := [] }

/-- Execute one adversary-scheduled concurrent round step with mandatory unique `SessionId`
    domain separation, cross-session quarantine, and pre-cut consistency barrier. -/
def execConcurrentStep {PK SlotR1 SlotR2 SlotR3 AdvState : Type} {Q_s : Nat}
    (eng : ConcurrentSlotEngine PK Q_s SlotR1 SlotR2 SlotR3)
    (A : ConcurrentUcAdversary AdvState)
    (st : ConcurrentExecState PK Q_s SlotR2 SlotR3) (advSt : AdvState) :
    ConcurrentExecState PK Q_s SlotR2 SlotR3 × AdvState :=
  let (cmd, advSt1) := A.chooseNextStep advSt
  match cmd with
  | .startRound1 req =>
    if decide (req.sessionId ∈ st.seenSids) then
      -- Domain-separation gate: duplicate `SessionId`s are rejected immediately.
      (st, A.observeOutcome advSt1 req.sessionId (.abort .walEpochRejected))
    else
      let seen' := req.sessionId :: st.seenSids
      if hSlot : st.allocatedSlots < Q_s then
        if !(validThresholdApproval st.tsig req.honestApprovers) then
          let out := SessionOutcome.abort .quorumRejected
          let wireRec : SessionWireRecord := ⟨req, [], [], [], [], [], [], out⟩
          ({ st with seenSids := seen', completed := wireRec :: st.completed },
           A.observeOutcome advSt1 req.sessionId out)
        else
          let pkDig := eng.pkDigestOf st.tsig.pk
          let msgDig := eng.msgDigestOf req
          match walPreSignStep st.honestWal pkDig req.reqEpoch msgDig with
          | .err wal' rej =>
            let out := SessionOutcome.abort (mapWalRejectReason rej)
            let wireRec : SessionWireRecord := ⟨req, [], [], [], [], [], [], out⟩
            ({ st with honestWal := wal', seenSids := seen', completed := wireRec :: st.completed },
             A.observeOutcome advSt1 req.sessionId out)
          | .ok wal' auth =>
            match auth with
            | .replayCached cachedSig =>
              let out := SessionOutcome.signOk cachedSig
              let wireRec : SessionWireRecord := ⟨req, [], [], [], [], [], [], out⟩
              ({ st with honestWal := wal', seenSids := seen', completed := wireRec :: st.completed },
               A.observeOutcome advSt1 req.sessionId out)
            | .authorizedFresh ep =>
              let slot : Fin Q_s := ⟨st.allocatedSlots, hSlot⟩
              let cursorUsed := st.maskSessionCursor
              let walReserved : WalLatchState := { wal' with nextEpoch := ep + 1 }
              let (honR1, r1St) :=
                eng.slotRound1 slot st.tsig.pk st.tsig.corruptParties req cursorUsed
              let (corrR1Fn, advSt2) := A.rushRound1 advSt1 req.sessionId honR1
              let corrR1 := st.tsig.corruptParties.map (fun c => (c, corrR1Fn c))
              match eng.slotVerify1 slot st.tsig.pk req r1St honR1 corrR1 with
              | .inl errPair =>
                let r1Err := errPair.1
                let doPoison := errPair.2
                let walF := if doPoison then walQuarantine walReserved else walReserved
                let out := SessionOutcome.abort r1Err
                let wireRec : SessionWireRecord := ⟨req, honR1, corrR1, [], [], [], [], out⟩
                ({ st with
                    honestWal := walF
                    maskSessionCursor := cursorUsed + 1
                    seenSids := seen'
                    allocatedSlots := st.allocatedSlots + 1
                    completed := wireRec :: st.completed },
                 A.observeOutcome advSt2 req.sessionId out)
              | .inr r2Init =>
                ({ st with
                    honestWal := walReserved
                    maskSessionCursor := cursorUsed + 1
                    seenSids := seen'
                    allocatedSlots := st.allocatedSlots + 1
                    sidMap := (req.sessionId, slot) :: st.sidMap
                    slots := updateConcurrentSlot st.slots slot
                      (.afterR1 ep msgDig req honR1 corrR1 r2Init) },
                 advSt2)
      else
        let out := SessionOutcome.abort .quorumRejected
        let wireRec : SessionWireRecord := ⟨req, [], [], [], [], [], [], out⟩
        ({ st with seenSids := seen', completed := wireRec :: st.completed },
         A.observeOutcome advSt1 req.sessionId out)
  | .stepRound2 sid =>
    match lookupSidSlot sid st.sidMap with
    | none => (st, A.observeOutcome advSt1 sid (.abort .walEpochRejected))
    | some slot =>
      match st.slots slot with
      | .unallocated => (st, A.observeOutcome advSt1 sid (.abort .walEpochRejected))
      | .afterR2 _ _ _ _ _ _ _ _ => (st, A.observeOutcome advSt1 sid (.abort .walEpochRejected))
      | .closed => (st, A.observeOutcome advSt1 sid (.abort .walEpochRejected))
      | .afterR1 ep msgDig req honR1 corrR1 r2Init =>
        if st.honestWal.poisoned then
          let out := SessionOutcome.abort .walPoisoned
          let wireRec : SessionWireRecord := ⟨req, honR1, corrR1, [], [], [], [], out⟩
          ({ st with
              slots := updateConcurrentSlot st.slots slot .closed
              completed := wireRec :: st.completed },
           A.observeOutcome advSt1 sid out)
        else
          let (honR2, r2St) :=
            eng.slotRound2 slot st.tsig.pk st.tsig.corruptParties req r2Init
          let (corrR2Fn, advSt2) := A.rushRound2 advSt1 sid honR2
          let corrR2 := st.tsig.corruptParties.map (fun c => (c, corrR2Fn c))
          match eng.slotPreCut slot st.tsig.pk req r2St honR2 corrR2 with
          | .inl barrierErr =>
            let out := SessionOutcome.abort barrierErr
            let wireRec : SessionWireRecord := ⟨req, honR1, corrR1, honR2, corrR2, [], [], out⟩
            ({ st with
                honestWal := walQuarantine st.honestWal
                slots := updateConcurrentSlot st.slots slot .closed
                completed := wireRec :: st.completed },
             A.observeOutcome advSt2 sid out)
          | .inr r3Init =>
            ({ st with
                tsig := { st.tsig with approvedMsgs := req.msg :: st.tsig.approvedMsgs }
                slots := updateConcurrentSlot st.slots slot
                  (.afterR2 ep msgDig req honR1 corrR1 honR2 corrR2 r3Init) },
             advSt2)
  | .stepRound3 sid =>
    match lookupSidSlot sid st.sidMap with
    | none => (st, A.observeOutcome advSt1 sid (.abort .walEpochRejected))
    | some slot =>
      match st.slots slot with
      | .unallocated => (st, A.observeOutcome advSt1 sid (.abort .walEpochRejected))
      | .afterR1 _ _ _ _ _ _ => (st, A.observeOutcome advSt1 sid (.abort .walEpochRejected))
      | .closed => (st, A.observeOutcome advSt1 sid (.abort .walEpochRejected))
      | .afterR2 ep msgDig req honR1 corrR1 honR2 corrR2 r3Init =>
        if st.honestWal.poisoned then
          let out := SessionOutcome.abort .walPoisoned
          let wireRec : SessionWireRecord := ⟨req, honR1, corrR1, honR2, corrR2, [], [], out⟩
          ({ st with
              slots := updateConcurrentSlot st.slots slot .closed
              completed := wireRec :: st.completed },
           A.observeOutcome advSt1 sid out)
        else
          let (honR3, r3St) :=
            eng.slotRound3 slot st.tsig.pk st.tsig.corruptParties req r3Init
          let (corrR3Fn, advSt2) := A.rushRound3 advSt1 sid honR3
          let corrR3 := st.tsig.corruptParties.map (fun c => (c, corrR3Fn c))
          match eng.slotFinalize slot st.tsig.pk req r3St honR3 corrR3 with
          | .inl cutErr =>
            let out := SessionOutcome.abort cutErr
            let wireRec : SessionWireRecord := ⟨req, honR1, corrR1, honR2, corrR2, honR3, corrR3, out⟩
            ({ st with
                honestWal := walQuarantine st.honestWal
                slots := updateConcurrentSlot st.slots slot .closed
                completed := wireRec :: st.completed },
             A.observeOutcome advSt2 sid out)
          | .inr sigBytes =>
            let committedWal : WalLatchState :=
              { st.honestWal with
                nextEpoch := Nat.max st.honestWal.nextEpoch (ep + 1)
                latchedRecord := some (ep, msgDig, sigBytes) }
            let out := SessionOutcome.signOk sigBytes
            let wireRec : SessionWireRecord := ⟨req, honR1, corrR1, honR2, corrR2, honR3, corrR3, out⟩
            ({ st with
                honestWal := committedWal
                slots := updateConcurrentSlot st.slots slot .closed
                completed := wireRec :: st.completed },
             A.observeOutcome advSt2 sid out)

/-- Run `numSteps` arbitrarily interleaved concurrent round transitions. -/
def execConcurrentSteps {PK SlotR1 SlotR2 SlotR3 AdvState : Type} {Q_s : Nat}
    (eng : ConcurrentSlotEngine PK Q_s SlotR1 SlotR2 SlotR3)
    (A : ConcurrentUcAdversary AdvState) :
    (numSteps : Nat) → ConcurrentExecState PK Q_s SlotR2 SlotR3 → AdvState →
    ConcurrentExecState PK Q_s SlotR2 SlotR3 × ExecTranscript AdvState
  | 0, st, advSt => (st, ⟨advSt, st.completed⟩)
  | n + 1, st, advSt =>
    let (st1, advSt1) := execConcurrentStep eng A st advSt
    execConcurrentSteps eng A n st1 advSt1

/-- Real-world `ConcurrentSlotEngine` running `proto` on `realTapes slot`. -/
def realConcurrentEngine {PK ShareT SessionTape R1St R2St R3St : Type} {Q_s : Nat}
    (proto : InteractiveThresholdProtocol PK ShareT SessionTape R1St R2St R3St)
    (honestShares : Nat → Option ShareT)
    (realTapes : Fin Q_s → SessionTape) :
    ConcurrentSlotEngine PK Q_s R1St R2St R3St :=
  { pkDigestOf   := proto.pkDigestOf
    msgDigestOf  := proto.msgDigestOf
    slotRound1   := fun j pk corr req cur =>
      proto.honestRound1 pk corr req cur honestShares (realTapes j)
    slotVerify1  := fun _ pk req r1 h1 c1 => proto.verifyRound1 pk req r1 h1 c1
    slotRound2   := fun j pk corr req r2 =>
      proto.honestRound2 pk corr req r2 honestShares (realTapes j)
    slotPreCut   := fun _ pk req r2 h2 c2 => proto.preCutBarrier pk req r2 h2 c2
    slotRound3   := fun j pk corr req r3 =>
      proto.honestRound3 pk corr req r3 honestShares (realTapes j)
    slotFinalize := fun _ pk req r3 h3 c3 => proto.finalizeCutOpen pk req r3 h3 c3 }

/-- Ideal-world `sk`-free `ConcurrentSlotEngine` running `sim` on `simTapes slot` and querying
    `idealSignOracle` strictly after `simPreCutBarrier` passes. -/
def idealConcurrentEngine {PK SimTape SimR1 SimR2 SimR3 : Type} {Q_s : Nat}
    (idealSignOracle : SessionScheduleReq → ByteArray)
    (sim : BlackBoxUcSimulator PK SimTape SimR1 SimR2 SimR3)
    (simTapes : Fin Q_s → SimTape) :
    ConcurrentSlotEngine PK Q_s SimR1 SimR2 (SimR3 × ByteArray) :=
  { pkDigestOf   := sim.pkDigestOf
    msgDigestOf  := sim.msgDigestOf
    slotRound1   := fun j pk corr req cur =>
      sim.simRound1 pk corr req cur (simTapes j)
    slotVerify1  := fun _ pk req s1 h1 c1 => sim.simVerifyRound1 pk req s1 h1 c1
    slotRound2   := fun j pk corr req s2 =>
      sim.simRound2 pk corr req s2 (simTapes j)
    slotPreCut   := fun _ pk req s2 h2 c2 =>
      match sim.simPreCutBarrier pk req s2 h2 c2 with
      | .inl err => .inl err
      | .inr s3  => .inr (s3, idealSignOracle req)
    slotRound3   := fun j pk corr req s3Pair =>
      let (honR3, s3') := sim.simRound3 pk corr req s3Pair.1 s3Pair.2 (simTapes j)
      (honR3, (s3', s3Pair.2))
    slotFinalize := fun _ pk req s3Pair h3 c3 =>
      sim.finalizeIdealCut pk req s3Pair.1 s3Pair.2 h3 c3 }

/-- `h`-Hybrid `ConcurrentSlotEngine`: slots `< h` run `sim`, slots `≥ h` run `proto`. -/
def hybridConcurrentEngine {PK ShareT SessionTape R1St R2St R3St SimTape SimR1 SimR2 SimR3 : Type}
    {Q_s : Nat} (h : Nat)
    (proto : InteractiveThresholdProtocol PK ShareT SessionTape R1St R2St R3St)
    (honestShares : Nat → Option ShareT)
    (idealSignOracle : SessionScheduleReq → ByteArray)
    (sim : BlackBoxUcSimulator PK SimTape SimR1 SimR2 SimR3)
    (realTapes : Fin Q_s → SessionTape) (simTapes : Fin Q_s → SimTape) :
    ConcurrentSlotEngine PK Q_s
      (PSum R1St SimR1) (PSum R2St SimR2) (PSum R3St (SimR3 × ByteArray)) :=
  { pkDigestOf   := proto.pkDigestOf
    msgDigestOf  := proto.msgDigestOf
    slotRound1   := fun j pk corr req cur =>
      if j.val < h then
        let (w, s1) := sim.simRound1 pk corr req cur (simTapes j)
        (w, .inr s1)
      else
        let (w, r1) := proto.honestRound1 pk corr req cur honestShares (realTapes j)
        (w, .inl r1)
    slotVerify1  := fun _ pk req st1 h1 c1 =>
      match st1 with
      | .inl r1 =>
        match proto.verifyRound1 pk req r1 h1 c1 with
        | .inl err => .inl err
        | .inr r2  => .inr (.inl r2)
      | .inr s1 =>
        match sim.simVerifyRound1 pk req s1 h1 c1 with
        | .inl err => .inl err
        | .inr s2  => .inr (.inr s2)
    slotRound2   := fun j pk corr req st2 =>
      match st2 with
      | .inl r2 =>
        let (w, r2') := proto.honestRound2 pk corr req r2 honestShares (realTapes j)
        (w, .inl r2')
      | .inr s2 =>
        let (w, s2') := sim.simRound2 pk corr req s2 (simTapes j)
        (w, .inr s2')
    slotPreCut   := fun _ pk req st2 h2 c2 =>
      match st2 with
      | .inl r2 =>
        match proto.preCutBarrier pk req r2 h2 c2 with
        | .inl err => .inl err
        | .inr r3  => .inr (.inl r3)
      | .inr s2 =>
        match sim.simPreCutBarrier pk req s2 h2 c2 with
        | .inl err => .inl err
        | .inr s3  => .inr (.inr (s3, idealSignOracle req))
    slotRound3   := fun j pk corr req st3 =>
      match st3 with
      | .inl r3 =>
        let (w, r3') := proto.honestRound3 pk corr req r3 honestShares (realTapes j)
        (w, .inl r3')
      | .inr s3Pair =>
        let (w, s3') := sim.simRound3 pk corr req s3Pair.1 s3Pair.2 (simTapes j)
        (w, .inr (s3', s3Pair.2))
    slotFinalize := fun _ pk req st3 h3 c3 =>
      match st3 with
      | .inl r3 => proto.finalizeCutOpen pk req r3 h3 c3
      | .inr s3Pair => sim.finalizeIdealCut pk req s3Pair.1 s3Pair.2 h3 c3 }

/-- **Concurrently Interleaved Real-World Protocol Execution (`ConcurrentProtocolExec`)**:
    Adversary `A` arbitrarily interleaves Round 1 / Round 2 / Round 3 steps across up to `Q_s`
    live sessions keyed by `SessionId` over `numSteps` scheduling steps. -/
def ConcurrentProtocolExec {PK ShareT SessionTape R1St R2St R3St AdvState : Type}
    (proto : InteractiveThresholdProtocol PK ShareT SessionTape R1St R2St R3St)
    (A : ConcurrentUcAdversary AdvState) (Q_s numSteps : Nat)
    (realTapes : Fin Q_s → SessionTape)
    (cl : RealClusterState PK ShareT) (advSt : AdvState) :
    RealClusterState PK ShareT × ExecTranscript AdvState :=
  let eng := realConcurrentEngine proto cl.honestShares realTapes
  let st0 := initConcurrentExecState Q_s R2St R3St cl.tsig cl.honestWal cl.maskSessionCursor
  let (stF, tr) := execConcurrentSteps eng A numSteps st0 advSt
  let sharesF := if stF.honestWal.poisoned && !cl.honestWal.poisoned then (fun _ => none) else cl.honestShares
  ({ tsig := stF.tsig
     honestWal := stF.honestWal
     maskSessionCursor := stF.maskSessionCursor
     honestShares := sharesF }, tr)

/-- **Concurrently Interleaved Ideal-World Execution (`ConcurrentIdealExec`)**:
    Strictly `sk`-free black-box `Sim` coupled to `idealSignOracle` across up to `Q_s` live
    concurrently interleaved sessions. -/
def ConcurrentIdealExec {PK SimTape SimR1 SimR2 SimR3 AdvState : Type}
    (idealSignOracle : SessionScheduleReq → ByteArray)
    (sim : BlackBoxUcSimulator PK SimTape SimR1 SimR2 SimR3)
    (A : ConcurrentUcAdversary AdvState) (Q_s numSteps : Nat)
    (simTapes : Fin Q_s → SimTape)
    (icl : IdealClusterState PK) (advSt : AdvState) :
    IdealClusterState PK × ExecTranscript AdvState :=
  let eng := idealConcurrentEngine idealSignOracle sim simTapes
  let st0 := initConcurrentExecState Q_s SimR2 (SimR3 × ByteArray)
    icl.tsig icl.honestWal icl.maskSessionCursor
  let (stF, tr) := execConcurrentSteps eng A numSteps st0 advSt
  ({ tsig := stF.tsig
     honestWal := stF.honestWal
     maskSessionCursor := stF.maskSessionCursor }, tr)

/-- **`h`-Hybrid Concurrent Execution (`ConcurrentHybridExec`)**:
    Slots `< h` execute `sim` on `simTapes`; slots `≥ h` execute `proto` on `realTapes`. -/
def ConcurrentHybridExec
    {PK ShareT SessionTape R1St R2St R3St SimTape SimR1 SimR2 SimR3 AdvState : Type}
    (h : Nat)
    (proto : InteractiveThresholdProtocol PK ShareT SessionTape R1St R2St R3St)
    (idealSignOracle : SessionScheduleReq → ByteArray)
    (sim : BlackBoxUcSimulator PK SimTape SimR1 SimR2 SimR3)
    (A : ConcurrentUcAdversary AdvState) (Q_s numSteps : Nat)
    (realTapes : Fin Q_s → SessionTape) (simTapes : Fin Q_s → SimTape)
    (cl : RealClusterState PK ShareT) (advSt : AdvState) :
    ExecTranscript AdvState :=
  let eng := hybridConcurrentEngine h proto cl.honestShares idealSignOracle sim realTapes simTapes
  let st0 := initConcurrentExecState Q_s (PSum R2St SimR2) (PSum R3St (SimR3 × ByteArray))
    cl.tsig cl.honestWal cl.maskSessionCursor
  (execConcurrentSteps eng A numSteps st0 advSt).2

private def slotPhaseSid {SlotR2 SlotR3 : Type} : ConcurrentSlotPhase SlotR2 SlotR3 → Option SessionId
  | .unallocated => none
  | .afterR1 _ _ req _ _ _ => some req.sessionId
  | .afterR2 _ _ req _ _ _ _ _ => some req.sessionId
  | .closed => none

private def ConcurrentSidInvariant {PK SlotR2 SlotR3 : Type} {Q_s : Nat}
    (st : ConcurrentExecState PK Q_s SlotR2 SlotR3) : Prop :=
  (st.completed.map (fun r => r.request.sessionId)).Nodup ∧
  (∀ r ∈ st.completed, r.request.sessionId ∈ st.seenSids) ∧
  (∀ (j : Fin Q_s) (sid : SessionId), slotPhaseSid (st.slots j) = some sid →
    sid ∈ st.seenSids ∧
    (∀ r ∈ st.completed, r.request.sessionId ≠ sid) ∧
    (∀ k : Fin Q_s, k ≠ j → slotPhaseSid (st.slots k) ≠ some sid)) ∧
  (∀ j : Fin Q_s, st.allocatedSlots ≤ j.val → st.slots j = .unallocated)

private theorem execConcurrentStep_preserves_sidInvariant
    {PK SlotR1 SlotR2 SlotR3 AdvState : Type} {Q_s : Nat}
    (eng : ConcurrentSlotEngine PK Q_s SlotR1 SlotR2 SlotR3)
    (A : ConcurrentUcAdversary AdvState)
    (st : ConcurrentExecState PK Q_s SlotR2 SlotR3) (advSt : AdvState)
    (hInv : ConcurrentSidInvariant st) :
    ConcurrentSidInvariant (execConcurrentStep eng A st advSt).1 := by
  obtain ⟨hNodup, hCompSeen, hSlotInv, hUnalloc⟩ := hInv
  unfold execConcurrentStep
  dsimp only
  cases (A.chooseNextStep advSt).1 with
  | startRound1 req =>
    dsimp only
    by_cases hSeen : req.sessionId ∈ st.seenSids
    · rw [ite_eq_left (decide_eq_true hSeen)]
      exact ⟨hNodup, hCompSeen, hSlotInv, hUnalloc⟩
    · rw [ite_eq_right (fun h => hSeen (of_decide_eq_true h))]
      have hPushComp : ∀ (wal' : WalLatchState) (cur' alloc' : Nat)
          (wRec : SessionWireRecord), wRec.request = req → st.allocatedSlots ≤ alloc' →
          ConcurrentSidInvariant
            { st with
              honestWal := wal'
              maskSessionCursor := cur'
              seenSids := req.sessionId :: st.seenSids
              allocatedSlots := alloc'
              completed := wRec :: st.completed } := by
        intro wal' cur' alloc' wRec hRecReq hAllocLe
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [List.map_cons, List.nodup_cons]
          refine ⟨?_, hNodup⟩
          intro hMemMap
          obtain ⟨rOld, hrMem, hrEq⟩ := List.mem_map.mp hMemMap
          rw [hRecReq] at hrEq
          exact hSeen (hrEq ▸ hCompSeen rOld hrMem)
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hOld
          · rw [hRecReq]; exact .head _
          · exact .tail _ (hCompSeen r hOld)
        · intro j sid hSome
          obtain ⟨hsSeen, hsComp, hsOther⟩ := hSlotInv j sid hSome
          refine ⟨.tail _ hsSeen, ?_, hsOther⟩
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hOld
          · rw [hRecReq]; intro hEq; exact hSeen (hEq ▸ hsSeen)
          · exact hsComp r hOld
        · intro j hj
          exact hUnalloc j (Nat.le_trans hAllocLe hj)
      split
      · next hSlot =>
        cases validThresholdApproval st.tsig req.honestApprovers
        · exact hPushComp st.honestWal st.maskSessionCursor st.allocatedSlots _ rfl (Nat.le_refl _)
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          cases walPreSignStep st.honestWal _ _ _ with
          | err wal' _ =>
            exact hPushComp wal' st.maskSessionCursor st.allocatedSlots _ rfl (Nat.le_refl _)
          | ok wal' auth =>
            cases auth with
            | replayCached _ =>
              exact hPushComp wal' st.maskSessionCursor st.allocatedSlots _ rfl (Nat.le_refl _)
            | authorizedFresh ep =>
              dsimp only
              cases eng.slotVerify1 _ _ _ _ _ _ with
              | inl pErr =>
                exact hPushComp _ (st.maskSessionCursor + 1) (st.allocatedSlots + 1) _ rfl
                  (Nat.le_succ _)
              | inr r2Init =>
                dsimp only [ConcurrentSidInvariant]
                let slot : Fin Q_s := ⟨st.allocatedSlots, hSlot⟩
                refine ⟨hNodup, fun r hr => .tail _ (hCompSeen r hr), ?_, ?_⟩
                · intro j sid hSome
                  by_cases hJ : j = slot
                  · subst hJ
                    rw [updateConcurrentSlot_same] at hSome
                    dsimp only [slotPhaseSid] at hSome
                    injection hSome with hSidEq
                    subst hSidEq
                    refine ⟨.head _, ?_, ?_⟩
                    · intro r hr hEq
                      exact hSeen (hEq ▸ hCompSeen r hr)
                    · intro k hkNe hkSome
                      rw [updateConcurrentSlot_ne _ _ k _ hkNe] at hkSome
                      obtain ⟨hkSeen, _, _⟩ := hSlotInv k req.sessionId hkSome
                      exact hSeen hkSeen
                  · rw [updateConcurrentSlot_ne _ _ j _ hJ] at hSome
                    obtain ⟨hjSeen, hjComp, hjOther⟩ := hSlotInv j sid hSome
                    refine ⟨.tail _ hjSeen, hjComp, ?_⟩
                    intro k hkNe
                    by_cases hK : k = slot
                    · subst hK
                      rw [updateConcurrentSlot_same]
                      dsimp only [slotPhaseSid]
                      intro hEq
                      injection hEq with hEqSid
                      exact hSeen (hEqSid ▸ hjSeen)
                    · rw [updateConcurrentSlot_ne _ _ k _ hK]
                      exact hjOther k hkNe
                · intro j hj
                  have hNe : j ≠ ⟨st.allocatedSlots, hSlot⟩ := by
                    intro he
                    have hv := congrArg Fin.val he
                    dsimp only at hv hj
                    omega
                  rw [updateConcurrentSlot_ne _ _ j _ hNe]
                  exact hUnalloc j (Nat.le_of_succ_le hj)
      · exact hPushComp st.honestWal st.maskSessionCursor st.allocatedSlots _ rfl (Nat.le_refl _)
  | stepRound2 sid =>
    dsimp only
    cases lookupSidSlot sid st.sidMap with
    | none => exact ⟨hNodup, hCompSeen, hSlotInv, hUnalloc⟩
    | some slot =>
      dsimp only
      have hClose : ∀ (wal' : WalLatchState) (req : SessionScheduleReq) (wRec : SessionWireRecord),
          slotPhaseSid (st.slots slot) = some req.sessionId →
          wRec.request = req →
          ConcurrentSidInvariant
            { st with
              honestWal := wal'
              slots := updateConcurrentSlot st.slots slot .closed
              completed := wRec :: st.completed } := by
        intro wal' req wRec hAtSlot hRecReq
        dsimp only [ConcurrentSidInvariant]
        obtain ⟨hsSeen, hsComp, hsOther⟩ := hSlotInv slot req.sessionId hAtSlot
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [List.map_cons, List.nodup_cons]
          refine ⟨?_, hNodup⟩
          intro hMemMap
          obtain ⟨rOld, hrMem, hrEq⟩ := List.mem_map.mp hMemMap
          rw [hRecReq] at hrEq
          exact hsComp rOld hrMem hrEq
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hOld
          · rw [hRecReq]; exact hsSeen
          · exact hCompSeen r hOld
        · intro j sid' hSome
          by_cases hJ : j = slot
          · subst hJ
            rw [updateConcurrentSlot_same] at hSome
            cases hSome
          · rw [updateConcurrentSlot_ne _ _ j _ hJ] at hSome
            obtain ⟨hjSeen, hjComp, hjOther⟩ := hSlotInv j sid' hSome
            refine ⟨hjSeen, ?_, ?_⟩
            · intro r hr
              rcases List.mem_cons.mp hr with rfl | hOld
              · rw [hRecReq]
                intro hEq
                subst hEq
                exact hsOther j hJ hSome
              · exact hjComp r hOld
            · intro k hkNe
              by_cases hK : k = slot
              · subst hK
                rw [updateConcurrentSlot_same]
                intro hC; cases hC
              · rw [updateConcurrentSlot_ne _ _ k _ hK]
                exact hjOther k hkNe
        · intro j hj
          have hUnJ := hUnalloc j hj
          by_cases hJ : j = slot
          · subst hJ
            rw [hUnJ] at hAtSlot
            cases hAtSlot
          · rw [updateConcurrentSlot_ne _ _ j _ hJ]
            exact hUnJ
      cases hPh : st.slots slot with
      | unallocated => exact ⟨hNodup, hCompSeen, hSlotInv, hUnalloc⟩
      | afterR2 _ _ _ _ _ _ _ _ => exact ⟨hNodup, hCompSeen, hSlotInv, hUnalloc⟩
      | closed => exact ⟨hNodup, hCompSeen, hSlotInv, hUnalloc⟩
      | afterR1 ep msgDig req honR1 corrR1 r2Init =>
        dsimp only
        have hAtSlot : slotPhaseSid (st.slots slot) = some req.sessionId := by
          rw [hPh]; rfl
        cases st.honestWal.poisoned
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases eng.slotPreCut _ _ _ _ _ _ with
          | inl _ => exact hClose (walQuarantine st.honestWal) req _ hAtSlot rfl
          | inr r3Init =>
            dsimp only [ConcurrentSidInvariant]
            refine ⟨hNodup, hCompSeen, ?_, ?_⟩
            · intro j sid' hSome
              have hSameSid : ∀ (h2 c2 : List (Nat × ByteArray)) x, slotPhaseSid
                  (updateConcurrentSlot st.slots slot
                    (.afterR2 ep msgDig req honR1 corrR1 h2 c2 r3Init) x) =
                  slotPhaseSid (st.slots x) := by
                intro h2 c2 x
                by_cases hx : x = slot
                · subst hx
                  rw [updateConcurrentSlot_same, hPh]
                  rfl
                · rw [updateConcurrentSlot_ne _ _ x _ hx]
              rw [hSameSid] at hSome
              obtain ⟨hjSeen, hjComp, hjOther⟩ := hSlotInv j sid' hSome
              refine ⟨hjSeen, hjComp, ?_⟩
              intro k hkNe
              rw [hSameSid]
              exact hjOther k hkNe
            · intro j hj
              have hUnJ := hUnalloc j hj
              by_cases hJ : j = slot
              · subst hJ; rw [hUnJ] at hPh; cases hPh
              · rw [updateConcurrentSlot_ne _ _ j _ hJ]; exact hUnJ
        · simp only [↓reduceIte]
          exact hClose st.honestWal req _ hAtSlot rfl
  | stepRound3 sid =>
    dsimp only
    cases lookupSidSlot sid st.sidMap with
    | none => exact ⟨hNodup, hCompSeen, hSlotInv, hUnalloc⟩
    | some slot =>
      dsimp only
      have hClose : ∀ (wal' : WalLatchState) (req : SessionScheduleReq) (wRec : SessionWireRecord),
          slotPhaseSid (st.slots slot) = some req.sessionId →
          wRec.request = req →
          ConcurrentSidInvariant
            { st with
              honestWal := wal'
              slots := updateConcurrentSlot st.slots slot .closed
              completed := wRec :: st.completed } := by
        intro wal' req wRec hAtSlot hRecReq
        dsimp only [ConcurrentSidInvariant]
        obtain ⟨hsSeen, hsComp, hsOther⟩ := hSlotInv slot req.sessionId hAtSlot
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [List.map_cons, List.nodup_cons]
          refine ⟨?_, hNodup⟩
          intro hMemMap
          obtain ⟨rOld, hrMem, hrEq⟩ := List.mem_map.mp hMemMap
          rw [hRecReq] at hrEq
          exact hsComp rOld hrMem hrEq
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hOld
          · rw [hRecReq]; exact hsSeen
          · exact hCompSeen r hOld
        · intro j sid' hSome
          by_cases hJ : j = slot
          · subst hJ
            rw [updateConcurrentSlot_same] at hSome
            cases hSome
          · rw [updateConcurrentSlot_ne _ _ j _ hJ] at hSome
            obtain ⟨hjSeen, hjComp, hjOther⟩ := hSlotInv j sid' hSome
            refine ⟨hjSeen, ?_, ?_⟩
            · intro r hr
              rcases List.mem_cons.mp hr with rfl | hOld
              · rw [hRecReq]
                intro hEq
                subst hEq
                exact hsOther j hJ hSome
              · exact hjComp r hOld
            · intro k hkNe
              by_cases hK : k = slot
              · subst hK
                rw [updateConcurrentSlot_same]
                intro hC; cases hC
              · rw [updateConcurrentSlot_ne _ _ k _ hK]
                exact hjOther k hkNe
        · intro j hj
          have hUnJ := hUnalloc j hj
          by_cases hJ : j = slot
          · subst hJ; rw [hUnJ] at hAtSlot; cases hAtSlot
          · rw [updateConcurrentSlot_ne _ _ j _ hJ]; exact hUnJ
      cases hPh : st.slots slot with
      | unallocated => exact ⟨hNodup, hCompSeen, hSlotInv, hUnalloc⟩
      | afterR1 _ _ _ _ _ _ => exact ⟨hNodup, hCompSeen, hSlotInv, hUnalloc⟩
      | closed => exact ⟨hNodup, hCompSeen, hSlotInv, hUnalloc⟩
      | afterR2 ep msgDig req honR1 corrR1 honR2 corrR2 r3Init =>
        dsimp only
        have hAtSlot : slotPhaseSid (st.slots slot) = some req.sessionId := by
          rw [hPh]; rfl
        cases st.honestWal.poisoned
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases eng.slotFinalize _ _ _ _ _ _ with
          | inl _ => exact hClose (walQuarantine st.honestWal) req _ hAtSlot rfl
          | inr sigBytes => exact hClose _ req _ hAtSlot rfl
        · simp only [↓reduceIte]
          exact hClose st.honestWal req _ hAtSlot rfl

/-- **Unique `SessionId` Domain-Separation Theorem (`concurrentProtocolExec_unique_sessionIds`)**:
    Across any `numSteps`-step arbitrarily interleaved execution of `ConcurrentProtocolExec`,
    every recorded session in the transcript carries a strictly unique `sessionId`. -/
theorem concurrentProtocolExec_unique_sessionIds
    {PK ShareT SessionTape R1St R2St R3St AdvState : Type}
    (proto : InteractiveThresholdProtocol PK ShareT SessionTape R1St R2St R3St)
    (A : ConcurrentUcAdversary AdvState) (Q_s numSteps : Nat)
    (realTapes : Fin Q_s → SessionTape)
    (cl : RealClusterState PK ShareT) (advSt : AdvState) :
    (((ConcurrentProtocolExec proto A Q_s numSteps realTapes cl advSt).2.sessions).map
      (fun r => r.request.sessionId)).Nodup := by
  have hLoop : ∀ (n : Nat)
      (st : ConcurrentExecState PK Q_s R2St R3St) (a : AdvState),
      ConcurrentSidInvariant st →
      (((execConcurrentSteps (realConcurrentEngine proto cl.honestShares realTapes) A n st a).2.sessions).map
        (fun r => r.request.sessionId)).Nodup := by
    intro n
    induction n with
    | zero => intro st _ hInv; exact hInv.1
    | succ m ih =>
      intro st a hInv
      exact ih _ _ (execConcurrentStep_preserves_sidInvariant _ A st a hInv)
  apply hLoop numSteps
  refine ⟨List.nodup_nil, (fun _ h => by cases h), ?_, fun _ _ => rfl⟩
  intro _ _ hSome
  cases hSome

/-- **Concurrent Pre-Cut Barrier Soundness (`concurrentProtocolExec_openings_have_barrier_witnesses`)**:
    Even under arbitrary round interleaving across `Q_s` concurrent sessions, every session exposing
    non-empty `honestRound3` wire bytes in `ConcurrentProtocolExec` has an explicit `preCutBarrier`
    success witness. -/
theorem concurrentProtocolExec_openings_have_barrier_witnesses
    {PK ShareT SessionTape R1St R2St R3St AdvState : Type}
    (proto : InteractiveThresholdProtocol PK ShareT SessionTape R1St R2St R3St)
    (A : ConcurrentUcAdversary AdvState) (Q_s numSteps : Nat)
    (realTapes : Fin Q_s → SessionTape)
    (cl : RealClusterState PK ShareT) (advSt : AdvState) :
    ∀ wRec ∈ (ConcurrentProtocolExec proto A Q_s numSteps realTapes cl advSt).2.sessions,
      SessionBarrierJustified proto wRec := by
  let eng := realConcurrentEngine proto cl.honestShares realTapes
  let Inv : ConcurrentExecState PK Q_s R2St R3St → Prop := fun st =>
    (∀ wRec ∈ st.completed, SessionBarrierJustified proto wRec) ∧
    (∀ (j : Fin Q_s) ep md req h1 c1 h2 c2 r3,
      st.slots j = .afterR2 ep md req h1 c1 h2 c2 r3 →
      ∃ (pk : PK) (r2 : R2St), proto.preCutBarrier pk req r2 h2 c2 = .inr r3)
  have hStep : ∀ st a, Inv st → Inv (execConcurrentStep eng A st a).1 := by
    intro st a ⟨hComp, hSlots⟩
    unfold execConcurrentStep
    dsimp only
    cases (A.chooseNextStep a).1 with
    | startRound1 req =>
      dsimp only
      split
      · exact ⟨hComp, hSlots⟩
      · split
        · next hSlot =>
          cases validThresholdApproval st.tsig req.honestApprovers
          · refine ⟨?_, hSlots⟩
            intro r hr; rcases List.mem_cons.mp hr with rfl | hOld
            · intro h; exact False.elim (h rfl)
            · exact hComp r hOld
          · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            cases walPreSignStep st.honestWal _ _ _ with
            | err _ _ =>
              refine ⟨?_, hSlots⟩
              intro r hr; rcases List.mem_cons.mp hr with rfl | hOld
              · intro h; exact False.elim (h rfl)
              · exact hComp r hOld
            | ok _ auth =>
              cases auth with
              | replayCached _ =>
                refine ⟨?_, hSlots⟩
                intro r hr; rcases List.mem_cons.mp hr with rfl | hOld
                · intro h; exact False.elim (h rfl)
                · exact hComp r hOld
              | authorizedFresh _ =>
                dsimp only
                cases eng.slotVerify1 _ _ _ _ _ _ with
                | inl _ =>
                  dsimp only [Inv]
                  refine ⟨?_, hSlots⟩
                  intro r hr; rcases List.mem_cons.mp hr with rfl | hOld
                  · intro h; exact False.elim (h rfl)
                  · exact hComp r hOld
                | inr _ =>
                  dsimp only [Inv]
                  refine ⟨hComp, ?_⟩
                  intro j ep md rq h1 c1 h2 c2 r3 hEq
                  by_cases hJ : j = ⟨st.allocatedSlots, hSlot⟩
                  · subst hJ; rw [updateConcurrentSlot_same] at hEq; cases hEq
                  · rw [updateConcurrentSlot_ne _ _ j _ hJ] at hEq
                    exact hSlots j ep md rq h1 c1 h2 c2 r3 hEq
        · refine ⟨?_, hSlots⟩
          intro r hr; rcases List.mem_cons.mp hr with rfl | hOld
          · intro h; exact False.elim (h rfl)
          · exact hComp r hOld
    | stepRound2 sid =>
      dsimp only
      cases lookupSidSlot sid st.sidMap with
      | none => exact ⟨hComp, hSlots⟩
      | some slot =>
        dsimp only
        cases hPh : st.slots slot with
        | unallocated => exact ⟨hComp, hSlots⟩
        | afterR2 _ _ _ _ _ _ _ _ => exact ⟨hComp, hSlots⟩
        | closed => exact ⟨hComp, hSlots⟩
        | afterR1 ep md req h1 c1 r2Init =>
          dsimp only
          cases st.honestWal.poisoned
          · simp only [Bool.false_eq_true, ↓reduceIte]
            cases hb : eng.slotPreCut slot st.tsig.pk req _ _ _ with
            | inl _ =>
              dsimp only [Inv]
              refine ⟨?_, ?_⟩
              · intro r hr; rcases List.mem_cons.mp hr with rfl | hOld
                · intro h; exact False.elim (h rfl)
                · exact hComp r hOld
              · intro j ep' md' rq h1' c1' h2' c2' r3 hEq
                by_cases hJ : j = slot
                · subst hJ; rw [updateConcurrentSlot_same] at hEq; cases hEq
                · rw [updateConcurrentSlot_ne _ _ j _ hJ] at hEq
                  exact hSlots j ep' md' rq h1' c1' h2' c2' r3 hEq
            | inr r3Init =>
              dsimp only [Inv]
              refine ⟨hComp, ?_⟩
              intro j ep' md' rq h1' c1' h2' c2' r3 hEq
              by_cases hJ : j = slot
              · subst hJ
                rw [updateConcurrentSlot_same] at hEq
                injection hEq with _ _ hReq _ _ hH2 hC2 hR3
                subst hReq hH2 hC2 hR3
                exact ⟨st.tsig.pk, _, hb⟩
              · rw [updateConcurrentSlot_ne _ _ j _ hJ] at hEq
                exact hSlots j ep' md' rq h1' c1' h2' c2' r3 hEq
          · simp only [↓reduceIte]
            dsimp only [Inv]
            refine ⟨?_, ?_⟩
            · intro r hr; rcases List.mem_cons.mp hr with rfl | hOld
              · intro h; exact False.elim (h rfl)
              · exact hComp r hOld
            · intro j ep' md' rq h1' c1' h2' c2' r3 hEq
              by_cases hJ : j = slot
              · subst hJ; rw [updateConcurrentSlot_same] at hEq; cases hEq
              · rw [updateConcurrentSlot_ne _ _ j _ hJ] at hEq
                exact hSlots j ep' md' rq h1' c1' h2' c2' r3 hEq
    | stepRound3 sid =>
      dsimp only
      cases lookupSidSlot sid st.sidMap with
      | none => exact ⟨hComp, hSlots⟩
      | some slot =>
        dsimp only
        cases hPh : st.slots slot with
        | unallocated => exact ⟨hComp, hSlots⟩
        | afterR1 _ _ _ _ _ _ => exact ⟨hComp, hSlots⟩
        | closed => exact ⟨hComp, hSlots⟩
        | afterR2 ep md req h1 c1 h2 c2 r3Init =>
          dsimp only
          obtain ⟨pkW, r2W, hbW⟩ := hSlots slot ep md req h1 c1 h2 c2 r3Init hPh
          have hRestSlots : ∀ j ep' md' rq h1' c1' h2' c2' r3,
              updateConcurrentSlot st.slots slot .closed j = .afterR2 ep' md' rq h1' c1' h2' c2' r3 →
              ∃ (pk : PK) (r2 : R2St), proto.preCutBarrier pk rq r2 h2' c2' = .inr r3 := by
            intro j ep' md' rq h1' c1' h2' c2' r3 hEq
            by_cases hJ : j = slot
            · subst hJ; rw [updateConcurrentSlot_same] at hEq; cases hEq
            · rw [updateConcurrentSlot_ne _ _ j _ hJ] at hEq
              exact hSlots j ep' md' rq h1' c1' h2' c2' r3 hEq
          cases st.honestWal.poisoned
          · simp only [Bool.false_eq_true, ↓reduceIte]
            cases eng.slotFinalize _ _ _ _ _ _ <;> (dsimp only [Inv]; refine ⟨?_, hRestSlots⟩)
            all_goals
              intro r hr; rcases List.mem_cons.mp hr with rfl | hOld
              · intro _; exact ⟨pkW, r2W, r3Init, hbW⟩
              · exact hComp r hOld
          · simp only [↓reduceIte]
            dsimp only [Inv]
            refine ⟨?_, hRestSlots⟩
            intro r hr; rcases List.mem_cons.mp hr with rfl | hOld
            · intro h; exact False.elim (h rfl)
            · exact hComp r hOld
  have hLoop : ∀ n st a, Inv st → ∀ wRec ∈ (execConcurrentSteps eng A n st a).2.sessions,
      SessionBarrierJustified proto wRec := by
    intro n
    induction n with
    | zero => intro st _ hI; exact hI.1
    | succ m ih => intro st a hI; exact ih _ _ (hStep st a hI)
  apply hLoop numSteps
  exact ⟨(fun _ h => by cases h), (fun _ _ _ _ _ _ _ _ _ h => by cases h)⟩

private def mapSlotPhase {A2 A3 B2 B3 : Type} (f2 : A2 → B2) (f3 : A3 → B3) :
    ConcurrentSlotPhase A2 A3 → ConcurrentSlotPhase B2 B3
  | .unallocated => .unallocated
  | .afterR1 ep md req h1 c1 r2 => .afterR1 ep md req h1 c1 (f2 r2)
  | .afterR2 ep md req h1 c1 h2 c2 r3 => .afterR2 ep md req h1 c1 h2 c2 (f3 r3)
  | .closed => .closed

private def mapConcurrentState {PK A2 A3 B2 B3 : Type} {Q_s : Nat}
    (f2 : A2 → B2) (f3 : A3 → B3)
    (st : ConcurrentExecState PK Q_s A2 A3) : ConcurrentExecState PK Q_s B2 B3 :=
  { tsig              := st.tsig
    honestWal         := st.honestWal
    maskSessionCursor := st.maskSessionCursor
    seenSids          := st.seenSids
    allocatedSlots    := st.allocatedSlots
    sidMap            := st.sidMap
    slots             := fun j => mapSlotPhase f2 f3 (st.slots j)
    completed         := st.completed }

private theorem execConcurrentSteps_map_eq
    {PK A1 A2 A3 B1 B2 B3 AdvState : Type} {Q_s : Nat}
    (engA : ConcurrentSlotEngine PK Q_s A1 A2 A3)
    (engB : ConcurrentSlotEngine PK Q_s B1 B2 B3)
    (A : ConcurrentUcAdversary AdvState)
    (pk0 : PK)
    (f1 : A1 → B1) (f2 : A2 → B2) (f3 : A3 → B3)
    (hPkDig : engA.pkDigestOf pk0 = engB.pkDigestOf pk0)
    (hMsgDig : engA.msgDigestOf = engB.msgDigestOf)
    (hR1 : ∀ j corr req cur,
      engB.slotRound1 j pk0 corr req cur =
        let (w, a1) := engA.slotRound1 j pk0 corr req cur; (w, f1 a1))
    (hV1 : ∀ j req a1 h1 c1,
      engB.slotVerify1 j pk0 req (f1 a1) h1 c1 =
        match engA.slotVerify1 j pk0 req a1 h1 c1 with
        | .inl err => .inl err
        | .inr a2 => .inr (f2 a2))
    (hR2 : ∀ j corr req a2,
      engB.slotRound2 j pk0 corr req (f2 a2) =
        let (w, a2') := engA.slotRound2 j pk0 corr req a2; (w, f2 a2'))
    (hPC : ∀ j req a2 h2 c2,
      engB.slotPreCut j pk0 req (f2 a2) h2 c2 =
        match engA.slotPreCut j pk0 req a2 h2 c2 with
        | .inl err => .inl err
        | .inr a3 => .inr (f3 a3))
    (hR3 : ∀ j corr req a3,
      engB.slotRound3 j pk0 corr req (f3 a3) =
        let (w, a3') := engA.slotRound3 j pk0 corr req a3; (w, f3 a3'))
    (hFin : ∀ j req a3 h3 c3,
      engB.slotFinalize j pk0 req (f3 a3) h3 c3 =
        engA.slotFinalize j pk0 req a3 h3 c3) :
    ∀ (n : Nat) (st : ConcurrentExecState PK Q_s A2 A3) (advSt : AdvState),
      st.tsig.pk = pk0 →
      (execConcurrentSteps engB A n (mapConcurrentState f2 f3 st) advSt).2 =
        (execConcurrentSteps engA A n st advSt).2
  | 0, _, _, _ => rfl
  | m + 1, st, advSt, hPk => by
    have hMapUpd : ∀ (slots : Fin Q_s → ConcurrentSlotPhase A2 A3) (slot : Fin Q_s)
        (ph : ConcurrentSlotPhase A2 A3),
        updateConcurrentSlot (fun j => mapSlotPhase f2 f3 (slots j)) slot (mapSlotPhase f2 f3 ph) =
          fun j => mapSlotPhase f2 f3 (updateConcurrentSlot slots slot ph j) := by
      intro slots slot ph
      funext j
      by_cases hj : j = slot
      · subst hj; rw [updateConcurrentSlot_same, updateConcurrentSlot_same]
      · rw [updateConcurrentSlot_ne _ _ j _ hj, updateConcurrentSlot_ne _ _ j _ hj]
    have hMapAfterR1 : ∀ ep md req h1 c1 (r2 : A2),
        mapSlotPhase f2 f3 (.afterR1 ep md req h1 c1 r2) = .afterR1 ep md req h1 c1 (f2 r2) :=
      fun _ _ _ _ _ _ => rfl
    have hMapAfterR2 : ∀ ep md req h1 c1 h2 c2 (r3 : A3),
        mapSlotPhase f2 f3 (.afterR2 ep md req h1 c1 h2 c2 r3) =
          .afterR2 ep md req h1 c1 h2 c2 (f3 r3) :=
      fun _ _ _ _ _ _ _ _ => rfl
    have hStep :
        (execConcurrentStep engB A (mapConcurrentState f2 f3 st) advSt =
          let (st1, adv1) := execConcurrentStep engA A st advSt
          (mapConcurrentState f2 f3 st1, adv1)) ∧
        (execConcurrentStep engA A st advSt).1.tsig.pk = pk0 := by
      unfold execConcurrentStep
      dsimp only [mapConcurrentState]
      cases (A.chooseNextStep advSt).1 with
      | startRound1 req =>
        dsimp only
        by_cases hSeen : req.sessionId ∈ st.seenSids
        · simp only [hSeen, decide_true, ↓reduceIte]
          exact ⟨trivial, hPk⟩
        · simp only [hSeen, decide_false, Bool.false_eq_true, ↓reduceIte]
          by_cases hSlot : st.allocatedSlots < Q_s
          · simp only [hSlot, ↓reduceDIte]
            by_cases hAppr : validThresholdApproval st.tsig req.honestApprovers = true
            · simp only [hAppr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              rw [hPk, ← hPkDig, ← hMsgDig]
              cases walPreSignStep st.honestWal _ _ _ with
              | err _ _ => exact ⟨rfl, hPk⟩
              | ok wal' auth =>
                cases auth with
                | replayCached _ => exact ⟨rfl, hPk⟩
                | authorizedFresh ep =>
                  dsimp only
                  simp only [hR1]
                  simp only [hV1]
                  cases engA.slotVerify1 _ _ _ _ _ _ with
                  | inl _ => exact ⟨rfl, hPk⟩
                  | inr a2 =>
                    refine ⟨?_, hPk⟩
                    dsimp only [mapConcurrentState]
                    rw [← hMapUpd st.slots ⟨st.allocatedSlots, hSlot⟩ (.afterR1 ep _ req _ _ a2)]
                    rfl
            · have hApprF : validThresholdApproval st.tsig req.honestApprovers = false :=
                Bool.eq_false_iff.mpr hAppr
              simp only [hApprF, Bool.not_false, ↓reduceIte]
              exact ⟨trivial, hPk⟩
          · simp only [hSlot, ↓reduceDIte]
            exact ⟨trivial, hPk⟩
      | stepRound2 sid =>
        dsimp only
        cases lookupSidSlot sid st.sidMap with
        | none => exact ⟨rfl, hPk⟩
        | some slot =>
          dsimp only
          cases hPh : st.slots slot with
          | unallocated => dsimp only [mapSlotPhase]; exact ⟨rfl, hPk⟩
          | afterR2 _ _ _ _ _ _ _ _ => dsimp only [mapSlotPhase]; exact ⟨rfl, hPk⟩
          | closed => dsimp only [mapSlotPhase]; exact ⟨rfl, hPk⟩
          | afterR1 ep md req h1 c1 a2 =>
            simp only [hMapAfterR1]
            by_cases hPois : st.honestWal.poisoned = true
            · simp only [hPois, ↓reduceIte]
              refine ⟨?_, hPk⟩
              rw [← hMapUpd st.slots slot .closed]
              rfl
            · have hPoisF : st.honestWal.poisoned = false := Bool.eq_false_iff.mpr hPois
              simp only [hPoisF, Bool.false_eq_true, ↓reduceIte]
              rw [hPk]
              simp only [hR2]
              simp only [hPC]
              cases engA.slotPreCut _ _ _ _ _ _ with
              | inl _ =>
                refine ⟨?_, hPk⟩
                rw [← hMapUpd st.slots slot .closed]
                rfl
              | inr a3 =>
                refine ⟨?_, rfl⟩
                rw [← hMapUpd st.slots slot (.afterR2 ep md req h1 c1 _ _ a3)]
                rfl
      | stepRound3 sid =>
        dsimp only
        cases lookupSidSlot sid st.sidMap with
        | none => exact ⟨rfl, hPk⟩
        | some slot =>
          dsimp only
          cases hPh : st.slots slot with
          | unallocated => dsimp only [mapSlotPhase]; exact ⟨rfl, hPk⟩
          | afterR1 _ _ _ _ _ _ => dsimp only [mapSlotPhase]; exact ⟨rfl, hPk⟩
          | closed => dsimp only [mapSlotPhase]; exact ⟨rfl, hPk⟩
          | afterR2 ep md req h1 c1 h2 c2 a3 =>
            simp only [hMapAfterR2]
            by_cases hPois : st.honestWal.poisoned = true
            · simp only [hPois, ↓reduceIte]
              refine ⟨?_, hPk⟩
              rw [← hMapUpd st.slots slot .closed]
              rfl
            · have hPoisF : st.honestWal.poisoned = false := Bool.eq_false_iff.mpr hPois
              simp only [hPoisF, Bool.false_eq_true, ↓reduceIte]
              rw [hPk]
              simp only [hR3]
              simp only [hFin]
              cases engA.slotFinalize _ _ _ _ _ _ <;>
                (refine ⟨?_, hPk⟩; rw [← hMapUpd st.slots slot .closed]; rfl)
    obtain ⟨hStEq, hPk1⟩ := hStep
    simp only [execConcurrentSteps]
    rw [hStEq]
    exact execConcurrentSteps_map_eq engA engB A pk0 f1 f2 f3
      hPkDig hMsgDig hR1 hV1 hR2 hPC hR3 hFin m _ _ hPk1

theorem concurrentProtocolExec_eq_hybrid_zero
    {PK ShareT SessionTape R1St R2St R3St SimTape SimR1 SimR2 SimR3 AdvState : Type}
    (proto : InteractiveThresholdProtocol PK ShareT SessionTape R1St R2St R3St)
    (idealSignOracle : SessionScheduleReq → ByteArray)
    (sim : BlackBoxUcSimulator PK SimTape SimR1 SimR2 SimR3)
    (A : ConcurrentUcAdversary AdvState) (Q_s numSteps : Nat)
    (realTapes : Fin Q_s → SessionTape) (simTapes : Fin Q_s → SimTape)
    (cl : RealClusterState PK ShareT) (advSt : AdvState) :
    (ConcurrentProtocolExec proto A Q_s numSteps realTapes cl advSt).2 =
      ConcurrentHybridExec 0 proto idealSignOracle sim A Q_s numSteps
        realTapes simTapes cl advSt := by
  unfold ConcurrentProtocolExec ConcurrentHybridExec
  dsimp only
  exact (execConcurrentSteps_map_eq
    (realConcurrentEngine proto cl.honestShares realTapes)
    (hybridConcurrentEngine 0 proto cl.honestShares idealSignOracle sim realTapes simTapes)
    A cl.tsig.pk PSum.inl PSum.inl PSum.inl rfl rfl
    (fun j _ _ _ => by simp [realConcurrentEngine, hybridConcurrentEngine])
    (fun _ _ _ _ _ => by simp [realConcurrentEngine, hybridConcurrentEngine])
    (fun _ _ _ _ => by simp [realConcurrentEngine, hybridConcurrentEngine])
    (fun _ _ _ _ _ => by simp [realConcurrentEngine, hybridConcurrentEngine])
    (fun _ _ _ _ => by simp [realConcurrentEngine, hybridConcurrentEngine])
    (fun _ _ _ _ _ => by simp [realConcurrentEngine, hybridConcurrentEngine])
    numSteps _ advSt rfl).symm

theorem concurrentIdealExec_eq_hybrid_top
    {PK ShareT SessionTape R1St R2St R3St SimTape SimR1 SimR2 SimR3 AdvState : Type}
    (proto : InteractiveThresholdProtocol PK ShareT SessionTape R1St R2St R3St)
    (idealSignOracle : SessionScheduleReq → ByteArray)
    (sim : BlackBoxUcSimulator PK SimTape SimR1 SimR2 SimR3)
    (A : ConcurrentUcAdversary AdvState) (Q_s numSteps : Nat)
    (realTapes : Fin Q_s → SessionTape) (simTapes : Fin Q_s → SimTape)
    (cl : RealClusterState PK ShareT) (icl : IdealClusterState PK) (advSt : AdvState)
    (hTsig : cl.tsig = icl.tsig) (hWal : cl.honestWal = icl.honestWal)
    (hCur : cl.maskSessionCursor = icl.maskSessionCursor)
    (hPkDig : proto.pkDigestOf icl.tsig.pk = sim.pkDigestOf icl.tsig.pk)
    (hMsgDig : proto.msgDigestOf = sim.msgDigestOf) :
    (ConcurrentIdealExec idealSignOracle sim A Q_s numSteps simTapes icl advSt).2 =
      ConcurrentHybridExec Q_s proto idealSignOracle sim A Q_s numSteps
        realTapes simTapes cl advSt := by
  unfold ConcurrentIdealExec ConcurrentHybridExec
  dsimp only
  have hInitEq :
      initConcurrentExecState Q_s (PSum R2St SimR2) (PSum R3St (SimR3 × ByteArray))
        cl.tsig cl.honestWal cl.maskSessionCursor =
      mapConcurrentState PSum.inr PSum.inr
        (initConcurrentExecState Q_s SimR2 (SimR3 × ByteArray)
          icl.tsig icl.honestWal icl.maskSessionCursor) := by
    rw [hTsig, hWal, hCur]
    rfl
  rw [hInitEq]
  exact (execConcurrentSteps_map_eq
    (idealConcurrentEngine idealSignOracle sim simTapes)
    (hybridConcurrentEngine Q_s proto cl.honestShares idealSignOracle sim realTapes simTapes)
    A icl.tsig.pk PSum.inr PSum.inr PSum.inr hPkDig.symm hMsgDig.symm
    (fun j _ _ _ => by dsimp only [idealConcurrentEngine, hybridConcurrentEngine]; rw [ite_eq_left j.isLt])
    (fun _ _ _ _ _ => by simp [idealConcurrentEngine, hybridConcurrentEngine])
    (fun _ _ _ _ => by simp [idealConcurrentEngine, hybridConcurrentEngine])
    (fun _ req' s2' h2' c2' => by
      simp only [idealConcurrentEngine, hybridConcurrentEngine]
      cases sim.simPreCutBarrier icl.tsig.pk req' s2' h2' c2' <;> rfl)
    (fun _ _ _ _ => by simp [idealConcurrentEngine, hybridConcurrentEngine])
    (fun _ _ _ _ _ => by simp [idealConcurrentEngine, hybridConcurrentEngine])
    numSteps _ advSt rfl).symm

/-- **Per-Session Roundwise Simulation Coupling (`PerSessionRoundSimSpec`)**:
    Captures exact pad-bijection hiding in Rounds 1 & 2 (`padBij` independent of check coin `c`),
    `≤ epsCheck / cardCheck` active pre-cut barrier soundness, and exact Round-3 cut-opening
    programming from `idealSignOracle`. -/
structure PerSessionRoundSimSpec
    {PK ShareT SessionTape R1St R2St R3St SimTape SimR1 SimR2 SimR3 : Type}
    (proto : InteractiveThresholdProtocol PK ShareT SessionTape R1St R2St R3St)
    (idealSignOracle : SessionScheduleReq → ByteArray)
    (sim : BlackBoxUcSimulator PK SimTape SimR1 SimR2 SimR3)
    (pk : PK) (corruptParties : List Nat) (honestShares : Nat → Option ShareT)
    (cardPad cardCheck epsCheck : Nat) where
  hPadPos        : 0 < cardPad
  hCheckPos      : 0 < cardCheck
  realTapeOf     : Fin cardPad → Fin cardCheck → SessionTape
  simTapeOf      : Fin cardPad → Fin cardCheck → SimTape
  hSimTapeIndep  : ∀ p c₁ c₂, simTapeOf p c₁ = simTapeOf p c₂
  padBij         : SimpleEquiv (Fin cardPad) (Fin cardPad)
  RelR1          : Fin cardPad → Fin cardCheck → SessionScheduleReq → R1St → SimR1 → Prop
  RelR2          : Fin cardPad → Fin cardCheck → SessionScheduleReq → R2St → SimR2 → Prop
  RelR3          : Fin cardPad → Fin cardCheck → SessionScheduleReq → R3St → SimR3 → Prop
  badCheck       : SessionScheduleReq → List (Nat × ByteArray) → List (Nat × ByteArray) →
                     Fin cardCheck → Bool
  hPkDigest      : proto.pkDigestOf pk = sim.pkDigestOf pk
  hMsgDigest     : proto.msgDigestOf = sim.msgDigestOf
  hRound1        : ∀ req cur p c,
    let (wR, r1) := proto.honestRound1 pk corruptParties req cur honestShares (realTapeOf p c)
    let (wS, s1) := sim.simRound1 pk corruptParties req cur (simTapeOf (padBij.toFun p) c)
    wR = wS ∧ RelR1 p c req r1 s1
  hVerify1       : ∀ p c req r1 s1 h1 c1, RelR1 p c req r1 s1 →
    (∃ err, proto.verifyRound1 pk req r1 h1 c1 = .inl err ∧
            sim.simVerifyRound1 pk req s1 h1 c1 = .inl err) ∨
    (∃ r2 s2, proto.verifyRound1 pk req r1 h1 c1 = .inr r2 ∧
              sim.simVerifyRound1 pk req s1 h1 c1 = .inr s2 ∧
              RelR2 p c req r2 s2)
  hRound2        : ∀ p c req r2 s2, RelR2 p c req r2 s2 →
    let (wR, r2') := proto.honestRound2 pk corruptParties req r2 honestShares (realTapeOf p c)
    let (wS, s2') := sim.simRound2 pk corruptParties req s2 (simTapeOf (padBij.toFun p) c)
    wR = wS ∧ RelR2 p c req r2' s2'
  hPreCut        : ∀ p c req r2 s2 h2 c2, RelR2 p c req r2 s2 →
    badCheck req h2 c2 c = false →
    (∃ err, proto.preCutBarrier pk req r2 h2 c2 = .inl err ∧
            sim.simPreCutBarrier pk req s2 h2 c2 = .inl err) ∨
    (∃ r3 s3, proto.preCutBarrier pk req r2 h2 c2 = .inr r3 ∧
              sim.simPreCutBarrier pk req s2 h2 c2 = .inr s3 ∧
              RelR3 p c req r3 s3)
  hRound3        : ∀ p c req r3 s3, RelR3 p c req r3 s3 →
    let (wR, r3') := proto.honestRound3 pk corruptParties req r3 honestShares (realTapeOf p c)
    let (wS, s3') := sim.simRound3 pk corruptParties req s3 (idealSignOracle req)
      (simTapeOf (padBij.toFun p) c)
    wR = wS ∧ RelR3 p c req r3' s3'
  hFinalize      : ∀ p c req r3 s3 h3 c3, RelR3 p c req r3 s3 →
    proto.finalizeCutOpen pk req r3 h3 c3 =
      sim.finalizeIdealCut pk req s3 (idealSignOracle req) h3 c3
  hBadCheckBound : ∀ req h2 c2,
    finSum cardCheck (fun c => if badCheck req h2 c2 c then 1 else 0) ≤ epsCheck

/-- Lift `padBij` on `Fin cardPad` while keeping `Fin cardCheck` fixed. -/
def liftPadCheckEquiv {cardPad cardCheck : Nat} (hCheck : 0 < cardCheck)
    (padBij : SimpleEquiv (Fin cardPad) (Fin cardPad)) :
    SimpleEquiv (Fin (cardPad * cardCheck)) (Fin (cardPad * cardCheck)) :=
  { toFun := fun x => ucPairFin (padBij.toFun (ucSplitLeft hCheck x)) (ucSplitRight hCheck x)
    invFun := fun y => ucPairFin (padBij.invFun (ucSplitLeft hCheck y)) (ucSplitRight hCheck y)
    left_inv := fun x => by
      change ucPairFin (padBij.invFun (ucSplitLeft hCheck (ucPairFin _ _)))
        (ucSplitRight hCheck (ucPairFin _ _)) = x
      rw [ucSplitLeft_pair hCheck, ucSplitRight_pair hCheck, padBij.left_inv]
      exact ucPair_split hCheck x
    right_inv := fun y => by
      change ucPairFin (padBij.toFun (ucSplitLeft hCheck (ucPairFin _ _)))
        (ucSplitRight hCheck (ucPairFin _ _)) = y
      rw [ucSplitLeft_pair hCheck, ucSplitRight_pair hCheck, padBij.right_inv]
      exact ucPair_split hCheck y }

/-- Observe the first `(req, honR2, corrR2)` tuple fed to `slotPreCut` at `slot = idx`
    across `numSteps` concurrent steps. -/
private def obsConcurrentSlotPreCut {PK SlotR1 SlotR2 SlotR3 AdvState : Type} {Q_s : Nat}
    (eng : ConcurrentSlotEngine PK Q_s SlotR1 SlotR2 SlotR3)
    (A : ConcurrentUcAdversary AdvState) (idx : Fin Q_s) :
    (numSteps : Nat) → ConcurrentExecState PK Q_s SlotR2 SlotR3 → AdvState →
    Option (SessionScheduleReq × List (Nat × ByteArray) × List (Nat × ByteArray))
  | 0, _, _ => none
  | m + 1, st, advSt =>
    let (cmd, advSt1) := A.chooseNextStep advSt
    match cmd with
    | .startRound1 _ =>
      let (st1, a1) := execConcurrentStep eng A st advSt
      obsConcurrentSlotPreCut eng A idx m st1 a1
    | .stepRound2 sid =>
      match lookupSidSlot sid st.sidMap with
      | some slot =>
        if slot = idx then
          match st.slots slot with
          | .unallocated =>
            let (st1, a1) := execConcurrentStep eng A st advSt
            obsConcurrentSlotPreCut eng A idx m st1 a1
          | .afterR2 _ _ _ _ _ _ _ _ =>
            let (st1, a1) := execConcurrentStep eng A st advSt
            obsConcurrentSlotPreCut eng A idx m st1 a1
          | .closed =>
            let (st1, a1) := execConcurrentStep eng A st advSt
            obsConcurrentSlotPreCut eng A idx m st1 a1
          | .afterR1 _ _ req _ _ r2Init =>
            if st.honestWal.poisoned then
              let (st1, a1) := execConcurrentStep eng A st advSt
              obsConcurrentSlotPreCut eng A idx m st1 a1
            else
              let (honR2, _) := eng.slotRound2 slot st.tsig.pk st.tsig.corruptParties req r2Init
              let (corrR2Fn, _) := A.rushRound2 advSt1 sid honR2
              let corrR2 := st.tsig.corruptParties.map (fun c => (c, corrR2Fn c))
              some (req, honR2, corrR2)
        else
          let (st1, a1) := execConcurrentStep eng A st advSt
          obsConcurrentSlotPreCut eng A idx m st1 a1
      | none =>
        let (st1, a1) := execConcurrentStep eng A st advSt
        obsConcurrentSlotPreCut eng A idx m st1 a1
    | .stepRound3 _ =>
      let (st1, a1) := execConcurrentStep eng A st advSt
      obsConcurrentSlotPreCut eng A idx m st1 a1

/-- **Main Concurrent Hybrid Reduction Theorem (`concurrent_hybrid_simulation_reduces_to_per_session`)**:
    Under unique `SessionId` domain separation, if `(proto, sim)` satisfies `PerSessionRoundSimSpec`
    with per-session active barrier soundness `≤ epsCheck / cardCheck`, then for **ANY** stateful
    rushing concurrent adversary `A` arbitrarily interleaving Round 1 / Round 2 / Round 3 steps
    across up to `Q_s` live sessions over `numSteps` steps and **EVERY** distinguisher `D`:
    `ratLe (rationalAcceptDiff cardAll concurrentRealView cardAll concurrentIdealView D) (Q_s * epsCheck, cardCheck)`. -/
theorem concurrent_hybrid_simulation_reduces_to_per_session
    {PK ShareT SessionTape R1St R2St R3St SimTape SimR1 SimR2 SimR3 AdvState : Type}
    (proto : InteractiveThresholdProtocol PK ShareT SessionTape R1St R2St R3St)
    (idealSignOracle : SessionScheduleReq → ByteArray)
    (sim : BlackBoxUcSimulator PK SimTape SimR1 SimR2 SimR3)
    (A : ConcurrentUcAdversary AdvState) (Q_s numSteps : Nat)
    (cl : RealClusterState PK ShareT) (icl : IdealClusterState PK) (advSt : AdvState)
    (hTsig : cl.tsig = icl.tsig) (hWal : cl.honestWal = icl.honestWal)
    (hCur : cl.maskSessionCursor = icl.maskSessionCursor)
    {cardPad cardCheck epsCheck : Nat}
    (spec : PerSessionRoundSimSpec proto idealSignOracle sim
      cl.tsig.pk cl.tsig.corruptParties cl.honestShares cardPad cardCheck epsCheck)
    (D : ExecTranscript AdvState → Bool) :
    let cardS := cardPad * cardCheck
    let hCardS : 0 < cardS := Nat.mul_pos spec.hPadPos spec.hCheckPos
    let cardAll := ucPow cardS Q_s
    let enumVec := finPowVecEquiv hCardS Q_s
    let mkReal := fun (v : Fin Q_s → Fin cardS) (j : Fin Q_s) =>
      spec.realTapeOf (ucSplitLeft spec.hCheckPos (v j)) (ucSplitRight spec.hCheckPos (v j))
    let mkSim := fun (v : Fin Q_s → Fin cardS) (j : Fin Q_s) =>
      spec.simTapeOf (ucSplitLeft spec.hCheckPos (v j)) (ucSplitRight spec.hCheckPos (v j))
    let realView := fun ω : Fin cardAll =>
      (ConcurrentProtocolExec proto A Q_s numSteps (mkReal (enumVec.toFun ω)) cl advSt).2
    let idealView := fun ω : Fin cardAll =>
      (ConcurrentIdealExec idealSignOracle sim A Q_s numSteps (mkSim (enumVec.toFun ω)) icl advSt).2
    ratLe (rationalAcceptDiff cardAll realView cardAll idealView D)
          (Q_s * epsCheck, cardCheck) := by
  intro cardS hCardS cardAll enumVec mkReal mkSim realView idealView
  let c0 : Fin cardCheck := ⟨0, spec.hCheckPos⟩
  let bijCoord : SimpleEquiv (Fin cardS) (Fin cardS) := liftPadCheckEquiv spec.hCheckPos spec.padBij
  let hybrids : (h : Nat) → h ≤ Q_s → (Fin Q_s → Fin cardS) → ExecTranscript AdvState :=
    fun h _ v => ConcurrentHybridExec h proto idealSignOracle sim A Q_s numSteps (mkReal v) (mkSim v) cl advSt
  let bad : Fin Q_s → (Fin Q_s → Fin cardS) → Bool := fun idx v =>
    let p := ucSplitLeft spec.hCheckPos (v idx)
    let c := ucSplitRight spec.hCheckPos (v idx)
    let v0 := updateFinVec v idx (ucPairFin p c0)
    let eng0 := hybridConcurrentEngine idx.val proto cl.honestShares idealSignOracle sim (mkReal v0) (mkSim v0)
    let stInit := initConcurrentExecState Q_s (PSum R2St SimR2) (PSum R3St (SimR3 × ByteArray))
      cl.tsig cl.honestWal cl.maskSessionCursor
    match obsConcurrentSlotPreCut eng0 A idx numSteps stInit advSt with
    | none => false
    | some (req, h2, c2) => spec.badCheck req h2 c2 c
  have hBadSlice : ∀ (idx : Fin Q_s) (v : Fin Q_s → Fin cardS),
      finSum cardS (fun x => if bad idx (updateFinVec v idx x) then 1 else 0) ≤
        cardPad * epsCheck := by
    intro idx v
    change finSum (cardPad * cardCheck) _ ≤ _
    rw [finSum_ucPairFin]
    have hInner : ∀ p : Fin cardPad,
        finSum cardCheck (fun c => if bad idx (updateFinVec v idx (ucPairFin p c)) then 1 else 0) ≤
          epsCheck := by
      intro p
      let v0 := updateFinVec v idx (ucPairFin p c0)
      let eng0 := hybridConcurrentEngine idx.val proto cl.honestShares idealSignOracle sim (mkReal v0) (mkSim v0)
      let stInit := initConcurrentExecState Q_s (PSum R2St SimR2) (PSum R3St (SimR3 × ByteArray))
        cl.tsig cl.honestWal cl.maskSessionCursor
      have hSameBad : ∀ c : Fin cardCheck,
          bad idx (updateFinVec v idx (ucPairFin p c)) =
            match obsConcurrentSlotPreCut eng0 A idx numSteps stInit advSt with
            | none => false
            | some (req, h2, c2) => spec.badCheck req h2 c2 c := by
        intro c
        dsimp only [bad]
        rw [updateFinVec_same, ucSplitLeft_pair spec.hCheckPos,
            ucSplitRight_pair spec.hCheckPos, updateFinVec_twice]
      rw [finSum_congr (fun c => by rw [hSameBad c])]
      cases obsConcurrentSlotPreCut eng0 A idx numSteps stInit advSt with
      | none =>
        simp only [Bool.false_eq_true, ↓reduceIte, finSum_const]
        omega
      | some args =>
        rcases args with ⟨req, h2, c2⟩
        exact spec.hBadCheckBound req h2 c2
    exact Nat.le_trans (finSum_le_finSum hInner) (by rw [finSum_const]; exact Nat.le_refl _)
  have hAgree : ∀ (idx : Fin Q_s) (v : Fin Q_s → Fin cardS),
      bad idx v = false →
      hybrids idx.val (Nat.le_of_lt idx.isLt) v =
        hybrids (idx.val + 1) idx.isLt (updateFinVec v idx (bijCoord.toFun (v idx))) := by
    intro idx v hBadFalse
    let p := ucSplitLeft spec.hCheckPos (v idx)
    let c := ucSplitRight spec.hCheckPos (v idx)
    let v0 := updateFinVec v idx (ucPairFin p c0)
    let v1 := updateFinVec v idx (bijCoord.toFun (v idx))
    let eng0 := hybridConcurrentEngine idx.val proto cl.honestShares idealSignOracle sim (mkReal v0) (mkSim v0)
    let engR := hybridConcurrentEngine idx.val proto cl.honestShares idealSignOracle sim (mkReal v) (mkSim v)
    let engS := hybridConcurrentEngine (idx.val + 1) proto cl.honestShares idealSignOracle sim (mkReal v1) (mkSim v1)
    have hMkRealIdx : mkReal v idx = spec.realTapeOf p c := rfl
    have hMkReal0Idx : mkReal v0 idx = spec.realTapeOf p c0 := by
      dsimp only [mkReal, v0]
      rw [updateFinVec_same, ucSplitLeft_pair spec.hCheckPos, ucSplitRight_pair spec.hCheckPos]
    have hMkSim1Idx : mkSim v1 idx = spec.simTapeOf (spec.padBij.toFun p) c := by
      dsimp only [mkSim, v1, bijCoord, liftPadCheckEquiv]
      rw [updateFinVec_same, ucSplitLeft_pair spec.hCheckPos, ucSplitRight_pair spec.hCheckPos]
    have hOtherEng : ∀ (j : Fin Q_s), j ≠ idx →
        (eng0.slotRound1 j = engR.slotRound1 j ∧ engR.slotRound1 j = engS.slotRound1 j) ∧
        (eng0.slotRound2 j = engR.slotRound2 j ∧ engR.slotRound2 j = engS.slotRound2 j) ∧
        (eng0.slotRound3 j = engR.slotRound3 j ∧ engR.slotRound3 j = engS.slotRound3 j) := by
      intro j hjNe
      have hjValNe : j.val ≠ idx.val := fun he => hjNe (Fin.ext he)
      have hLtSame : (j.val < idx.val) ↔ (j.val < idx.val + 1) :=
        ⟨fun h => Nat.lt_succ_of_lt h, fun h => Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) hjValNe⟩
      have hV0j : v0 j = v j := updateFinVec_other v idx j _ hjNe
      have hV1j : v1 j = v j := updateFinVec_other v idx j _ hjNe
      have hMR0 : mkReal v0 j = mkReal v j := by dsimp only [mkReal]; rw [hV0j]
      have hMR1 : mkReal v1 j = mkReal v j := by dsimp only [mkReal]; rw [hV1j]
      have hMS0 : mkSim v0 j = mkSim v j := by dsimp only [mkSim]; rw [hV0j]
      have hMS1 : mkSim v1 j = mkSim v j := by dsimp only [mkSim]; rw [hV1j]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · funext pk' corr' req' cur'
        dsimp only [eng0, engR, hybridConcurrentEngine]
        rw [hMR0, hMS0]
      · funext pk' corr' req' cur'
        dsimp only [engR, engS, hybridConcurrentEngine]
        by_cases hLt : j.val < idx.val
        · have hLt1 : j.val < idx.val + 1 := hLtSame.mp hLt
          simp only [hLt, hLt1, ↓reduceIte, hMS1]
        · have hLt1 : ¬ (j.val < idx.val + 1) := fun h1 => hLt (hLtSame.mpr h1)
          simp only [hLt, hLt1, ↓reduceIte, hMR1]
      · funext pk' corr' req' st2'
        dsimp only [eng0, engR, hybridConcurrentEngine]; rw [hMR0, hMS0]
      · funext pk' corr' req' st2'
        dsimp only [engR, engS, hybridConcurrentEngine]; rw [hMR1, hMS1]
      · funext pk' corr' req' st3'
        dsimp only [eng0, engR, hybridConcurrentEngine]; rw [hMR0, hMS0]
      · funext pk' corr' req' st3'
        dsimp only [engR, engS, hybridConcurrentEngine]; rw [hMR1, hMS1]
    -- Phase B: once `idx < allocatedSlots` and slot `idx` is no longer in `afterR1`, `engR` and `engS` step identically.
    have hPostPreCut : ∀ (m : Nat)
        (st : ConcurrentExecState PK Q_s (PSum R2St SimR2) (PSum R3St (SimR3 × ByteArray)))
        (slotsS : Fin Q_s → ConcurrentSlotPhase (PSum R2St SimR2) (PSum R3St (SimR3 × ByteArray)))
        (a : AdvState),
        st.tsig.pk = cl.tsig.pk →
        st.tsig.corruptParties = cl.tsig.corruptParties →
        idx.val < st.allocatedSlots →
        (∀ j : Fin Q_s, j ≠ idx → st.slots j = slotsS j) →
        ((st.slots idx = .closed ∧ slotsS idx = .closed) ∨
         (st.slots idx = .unallocated ∧ slotsS idx = .unallocated) ∨
         (∃ ep md req h1 c1 h2 c2 r3 s3,
            st.slots idx = .afterR2 ep md req h1 c1 h2 c2 (.inl r3) ∧
            slotsS idx = .afterR2 ep md req h1 c1 h2 c2 (.inr (s3, idealSignOracle req)) ∧
            spec.RelR3 p c req r3 s3)) →
        (execConcurrentSteps engR A m st a).2 =
          (execConcurrentSteps engS A m { st with slots := slotsS } a).2 := by
      intro m
      induction m with
      | zero => intros; rfl
      | succ m ih =>
        intro st slotsS a hPkE hCorrE hIdxAlloc hSlotsNe hSlotIdx
        simp only [execConcurrentSteps]
        unfold execConcurrentStep
        dsimp only
        cases (A.chooseNextStep a).1 with
        | startRound1 req =>
          dsimp only
          split
          · exact ih st slotsS _ hPkE hCorrE hIdxAlloc hSlotsNe hSlotIdx
          · split
            · next hSlot =>
              cases validThresholdApproval st.tsig req.honestApprovers
              · exact ih _ slotsS _ hPkE hCorrE hIdxAlloc hSlotsNe hSlotIdx
              · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                have hEDig : engR.pkDigestOf = proto.pkDigestOf ∧ engS.pkDigestOf = proto.pkDigestOf ∧
                    engR.msgDigestOf = proto.msgDigestOf ∧ engS.msgDigestOf = proto.msgDigestOf :=
                  ⟨rfl, rfl, rfl, rfl⟩
                rw [hEDig.1, hEDig.2.1, hEDig.2.2.1, hEDig.2.2.2]
                cases walPreSignStep st.honestWal (proto.pkDigestOf st.tsig.pk) req.reqEpoch (proto.msgDigestOf req) with
                | err _ _ =>
                  exact ih _ slotsS _ hPkE hCorrE hIdxAlloc hSlotsNe hSlotIdx
                | ok wal' auth =>
                  dsimp only
                  cases auth with
                  | replayCached _ =>
                    exact ih _ slotsS _ hPkE hCorrE hIdxAlloc hSlotsNe hSlotIdx
                  | authorizedFresh ep =>
                    dsimp only
                    let newSlot : Fin Q_s := ⟨st.allocatedSlots, hSlot⟩
                    have hNewNeIdx : newSlot ≠ idx := by
                      intro he
                      have hv := congrArg Fin.val he
                      dsimp only [newSlot] at hv
                      omega
                    have hR1Eq := (hOtherEng ⟨st.allocatedSlots, hSlot⟩ hNewNeIdx).1.2
                    simp only [hR1Eq]
                    have hV1Same : ∀ x h1 c1, engR.slotVerify1 newSlot st.tsig.pk req x h1 c1 =
                        engS.slotVerify1 newSlot st.tsig.pk req x h1 c1 := fun _ _ _ => rfl
                    rw [hV1Same]
                    cases engS.slotVerify1 newSlot st.tsig.pk req _ _ _ with
                    | inl _ =>
                      exact ih _ slotsS _ hPkE hCorrE (by dsimp only; omega) hSlotsNe hSlotIdx
                    | inr r2Init =>
                      refine ih _ (updateConcurrentSlot slotsS newSlot _) _ hPkE hCorrE (by dsimp only; omega) ?_ ?_
                      · intro j hjNe
                        dsimp only
                        by_cases hJNew : j = newSlot
                        · subst hJNew; rw [updateConcurrentSlot_same, updateConcurrentSlot_same]
                        · rw [updateConcurrentSlot_ne _ _ j _ hJNew, updateConcurrentSlot_ne _ _ j _ hJNew]
                          exact hSlotsNe j hjNe
                      · dsimp only
                        rw [updateConcurrentSlot_ne _ _ idx _ hNewNeIdx.symm,
                            updateConcurrentSlot_ne _ _ idx _ hNewNeIdx.symm]
                        exact hSlotIdx
            · exact ih _ slotsS _ hPkE hCorrE hIdxAlloc hSlotsNe hSlotIdx
        | stepRound2 sid =>
          dsimp only
          cases lookupSidSlot sid st.sidMap with
          | none => exact ih st slotsS _ hPkE hCorrE hIdxAlloc hSlotsNe hSlotIdx
          | some slot =>
            dsimp only
            by_cases hSlIdx : slot = idx
            · subst hSlIdx
              rcases hSlotIdx with ⟨hC1, hC2⟩ | ⟨hU1, hU2⟩ | ⟨ep, md, rq, h1, c1, h2, c2, r3, s3, hA1, hA2, hRel⟩
              · rw [hC1, hC2]; exact ih st slotsS _ hPkE hCorrE hIdxAlloc hSlotsNe (.inl ⟨hC1, hC2⟩)
              · rw [hU1, hU2]; exact ih st slotsS _ hPkE hCorrE hIdxAlloc hSlotsNe (.inr (.inl ⟨hU1, hU2⟩))
              · rw [hA1, hA2]
                exact ih st slotsS _ hPkE hCorrE hIdxAlloc hSlotsNe
                  (.inr (.inr ⟨ep, md, rq, h1, c1, h2, c2, r3, s3, hA1, hA2, hRel⟩))
            · rw [← hSlotsNe slot hSlIdx]
              cases hPh : st.slots slot with
              | unallocated => exact ih st slotsS _ hPkE hCorrE hIdxAlloc hSlotsNe hSlotIdx
              | afterR2 _ _ _ _ _ _ _ _ => exact ih st slotsS _ hPkE hCorrE hIdxAlloc hSlotsNe hSlotIdx
              | closed => exact ih st slotsS _ hPkE hCorrE hIdxAlloc hSlotsNe hSlotIdx
              | afterR1 ep md rq h1 c1 st2 =>
                dsimp only
                have hUpdOther : ∀ ph,
                    (∀ j, j ≠ idx → updateConcurrentSlot st.slots slot ph j = updateConcurrentSlot slotsS slot ph j) := by
                  intro ph j hjNe
                  by_cases hJ : j = slot
                  · subst hJ; rw [updateConcurrentSlot_same, updateConcurrentSlot_same]
                  · rw [updateConcurrentSlot_ne _ _ j _ hJ, updateConcurrentSlot_ne _ _ j _ hJ]
                    exact hSlotsNe j hjNe
                cases st.honestWal.poisoned
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  simp only [(hOtherEng slot hSlIdx).2.1.2]
                  have hPCSame : ∀ x h2 c2, engR.slotPreCut slot st.tsig.pk rq x h2 c2 =
                      engS.slotPreCut slot st.tsig.pk rq x h2 c2 := fun _ _ _ => rfl
                  rw [hPCSame]
                  cases engS.slotPreCut slot st.tsig.pk rq _ _ _ with
                  | inl _ =>
                    refine ih _ (updateConcurrentSlot slotsS slot .closed) _ hPkE hCorrE hIdxAlloc (hUpdOther .closed) ?_
                    dsimp only
                    rw [updateConcurrentSlot_ne _ _ idx _ (Ne.symm hSlIdx),
                        updateConcurrentSlot_ne _ _ idx _ (Ne.symm hSlIdx)]
                    exact hSlotIdx
                  | inr r3New =>
                    refine ih _ (updateConcurrentSlot slotsS slot _) _ hPkE hCorrE hIdxAlloc (hUpdOther _) ?_
                    dsimp only
                    rw [updateConcurrentSlot_ne _ _ idx _ (Ne.symm hSlIdx),
                        updateConcurrentSlot_ne _ _ idx _ (Ne.symm hSlIdx)]
                    exact hSlotIdx
                · simp only [↓reduceIte]
                  refine ih _ (updateConcurrentSlot slotsS slot .closed) _ hPkE hCorrE hIdxAlloc (hUpdOther .closed) ?_
                  dsimp only
                  rw [updateConcurrentSlot_ne _ _ idx _ (Ne.symm hSlIdx),
                      updateConcurrentSlot_ne _ _ idx _ (Ne.symm hSlIdx)]
                  exact hSlotIdx
        | stepRound3 sid =>
          dsimp only
          cases lookupSidSlot sid st.sidMap with
          | none => exact ih st slotsS _ hPkE hCorrE hIdxAlloc hSlotsNe hSlotIdx
          | some slot =>
            dsimp only
            by_cases hSlIdx : slot = idx
            · subst hSlIdx
              rcases hSlotIdx with ⟨hC1, hC2⟩ | ⟨hU1, hU2⟩ | ⟨ep, md, rq, h1, c1, h2, c2, r3, s3, hA1, hA2, hRel3⟩
              · rw [hC1, hC2]; exact ih st slotsS _ hPkE hCorrE hIdxAlloc hSlotsNe (.inl ⟨hC1, hC2⟩)
              · rw [hU1, hU2]; exact ih st slotsS _ hPkE hCorrE hIdxAlloc hSlotsNe (.inr (.inl ⟨hU1, hU2⟩))
              · rw [hA1, hA2]
                dsimp only
                have hClosedOther : ∀ j, j ≠ slot →
                    updateConcurrentSlot st.slots slot .closed j = updateConcurrentSlot slotsS slot .closed j := by
                  intro j hjNe
                  rw [updateConcurrentSlot_ne _ _ j _ hjNe, updateConcurrentSlot_ne _ _ j _ hjNe]
                  exact hSlotsNe j hjNe
                have hClosedIdx :
                    updateConcurrentSlot st.slots slot .closed slot = .closed ∧
                    updateConcurrentSlot slotsS slot .closed slot = .closed :=
                  ⟨updateConcurrentSlot_same _ _ _, updateConcurrentSlot_same _ _ _⟩
                cases st.honestWal.poisoned
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  have hR3Spec := spec.hRound3 p c rq r3 s3 hRel3
                  dsimp only [engR, engS, hybridConcurrentEngine]
                  rw [hPkE, hCorrE, hMkRealIdx, hMkSim1Idx]
                  rcases hR3R : proto.honestRound3 cl.tsig.pk cl.tsig.corruptParties rq r3 cl.honestShares (spec.realTapeOf p c) with ⟨wR3, r3'⟩
                  rcases hR3S : sim.simRound3 cl.tsig.pk cl.tsig.corruptParties rq s3 (idealSignOracle rq) (spec.simTapeOf (spec.padBij.toFun p) c) with ⟨wS3, s3'⟩
                  rw [hR3R, hR3S] at hR3Spec
                  obtain ⟨hW3Eq, hRel3'⟩ := hR3Spec
                  subst hW3Eq
                  simp only [hR3R, hR3S]
                  have hFinEq := fun c3 => spec.hFinalize p c rq r3' s3' wR3 c3 hRel3'
                  simp only [hFinEq]
                  cases sim.finalizeIdealCut cl.tsig.pk rq s3' (idealSignOracle rq) wR3 _ <;>
                    exact ih _ (updateConcurrentSlot slotsS slot .closed) _ hPkE hCorrE hIdxAlloc hClosedOther (.inl hClosedIdx)
                · simp only [↓reduceIte]
                  exact ih _ (updateConcurrentSlot slotsS slot .closed) _ hPkE hCorrE hIdxAlloc hClosedOther (.inl hClosedIdx)
            · rw [← hSlotsNe slot hSlIdx]
              cases hPh : st.slots slot with
              | unallocated => exact ih st slotsS _ hPkE hCorrE hIdxAlloc hSlotsNe hSlotIdx
              | afterR1 _ _ _ _ _ _ => exact ih st slotsS _ hPkE hCorrE hIdxAlloc hSlotsNe hSlotIdx
              | closed => exact ih st slotsS _ hPkE hCorrE hIdxAlloc hSlotsNe hSlotIdx
              | afterR2 ep md rq h1 c1 h2 c2 st3 =>
                dsimp only
                have hClosedOther : ∀ j, j ≠ idx →
                    updateConcurrentSlot st.slots slot .closed j = updateConcurrentSlot slotsS slot .closed j := by
                  intro j hjNe
                  by_cases hJ : j = slot
                  · subst hJ; rw [updateConcurrentSlot_same, updateConcurrentSlot_same]
                  · rw [updateConcurrentSlot_ne _ _ j _ hJ, updateConcurrentSlot_ne _ _ j _ hJ]
                    exact hSlotsNe j hjNe
                cases st.honestWal.poisoned
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  simp only [(hOtherEng slot hSlIdx).2.2.2]
                  have hFinSame : ∀ x h3 c3, engR.slotFinalize slot st.tsig.pk rq x h3 c3 =
                      engS.slotFinalize slot st.tsig.pk rq x h3 c3 := fun _ _ _ => rfl
                  rw [hFinSame]
                  cases engS.slotFinalize slot st.tsig.pk rq _ _ _ <;>
                    (refine ih _ (updateConcurrentSlot slotsS slot .closed) _ hPkE hCorrE hIdxAlloc hClosedOther ?_;
                     dsimp only;
                     rw [updateConcurrentSlot_ne _ _ idx _ (Ne.symm hSlIdx),
                         updateConcurrentSlot_ne _ _ idx _ (Ne.symm hSlIdx)];
                     exact hSlotIdx)
                · simp only [↓reduceIte]
                  refine ih _ (updateConcurrentSlot slotsS slot .closed) _ hPkE hCorrE hIdxAlloc hClosedOther ?_
                  dsimp only
                  rw [updateConcurrentSlot_ne _ _ idx _ (Ne.symm hSlIdx),
                      updateConcurrentSlot_ne _ _ idx _ (Ne.symm hSlIdx)]
                  exact hSlotIdx
    -- Phase A: before slot `idx` executes `preCutBarrier`, `({ st with slots := slots0 }, st, { st with slots := slotsS })` step in lockstep.
    have hPrePreCut : ∀ (m : Nat)
        (st : ConcurrentExecState PK Q_s (PSum R2St SimR2) (PSum R3St (SimR3 × ByteArray)))
        (slots0 slotsS : Fin Q_s → ConcurrentSlotPhase (PSum R2St SimR2) (PSum R3St (SimR3 × ByteArray)))
        (a : AdvState),
        st.tsig.pk = cl.tsig.pk →
        st.tsig.corruptParties = cl.tsig.corruptParties →
        (∀ j : Fin Q_s, j ≠ idx → slots0 j = st.slots j ∧ st.slots j = slotsS j) →
        (∀ j : Fin Q_s, st.allocatedSlots ≤ j.val → st.slots j = .unallocated) →
        ((slots0 idx = .unallocated ∧ st.slots idx = .unallocated ∧ slotsS idx = .unallocated) ∨
         (idx.val < st.allocatedSlots ∧
          ∃ ep md rq h1 c1 r2_0 r2_c s2,
            slots0 idx = .afterR1 ep md rq h1 c1 (.inl r2_0) ∧
            st.slots idx = .afterR1 ep md rq h1 c1 (.inl r2_c) ∧
            slotsS idx = .afterR1 ep md rq h1 c1 (.inr s2) ∧
            spec.RelR2 p c0 rq r2_0 s2 ∧
            spec.RelR2 p c rq r2_c s2)) →
        (match obsConcurrentSlotPreCut eng0 A idx m { st with slots := slots0 } a with
         | none => false
         | some (rq, h2, c2) => spec.badCheck rq h2 c2 c) = false →
        (execConcurrentSteps engR A m st a).2 =
          (execConcurrentSteps engS A m { st with slots := slotsS } a).2 := by
      intro m
      induction m with
      | zero => intros; rfl
      | succ m ih =>
        intro st slots0 slotsS a hPkE hCorrE hSlNe hUnalloc hIdxSt hObsFalse
        simp only [execConcurrentSteps]
        cases hCmd : (A.chooseNextStep a).1 with
        | startRound1 req =>
          have hObsStep : obsConcurrentSlotPreCut eng0 A idx (m + 1) { st with slots := slots0 } a =
              let (st0', a') := execConcurrentStep eng0 A { st with slots := slots0 } a
              obsConcurrentSlotPreCut eng0 A idx m st0' a' := by
            conv => lhs; unfold obsConcurrentSlotPreCut
            simp only [hCmd]
          rw [hObsStep] at hObsFalse
          unfold execConcurrentStep at hObsFalse ⊢
          simp only [hCmd] at hObsFalse ⊢
          split
          · next hDup =>
            simp only [hDup, ↓reduceIte] at hObsFalse
            exact ih st slots0 slotsS _ hPkE hCorrE hSlNe hUnalloc hIdxSt hObsFalse
          · next hNotDup =>
            simp only [hNotDup, Bool.false_eq_true, ↓reduceIte] at hObsFalse
            split
            · next hSlot =>
              simp only [hSlot, ↓reduceDIte] at hObsFalse
              cases hQuo : validThresholdApproval st.tsig req.honestApprovers
              · simp only [hQuo, Bool.not_false, ↓reduceIte] at hObsFalse
                exact ih _ slots0 slotsS _ hPkE hCorrE hSlNe hUnalloc hIdxSt hObsFalse
              · simp only [hQuo, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hObsFalse ⊢
                have hEDig : eng0.pkDigestOf = proto.pkDigestOf ∧ engR.pkDigestOf = proto.pkDigestOf ∧
                    engS.pkDigestOf = proto.pkDigestOf ∧ eng0.msgDigestOf = proto.msgDigestOf ∧
                    engR.msgDigestOf = proto.msgDigestOf ∧ engS.msgDigestOf = proto.msgDigestOf :=
                  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
                rw [hEDig.1, hEDig.2.2.2.1] at hObsFalse
                rw [hEDig.2.1, hEDig.2.2.1, hEDig.2.2.2.2.1, hEDig.2.2.2.2.2]
                cases hWalStep : walPreSignStep st.honestWal (proto.pkDigestOf st.tsig.pk) req.reqEpoch (proto.msgDigestOf req) with
                | err _ _ =>
                  rw [hWalStep] at hObsFalse
                  exact ih _ slots0 slotsS _ hPkE hCorrE hSlNe hUnalloc hIdxSt hObsFalse
                | ok wal' auth =>
                  rw [hWalStep] at hObsFalse
                  dsimp only at hObsFalse ⊢
                  cases auth with
                  | replayCached _ =>
                    exact ih _ slots0 slotsS _ hPkE hCorrE hSlNe hUnalloc hIdxSt hObsFalse
                  | authorizedFresh ep =>
                    dsimp only at hObsFalse ⊢
                    let newSlot : Fin Q_s := ⟨st.allocatedSlots, hSlot⟩
                    have hUnallocNext : ∀ (ph : _),
                        (∀ j, st.allocatedSlots + 1 ≤ j.val → updateConcurrentSlot st.slots newSlot ph j = .unallocated) := by
                      intro ph j hj
                      have hNe : j ≠ newSlot := by
                        intro he; have hv := congrArg Fin.val he; dsimp only [newSlot] at hv; omega
                      rw [updateConcurrentSlot_ne _ _ j _ hNe]
                      exact hUnalloc j (Nat.le_of_succ_le hj)
                    by_cases hNewIdx : newSlot = idx
                    · -- Allocating slot `idx` itself!
                      have hAllocEqIdx : st.allocatedSlots = idx.val := congrArg Fin.val hNewIdx
                      have hNew0 : (⟨st.allocatedSlots, hSlot⟩ : Fin Q_s) = idx := hNewIdx
                      simp only [hNew0] at hObsFalse ⊢
                      have hSimC0Eq : spec.simTapeOf (spec.padBij.toFun p) c0 =
                          spec.simTapeOf (spec.padBij.toFun p) c := spec.hSimTapeIndep _ _ _
                      have hR1_0 := spec.hRound1 req st.maskSessionCursor p c0
                      have hR1_c := spec.hRound1 req st.maskSessionCursor p c
                      rw [hSimC0Eq] at hR1_0
                      dsimp only [eng0, engR, engS, hybridConcurrentEngine] at hObsFalse ⊢
                      have hNotLt0 : ¬ (idx.val < idx.val) := Nat.lt_irrefl _
                      have hLt1 : idx.val < idx.val + 1 := Nat.lt_succ_self _
                      simp only [hNotLt0, hLt1, ↓reduceIte,
                        hPkE, hCorrE, hMkReal0Idx, hMkRealIdx, hMkSim1Idx] at hObsFalse ⊢
                      rcases hPR0 : proto.honestRound1 cl.tsig.pk cl.tsig.corruptParties req st.maskSessionCursor cl.honestShares (spec.realTapeOf p c0) with ⟨w0, r1_0⟩
                      rcases hPRc : proto.honestRound1 cl.tsig.pk cl.tsig.corruptParties req st.maskSessionCursor cl.honestShares (spec.realTapeOf p c) with ⟨wc, r1_c⟩
                      rcases hPS  : sim.simRound1 cl.tsig.pk cl.tsig.corruptParties req st.maskSessionCursor (spec.simTapeOf (spec.padBij.toFun p) c) with ⟨wS, s1⟩
                      rw [hPR0, hPS] at hR1_0
                      rw [hPRc, hPS] at hR1_c
                      obtain ⟨hW0Eq, hRel1_0⟩ := hR1_0
                      obtain ⟨hWcEq, hRel1_c⟩ := hR1_c
                      subst hW0Eq
                      subst wc
                      simp only [hPR0, hPRc, hPS] at hObsFalse ⊢
                      rcases spec.hVerify1 p c0 req r1_0 s1 w0
                          (cl.tsig.corruptParties.map (fun c' => (c', (A.rushRound1 (A.chooseNextStep a).2 req.sessionId w0).1 c'))) hRel1_0 with
                        ⟨err0, hV1_0, hVS_0⟩ | ⟨r2_0, s2_0, hV1_0, hVS_0, hRel2_0⟩
                      · rcases spec.hVerify1 p c req r1_c s1 w0
                            (cl.tsig.corruptParties.map (fun c' => (c', (A.rushRound1 (A.chooseNextStep a).2 req.sessionId w0).1 c'))) hRel1_c with
                          ⟨errc, hV1_c, hVS_c⟩ | ⟨_, _, _, hVS_c, _⟩
                        · have hErrEq : errc = err0 := by rw [hVS_0] at hVS_c; exact (PSum.inl.inj hVS_c).symm
                          subst errc
                          simp only [hV1_0] at hObsFalse
                          simp only [hV1_c, hVS_0]
                          exact hPostPreCut m _ slotsS _ hPkE hCorrE
                            (by dsimp only; omega) (fun j hj => (hSlNe j hj).2)
                            (.inr (.inl ⟨by
                              rcases hIdxSt with ⟨_, hU, _⟩ | ⟨hLtC, _⟩
                              · exact hU
                              · exact absurd hLtC (by omega), by
                              rcases hIdxSt with ⟨_, _, hU⟩ | ⟨hLtC, _⟩
                              · exact hU
                              · exact absurd hLtC (by omega)⟩))
                        · rw [hVS_0] at hVS_c; cases hVS_c
                      · rcases spec.hVerify1 p c req r1_c s1 w0
                            (cl.tsig.corruptParties.map (fun c' => (c', (A.rushRound1 (A.chooseNextStep a).2 req.sessionId w0).1 c'))) hRel1_c with
                          ⟨_, _, hVS_c⟩ | ⟨r2_c, s2_c, hV1_c, hVS_c, hRel2_c⟩
                        · rw [hVS_0] at hVS_c; cases hVS_c
                        · have hS2Eq : s2_c = s2_0 := by rw [hVS_0] at hVS_c; exact (PSum.inr.inj hVS_c).symm
                          subst s2_c
                          simp only [hV1_0] at hObsFalse
                          simp only [hV1_c, hVS_0]
                          refine ih _
                            (updateConcurrentSlot slots0 idx (.afterR1 ep (proto.msgDigestOf req) req w0
                              (cl.tsig.corruptParties.map (fun c' => (c', (A.rushRound1 (A.chooseNextStep a).2 req.sessionId w0).1 c')))
                              (.inl r2_0)))
                            (updateConcurrentSlot slotsS idx _) _ hPkE hCorrE ?_ ?_ ?_ ?_
                          · intro j hjNe
                            dsimp only
                            rw [updateConcurrentSlot_ne _ _ j _ hjNe,
                                updateConcurrentSlot_ne _ _ j _ hjNe,
                                updateConcurrentSlot_ne _ _ j _ hjNe]
                            exact hSlNe j hjNe
                          · intro j hj
                            dsimp only at hj ⊢
                            have hNe : j ≠ idx := by intro he; subst he; omega
                            rw [updateConcurrentSlot_ne _ _ j _ hNe]
                            exact hUnalloc j (Nat.le_of_succ_le hj)
                          · right
                            dsimp only
                            refine ⟨by omega, ep, _, req, w0, _, r2_0, r2_c, s2_0,
                              updateConcurrentSlot_same _ _ _,
                              updateConcurrentSlot_same _ _ _,
                              updateConcurrentSlot_same _ _ _,
                              hRel2_0, hRel2_c⟩
                          · exact hObsFalse
                    · -- Allocating some other slot `newSlot ≠ idx`
                      obtain ⟨⟨hR1_0R, hR1_RS⟩, _, _⟩ := hOtherEng ⟨st.allocatedSlots, hSlot⟩ hNewIdx
                      simp only [hR1_0R, hR1_RS] at hObsFalse
                      simp only [hR1_RS]
                      have hV1Eq0 : ∀ x h1 c1,
                          eng0.slotVerify1 ⟨st.allocatedSlots, hSlot⟩ st.tsig.pk req x h1 c1 =
                          engS.slotVerify1 ⟨st.allocatedSlots, hSlot⟩ st.tsig.pk req x h1 c1 := fun _ _ _ => rfl
                      have hV1EqR : ∀ x h1 c1,
                          engR.slotVerify1 ⟨st.allocatedSlots, hSlot⟩ st.tsig.pk req x h1 c1 =
                          engS.slotVerify1 ⟨st.allocatedSlots, hSlot⟩ st.tsig.pk req x h1 c1 := fun _ _ _ => rfl
                      simp only [hV1Eq0] at hObsFalse
                      simp only [hV1EqR]
                      generalize engS.slotVerify1 ⟨st.allocatedSlots, hSlot⟩ st.tsig.pk req _ _ _ = ver
                        at hObsFalse ⊢
                      cases ver with
                      | inl _ =>
                        dsimp only at hObsFalse ⊢
                        refine ih _ slots0 slotsS _ hPkE hCorrE hSlNe
                          (fun j hj => hUnalloc j (Nat.le_of_succ_le hj)) ?_ hObsFalse
                        rcases hIdxSt with hU | ⟨hLt, hEx⟩
                        · exact .inl hU
                        · exact .inr ⟨Nat.lt_succ_of_lt hLt, hEx⟩
                      | inr r2New =>
                        dsimp only at hObsFalse ⊢
                        refine ih _ (updateConcurrentSlot slots0 newSlot _) (updateConcurrentSlot slotsS newSlot _) _
                          hPkE hCorrE ?_ ?_ ?_ hObsFalse
                        · intro j hjNe
                          dsimp only
                          by_cases hJ : j = newSlot
                          · subst hJ
                            rw [updateConcurrentSlot_same, updateConcurrentSlot_same, updateConcurrentSlot_same]
                            exact ⟨rfl, rfl⟩
                          · rw [updateConcurrentSlot_ne _ _ j _ hJ,
                                updateConcurrentSlot_ne _ _ j _ hJ,
                                updateConcurrentSlot_ne _ _ j _ hJ]
                            exact hSlNe j hjNe
                        · exact hUnallocNext _
                        · dsimp only
                          rw [updateConcurrentSlot_ne _ _ idx _ (Ne.symm hNewIdx),
                              updateConcurrentSlot_ne _ _ idx _ (Ne.symm hNewIdx),
                              updateConcurrentSlot_ne _ _ idx _ (Ne.symm hNewIdx)]
                          rcases hIdxSt with hU | ⟨hLt, hEx⟩
                          · exact .inl hU
                          · exact .inr ⟨Nat.lt_succ_of_lt hLt, hEx⟩
            · next hNoSlot =>
              simp only [hNoSlot, ↓reduceDIte] at hObsFalse
              exact ih _ slots0 slotsS _ hPkE hCorrE hSlNe hUnalloc hIdxSt hObsFalse
        | stepRound2 sid =>
          conv at hObsFalse => arg 1; unfold obsConcurrentSlotPreCut
          simp only [hCmd] at hObsFalse
          unfold execConcurrentStep
          simp only [hCmd]
          cases hLook : lookupSidSlot sid st.sidMap with
          | none =>
            rw [hLook] at hObsFalse
            dsimp only [execConcurrentStep] at hObsFalse
            simp only [hCmd, hLook] at hObsFalse
            exact ih st slots0 slotsS _ hPkE hCorrE hSlNe hUnalloc hIdxSt hObsFalse
          | some slot =>
            dsimp only
            rw [hLook] at hObsFalse
            dsimp only at hObsFalse
            by_cases hSlIdx : slot = idx
            · subst hSlIdx
              rw [ite_eq_left rfl] at hObsFalse
              rcases hIdxSt with ⟨hU0, hUR, hUS⟩ |
                ⟨hIdxLt, ep, md, rq, h1, c1, r2_0, r2_c, s2, hA0, hAR, hAS, hRel2_0, hRel2_c⟩
              · rw [hU0] at hObsFalse
                rw [hUR, hUS]
                dsimp only [execConcurrentStep] at hObsFalse
                simp only [hCmd, hLook, hU0] at hObsFalse
                exact ih st slots0 slotsS _ hPkE hCorrE hSlNe hUnalloc (.inl ⟨hU0, hUR, hUS⟩) hObsFalse
              · rw [hA0] at hObsFalse
                rw [hAR, hAS]
                dsimp only at hObsFalse ⊢
                cases hPois : st.honestWal.poisoned
                · -- THE CRITICAL PRE-CUT BARRIER TRANSITION AT SLOT `slot = idx`!
                  simp only [hPois, Bool.false_eq_true, ↓reduceIte] at hObsFalse ⊢
                  have hSimC0Eq : spec.simTapeOf (spec.padBij.toFun p) c0 =
                      spec.simTapeOf (spec.padBij.toFun p) c := spec.hSimTapeIndep _ _ _
                  have hR2Spec0 := spec.hRound2 p c0 rq r2_0 s2 hRel2_0
                  have hR2Specc := spec.hRound2 p c rq r2_c s2 hRel2_c
                  rw [hSimC0Eq] at hR2Spec0
                  dsimp only [eng0, engR, engS, hybridConcurrentEngine] at hObsFalse ⊢
                  rw [hPkE, hCorrE, hMkReal0Idx] at hObsFalse
                  rw [hPkE, hCorrE, hMkRealIdx, hMkSim1Idx]
                  rcases hPR0 : proto.honestRound2 cl.tsig.pk cl.tsig.corruptParties rq r2_0 cl.honestShares (spec.realTapeOf p c0) with ⟨w2_0, r2'_0⟩
                  rcases hPRc : proto.honestRound2 cl.tsig.pk cl.tsig.corruptParties rq r2_c cl.honestShares (spec.realTapeOf p c) with ⟨w2_c, r2'_c⟩
                  rcases hPS  : sim.simRound2 cl.tsig.pk cl.tsig.corruptParties rq s2 (spec.simTapeOf (spec.padBij.toFun p) c) with ⟨w2_S, s2'⟩
                  rw [hPR0, hPS] at hR2Spec0
                  rw [hPRc, hPS] at hR2Specc
                  obtain ⟨hW2_0, _⟩ := hR2Spec0
                  obtain ⟨hW2_c, hRel2'_c⟩ := hR2Specc
                  subst hW2_0
                  subst w2_c
                  simp only [hPR0, hPRc, hPS] at hObsFalse ⊢
                  rcases spec.hPreCut p c rq r2'_c s2' w2_0 _ hRel2'_c hObsFalse with
                    ⟨errB, hPCR, hPCS⟩ | ⟨r3Init, s3Init, hPCR, hPCS, hRel3⟩
                  · simp only [hPCR, hPCS]
                    exact hPostPreCut m _ (updateConcurrentSlot slotsS slot .closed) _ hPkE hCorrE hIdxLt
                      (fun j hj => by
                        dsimp only
                        rw [updateConcurrentSlot_ne _ _ j _ hj, updateConcurrentSlot_ne _ _ j _ hj]
                        exact (hSlNe j hj).2)
                      (.inl ⟨updateConcurrentSlot_same _ _ _, updateConcurrentSlot_same _ _ _⟩)
                  · simp only [hPCR, hPCS]
                    exact hPostPreCut m _ (updateConcurrentSlot slotsS slot _) _ rfl rfl hIdxLt
                      (fun j hj => by
                        dsimp only
                        rw [updateConcurrentSlot_ne _ _ j _ hj, updateConcurrentSlot_ne _ _ j _ hj]
                        exact (hSlNe j hj).2)
                      (.inr (.inr ⟨ep, md, rq, h1, c1, w2_0, _, r3Init, s3Init,
                        updateConcurrentSlot_same _ _ _, updateConcurrentSlot_same _ _ _, hRel3⟩))
                · -- Poisoned before `preCutBarrier`: closes into Phase B!
                  simp only [hPois, ↓reduceIte] at hObsFalse ⊢
                  exact hPostPreCut m _ (updateConcurrentSlot slotsS slot .closed) _ hPkE hCorrE hIdxLt
                    (fun j hj => by
                      dsimp only
                      rw [updateConcurrentSlot_ne _ _ j _ hj, updateConcurrentSlot_ne _ _ j _ hj]
                      exact (hSlNe j hj).2)
                    (.inl ⟨updateConcurrentSlot_same _ _ _, updateConcurrentSlot_same _ _ _⟩)
            · -- `stepRound2` on some other slot `slot ≠ idx`
              rw [ite_eq_right hSlIdx] at hObsFalse
              obtain ⟨hSl0R, hSlRS⟩ := hSlNe slot hSlIdx
              dsimp only [execConcurrentStep] at hObsFalse
              simp only [hCmd, hLook, hSl0R] at hObsFalse
              rw [← hSlRS]
              cases hPh : st.slots slot with
              | unallocated =>
                rw [hPh] at hObsFalse
                exact ih st slots0 slotsS _ hPkE hCorrE hSlNe hUnalloc hIdxSt hObsFalse
              | afterR2 _ _ _ _ _ _ _ _ =>
                rw [hPh] at hObsFalse
                exact ih st slots0 slotsS _ hPkE hCorrE hSlNe hUnalloc hIdxSt hObsFalse
              | closed =>
                rw [hPh] at hObsFalse
                exact ih st slots0 slotsS _ hPkE hCorrE hSlNe hUnalloc hIdxSt hObsFalse
              | afterR1 ep md rq h1 c1 st2 =>
                rw [hPh] at hObsFalse
                dsimp only at hObsFalse ⊢
                have hUpdOther : ∀ ph,
                    (∀ j, j ≠ idx →
                      updateConcurrentSlot slots0 slot ph j = updateConcurrentSlot st.slots slot ph j ∧
                      updateConcurrentSlot st.slots slot ph j = updateConcurrentSlot slotsS slot ph j) := by
                  intro ph j hjNe
                  by_cases hJ : j = slot
                  · subst hJ
                    rw [updateConcurrentSlot_same, updateConcurrentSlot_same, updateConcurrentSlot_same]
                    exact ⟨rfl, rfl⟩
                  · rw [updateConcurrentSlot_ne _ _ j _ hJ,
                        updateConcurrentSlot_ne _ _ j _ hJ,
                        updateConcurrentSlot_ne _ _ j _ hJ]
                    exact hSlNe j hjNe
                have hUnallocUpd : ∀ ph,
                    (∀ j, st.allocatedSlots ≤ j.val → updateConcurrentSlot st.slots slot ph j = .unallocated) := by
                  intro ph j hj
                  have hUnJ := hUnalloc j hj
                  by_cases hJ : j = slot
                  · subst hJ; rw [hUnJ] at hPh; cases hPh
                  · rw [updateConcurrentSlot_ne _ _ j _ hJ]; exact hUnJ
                cases hPois : st.honestWal.poisoned
                · simp only [hPois, Bool.false_eq_true, ↓reduceIte] at hObsFalse ⊢
                  obtain ⟨_, ⟨hR2_0R, hR2_RS⟩, _⟩ := hOtherEng slot hSlIdx
                  simp only [hR2_0R, hR2_RS] at hObsFalse
                  simp only [hR2_RS]
                  have hPC0 : ∀ x h2 c2, eng0.slotPreCut slot st.tsig.pk rq x h2 c2 =
                      engS.slotPreCut slot st.tsig.pk rq x h2 c2 := fun _ _ _ => rfl
                  have hPCR : ∀ x h2 c2, engR.slotPreCut slot st.tsig.pk rq x h2 c2 =
                      engS.slotPreCut slot st.tsig.pk rq x h2 c2 := fun _ _ _ => rfl
                  simp only [hPC0] at hObsFalse
                  simp only [hPCR]
                  generalize engS.slotPreCut slot st.tsig.pk rq _ _ _ = pc at hObsFalse ⊢
                  cases pc with
                  | inl _ =>
                    dsimp only at hObsFalse ⊢
                    refine ih _ (updateConcurrentSlot slots0 slot .closed) (updateConcurrentSlot slotsS slot .closed) _ hPkE hCorrE
                      (hUpdOther .closed) (hUnallocUpd .closed) ?_ hObsFalse
                    dsimp only
                    rw [updateConcurrentSlot_ne _ _ idx _ (Ne.symm hSlIdx),
                        updateConcurrentSlot_ne _ _ idx _ (Ne.symm hSlIdx),
                        updateConcurrentSlot_ne _ _ idx _ (Ne.symm hSlIdx)]
                    exact hIdxSt
                  | inr r3New =>
                    dsimp only at hObsFalse ⊢
                    refine ih _ (updateConcurrentSlot slots0 slot _) (updateConcurrentSlot slotsS slot _) _ hPkE hCorrE
                      (hUpdOther _) (hUnallocUpd _) ?_ hObsFalse
                    dsimp only
                    rw [updateConcurrentSlot_ne _ _ idx _ (Ne.symm hSlIdx),
                        updateConcurrentSlot_ne _ _ idx _ (Ne.symm hSlIdx),
                        updateConcurrentSlot_ne _ _ idx _ (Ne.symm hSlIdx)]
                    exact hIdxSt
                · simp only [hPois, ↓reduceIte] at hObsFalse ⊢
                  refine ih _ (updateConcurrentSlot slots0 slot .closed) (updateConcurrentSlot slotsS slot .closed) _ hPkE hCorrE
                    (hUpdOther .closed) (hUnallocUpd .closed) ?_ hObsFalse
                  dsimp only
                  rw [updateConcurrentSlot_ne _ _ idx _ (Ne.symm hSlIdx),
                      updateConcurrentSlot_ne _ _ idx _ (Ne.symm hSlIdx),
                      updateConcurrentSlot_ne _ _ idx _ (Ne.symm hSlIdx)]
                  exact hIdxSt
        | stepRound3 sid =>
          have hObsStep : obsConcurrentSlotPreCut eng0 A idx (m + 1) { st with slots := slots0 } a =
              let (st0', a') := execConcurrentStep eng0 A { st with slots := slots0 } a
              obsConcurrentSlotPreCut eng0 A idx m st0' a' := by
            conv => lhs; unfold obsConcurrentSlotPreCut
            simp only [hCmd]
          rw [hObsStep] at hObsFalse
          unfold execConcurrentStep at hObsFalse ⊢
          simp only [hCmd] at hObsFalse ⊢
          cases hLook : lookupSidSlot sid st.sidMap with
          | none =>
            simp only [hLook] at hObsFalse
            exact ih st slots0 slotsS _ hPkE hCorrE hSlNe hUnalloc hIdxSt hObsFalse
          | some slot =>
            dsimp only
            simp only [hLook] at hObsFalse
            by_cases hSlIdx : slot = idx
            · subst hSlIdx
              rcases hIdxSt with ⟨hU0, hUR, hUS⟩ |
                ⟨hIdxLt, ep, md, rq, h1, c1, r2_0, r2_c, s2, hA0, hAR, hAS, hRel2_0, hRel2_c⟩
              · rw [hU0] at hObsFalse
                rw [hUR, hUS]
                exact ih st slots0 slotsS _ hPkE hCorrE hSlNe hUnalloc (.inl ⟨hU0, hUR, hUS⟩) hObsFalse
              · rw [hA0] at hObsFalse
                rw [hAR, hAS]
                exact ih st slots0 slotsS _ hPkE hCorrE hSlNe hUnalloc
                  (.inr ⟨hIdxLt, ep, md, rq, h1, c1, r2_0, r2_c, s2, hA0, hAR, hAS, hRel2_0, hRel2_c⟩) hObsFalse
            · obtain ⟨hSl0R, hSlRS⟩ := hSlNe slot hSlIdx
              rw [hSl0R] at hObsFalse
              rw [← hSlRS]
              cases hPh : st.slots slot with
              | unallocated =>
                rw [hPh] at hObsFalse
                exact ih st slots0 slotsS _ hPkE hCorrE hSlNe hUnalloc hIdxSt hObsFalse
              | afterR1 _ _ _ _ _ _ =>
                rw [hPh] at hObsFalse
                exact ih st slots0 slotsS _ hPkE hCorrE hSlNe hUnalloc hIdxSt hObsFalse
              | closed =>
                rw [hPh] at hObsFalse
                exact ih st slots0 slotsS _ hPkE hCorrE hSlNe hUnalloc hIdxSt hObsFalse
              | afterR2 ep md rq h1 c1 h2 c2 st3 =>
                rw [hPh] at hObsFalse
                dsimp only at hObsFalse ⊢
                have hClosedOther : ∀ j, j ≠ idx →
                    updateConcurrentSlot slots0 slot .closed j = updateConcurrentSlot st.slots slot .closed j ∧
                    updateConcurrentSlot st.slots slot .closed j = updateConcurrentSlot slotsS slot .closed j := by
                  intro j hjNe
                  by_cases hJ : j = slot
                  · subst hJ
                    rw [updateConcurrentSlot_same, updateConcurrentSlot_same, updateConcurrentSlot_same]
                    exact ⟨rfl, rfl⟩
                  · rw [updateConcurrentSlot_ne _ _ j _ hJ,
                        updateConcurrentSlot_ne _ _ j _ hJ,
                        updateConcurrentSlot_ne _ _ j _ hJ]
                    exact hSlNe j hjNe
                have hUnallocClosed : ∀ j, st.allocatedSlots ≤ j.val →
                    updateConcurrentSlot st.slots slot .closed j = .unallocated := by
                  intro j hj
                  have hUnJ := hUnalloc j hj
                  by_cases hJ : j = slot
                  · subst hJ; rw [hUnJ] at hPh; cases hPh
                  · rw [updateConcurrentSlot_ne _ _ j _ hJ]; exact hUnJ
                cases hPois : st.honestWal.poisoned
                · simp only [hPois, Bool.false_eq_true, ↓reduceIte] at hObsFalse ⊢
                  obtain ⟨_, _, ⟨hR3_0R, hR3_RS⟩⟩ := hOtherEng slot hSlIdx
                  simp only [hR3_0R, hR3_RS] at hObsFalse
                  simp only [hR3_RS]
                  have hF0 : ∀ x h3 c3, eng0.slotFinalize slot st.tsig.pk rq x h3 c3 =
                      engS.slotFinalize slot st.tsig.pk rq x h3 c3 := fun _ _ _ => rfl
                  have hFR : ∀ x h3 c3, engR.slotFinalize slot st.tsig.pk rq x h3 c3 =
                      engS.slotFinalize slot st.tsig.pk rq x h3 c3 := fun _ _ _ => rfl
                  simp only [hF0] at hObsFalse
                  simp only [hFR]
                  generalize engS.slotFinalize slot st.tsig.pk rq _ _ _ = fin at hObsFalse ⊢
                  cases fin <;>
                    (dsimp only at hObsFalse ⊢
                     refine ih _ (updateConcurrentSlot slots0 slot .closed) (updateConcurrentSlot slotsS slot .closed) _ hPkE hCorrE
                       hClosedOther hUnallocClosed ?_ hObsFalse
                     dsimp only
                     rw [updateConcurrentSlot_ne _ _ idx _ (Ne.symm hSlIdx),
                         updateConcurrentSlot_ne _ _ idx _ (Ne.symm hSlIdx),
                         updateConcurrentSlot_ne _ _ idx _ (Ne.symm hSlIdx)]
                     exact hIdxSt)
                · simp only [hPois, ↓reduceIte] at hObsFalse ⊢
                  refine ih _ (updateConcurrentSlot slots0 slot .closed) (updateConcurrentSlot slotsS slot .closed) _ hPkE hCorrE
                    hClosedOther hUnallocClosed ?_ hObsFalse
                  dsimp only
                  rw [updateConcurrentSlot_ne _ _ idx _ (Ne.symm hSlIdx),
                      updateConcurrentSlot_ne _ _ idx _ (Ne.symm hSlIdx),
                      updateConcurrentSlot_ne _ _ idx _ (Ne.symm hSlIdx)]
                  exact hIdxSt
    let stInit := initConcurrentExecState Q_s (PSum R2St SimR2) (PSum R3St (SimR3 × ByteArray))
      cl.tsig cl.honestWal cl.maskSessionCursor
    exact hPrePreCut numSteps stInit stInit.slots stInit.slots advSt
      rfl rfl (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => rfl) (.inl ⟨rfl, rfl, rfl⟩) hBadFalse
  have hMain := concurrent_product_hybrid_bound hCardS hybrids
    (fun _ _ => bijCoord) (fun _ _ _ _ => rfl) bad (cardPad * epsCheck) hAgree hBadSlice D
  dsimp only at hMain
  have hZeroEq : distAcceptCount cardAll realView D =
      finSum cardAll (fun ω => if D (hybrids 0 (Nat.zero_le Q_s) (enumVec.toFun ω)) then 1 else 0) := by
    apply finSum_congr
    intro ω
    exact congrArg (fun t => if D t then 1 else 0)
      (concurrentProtocolExec_eq_hybrid_zero proto idealSignOracle sim A Q_s numSteps
        (mkReal (enumVec.toFun ω)) (mkSim (enumVec.toFun ω)) cl advSt)
  have hTopEq : distAcceptCount cardAll idealView D =
      finSum cardAll (fun ω => if D (hybrids Q_s (Nat.le_refl Q_s) (enumVec.toFun ω)) then 1 else 0) := by
    apply finSum_congr
    intro ω
    have hPkIcl : proto.pkDigestOf icl.tsig.pk = sim.pkDigestOf icl.tsig.pk := by
      rw [← hTsig]; exact spec.hPkDigest
    exact congrArg (fun t => if D t then 1 else 0)
      (concurrentIdealExec_eq_hybrid_top proto idealSignOracle sim A Q_s numSteps
        (mkReal (enumVec.toFun ω)) (mkSim (enumVec.toFun ω)) cl icl advSt
        hTsig hWal hCur hPkIcl spec.hMsgDigest)
  rw [← hZeroEq, ← hTopEq] at hMain
  -- Cancel `cardPad > 0` from `diff * (cardPad * cardCheck) ≤ (Q_s * (cardPad * epsCheck)) * cardAll`!
  have hAllPos : 0 < cardAll := ucPow_pos hCardS Q_s
  let diff := natAbsDiff (distAcceptCount cardAll realView D) (distAcceptCount cardAll idealView D)
  have hScaled : cardPad * (diff * cardCheck) ≤ cardPad * ((Q_s * epsCheck) * cardAll) := by
    have hL : cardPad * (diff * cardCheck) = diff * cardS := by
      dsimp only [cardS]; ac_rfl
    have hR : cardPad * ((Q_s * epsCheck) * cardAll) = (Q_s * (cardPad * epsCheck)) * cardAll := by
      ac_rfl
    rw [hL, hR]
    exact hMain
  have hCanceled : diff * cardCheck ≤ (Q_s * epsCheck) * cardAll :=
    Nat.le_of_mul_le_mul_left hScaled spec.hPadPos
  unfold ratLe rationalAcceptDiff
  refine ⟨Nat.mul_pos hAllPos hAllPos, spec.hCheckPos, ?_⟩
  rw [natAbsDiff_mul_right]
  have hRearrL : diff * cardAll * cardCheck = diff * cardCheck * cardAll := by ac_rfl
  have hRearrR : Q_s * epsCheck * (cardAll * cardAll) = (Q_s * epsCheck) * cardAll * cardAll := by ac_rfl
  rw [hRearrL, hRearrR]
  exact Nat.mul_le_mul_right cardAll hCanceled

/-- **`#tooth` Reused `SessionId` / Mask Breaks Concurrent Session Isolation
    (`tooth_concurrent_reused_session_id_breaks_isolation`)**:
    Without unique `SessionId` domain separation, reusing the same 4-bit mask slot across two
    concurrent sessions leaks the exact secret XOR `w₁ ^^^ w₂` with probability `16 / 16 = 1`,
    whereas independent session masks satisfy `(w₁ ^^^ m₁) ^^^ (w₂ ^^^ m₂) = w₁ ^^^ w₂` on only
    `16 / 256` (`1 / 16`) mask pairs. -/

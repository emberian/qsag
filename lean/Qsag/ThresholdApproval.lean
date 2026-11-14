module
/-
# Qsag.ThresholdApproval — Cryptographic Quorum Approval & Non-Empty Honest Threshold Gate

Formalizes the public state `IdealTsigState` of $\mathcal{F}_{\text{TSIG}}^{\text{id-abort}}$ together
with structural and cryptographic quorum gates:
1. **Structural Honest-Minority & Quarantine Gate (`validThresholdApproval`)**:
   Enforces `0 < threshold ≤ numParties`, strict dishonest-minority bound `|corruptParties| < threshold`,
   strictly non-empty honest participation (`honestApprovers ≠ []`, rejecting `[]` unconditionally),
   duplicate-free in-range party IDs, and quarantine exclusion of `identifiedCheaters` from both
   honest approvers and corrupt quorum weight.
2. **Cryptographic Approval Certificate Verification (`verifyEncodedThresholdApproval`)**:
   Verifies explicit per-custodian cryptographic signatures over the injective domain-separated
   payload `encodeApprovalPayload (encodePk st.pk) epoch (encodeMsg msg)` (`"QSAG.THRESHOLD.APPROVAL/v1"`),
   enforces anti-replay `msg ∉ st.approvedMsgs`, enforces `approvers.length ≥ threshold > maxFaulty`,
   and constructively guarantees verification for at least one non-corrupt, unquarantined registry ID on
   the encoded `(st.pk, epoch, msg)` tuple (`encodedThresholdApproval_sound`).
   This compatibility API does not guarantee independent ownership or injective typed codecs.
3. **Canonical Boundary (`verifyCryptographicThresholdApproval`)**:
   Requires injective PK/message codecs, frames the party ID into every signed payload, and
   rejects aliases anywhere in the in-range key registry. Its soundness is signature verification;
   signer-origin and secret-key secrecy still require the corresponding cryptographic assumptions.
-/

public import Qsag.Keccak
public import Qsag.UcGames

public section
namespace Qsag

set_option autoImplicit false

/-- Public state of $\mathcal{F}_{\text{TSIG}}^{\text{id-abort}}$: contains ZERO secret keys (`SK`)
    and ZERO secret shares. -/
structure IdealTsigState (PK Msg : Type) where
  pk : PK
  threshold : Nat
  numParties : Nat
  corruptParties : List Nat
  approvedMsgs : List Msg
  identifiedCheaters : List Nat

/-- Check whether `honestApprovers` is a non-empty, duplicate-free set of unquarantined honest party
    indices under strict dishonest minority (`corruptParties.length < threshold`) that together with
    unquarantined corrupt parties reaches `threshold`. -/
@[expose] def validThresholdApproval {PK Msg : Type}
    (st : IdealTsigState PK Msg) (honestApprovers : List Nat) : Bool :=
  let activeCorrupt := st.corruptParties.filter (fun c => decide (c ∉ st.identifiedCheaters))
  decide (0 < st.threshold ∧ st.threshold ≤ st.numParties) &&
  decide (st.corruptParties.length < st.threshold) &&
  decide (0 < honestApprovers.length) &&
  decide st.corruptParties.Nodup &&
  st.corruptParties.all (fun c => decide (c < st.numParties)) &&
  decide honestApprovers.Nodup &&
  honestApprovers.all (fun h =>
    decide (h < st.numParties) &&
    decide (h ∉ st.corruptParties) &&
    decide (h ∉ st.identifiedCheaters)) &&
  decide (st.threshold ≤ activeCorrupt.length + honestApprovers.length)

/-- Domain tag `"QSAG.THRESHOLD.APPROVAL/v1"` (`26` ASCII bytes) binding approval signatures. -/
def approvalDomainTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x54, 0x48, 0x52, 0x45, 0x53, 0x48, 0x4F, 0x4C,
   0x44, 0x2E, 0x41, 0x50, 0x50, 0x52, 0x4F, 0x56, 0x41, 0x4C, 0x2F, 0x76, 0x31]

/-- Canonical injective multi-frame encoding of `(domain, pkBytes, epoch, msgBytes)`. -/
@[expose] def encodeApprovalPayload (pkBytes : List UInt8) (epoch : Nat) (msgBytes : List UInt8) :
    List UInt8 :=
  encodeMultiFrame [approvalDomainTag, pkBytes, leb128 epoch, msgBytes]

private theorem leb128_injective {n₁ n₂ : Nat} (h : leb128 n₁ = leb128 n₂) : n₁ = n₂ := by
  have hApp : leb128 n₁ ++ [] = leb128 n₂ ++ [] := by simpa using h
  exact (leb128_prefix_inj hApp).1

/-- **Preimage Injectivity (`encodeApprovalPayload_injective`)**:
    Every component `(pkBytes, epoch, msgBytes)` is length-framed; no boundary-shift or mod-256
    epoch truncation collision is possible (`0 Classical.choice`). -/
theorem encodeApprovalPayload_injective
    {pk₁ pk₂ : List UInt8} {ep₁ ep₂ : Nat} {m₁ m₂ : List UInt8}
    (h : encodeApprovalPayload pk₁ ep₁ m₁ = encodeApprovalPayload pk₂ ep₂ m₂) :
    pk₁ = pk₂ ∧ ep₁ = ep₂ ∧ m₁ = m₂ := by
  have hFields := encodeMultiFrame_injective h
  simp only [List.cons.injEq] at hFields
  exact ⟨hFields.2.1, leb128_injective hFields.2.2.1, hFields.2.2.2.1⟩

/-- Individual custodian approval certificate pairing `partyId` with cryptographic signature `sig`. -/
structure SignedQuorumApproval (AuthSig : Type) where
  partyId : Nat
  sig     : AuthSig
  deriving DecidableEq, Repr

/-- Single-certificate cryptographic check over `(pkBytes, epoch, msgBytes)`. -/
def verifySingleApproverCert {AuthPK AuthSK AuthSig : Type}
    (S_auth : AbstractSigScheme AuthPK AuthSK (List UInt8) AuthSig)
    (approverPks : Nat → Option AuthPK)
    (payload : List UInt8)
    (cert : SignedQuorumApproval AuthSig) : Bool :=
  match approverPks cert.partyId with
  | none => false
  | some apk => S_auth.verify apk payload cert.sig

/-- **Full Cryptographic Quorum Approval Predicate (`verifyEncodedThresholdApproval`)**:
    1. Rejects already-approved messages and any collision with their encoded bytes;
    2. Enforces `maxFaulty < st.threshold ≤ approvers.length` and `st.corruptParties.length ≤ maxFaulty`;
    3. Enforces duplicate-free, in-range, unquarantined `approvers` (`partyId ∉ st.identifiedCheaters`);
    4. Verifies every custodian's cryptographic signature over `encodeApprovalPayload (encodePk st.pk) epoch (encodeMsg msg)`;
    5. Requires the non-corrupt subset `honestApprovers` to pass `validThresholdApproval st honestApprovers`. -/
@[expose] def verifyEncodedThresholdApproval {PK Msg AuthPK AuthSK AuthSig : Type}
    [DecidableEq Msg]
    (S_auth : AbstractSigScheme AuthPK AuthSK (List UInt8) AuthSig)
    (approverPks : Nat → Option AuthPK)
    (encodePk : PK → List UInt8)
    (encodeMsg : Msg → List UInt8)
    (maxFaulty : Nat)
    (st : IdealTsigState PK Msg)
    (epoch : Nat)
    (msg : Msg)
    (approvers : List (SignedQuorumApproval AuthSig)) : Bool :=
  let payload := encodeApprovalPayload (encodePk st.pk) epoch (encodeMsg msg)
  let ids := approvers.map SignedQuorumApproval.partyId
  let honestApprovers := ids.filter (fun p => decide (p ∉ st.corruptParties))
  (decide (msg ∉ st.approvedMsgs) &&
    decide (encodeMsg msg ∉ st.approvedMsgs.map encodeMsg)) &&
  decide (maxFaulty < st.threshold ∧ st.threshold ≤ approvers.length ∧ st.corruptParties.length ≤ maxFaulty) &&
  decide ids.Nodup &&
  approvers.all (fun cert =>
    decide (cert.partyId < st.numParties) &&
    decide (cert.partyId ∉ st.identifiedCheaters) &&
    verifySingleApproverCert S_auth approverPks payload cert) &&
  validThresholdApproval st honestApprovers

/-- Empty `honestApprovers = []` is unconditionally rejected for EVERY state `st`. -/
theorem empty_honest_approvers_rejected {PK Msg : Type} (st : IdealTsigState PK Msg) :
    validThresholdApproval st [] = false := by
  simp [validThresholdApproval]

/-- Dishonest-majority / full-corrupt thresholds (`threshold ≤ corruptParties.length`) are rejected. -/
theorem corrupt_majority_threshold_rejected {PK Msg : Type}
    (st : IdealTsigState PK Msg) (honestApprovers : List Nat)
    (hBad : st.threshold ≤ st.corruptParties.length) :
    validThresholdApproval st honestApprovers = false := by
  have hNotLt : ¬ (st.corruptParties.length < st.threshold) := by omega
  simp [validThresholdApproval, hNotLt]

/-- Any quarantined cheater in `honestApprovers` causes `validThresholdApproval` to reject. -/
theorem identified_cheater_honest_rejected {PK Msg : Type}
    (st : IdealTsigState PK Msg) (honestApprovers : List Nat)
    {c : Nat} (hMem : c ∈ honestApprovers) (hCheater : c ∈ st.identifiedCheaters) :
    validThresholdApproval st honestApprovers = false := by
  apply Bool.eq_false_iff.mpr
  intro hOk
  unfold validThresholdApproval at hOk
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hOk
  have hc := hOk.1.2 c hMem
  exact hc.2 hCheater

/-- Replaying an already-approved message `msg ∈ st.approvedMsgs` is rejected. -/
theorem legacy_approved_msg_replay_rejected {PK Msg AuthPK AuthSK AuthSig : Type} [DecidableEq Msg]
    (S_auth : AbstractSigScheme AuthPK AuthSK (List UInt8) AuthSig)
    (approverPks : Nat → Option AuthPK)
    (encodePk : PK → List UInt8)
    (encodeMsg : Msg → List UInt8)
    (maxFaulty : Nat)
    (st : IdealTsigState PK Msg)
    (epoch : Nat)
    (msg : Msg)
    (approvers : List (SignedQuorumApproval AuthSig))
    (hReplay : msg ∈ st.approvedMsgs) :
    verifyEncodedThresholdApproval S_auth approverPks encodePk encodeMsg maxFaulty st epoch msg approvers = false := by
  simp [verifyEncodedThresholdApproval, hReplay]

/-- Replay is checked in the actual signed byte domain, including colliding typed messages. -/
theorem encoded_approved_msg_replay_rejected {PK Msg AuthPK AuthSK AuthSig : Type}
    [DecidableEq Msg] (S : AbstractSigScheme AuthPK AuthSK (List UInt8) AuthSig)
    (keys : Nat → Option AuthPK) (encPk : PK → List UInt8) (encMsg : Msg → List UInt8)
    (faults : Nat) (st : IdealTsigState PK Msg) (epoch : Nat) (msg old : Msg)
    (certs : List (SignedQuorumApproval AuthSig))
    (hOld : old ∈ st.approvedMsgs) (hCollision : encMsg msg = encMsg old) :
    verifyEncodedThresholdApproval S keys encPk encMsg faults st epoch msg certs = false := by
  have hMem : encMsg msg ∈ st.approvedMsgs.map encMsg := by
    rw [hCollision]
    exact List.mem_map.mpr ⟨old, hOld, rfl⟩
  simp [verifyEncodedThresholdApproval, hMem]

/-- **Cryptographic Quorum Soundness (`encodedThresholdApproval_sound`)**:
    When `verifyEncodedThresholdApproval = true`:
    1. `msg ∉ st.approvedMsgs` (fresh unapproved message),
    2. `approvers.length ≥ st.threshold > maxFaulty`,
    3. `validThresholdApproval st honestApprovers = true` and `honestApprovers ≠ []`, and
    4. At least one honest, unquarantined custodian `cert ∈ approvers` (`cert.partyId ∉ st.corruptParties`,
       `cert.partyId ∉ st.identifiedCheaters`) holds a valid public key `apk` in `approverPks` whose
       signature `cert.sig` verifies on `encodeApprovalPayload (encodePk st.pk) epoch (encodeMsg msg)`! -/
theorem encodedThresholdApproval_sound {PK Msg AuthPK AuthSK AuthSig : Type} [DecidableEq Msg]
    (S_auth : AbstractSigScheme AuthPK AuthSK (List UInt8) AuthSig)
    (approverPks : Nat → Option AuthPK)
    (encodePk : PK → List UInt8)
    (encodeMsg : Msg → List UInt8)
    (maxFaulty : Nat)
    (st : IdealTsigState PK Msg)
    (epoch : Nat)
    (msg : Msg)
    (approvers : List (SignedQuorumApproval AuthSig))
    (hOk : verifyEncodedThresholdApproval S_auth approverPks encodePk encodeMsg
             maxFaulty st epoch msg approvers = true) :
    let payload := encodeApprovalPayload (encodePk st.pk) epoch (encodeMsg msg)
    let honestApprovers :=
      (approvers.map SignedQuorumApproval.partyId).filter (fun p => decide (p ∉ st.corruptParties))
    msg ∉ st.approvedMsgs ∧
    maxFaulty < st.threshold ∧
    st.threshold ≤ approvers.length ∧
    honestApprovers ≠ [] ∧
    validThresholdApproval st honestApprovers = true ∧
    ∃ cert ∈ approvers, ∃ apk : AuthPK,
      cert.partyId < st.numParties ∧
      cert.partyId ∉ st.corruptParties ∧
      cert.partyId ∉ st.identifiedCheaters ∧
      approverPks cert.partyId = some apk ∧
      S_auth.verify apk payload cert.sig = true := by
  unfold verifyEncodedThresholdApproval at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hOk
  rcases hOk with ⟨⟨⟨⟨hFresh, hBounds⟩, _hIdsNd⟩, hAllCerts⟩, hValHon⟩
  have hHonNonempty :
      (approvers.map SignedQuorumApproval.partyId).filter (fun p => decide (p ∉ st.corruptParties)) ≠ [] := by
    intro hNil
    rw [hNil, empty_honest_approvers_rejected] at hValHon
    cases hValHon
  refine ⟨hFresh.1, hBounds.1, hBounds.2.1, hHonNonempty, hValHon, ?_⟩
  cases hFilt : (approvers.map SignedQuorumApproval.partyId).filter (fun p => decide (p ∉ st.corruptParties)) with
  | nil => exact False.elim (hHonNonempty hFilt)
  | cons hPid rest =>
    have hMemFilt : hPid ∈ (approvers.map SignedQuorumApproval.partyId).filter (fun p => decide (p ∉ st.corruptParties)) := by
      rw [hFilt]; exact .head _
    rcases List.mem_filter.mp hMemFilt with ⟨hMemIds, hNotCorrDec⟩
    have hNotCorr : hPid ∉ st.corruptParties := of_decide_eq_true hNotCorrDec
    rcases List.mem_map.mp hMemIds with ⟨cert, hCertMem, rfl⟩
    have hCertOk := hAllCerts cert hCertMem
    rcases hCertOk with ⟨⟨hRange, hNotCheat⟩, hSigOk⟩
    unfold verifySingleApproverCert at hSigOk
    cases hApk : approverPks cert.partyId with
    | none => rw [hApk] at hSigOk; cases hSigOk
    | some apk =>
      rw [hApk] at hSigOk
      exact ⟨cert, hCertMem, apk, hRange, hNotCorr, hNotCheat, hApk, hSigOk⟩

/-- Concrete 256-bit `SHAKE256` keyed authentication scheme instantiating `AbstractSigScheme` for
    executable `#tooth` and inhabitedness verification. -/
def shakeApprovalAuthScheme : AbstractSigScheme (List UInt8) (List UInt8) (List UInt8) (List UInt8) where
  sign := fun sk m => shake256Xof 32 (encodeMultiFrame [sk, m])
  verify := fun pk m tag => decide (tag = shake256Xof 32 (encodeMultiFrame [pk, m]))
  complete := fun pk sk => pk = sk
  completeness := fun {_pk _sk} hEq _m => by
    subst hEq
    exact decide_eq_true rfl

/-- **`#tooth` Mutation Witness (`tooth_wrong_pk_or_empty_quorum_rejected`)**:
    1. Replacing `st.pk` with a distinct `pk' ≠ st.pk` causes `verifyEncodedThresholdApproval`
       to reject valid quorum certificates (unless a concrete 256-bit `SHAKE256` collision occurs);
    2. Mutating `validThresholdApproval` by dropping `0 < honestApprovers.length` and
       `corruptParties.length < threshold` (`unprotectedCountingApproval`) accepts `honestApprovers = []`
       on `threshold = 1, corruptParties = [0]`, whereas `validThresholdApproval` rejects it! -/
theorem tooth_wrong_pk_or_empty_quorum_rejected :
    let stUnilat : IdealTsigState (List UInt8) (List UInt8) :=
      ⟨[0x11], 1, 2, [0], [], []⟩
    let unprotectedCountingApproval (s : IdealTsigState (List UInt8) (List UInt8)) (hon : List Nat) : Bool :=
      decide (0 < s.threshold ∧ s.threshold ≤ s.numParties) &&
      decide (s.threshold ≤ s.corruptParties.length + hon.length)
    unprotectedCountingApproval stUnilat [] = true ∧
    validThresholdApproval stUnilat [] = false ∧
    (∀ (k0 k1 pk₁ pk₂ msg : List UInt8) (ep : Nat),
      pk₁ ≠ pk₂ →
      let pks : Nat → Option (List UInt8) := fun i => if i == 0 then some k0 else if i == 1 then some k1 else none
      let payload₁ := encodeApprovalPayload pk₁ ep msg
      let certs : List (SignedQuorumApproval (List UInt8)) :=
        [⟨0, shakeApprovalAuthScheme.sign k0 payload₁⟩,
         ⟨1, shakeApprovalAuthScheme.sign k1 payload₁⟩]
      let st₂ : IdealTsigState (List UInt8) (List UInt8) := ⟨pk₂, 2, 3, [2], [], []⟩
      verifyEncodedThresholdApproval shakeApprovalAuthScheme pks id id 1 st₂ ep msg certs = true →
      Nonempty (HashCollisionWitness (shake256Xof 32))) := by
  refine ⟨by decide, empty_honest_approvers_rejected _, ?_⟩
  intro k0 k1 pk₁ pk₂ msg ep hPkNe pks payload₁ certs st₂ hAcc
  obtain ⟨_, _, _, _, _, cert, hCertMem, apk, _, _, _, hApk, hVer⟩ :=
    encodedThresholdApproval_sound shakeApprovalAuthScheme pks id id 1 st₂ ep msg certs hAcc
  have hPayNe : payload₁ ≠ encodeApprovalPayload pk₂ ep msg := by
    intro hEq
    exact hPkNe (encodeApprovalPayload_injective hEq).1
  rcases List.mem_cons.mp hCertMem with rfl | hTail
  · simp only [pks, Nat.reduceBEq, ↓reduceIte, Option.some.injEq] at hApk
    subst hApk
    have hTagEq : shake256Xof 32 (encodeMultiFrame [k0, payload₁]) =
        shake256Xof 32 (encodeMultiFrame [k0, encodeApprovalPayload pk₂ ep msg]) :=
      of_decide_eq_true hVer
    refine ⟨⟨encodeMultiFrame [k0, payload₁], encodeMultiFrame [k0, encodeApprovalPayload pk₂ ep msg], ?_, hTagEq⟩⟩
    intro hInEq
    have hF := encodeMultiFrame_injective hInEq
    simp only [List.cons.injEq] at hF
    exact hPayNe hF.2.1
  · rcases List.mem_singleton.mp hTail with rfl
    simp only [pks, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hApk
    subst hApk
    have hTagEq : shake256Xof 32 (encodeMultiFrame [k1, payload₁]) =
        shake256Xof 32 (encodeMultiFrame [k1, encodeApprovalPayload pk₂ ep msg]) :=
      of_decide_eq_true hVer
    refine ⟨⟨encodeMultiFrame [k1, payload₁], encodeMultiFrame [k1, encodeApprovalPayload pk₂ ep msg], ?_, hTagEq⟩⟩
    intro hInEq
    have hF := encodeMultiFrame_injective hInEq
    simp only [List.cons.injEq] at hF
    exact hPayNe hF.2.1

/-- **Inhabitedness Witness (`inhabited_encoded_threshold_approval`)**:
    Demonstrates a concrete 2-of-3 quorum (`threshold = 2 > maxFaulty = 1`, `corruptParties = [2]`)
    over 32-byte keys and `SHAKE256` authentication tags where `verifyEncodedThresholdApproval = true`. -/
theorem inhabited_encoded_threshold_approval :
    let pk : List UInt8 := List.replicate 32 0x42
    let msg : List UInt8 := [0xDE, 0xAD, 0xBE, 0xEF]
    let k0 : List UInt8 := List.replicate 32 0x01
    let k1 : List UInt8 := List.replicate 32 0x02
    let pks : Nat → Option (List UInt8) :=
      fun i => if i == 0 then some k0 else if i == 1 then some k1 else none
    let st : IdealTsigState (List UInt8) (List UInt8) := ⟨pk, 2, 3, [2], [], []⟩
    let payload := encodeApprovalPayload pk 7 msg
    let certs : List (SignedQuorumApproval (List UInt8)) :=
      [⟨0, shakeApprovalAuthScheme.sign k0 payload⟩,
       ⟨1, shakeApprovalAuthScheme.sign k1 payload⟩]
    verifyEncodedThresholdApproval shakeApprovalAuthScheme pks id id 1 st 7 msg certs = true := by
  intro pk msg k0 k1 pks st payload certs
  unfold verifyEncodedThresholdApproval verifySingleApproverCert validThresholdApproval
  have hSig0 : shakeApprovalAuthScheme.verify k0 payload (shakeApprovalAuthScheme.sign k0 payload) = true :=
    shakeApprovalAuthScheme.completeness rfl payload
  have hSig1 : shakeApprovalAuthScheme.verify k1 payload (shakeApprovalAuthScheme.sign k1 payload) = true :=
    shakeApprovalAuthScheme.completeness rfl payload
  dsimp only [certs, st, pks, id]
  simp only [List.map, List.filter, List.all, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  rw [hSig0, hSig1]
  decide

/-- A codec contract is necessary to lift byte equality to typed authorization. -/
structure ApprovalCodec (α : Type) where
  encode : α → List UInt8
  injective : ∀ {a b}, encode a = encode b → a = b

/-- Versioned, injective party binding around the existing framed approval payload. -/
def encodePartyApprovalPayload (party : Nat) (payload : List UInt8) : List UInt8 :=
  encodeMultiFrame [[0x51, 0x53, 0x41, 0x47, 0x02], leb128 party, payload]

theorem encodePartyApprovalPayload_injective {i j : Nat} {a b : List UInt8}
    (h : encodePartyApprovalPayload i a = encodePartyApprovalPayload j b) :
    i = j ∧ a = b := by
  have hf := encodeMultiFrame_injective h
  simp only [List.cons.injEq] at hf
  exact ⟨leb128_injective hf.2.1, hf.2.2.1⟩

theorem approvalCodec_payload_injective {PK Msg : Type}
    (pkCodec : ApprovalCodec PK) (msgCodec : ApprovalCodec Msg)
    {pk pk' : PK} {m m' : Msg} {e e' i j : Nat}
    (h : encodePartyApprovalPayload i (encodeApprovalPayload (pkCodec.encode pk) e (msgCodec.encode m)) =
      encodePartyApprovalPayload j (encodeApprovalPayload (pkCodec.encode pk') e' (msgCodec.encode m'))) :
    i = j ∧ pk = pk' ∧ e = e' ∧ m = m' := by
  have hp := encodePartyApprovalPayload_injective h
  have hc := encodeApprovalPayload_injective hp.2
  exact ⟨hp.1, pkCodec.injective hc.1, hc.2.1, msgCodec.injective hc.2.2⟩

/-- Registry injectivity is checked over all in-range identities, including corrupt parties
outside this certificate. It excludes aliasing, not compromise of independently registered keys. -/
def approvalRegistryUnique {AuthPK : Type} [DecidableEq AuthPK]
    (keys : Nat → Option AuthPK) (count : Nat) : Bool :=
  (List.range count).all fun i => (List.range count).all fun j =>
    decide (i = j ∨ keys i = none ∨ keys i ≠ keys j)

/-- Strict boundary: canonical codecs, party-bound signatures, and a non-aliasing registry.
The explicitly named encoded verifier above describes authorization of encoded bytes only.
The structural API consumed by custody and apex modules is unchanged. -/
def verifyCryptographicThresholdApproval {PK Msg AuthPK AuthSK AuthSig : Type}
    [DecidableEq Msg] [DecidableEq AuthPK]
    (S : AbstractSigScheme AuthPK AuthSK (List UInt8) AuthSig)
    (keys : Nat → Option AuthPK) (pkCodec : ApprovalCodec PK) (msgCodec : ApprovalCodec Msg)
    (faults : Nat) (st : IdealTsigState PK Msg) (epoch : Nat) (msg : Msg)
    (certs : List (SignedQuorumApproval AuthSig)) : Bool :=
  let ids := certs.map SignedQuorumApproval.partyId
  let payload := encodeApprovalPayload (pkCodec.encode st.pk) epoch (msgCodec.encode msg)
  decide (msg ∉ st.approvedMsgs) &&
  decide (faults < st.threshold ∧ st.threshold ≤ certs.length ∧ st.corruptParties.length ≤ faults) &&
  decide ids.Nodup && approvalRegistryUnique keys st.numParties &&
  certs.all (fun c => decide (c.partyId < st.numParties) &&
    decide (c.partyId ∉ st.identifiedCheaters) &&
    verifySingleApproverCert S keys (encodePartyApprovalPayload c.partyId payload) c) &&
  validThresholdApproval st (ids.filter (fun p => decide (p ∉ st.corruptParties)))

theorem approvalRegistryUnique_distinct {AuthPK : Type} [DecidableEq AuthPK]
    (keys : Nat → Option AuthPK) (count i j : Nat) (pk : AuthPK)
    (h : approvalRegistryUnique keys count = true)
    (hi : i < count) (hj : j < count) (hkey : keys i = some pk) (hne : i ≠ j) :
    keys j ≠ some pk := by
  simp only [approvalRegistryUnique, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  rcases h i hi j hj with heq | hempty | hdiff
  · exact False.elim (hne heq)
  · rw [hkey] at hempty; cases hempty
  · intro hsame; exact hdiff (hkey.trans hsame.symm)

theorem approved_msg_replay_rejected {PK Msg AuthPK AuthSK AuthSig : Type}
    [DecidableEq Msg] [DecidableEq AuthPK]
    (S : AbstractSigScheme AuthPK AuthSK (List UInt8) AuthSig)
    (keys : Nat → Option AuthPK) (pc : ApprovalCodec PK) (mc : ApprovalCodec Msg)
    (faults : Nat) (st : IdealTsigState PK Msg) (epoch : Nat) (msg : Msg)
    (certs : List (SignedQuorumApproval AuthSig)) (h : msg ∈ st.approvedMsgs) :
    verifyCryptographicThresholdApproval S keys pc mc faults st epoch msg certs = false := by
  simp [verifyCryptographicThresholdApproval, h]

/-- Every accepted certificate verifies in its own party context, and the entire registry
is free of key aliases. Verification alone is not a claim of secret-key possession. -/
theorem cryptographicThresholdApproval_sound {PK Msg AuthPK AuthSK AuthSig : Type}
    [DecidableEq Msg] [DecidableEq AuthPK]
    (S : AbstractSigScheme AuthPK AuthSK (List UInt8) AuthSig)
    (keys : Nat → Option AuthPK) (pc : ApprovalCodec PK) (mc : ApprovalCodec Msg)
    (faults : Nat) (st : IdealTsigState PK Msg) (epoch : Nat) (msg : Msg)
    (certs : List (SignedQuorumApproval AuthSig))
    (h : verifyCryptographicThresholdApproval S keys pc mc faults st epoch msg certs = true) :
    msg ∉ st.approvedMsgs ∧ approvalRegistryUnique keys st.numParties = true ∧
    (certs.map SignedQuorumApproval.partyId).Nodup ∧
    ∀ c ∈ certs, c.partyId < st.numParties ∧ c.partyId ∉ st.identifiedCheaters ∧
      ∃ pk, keys c.partyId = some pk ∧
        S.verify pk (encodePartyApprovalPayload c.partyId
          (encodeApprovalPayload (pc.encode st.pk) epoch (mc.encode msg))) c.sig = true := by
  simp only [verifyCryptographicThresholdApproval, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h
  refine ⟨h.1.1.1.1.1, h.1.1.2, h.1.1.1.2, ?_⟩
  intro c hc
  have hk := h.1.2 c hc
  refine ⟨hk.1.1, hk.1.2, ?_⟩
  have hv := hk.2
  unfold verifySingleApproverCert at hv
  cases hp : keys c.partyId with
  | none => rw [hp] at hv; cases hv
  | some pk => rw [hp] at hv; exact ⟨pk, rfl, hv⟩

theorem canonicalApproval_distinct_party_keys {PK Msg AuthPK AuthSK AuthSig : Type}
    [DecidableEq Msg] [DecidableEq AuthPK]
    (S : AbstractSigScheme AuthPK AuthSK (List UInt8) AuthSig)
    (keys : Nat → Option AuthPK) (pc : ApprovalCodec PK) (mc : ApprovalCodec Msg)
    (faults : Nat) (st : IdealTsigState PK Msg) (epoch : Nat) (msg : Msg)
    (certs : List (SignedQuorumApproval AuthSig))
    (h : verifyCryptographicThresholdApproval S keys pc mc faults st epoch msg certs = true)
    (i j : Nat) (pk : AuthPK) (hi : i < st.numParties) (hj : j < st.numParties)
    (hk : keys i = some pk) (hne : i ≠ j) : keys j ≠ some pk :=
  approvalRegistryUnique_distinct keys st.numParties i j pk
    (cryptographicThresholdApproval_sound S keys pc mc faults st epoch msg certs h).2.1 hi hj hk hne

theorem canonicalApproval_shared_key_rejected {PK Msg AuthPK AuthSK AuthSig : Type}
    [DecidableEq Msg] [DecidableEq AuthPK]
    (S : AbstractSigScheme AuthPK AuthSK (List UInt8) AuthSig)
    (keys : Nat → Option AuthPK) (pc : ApprovalCodec PK) (mc : ApprovalCodec Msg)
    (faults : Nat) (st : IdealTsigState PK Msg) (epoch : Nat) (msg : Msg)
    (certs : List (SignedQuorumApproval AuthSig)) (i j : Nat) (pk : AuthPK)
    (hi : i < st.numParties) (hj : j < st.numParties)
    (hki : keys i = some pk) (hkj : keys j = some pk) (hne : i ≠ j) :
    verifyCryptographicThresholdApproval S keys pc mc faults st epoch msg certs = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact canonicalApproval_distinct_party_keys S keys pc mc faults st epoch msg certs
    h i j pk hi hj hki hne hkj

theorem canonicalApproval_honest_quorum {PK Msg AuthPK AuthSK AuthSig : Type}
    [DecidableEq Msg] [DecidableEq AuthPK]
    (S : AbstractSigScheme AuthPK AuthSK (List UInt8) AuthSig)
    (keys : Nat → Option AuthPK) (pc : ApprovalCodec PK) (mc : ApprovalCodec Msg)
    (faults : Nat) (st : IdealTsigState PK Msg) (epoch : Nat) (msg : Msg)
    (certs : List (SignedQuorumApproval AuthSig))
    (h : verifyCryptographicThresholdApproval S keys pc mc faults st epoch msg certs = true) :
    let honest := (certs.map SignedQuorumApproval.partyId).filter
      (fun p => decide (p ∉ st.corruptParties))
    faults < st.threshold ∧ st.threshold ≤ certs.length ∧
      honest ≠ [] ∧ validThresholdApproval st honest = true := by
  simp only [verifyCryptographicThresholdApproval, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1.1.1.1.2.1, h.1.1.1.1.2.2.1, ?_, h.2⟩
  intro hn
  have hv := h.2
  rw [hn, empty_honest_approvers_rejected] at hv
  cases hv

/-- Identity is a canonical codec for the authorization byte domain. -/
def approvalBytesCodec : ApprovalCodec (List UInt8) := ⟨id, fun h => h⟩

theorem inhabited_cryptographic_threshold_approval :
    let k0 : List UInt8 := [1]
    let k1 : List UInt8 := [2]
    let keys : Nat → Option (List UInt8) := fun i =>
      if i == 0 then some k0 else if i == 1 then some k1 else none
    let st : IdealTsigState (List UInt8) (List UInt8) := ⟨[42], 2, 3, [2], [], []⟩
    let payload := encodeApprovalPayload [42] 7 [99]
    let certs : List (SignedQuorumApproval (List UInt8)) :=
      [⟨0, shakeApprovalAuthScheme.sign k0 (encodePartyApprovalPayload 0 payload)⟩,
       ⟨1, shakeApprovalAuthScheme.sign k1 (encodePartyApprovalPayload 1 payload)⟩]
    verifyCryptographicThresholdApproval shakeApprovalAuthScheme keys approvalBytesCodec approvalBytesCodec
      1 st 7 [99] certs = true := by
  intro k0 k1 keys st payload certs
  have h0 := shakeApprovalAuthScheme.completeness (pk := k0) (sk := k0) rfl
    (encodePartyApprovalPayload 0 payload)
  have h1 := shakeApprovalAuthScheme.completeness (pk := k1) (sk := k1) rfl
    (encodePartyApprovalPayload 1 payload)
  unfold verifyCryptographicThresholdApproval verifySingleApproverCert validThresholdApproval
  dsimp only [certs, st, keys, approvalBytesCodec, id]
  simp only [List.map, List.filter, List.all, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  rw [h0, h1]
  decide

theorem tooth_shared_registry_key_rejected :
    approvalRegistryUnique (fun _ => some (7 : Nat)) 2 = false := by decide

theorem tooth_party_payload_not_relabelable :
    encodePartyApprovalPayload 0 [] ≠ encodePartyApprovalPayload 1 [] := by
  intro h
  have hn := (encodePartyApprovalPayload_injective h).1
  exact (by decide : (0 : Nat) ≠ 1) hn

/-- The certificate is accepted before approval and rejected after approving a distinct
message with identical bytes. Thus rejection is sensitive to the encoded replay guard. -/
theorem tooth_colliding_message_replay_rejected :
    let payload := encodeApprovalPayload [] 0 []
    let certs : List (SignedQuorumApproval (List UInt8)) :=
      [⟨0, shakeApprovalAuthScheme.sign [] payload⟩]
    verifyEncodedThresholdApproval shakeApprovalAuthScheme (fun _ => some [])
      (fun (_ : Bool) => []) (fun (_ : Bool) => []) 0
      ⟨false, 1, 1, [], [false], []⟩ 0 true certs = false ∧
    verifyEncodedThresholdApproval shakeApprovalAuthScheme (fun _ => some [])
      (fun (_ : Bool) => []) (fun (_ : Bool) => []) 0
      ⟨false, 1, 1, [], [], []⟩ 0 true certs = true := by
  intro payload certs
  constructor
  · apply encoded_approved_msg_replay_rejected (old := false)
    · exact .head _
    · rfl
  · have hs := shakeApprovalAuthScheme.completeness (pk := []) (sk := []) rfl payload
    unfold verifyEncodedThresholdApproval verifySingleApproverCert validThresholdApproval
    dsimp only [certs]
    simp only [List.map, List.filter, List.all]
    rw [hs]
    decide

/-- Constant encoders cannot satisfy the canonical codec contract. -/
theorem tooth_constant_bool_codec_rejected :
    ¬ (∀ {a b : Bool}, (fun (_ : Bool) => ([] : List UInt8)) a =
      (fun (_ : Bool) => ([] : List UInt8)) b → a = b) := by
  intro h
  have bad : false = true := h rfl
  cases bad

end Qsag
end

module
public import Qsag.Exec.IdealOutputBoundary
public import Qsag.Exec.InteractiveUcEngine
public import Qsag.Protocol.Threshold.ThresholdMpc
public import Qsag.Protocol.Signing.HashSigs
import Qsag.Tactic.AssuranceKit

/-!
# Coherent partial RSS production-signing profile

The shared computation, reference signer, enrolled key, canonical request and wire
encoder are connected here by proved equalities. The RSS oracle is the existing
actual shared-cSHAKE constructor. This is a computation refinement, not a network
simulation: it does not implement authenticated approval, per-host custody, setup,
or physical durable storage. The reference evaluator reconstructs the key and is
provided for checking the same mathematical function, not as a distributed signer.
-/

public section
namespace Qsag.RssProduction
set_option autoImplicit false

/-- Structural sharing/width requirements; key coherence is derived below. -/
structure Material where
  seed : RssByteShares
  prf : RssByteShares
  pkSeed : List UInt8
  seedWf : seed.WellFormed
  prfWf : prf.WellFormed
  seedWidth : seed.b0.length = 32
  prfWidth : prf.b0.length = 32
  pkWidth : pkSeed.length = 32

structure Profile where
  material : Material
  params : PqHashParams
  context : List UInt8
  grindLimit : Nat
  tape : Nat → Nat → Nat → Nat → RssPrfZeroSeeds

def referenceKey (p : Profile) : PqSecretKey :=
  ⟨reconstructRssBytes p.material.seed, reconstructRssBytes p.material.prf, p.material.pkSeed⟩

def sharedOracle (p : Profile) : ProductionPqHashMpcOracles :=
  mkRssProductionPqHashMpcOracles p.material.seed p.material.prf p.material.pkSeed p.tape

/-- No caller supplies an enrolled key unrelated to the sharing. -/
def enrolledKey (p : Profile) : PqPublicKey :=
  derivePublicKey cshake256Suite p.params (referenceKey p)

theorem sharedOracle_matches (p : Profile) :
    (sharedOracle p).MatchesKey cshake256Suite (referenceKey p) :=
  mkRssProductionPqHashMpcOracles_matchesKey p.material.seedWf p.material.prfWf
    p.material.pkSeed p.tape

theorem enrollment_from_shared_computation (p : Profile) :
    derivePublicKeyMpc cshake256Suite p.params (sharedOracle p).toPqHashMpcOracles
      p.material.pkSeed = enrolledKey p := by
  unfold derivePublicKeyMpc enrolledKey
  dsimp only
  have h := mpcComputeXmssSubtreeRoot_eq cshake256Suite p.params
    (sharedOracle p).toPqHashMpcOracles (referenceKey p) (sharedOracle_matches p).1
  dsimp only [referenceKey] at h
  rw [h]
  rfl

def encodeParameters (p : PqHashParams) : List UInt8 :=
  encodeMultiFrame [leb128 p.w, leb128 p.ell1, leb128 p.subtreeHeight,
    leb128 p.numLayers, leb128 p.forsTrees, leb128 p.forsHeight,
    leb128 p.maxSigsLog2, [if p.statefulJorts then 1 else 0]]

private theorem natFrame_injective {a b : Nat} (h : leb128 a = leb128 b) : a = b :=
  (leb128_prefix_inj (show leb128 a ++ [] = leb128 b ++ [] by simpa using h)).1

theorem encodeParameters_injective {a b : PqHashParams}
    (h : encodeParameters a = encodeParameters b) : a = b := by
  have hf := encodeMultiFrame_injective h
  simp only [List.cons.injEq] at hf
  rcases hf with ⟨hw, he, hs, hn, hf, hh, hm, hb, _⟩
  have hbool : a.statefulJorts = b.statefulJorts := by
    cases ha : a.statefulJorts <;> cases hz : b.statefulJorts <;>
      simp only [ha, hz, Bool.false_eq_true, ↓reduceIte] at hb ⊢
    · exact False.elim ((by decide : (0 : UInt8) ≠ 1) hb.1)
    · exact False.elim ((by decide : (1 : UInt8) ≠ 0) hb.1)
  cases a; cases b
  simp only [PqHashParams.mk.injEq]
  exact ⟨natFrame_injective hw, natFrame_injective he, natFrame_injective hs,
    natFrame_injective hn, natFrame_injective hf, natFrame_injective hh,
    natFrame_injective hm, hbool⟩

/-- Bind public enrollment, every parameter field, application context and resource
    limit, plus every SessionScheduleReq field. There is no separate retry counter. -/
def payload (p : Profile) (req : SessionScheduleReq) : List UInt8 :=
  encodeMultiFrame ["QSAG.RSS.PRODUCTION.REQUEST/v1".toUTF8.data.toList,
    encodeUcPqPublicKey (enrolledKey p), encodeParameters p.params, p.context,
    leb128 p.grindLimit, encodeUcSigningRequest req]

theorem payload_request_binding {p q : Profile} {a b : SessionScheduleReq}
    (h : payload p a = payload q b) : a = b := by
  have he := encodeMultiFrame_injective h
  simp only [List.cons.injEq] at he
  exact encodeUcSigningRequest_injective he.2.2.2.2.2.1

theorem payload_enrollment_binding {p q : Profile} {a b : SessionScheduleReq}
    (h : payload p a = payload q b) : enrolledKey p = enrolledKey q := by
  have he := encodeMultiFrame_injective h
  simp only [List.cons.injEq] at he
  exact encodeUcPqPublicKey_injective he.2.1

theorem payload_profile_binding {p q : Profile} {a b : SessionScheduleReq}
    (h : payload p a = payload q b) :
    p.params = q.params ∧ p.context = q.context ∧ p.grindLimit = q.grindLimit := by
  have he := encodeMultiFrame_injective h
  simp only [List.cons.injEq] at he
  exact ⟨encodeParameters_injective he.2.2.1, he.2.2.2.1,
    natFrame_injective he.2.2.2.2.1⟩

/-- A WAL enrollment pins the whole public signing configuration, not merely a
    key that some parameter/context changes could leave unchanged. -/
def enrollmentEncoding (p : Profile) : List UInt8 :=
  encodeMultiFrame ["QSAG.RSS.PRODUCTION.ENROLLMENT/v1".toUTF8.data.toList,
    encodeUcPqPublicKey (enrolledKey p), encodeParameters p.params, p.context, leb128 p.grindLimit]

def enrollmentDigest (p : Profile) : List UInt8 := shake256Xof 32 (enrollmentEncoding p)

theorem enrollmentDigest_length (p : Profile) : (enrollmentDigest p).length = 32 :=
  shake256Xof_length 32 (enrollmentEncoding p)

theorem enrollmentEncoding_binding {p q : Profile}
    (h : enrollmentEncoding p = enrollmentEncoding q) :
    enrolledKey p = enrolledKey q ∧ p.params = q.params ∧
      p.context = q.context ∧ p.grindLimit = q.grindLimit := by
  have he := encodeMultiFrame_injective h
  simp only [List.cons.injEq] at he
  exact ⟨encodeUcPqPublicKey_injective he.2.1, encodeParameters_injective he.2.2.1,
    he.2.2.2.1, natFrame_injective he.2.2.2.2.1⟩

def enrollmentDigest_binding_or_collision (p q : Profile)
    (h : enrollmentDigest p = enrollmentDigest q) :
    PSum (enrolledKey p = enrolledKey q ∧ p.params = q.params ∧
      p.context = q.context ∧ p.grindLimit = q.grindLimit)
      (HashCollisionWitness (shake256Xof 32)) := by
  if he : enrollmentEncoding p = enrollmentEncoding q then
    exact .inl (enrollmentEncoding_binding he)
  else
    exact .inr ⟨enrollmentEncoding p, enrollmentEncoding q, he, h⟩

/-- Partial shared-circuit signing. Stateful epochs select actual production leaves. -/
def sharedSign (p : Profile) (req : SessionScheduleReq) : Option PqHashSig :=
  if p.params.statefulJorts then
    mpcEvalProductionStatefulSign cshake256Suite p.params (sharedOracle p)
      p.material.pkSeed (payload p req) req.optRand req.reqEpoch p.grindLimit
  else
    mpcEvalProductionStatelessSign cshake256Suite p.params (sharedOracle p)
      p.material.pkSeed (payload p req) req.optRand p.grindLimit

/-- Efficient reference computation; equality to sharedSign is proved, including
    failure. This evaluator reconstructs the key and has no distributed-custody claim. -/
def referenceSign (p : Profile) (req : SessionScheduleReq) : Option PqHashSig :=
  if p.params.statefulJorts then
    evalProductionStatefulSign cshake256Suite p.params (referenceKey p)
      (payload p req) req.optRand req.reqEpoch p.grindLimit
  else
    evalProductionStatelessSign cshake256Suite p.params (referenceKey p)
      (payload p req) req.optRand p.grindLimit

theorem sharedSign_eq_reference (p : Profile) (req : SessionScheduleReq) :
    sharedSign p req = referenceSign p req := by
  unfold sharedSign referenceSign
  split
  · exact thresholdProductionStatefulSign_eq_evalProductionStatefulSign _ _ _ _
      (sharedOracle_matches p) _ _ _ _
  · exact thresholdProductionStatelessSign_eq_evalProductionStatelessSign _ _ _ _
      (sharedOracle_matches p) _ _ _

theorem sharedSign_verifies (p : Profile) (req : SessionScheduleReq) (sig : PqHashSig)
    (h : sharedSign p req = some sig) :
    verifyProductionPqHashSig cshake256Suite p.params (enrolledKey p) (payload p req) sig = true := by
  rw [sharedSign_eq_reference] at h
  unfold referenceSign at h
  split at h
  · exact verifyProductionPqHashSig_evalProductionStatefulSign _ _ _ _ _ _ _ _ h
  · exact verifyProductionPqHashSig_evalProductionStatelessSign _ _ _ _ _ _ _ h

inductive Failure where
  | signingUnavailable
  | encoding (reason : FaultStage)
  | wal (reason : WalRejectReason)
  deriving DecidableEq, Repr

def encodeResult (params : PqHashParams) : Option PqHashSig → Except Failure (List UInt8)
  | none => .error .signingUnavailable
  | some sig => match encodeProductionSigWire params sig with
    | .error reason => .error (.encoding reason)
    | .ok raw => .ok raw

def partialOutput (p : Profile) (req : SessionScheduleReq) : Except Failure (List UInt8) :=
  encodeResult p.params (sharedSign p req)

def referenceOutput (p : Profile) (req : SessionScheduleReq) : Except Failure (List UInt8) :=
  encodeResult p.params (referenceSign p req)

theorem partialOutput_eq_reference (p : Profile) (req : SessionScheduleReq) :
    partialOutput p req = referenceOutput p req := by
  unfold partialOutput referenceOutput
  rw [sharedSign_eq_reference]

/-- Released bytes encode exactly a successful shared computation and decode to a
    signature verified under the derived enrollment key, on the full request. -/
theorem partialOutput_sound (p : Profile) (req : SessionScheduleReq) (raw : List UInt8)
    (h : partialOutput p req = .ok raw) :
    ∃ sig, sharedSign p req = some sig ∧
      encodeProductionSigWire p.params sig = .ok raw ∧
      decodeProductionSigWire p.params raw = .ok sig ∧
      raw.length = p.params.wireSigBytes ∧
      verifyProductionPqHashSig cshake256Suite p.params (enrolledKey p) (payload p req) sig = true := by
  unfold partialOutput at h
  cases hs : sharedSign p req with
  | none => rw [hs] at h; cases h
  | some sig =>
    rw [hs] at h
    unfold encodeResult at h
    dsimp only at h
    cases he : encodeProductionSigWire p.params sig with
    | error err => rw [he] at h; cases h
    | ok bytes =>
      rw [he] at h
      cases h
      have hc := decodeProductionSigWire_encodeProductionSigWire p.params sig raw he
      exact ⟨sig, rfl, he, hc.2, hc.1, sharedSign_verifies p req sig hs⟩

theorem partialOutput_signing_failure (p : Profile) (req : SessionScheduleReq)
    (h : referenceSign p req = none) :
    partialOutput p req = .error .signingUnavailable := by
  unfold partialOutput
  rw [sharedSign_eq_reference, h]
  rfl

/-- Existing atomic WAL model wrapped around the actual partial result. Failure
    quarantines the attempted state; it is never converted into success bytes. -/
def releaseWith (p : Profile) (req : SessionScheduleReq) (wal : WalLatchState)
    (compute : Unit → Except Failure (List UInt8)) : WalLatchState × Except Failure (List UInt8) :=
  match walPreSignStep wal (enrollmentDigest p) req.reqEpoch (payload p req) with
  | .err st reason => (st, .error (.wal reason))
  | .ok st (.replayCached bytes) => (st, .ok (unpackWire bytes))
  | .ok st (.authorizedFresh epoch) =>
    match compute () with
    | .error reason => (walQuarantine st, .error reason)
    | .ok raw => (walCommitAuthorized st epoch (payload p req) (packWire raw), .ok raw)

def initial (p : Profile) : WalLatchState :=
  initWalLatchState (enrollmentDigest p)

def release (p : Profile) (req : SessionScheduleReq) (wal : WalLatchState) :=
  releaseWith p req wal (fun _ => partialOutput p req)

def referenceRelease (p : Profile) (req : SessionScheduleReq) (wal : WalLatchState) :=
  releaseWith p req wal (fun _ => referenceOutput p req)

theorem release_eq_reference (p : Profile) (req : SessionScheduleReq) (wal : WalLatchState) :
    release p req wal = referenceRelease p req wal := by
  unfold release referenceRelease
  simp only [partialOutput_eq_reference]

theorem release_fresh_sound (p : Profile) (req : SessionScheduleReq)
    (wal st : WalLatchState) (epoch : Nat) (raw : List UInt8)
    (hFresh : walPreSignStep wal (enrollmentDigest p) req.reqEpoch
      (payload p req) = .ok st (.authorizedFresh epoch))
    (hOut : (release p req wal).2 = .ok raw) :
    (release p req wal).1 = walCommitAuthorized st epoch (payload p req) (packWire raw) ∧
    ∃ sig, sharedSign p req = some sig ∧
      decodeProductionSigWire p.params raw = .ok sig ∧
      verifyProductionPqHashSig cshake256Suite p.params (enrolledKey p) (payload p req) sig = true := by
  unfold release releaseWith at hOut ⊢
  rw [hFresh] at hOut ⊢
  cases ho : partialOutput p req with
  | error err => rw [ho] at hOut; cases hOut
  | ok bytes =>
    rw [ho] at hOut
    dsimp only at hOut ⊢
    cases hOut
    obtain ⟨sig, hs, _, hd, _, hv⟩ := partialOutput_sound p req raw ho
    exact ⟨rfl, sig, hs, hd, hv⟩

theorem release_failure_quarantines (p : Profile) (req : SessionScheduleReq)
    (wal st : WalLatchState) (epoch : Nat) (err : Failure)
    (hFresh : walPreSignStep wal (enrollmentDigest p) req.reqEpoch
      (payload p req) = .ok st (.authorizedFresh epoch))
    (hFail : referenceOutput p req = .error err) :
    release p req wal = (walQuarantine st, .error err) := by
  unfold release releaseWith
  rw [hFresh, partialOutput_eq_reference, hFail]

theorem referenceSign_outOfRange (p : Profile) (req : SessionScheduleReq)
    (hMode : p.params.statefulJorts = true)
    (hRange : p.params.productionLeafIdxInRange req.reqEpoch = false) :
    referenceSign p req = none := by
  unfold referenceSign
  rw [hMode]
  simp only [↓reduceIte]
  rw [evalProductionStatefulSign_eq]
  simp only [hMode, hRange, Bool.not_true, Bool.not_false, Bool.or_true, ↓reduceIte]

theorem partialOutput_outOfRange (p : Profile) (req : SessionScheduleReq)
    (hMode : p.params.statefulJorts = true)
    (hRange : p.params.productionLeafIdxInRange req.reqEpoch = false) :
    partialOutput p req = .error .signingUnavailable :=
  partialOutput_signing_failure p req (referenceSign_outOfRange p req hMode hRange)

/-- A committed request retries exactly without executing the signing thunk. -/
theorem release_exact_retry (p : Profile) (req : SessionScheduleReq)
    (raw : List UInt8) (hEpoch : req.reqEpoch = 0) :
    let st := walCommitAuthorized (initial p) 0 (payload p req) (packWire raw)
    release p req st = (st, .ok raw) := by
  simp only [release, releaseWith, initial, walPreSignStep, walCommitAuthorized,
    initWalLatchState, hEpoch, decide_true, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, Nat.reduceBEq, Bool.and_true, unpackWire_packWire]

/-- Changing any request field at the committed epoch cannot recover its cached
    bytes through the release adapter. -/
theorem release_changed_request_rejected (p : Profile) (req changed : SessionScheduleReq)
    (raw : List UInt8) (hEpoch : changed.reqEpoch = 0) (hDifferent : changed ≠ req) :
    let st := walCommitAuthorized (initial p) 0 (payload p req) (packWire raw)
    release p changed st = (st, .error (.wal .staleOrOutOfOrderEpoch)) := by
  have hNe : payload p changed ≠ payload p req :=
    fun h => hDifferent (payload_request_binding h)
  simp only [release, releaseWith, initial, walPreSignStep, walCommitAuthorized,
    initWalLatchState, hEpoch, hNe, decide_true, decide_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, Nat.reduceBEq, Bool.and_false]
  rfl

theorem initial_fresh (p : Profile) (req : SessionScheduleReq)
    (hEpoch : req.reqEpoch = 0) :
    walPreSignStep (initial p) (enrollmentDigest p) req.reqEpoch (payload p req) =
      .ok (initial p) (.authorizedFresh 0) := by
  simp only [initial, initWalLatchState, walPreSignStep, hEpoch, decide_true,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.reduceBEq]

theorem release_profile_mismatch (p q : Profile) (req : SessionScheduleReq)
    (h : enrollmentDigest q ≠ enrollmentDigest p) :
    (release q req (initial p)).2 = .error (.wal .pkDigestMismatch) := by
  simp only [release, releaseWith, initial, initWalLatchState, walPreSignStep,
    h, decide_false, Bool.not_false, Bool.false_eq_true, ↓reduceIte]

#verify_constructive enrollmentDigest_length enrollmentEncoding_binding initial_fresh
  release_profile_mismatch encodeParameters_injective payload_profile_binding
  referenceSign_outOfRange partialOutput_outOfRange release_exact_retry release_changed_request_rejected
  sharedOracle_matches enrollment_from_shared_computation
  payload_request_binding payload_enrollment_binding sharedSign_eq_reference sharedSign_verifies
  partialOutput_eq_reference partialOutput_sound partialOutput_signing_failure
  release_eq_reference release_fresh_sound release_failure_quarantines

end Qsag.RssProduction
end

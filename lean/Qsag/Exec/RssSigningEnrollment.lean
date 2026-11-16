module
public import Qsag.Exec.RssSigningExecution
public import Qsag.Exec.RssSigningControl
public import Qsag.Exec.RssSigningProgram
public import Qsag.Exec.RssProductionProfile
public import Qsag.Protocol.Threshold.ThresholdMpc
public import Qsag.Protocol.Signing.HashSigs
import Qsag.Tactic.AssuranceKit

/-!
Public-only online enrollment interface. Its constructor derives the key with
the actual shared oracle; no reconstructed reference key is used by online
control or request framing. Rust's bound-key entry fixes opt_rand and omits
online DKG. Exact evaluator equalities preserve the old shared specification.
Grouped-cut timing and enrollment transcript simulation remain separate.
-/
public section
namespace Qsag.RssSigning
set_option autoImplicit false

structure PublicEnrollment where
  params : PqHashParams
  key : PqPublicKey
  context : Bytes
  grindLimit : Nat

def sharedEnrollment (profile : RssProduction.Profile) : PublicEnrollment :=
  ⟨profile.params, derivePublicKeyMpc cshake256Suite profile.params
    (RssProduction.sharedOracle profile).toPqHashMpcOracles profile.material.pkSeed,
    profile.context, profile.grindLimit⟩

theorem sharedEnrollment_key (profile : RssProduction.Profile) :
    (sharedEnrollment profile).key = RssProduction.enrolledKey profile :=
  RssProduction.enrollment_from_shared_computation profile

def publicPayload (enrollment : PublicEnrollment) (request : SessionScheduleReq) : Bytes :=
  encodeMultiFrame ["QSAG.RSS.PRODUCTION.REQUEST/v1".toUTF8.data.toList,
    encodeUcPqPublicKey enrollment.key, RssProduction.encodeParameters enrollment.params,
    enrollment.context, leb128 enrollment.grindLimit, encodeUcSigningRequest request]

theorem publicPayload_eq (profile : RssProduction.Profile) (request : SessionScheduleReq) :
    publicPayload (sharedEnrollment profile) request = RssProduction.payload profile request := by
  unfold publicPayload RssProduction.payload
  rw [sharedEnrollment_key]
  rfl

def publicPrepared (enrollment : PublicEnrollment) (request : SessionScheduleReq) : Prepared :=
  ⟨publicPayload enrollment request⟩

theorem publicPrepared_eq (profile : RssProduction.Profile) (request : SessionScheduleReq) :
    publicPrepared (sharedEnrollment profile) request = preparePublic profile request := by
  unfold publicPrepared preparePublic
  rw [publicPayload_eq]

def enrolledStateful (enrollment : PublicEnrollment) (msg optRand : Bytes)
    (epoch : Nat) : Program (Option PqHashSig) :=
  if !enrollment.params.statefulJorts || !enrollment.params.productionWellFormed ||
      !enrollment.params.productionLeafIdxInRange epoch then pure none
  else
    let pk := enrollment.key
    let mu := thPreHash cshake256Suite pk.pkSeed pk.pkRoot msg
    do
      let rRand ← ask (.prfMsg optRand mu)
      core cshake256Suite enrollment.params pk.pkSeed pk msg mu rRand epoch none enrollment.grindLimit

def enrolledStateless (enrollment : PublicEnrollment) (msg optRand : Bytes) : Program (Option PqHashSig) :=
  if enrollment.params.statefulJorts || !enrollment.params.productionWellFormed then pure none
  else
    let pk := enrollment.key
    let mu := thPreHash cshake256Suite pk.pkSeed pk.pkRoot msg
    do
      let rRand ← ask (.prfMsg optRand mu)
      match deriveProductionStatelessInputs cshake256Suite enrollment.params rRand pk.pkSeed pk.pkRoot mu with
      | none => pure none
      | some (leaf, indices) =>
        core cshake256Suite enrollment.params pk.pkSeed pk msg mu rRand leaf
          (some indices) enrollment.grindLimit

private theorem enrolledStateful_of_key (enrollment : PublicEnrollment)
    (o : ProductionPqHashMpcOracles) (msg optRand : Bytes) (epoch : Nat)
    (hk : derivePublicKeyMpc cshake256Suite enrollment.params o.toPqHashMpcOracles
      enrollment.key.pkSeed = enrollment.key) :
    evaluate o (enrolledStateful enrollment msg optRand epoch) =
      mpcEvalProductionStatefulSign cshake256Suite enrollment.params o enrollment.key.pkSeed
        msg optRand epoch enrollment.grindLimit := by
  simp only [enrolledStateful, mpcEvalProductionStatefulSign]
  split
  · rfl
  · rw [hk]
    simp only [evaluate_bind, evaluate_ask, answer, evaluate_core]

private theorem enrolledStateless_of_key (enrollment : PublicEnrollment)
    (o : ProductionPqHashMpcOracles) (msg optRand : Bytes)
    (hk : derivePublicKeyMpc cshake256Suite enrollment.params o.toPqHashMpcOracles
      enrollment.key.pkSeed = enrollment.key) :
    evaluate o (enrolledStateless enrollment msg optRand) =
      mpcEvalProductionStatelessSign cshake256Suite enrollment.params o enrollment.key.pkSeed
        msg optRand enrollment.grindLimit := by
  simp only [enrolledStateless, mpcEvalProductionStatelessSign]
  split
  · rfl
  · rw [hk]
    simp only [evaluate_bind, evaluate_ask, answer]
    split <;> simp_all only [evaluate_pure, evaluate_core]

theorem evaluate_enrolledStateful (profile : RssProduction.Profile) (msg optRand : Bytes) (epoch : Nat) :
    evaluate (RssProduction.sharedOracle profile)
      (enrolledStateful (sharedEnrollment profile) msg optRand epoch) =
      mpcEvalProductionStatefulSign cshake256Suite profile.params (RssProduction.sharedOracle profile)
        profile.material.pkSeed msg optRand epoch profile.grindLimit :=
  enrolledStateful_of_key (sharedEnrollment profile) (RssProduction.sharedOracle profile)
    msg optRand epoch (by rfl)

theorem evaluate_enrolledStateless (profile : RssProduction.Profile) (msg optRand : Bytes) :
    evaluate (RssProduction.sharedOracle profile)
      (enrolledStateless (sharedEnrollment profile) msg optRand) =
      mpcEvalProductionStatelessSign cshake256Suite profile.params (RssProduction.sharedOracle profile)
        profile.material.pkSeed msg optRand profile.grindLimit :=
  enrolledStateless_of_key (sharedEnrollment profile) (RssProduction.sharedOracle profile)
    msg optRand (by rfl)

def enrolledSigningProgram (enrollment : PublicEnrollment) (request : SessionScheduleReq) :
    Program (Option PqHashSig) :=
  if enrollment.params.statefulJorts then
    enrolledStateful enrollment (publicPayload enrollment request) request.optRand request.reqEpoch
  else enrolledStateless enrollment (publicPayload enrollment request) request.optRand

theorem enrolledSigningProgram_refines (profile : RssProduction.Profile) (request : SessionScheduleReq) :
    evaluate (RssProduction.sharedOracle profile) (enrolledSigningProgram (sharedEnrollment profile) request) =
      RssProduction.sharedSign profile request := by
  have hp : (sharedEnrollment profile).params = profile.params := rfl
  simp only [enrolledSigningProgram, publicPayload_eq, RssProduction.sharedSign, hp]
  split <;> simp only [evaluate_enrolledStateful, evaluate_enrolledStateless]

/-- Public enrollment + separate local share material are the executable inputs;
referenceKey and RssProduction.payload are absent from the executable body. -/
def enrolledExecution (enrollment : PublicEnrollment) (material : RssProduction.Material)
    (request : SessionScheduleReq) (tape : ParticipantTape) (first : Nat := 0) :
    Execution (Option PqHashSig) :=
  runPrepared (publicPrepared enrollment request) material tape first (enrolledSigningProgram enrollment request)

theorem enrolledExecution_refines (profile : RssProduction.Profile) (request : SessionScheduleReq)
    (tape : ParticipantTape) (first : Nat) :
    (enrolledExecution (sharedEnrollment profile) profile.material request tape first).result =
      RssProduction.sharedSign profile request := by
  unfold enrolledExecution
  rw [publicPrepared_eq, runPrepared_result, enrolledSigningProgram_refines]

/-- The public-only enrolled computation preserves actual encoding errors and
signing failure as well as successful wire bytes. No success premise is used. -/
theorem enrolledExecution_wire_refines (profile : RssProduction.Profile) (request : SessionScheduleReq)
    (tape : ParticipantTape) (first : Nat) :
    RssProduction.encodeResult (sharedEnrollment profile).params
      (enrolledExecution (sharedEnrollment profile) profile.material request tape first).result =
        RssProduction.partialOutput profile request := by
  rw [enrolledExecution_refines]
  rfl

/-- Exact keccak_mpc.rs tsw_rss_opt_rand domain/frame; it is different from
`build_stateless_det_opt_domain` in tsw_baggy.rs. -/
def rustRssOptRand (pk : PqPublicKey) : Bytes :=
  cshake256Bytes "QSAG.TSW.RSS.OPT_RAND/v1".toUTF8.data.toList
    (encodeMultiFrame [pk.pkSeed, pk.pkRoot])

def rustStatelessProgram (enrollment : PublicEnrollment) (message : Bytes) : Program (Option PqHashSig) :=
  enrolledStateless enrollment message (rustRssOptRand enrollment.key)

theorem rustStatelessProgram_refines (profile : RssProduction.Profile) (message : Bytes) :
    evaluate (RssProduction.sharedOracle profile) (rustStatelessProgram (sharedEnrollment profile) message) =
      mpcEvalProductionStatelessSign cshake256Suite profile.params (RssProduction.sharedOracle profile)
        profile.material.pkSeed message (rustRssOptRand (sharedEnrollment profile).key) profile.grindLimit :=
  evaluate_enrolledStateless profile message _

/-- The first private computation after public enrollment is PRF-msg. -/
theorem enrolledStateless_first_request (enrollment : PublicEnrollment) (message optRand : Bytes)
    (hs : enrollment.params.statefulJorts = false) (hw : enrollment.params.productionWellFormed = true) :
    ∃ next, enrolledStateless enrollment message optRand =
      .query (.prfMsg optRand (thPreHash cshake256Suite enrollment.key.pkSeed enrollment.key.pkRoot message)) next := by
  simp only [enrolledStateless, hs, hw, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, rfl⟩

#verify_constructive sharedEnrollment_key publicPayload_eq publicPrepared_eq evaluate_enrolledStateful
  evaluate_enrolledStateless enrolledSigningProgram_refines enrolledExecution_refines enrolledExecution_wire_refines
  rustStatelessProgram_refines enrolledStateless_first_request
end Qsag.RssSigning

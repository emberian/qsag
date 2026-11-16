module
/-
# Qsag.Top.ClosedProtocolReductions — closed reductions from the executable verifiers to security games

Top-level statements (zero `import all`) in `Spec.GameBound` form. Each is one implication
from an execution of the verifier to explicit reduction events, not a tuple of lemmas.

1. `whir_exec_closed_qrom_soundness`: for a statement outside the language and any `Q`-query
   Fiat–Shamir adversary, `Pr[execWhirVerify accepts] ≤ scheduleQromError sched Q +
   Pr[the collision finder outputs a Merkle-hash collision]`. `whirCollisionReduction` turns
   the finder's output into a `Spec.HashCollision` of the underlying byte hash, and
   `whirCollisionReduction_validBreak` shows that output is a `Spec.ValidBreak`: a collision of
   the byte hash. It is a break of `Spec.AggregateSoundnessOutcome` only together with the fact
   that both inputs are recorded prover queries (`Spec.TranscriptBreak`), which this reduction
   does not state.
   `deployed_whir_exec_closed_qrom_128` instantiates the `nv = 24` schedule at `Q ≤ 2^40`.
2. `jorts_baggy_closed_euf_cma_keyed_target_bound`: for the adversary-driven experiment with
   the epoch latch, `Pr[ExecEufCmaGame wins] ≤ εI + prodPathTargetCount · εT +
   prodPreCandidateCount · εP`, where the three `ε` bound games played by explicit adversaries
   that receive the public key and the hash and signing oracles only.
   `jorts_baggy_closed_euf_cma_same_trace_classification` is the partition of the winning coins
   by the extractor run on the whole outcome.

Standing assumptions, stated where they enter:
* the WHIR theorems take a `ClosedWhir.WhirScheduleCert` (a Boolean round-by-round state
  function of the verifier with flip counts inside the schedule's round bounds); none is
  constructed for a schedule with stages;
* the adversary's output carries the committed tables, and the Fiat–Shamir oracle is queried
  on whole message prefixes (`ClosedFs` module header);
* the signature bound takes hardness of the subset-cover game and of two keyed games
  (`ExecSubsetCoverHard`, `ExecKeyedPathCollisionHard`, `ExecKeyedSecretPreimageHard`) as
  hypotheses, for classes containing the reduction adversaries. The keyed games have the
  signer's own hash inputs as targets; they are not the `SM-DT-TCR` / `SM-DT-PRE` experiments
  of `Spec.Assumptions`, and no reduction to those is proved.
-/

public import Qsag.Spec.GameBound
public import Qsag.Spec.Assumptions
public import Qsag.Spec.IdealAggregate
public import Qsag.Protocol.Aggregation.ClosedFsQromCompile
public import Qsag.Protocol.Aggregation.ClosedWhirSchedule
public import Qsag.Protocol.Signing.ExecEufCmaClosedGame
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Top

set_option autoImplicit false

/-! ## 1. Executable WHIR verifier: closed QROM soundness -/

section Whir
variable {F D : Type} [CommRingOps F] [DecidableEq F] [DecidableEq D]

/-- Probability that the executable WHIR verifier accepts the output of the `Q`-query adversary
    `A`, over the uniform Fiat–Shamir oracle and the final measurement. -/
def WhirSoundnessWinProb {cardX cardAnc Q w : Nat}
    (env : Qsag.ClosedWhir.WhirEnv F) (sched : Qsag.ClosedWhir.WhirVerifierSchedule)
    (M : Qsag.ClosedFs.MerkleSetup D F)
    (c : Qsag.ClosedFs.FsCodec (Qsag.ClosedWhir.WhirMsg F) sched.numRounds cardX)
    (aux : Fin cardX → List (F × List D)) (x : Qsag.ClosedWhir.WhirStmt F)
    (A : Qsag.QuantumAdv cardX w cardAnc Q) : Qsag.RatBound :=
  ⟨Qsag.uniformOracleSum w cardX (fun H =>
      Qsag.QVec.queryMassOn
        (Qsag.ClosedFs.execFsAccept (Qsag.ClosedWhir.whirOracleIop env sched w) M c aux x H)
        (Qsag.runQuantumAdv A H)),
    (2 ^ w) ^ cardX * (Qsag.prefixScale A Q (Nat.le_refl Q) * Qsag.QVec.stateNormSq A.init),
    Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos w))
      (Nat.mul_pos (Qsag.prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩

/-- Probability that the verifier accepts and the collision finder outputs a collision of the
    Merkle hash: the success probability of the collision reduction. -/
def WhirMerkleCollisionWinProb {cardX cardAnc Q w : Nat}
    (env : Qsag.ClosedWhir.WhirEnv F) (sched : Qsag.ClosedWhir.WhirVerifierSchedule)
    (M : Qsag.ClosedFs.MerkleSetup D F)
    (c : Qsag.ClosedFs.FsCodec (Qsag.ClosedWhir.WhirMsg F) sched.numRounds cardX)
    (aux : Fin cardX → List (F × List D)) (x : Qsag.ClosedWhir.WhirStmt F)
    (A : Qsag.QuantumAdv cardX w cardAnc Q) : Qsag.RatBound :=
  ⟨Qsag.uniformOracleSum w cardX (fun H =>
      Qsag.QVec.queryMassOn
        (Qsag.ClosedFs.execFsCollisionEvent (Qsag.ClosedWhir.whirOracleIop env sched w) M c aux x H)
        (Qsag.runQuantumAdv A H)),
    (2 ^ w) ^ cardX * (Qsag.prefixScale A Q (Nat.le_refl Q) * Qsag.QVec.stateNormSq A.init),
    Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos w))
      (Nat.mul_pos (Qsag.prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩

/-- **Closed QROM soundness of the executable multi-round WHIR verifier.** -/
theorem whir_exec_closed_qrom_soundness {cardX cardAnc Q w : Nat}
    (env : Qsag.ClosedWhir.WhirEnv F) (sched : Qsag.ClosedWhir.WhirVerifierSchedule)
    (M : Qsag.ClosedFs.MerkleSetup D F)
    (sc : Qsag.ClosedWhir.WhirScheduleCert env sched w)
    (c : Qsag.ClosedFs.FsCodec (Qsag.ClosedWhir.WhirMsg F) sched.numRounds cardX)
    (aux : Fin cardX → List (F × List D))
    (x : Qsag.ClosedWhir.WhirStmt F) (hx : ¬ Qsag.ClosedWhir.whirInLang env sched x)
    (A : Qsag.QuantumAdv cardX w cardAnc Q) :
    Qsag.Spec.GameBound
      (Qsag.Spec.RatBound.ofBudget (WhirSoundnessWinProb env sched M c aux x A))
      (Qsag.Spec.RatBound.ofBudget
        (Qsag.RatBound.add (Qsag.ClosedWhir.scheduleQromError sched Q)
          (WhirMerkleCollisionWinProb env sched M c aux x A))) :=
  (Qsag.Spec.RatBound.ofBudget_le_iff _ _).mpr
    (Qsag.ClosedWhir.whir_exec_closed_qrom_soundness env sched M sc c aux x hx A)

/-- **Deployed `nv = 24` schedule, `Q ≤ 2^40`: `2^-128` plus the collision reduction.** -/
theorem deployed_whir_exec_closed_qrom_128 {cardX cardAnc Q w : Nat}
    (env : Qsag.ClosedWhir.WhirEnv F) (M : Qsag.ClosedFs.MerkleSetup D F)
    (sc : Qsag.ClosedWhir.WhirScheduleCert env Qsag.ClosedWhir.deployedSched w)
    (c : Qsag.ClosedFs.FsCodec (Qsag.ClosedWhir.WhirMsg F)
      Qsag.ClosedWhir.deployedSched.numRounds cardX)
    (aux : Fin cardX → List (F × List D))
    (x : Qsag.ClosedWhir.WhirStmt F)
    (hx : ¬ Qsag.ClosedWhir.whirInLang env Qsag.ClosedWhir.deployedSched x)
    (A : Qsag.QuantumAdv cardX w cardAnc Q) (hQ : Q ≤ 2 ^ 40) :
    Qsag.Spec.GameBound
      (Qsag.Spec.RatBound.ofBudget
        (WhirSoundnessWinProb env Qsag.ClosedWhir.deployedSched M c aux x A))
      (Qsag.Spec.RatBound.ofBudget
        (Qsag.RatBound.add (Qsag.RatBound.invPow2 128)
          (WhirMerkleCollisionWinProb env Qsag.ClosedWhir.deployedSched M c aux x A))) :=
  (Qsag.Spec.RatBound.ofBudget_le_iff _ _).mpr
    (Qsag.ClosedWhir.deployed_whir_exec_closed_qrom_128 env M sc c aux x hx A hQ)

end Whir

/-- **The collision reduction's output.** With the Merkle hash realized by a byte hash `Hb`
    through prefix-free framings, every output on which the collision event holds yields an
    explicit `Spec.HashCollision Hb`. -/
def whirCollisionReduction {F : Type} [CommRingOps F] [DecidableEq F] {cardX w : Nat}
    (Hb : Qsag.Spec.Bytes → Qsag.Spec.Bytes)
    (nodeC : Qsag.Spec.FramedCodec (Nat × Nat × Qsag.Spec.Bytes × Qsag.Spec.Bytes))
    (leafC : Qsag.Spec.FramedCodec (Nat × Nat × F))
    (env : Qsag.ClosedWhir.WhirEnv F) (sched : Qsag.ClosedWhir.WhirVerifierSchedule)
    (c : Qsag.ClosedFs.FsCodec (Qsag.ClosedWhir.WhirMsg F) sched.numRounds cardX)
    (aux : Fin cardX → List (F × List Qsag.Spec.Bytes)) (x : Qsag.ClosedWhir.WhirStmt F)
    (H : Fin cardX → BitVec w) (o : Fin cardX)
    (h : Qsag.ClosedFs.execFsCollisionEvent (Qsag.ClosedWhir.whirOracleIop env sched w)
      (Qsag.ClosedFs.framedSetup Hb nodeC leafC) c aux x H o = true) :
    Qsag.Spec.HashCollision Hb :=
  Qsag.ClosedFs.CollisionWitness.toHashCollision Hb nodeC leafC
    (Qsag.ClosedFs.execFsCollisionWitness (Qsag.ClosedWhir.whirOracleIop env sched w)
      (Qsag.ClosedFs.framedSetup Hb nodeC leafC) c aux x H o h)

/-- The collision reduction's output is a validated break of the byte hash `Hb`
    (`Spec.ValidBreak`). Membership of its two inputs in a prover's oracle transcript, which
    `Spec.TranscriptBreak` also requires, is not part of this statement. -/
theorem whirCollisionReduction_validBreak {F : Type} [CommRingOps F] [DecidableEq F]
    {cardX w : Nat}
    (Hb : Qsag.Spec.Bytes → Qsag.Spec.Bytes)
    (nodeC : Qsag.Spec.FramedCodec (Nat × Nat × Qsag.Spec.Bytes × Qsag.Spec.Bytes))
    (leafC : Qsag.Spec.FramedCodec (Nat × Nat × F))
    (env : Qsag.ClosedWhir.WhirEnv F) (sched : Qsag.ClosedWhir.WhirVerifierSchedule)
    (c : Qsag.ClosedFs.FsCodec (Qsag.ClosedWhir.WhirMsg F) sched.numRounds cardX)
    (aux : Fin cardX → List (F × List Qsag.Spec.Bytes)) (x : Qsag.ClosedWhir.WhirStmt F)
    (H : Fin cardX → BitVec w) (o : Fin cardX)
    (h : Qsag.ClosedFs.execFsCollisionEvent (Qsag.ClosedWhir.whirOracleIop env sched w)
      (Qsag.ClosedFs.framedSetup Hb nodeC leafC) c aux x H o = true) :
    Qsag.Spec.ValidBreak Hb
      ⟨(whirCollisionReduction Hb nodeC leafC env sched c aux x H o h).m₁,
       (whirCollisionReduction Hb nodeC leafC env sched c aux x H o h).m₂⟩ :=
  (whirCollisionReduction Hb nodeC leafC env sched c aux x H o h).validBreak

/-! ## 2. Closed adaptive EUF-CMA experiment with the epoch latch -/

/-- **Same-trace classification of the closed EUF-CMA experiment.** The adversary-driven
    experiment `ExecEufCmaGame` (executable signer behind a monotone epoch latch, executable
    verifier on a fresh message) is bounded by the probabilities of the three extractor events
    on its own trace. The events are computed from the whole outcome, secret key included. -/
theorem jorts_baggy_closed_euf_cma_same_trace_classification {n qHash qSign : Nat} (hPos : 0 < n)
    (suite : Qsag.TweakableHashSuite) (params : Qsag.PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16)
    (keygen : Fin n → Qsag.PqSecretKey)
    (adv : Fin n → Qsag.SeedWithheldEufCmaAdv qHash qSign) :
    Qsag.Spec.GameBound (Qsag.ExecEufCmaGame hPos suite params keygen adv).winProb
      ((Qsag.execEufCmaItsrReduction hPos suite params hw keygen adv).winProb.add
        ((Qsag.execEufCmaTcrReduction hPos suite params hw keygen adv).winProb.add
          (Qsag.execEufCmaPreReduction hPos suite params hw keygen adv).winProb)) :=
  _root_.Qsag.jorts_baggy_closed_euf_cma_same_trace_classification hPos suite params hw keygen adv

/-- **Closed EUF-CMA bound by three games played without the secret key.** The key is uniform
    on `KeyOk` and read from the challenger coordinate; the forger reads the adversary
    coordinate. The reduction adversaries (`adv a` itself, `execCollisionReductionAdv params
    slot (adv a)`, `execPreimageReductionAdv params slot (adv a)`) receive the public key and
    the oracles, and carry their query budgets in their types. Hardness of the subset-cover
    game and of the two keyed games against classes containing them bounds the forger. -/
theorem jorts_baggy_closed_euf_cma_keyed_target_bound {n nK nA qHash qSign : Nat} (hPos : 0 < n)
    (suite : Qsag.TweakableHashSuite) (params : Qsag.PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16)
    (π : Qsag.Spec.CoinSplit n nK nA)
    (keygen : Fin nK → Qsag.PqSecretKey) {KeyOk : Qsag.PqSecretKey → Prop}
    (hKey : Qsag.Spec.UniformOn KeyOk keygen)
    (adv : Fin nA → Qsag.SeedWithheldEufCmaAdv qHash qSign)
    {𝒜I : (Qsag.PqPublicKey → Qsag.ProdAdaptiveTree (List UInt8 × Qsag.PqHashSig)) → Prop}
    {𝒜T : (Qsag.PqPublicKey → Qsag.ProdAdaptiveTree (Option Qsag.SmDtTcrSubmission)) → Prop}
    {𝒜P : (Qsag.PqPublicKey → Qsag.ProdAdaptiveTree (Option Qsag.SmDtPreSubmission)) → Prop}
    (hAI : ∀ a : Fin nA, 𝒜I (adv a).run)
    (hAT : ∀ (slot : Nat) (a : Fin nA),
      𝒜T (Qsag.execCollisionReductionAdv params slot (adv a)).run)
    (hAP : ∀ (slot : Nat) (a : Fin nA),
      𝒜P (Qsag.execPreimageReductionAdv params slot (adv a)).run)
    {εI εT εP : Qsag.Spec.RatBound}
    (hI : Qsag.ExecSubsetCoverHard 𝒜I suite params KeyOk qHash qSign εI)
    (hT : Qsag.ExecKeyedPathCollisionHard 𝒜T suite params KeyOk
      (qHash + Qsag.prodTcrReductionHashBudget params) qSign εT)
    (hP : Qsag.ExecKeyedSecretPreimageHard 𝒜P suite params KeyOk
      (qHash + (1 + Qsag.prodXofHashBudget params)) qSign εP) :
    Qsag.Spec.GameBound
      (Qsag.ExecEufCmaGame hPos suite params (fun ω => keygen (π.chal ω))
        (fun ω => adv (π.advc ω))).winProb
      ((εI.add (Qsag.Spec.RatBound.scale (Qsag.prodPathTargetCount params qSign) εT)).add
        (Qsag.Spec.RatBound.scale (Qsag.prodPreCandidateCount params) εP)) :=
  _root_.Qsag.jorts_baggy_closed_euf_cma_keyed_target_bound hPos suite params hw π keygen hKey adv
    hAI hAT hAP hI hT hP

#verify_constructive
  Qsag.Top.whir_exec_closed_qrom_soundness
  Qsag.Top.deployed_whir_exec_closed_qrom_128
  Qsag.Top.whirCollisionReduction_validBreak
  Qsag.Top.jorts_baggy_closed_euf_cma_same_trace_classification
  Qsag.Top.jorts_baggy_closed_euf_cma_keyed_target_bound

end Qsag.Top
end

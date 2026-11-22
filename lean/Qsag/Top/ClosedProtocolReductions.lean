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

Standing assumptions and explicit boundaries, stated where they enter:
* **`WhirScheduleCert`.** Two unconditional certificates are constructed in `ClosedWhir`:
  1. `flatHemSlicedWhir_closed_qrom_soundness` and
     `flatHemSlicedWhir_succinct_closed_qrom_soundness` (`flatHemSlicedWhir_nonvacuity`) discharge
     `ClosedWhir.WhirScheduleCert` unconditionally on the two-stage (`6`-round) schedule
     `ClosedWhir.flatHemSlicedSched` (`64 → 32 → 16` coset chain over `QuarticGoldilocks`,
     `q = 2^62`, `w = 256`) using **strictly proved `[CWYZ26]` sliced MCA counts**
     (`sliced_singleStep_bridge_four_challenge_bound`, `WhirStage.decode_list_le`), exercising fold,
     out-of-domain, and shift-query rounds with `scheduleQromError < 2^-20 < 1`;
  2. `sampledQueryWhir_closed_qrom_soundness` (`sampledQueryWhir_nonvacuity`) certifies a one-stage
     toy schedule with one sampled query (`scheduleQromError > 1`).
  By contrast, `deployed_whir_exec_closed_qrom_128` for the `nv = 24` schedule remains conditional:
  it takes `ClosedWhir.WhirScheduleCert env deployedSched w` as a hypothesis, and `deployedStages`
  uses the profile input `whirAffineStageSimpleNum`, which the proved sliced MCA counts do not
  reach;
* **`zk-Hem v2` schedules (§1c).** `zkHemV2QuinticWhir_closed_qrom_soundness` discharges the
  certificate on `ZkHemV2Cert.zkHemV2QuinticSched`: one stage, no fold round, a 64-point coset
  over `QuinticGoldilocks`, challenge width `400`. It is not a deployed table size.
  `zkHemV2_deployed_succinct_qrom_gameBound_128` concerns the deployed family
  `ZkHemV2Cert.zkHemV2ProdSched logCells` (`16 ≤ logCells ≤ 28`, `Q ≤ 2^64`) and is conditional:
  it takes `ClosedWhir.WhirScheduleCert env (zkHemV2ProdSched logCells) 400` and the Merkle
  collision bound `ZkHemV2Cert.merkle400QromBound Q` as hypotheses. Proved without hypotheses:
  `scheduleQromError (zkHemV2ProdSched logCells) Q + 6680 · Q^3 / 2^400 < 2^-128`;
* **Succinct vs. table-carrying Fiat–Shamir:** `whir_succinct_closed_qrom_soundness` and
  `whirSuccinctCollisionReduction` (`whirSuccinctCollisionReduction_validBreak`) hash ONLY succinct
  `(Option D, WhirPub F)` message prefixes in the Fiat–Shamir oracle and verify authentication
  paths against wire-transmitted Merkle roots (`ClosedFs.succinct_fs_qrom_closed_soundness`),
  whereas `whir_exec_closed_qrom_soundness` places full tables in `WhirMsg`;
* **Signature reductions:** `jorts_baggy_closed_euf_cma_keyed_target_bound` reduces directly to
  `ExecSubsetCoverHard`, `ExecKeyedPathCollisionHard`, and `ExecKeyedSecretPreimageHard`, while
  `jorts_baggy_closed_euf_cma_prf_keygen_hop` and
  `jorts_baggy_closed_euf_cma_spec_assumptions_bound` connect `ExecEufCmaGame` to canonical
  `Spec.PrfHard`, `Spec.ItsrHard`, `Spec.SmDtTcrHard`, and `Spec.SmDtPreHard` locales (inhabited
  unconditionally at `6 / 256 < 1` by `concrete_exec_euf_cma_spec_assumptions_witness`).
-/

public import Qsag.Spec.GameBound
public import Qsag.Spec.Assumptions
public import Qsag.Spec.IdealAggregate
public import Qsag.Protocol.Aggregation.ClosedFsQromCompile
public import Qsag.Protocol.Aggregation.ClosedWhirSchedule
public import Qsag.Protocol.Aggregation.ZkHemV2ScheduleCert
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

/-- **Conditional on `WhirScheduleCert` for `deployedSched` (`nv = 24`, `Q ≤ 2^40`): `2^-128`
    plus the collision reduction.** Explicit open obligation: constructing `sc` for the 4-stage
    `deployedSched` (whose `mcaNum` uses `whirAffineStageSimpleNum`). -/
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

/-- **`whir_exec_closed_qrom_soundness` with its certificate hypothesis discharged**, on the
    one-stage schedule `ClosedWhir.sampledQuerySched` at challenge width two
    (`ClosedWhir.sampledQueryCert`). The schedule is a toy with a single sampled query and no
    fold, sumcheck or out-of-domain round; its `scheduleQromError` is above one, so this instance
    shows that the theorem's hypotheses are jointly satisfiable by a verifier with a stage, and
    carries no numerical security claim. -/
theorem sampledQueryWhir_closed_qrom_soundness {D : Type} [DecidableEq D]
    {cardX cardAnc Q : Nat}
    (M : Qsag.ClosedFs.MerkleSetup D Qsag.Goldilocks)
    (c : Qsag.ClosedFs.FsCodec (Qsag.ClosedWhir.WhirMsg Qsag.Goldilocks)
      Qsag.ClosedWhir.sampledQuerySched.numRounds cardX)
    (aux : Fin cardX → List (Qsag.Goldilocks × List D))
    (x : Qsag.ClosedWhir.WhirStmt Qsag.Goldilocks)
    (hx : ¬ Qsag.ClosedWhir.whirInLang Qsag.ClosedWhir.sampledQueryEnv
      Qsag.ClosedWhir.sampledQuerySched x)
    (A : Qsag.QuantumAdv cardX 2 cardAnc Q) :
    Qsag.Spec.GameBound
      (Qsag.Spec.RatBound.ofBudget
        (WhirSoundnessWinProb Qsag.ClosedWhir.sampledQueryEnv
          Qsag.ClosedWhir.sampledQuerySched M c aux x A))
      (Qsag.Spec.RatBound.ofBudget
        (Qsag.RatBound.add
          (Qsag.ClosedWhir.scheduleQromError Qsag.ClosedWhir.sampledQuerySched Q)
          (WhirMerkleCollisionWinProb Qsag.ClosedWhir.sampledQueryEnv
            Qsag.ClosedWhir.sampledQuerySched M c aux x A))) :=
  whir_exec_closed_qrom_soundness Qsag.ClosedWhir.sampledQueryEnv
    Qsag.ClosedWhir.sampledQuerySched M Qsag.ClosedWhir.sampledQueryCert c aux x hx A

/-- What the one-stage instance has that the empty schedule lacks: a stage passing the Johnson
    check, an honest transcript the verifier accepts, a statement outside the language, a
    challenge on which that false statement is still accepted, and a nonzero certified flip
    count for the query round. -/
theorem sampledQueryWhir_nonvacuity :
    Qsag.ClosedWhir.sampledQuerySched.stages.length = 1 ∧
    Qsag.ClosedWhir.sampledQuerySched.johnsonOk = true ∧
    (Qsag.ClosedWhir.whirOracleIop Qsag.ClosedWhir.sampledQueryEnv
      Qsag.ClosedWhir.sampledQuerySched 2).verify
      ⟨[Qsag.Goldilocks.one, Qsag.Goldilocks.one, Qsag.Goldilocks.one, Qsag.Goldilocks.one],
       Qsag.Goldilocks.one⟩
      [(⟨[], [Qsag.Goldilocks.one], []⟩, 0), (⟨[], [], []⟩, 0)] = true ∧
    ¬ Qsag.ClosedWhir.whirInLang Qsag.ClosedWhir.sampledQueryEnv
      Qsag.ClosedWhir.sampledQuerySched
      ⟨[Qsag.Goldilocks.one, Qsag.Goldilocks.one, Qsag.Goldilocks.one, Qsag.Goldilocks.one],
       Qsag.Goldilocks.zero⟩ ∧
    (Qsag.ClosedWhir.whirOracleIop Qsag.ClosedWhir.sampledQueryEnv
      Qsag.ClosedWhir.sampledQuerySched 2).verify
      ⟨[Qsag.Goldilocks.one, Qsag.Goldilocks.one, Qsag.Goldilocks.one, Qsag.Goldilocks.one],
       Qsag.Goldilocks.zero⟩
      [(⟨[], [Qsag.Goldilocks.zero, Qsag.Goldilocks.one], []⟩, 0), (⟨[], [], []⟩, 1)] = true ∧
    Qsag.ClosedWhir.sampledQueryCert.cert.bad
      ⟨1, Nat.lt_of_lt_of_eq (by decide : 1 < 2)
        Qsag.ClosedWhir.sampledQuerySched_shape.2.2.symm⟩ = 2 :=
  ⟨Qsag.ClosedWhir.sampledQuerySched_shape.1,
   Qsag.ClosedWhir.sampledQuerySched_shape.2.1,
   Qsag.ClosedWhir.sampledQuery_honest_accepts.1,
   Qsag.ClosedWhir.sampledQuery_false_not_inLang,
   Qsag.ClosedWhir.sampledQuery_false_statement_accepted_once.1,
   Qsag.ClosedWhir.sampledQueryCert_query_round_bad⟩

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

/-! ### 1b. Succinct Merkle-root-and-opening WHIR QROM soundness & multi-stage `[CWYZ26]` instance -/

section SuccinctWhir
variable {F D : Type} [CommRingOps F] [DecidableEq F] [DecidableEq D]

/-- Acceptance probability of the succinct Merkle-root-and-opening WHIR verifier under Fiat–Shamir
    hashing of `(Option D, WhirPub F)` message prefixes only. -/
def WhirSuccinctSoundnessWinProb {cardX cardAnc Q w : Nat}
    (env : Qsag.ClosedWhir.WhirEnv F) (sched : Qsag.ClosedWhir.WhirVerifierSchedule)
    (M : Qsag.ClosedFs.MerkleSetup D F) (dfltRoot : D)
    (codec : Qsag.ClosedFs.FsCodec
      (Qsag.ClosedFs.SuccinctRoundMsg D (Qsag.ClosedWhir.WhirPub F)) sched.numRounds cardX)
    (aux : Fin cardX → List (F × List D))
    (claim : F) (initRoots : Nat → D)
    (A : Qsag.QuantumAdv cardX w cardAnc Q) : Qsag.RatBound :=
  ⟨Qsag.uniformOracleSum w cardX (fun H =>
      Qsag.QVec.queryMassOn
        (Qsag.ClosedFs.succinctFsAccept (Qsag.ClosedWhir.whirOracleIop env sched w)
          (Qsag.ClosedWhir.whirSuccinctBridge env sched w dfltRoot) M codec aux claim initRoots H)
        (Qsag.runQuantumAdv A H)),
    (2 ^ w) ^ cardX * (Qsag.prefixScale A Q (Nat.le_refl Q) * Qsag.QVec.stateNormSq A.init),
    Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos w))
      (Nat.mul_pos (Qsag.prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩

/-- Probability that the succinct WHIR verifier accepts AND `findCollision` extracts an explicit
    Merkle collision against `tblOf`. -/
def WhirSuccinctMerkleCollisionWinProb {cardX cardAnc Q w : Nat}
    (env : Qsag.ClosedWhir.WhirEnv F) (sched : Qsag.ClosedWhir.WhirVerifierSchedule)
    (M : Qsag.ClosedFs.MerkleSetup D F) (dfltRoot : D)
    (codec : Qsag.ClosedFs.FsCodec
      (Qsag.ClosedFs.SuccinctRoundMsg D (Qsag.ClosedWhir.WhirPub F)) sched.numRounds cardX)
    (aux : Fin cardX → List (F × List D))
    (claim : F) (initRoots : Nat → D) (tblOf : Nat → D → Nat → F)
    (A : Qsag.QuantumAdv cardX w cardAnc Q) : Qsag.RatBound :=
  ⟨Qsag.uniformOracleSum w cardX (fun H =>
      Qsag.QVec.queryMassOn
        (Qsag.ClosedFs.succinctFsCollisionEvent (Qsag.ClosedWhir.whirOracleIop env sched w)
          (Qsag.ClosedWhir.whirSuccinctBridge env sched w dfltRoot)
          M codec aux claim initRoots tblOf H)
        (Qsag.runQuantumAdv A H)),
    (2 ^ w) ^ cardX * (Qsag.prefixScale A Q (Nat.le_refl Q) * Qsag.QVec.stateNormSq A.init),
    Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos w))
      (Nat.mul_pos (Qsag.prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩

/-- **Closed Succinct-Transcript QROM Soundness of Multi-Round WHIR
    (`whir_succinct_closed_qrom_soundness`)**:
    Bounds succinct Merkle-root-and-opening acceptance by `scheduleQromError sched Q` plus the
    explicit `MerkleCollision` extraction probability. -/
theorem whir_succinct_closed_qrom_soundness {cardX cardAnc Q w : Nat}
    (env : Qsag.ClosedWhir.WhirEnv F) (sched : Qsag.ClosedWhir.WhirVerifierSchedule)
    (M : Qsag.ClosedFs.MerkleSetup D F) (dfltRoot : D)
    (sc : Qsag.ClosedWhir.WhirScheduleCert env sched w)
    (codec : Qsag.ClosedFs.FsCodec
      (Qsag.ClosedFs.SuccinctRoundMsg D (Qsag.ClosedWhir.WhirPub F)) sched.numRounds cardX)
    (aux : Fin cardX → List (F × List D))
    (claim : F) (initRoots : Nat → D) (tblOf : Nat → D → Nat → F)
    (hx : ¬ Qsag.ClosedWhir.whirInLang env sched
      ((Qsag.ClosedWhir.whirSuccinctBridge env sched w dfltRoot).liftStmt claim initRoots tblOf))
    (hRoots : ∀ (H : Fin cardX → BitVec w) (o : Fin cardX),
      Qsag.ClosedFs.succinctFsAccept (Qsag.ClosedWhir.whirOracleIop env sched w)
        (Qsag.ClosedWhir.whirSuccinctBridge env sched w dfltRoot)
        M codec aux claim initRoots H o = true →
      let str := Qsag.ClosedFs.fsTranscript codec H (codec.dec o)
      ∀ q ∈ (Qsag.ClosedWhir.whirOracleIop env sched w).queries claim
          (str.map (fun sc' => (sc'.1.pub, sc'.2))),
        M.root q.1 ((Qsag.ClosedWhir.whirOracleIop env sched w).depth q.1)
          (tblOf q.1 ((Qsag.ClosedWhir.whirSuccinctBridge env sched w dfltRoot).rootsOf
            initRoots (str.map Prod.fst) q.1)) =
          (Qsag.ClosedWhir.whirSuccinctBridge env sched w dfltRoot).rootsOf
            initRoots (str.map Prod.fst) q.1)
    (A : Qsag.QuantumAdv cardX w cardAnc Q) :
    Qsag.Spec.GameBound
      (Qsag.Spec.RatBound.ofBudget
        (WhirSuccinctSoundnessWinProb env sched M dfltRoot codec aux claim initRoots A))
      (Qsag.Spec.RatBound.ofBudget
        (Qsag.RatBound.add (Qsag.ClosedWhir.scheduleQromError sched Q)
          (WhirSuccinctMerkleCollisionWinProb env sched M dfltRoot codec aux claim
            initRoots tblOf A))) :=
  (Qsag.Spec.RatBound.ofBudget_le_iff _ _).mpr
    (Qsag.ClosedWhir.whir_succinct_closed_qrom_soundness env sched M dfltRoot sc codec aux
      claim initRoots tblOf hx hRoots A)

end SuccinctWhir

/-- Succinct collision reduction turning `succinctFsCollisionEvent` into `Spec.HashCollision Hb`. -/
def whirSuccinctCollisionReduction {F : Type} [CommRingOps F] [DecidableEq F] {cardX w : Nat}
    (Hb : Qsag.Spec.Bytes → Qsag.Spec.Bytes)
    (nodeC : Qsag.Spec.FramedCodec (Nat × Nat × Qsag.Spec.Bytes × Qsag.Spec.Bytes))
    (leafC : Qsag.Spec.FramedCodec (Nat × Nat × F))
    (env : Qsag.ClosedWhir.WhirEnv F) (sched : Qsag.ClosedWhir.WhirVerifierSchedule)
    (dfltRoot : Qsag.Spec.Bytes)
    (codec : Qsag.ClosedFs.FsCodec
      (Qsag.ClosedFs.SuccinctRoundMsg Qsag.Spec.Bytes (Qsag.ClosedWhir.WhirPub F))
      sched.numRounds cardX)
    (aux : Fin cardX → List (F × List Qsag.Spec.Bytes))
    (claim : F) (initRoots : Nat → Qsag.Spec.Bytes)
    (tblOf : Nat → Qsag.Spec.Bytes → Nat → F)
    (H : Fin cardX → BitVec w) (o : Fin cardX)
    (h : Qsag.ClosedFs.succinctFsCollisionEvent (Qsag.ClosedWhir.whirOracleIop env sched w)
      (Qsag.ClosedWhir.whirSuccinctBridge env sched w dfltRoot)
      (Qsag.ClosedFs.framedSetup Hb nodeC leafC) codec aux claim initRoots tblOf H o = true) :
    Qsag.Spec.HashCollision Hb :=
  Qsag.ClosedFs.succinctFsCollisionReduction Hb nodeC leafC
    (Qsag.ClosedWhir.whirOracleIop env sched w)
    (Qsag.ClosedWhir.whirSuccinctBridge env sched w dfltRoot)
    codec aux claim initRoots tblOf H o h

theorem whirSuccinctCollisionReduction_validBreak {F : Type} [CommRingOps F] [DecidableEq F]
    {cardX w : Nat}
    (Hb : Qsag.Spec.Bytes → Qsag.Spec.Bytes)
    (nodeC : Qsag.Spec.FramedCodec (Nat × Nat × Qsag.Spec.Bytes × Qsag.Spec.Bytes))
    (leafC : Qsag.Spec.FramedCodec (Nat × Nat × F))
    (env : Qsag.ClosedWhir.WhirEnv F) (sched : Qsag.ClosedWhir.WhirVerifierSchedule)
    (dfltRoot : Qsag.Spec.Bytes)
    (codec : Qsag.ClosedFs.FsCodec
      (Qsag.ClosedFs.SuccinctRoundMsg Qsag.Spec.Bytes (Qsag.ClosedWhir.WhirPub F))
      sched.numRounds cardX)
    (aux : Fin cardX → List (F × List Qsag.Spec.Bytes))
    (claim : F) (initRoots : Nat → Qsag.Spec.Bytes)
    (tblOf : Nat → Qsag.Spec.Bytes → Nat → F)
    (H : Fin cardX → BitVec w) (o : Fin cardX)
    (h : Qsag.ClosedFs.succinctFsCollisionEvent (Qsag.ClosedWhir.whirOracleIop env sched w)
      (Qsag.ClosedWhir.whirSuccinctBridge env sched w dfltRoot)
      (Qsag.ClosedFs.framedSetup Hb nodeC leafC) codec aux claim initRoots tblOf H o = true) :
    Qsag.Spec.ValidBreak Hb
      ⟨(whirSuccinctCollisionReduction Hb nodeC leafC env sched dfltRoot codec aux claim
          initRoots tblOf H o h).m₁,
       (whirSuccinctCollisionReduction Hb nodeC leafC env sched dfltRoot codec aux claim
          initRoots tblOf H o h).m₂⟩ :=
  (whirSuccinctCollisionReduction Hb nodeC leafC env sched dfltRoot codec aux claim
    initRoots tblOf H o h).validBreak

/-- **Unconditional Multi-Stage `[CWYZ26]` Sliced-MCA WHIR Closed QROM Soundness
    (`flatHemSlicedWhir_closed_qrom_soundness`)**:
    Discharges `ClosedWhir.WhirScheduleCert` unconditionally via `ClosedWhir.flatHemSlicedCert` on
    the two-stage (`6`-round) schedule `ClosedWhir.flatHemSlicedSched` (`q = 2^62, w = 256`). -/
theorem flatHemSlicedWhir_closed_qrom_soundness {D : Type} [DecidableEq D]
    {cardX cardAnc Q : Nat}
    (M : Qsag.ClosedFs.MerkleSetup D Qsag.QuarticGoldilocks)
    (c : Qsag.ClosedFs.FsCodec (Qsag.ClosedWhir.WhirMsg Qsag.QuarticGoldilocks)
      Qsag.ClosedWhir.flatHemSlicedSched.numRounds cardX)
    (aux : Fin cardX → List (Qsag.QuarticGoldilocks × List D))
    (x : Qsag.ClosedWhir.WhirStmt Qsag.QuarticGoldilocks)
    (hx : ¬ Qsag.ClosedWhir.whirInLang Qsag.ClosedWhir.flatHemSlicedEnv
      Qsag.ClosedWhir.flatHemSlicedSched x)
    (A : Qsag.QuantumAdv cardX 256 cardAnc Q) :
    Qsag.Spec.GameBound
      (Qsag.Spec.RatBound.ofBudget
        (WhirSoundnessWinProb Qsag.ClosedWhir.flatHemSlicedEnv
          Qsag.ClosedWhir.flatHemSlicedSched M c aux x A))
      (Qsag.Spec.RatBound.ofBudget
        (Qsag.RatBound.add
          (Qsag.ClosedWhir.scheduleQromError Qsag.ClosedWhir.flatHemSlicedSched Q)
          (WhirMerkleCollisionWinProb Qsag.ClosedWhir.flatHemSlicedEnv
            Qsag.ClosedWhir.flatHemSlicedSched M c aux x A))) :=
  whir_exec_closed_qrom_soundness Qsag.ClosedWhir.flatHemSlicedEnv
    Qsag.ClosedWhir.flatHemSlicedSched M Qsag.ClosedWhir.flatHemSlicedCert c aux x hx A

/-- **Unconditional Multi-Stage `[CWYZ26]` Succinct-Transcript WHIR Closed QROM Soundness
    (`flatHemSlicedWhir_succinct_closed_qrom_soundness`)**:
    Composes `whir_succinct_closed_qrom_soundness` with `ClosedWhir.flatHemSlicedCert` (`0`
    certificate assumptions, succinct `(Option D, WhirPub)` Fiat–Shamir hashing, explicit
    `MerkleCollision` branch). -/
theorem flatHemSlicedWhir_succinct_closed_qrom_soundness {D : Type} [DecidableEq D]
    {cardX cardAnc Q : Nat}
    (M : Qsag.ClosedFs.MerkleSetup D Qsag.QuarticGoldilocks) (dfltRoot : D)
    (codec : Qsag.ClosedFs.FsCodec
      (Qsag.ClosedFs.SuccinctRoundMsg D (Qsag.ClosedWhir.WhirPub Qsag.QuarticGoldilocks))
      Qsag.ClosedWhir.flatHemSlicedSched.numRounds cardX)
    (aux : Fin cardX → List (Qsag.QuarticGoldilocks × List D))
    (claim : Qsag.QuarticGoldilocks) (initRoots : Nat → D)
    (tblOf : Nat → D → Nat → Qsag.QuarticGoldilocks)
    (hx : ¬ Qsag.ClosedWhir.whirInLang Qsag.ClosedWhir.flatHemSlicedEnv
      Qsag.ClosedWhir.flatHemSlicedSched
      ((Qsag.ClosedWhir.whirSuccinctBridge Qsag.ClosedWhir.flatHemSlicedEnv
        Qsag.ClosedWhir.flatHemSlicedSched 256 dfltRoot).liftStmt claim initRoots tblOf))
    (hRoots : ∀ (H : Fin cardX → BitVec 256) (o : Fin cardX),
      Qsag.ClosedFs.succinctFsAccept
        (Qsag.ClosedWhir.whirOracleIop Qsag.ClosedWhir.flatHemSlicedEnv
          Qsag.ClosedWhir.flatHemSlicedSched 256)
        (Qsag.ClosedWhir.whirSuccinctBridge Qsag.ClosedWhir.flatHemSlicedEnv
          Qsag.ClosedWhir.flatHemSlicedSched 256 dfltRoot)
        M codec aux claim initRoots H o = true →
      let str := Qsag.ClosedFs.fsTranscript codec H (codec.dec o)
      ∀ q ∈ (Qsag.ClosedWhir.whirOracleIop Qsag.ClosedWhir.flatHemSlicedEnv
          Qsag.ClosedWhir.flatHemSlicedSched 256).queries claim
          (str.map (fun sc' => (sc'.1.pub, sc'.2))),
        M.root q.1 ((Qsag.ClosedWhir.whirOracleIop Qsag.ClosedWhir.flatHemSlicedEnv
            Qsag.ClosedWhir.flatHemSlicedSched 256).depth q.1)
          (tblOf q.1 ((Qsag.ClosedWhir.whirSuccinctBridge Qsag.ClosedWhir.flatHemSlicedEnv
            Qsag.ClosedWhir.flatHemSlicedSched 256 dfltRoot).rootsOf
            initRoots (str.map Prod.fst) q.1)) =
          (Qsag.ClosedWhir.whirSuccinctBridge Qsag.ClosedWhir.flatHemSlicedEnv
            Qsag.ClosedWhir.flatHemSlicedSched 256 dfltRoot).rootsOf
            initRoots (str.map Prod.fst) q.1)
    (A : Qsag.QuantumAdv cardX 256 cardAnc Q) :
    Qsag.Spec.GameBound
      (Qsag.Spec.RatBound.ofBudget
        (WhirSuccinctSoundnessWinProb Qsag.ClosedWhir.flatHemSlicedEnv
          Qsag.ClosedWhir.flatHemSlicedSched M dfltRoot codec aux claim initRoots A))
      (Qsag.Spec.RatBound.ofBudget
        (Qsag.RatBound.add
          (Qsag.ClosedWhir.scheduleQromError Qsag.ClosedWhir.flatHemSlicedSched Q)
          (WhirSuccinctMerkleCollisionWinProb Qsag.ClosedWhir.flatHemSlicedEnv
            Qsag.ClosedWhir.flatHemSlicedSched M dfltRoot codec aux claim initRoots tblOf A))) :=
  whir_succinct_closed_qrom_soundness Qsag.ClosedWhir.flatHemSlicedEnv
    Qsag.ClosedWhir.flatHemSlicedSched M dfltRoot Qsag.ClosedWhir.flatHemSlicedCert
    codec aux claim initRoots tblOf hx hRoots A

/-- Non-vacuity witness bundle for the unconditional two-stage `[CWYZ26]` schedule:
    `2` stages (`6` rounds) passing `johnsonOk`, `< 2^-20` error at `Q = 0` and `< 1` at `Q = 256`,
    accepted honest two-stage proof, false statement outside `whirInLang`, positive certified
    fold-round flip count, and an explicit challenge where the false statement is accepted. -/
theorem flatHemSlicedWhir_nonvacuity :
    Qsag.ClosedWhir.flatHemSlicedSched.stages.length = 2 ∧
    Qsag.ClosedWhir.flatHemSlicedSched.johnsonOk = true ∧
    Qsag.atLeastBits 20
      (Qsag.ClosedWhir.scheduleQromError Qsag.ClosedWhir.flatHemSlicedSched 0) ∧
    Qsag.RatBound.lt
      (Qsag.ClosedWhir.scheduleQromError Qsag.ClosedWhir.flatHemSlicedSched 256)
      Qsag.RatBound.one ∧
    ¬ Qsag.ClosedWhir.whirInLang Qsag.ClosedWhir.flatHemSlicedEnv
      Qsag.ClosedWhir.flatHemSlicedSched
      ⟨List.replicate 64 (Qsag.hemFoldQg 1), Qsag.hemFoldQg 2⟩ ∧
    (Qsag.ClosedWhir.whirOracleIop Qsag.ClosedWhir.flatHemSlicedEnv
      Qsag.ClosedWhir.flatHemSlicedSched 256).verify
      ⟨List.replicate 64 (Qsag.hemFoldQg 1), Qsag.hemFoldQg 1⟩
      [(⟨[], [Qsag.hemFoldQg 1, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero,
              CommRingOps.zero], []⟩, Qsag.ClosedWhir.flatHemQ),
       (⟨List.replicate 32 (Qsag.hemFoldQg 1), [], []⟩, 0),
       (⟨[], [], [Qsag.hemFoldQg 1, Qsag.hemFoldQg 1]⟩, 1),
       (⟨[], [Qsag.hemFoldQg 39, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero,
              CommRingOps.zero], []⟩, Qsag.ClosedWhir.flatHemQ),
       (⟨[], [Qsag.hemFoldQg 1], []⟩, 0),
       (⟨[], [], [Qsag.hemFoldQg 1, Qsag.hemFoldQg 1]⟩, 0)] = true ∧
    (Qsag.ClosedWhir.whirOracleIop Qsag.ClosedWhir.flatHemSlicedEnv
      Qsag.ClosedWhir.flatHemSlicedSched 256).verify
      ⟨List.replicate 64 (Qsag.hemFoldQg 1), Qsag.hemFoldQg 2⟩
      [(⟨[], [], []⟩, 0), (⟨[], [], []⟩, 0),
       (⟨[], [], [CommRingOps.zero, CommRingOps.zero]⟩, 0),
       (⟨[], [], []⟩, 0), (⟨[], [], []⟩, 0),
       (⟨[], [], [CommRingOps.zero, CommRingOps.zero]⟩, 0)] = true ∧
    0 < Qsag.ClosedWhir.flatHemSlicedCert.cert.bad
      ⟨0, Nat.lt_of_lt_of_eq (by decide : 0 < 6)
        Qsag.ClosedWhir.flatHemSlicedSched_shape.2.2.symm⟩ :=
  ⟨Qsag.ClosedWhir.flatHemSlicedSched_shape.1,
   Qsag.ClosedWhir.flatHemSlicedSched_shape.2.1,
   Qsag.ClosedWhir.flatHemSlicedSched_error_bits.1,
   Qsag.ClosedWhir.flatHemSlicedSched_error_bits.2,
   Qsag.ClosedWhir.flatHemSliced_false_not_inLang,
   Qsag.ClosedWhir.flatHemSliced_honest_accepts,
   Qsag.ClosedWhir.flatHemSliced_false_accepted_once.1,
   Qsag.ClosedWhir.flatHemSlicedCert_fold0_bad_pos⟩

/-! ### 1c. `zk-Hem v2`: `QuinticGoldilocks`, width-400 challenges, 9-product Toom-3 -/

/-- **Nine-product Toom-3 multiplication in `𝔽_{p^5} = 𝔽_p[u] / (u^5 - 3)` equals the schoolbook
    product (`toom3_fp5_nine_triple_mul_eq`).** `Qsag.toom3MulFp5` evaluates both operands at
    `{0, ±1, ±2, ±3, 4, ∞}`, multiplies pointwise (nine base-field products), interpolates and
    reduces; the result is `QuinticGoldilocks.mul` for all inputs. A ring identity: it says
    nothing about the secret-shared execution of those nine products. -/
theorem toom3_fp5_nine_triple_mul_eq (x y : Qsag.QuinticGoldilocks) :
    Qsag.toom3MulFp5 x y = Qsag.QuinticGoldilocks.mul x y :=
  Qsag.toom3MulFp5_eq_quinticMul x y

/-- **`whir_exec_closed_qrom_soundness` with its certificate discharged over `QuinticGoldilocks`
    at challenge width `400` (`zkHemV2QuinticWhir_closed_qrom_soundness`).** The certificate is
    `ZkHemV2Cert.zkHemV2QuinticCert` for `ZkHemV2Cert.zkHemV2QuinticSched`: one stage with no fold
    round on a 64-point coset (rate `2^-6`, degree bound `1`), `5` out-of-domain points and `66`
    queries. It is not one of the deployed table sizes of `ZkHemV2Cert.zkHemV2ProdSched`; it shows
    the certificate hypothesis is satisfiable over the degree-5 field at width `400`. -/
theorem zkHemV2QuinticWhir_closed_qrom_soundness {D : Type} [DecidableEq D]
    {cardX cardAnc Q : Nat}
    (M : Qsag.ClosedFs.MerkleSetup D Qsag.QuinticGoldilocks)
    (c : Qsag.ClosedFs.FsCodec (Qsag.ClosedWhir.WhirMsg Qsag.QuinticGoldilocks)
      Qsag.ZkHemV2Cert.zkHemV2QuinticSched.numRounds cardX)
    (aux : Fin cardX → List (Qsag.QuinticGoldilocks × List D))
    (x : Qsag.ClosedWhir.WhirStmt Qsag.QuinticGoldilocks)
    (hx : ¬ Qsag.ClosedWhir.whirInLang Qsag.ZkHemV2Cert.zkHemV2QuinticEnv
      Qsag.ZkHemV2Cert.zkHemV2QuinticSched x)
    (A : Qsag.QuantumAdv cardX 400 cardAnc Q) :
    Qsag.Spec.GameBound
      (Qsag.Spec.RatBound.ofBudget
        (WhirSoundnessWinProb Qsag.ZkHemV2Cert.zkHemV2QuinticEnv
          Qsag.ZkHemV2Cert.zkHemV2QuinticSched M c aux x A))
      (Qsag.Spec.RatBound.ofBudget
        (Qsag.RatBound.add
          (Qsag.ClosedWhir.scheduleQromError Qsag.ZkHemV2Cert.zkHemV2QuinticSched Q)
          (WhirMerkleCollisionWinProb Qsag.ZkHemV2Cert.zkHemV2QuinticEnv
            Qsag.ZkHemV2Cert.zkHemV2QuinticSched M c aux x A))) :=
  whir_exec_closed_qrom_soundness Qsag.ZkHemV2Cert.zkHemV2QuinticEnv
    Qsag.ZkHemV2Cert.zkHemV2QuinticSched M Qsag.ZkHemV2Cert.zkHemV2QuinticCert c aux x hx A

/-- **Conditional on `WhirScheduleCert` for `zkHemV2ProdSched logCells` and on the Merkle
    collision bound: succinct Fiat–Shamir acceptance below `2^-128`
    (`zkHemV2_deployed_succinct_qrom_gameBound_128`).** For `16 ≤ logCells ≤ 28` and `Q ≤ 2^64`,
    a statement outside the language is accepted with probability strictly below `2^-128`, hence
    `Spec.GameBound` against `2^-128`. Hypotheses, none discharged here:
    * `sc`: a `ClosedWhir.WhirScheduleCert` for `ZkHemV2Cert.zkHemV2ProdSched logCells` at width
      `400`. None is constructed for a deployed table size; the `mcaNum` entries of
      `zkHemV2ProdStages` are numeric inputs (Stage 0 is pinned to the `[DKT26]` Theorem 5.12
      count by `ZkHemV2Cert.zkHemV2ProdStages_dkt26_exact`).
    * `hMerkle`: the collision-event probability is at most `ZkHemV2Cert.merkle400QromBound Q`
      (`6680 · Q^3 / 2^400`).
    * `hRoots`: the Merkle-root consistency premise of `whir_succinct_closed_qrom_soundness`.
    What is proved with no hypothesis is the arithmetic
    `scheduleQromError (zkHemV2ProdSched logCells) Q + 6680 · Q^3 / 2^400 < 2^-128`
    (`ZkHemV2Cert.zkHemV2_prod_qrom_error_lt_128_at_2pow64`). -/
theorem zkHemV2_deployed_succinct_qrom_gameBound_128 {D : Type} [DecidableEq D]
    {cardX cardAnc Q : Nat} (logCells : Nat)
    (hLo : 16 ≤ logCells) (hHi : logCells ≤ 28) (hQ : Q ≤ 2 ^ 64)
    (env : Qsag.ClosedWhir.WhirEnv Qsag.QuinticGoldilocks)
    (M : Qsag.ClosedFs.MerkleSetup D Qsag.QuinticGoldilocks) (dfltRoot : D)
    (sc : Qsag.ClosedWhir.WhirScheduleCert env (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells) 400)
    (codec : Qsag.ClosedFs.FsCodec
      (Qsag.ClosedFs.SuccinctRoundMsg D (Qsag.ClosedWhir.WhirPub Qsag.QuinticGoldilocks))
      (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells).numRounds cardX)
    (aux : Fin cardX → List (Qsag.QuinticGoldilocks × List D))
    (claim : Qsag.QuinticGoldilocks) (initRoots : Nat → D)
    (tblOf : Nat → D → Nat → Qsag.QuinticGoldilocks)
    (hx : ¬ Qsag.ClosedWhir.whirInLang env (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells)
      ((Qsag.ClosedWhir.whirSuccinctBridge env (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells)
        400 dfltRoot).liftStmt claim initRoots tblOf))
    (hRoots : ∀ (H : Fin cardX → BitVec 400) (o : Fin cardX),
      Qsag.ClosedFs.succinctFsAccept
        (Qsag.ClosedWhir.whirOracleIop env (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells) 400)
        (Qsag.ClosedWhir.whirSuccinctBridge env (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells)
          400 dfltRoot)
        M codec aux claim initRoots H o = true →
      let str := Qsag.ClosedFs.fsTranscript codec H (codec.dec o)
      ∀ q ∈ (Qsag.ClosedWhir.whirOracleIop env
          (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells) 400).queries claim
          (str.map (fun sc' => (sc'.1.pub, sc'.2))),
        M.root q.1 ((Qsag.ClosedWhir.whirOracleIop env
            (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells) 400).depth q.1)
          (tblOf q.1 ((Qsag.ClosedWhir.whirSuccinctBridge env
            (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells) 400 dfltRoot).rootsOf
            initRoots (str.map Prod.fst) q.1)) =
          (Qsag.ClosedWhir.whirSuccinctBridge env
            (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells) 400 dfltRoot).rootsOf
            initRoots (str.map Prod.fst) q.1)
    (A : Qsag.QuantumAdv cardX 400 cardAnc Q)
    (hMerkle : Qsag.RatBound.le
      (WhirSuccinctMerkleCollisionWinProb env (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells)
        M dfltRoot codec aux claim initRoots tblOf A)
      (Qsag.ZkHemV2Cert.merkle400QromBound Q)) :
    Qsag.RatBound.lt
      (WhirSuccinctSoundnessWinProb env (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells)
        M dfltRoot codec aux claim initRoots A)
      (Qsag.RatBound.invPow2 128) ∧
    Qsag.Spec.GameBound
      (Qsag.Spec.RatBound.ofBudget
        (WhirSuccinctSoundnessWinProb env (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells)
          M dfltRoot codec aux claim initRoots A))
      (Qsag.Spec.RatBound.ofBudget (Qsag.RatBound.invPow2 128)) := by
  have hLt := Qsag.ZkHemV2Cert.zkHemV2_deployed_succinct_qrom_soundness_128
    logCells hLo hHi hQ env M dfltRoot sc codec aux claim initRoots tblOf hx hRoots A hMerkle
  exact ⟨hLt, (Qsag.Spec.RatBound.ofBudget_le_iff _ _).mpr (Nat.le_of_lt hLt)⟩

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

/-- **Closed EUF-CMA PRF Key-Derivation Hop (`jorts_baggy_closed_euf_cma_prf_keygen_hop`)**:
    Replaces PRF-derived secret keys `(prf k [0], prf k [1], prf k [2])` with uniform oracle keys
    under `Spec.PrfHard` via the explicit `Within 3` distinguisher `execKeygenDistinguisher`. -/
theorem jorts_baggy_closed_euf_cma_prf_keygen_hop {n nC nA qHash qSign : Nat} (hPos : 0 < n)
    (suite : Qsag.TweakableHashSuite) (params : Qsag.PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16)
    (adv : Fin nA → Qsag.SeedWithheldEufCmaAdv qHash qSign)
    (prf : Qsag.Spec.Bytes → Qsag.Spec.Bytes → Qsag.Spec.Bytes)
    (keyLen inLen outLen qPrf : Nat) (hqPrf : 3 ≤ qPrf)
    {𝒜 : Qsag.Spec.Code Qsag.Spec.byteOracleIface Bool → Prop}
    {εPrf : Qsag.Spec.RatBound} (hPrf : Qsag.Spec.PrfHard 𝒜 prf keyLen inLen outLen qPrf εPrf)
    (π : Qsag.Spec.CoinSplit n nC nA)
    (sample : Fin nC → Qsag.Spec.Bytes × (Qsag.Spec.Bytes → Qsag.Spec.Bytes))
    (hU : Qsag.Spec.UniformOn (Qsag.Spec.PrfSampleOk keyLen inLen outLen) sample)
    (hD : ∀ a : Fin nA, 𝒜 (Qsag.execKeygenDistinguisher suite params (adv a))) :
    let keygenReal : Fin n → Qsag.PqSecretKey :=
      fun ω => Qsag.keygenFromByteOracle (prf (sample (π.chal ω)).1)
    let keygenIdeal : Fin n → Qsag.PqSecretKey :=
      fun ω => Qsag.keygenFromByteOracle (sample (π.chal ω)).2
    let advCoin : Fin n → Qsag.SeedWithheldEufCmaAdv qHash qSign := fun ω => adv (π.advc ω)
    Qsag.Spec.GameBound (Qsag.ExecEufCmaGame hPos suite params keygenReal advCoin).winProb
      (((Qsag.execEufCmaItsrReduction hPos suite params hw keygenIdeal advCoin).winProb.add
        ((Qsag.execEufCmaTcrReduction hPos suite params hw keygenIdeal advCoin).winProb.add
          (Qsag.execEufCmaPreReduction hPos suite params hw keygenIdeal advCoin).winProb)).add εPrf) :=
  _root_.Qsag.jorts_baggy_closed_euf_cma_keygen_hop_concrete hPos suite params hw adv prf
    keyLen inLen outLen qPrf hhqPrf hPrf π sample hU hD
where
  hhqPrf := hqPrf

/-- **Closed EUF-CMA Bound via Canonical `Spec.Assumptions` Locales
    (`jorts_baggy_closed_euf_cma_spec_assumptions_bound`)**:
    Composes any `ExecEufCmaReductionEmbedding` directly with `Spec.ItsrHard`, `Spec.SmDtTcrHard`,
    and `Spec.SmDtPreHard` (`Spec.hashSig_forger_bound`). -/
theorem jorts_baggy_closed_euf_cma_spec_assumptions_bound {n qHash qSign : Nat} {hPos : 0 < n}
    {suite : Qsag.TweakableHashSuite} {params : Qsag.PqHashParams}
    {keygen : Fin n → Qsag.PqSecretKey}
    {adv : Fin n → Qsag.SeedWithheldEufCmaAdv qHash qSign}
    (E : Qsag.ExecEufCmaReductionEmbedding hPos suite params keygen adv)
    {εItsr εTcr εPre : Qsag.Spec.RatBound}
    (hItsr : Qsag.Spec.ItsrHard E.𝒜I E.hmsg E.randLen E.qItsr εItsr)
    (hTcr : Qsag.Spec.SmDtTcrHard E.𝒜T E.th E.seedLen E.qTcr εTcr)
    (hPre : Qsag.Spec.SmDtPreHard E.𝒜P E.th E.seedLen E.inputLen E.qPre εPre) :
    Qsag.Spec.GameBound (Qsag.ExecEufCmaGame hPos suite params keygen adv).winProb
      ((εItsr.add εTcr).add εPre) :=
  E.forger_bound hItsr hTcr hPre

/-- **Unconditional Non-Vacuous `< 1` Forger Bound Witness
    (`concrete_exec_euf_cma_spec_assumptions_witness`)**:
    Discharges `ItsrHard`, `SmDtTcrHard`, and `SmDtPreHard` via `byteIdxHmsg_itsrHard_within`,
    `poly257Hash_smDtTcrHard_within`, and `poly257Hash_smDtPreHard_within` (`6 / 256 < 1`, while
    coin `0` wins `ExecEufCmaGame`). -/
theorem concrete_exec_euf_cma_spec_assumptions_witness :
    (Qsag.ExecEufCmaGame (by decide : 0 < 256 * 256) Qsag.seedZeroRootSuite
      Qsag.prodToyStatefulParams Qsag.seedPairKeygen
      (fun _ => Qsag.seedWithheldZeroGuessAdv)).win ⟨0, by decide⟩ = true ∧
    Qsag.Spec.GameBound
      (Qsag.ExecEufCmaGame (by decide : 0 < 256 * 256) Qsag.seedZeroRootSuite
        Qsag.prodToyStatefulParams Qsag.seedPairKeygen
        (fun _ => Qsag.seedWithheldZeroGuessAdv)).winProb
      (((⟨2, 256, by decide⟩ : Qsag.Spec.RatBound).add ⟨2, 256, by decide⟩).add
        ⟨2, 256, by decide⟩) ∧
    (((⟨2, 256, by decide⟩ : Qsag.Spec.RatBound).add ⟨2, 256, by decide⟩).add
      ⟨2, 256, by decide⟩).lt Qsag.Spec.RatBound.one :=
  Qsag.concreteExecEufCma_forger_bound

#verify_constructive
  Qsag.Top.whir_exec_closed_qrom_soundness
  Qsag.Top.deployed_whir_exec_closed_qrom_128
  Qsag.Top.sampledQueryWhir_closed_qrom_soundness
  Qsag.Top.sampledQueryWhir_nonvacuity
  Qsag.Top.whirCollisionReduction_validBreak
  Qsag.Top.whir_succinct_closed_qrom_soundness
  Qsag.Top.whirSuccinctCollisionReduction_validBreak
  Qsag.Top.flatHemSlicedWhir_closed_qrom_soundness
  Qsag.Top.flatHemSlicedWhir_succinct_closed_qrom_soundness
  Qsag.Top.flatHemSlicedWhir_nonvacuity
  Qsag.Top.toom3_fp5_nine_triple_mul_eq
  Qsag.Top.zkHemV2QuinticWhir_closed_qrom_soundness
  Qsag.Top.zkHemV2_deployed_succinct_qrom_gameBound_128
  Qsag.Top.jorts_baggy_closed_euf_cma_same_trace_classification
  Qsag.Top.jorts_baggy_closed_euf_cma_keyed_target_bound
  Qsag.Top.jorts_baggy_closed_euf_cma_prf_keygen_hop
  Qsag.Top.jorts_baggy_closed_euf_cma_spec_assumptions_bound
  Qsag.Top.concrete_exec_euf_cma_spec_assumptions_witness

#tooth_pair Qsag.Top.toom3_fp5_nine_triple_mul_eq vs
  Qsag.tooth_toom3_wrong_reduction_ne_quinticMul
#tooth_pair Qsag.Top.zkHemV2_deployed_succinct_qrom_gameBound_128 vs
  Qsag.ZkHemV2Cert.tooth_v1_256bit_digest_violates_qrom_128_at_2pow64

end Qsag.Top
end

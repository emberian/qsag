module
/- Authenticated extraction over a recorded oracle transcript.
The verifier configuration supplies the public leaf and step matrix coefficients.
The finite-game reduction and the schedule arithmetic are separate results. -/
public import Qsag.Protocol.Aggregation.ConcreteIvcArgumentProver
import Qsag.Tactic.AssuranceKit

public section
attribute [-instance] Fin.instLinearOrderPackage
namespace Qsag.MultiDepthQrom
open Qsag Qsag.ClosedFs Qsag.ClosedWhir Qsag.ZkHemV2Cert Qsag.ZkHemV2Packed Qsag.SuccinctWhirAgg
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 100000

structure IvcExtractionContext (_committeeSize : Nat) where
  profile : AggSigProfile
  cfg : ConcreteIvcConfig

/-- Recover the R1CS node witness from authenticated stage-zero codeword reads.
    Check exactly the public prefix and arithmetic rows used by the prover.
    The prefix includes the statement, accumulator and application commitment. -/
private def recoverIvcCells {n : Nat} (env : IvcExtractionContext n) (ro : IvcAlgebra.RO)
    (log : QromQueryTranscript) (stmt : IvcTreeStatement)
    (pi : FixedShapeWhirProof env.cfg.params) : Option (Array Goldilocks) := do
  let cs ← IvcAlgebra.recoverNodeCoefficients pi (log.filter fun (x,y) => ro x == y)
  let k := env.cfg.params.logCells
  let arg ← IvcAlgebra.parseArgument k pi.algebraWords
  let digest := ro (encodeMultiFrame [[73,86,67,45,77,65,84,82,73,88,45,80,79,73,78,84],arg.acc.encode])
  guard (digest.length = 56)
  let inputs ← IvcAlgebra.fixedPublicCells env.cfg (IvcAlgebra.argumentPublicFrame stmt digest pi.witnessCommitRoot)
  let z := (Array.range (2^k)).map (WhirAssignmentRecovery.vertex cs)
  guard (z.toList.take (1 + inputs.length) = Goldilocks.one :: inputs)
  return z

def recoverIvcAssignment {n : Nat} (env : IvcExtractionContext n) (ro : IvcAlgebra.RO)
    (log : QromQueryTranscript) (d : Nat) (stmt : IvcTreeStatement)
    (pi : FixedShapeWhirProof env.cfg.params) : Option (Array Goldilocks) :=
  (recoverIvcCells env ro log stmt pi).filter fun z =>
    (IvcAlgebra.checkedRowTables env.cfg d (z.map QuinticGoldilocks.ofBase)).isSome

theorem recovered_assignment_satisfies_rows {n : Nat} (env : IvcExtractionContext n)
    (ro : IvcAlgebra.RO) (log : QromQueryTranscript) (d : Nat) (stmt : IvcTreeStatement)
    (pi : FixedShapeWhirProof env.cfg.params) (z : Array Goldilocks)
    (success : recoverIvcAssignment env ro log d stmt pi = some z) :
    (IvcAlgebra.checkedRowTables env.cfg d (z.map QuinticGoldilocks.ofBase)).isSome = true := by
  exact (Option.filter_eq_some_iff.mp success).2

#verify_constructive recovered_assignment_satisfies_rows

/-- Every active validator in an extracted leaf shard has a valid native signature (`XMSS` or `Corduroy`),
    `0 < quorumCount`, and `threshold ≤ Composed.weight stmt.bitmap`. -/
@[expose] def ValidQuorumSignatures {nVal : Nat} (profile : AggSigProfile)
    (ro : Spec.Bytes → Spec.Bytes) (regRoot : Spec.Bytes) (msg : Spec.Bytes) (shard : ExtractedLeafShard nVal) : Prop :=
  0 < shard.quorumCount ∧
  shard.threshold ≤ Composed.weight shard.stmt.bitmap ∧
  shard.stmt.message = msg ∧
  (List.finRange nVal).all (fun i =>
    !shard.stmt.bitmap.getLsbD i.val || ((shard.stmt.roster i).profile == profile)) = true ∧
  stepOp256TableOk profile (succinctCommitteeSlots shard.stmt) shard.rows = true ∧
  Spec.ValidAggregateWitness (verifyAggNativeSig (profileGeom profile)) shard.stmt
    (fun i => some (extractSlotNativeSig profile shard.rows i.val)) ∧
  registryMember ro regRoot shard = true

private def leafNodeCheck {nVal : Nat} (profile : AggSigProfile)
    (ro : Spec.Bytes → Spec.Bytes) (stmt : IvcTreeStatement) (shard : ExtractedLeafShard nVal) : Bool :=
  decide (shard.shardId = stmt.lo ∧ stmt.hi = stmt.lo + 1 ∧
    shard.quorumCount = stmt.totalQuorums ∧ 0 < shard.quorumCount ∧
    shard.threshold ≤ Composed.weight shard.stmt.bitmap ∧
    shard.stmt.message = stmt.message ∧ registryMember ro stmt.policyRegistryRoot shard = true ∧
    0 < shard.threshold ∧ shard.quorumCount = Composed.weight shard.stmt.bitmap) &&
  (List.finRange nVal).all (fun i =>
    !shard.stmt.bitmap.getLsbD i.val || ((shard.stmt.roster i).profile == profile)) &&
  stepOp256TableOk profile (succinctCommitteeSlots shard.stmt) shard.rows

@[expose] def checkChildHeaders (d : Nat) (stmt stmtL stmtR : IvcTreeStatement) : Bool :=
  decide (stmtL.policyRegistryRoot = stmt.policyRegistryRoot ∧
    stmtR.policyRegistryRoot = stmt.policyRegistryRoot ∧
    stmtL.epochFloor = stmt.epochFloor ∧ stmtR.epochFloor = stmt.epochFloor ∧
    stmtL.message = stmt.message ∧ stmtR.message = stmt.message ∧
    stmtL.lo = stmt.lo ∧ stmtL.hi = stmt.lo + 2 ^ d ∧
    stmtL.hi = stmtR.lo ∧ stmtR.hi = stmt.hi ∧
    stmt.totalQuorums = stmtL.totalQuorums + stmtR.totalQuorums)

@[expose] def parentStitchCheck {nVal : Nat}
    (env : IvcExtractionContext nVal) (H : Spec.Bytes → Spec.Bytes) (d : Nat)
    (stmt stmtL stmtR : IvcTreeStatement)
    (piL piR parent : FixedShapeWhirProof env.cfg.params) (fold : List Goldilocks) : Bool :=
  checkChildHeaders d stmt stmtL stmtR &&
  verifyConcreteIvcRoot env.profile env.cfg H d stmtL piL &&
  verifyConcreteIvcRoot env.profile env.cfg H d stmtR piR &&
  IvcAlgebra.parentFoldAgrees env.profile env.cfg H d stmtL stmtR piL piR parent fold

/-- **Arbitrary-Depth `d` Straight-Line QROM Multi-Level Knowledge Extractor (`extractMultiDepthQrom`):**
    Inspects the adversary's **single** recorded QROM transcript `T` (`T.length ≤ Q`) across all
    `d` recursion levels **without rewinding**! -/
def extractMultiDepthQrom {nVal : Nat}
    (env : IvcExtractionContext nVal) (H : Spec.Bytes → Spec.Bytes) :
    (d : Nat) → QromQueryTranscript → IvcTreeStatement → FixedShapeWhirProof env.cfg.params →
      Option (List (ExtractedLeafShard nVal))
  | 0, T, stmt, pi =>
    if verifyConcreteIvcRoot env.profile env.cfg H 0 stmt pi then
      match extractIvcStepFromTranscript nVal env.profile H T 0 stmt pi with
      | some (.leaf shard) =>
        if leafNodeCheck env.profile H stmt shard then some [shard] else none
      | _ => none
    else none
  | d + 1, T, stmt, pi =>
    if verifyConcreteIvcRoot env.profile env.cfg H (d + 1) stmt pi then
      match extractIvcStepFromTranscript nVal env.profile H T (d + 1) stmt pi with
      | some (.parent stmtL stmtR piL piR fold) =>
        if parentStitchCheck env H d stmt stmtL stmtR piL piR pi fold then
          match extractMultiDepthQrom env H d T stmtL piL,
                extractMultiDepthQrom env H d T stmtR piR with
          | some leftShards, some rightShards => some (leftShards ++ rightShards)
          | _, _ => none
        else none
      | _ => none
    else none

/-! ## §4. Inductive Soundness Over Arbitrary Depth `d : Nat` (`ZERO` `2^d` Rewinding Blowup!) -/

/-- Per-node step extraction soundness failure on the single QROM transcript `T`. -/
def concreteIvcStepBad {nVal : Nat}
    (env : IvcExtractionContext nVal) (H : Spec.Bytes → Spec.Bytes)
    (T : QromQueryTranscript) : Nat → IvcTreeStatement → FixedShapeWhirProof env.cfg.params → Bool
  | 0, stmt, pi =>
    verifyConcreteIvcRoot env.profile env.cfg H 0 stmt pi && !hasQueryCollision T &&
    match extractIvcStepFromTranscript nVal env.profile H T 0 stmt pi with
    | some (.leaf shard) => !leafNodeCheck env.profile H stmt shard
    | _ => true
  | d + 1, stmt, pi =>
    verifyConcreteIvcRoot env.profile env.cfg H (d + 1) stmt pi && !hasQueryCollision T &&
    match extractIvcStepFromTranscript nVal env.profile H T (d + 1) stmt pi with
    | some (.parent stmtL stmtR piL piR fold) => !parentStitchCheck env H d stmt stmtL stmtR piL piR pi fold
    | _ => true

/-- Total nodes `2^{d+1} - 1` in a depth-`d` binary recursion tree (`0` = root, `2^d` leaves). -/
@[expose] def treeNodeCount (d : Nat) : Nat := 2 ^ (d + 1) - 1

theorem treeNodeCount_zero : treeNodeCount 0 = 1 := rfl

theorem treeNodeCount_succ (d : Nat) :
    treeNodeCount (d + 1) = 1 + treeNodeCount d + treeNodeCount d := by
  unfold treeNodeCount
  have hPos : 1 ≤ 2 ^ (d + 1) := Nat.one_le_two_pow
  have hPow : 2 ^ (d + 1 + 1) = 2 ^ (d + 1) + 2 ^ (d + 1) := by
    rw [Nat.pow_succ, Nat.mul_two]
  omega

/-- Preorder lookup starting from this root. Descents use only recovered child commitments. -/
def treeNodeAt {n : Nat} (env : IvcExtractionContext n) (H : Spec.Bytes → Spec.Bytes)
    (T : QromQueryTranscript) : Nat → IvcTreeStatement → FixedShapeWhirProof env.cfg.params → Nat →
      Option (Nat × IvcTreeStatement × FixedShapeWhirProof env.cfg.params)
  | d, s, p, 0 => some (d,s,p)
  | 0, _, _, _ + 1 => none
  | d + 1, s, p, i + 1 => do
    let .parent l r pl pr _ ← extractIvcStepFromTranscript n env.profile H T (d+1) s p | none
    if i < treeNodeCount d then treeNodeAt env H T d l pl i
    else treeNodeAt env H T d r pr (i - treeNodeCount d)

/-- Deterministic inductive tree soundness theorem (`extractMultiDepthQrom_inductive_sound`):
    For EVERY depth `d : Nat`, if `verifyConcreteIvcRoot env.profile env.cfg H d stmt pi = true` and `T` has
    `hasQueryCollision T = false`, then EITHER `extractMultiDepthQrom env H d T stmt pi = some shards`
    returns valid native quorum signatures for **ALL `2^d` leaf shards** (`shards.length = 2^d`,
    exact shard IDs `List.range' stmt.lo (2^d)`, conserved `stmt.totalQuorums`), OR an explicit
    internal/leaf node `(lvl, sNode, piNode)` at one of the `2^{d+1} - 1` tree positions triggers
    `concreteIvcStepBad env H T lvl sNode piNode = true`! -/
theorem extractMultiDepthQrom_inductive_sound {nVal : Nat}
    (env : IvcExtractionContext nVal) (hDep : IsDeployedAggProfile env.profile)
    (H : Spec.Bytes → Spec.Bytes) (T : QromQueryTranscript)
    (hNoColl : hasQueryCollision T = false) :
    ∀ (d : Nat) (stmt : IvcTreeStatement) (pi : FixedShapeWhirProof env.cfg.params),
      verifyConcreteIvcRoot env.profile env.cfg H d stmt pi = true →
      (∃ shards : List (ExtractedLeafShard nVal),
        extractMultiDepthQrom env H d T stmt pi = some shards ∧
        shards.length = 2 ^ d ∧
        shards.map ExtractedLeafShard.shardId = List.range' stmt.lo (2 ^ d) ∧
        (shards.map ExtractedLeafShard.quorumCount).sum = stmt.totalQuorums ∧
        ∀ shard ∈ shards, ValidQuorumSignatures env.profile H stmt.policyRegistryRoot stmt.message shard) ∨
      (∃ (nodeIdx : Nat) (lvl : Nat) (sNode : IvcTreeStatement) (piNode : FixedShapeWhirProof env.cfg.params),
        nodeIdx < treeNodeCount d ∧ lvl ≤ d ∧
        treeNodeAt env H T d stmt pi nodeIdx = some (lvl,sNode,piNode) ∧
        concreteIvcStepBad env H T lvl sNode piNode = true)
  | 0, stmt, pi, hVer => by
    unfold extractMultiDepthQrom; rw [hVer]
    cases hLook : extractIvcStepFromTranscript nVal env.profile H T 0 stmt pi with
    | none =>
      exact .inr ⟨0, 0, stmt, pi, by decide, Nat.le_refl 0, by rw [treeNodeAt],
        by unfold concreteIvcStepBad; dsimp only; rw [hVer, hNoColl, hLook]; rfl⟩
    | some w =>
      cases w with
      | parent _ _ _ _ _ =>
        exact .inr ⟨0, 0, stmt, pi, by decide, Nat.le_refl 0, by rw [treeNodeAt],
          by unfold concreteIvcStepBad; dsimp only; rw [hVer, hNoColl, hLook]; rfl⟩
      | leaf shard =>
        cases hOk : leafNodeCheck env.profile H stmt shard with
        | false =>
          exact .inr ⟨0, 0, stmt, pi, by decide, Nat.le_refl 0, by rw [treeNodeAt],
            by unfold concreteIvcStepBad; dsimp only; rw [hVer, hNoColl, hLook]; dsimp only; rw [hOk]; rfl⟩
        | true =>
          left; dsimp only; rw [hOk]
          have hUnf := hOk; unfold leafNodeCheck at hUnf
          rw [Bool.and_eq_true, Bool.and_eq_true] at hUnf
          obtain ⟨⟨hDec, hProfAll⟩, hTable⟩ := hUnf
          obtain ⟨hId, _, hQEq, hQPos, hQWt, hMsg, hRegistry, _, _⟩ := of_decide_eq_true hDec
          refine ⟨[shard], rfl, rfl,
            by simp only [List.map_cons, List.map_nil, hId, Nat.pow_zero]; rfl,
            by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, hQEq],
            fun s hs => ?_⟩
          rcases List.mem_singleton.mp hs with rfl
          exact ⟨hQPos, hQWt, hMsg, hProfAll, hTable,
            stepOp256TableOk_bothProfiles_extract env.profile hDep s.stmt s.rows hProfAll hTable, hRegistry⟩
  | d + 1, stmt, pi, hVer => by
    unfold extractMultiDepthQrom; rw [hVer]
    cases hLook : extractIvcStepFromTranscript nVal env.profile H T (d + 1) stmt pi with
    | none =>
      exact .inr ⟨0, d + 1, stmt, pi, by rw [treeNodeCount_succ]; omega, Nat.le_refl _, by rw [treeNodeAt],
        by unfold concreteIvcStepBad; dsimp only; rw [hVer, hNoColl, hLook]; rfl⟩
    | some w =>
      cases w with
      | leaf _ =>
        exact .inr ⟨0, d + 1, stmt, pi, by rw [treeNodeCount_succ]; omega, Nat.le_refl _, by rw [treeNodeAt],
          by unfold concreteIvcStepBad; dsimp only; rw [hVer, hNoColl, hLook]; rfl⟩
      | parent stmtL stmtR piL piR fold =>
        cases hStitch : parentStitchCheck env H d stmt stmtL stmtR piL piR pi fold with
        | false =>
          exact .inr ⟨0, d + 1, stmt, pi, by rw [treeNodeCount_succ]; omega, Nat.le_refl _, by rw [treeNodeAt],
            by unfold concreteIvcStepBad; dsimp only; rw [hVer, hNoColl, hLook]; dsimp only; rw [hStitch]; rfl⟩
        | true =>
          dsimp only; rw [hStitch]
          have hStUnf := hStitch; unfold parentStitchCheck at hStUnf
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hStUnf
          obtain ⟨⟨⟨hDec, hVerL⟩, hVerR⟩, _⟩ := hStUnf
          unfold checkChildHeaders at hDec
          obtain ⟨hRegL, hRegR, _, _, hMsgL, hMsgR, hLoL, hHiL, hMid, _, hQSum⟩ := of_decide_eq_true hDec
          rcases extractMultiDepthQrom_inductive_sound env hDep H T hNoColl d stmtL piL hVerL with
            ⟨shL, hExL, hLenL, hIdsL, hSumL, hValL⟩ | ⟨idxL, lvlL, sL, pL, hLtL, hLvlL, hAtL, hBadL⟩
          · rcases extractMultiDepthQrom_inductive_sound env hDep H T hNoColl d stmtR piR hVerR with
              ⟨shR, hExR, hLenR, hIdsR, hSumR, hValR⟩ | ⟨idxR, lvlR, sR, pR, hLtR, hLvlR, hAtR, hBadR⟩
            · left; rw [hExL, hExR]
              refine ⟨shL ++ shR, rfl,
                by rw [List.length_append, hLenL, hLenR, Nat.pow_succ, Nat.mul_two],
                by rw [List.map_append, hIdsL, hIdsR, hLoL, ← hMid, hHiL, Nat.pow_succ, Nat.mul_two, List.range'_append_1],
                by rw [List.map_append, List.sum_append, hSumL, hSumR, hQSum], fun sh hMem => ?_⟩
              rcases List.mem_append.mp hMem with hInL | hInR
              · have hv := hValL sh hInL; rwa [hRegL, hMsgL] at hv
              · have hv := hValR sh hInR; rwa [hRegR, hMsgR] at hv
            · exact .inr ⟨1 + treeNodeCount d + idxR, lvlR, sR, pR,
                by rw [treeNodeCount_succ]; omega, by omega, by
                  rw [show 1 + treeNodeCount d + idxR = (treeNodeCount d + idxR) + 1 by omega,
                    treeNodeAt, hLook]; simpa [show ¬ treeNodeCount d + idxR < treeNodeCount d by omega] using hAtR, hBadR⟩
          · exact .inr ⟨1 + idxL, lvlL, sL, pL,
              by rw [treeNodeCount_succ]; omega, by omega, by
                rw [Nat.add_comm 1 idxL, treeNodeAt, hLook]; simpa [hLtL] using hAtL, hBadL⟩

/-- Pair the responses with the queries recorded by the oracle interpreter. -/
def recordedIvcRun {α : Type} (ro : Spec.Bytes → Spec.Bytes)
    (p : OracleComp Spec.Bytes Spec.Bytes α) : α × QromQueryTranscript :=
  (evalOracleComp ro p, (queryLog ro p).map fun x => (x,ro x))

theorem recordedIvcRun_spec {α : Type} (ro : Spec.Bytes → Spec.Bytes)
    (p : OracleComp Spec.Bytes Spec.Bytes α) {Q : Nat} (hq : QueryBounded Q p) :
    (recordedIvcRun ro p).2.length ≤ Q ∧ ∀ e ∈ (recordedIvcRun ro p).2, e.2 = ro e.1 := by
  constructor
  · simpa [recordedIvcRun] using queryLog_length_le ro hq
  · intro e he
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp he
    rfl

def indexedStepBad {n : Nat} (env : IvcExtractionContext n) (ro : Spec.Bytes → Spec.Bytes)
    (d : Nat) (run : (IvcTreeStatement × FixedShapeWhirProof env.cfg.params) × QromQueryTranscript)
    (idx : Nat) : Bool :=
  (treeNodeAt env ro run.2 d run.1.1 run.1.2 idx).any
    fun (level,s,p) => concreteIvcStepBad env ro run.2 level s p

theorem erasedTranscript_fails {n : Nat} (env : IvcExtractionContext n) (ro : Spec.Bytes → Spec.Bytes)
    (d : Nat) (s : IvcTreeStatement) (p : FixedShapeWhirProof env.cfg.params)
    (h : verifyConcreteIvcRoot env.profile env.cfg ro d s p = true) :
    hasQueryCollision [] = false ∧ extractMultiDepthQrom env ro d [] s p = none ∧
      concreteIvcStepBad env ro [] d s p = true := by
  have hc : hasQueryCollision [] = false := hasQueryCollision_nil
  cases d <;> simp [extractMultiDepthQrom, concreteIvcStepBad, h, hc, extractIvcStepFromTranscript_nil]

/-- Constant challenger coins admit replay of a known accepted proof as a zero-query program. -/
theorem singletonReplay_exceeds_128 {n : Nat} (env : IvcExtractionContext n)
    (ro : Spec.Bytes → Spec.Bytes) (d : Nat) (s : IvcTreeStatement)
    (p : FixedShapeWhirProof env.cfg.params) (h : verifyConcreteIvcRoot env.profile env.cfg ro d s p = true) :
    let run := recordedIvcRun ro (.pure (s,p))
    ¬ Spec.GameBound (Spec.FinGame.mk (n := 1) (by decide) (fun _ =>
      verifyConcreteIvcRoot env.profile env.cfg ro d run.1.1 run.1.2 &&
      (extractMultiDepthQrom env ro d run.2 run.1.1 run.1.2).isNone)).winProb (Spec.RatBound.invPow2 128) := by
  have he := (erasedTranscript_fails env ro d s p h).2.1
  dsimp only
  have hr : recordedIvcRun ro (.pure (s,p)) = ((s,p),[]) := by
    simp [recordedIvcRun, evalOracleComp, queryLog_pure]
  rw [hr]
  simp only [h, he, Option.isNone_none, Bool.and_self]
  change ¬ (1 * 2 ^ 128 ≤ 1 * 1)
  decide

private theorem sampleSum_allZero :
    ∀ (n : Nat) (f : Fin n → Nat), (∀ ω : Fin n, f ω = 0) → Spec.sampleSum n f = 0
  | 0, _, _ => rfl
  | n + 1, f, hZ => by
    unfold Spec.sampleSum
    rw [hZ ⟨0, Nat.zero_lt_succ n⟩, Nat.zero_add]
    exact sampleSum_allZero n _ (fun i => hZ _)

private theorem sampleSum_le_add :
    ∀ (n : Nat) (f g h : Fin n → Nat),
      (∀ ω : Fin n, f ω ≤ g ω + h ω) →
      Spec.sampleSum n f ≤ Spec.sampleSum n g + Spec.sampleSum n h
  | 0, _, _, _, _ => Nat.le_refl 0
  | n + 1, f, g, h, hPt => by
    unfold Spec.sampleSum
    have h0 := hPt ⟨0, Nat.zero_lt_succ n⟩
    have ih := sampleSum_le_add n
      (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
      (fun i => g ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
      (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
      (fun i => hPt ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    omega

private theorem sampleSum_any_fin_le {n : Nat} :
    ∀ (m : Nat) (nodeBad : Nat → Fin n → Bool),
      Spec.sampleSum n (fun ω => if (List.range m).any (fun k => nodeBad k ω) then 1 else 0) ≤
        (List.range m).foldr (fun k acc =>
          Spec.sampleSum n (fun ω => if nodeBad k ω then 1 else 0) + acc) 0
  | 0, nodeBad => by
    have hZ : Spec.sampleSum n
        (fun ω => if (List.range 0).any (fun k => nodeBad k ω) then 1 else 0) = 0 :=
      sampleSum_allZero n _ (fun _ => rfl)
    rw [hZ]
    exact Nat.zero_le _
  | m + 1, nodeBad => by
    have ih := sampleSum_any_fin_le m nodeBad
    have hSum : Spec.sampleSum n (fun ω => if (List.range (m + 1)).any (fun k => nodeBad k ω) then 1 else 0) ≤
        Spec.sampleSum n (fun ω => if (List.range m).any (fun k => nodeBad k ω) then 1 else 0) +
        Spec.sampleSum n (fun ω => if nodeBad m ω then 1 else 0) :=
      sampleSum_le_add n _ _ _ (fun ω => by
        rw [List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
        cases (List.range m).any (fun k => nodeBad k ω) <;> cases nodeBad m ω <;> decide)
    have hFoldAppend :
        (List.range (m + 1)).foldr (fun k acc =>
          Spec.sampleSum n (fun ω => if nodeBad k ω then 1 else 0) + acc) 0 =
        (List.range m).foldr (fun k acc =>
          Spec.sampleSum n (fun ω => if nodeBad k ω then 1 else 0) + acc) 0 +
          Spec.sampleSum n (fun ω => if nodeBad m ω then 1 else 0) := by
      rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, Nat.add_zero]
      clear ih hSum
      generalize Spec.sampleSum n (fun ω => if nodeBad m ω then 1 else 0) = tailVal
      induction (List.range m) with
      | nil => exact (Nat.zero_add tailVal).symm
      | cons a as iha => simp only [List.foldr_cons, iha, Nat.add_assoc]
    rw [hFoldAppend]
    exact Nat.le_trans hSum (Nat.add_le_add_right ih _)

private theorem foldr_bounded_le_scale {n m : Nat} (ε : RatBound) (nodeBad : Nat → Fin n → Bool)
    (hEach : ∀ k, k < m → Spec.sampleSum n (fun ω => if nodeBad k ω then 1 else 0) * ε.den ≤ ε.num * n) :
    ∀ j : Nat, j ≤ m →
      ((List.range j).foldr (fun k acc =>
        Spec.sampleSum n (fun ω => if nodeBad k ω then 1 else 0) + acc) 0) * ε.den ≤
        (j * ε.num) * n
  | 0, _ => by simp
  | j + 1, hj => by
    have ih := foldr_bounded_le_scale ε nodeBad hEach j (by omega)
    have hLast := hEach j (by omega)
    have hFold :
        (List.range (j + 1)).foldr (fun k acc =>
          Spec.sampleSum n (fun ω => if nodeBad k ω then 1 else 0) + acc) 0 =
        (List.range j).foldr (fun k acc =>
          Spec.sampleSum n (fun ω => if nodeBad k ω then 1 else 0) + acc) 0 +
          Spec.sampleSum n (fun ω => if nodeBad j ω then 1 else 0) := by
      rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, Nat.add_zero]
      generalize Spec.sampleSum n (fun ω => if nodeBad j ω then 1 else 0) = v
      induction (List.range j) with
      | nil => exact (Nat.zero_add v).symm
      | cons a as iha => simp only [List.foldr_cons, iha, Nat.add_assoc]
    rw [hFold, Nat.add_mul, Nat.succ_mul, Nat.add_mul]
    exact Nat.add_le_add ih hLast

/-- Finite union bound for the concrete indexed extraction event. To instantiate this result
with a schedule error one must prove that error bounds each reachable node in the oracle game. -/
theorem multidepth_recursive_qrom_extractor_sound {n nc na nv : Nat}
    (env : IvcExtractionContext nv) (hDep : IsDeployedAggProfile env.profile)
    (d Q : Nat) (hn : 0 < n) (π : Spec.CoinSplit n nc na)
    (oracle : Fin nc → Spec.Bytes → Spec.Bytes)
    (prover : Fin na → OracleComp Spec.Bytes Spec.Bytes (IvcTreeStatement × FixedShapeWhirProof env.cfg.params))
    (budget : ∀ i, QueryBounded Q (prover i)) (step coll : RatBound) :
    let H := fun w => oracle (π.chal w)
    let run := fun w => recordedIvcRun (H w) (prover (π.advc w))
    let bad := fun i w => indexedStepBad env (H w) d (run w) i
    let collision := fun w => hasQueryCollision (run w).2
    let fail := fun w => verifyConcreteIvcRoot env.profile env.cfg (H w) d (run w).1.1 (run w).1.2 &&
      (extractMultiDepthQrom env (H w) d (run w).2 (run w).1.1 (run w).1.2).isNone
    (∀ i, i < treeNodeCount d →
      Spec.GameBound (Spec.FinGame.mk hn (bad i)).winProb (toSpecRatBound step)) →
    Spec.GameBound (Spec.FinGame.mk hn collision).winProb (toSpecRatBound coll) →
    (∀ w, (run w).2.length ≤ Q ∧ (fail w = true →
      (∃ b, Spec.TranscriptBreak (H w) (run w).2 b) ∨ ∃ i < treeNodeCount d, bad i w = true)) ∧
    Spec.GameBound (Spec.FinGame.mk hn fail).winProb
      (toSpecRatBound (RatBound.add (RatBound.scale (treeNodeCount d) step) coll)) := by
  intro H run bad collision fail perNode collisionBound
  have cover (w : Fin n) (hf : fail w = true) :
      (List.range (treeNodeCount d)).any (fun i => bad i w) = true ∨ collision w = true := by
    cases hc : collision w with
    | true => exact .inr rfl
    | false =>
      obtain ⟨hv, he⟩ := Bool.and_eq_true_iff.mp hf
      rcases extractMultiDepthQrom_inductive_sound env hDep (H w) (run w).2 hc d
          (run w).1.1 (run w).1.2 hv with
        ⟨_, hx, _⟩ | ⟨i,l,s,p,hi,_,hat,hb⟩
      · rw [hx] at he
        cases he
      · left
        exact List.any_eq_true.mpr ⟨i, List.mem_range.mpr hi, by
          simpa [bad, indexedStepBad, hat] using hb⟩
  constructor
  · intro w
    obtain ⟨hlen, hlog⟩ := recordedIvcRun_spec (H w) _ (budget (π.advc w))
    refine ⟨hlen, fun hf => ?_⟩
    rcases cover w hf with hb | hc
    · obtain ⟨i,hi,hb⟩ := List.any_eq_true.mp hb
      exact .inr ⟨i,List.mem_range.mp hi,hb⟩
    · exact .inl (hasQueryCollision_sound (H w) (run w).2 hlog hc)
  · have hop := Spec.event_le_two_reductions (Spec.FinGame.mk hn fail)
        (Spec.FinGame.mk hn fun w => (List.range (treeNodeCount d)).any fun i => bad i w)
        (Spec.FinGame.mk hn collision) cover
    apply Spec.GameBound.trans hop
    have hPer : Spec.GameBound (Spec.FinGame.mk hn
        (fun w => (List.range (treeNodeCount d)).any fun i => bad i w)).winProb
        (toSpecRatBound (RatBound.scale (treeNodeCount d) step)) :=
      Nat.le_trans (Nat.mul_le_mul_right step.den (sampleSum_any_fin_le (treeNodeCount d) bad))
      (foldr_bounded_le_scale step bad perNode (treeNodeCount d) (Nat.le_refl _))
    exact Spec.RatBound.add_le_add hPer collisionBound

#verify_constructive recordedIvcRun_spec erasedTranscript_fails sampleSum_allZero sampleSum_le_add
  sampleSum_any_fin_le foldr_bounded_le_scale multidepth_recursive_qrom_extractor_sound
private theorem le_countMax {x : Nat} (xs : List Nat) (hx : x ∈ xs) :
    x ≤ xs.foldr Nat.max 0 := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    cases hx with
    | head => exact Nat.le_max_left _ _
    | tail _ hm => exact Nat.le_trans (ih hm) (Nat.le_max_right _ _)

/-- Unconditional finite-game bound in terms of the measured worst reachable-node probability.
Neither the collision probability nor the per-node probability is supplied by the caller. -/
theorem measuredIvcExtractionFailure_bound {n nc na nv : Nat}
    (env : IvcExtractionContext nv) (hDep : IsDeployedAggProfile env.profile)
    (d Q : Nat) (hn : 0 < n) (π : Spec.CoinSplit n nc na)
    (oracle : Fin nc → Spec.Bytes → Spec.Bytes)
    (prover : Fin na → OracleComp Spec.Bytes Spec.Bytes (IvcTreeStatement × FixedShapeWhirProof env.cfg.params))
    (budget : ∀ i, QueryBounded Q (prover i)) :
    let H := fun w => oracle (π.chal w)
    let run := fun w => recordedIvcRun (H w) (prover (π.advc w))
    let count := fun i => (Spec.FinGame.mk hn (fun w => indexedStepBad env (H w) d (run w) i)).winCount
    let step : RatBound := ⟨((List.range (treeNodeCount d)).map count).foldr Nat.max 0,n,hn⟩
    let collision := Spec.FinGame.mk hn (fun w => hasQueryCollision (run w).2)
    let coll : RatBound := ⟨collision.winCount,n,hn⟩
    let fail := Spec.FinGame.mk hn (fun w => verifyConcreteIvcRoot env.profile env.cfg (H w) d
        (run w).1.1 (run w).1.2 &&
      (extractMultiDepthQrom env (H w) d (run w).2 (run w).1.1 (run w).1.2).isNone)
    Spec.GameBound fail.winProb (toSpecRatBound (RatBound.add (RatBound.scale (treeNodeCount d) step) coll)) := by
  intro H run count step collision coll fail
  apply (multidepth_recursive_qrom_extractor_sound env hDep d Q hn π oracle prover budget step coll ?_ ?_).2
  · intro i hi
    exact Nat.mul_le_mul_right n (le_countMax _ (List.mem_map_of_mem (f := count) (List.mem_range.mpr hi)))
  · exact Spec.GameBound.refl collision.winProb

#verify_constructive le_countMax measuredIvcExtractionFailure_bound

theorem multidepth_recursive_refines_idealAggregate {nVal : Nat}
    (env : IvcExtractionContext nVal) (hDep : IsDeployedAggProfile env.profile)
    (H : Spec.Bytes → Spec.Bytes) (d : Nat)
    (T : QromQueryTranscript) (stmt : IvcTreeStatement)
    (rootProof : FixedShapeWhirProof env.cfg.params)
    (shards : List (ExtractedLeafShard nVal))
    (hEx : extractMultiDepthQrom env H d T stmt rootProof = some shards) :
    (∀ sh ∈ shards,
      Spec.ValidAggregateWitness (verifyAggNativeSig (profileGeom env.profile)) sh.stmt
        (fun i => some (extractSlotNativeSig env.profile sh.rows i.val))) ∧
    (Spec.idealAggregateMachine (verifyAggNativeSig (profileGeom env.profile))).ValidTrace []
      (shards.map (fun sh => ((sh.stmt, fun i => some (extractSlotNativeSig env.profile sh.rows i.val)), ())))
      (shards.map ExtractedLeafShard.stmt) := by
  have hEachValid : ∀ (lvl : Nat) (s0 : IvcTreeStatement) (p0 : FixedShapeWhirProof env.cfg.params)
      (out : List (ExtractedLeafShard nVal)),
      extractMultiDepthQrom env H lvl T s0 p0 = some out →
      ∀ sh ∈ out,
        (List.finRange nVal).all (fun i =>
          !sh.stmt.bitmap.getLsbD i.val || ((sh.stmt.roster i).profile == env.profile)) = true ∧
        stepOp256TableOk env.profile (succinctCommitteeSlots sh.stmt) sh.rows = true := by
    intro lvl; induction lvl with
    | zero =>
      intro s0 p0 out hOut sh hMem
      unfold extractMultiDepthQrom at hOut
      cases hV : verifyConcreteIvcRoot env.profile env.cfg H 0 s0 p0 <;> rw [hV] at hOut
      · cases hOut
      · cases hL : extractIvcStepFromTranscript nVal env.profile H T 0 s0 p0 <;> rw [hL] at hOut
        · cases hOut
        · rename_i w; cases w with
          | parent _ _ _ _ _ => cases hOut
          | leaf shard =>
            dsimp only at hOut
            cases hg : leafNodeCheck env.profile H s0 shard <;> rw [hg] at hOut
            · cases hOut
            · injection hOut with hEq; subst hEq
              rcases List.mem_singleton.mp hMem with rfl
              unfold leafNodeCheck at hg; rw [Bool.and_eq_true, Bool.and_eq_true] at hg
              exact ⟨hg.1.2, hg.2⟩
    | succ k ih =>
      intro s0 p0 out hOut sh hMem
      unfold extractMultiDepthQrom at hOut
      cases hV : verifyConcreteIvcRoot env.profile env.cfg H (k + 1) s0 p0 <;> rw [hV] at hOut
      · cases hOut
      · cases hL : extractIvcStepFromTranscript nVal env.profile H T (k + 1) s0 p0 <;> rw [hL] at hOut
        · cases hOut
        · rename_i w; cases w with
          | leaf _ => cases hOut
          | parent sL sR pL pR fold =>
            dsimp only at hOut
            cases hg : parentStitchCheck env H k s0 sL sR pL pR p0 fold <;> rw [hg] at hOut
            · cases hOut
            · cases heL : extractMultiDepthQrom env H k T sL pL <;> rw [heL] at hOut
              · cases hOut
              · cases heR : extractMultiDepthQrom env H k T sR pR <;> rw [heR] at hOut
                · cases hOut
                · injection hOut with hEq; subst hEq
                  rcases List.mem_append.mp hMem with hmL | hmR
                  · exact ih sL pL _ heL sh hmL
                  · exact ih sR pR _ heR sh hmR
  have valid : ∀ sh ∈ shards, Spec.ValidAggregateWitness (verifyAggNativeSig (profileGeom env.profile))
      sh.stmt (fun i => some (extractSlotNativeSig env.profile sh.rows i.val)) := by
    intro sh hm
    obtain ⟨hp,ht⟩ := hEachValid d stmt rootProof shards hEx sh hm
    exact stepOp256TableOk_bothProfiles_extract env.profile hDep sh.stmt sh.rows hp ht
  refine ⟨valid, ?_⟩
  have trace (xs : List (ExtractedLeafShard nVal)) (log : List (Spec.AggregateStatement AggValidatorPk nVal))
      (hv : ∀ sh ∈ xs, Spec.ValidAggregateWitness (verifyAggNativeSig (profileGeom env.profile))
        sh.stmt (fun i => some (extractSlotNativeSig env.profile sh.rows i.val))) :
      (Spec.idealAggregateMachine (verifyAggNativeSig (profileGeom env.profile))).ValidTrace log
        (xs.map fun sh => ((sh.stmt, fun i => some (extractSlotNativeSig env.profile sh.rows i.val)), ()))
        (log ++ xs.map ExtractedLeafShard.stmt) := by
    induction xs generalizing log with
    | nil =>
      simp only [List.map_nil, List.append_nil]
      exact .nil log
    | cons x xs ih =>
      apply Spec.Machine.ValidTrace.accept
        (Spec.idealAggregateMachine_accepts_witness _ log x.stmt _ (hv x List.mem_cons_self))
      simpa using ih (log ++ [x.stmt]) (fun sh hm => hv sh (List.mem_cons_of_mem _ hm))
  exact trace shards [] valid

/-- **Arbitrary-Depth `d` Reduction to Leaf `EUF-CMA` (`multidepth_recursive_euf_cma_reduction`):**
    If a depth-`d` succinct recursive root proof is accepted (`verifySuccinctIvcRoot = true`), then
    EITHER QROM collision occurs on `T` (`hasQueryCollision T = true`), OR one of the `2^{d+1} - 1`
    tree nodes hits `concreteIvcStepBad`, OR for **every** extracted leaf shard `sh ∈ shards` and **every**
    active validator `v` in `sh`, either `v`'s quorum participated OR a single-signer leaf `EUF-CMA`
    forgery (`Composed.QuorumForgery`) is constructively extracted! -/
theorem multidepth_recursive_euf_cma_reduction {nVal : Nat}
    (env : IvcExtractionContext nVal) (hDep : IsDeployedAggProfile env.profile)
    (H : Spec.Bytes → Spec.Bytes) (T : QromQueryTranscript)
    (d : Nat) (stmt : IvcTreeStatement) (rootProof : FixedShapeWhirProof env.cfg.params)
    (custodyOf : Nat → Fin nVal → Composed.Custody)
    (hAcc : verifyConcreteIvcRoot env.profile env.cfg H d stmt rootProof = true) :
    hasQueryCollision T = true ∨
    (∃ (nodeIdx lvl : Nat) (sN : IvcTreeStatement) (pN : FixedShapeWhirProof env.cfg.params),
      nodeIdx < treeNodeCount d ∧ lvl ≤ d ∧ treeNodeAt env H T d stmt rootProof nodeIdx = some (lvl,sN,pN) ∧ concreteIvcStepBad env H T lvl sN pN = true) ∨
    (∃ shards : List (ExtractedLeafShard nVal),
      extractMultiDepthQrom env H d T stmt rootProof = some shards ∧
      shards.length = 2 ^ d ∧
      ∀ sh ∈ shards,
        (∀ v : Fin nVal, sh.stmt.roster v = (custodyOf sh.shardId v).state.pk) →
        ∀ v : Fin nVal, sh.stmt.bitmap.getLsbD v.val = true →
          Composed.QuorumForgery (profileGeom env.profile) (custodyOf sh.shardId v) stmt.message ∨
          Composed.quorumParticipated (custodyOf sh.shardId v) stmt.message = true) := by
  cases hColl : hasQueryCollision T with
  | true => exact .inl rfl
  | false =>
    rcases extractMultiDepthQrom_inductive_sound env hDep H T hColl d stmt rootProof hAcc with
      ⟨shards, hEx, hLen, _, _, hVal⟩ | hBad
    · right; right
      refine ⟨shards, hEx, hLen, fun sh hMem hRoster v hAct => ?_⟩
      obtain ⟨_, _, hMsg, _, _, hWit, _⟩ := hVal sh hMem
      obtain ⟨sig, _, hSigVer⟩ := (Spec.ValidAggregateWitness_iff _ _ _).mp hWit v hAct
      rw [hRoster v, hMsg] at hSigVer
      cases hq : Composed.quorumParticipated (custodyOf sh.shardId v) stmt.message with
      | false => exact .inl ⟨sig, hSigVer, hq⟩
      | true => exact .inr rfl
    · exact .inr (.inl hBad)

theorem multidepth_recursive_budget_lt_128
    (prof : WhirCommitmentProfile) {d Q : Nat} (hd : d ≤ 16) (hQ : Q ≤ 2 ^ 64) :
    RatBound.lt
      (RatBound.add (RatBound.scale (treeNodeCount d) (scheduleQromError zkHemV2RecursiveMarginSched Q))
        (merkleProfileQromBound prof Q))
      (RatBound.invPow2 128) :=
  zkHemV2RecursiveMargin_tree_lt_128 prof hd hQ

/-- Leaf completeness for a native active XMSS signer and a 64-level registry path. -/
theorem activeXmssLeaf_validQuorum (ro : Spec.Bytes → Spec.Bytes) (id : Nat) (hid : id < 2 ^ 64)
    (path : List Spec.Bytes) (hlen : path.length = 64)
    (ctrs : ValidSigningCtrs xmssPoseidon2Geom auditSkSeed
      (deriveAggPublicKey xmssPoseidon2Geom auditSkSeed auditPkSeed) auditMsg auditRRand 0) :
    let pk := deriveAggPublicKey xmssPoseidon2Geom auditSkSeed auditPkSeed
    let sig := signAggNative xmssPoseidon2Geom auditSkSeed pk auditMsg auditRRand 0 ctrs.layer0Ctr ctrs.upperCtrs
    let rows := stepXmssRows pk (computeMessageMu pk auditMsg) sig
    let s : ExtractedLeafShard 1 := ⟨id,1,1,⟨fun _ => pk,1#1,auditMsg⟩,rows,path⟩
    ValidQuorumSignatures .xmssPoseidon2 ro (registryRootFor ro s) auditMsg s := by
  intro pk sig rows s
  have hVerSig : verifyAggNativeSig xmssPoseidon2Geom pk auditMsg sig = true :=
    (inhabited_aggNativeSig_euf_cma_pipeline.2.2.2 ctrs).1
  have hPkProf : pk.profile = .xmssPoseidon2 := stepXmssNative_profile pk auditMsg sig hVerSig
  have hSlots : succinctCommitteeSlots (⟨fun _ => pk, 1#1, auditMsg⟩ :
      Spec.AggregateStatement AggValidatorPk 1) = [some (pk, computeMessageMu pk auditMsg)] := by
    have hFin1 : List.finRange 1 = [⟨0, by decide⟩] := by decide
    have hBit1 : (1#1 : BitVec 1).getLsbD 0 = true := by decide
    unfold succinctCommitteeSlots; rw [hFin1]; dsimp only [List.map]; rw [hBit1]; rfl
  have hTable : stepOp256TableOk .xmssPoseidon2
      (succinctCommitteeSlots (⟨fun _ => pk, 1#1, auditMsg⟩ :
        Spec.AggregateStatement AggValidatorPk 1)) rows = true := by
    rw [hSlots]; exact stepXmssRows_of_verify pk auditMsg sig hVerSig
  have hProf : (List.finRange 1).all (fun i =>
      !(1#1 : BitVec 1).getLsbD i.val || (pk.profile == .xmssPoseidon2)) = true := by
    have hFin1 : List.finRange 1 = [⟨0, by decide⟩] := by decide
    rw [hFin1]; simp [hPkProf]
  refine ⟨Nat.one_pos, (show 1 ≤ Composed.weight (1#1) by decide), rfl, hProf, hTable, ?_, ?_⟩
  · exact stepOp256TableOk_bothProfiles_extract .xmssPoseidon2 (.inl rfl) s.stmt s.rows hProf hTable
  · exact registryMember_rootFor ro s hlen hid

theorem inhabited_multidepth_lt_128 :
    ∃ (prof : WhirCommitmentProfile) (d Q : Nat),
      d ≤ 16 ∧ Q ≤ 2 ^ 64 ∧ 0 < (merkleProfileQromBound prof Q).den :=
  ⟨.poseidon2Gl24,16,2^64,Nat.le_refl _,Nat.le_refl _,(merkleProfileQromBound .poseidon2Gl24 (2^64)).h_pos⟩

#verify_constructive activeXmssLeaf_validQuorum inhabited_multidepth_lt_128
#verify_inhabited multidepth_recursive_budget_lt_128 inhabited_multidepth_lt_128
theorem parentStitchCheck_verifies_both {n : Nat} (env : IvcExtractionContext n)
    (ro : Spec.Bytes → Spec.Bytes) (d : Nat) (s l r : IvcTreeStatement)
    (pl pr parent : FixedShapeWhirProof env.cfg.params) (fold : List Goldilocks)
    (h : parentStitchCheck env ro d s l r pl pr parent fold = true) :
    checkChildHeaders d s l r = true ∧ verifyConcreteIvcRoot env.profile env.cfg ro d l pl = true ∧
      verifyConcreteIvcRoot env.profile env.cfg ro d r pr = true := by
  simpa only [Bool.and_eq_true, and_assoc] using (Bool.and_eq_true_iff.mp h).1

def toothEnv : IvcExtractionContext 1 :=
  ⟨.xmssPoseidon2,⟨⟨5,2,[⟨2,5,1,13,4⟩,⟨1,2,1,10,3⟩]⟩,1,0,24,[]⟩⟩

def toothStmt (lo hi : Nat) : IvcTreeStatement := ⟨[],0,lo,hi,hi-lo,[42]⟩

def omittedChild : FixedShapeWhirProof toothEnv.cfg.params := ⟨0,0,[],[],[],[]⟩

def childArgumentDigest {p : IvcWhirParams} (ro : Spec.Bytes → Spec.Bytes) (s : IvcTreeStatement)
    (pi : FixedShapeWhirProof p) : Spec.Bytes :=
  -- "IVC-CHILD-ARGUMENT"
  ro (encodeMultiFrame [[73, 86, 67, 45, 67, 72, 73, 76, 68, 45, 65, 82, 71, 85, 77, 69, 78, 84], NodeWire.statement s, encodeFixedShapeWhirProof pi])

/-- Header-and-digest mutation of the parent check used by the negative test. -/
def digestOnlyStitch {p : IvcWhirParams} (ro : Spec.Bytes → Spec.Bytes) (d : Nat)
    (s l r : IvcTreeStatement) (pl pr : FixedShapeWhirProof p) (dl dr : Spec.Bytes) : Bool :=
  checkChildHeaders d s l r && decide (childArgumentDigest ro l pl = dl ∧ childArgumentDigest ro r pr = dr)

/-- Two contiguous headers pass the digest-only mutation despite omitted child arguments. -/
theorem tooth_digestOnly_recursion_forges_without_child_verifier :
    ¬ (digestOnlyStitch (shake256Xof 56) 1 (toothStmt 0 4) (toothStmt 0 2) (toothStmt 2 4)
        omittedChild omittedChild (childArgumentDigest (shake256Xof 56) (toothStmt 0 2) omittedChild)
        (childArgumentDigest (shake256Xof 56) (toothStmt 2 4) omittedChild) = false ∨
      parentStitchCheck toothEnv (shake256Xof 56) 1 (toothStmt 0 4) (toothStmt 0 2)
        (toothStmt 2 4) omittedChild omittedChild omittedChild [] = true) := by
  have headers : checkChildHeaders 1 (toothStmt 0 4) (toothStmt 0 2) (toothStmt 2 4) = true := by decide +kernel
  have bad : omittedChild.wellFormed = false := by decide +kernel
  have reject := verifyConcreteIvcRoot_rejects_shape toothEnv.profile toothEnv.cfg (shake256Xof 56)
    1 (toothStmt 0 2) omittedChild bad
  simp [digestOnlyStitch, parentStitchCheck, headers, reject]

theorem tooth_root_interval_bit_flip (profile : AggSigProfile) (cfg : ConcreteIvcConfig)
    (ro : Spec.Bytes → Spec.Bytes) (p : FixedShapeWhirProof cfg.params) :
    ¬ (verifyConcreteIvcRoot profile cfg ro 2 {(toothStmt 0 4) with hi := 4 ^^^ 1} p = true) := by
  rw [verifyConcreteIvcRoot_rejects_interval _ _ _ _ _ _ (by decide +kernel)]
  decide

theorem tooth_child_boundary_bit_flip :
    ¬ (checkChildHeaders 1 (toothStmt 0 4) {(toothStmt 0 2) with hi := 2 ^^^ 1} (toothStmt 2 4) = true) := by
  decide +kernel

#verify_constructive tooth_root_interval_bit_flip tooth_child_boundary_bit_flip
#tooth_pair verifyConcreteIvcRoot_rejects_interval vs tooth_root_interval_bit_flip
#tooth_pair parentStitchCheck_verifies_both vs tooth_child_boundary_bit_flip

#verify_constructive parentStitchCheck_verifies_both tooth_digestOnly_recursion_forges_without_child_verifier
  singletonReplay_exceeds_128
#tooth_pair parentStitchCheck_verifies_both vs tooth_digestOnly_recursion_forges_without_child_verifier

#verify_constructive treeNodeCount_zero treeNodeCount_succ extractMultiDepthQrom_inductive_sound
  multidepth_recursive_refines_idealAggregate multidepth_recursive_euf_cma_reduction
  multidepth_recursive_budget_lt_128

#tooth_pair ivcRootProof_byteSize_independent_of_depth vs tooth_unbounded_proof_violates_constant_openingByteLen
#tooth_pair poseidon2W24_twoChildStep_fits_2pow20_rows vs tooth_poseidon2_w12_twoChildStep_exceeds_2pow20_rows

/-- Prove the leaves in interval order, then commit their proofs and matrix fold at
each parent. Each node starts its own Fiat–Shamir state. -/
def proveConcreteIvcTree {nVal : Nat} (env : IvcExtractionContext nVal)
    (ro : Spec.Bytes → Spec.Bytes) (d lo : Nat) (regRoot : Spec.Bytes)
    (epochFloor : Nat) (msg : Spec.Bytes) (shards : List (ExtractedLeafShard nVal))
    (leafAcc : IvcAlgebra.MatrixClaim) (privateCellsFn : Nat → Nat → List Goldilocks)
    (seedPrefix : Spec.Bytes) :
    Option (IvcTreeStatement × FixedShapeWhirProof env.cfg.params × QromQueryTranscript) := do
  let finish level start stmt w acc log := do
    let seed := encodeMultiFrame [seedPrefix, leb128 level, leb128 start]
    let (pi, trace) ← (IvcAlgebra.proveCommittedIvcArgument (n := nVal) env.profile env.cfg ro
      level stmt w acc seed (privateCellsFn level start)).run {}
    return (stmt, pi, log ++ trace.reverseLog.reverse)
  match d with
  | 0 =>
    let [s] := shards | none
    guard (s.shardId == lo && s.stmt.message == msg)
    finish 0 lo ⟨regRoot, epochFloor, lo, lo + 1, s.quorumCount, msg⟩ (.leaf s) leafAcc []
  | k + 1 =>
    let width := 2 ^ k
    let (l, pl, ql) ← proveConcreteIvcTree env ro k lo regRoot epochFloor msg
      (shards.take width) leafAcc privateCellsFn seedPrefix
    let (r, pr, qr) ← proveConcreteIvcTree env ro k (lo + width) regRoot epochFloor msg
      (shards.drop width) leafAcc privateCellsFn seedPrefix
    let (w, acc) ← IvcAlgebra.prepareParentWitness nVal env.profile env.cfg ro k l r pl pr
    finish (k + 1) lo ⟨regRoot, epochFloor, l.lo, r.hi, l.totalQuorums + r.totalQuorums, msg⟩
      w acc (ql ++ qr)

#verify_kernel proveConcreteIvcTree

/-- A successful extraction authenticates each returned signature against the root
statement. This projection requires neither a collision assumption nor a search for a bad node. -/
theorem extractedQuorums_valid {n : Nat} (env : IvcExtractionContext n)
    (deployed : IsDeployedAggProfile env.profile) (ro : Spec.Bytes → Spec.Bytes)
    (T : QromQueryTranscript) (d : Nat) (s : IvcTreeStatement)
    (p : FixedShapeWhirProof env.cfg.params) (out : List (ExtractedLeafShard n))
    (success : extractMultiDepthQrom env ro d T s p = some out) :
    ∀ sh ∈ out, ValidQuorumSignatures env.profile ro s.policyRegistryRoot s.message sh := by
  induction d generalizing s p out with
  | zero =>
    unfold extractMultiDepthQrom at success
    split at success <;> try contradiction
    split at success <;> try contradiction
    rename_i shard _
    split at success <;> try contradiction
    rename_i ok
    cases success
    intro sh h
    obtain rfl := List.mem_singleton.mp h
    unfold leafNodeCheck at ok
    rw [Bool.and_eq_true, Bool.and_eq_true] at ok
    obtain ⟨⟨dec, prof⟩, table⟩ := ok
    obtain ⟨_, _, _, count, weight, msg, reg, _⟩ := of_decide_eq_true dec
    exact ⟨count, weight, msg, prof, table,
      stepOp256TableOk_bothProfiles_extract env.profile deployed _ _ prof table, reg⟩
  | succ d ih =>
    unfold extractMultiDepthQrom at success
    split at success <;> try contradiction
    split at success <;> try contradiction
    split at success <;> try contradiction
    rename_i stitch
    split at success <;> try contradiction
    rename_i left right hl hr
    cases success
    have headers := (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp stitch).1).1).1
    obtain ⟨regL, regR, _, _, msgL, msgR, _⟩ := of_decide_eq_true headers
    intro sh h
    rcases List.mem_append.mp h with h | h
    · simpa only [regL, msgL] using ih _ _ left hl sh h
    · simpa only [regR, msgR] using ih _ _ right hr sh h

#verify_constructive extractedQuorums_valid

/-- Every accepted parent rejects changing the low bit of the left child's right boundary. -/
theorem parentStitchCheck_childHi_flip {n : Nat} (env : IvcExtractionContext n)
    (ro : Spec.Bytes → Spec.Bytes) (d : Nat) (s l r : IvcTreeStatement)
    (pl pr parent : FixedShapeWhirProof env.cfg.params) (fold : List Goldilocks)
    (ok : parentStitchCheck env ro d s l r pl pr parent fold = true) :
    ¬ (parentStitchCheck env ro d s {l with hi := l.hi ^^^ 1} r pl pr parent fold = true) := by
  intro altered
  have original := (parentStitchCheck_verifies_both _ _ _ _ _ _ _ _ _ _ ok).1
  have changed := (parentStitchCheck_verifies_both _ _ _ _ _ _ _ _ _ _ altered).1
  unfold checkChildHeaders at original changed
  have mid := (of_decide_eq_true original).2.2.2.2.2.2.2.2.1
  have other := (of_decide_eq_true changed).2.2.2.2.2.2.2.2.1
  change l.hi ^^^ 1 = r.lo at other
  rw [← mid] at other
  have impossible := congrArg (fun k => l.hi ^^^ k) other
  have eq : 1 = 0 := by
    simpa only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] using impossible
  contradiction

#verify_constructive parentStitchCheck_childHi_flip
#tooth_pair parentStitchCheck_verifies_both vs parentStitchCheck_childHi_flip

open IvcAlgebra in
/-- Executable fixture with a seventh-power row and a private Boolean row in each circuit. -/
def realDepth2Env : IvcExtractionContext 1 :=
  let width := 30
  let matrix : List SparseEntry := [false,true].flatMap fun step =>
    [⟨0,0,0,step,.one⟩, ⟨0,0,2,step,.one⟩,
     ⟨1,width+1,0,step,.one⟩, ⟨1,width+1,1,step,.one⟩, ⟨1,width+1,2,step,.one⟩]
  ⟨.xmssPoseidon2, ⟨⟨5,2,[⟨2,5,1,13,4⟩,⟨1,2,1,10,3⟩]⟩,1,1,width,matrix⟩⟩

/-- Polynomial byte absorption followed by seven SplitMix64 outputs. Each output
is reduced to a canonical limb for the transcript decoder. Fixture oracle only. -/
def ivcFastXof56 (input : Spec.Bytes) : Spec.Bytes :=
  let state := input.foldl (fun (s : UInt64) b => s * 1099511628211 + b.toUInt64 + 1)
    14695981039346656037
  (List.range 7).flatMap fun i =>
    let z := state + 0x9e3779b97f4a7c15 * (i + 1).toUInt64
    let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9
    let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
    goldilocksToBytesLE (Goldilocks.ofNat (z ^^^ (z >>> 31)).toNat)

def realDepth2LeafAcc : IvcAlgebra.MatrixClaim := ⟨List.replicate 13 .zero, .one⟩

theorem realDepth2LeafAcc_valid :
    IvcAlgebra.checkSparseMatrix realDepth2Env.cfg.params.logCells
      realDepth2Env.cfg.matrixEntries realDepth2LeafAcc = true := by decide +kernel

#verify_constructive realDepth2LeafAcc_valid

/-- Public XMSS input at leaf zero of the existing audit key. The root and the
six siblings are cached so constructing the witness does not sign the other 63 leaves.
The chain signature is generated for the audit message and counter 75. -/
def realDepth2Validator : AggValidatorPk × AggNativeSignature :=
  let lane (a b c d : Nat) : Digest4 :=
    ⟨Goldilocks.ofNat a, Goldilocks.ofNat b, Goldilocks.ofNat c, Goldilocks.ofNat d⟩
  let pk : AggValidatorPk := ⟨.xmssPoseidon2, auditPkSeed,
    lane 3690926187097264219 7566736787732222205 10176382118074955865 12758867095344999659⟩
  let path := [
    lane 4846336481263352241 2597757666866916932 9429260465820565669 9894789749011987550,
    lane 7953622434912262779 17074989025603421244 9506728927506859421 3706719941687098990,
    lane 9434189806512628102 16233860307913929799 4268692714948414682 8248976890072452016,
    lane 15933739023518117102 9024131288799361927 9874998687225347034 15820939896930578627,
    lane 3647938790289962849 3801707473466894100 13288051542904986134 16116442420645072324,
    lane 6295998514126158986 3927169138491465007 9590429413340265261 9960879540526191661]
  let hmsg := computeHmsgStateful pk auditRRand (computeMessageMu pk auditMsg) 0 75
  let digits := (extractWotsDigitsChecked xmssPoseidon2Geom hmsg).getD []
  let chains := digits.zipIdx.map fun (digit, i) =>
    wotsChainWalk auditPkSeed 0 0 0 i 0 digit (wotsSecretStart auditSkSeed auditPkSeed 0 0 0 i)
  (pk, ⟨.xmssPoseidon2, auditRRand, 0, [], [⟨75, chains, path⟩]⟩)

def realDepth2UnregisteredShards : List (ExtractedLeafShard 1) :=
  let (pk, sig) := realDepth2Validator
  let rows := stepXmssRows pk (computeMessageMu pk auditMsg) sig
  let stmt : Spec.AggregateStatement AggValidatorPk 1 := ⟨fun _ => pk, 1#1, auditMsg⟩
  (List.range 4).map fun id => ⟨id, 1, 1, stmt, rows, []⟩

def realDepth2Registry := buildRegistry ivcFastXof56 realDepth2UnregisteredShards

def realDepth2Run := do
  let (root, shards) ← realDepth2Registry
  -- "W1-depth-2"
  proveConcreteIvcTree realDepth2Env ivcFastXof56 2 0 root 0 auditMsg shards realDepth2LeafAcc
    (fun _ _ => [.one]) [87, 49, 45, 100, 101, 112, 116, 104, 45, 50]

def realDepth2Stmt := (realDepth2Run.map Prod.fst).getD ⟨[],0,0,0,0,[]⟩
def realDepth2IvcProof := (realDepth2Run.map fun r => r.2.1).getD ⟨0,0,[],[],[],[]⟩
def realDepth2Transcript := (realDepth2Run.map fun r => r.2.2).getD []

#verify_kernel realDepth2Run realDepth2IvcProof realDepth2Transcript

/-- The executable coverage check on the decoded list. -/
def realDepth2Coverage (shards : List (ExtractedLeafShard 1)) : Bool :=
  decide (shards.length = 4 ∧ shards.map ExtractedLeafShard.shardId = [0,1,2,3] ∧
    (shards.map ExtractedLeafShard.quorumCount).sum = 4)

def realDepth2FlipLimb (words : List Goldilocks) :=
  words.modify 0 (fun x => Goldilocks.ofNat (x.val ^^^ 1))

@[expose] def flipRootCoefficient {p : IvcWhirParams} (pi : FixedShapeWhirProof p) : FixedShapeWhirProof p :=
  {pi with finalCoeffWords := pi.finalCoeffWords.modify 0 (fun x => Goldilocks.ofNat (x.val ^^^ 1))}

@[expose] def flipSecondStageOod {p : IvcWhirParams} (pi : FixedShapeWhirProof p) : FixedShapeWhirProof p :=
  {pi with stages := pi.stages.modify 1 (fun s =>
    {s with oodWords := s.oodWords.modify 0 (fun x => Goldilocks.ofNat (x.val ^^^ 1))})}

/-- Decode the committed parent from the actual log, flip the left child’s boundary field
`hi`, then bind the modified payload with the original nonce. -/
def flipCommittedChildHi {n : Nat} (env : IvcExtractionContext n) (ro : Spec.Bytes → Spec.Bytes)
    (d : Nat) (s : IvcTreeStatement) (pi : FixedShapeWhirProof env.cfg.params)
    (T : QromQueryTranscript) : Option (FixedShapeWhirProof env.cfg.params) := do
  let some (.parent l r pl pr fold) := extractIvcStepFromTranscript n env.profile ro T d s pi | none
  let w : CommittedIvcNodeWitness env.cfg.params n := .parent {l with hi := l.hi ^^^ 1} r pl pr fold
  let root := ro (nodeCommitmentInput env.profile d s pi.stage0Nonce (NodeWire.node w))
  return {pi with witnessCommitRoot := BitVec.ofNat 448 (decodeNatLeBytes root)}

/-- One decision procedure for the positive execution certificate. Native execution
and kernel reduction can exercise precisely the same Boolean. -/
def realDepth2AcceptsAndExtracts : Bool :=
  realDepth2Run.any fun (s, p, t) =>
    !hasQueryCollision t &&
    verifyConcreteIvcRoot realDepth2Env.profile realDepth2Env.cfg ivcFastXof56 2 s p &&
    (extractMultiDepthQrom realDepth2Env ivcFastXof56 2 t s p).any realDepth2Coverage

theorem realDepth2AcceptsAndExtracts_of_check (checked : realDepth2AcceptsAndExtracts = true) :
    ∃ shards, realDepth2Run = some (realDepth2Stmt, realDepth2IvcProof, realDepth2Transcript) ∧
      hasQueryCollision realDepth2Transcript = false ∧
      verifyConcreteIvcRoot realDepth2Env.profile realDepth2Env.cfg ivcFastXof56
        2 realDepth2Stmt realDepth2IvcProof = true ∧
      extractMultiDepthQrom realDepth2Env ivcFastXof56 2 realDepth2Transcript realDepth2Stmt
        realDepth2IvcProof = some shards ∧ shards.length = 4 ∧
      shards.map ExtractedLeafShard.shardId = [0,1,2,3] ∧
      (shards.map ExtractedLeafShard.quorumCount).sum = 4 ∧
      ∀ sh ∈ shards, ValidQuorumSignatures realDepth2Env.profile ivcFastXof56
        realDepth2Stmt.policyRegistryRoot realDepth2Stmt.message sh := by
  unfold realDepth2AcceptsAndExtracts at checked
  cases run : realDepth2Run with
  | none => simp [run] at checked
  | some result =>
    obtain ⟨s, p, t⟩ := result
    rw [run] at checked
    change ((!hasQueryCollision t && _) && _) = true at checked
    obtain ⟨both, extracted⟩ := Bool.and_eq_true_iff.mp checked
    obtain ⟨nc, verified⟩ := Bool.and_eq_true_iff.mp both
    cases he : extractMultiDepthQrom realDepth2Env ivcFastXof56 2 t s p with
    | none => simp [he] at extracted
    | some shards =>
      rw [he] at extracted
      obtain ⟨len, ids, total⟩ := of_decide_eq_true (show realDepth2Coverage shards = true from extracted)
      refine ⟨shards, ?_⟩
      simp only [realDepth2Stmt, realDepth2IvcProof, realDepth2Transcript, run, Option.map_some,
        Option.getD_some, true_and]
      exact ⟨by simpa using nc, verified, he, len, ids, total,
        extractedQuorums_valid _ (.inl rfl) _ _ _ _ _ _ he⟩

#verify_constructive realDepth2AcceptsAndExtracts_of_check

end Qsag.MultiDepthQrom
end

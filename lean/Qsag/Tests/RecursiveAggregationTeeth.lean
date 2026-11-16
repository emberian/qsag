module
import all Qsag.Math.GoldilocksBase
/-
Fixtures and teeth for the recursive aggregation modules.

A. Two-layer and succinct-outer `Hem` fixtures for
   `Qsag.Protocol.Aggregation.Poseidon2AlgebraicAndRecursiveHem`: two concrete singleton-committee
   shard certificates built by the honest two-stage WHIR prover (`concreteHemShard`), their
   commitment-opening transcripts, the accepted two-shard root under `poseidon2Hash32`
   (`inhabited_verifyHierarchicalHem_two_shards`, `inhabited_transcript_grounded_two_shards`), the
   forged-threshold and replay teeth (`tooth_forged_lower_shard_threshold_rejected`,
   `tooth_concrete_unscoped_shard_replay`), the accepted succinct outer certificate
   (`inhabited_verifySuccinctRecursiveHem`) and its downgrade/tamper tooth
   (`tooth_succinctRecursiveHem_rejects_downgrade_and_tamper`). The examples use the field-based
   signature suite from `Aggregation`, not a claimed secure instantiation of that suite.

B. Recursive tree of `Qsag.Protocol.Aggregation.RecursivePoseidon2WhirSoundness`:
   the header pair `shardId = 0` / `shardId = p` that has one `Poseidon2` preimage and is now split
   by `verifyRecursiveShardHeader` (`tooth_noncanonical_shard_header_collides_and_is_rejected`);
   swapped round messages change the derived challenges
   (`tooth_swapped_round_messages_change_challenge`,
   `tooth_swapped_sumcheck_round_changes_theta`); a leaf whose shard has no quorum is rejected
   although its child-WHIR proof accepts (`tooth_accepting_child_proof_without_quorum_rejected`),
   and the leaf relation has no witness when no committee key has a valid signature
   (`tooth_leaf_relation_requires_a_valid_signature`); the accepted depth-1 tree over the two
   concrete shards (`inhabited_verifyRecursiveHemTree`) with its extraction environments
   (`inhabited_recursive_hem_forgery_or_break`).
-/
public import Qsag.Protocol.Aggregation.Poseidon2AlgebraicAndRecursiveHem
public import Qsag.Protocol.Aggregation.RecursivePoseidon2WhirSoundness
import all Qsag.Protocol.Aggregation.RecursivePoseidon2WhirSoundness
import all Qsag.Oracle.FiatShamir
import all Qsag.Protocol.Aggregation.Poseidon2AlgebraicAndRecursiveHem
import all Qsag.Protocol.Aggregation.Aggregation
import all Qsag.Oracle.Poseidon2
import all Qsag.Oracle.Keccak
import all Qsag.Math.Goldilocks
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

open Aggregation RoundPoly

set_option autoImplicit false

/-! ## A. Two-layer and succinct-outer Hem fixtures (from Poseidon2AlgebraicAndRecursiveHem) -/

/-! ### A.1 Concrete accepting hierarchical certificates and prover transcripts -/

/-- Two distinct singleton committees use the same relation `x^7 = 0`, represented by
    `(seed, root) = (0, 0)` and `(1, 1)`. Both use the honest two-stage WHIR prover.
    This is an inhabitedness example for the field-based signature suite, not a security
    assertion about that suite. The threshold and the actual signer count are both one. -/
def concreteHemShard (second : Bool) : HemShardProof :=
  let seed := if second then Goldilocks.one else Goldilocks.zero
  let sid : List UInt8 := [if second then 1 else 0]
  let msg := shardBoundMessage sid [] []
  let bundle := buildHonestSbox7WhirBundle seed Goldilocks.zero Goldilocks.one msg
  { shardId := sid, threshold := 1, inst := rsSbox7Inst seed seed msg,
    proof := bundle.1, fs := bundle.2.1 }

def concreteHemArith : RowArithmetization := rsSbox7TraceArith Goldilocks.zero Goldilocks.zero

def concreteHemRegistry : List ShardRegistration :=
  [concreteHemShard false, concreteHemShard true].map HemShardProof.registration

def concreteHemRegistryDigest : List UInt8 :=
  poseidon2Hash32 (encodeRegistry concreteHemRegistry)

private theorem concreteHemArith_eq_seed (second : Bool) :
    let seed := if second then Goldilocks.one else Goldilocks.zero
    rsSbox7TraceArith seed (CommRingOps.add (pow7Goldilocks Goldilocks.zero) seed) =
      concreteHemArith := by
  cases second <;>
    (dsimp only [concreteHemArith, rsSbox7TraceArith]
     congr 1)

private theorem concreteSeedRoot_eq (second : Bool) :
    let seed := if second then Goldilocks.one else Goldilocks.zero
    CommRingOps.add (pow7Goldilocks Goldilocks.zero) seed = seed := by
  cases second <;> decide

theorem concreteHemShard_accepts (second : Bool) :
    verifyHemShard concreteHemArith rsSbox7WhirDomain [] [] (concreteHemShard second) = true := by
  have hAcc := (honestSbox7WhirProof_accepts
    (if second then Goldilocks.one else Goldilocks.zero)
    Goldilocks.zero Goldilocks.one
    (shardBoundMessage [if second then 1 else 0] [] [])).1
  rw [concreteHemArith_eq_seed second, concreteSeedRoot_eq second] at hAcc
  have c1 : decide ((concreteHemShard second).inst.message =
      shardBoundMessage (concreteHemShard second).shardId [] []) = true := by
    cases second <;> exact decide_eq_true rfl
  have c2 : decide (1 ≤ (concreteHemShard second).threshold) = true := by
    cases second <;> decide
  have c3 : decide ((concreteHemShard second).threshold ≤
      (concreteHemShard second).inst.committee.length) = true := by
    cases second <;> decide
  have c4 : decide ((concreteHemShard second).threshold ≤
      bitmapPopcountSpec (concreteHemShard second).proof.agg.bitmap) = true := by
    cases second <;> exact decide_eq_true (Nat.le_refl 1)
  unfold verifyHemShard
  rw [c1, c2, c3, c4]
  exact hAcc

theorem concreteHemShard_lawful (second : Bool) :
    concreteHemArith.Lawful rsSbox7WhirDomain (concreteHemShard second).inst := by
  cases second
  · exact rsSbox7TraceArith_lawful Goldilocks.zero Goldilocks.zero (shardBoundMessage [0] [] [])
  · have hLaw := rsSbox7TraceArith_lawful Goldilocks.one Goldilocks.one (shardBoundMessage [1] [] [])
    have hEq : rsSbox7TraceArith Goldilocks.one Goldilocks.one = concreteHemArith := by
      dsimp only [concreteHemArith, rsSbox7TraceArith]
      congr 1
    rwa [hEq] at hLaw

/-- Concrete prover commitment-opening transcript for `concreteHemShard second`. -/
def concreteHemShardTranscript (second : Bool) :
    ShardProverTranscript concreteHemArith rsSbox7WhirDomain :=
  let seed := if second then Goldilocks.one else Goldilocks.zero
  let sid : List UInt8 := [if second then 1 else 0]
  let msg := shardBoundMessage sid [] []
  let bundle := buildHonestSbox7WhirBundle seed Goldilocks.zero Goldilocks.one msg
  { shard := concreteHemShard second
    law := concreteHemShard_lawful second
    transcript := transcriptOfBoundView rsSbox7WhirDomain bundle.2.2 }

theorem concreteHemShardTranscript_accepts (second : Bool) :
    verifyCommittedTableTranscript rsSbox7WhirDomain (concreteHemShard second).proof
      (concreteHemShardTranscript second).transcript = true := by
  have hBound := (honestSbox7WhirProof_accepts
    (if second then Goldilocks.one else Goldilocks.zero)
    Goldilocks.zero Goldilocks.one
    (shardBoundMessage [if second then 1 else 0] [] [])).2
  have hNodup : (rsSbox7WhirDomain.stages.map (·.stageIdx)).Nodup := by decide
  exact verifyCommittedTableTranscript_transcriptOfBoundView rsSbox7WhirDomain _ _ hNodup hBound

private theorem concreteHemCommittee_nodup :
    (hierarchicalCommittee [concreteHemShard false, concreteHemShard true]).Nodup := by
  change [mkSbox7Pk Goldilocks.zero Goldilocks.zero,
    mkSbox7Pk Goldilocks.one Goldilocks.one].Nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.nodup_nil, and_true, not_false_eq_true]
  intro h
  have hs := congrArg PqPublicKey.pkSeed h
  exact (by decide :
    (mkSbox7Pk Goldilocks.zero Goldilocks.zero).pkSeed ≠
      (mkSbox7Pk Goldilocks.one Goldilocks.one).pkSeed) hs

/-- A root certificate with two distinct shard ids, two distinct public keys, and two active
    signers. Its registry commitment is computed by the deployed Poseidon2 hash. -/
theorem inhabited_verifyHierarchicalHem_two_shards :
    verifyHierarchicalHem poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
      concreteHemRegistryDigest [] [] [concreteHemShard false, concreteHemShard true] = true ∧
    verifyHemHierarchyAgainstRegistry concreteHemArith rsSbox7WhirDomain
      concreteHemRegistry [] [] [concreteHemShard false, concreteHemShard true] = true ∧
    hierarchicalClaimedWeight [concreteHemShard false, concreteHemShard true] = 2 ∧
    hierarchicalThresholdSum [concreteHemShard false, concreteHemShard true] = 2 ∧
    registryThresholdSum concreteHemRegistry = 2 := by
  have hIds : (hierarchicalShardIds [concreteHemShard false, concreteHemShard true]).Nodup := by
    decide
  have hKeys : (hierarchicalCommittee [concreteHemShard false, concreteHemShard true]).Nodup :=
    concreteHemCommittee_nodup
  have hall : [concreteHemShard false, concreteHemShard true].all
      (verifyHemShard concreteHemArith rsSbox7WhirDomain [] []) = true := by
    simp only [List.all_cons, List.all_nil, concreteHemShard_accepts, Bool.and_self]
  have hWf : concreteHemRegistry.all ShardRegistration.WellFormed = true := by decide
  have hDig : decide (poseidon2Hash32 (encodeRegistry
      ([concreteHemShard false, concreteHemShard true].map HemShardProof.registration)) =
      concreteHemRegistryDigest) = true := decide_eq_true rfl
  have hRegEq : decide ([concreteHemShard false, concreteHemShard true].map
      HemShardProof.registration = concreteHemRegistry) = true := decide_eq_true rfl
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · unfold verifyHierarchicalHem
    rw [hDig, decide_eq_true hIds, decide_eq_true hKeys, hall]
    rfl
  · unfold verifyHemHierarchyAgainstRegistry
    rw [hWf, hRegEq, decide_eq_true hIds, decide_eq_true hKeys, hall]
    rfl

/-- End-to-end inhabitedness of transcript-grounded hierarchical extraction & query cost accounting:
    two concrete prover transcripts pass `verifyCommittedTableTranscript` with exact sweep cost
    `hierarchyTranscriptQueryCost rsSbox7WhirDomain 2 = 24`. -/
theorem inhabited_transcript_grounded_two_shards :
    let trs := [concreteHemShardTranscript false, concreteHemShardTranscript true]
    (∀ t ∈ trs, verifyCommittedTableTranscript rsSbox7WhirDomain t.shard.proof t.transcript = true) ∧
    verifyHierarchicalHem poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
      concreteHemRegistryDigest [] [] (trs.map (·.shard)) = true ∧
    hierarchySweepOpeningCount trs = 24 ∧
    hierarchyTranscriptQueryCost rsSbox7WhirDomain trs.length = 24 := by
  intro trs
  have hAllTr : ∀ t ∈ trs,
      verifyCommittedTableTranscript rsSbox7WhirDomain t.shard.proof t.transcript = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact concreteHemShardTranscript_accepts false
    · rcases List.mem_cons.mp ht' with rfl | hNil
      · exact concreteHemShardTranscript_accepts true
      · cases hNil
  have hVer : verifyHierarchicalHem poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
      concreteHemRegistryDigest [] [] (trs.map (·.shard)) = true :=
    inhabited_verifyHierarchicalHem_two_shards.1
  have hF := verifyHierarchicalHem_facts hVer
  have hCostEq : hierarchySweepOpeningCount trs =
      hierarchyTranscriptQueryCost rsSbox7WhirDomain trs.length :=
    hierarchySweepOpeningCount_eq_queryCost trs (fun t ht =>
      ⟨hF.2.2.2 t.shard (List.mem_map.mpr ⟨t, ht, rfl⟩), hAllTr t ht⟩)
  have hQuery24 : hierarchyTranscriptQueryCost rsSbox7WhirDomain trs.length = 24 := by decide
  exact ⟨hAllTr, hVer, hCostEq.trans hQuery24, hQuery24⟩

/-- Kernel-reducible UTF-8 bytes of `"QSAG.PQ.SUITE.SBOX7/v1"` for concrete Poseidon2 evaluation. -/
def concretePoseidonSuiteTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2e, 0x50, 0x51, 0x2e, 0x53, 0x55, 0x49, 0x54,
   0x45, 0x2e, 0x53, 0x42, 0x4f, 0x58, 0x37, 0x2f, 0x76, 0x31]

def concreteTwoKeyCommittee : List PqPublicKey :=
  [mkSbox7Pk Goldilocks.zero Goldilocks.zero, mkSbox7Pk Goldilocks.one Goldilocks.one]

def concreteTwoKeyRegistry : List ShardRegistration :=
  [{ shardId := [0]
     threshold := 2
     suiteId := concretePoseidonSuiteTag
     params := sbox7Params
     committee := concreteTwoKeyCommittee }]

def concreteTwoKeyRegistryDigest : List UInt8 :=
  poseidon2Hash32 (encodeRegistry concreteTwoKeyRegistry)

def concreteLoweredTwoKeyShard : HemShardProof :=
  let base := concreteHemShard false
  { shardId := [0]
    threshold := 1
    inst := { rsSbox7Inst Goldilocks.zero Goldilocks.zero (shardBoundMessage [0] [] []) with
              suite := { sbox7FieldSuite with suiteId := concretePoseidonSuiteTag }
              committee := concreteTwoKeyCommittee }
    proof := base.proof
    fs := base.fs }

set_option maxRecDepth 16384 in
/-- `#tooth` **Forged Lower Shard Threshold Rejected (`tooth_forged_lower_shard_threshold_rejected`)**:
    (a) **General security refutation**: for any hash `H`, registered policy `registry`, and
        submitted `shards`, if shard `i` lowers `threshold < (registry[i]).threshold` under an
        unchanged `registryDigest = H (encodeRegistry registry)`, then
        `verifyHemHierarchyAgainstRegistry` unconditionally returns `false`, and either
        `verifyHierarchicalHem` returns `false` or `forgedLowerThreshold_rejected_or_collision`
        constructively extracts a `HashCollisionWitness H`.
    (b) **Concrete `poseidon2Hash32` witnesses**:
        1. Lowering shard `0`'s threshold from `1` to `0` on the accepted two-shard Poseidon2
           hierarchy flips `verifyHierarchicalHem` from `true` to `false`.
        2. Lowering a 2-key committee's threshold from `2` to `1` (while keeping `1 ≤ 1 ≤ 2`
           well-formed and keeping `shardId`, `suiteId`, `params`, and `committee` identical)
           changes the concrete `poseidon2Hash32` registry digest and causes
           `verifyHierarchicalHem` to evaluate to `false`. -/
theorem tooth_forged_lower_shard_threshold_rejected :
    (∀ (H : Hash) (arith : RowArithmetization) (dom : WhirDomain)
       (registryDigest epochFloor msg : List UInt8) (registry : List ShardRegistration)
       (_hReg : H (encodeRegistry registry) = registryDigest)
       (shards : List HemShardProof) (i : Nat)
       (hiS : i < shards.length) (hiR : i < registry.length),
      (shards[i]'hiS).threshold < (registry[i]'hiR).threshold →
      verifyHemHierarchyAgainstRegistry arith dom registry epochFloor msg shards = false ∧
      (verifyHierarchicalHem H arith dom registryDigest epochFloor msg shards = false ∨
       Nonempty (HashCollisionWitness H))) ∧
    verifyHierarchicalHem poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
      concreteHemRegistryDigest [] []
      [{ concreteHemShard false with threshold := 0 }, concreteHemShard true] = false ∧
    concreteLoweredTwoKeyShard.registration.WellFormed = true ∧
    poseidon2Hash32 (encodeRegistry [concreteLoweredTwoKeyShard.registration]) ≠
      concreteTwoKeyRegistryDigest ∧
    verifyHierarchicalHem poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
      concreteTwoKeyRegistryDigest [] [] [concreteLoweredTwoKeyShard] = false := by
  have hDigNe :
      poseidon2Hash32 (encodeRegistry [concreteLoweredTwoKeyShard.registration]) ≠
        concreteTwoKeyRegistryDigest := by
    unfold concreteTwoKeyRegistryDigest
    decide
  refine ⟨?_, ?_, by decide, hDigNe, ?_⟩
  · intro H arith dom registryDigest epochFloor msg registry hReg shards i hiS hiR hLower
    match forgedLowerThreshold_rejected_or_collision H arith dom registryDigest epochFloor msg
        registry hReg shards i hiS hiR hLower with
    | .inl ⟨hHierFalse, hDirectFalse⟩ => exact ⟨hDirectFalse, .inl hHierFalse⟩
    | .inr col =>
      have hNe : shards.map HemShardProof.registration ≠ registry := fun hEq => by
        have hAt : (shards.map HemShardProof.registration)[i]? = registry[i]? :=
          congrArg (·[i]?) hEq
        rw [List.getElem?_map, List.getElem?_eq_getElem hiS, List.getElem?_eq_getElem hiR,
            Option.map_some, Option.some.injEq] at hAt
        have hThr : (shards[i]'hiS).threshold = (registry[i]'hiR).threshold :=
          congrArg ShardRegistration.threshold hAt
        exact absurd (hThr ▸ hLower) (Nat.lt_irrefl _)
      refine ⟨?_, .inr ⟨col⟩⟩
      unfold verifyHemHierarchyAgainstRegistry
      simp [decide_eq_false hNe]
  · apply Bool.eq_false_iff.mpr
    intro hAcc
    have hAll := (verifyHierarchicalHem_facts hAcc).2.2.2
    have h0 := hAll { concreteHemShard false with threshold := 0 } (List.mem_cons_self ..)
    have hGe1 := (verifyHemShard_facts h0).2.1
    simp at hGe1
  · unfold verifyHierarchicalHem
    have hDigNeMap :
        poseidon2Hash32 (encodeRegistry ([concreteLoweredTwoKeyShard].map
          HemShardProof.registration)) ≠ concreteTwoKeyRegistryDigest := hDigNe
    rw [decide_eq_false hDigNeMap]
    rfl

/-- Unconditional replay: the same actual accepting one-signer certificate is counted twice
    by the unscoped verifier, while the scoped root rejects it. No accepted-shard premise. -/
theorem tooth_concrete_unscoped_shard_replay :
    verifyHierarchicalHemUnscoped concreteHemArith rsSbox7WhirDomain
      [concreteHemShard false, concreteHemShard false] = true ∧
    hierarchicalClaimedWeight [concreteHemShard false, concreteHemShard false] = 2 ∧
    bitmapPopcountSpec (concreteHemShard false).proof.agg.bitmap = 1 ∧
    (∀ q ∈ hierarchicalActiveSlots [concreteHemShard false, concreteHemShard false],
      q ∈ shardActiveSlots (concreteHemShard false)) ∧
    verifyHierarchicalHem poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
      concreteHemRegistryDigest [] [] [concreteHemShard false, concreteHemShard false] = false := by
  have h := tooth_unscoped_shard_id_allows_quorum_replay_multiplication
    poseidon2Hash32 concreteHemArith rsSbox7WhirDomain concreteHemRegistryDigest [] []
    (concreteHemShard false) 2 (by decide) (concreteHemShard_accepts false)
  exact ⟨h.1, rfl, rfl, h.2.2.2.1, h.2.2.2.2⟩

/-! ### A.2 Concrete succinct outer certificate -/

def concreteSuccinctOuterHeaders : List ShardCompressedHeader :=
  [concreteHemShard false, concreteHemShard true].map (shardToCompressedHeader (fun _ => [0x01]))

def concreteOuterMsg : List UInt8 :=
  succinctOuterBoundMessage concreteHemRegistryDigest [] []
    (poseidon2Hash32 (encodeCompressedHeaderChain concreteSuccinctOuterHeaders))

private def concreteOuterBundle :=
  buildHonestSbox7WhirBundle Goldilocks.zero Goldilocks.zero Goldilocks.one concreteOuterMsg

/-- Concrete accepting `SuccinctOuterHemCertificate` over the two `concreteHemShard` shards, using
    `poseidon2Hash32` and the honest `bciksJohnsonQrom128` WHIR prover. -/
def concreteSuccinctOuterCert : SuccinctOuterHemCertificate :=
  { headers := concreteSuccinctOuterHeaders
    outerInst := rsSbox7Inst Goldilocks.zero Goldilocks.zero concreteOuterMsg
    outerProof := concreteOuterBundle.1
    outerFs := concreteOuterBundle.2.1 }

theorem inhabited_verifySuccinctRecursiveHem :
    verifySuccinctRecursiveHem poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
      concreteHemRegistryDigest [] [] concreteSuccinctOuterCert = true ∧
    concreteSuccinctOuterCert.outerProof.agg.regime = .bciksJohnsonQrom128 := by
  have hIds : (concreteSuccinctOuterHeaders.map (·.shardId)).Nodup := by
    rw [concreteSuccinctOuterHeaders, map_sid_of_headers]
    decide
  have hCom : (headerCommitteeFlat concreteSuccinctOuterHeaders).Nodup := by
    rw [concreteSuccinctOuterHeaders, flat_com_of_headers]
    exact concreteHemCommittee_nodup
  have hLen : 1 ≤ concreteSuccinctOuterHeaders.length :=
    Nat.le_succ 1
  have hHdrQ : ∀ second : Bool,
      verifyHeaderQuorum (shardToCompressedHeader (fun _ => [0x01]) (concreteHemShard second)) = true := by
    intro second
    have c1 : decide (1 ≤ (concreteHemShard second).threshold) = true := by
      cases second <;> decide
    have c2 : decide ((concreteHemShard second).threshold ≤
        (concreteHemShard second).inst.committee.length) = true := by
      cases second <;> decide
    have c3 : decide ((concreteHemShard second).threshold ≤
        bitmapPopcountSpec (concreteHemShard second).proof.agg.bitmap) = true := by
      cases second <;> exact decide_eq_true (Nat.le_refl 1)
    unfold verifyHeaderQuorum shardToCompressedHeader
    dsimp only
    rw [c1, c2, c3]
    rfl
  have hQ : concreteSuccinctOuterHeaders.all verifyHeaderQuorum = true := by
    unfold concreteSuccinctOuterHeaders
    simp only [List.map, List.all_cons, List.all_nil, hHdrQ, Bool.and_self]
  have hAcc : verifySuccinctAggregate concreteHemArith rsSbox7WhirDomain
      (rsSbox7Inst Goldilocks.zero Goldilocks.zero concreteOuterMsg)
      concreteOuterBundle.1 concreteOuterBundle.2.1 = true := by
    have hRaw := (honestSbox7WhirProof_accepts Goldilocks.zero Goldilocks.zero Goldilocks.one concreteOuterMsg).1
    have hz : CommRingOps.add (pow7Goldilocks Goldilocks.zero) Goldilocks.zero = Goldilocks.zero := by decide
    have hArithEq : rsSbox7TraceArith Goldilocks.zero
        (CommRingOps.add (pow7Goldilocks Goldilocks.zero) Goldilocks.zero) = concreteHemArith := by
      rw [hz]; rfl
    rw [hArithEq, hz] at hRaw
    exact hRaw
  have hMapReg : concreteSuccinctOuterHeaders.map ShardCompressedHeader.registration =
      concreteHemRegistry :=
    map_reg_of_headers (fun _ => [0x01]) [concreteHemShard false, concreteHemShard true]
  have hDig : decide (poseidon2Hash32 (encodeRegistry
      (concreteSuccinctOuterHeaders.map ShardCompressedHeader.registration)) =
      concreteHemRegistryDigest) = true := by
    rw [hMapReg]
    exact decide_eq_true rfl
  have hPrfReg : ∀ m : List UInt8,
      (buildHonestSbox7WhirBundle Goldilocks.zero Goldilocks.zero Goldilocks.one m).1.agg.regime =
        .bciksJohnsonQrom128 := fun _ => rfl
  have hRegEq : concreteSuccinctOuterCert.outerProof.agg.regime = .bciksJohnsonQrom128 :=
    hPrfReg concreteOuterMsg
  have hInstReg : decide ((rsSbox7Inst Goldilocks.zero Goldilocks.zero concreteOuterMsg).regime =
      .bciksJohnsonQrom128) = true :=
    decide_eq_true rfl
  have hPrfRegDec : decide (concreteOuterBundle.1.agg.regime = .bciksJohnsonQrom128) = true :=
    decide_eq_true (hPrfReg concreteOuterMsg)
  have hMsgEq : decide ((rsSbox7Inst Goldilocks.zero Goldilocks.zero concreteOuterMsg).message =
      succinctOuterBoundMessage concreteHemRegistryDigest [] []
        (poseidon2Hash32 (encodeCompressedHeaderChain concreteSuccinctOuterHeaders))) = true :=
    decide_eq_true rfl
  refine ⟨?_, hRegEq⟩
  unfold verifySuccinctRecursiveHem
  change (decide (1 ≤ concreteSuccinctOuterHeaders.length) &&
    decide (poseidon2Hash32 (encodeRegistry (concreteSuccinctOuterHeaders.map ShardCompressedHeader.registration)) =
      concreteHemRegistryDigest) &&
    decide ((concreteSuccinctOuterHeaders.map (·.shardId)).Nodup) &&
    decide ((headerCommitteeFlat concreteSuccinctOuterHeaders).Nodup) &&
    concreteSuccinctOuterHeaders.all verifyHeaderQuorum &&
    decide ((rsSbox7Inst Goldilocks.zero Goldilocks.zero concreteOuterMsg).regime = .bciksJohnsonQrom128) &&
    decide (concreteOuterBundle.1.agg.regime = .bciksJohnsonQrom128) &&
    decide ((rsSbox7Inst Goldilocks.zero Goldilocks.zero concreteOuterMsg).message =
      succinctOuterBoundMessage concreteHemRegistryDigest [] []
        (poseidon2Hash32 (encodeCompressedHeaderChain concreteSuccinctOuterHeaders))) &&
    verifySuccinctAggregate concreteHemArith rsSbox7WhirDomain
      (rsSbox7Inst Goldilocks.zero Goldilocks.zero concreteOuterMsg)
      concreteOuterBundle.1 concreteOuterBundle.2.1) = true
  rw [decide_eq_true hLen, hDig, decide_eq_true hIds, decide_eq_true hCom, hQ,
      hInstReg, hPrfRegDec, hMsgEq, hAcc]
  rfl

/-- `#tooth` **Succinct Outer Recursive Regime Downgrade & Header-Chain Tamper Rejection**:
    1. Downgrading `outerInst.regime` to `.bciksJohnsonClassical128` causes `verifySuccinctRecursiveHem`
       to return `false`.
    2. Tampering `headers` to any `headers' ≠ cert.headers` on an accepting certificate forces either
       `verifySuccinctRecursiveHem ... { cert with headers := headers' } = false` or an explicit
       `HashCollisionWitness H` on `encodeCompressedHeaderChain`.
    3. On concrete `concreteSuccinctOuterCert` (with injective transcript hash `fun bs => bs`),
       mutating `childProofDigest` from `[0x01]` to `[0xFF]` causes `verifySuccinctRecursiveHem` to
       evaluate to `false`. -/
theorem tooth_succinctRecursiveHem_rejects_downgrade_and_tamper :
    (∀ H outerArith outerDom regDig ep msg (cert : SuccinctOuterHemCertificate),
      cert.outerInst.regime = .bciksJohnsonClassical128 →
      verifySuccinctRecursiveHem H outerArith outerDom regDig ep msg cert = false) ∧
    (∀ H outerArith outerDom regDig ep msg (cert : SuccinctOuterHemCertificate)
        (headers' : List ShardCompressedHeader),
      verifySuccinctRecursiveHem H outerArith outerDom regDig ep msg cert = true →
      headers' ≠ cert.headers →
      (HashCollisionWitness H → False) →
      verifySuccinctRecursiveHem H outerArith outerDom regDig ep msg
        { cert with headers := headers' } = false) ∧
    verifySuccinctRecursiveHem (fun bs => bs) concreteHemArith rsSbox7WhirDomain
      (encodeRegistry concreteHemRegistry) [] []
      { concreteSuccinctOuterCert with
        headers := concreteSuccinctOuterHeaders.map
          (fun h => { h with childProofDigest := [0xFF] })
        outerInst := rsSbox7Inst Goldilocks.zero Goldilocks.zero
          (succinctOuterBoundMessage (encodeRegistry concreteHemRegistry) [] []
            (encodeCompressedHeaderChain concreteSuccinctOuterHeaders)) } = false := by
  refine ⟨?_, ?_, ?_⟩
  · intro H outerArith outerDom regDig ep msg cert hCl
    apply Bool.eq_false_iff.mpr
    intro hAcc
    have hQr := (verifySuccinctRecursiveHem_facts hAcc).2.2.2.2.2.1
    rw [hCl] at hQr
    cases hQr
  · intro H outerArith outerDom regDig ep msg cert headers' hAcc hNe hNoCol
    apply Bool.eq_false_iff.mpr
    intro hAcc'
    have hMsg := (verifySuccinctRecursiveHem_facts hAcc).2.2.2.2.2.2.2.1
    have hMsg' := (verifySuccinctRecursiveHem_facts hAcc').2.2.2.2.2.2.2.1
    dsimp only at hMsg'
    rw [hMsg] at hMsg'
    have hDigEq := (succinctOuterBoundMessage_injective hMsg').2.2.2
    have hEncNe : encodeCompressedHeaderChain headers' ≠ encodeCompressedHeaderChain cert.headers := by
      intro hEncEq
      exact hNe (encodeCompressedHeaderChain_injective hEncEq)
    exact hNoCol ⟨encodeCompressedHeaderChain headers', encodeCompressedHeaderChain cert.headers,
      hEncNe, hDigEq.symm⟩
  · apply Bool.eq_false_iff.mpr
    intro hAcc'
    have hMsg' := (verifySuccinctRecursiveHem_facts hAcc').2.2.2.2.2.2.2.1
    dsimp only [rsSbox7Inst] at hMsg'
    have hEncEq := (succinctOuterBoundMessage_injective hMsg').2.2.2
    have hHdrEq := encodeCompressedHeaderChain_injective hEncEq
    have hDflt := shardToCompressedHeader (fun _ => [0x01]) (concreteHemShard false)
    have hHead := congrArg (fun hs : List ShardCompressedHeader => (hs.headD hDflt).childProofDigest) hHdrEq
    have hL : (concreteSuccinctOuterHeaders.headD hDflt).childProofDigest = [0x01] := rfl
    have hR : ((concreteSuccinctOuterHeaders.map
        (fun h => { h with childProofDigest := [0xFF] })).headD hDflt).childProofDigest = [0xFF] := rfl
    rw [hL, hR] at hHead
    exact absurd hHead (by decide)

/-! ## B. Recursive tree: header canonicality, transcript order, leaf relation -/

/-! ### B.1 Header canonicality (the `0` / `p` pair) -/

def headerShardZero : RecursiveShardHeader :=
  { shardId := 0, threshold := 2, committeeSize := 3, validCount := 2,
    publicDigest := ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩ }

def headerShardP : RecursiveShardHeader :=
  { shardId := goldilocksPrime, threshold := 2, committeeSize := 3, validCount := 2,
    publicDigest := ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩ }

/-- The two headers differ, reduce to one `Poseidon2` preimage (hence one digest), and only the
    canonical one passes `verifyRecursiveShardHeader`: without the `shardId < p` check the tree
    would carry two distinct shard ids under one digest. -/
theorem tooth_noncanonical_shard_header_collides_and_is_rejected :
    ∃ h1 h2 : RecursiveShardHeader,
      ¬ (h1 = h2) ∧
      leafShardHeaderPreimage h1 = leafShardHeaderPreimage h2 ∧
      hashLeafShardHeader h1 = hashLeafShardHeader h2 ∧
      verifyRecursiveShardHeader h1 = true ∧
      verifyRecursiveShardHeader h2 = false := by
  have hPre : leafShardHeaderPreimage headerShardZero = leafShardHeaderPreimage headerShardP := by
    decide
  refine ⟨headerShardZero, headerShardP, by decide, hPre, ?_, by decide, by decide⟩
  unfold hashLeafShardHeader
  rw [hPre]

/-- Positive instance of `leafShardHeaderPreimage_injective`: two canonical headers. -/
theorem inhabited_canonical_shard_headers :
    verifyRecursiveShardHeader headerShardZero = true ∧
    verifyRecursiveShardHeader { headerShardZero with shardId := 1 } = true ∧
    ¬ (leafShardHeaderPreimage headerShardZero =
      leafShardHeaderPreimage { headerShardZero with shardId := 1 }) := by
  refine ⟨by decide, by decide, by decide⟩

/-! ### B.2 Transcript order -/

def swapRoundA : FsRound := ⟨Goldilocks.ofNat 10, [Goldilocks.ofNat 1], [Goldilocks.ofNat 11]⟩
def swapRoundB : FsRound := ⟨Goldilocks.ofNat 10, [Goldilocks.ofNat 2], [Goldilocks.ofNat 11]⟩

/-- Swapping two round messages changes the challenge derived after them. -/
theorem tooth_swapped_round_messages_change_challenge :
    ¬ (fsDeriveChallenges [swapRoundA, swapRoundB] = fsDeriveChallenges [swapRoundB, swapRoundA]) := by
  decide +kernel

def swapPolyA : List QuarticGoldilocks :=
  [⟨⟨Goldilocks.one, Goldilocks.zero⟩, ⟨Goldilocks.zero, Goldilocks.zero⟩⟩]

def swapPolyB : List QuarticGoldilocks :=
  [⟨⟨Goldilocks.zero, Goldilocks.zero⟩, ⟨Goldilocks.zero, Goldilocks.zero⟩⟩]

def swapZeroLane : Lane4 := ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩

def swapZeroExt : QuarticGoldilocks :=
  ⟨⟨Goldilocks.zero, Goldilocks.zero⟩, ⟨Goldilocks.zero, Goldilocks.zero⟩⟩

set_option maxRecDepth 1000000 in
/-- In the child verifier, exchanging two sumcheck round polynomials changes the fold challenge
    `theta` squeezed after them: the round messages are absorbed, in order. -/
theorem tooth_swapped_sumcheck_round_changes_theta :
    ¬ ((childWhirChallenges swapZeroLane 1 0 swapZeroLane swapZeroExt swapZeroLane
          [swapPolyA, swapPolyB] []).theta =
       (childWhirChallenges swapZeroLane 1 0 swapZeroLane swapZeroExt swapZeroLane
          [swapPolyB, swapPolyA] []).theta) := by
  decide +kernel

/-- The frame encoding separates a message from its split: one frame `[1, 2]` and two frames
    `[1]`, `[2]` under the same tag have different block encodings. -/
theorem tooth_frame_boundary_is_encoded :
    ¬ (fsTranscriptBlocks [⟨Goldilocks.ofNat 10, [Goldilocks.ofNat 1, Goldilocks.ofNat 2]⟩] =
       fsTranscriptBlocks [⟨Goldilocks.ofNat 10, [Goldilocks.ofNat 1]⟩,
         ⟨Goldilocks.ofNat 10, [Goldilocks.ofNat 2]⟩]) := by
  decide

/-! ### B.3 Leaf relation -/

private theorem filter_false_nil {α : Type} : ∀ l : List α, l.filter (fun _ => false) = []
  | [] => rfl
  | _ :: l => filter_false_nil l

/-- The leaf relation has no witness for a shard with `threshold ≥ 1` none of whose committee keys
    has a signature accepted by `verifyPqHashSig` on the shard-bound message. -/
theorem tooth_leaf_relation_requires_a_valid_signature (epochFloor msg : List UInt8)
    (registry : List ShardRegistration) (s : HemShardProof) (hThr : 1 ≤ s.threshold)
    (hNoSig : ∀ pk ∈ s.inst.committee, ∀ sig : PqHashSig,
      verifyPqHashSig s.inst.suite s.inst.params pk
        (shardBoundMessage s.shardId epochFloor msg) sig = false) :
    LeafShardQuorumWitness epochFloor msg registry s → False := by
  intro w
  have hFew : (s.inst.committee.filter (fun _ => false)).length < s.threshold := by
    rw [filter_false_nil]
    exact hThr
  obtain ⟨q, hq, _⟩ := w.exists_sig_not (fun _ => false) hFew
  obtain ⟨hPk, hValid⟩ := w.sig_valid q hq
  rw [hNoSig q.slot.pk hPk q.sig] at hValid
  exact absurd hValid Bool.false_ne_true

/-- `concreteHemShard false` with its threshold raised above its single signer. -/
def subQuorumHemShard : HemShardProof := { concreteHemShard false with threshold := 2 }

def subQuorumRecursiveLeaf : RecursiveHemLeafCert :=
  { header := mkLeafShardHeader concreteHemRegistryDigest [] [] 0 subQuorumHemShard
    shard := subQuorumHemShard
    leafProof := mkHonestChildWhirWitness
      (hashLeafShardHeader (mkLeafShardHeader concreteHemRegistryDigest [] [] 0 subQuorumHemShard))
      swapZeroLane }

/-- A leaf whose shard has no quorum is rejected although its child-WHIR proof on the header
    digest accepts: the child proof carries no signature statement. -/
theorem tooth_accepting_child_proof_without_quorum_rejected :
    ∃ leaf : RecursiveHemLeafCert,
      ChildWhirCircuitAccepts (hashLeafShardHeader leaf.header) leaf.leafProof = true ∧
      verifyRecursiveHemTree poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
        concreteHemRegistryDigest [] [] 2 0 leaf = false := by
  refine ⟨subQuorumRecursiveLeaf, mkHonestChildWhirWitness_accepts _ _, ?_⟩
  apply recursive_tree_rejects_leaf_with_failing_shard
  have hQ : decide (subQuorumRecursiveLeaf.shard.threshold ≤
      bitmapPopcountSpec subQuorumRecursiveLeaf.shard.proof.agg.bitmap) = false := by rfl
  unfold verifyHemShard
  rw [hQ, Bool.and_false, Bool.false_and]

/-! ### B.4 Accepted depth-1 tree over the two concrete shards -/

def concreteRecursiveLeaf (b : Bool) : RecursiveHemLeafCert :=
  { header := mkLeafShardHeader concreteHemRegistryDigest [] [] (if b then 1 else 0)
      (concreteHemShard b)
    shard := concreteHemShard b
    leafProof := mkHonestChildWhirWitness
      (hashLeafShardHeader (mkLeafShardHeader concreteHemRegistryDigest [] []
        (if b then 1 else 0) (concreteHemShard b))) swapZeroLane }

theorem concreteRecursiveLeaf_header_valid (b : Bool) :
    verifyRecursiveShardHeader (concreteRecursiveLeaf b).header = true := by
  have hThr : (concreteHemShard b).threshold = 1 := by cases b <;> rfl
  have hCom : (concreteHemShard b).inst.committee.length = 1 := by cases b <;> rfl
  have hPop : bitmapPopcountSpec (concreteHemShard b).proof.agg.bitmap = 1 := by cases b <;> rfl
  unfold verifyRecursiveShardHeader concreteRecursiveLeaf mkLeafShardHeader
  dsimp only
  rw [hThr, hCom, hPop]
  cases b <;> decide

theorem concreteRecursiveLeaf_binds (b : Bool) :
    leafHeaderBindsShard concreteHemRegistryDigest [] [] (concreteRecursiveLeaf b).header
      (concreteRecursiveLeaf b).shard = true :=
  leafHeaderBindsShard_mk concreteHemRegistryDigest [] [] (if b then 1 else 0) (concreteHemShard b)
    (by cases b <;> rfl)

def concreteDepth1Agg : RecursiveHemAggregate 1 :=
  ({ summaryDigest := poseidon2SummaryHash 1 2
       [hashLeafShardHeader (concreteRecursiveLeaf false).header,
        hashLeafShardHeader (concreteRecursiveLeaf true).header]
     outerProof := mkHonestChildWhirWitness
       (poseidon2SummaryHash 1 2
         [hashLeafShardHeader (concreteRecursiveLeaf false).header,
          hashLeafShardHeader (concreteRecursiveLeaf true).header]) swapZeroLane
     children := [concreteRecursiveLeaf false, concreteRecursiveLeaf true] } :
    RecursiveHemOuterCert (RecursiveHemAggregate 0))

/-- The depth-1, fan-in-2 tree over the two concrete shard certificates is accepted against the
    registry commitment under `poseidon2Hash32`. -/
theorem inhabited_verifyRecursiveHemTree :
    verifyRecursiveHemTree poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
      concreteHemRegistryDigest [] [] 2 1 concreteDepth1Agg = true :=
  verifyRecursiveHemTree_depth1_pair poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
    concreteHemRegistryDigest [] [] (concreteRecursiveLeaf false) (concreteRecursiveLeaf true) _
    (concreteRecursiveLeaf_header_valid false) (concreteRecursiveLeaf_header_valid true)
    (concreteRecursiveLeaf_binds false) (concreteRecursiveLeaf_binds true)
    (mkHonestChildWhirWitness_accepts _ _) (mkHonestChildWhirWitness_accepts _ _)
    (mkHonestChildWhirWitness_accepts _ _)
    inhabited_verifyHierarchicalHem_two_shards.1

/-- Extraction environment of a concrete shard: the tables of its verified opening transcript. -/
def concreteHemShardEnv (b : Bool) : HemShardEnv concreteHemArith rsSbox7WhirDomain :=
  { shard := concreteHemShard b
    law := concreteHemShard_lawful b
    view := reconstructSuccinctView rsSbox7WhirDomain (concreteHemShardTranscript b).transcript
    bound := reconstructSuccinctView_stagesBound rsSbox7WhirDomain (concreteHemShard b).proof
      (concreteHemShardTranscript b).transcript (concreteHemShardTranscript_accepts b) }

/-- Every hypothesis of `recursive_hem_false_statement_yields_forgery_or_break` holds for the
    concrete tree with the empty signing log, and its conclusion follows. -/
theorem inhabited_recursive_hem_forgery_or_break :
    (∃ (s : HemShardProof) (pk : PqPublicKey) (sig : PqHashSig),
      s ∈ recursiveHemLeafShards 1 concreteDepth1Agg ∧
      s.registration ∈ concreteHemRegistry ∧
      pk ∈ s.inst.committee ∧
      (fun (_ : PqPublicKey) (_ : List UInt8) => false) pk (shardBoundMessage s.shardId [] []) = false ∧
      verifyPqHashSig s.inst.suite s.inst.params pk (shardBoundMessage s.shardId [] []) sig = true) ∨
    Nonempty (HemHierarchyBreak poseidon2Hash32 concreteHemArith rsSbox7WhirDomain
      [concreteHemShardEnv false, concreteHemShardEnv true]) := by
  refine recursive_hem_false_statement_yields_forgery_or_break poseidon2Hash32 concreteHemArith
    rsSbox7WhirDomain concreteHemRegistryDigest [] [] concreteHemRegistry rfl 2 1 concreteDepth1Agg
    [concreteHemShardEnv false, concreteHemShardEnv true] rfl inhabited_verifyRecursiveHemTree
    (fun _ _ => false) ⟨concreteHemShard false, List.mem_cons_self .., ?_⟩
  show ((concreteHemShard false).inst.committee.filter (fun _ => false)).length <
    (concreteHemShard false).threshold
  rw [filter_false_nil]
  exact Nat.zero_lt_one

#verify_constructive
  Qsag.concreteHemShard_accepts
  Qsag.concreteHemShard_lawful
  Qsag.concreteHemShardTranscript_accepts
  Qsag.inhabited_verifyHierarchicalHem_two_shards
  Qsag.inhabited_transcript_grounded_two_shards
  Qsag.tooth_forged_lower_shard_threshold_rejected
  Qsag.tooth_concrete_unscoped_shard_replay
  Qsag.inhabited_verifySuccinctRecursiveHem
  Qsag.tooth_succinctRecursiveHem_rejects_downgrade_and_tamper
  Qsag.tooth_noncanonical_shard_header_collides_and_is_rejected
  Qsag.inhabited_canonical_shard_headers
  Qsag.tooth_swapped_round_messages_change_challenge
  Qsag.tooth_swapped_sumcheck_round_changes_theta
  Qsag.tooth_frame_boundary_is_encoded
  Qsag.tooth_leaf_relation_requires_a_valid_signature
  Qsag.tooth_accepting_child_proof_without_quorum_rejected
  Qsag.inhabited_verifyRecursiveHemTree
  Qsag.inhabited_recursive_hem_forgery_or_break

#tooth_pair Qsag.leafShardHeaderPreimage_injective vs Qsag.tooth_noncanonical_shard_header_collides_and_is_rejected
#tooth_pair Qsag.childWhirTranscript_challenge vs Qsag.tooth_swapped_round_messages_change_challenge
#tooth_pair Qsag.fsTranscriptBlocks_injective vs Qsag.tooth_frame_boundary_is_encoded
#tooth_pair Qsag.inhabited_verifyRecursiveHemTree vs Qsag.tooth_accepting_child_proof_without_quorum_rejected

end Qsag
end

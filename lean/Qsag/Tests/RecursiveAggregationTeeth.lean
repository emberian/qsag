module
public import Qsag.Math.GoldilocksBase
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
public import Qsag.Oracle.FiatShamir
public import Qsag.Protocol.Aggregation.Aggregation
public import Qsag.Oracle.Poseidon2
public import Qsag.Oracle.Keccak
public import Qsag.Math.Goldilocks
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

open Aggregation RoundPoly

set_option autoImplicit false

/-! ## Where the fixtures live

The fixtures and teeth described in the header evaluate sealed definitions (`verifyHemShard`,
the Sbox7 WHIR prover, the `Poseidon2` transcript sponge), so they are proved next to those
definitions and this module audits and pairs them:

* section A (`concreteHemShard` … `tooth_succinctRecursiveHem_rejects_downgrade_and_tamper`) in
  `Protocol/Aggregation/Poseidon2AlgebraicAndRecursiveHem`;
* section B (`headerShardZero` … `inhabited_recursive_hem_forgery_or_break`) in
  `Protocol/Aggregation/RecursivePoseidon2WhirSoundness`;
* the concrete `Poseidon2` evaluations they rest on are KATs in `Oracle/Poseidon2`. -/

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

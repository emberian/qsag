module
public import Qsag.Protocol.Aggregation.Aggregation
public import Qsag.Protocol.Aggregation.HemInterpolation
public import Qsag.Protocol.Aggregation.SuccinctAggregationIop
public import Qsag.Oracle.Qrom
public import Qsag.Math.GoldilocksBase
public import Qsag.Oracle.Keccak

public import Qsag.Protocol.Aggregation.ComposedQsAgAndMergeSecurity
public import Qsag.Protocol.Aggregation.CrossProtocolAndDualOracleComposition
public import Qsag.Math.Goldilocks
public import Qsag.Math.GoldilocksEncoding
public import Qsag.Math.QuinticExt5
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.AggregationParityTeeth
set_option autoImplicit false
attribute [-instance] Fin.instLinearOrderPackage UInt8.instLawfulEqOrd


/-- Domain labels for frontier signatures, HD budgets, policy and selective disclosure. -/
theorem inhabited_current_labels :
    (CrossProtocol.auditedLabelsOf "qsag-fts").contains "QSAG.FTS.HMSG.V1" = true ∧
    (CrossProtocol.auditedLabelsOf "qsag-hd").contains "QSAG.HD.QUERY_BUDGET.V4" = true ∧
    (CrossProtocol.auditedLabelsOf "qsag-policy").contains "QSAG.POLICY.DURABLE_LEDGER.V6" = true ∧
    (CrossProtocol.auditedLabelsOf "qsag-cred").contains "QSAG.VC.SD_STMT_DIGEST.V2" = true := by
  decide +kernel

/-- `#tooth`: the superseded labels are no longer inventoried. -/
theorem tooth_stale_labels_absent :
    ¬ ((CrossProtocol.auditedLabelsOf "qsag-hd").contains "QSAG.HD.QUERY_BUDGET.V2" = true) ∧
    ¬ ((CrossProtocol.auditedLabelsOf "qsag-hd").contains "QSAG.HD.QUERY_BUDGET.V3" = true) ∧
    ¬ ((CrossProtocol.auditedLabelsOf "qsag-policy").contains "QSAG.POLICY.DURABLE_LEDGER.V5" = true) ∧
    ¬ ((CrossProtocol.auditedLabelsOf "qsag-cred").contains "QSAG.VC.SD_STMT_DIGEST.V1" = true) := by
  decide +kernel

#verify_constructive inhabited_current_labels
  tooth_stale_labels_absent


end Qsag.AggregationParityTeeth
end

public section
namespace Qsag.Aggregation
/-- Concrete inhabitedness witness: a genuine 16-bit `cSHAKE256` Proof-of-Work (`powBits = 16`,
    nonce `70035`) on the digest of `powWitnessSeed` (`"WHIR_STAGE_POW"` under
    `"QSAG.AGG.FS_TRANSCRIPT/v1"`), checked by the Lean kernel. -/
theorem inhabited_whir_stage_pow_16 :
    verifyWhirStagePow (stagePowDigest powWitnessSeed) 70035 16 = true := stage_pow_fixture_accepts

/-- `#tooth` Invalid PoW Nonce Rejection (`powNonce = 0` fails 16-bit PoW on the witness digest). -/
theorem tooth_whir_pow16_nonce0_rejected :
    verifyWhirStagePow (stagePowDigest powWitnessSeed) 0 16 = false := stage_pow_fixture_rejects_zero

theorem tooth_whir_pow_nonce_mutation :
    ∃ nonce : Nat, nonce ≠ 70035 ∧
      verifyWhirStagePow (stagePowDigest powWitnessSeed) nonce 16 = false :=
  ⟨0, by decide, tooth_whir_pow16_nonce0_rejected⟩

#tooth_pair verifyWhirStagePow_16_iff vs tooth_whir_pow_nonce_mutation
theorem inhabited_whir_pow_inputs :
    ∃ (chal : List UInt8) (nonce : Nat),
      chal = stagePowDigest powWitnessSeed ∧ nonce = 70035 ∧
      chal.length = 32 ∧ nonce < 2 ^ 64 ∧ verifyWhirStagePow chal nonce 16 = true :=
  ⟨stagePowDigest powWitnessSeed, 70035, rfl, rfl, stagePowDigest_length _,
    by decide, inhabited_whir_stage_pow_16⟩

#verify_inhabited verifyWhirStagePow_16_iff inhabited_whir_pow_inputs


end Qsag.Aggregation
end

public section
namespace Qsag
/-- A concrete `ByteArray → ByteArray` digest with 32-byte output: the first 32 bytes of the
    input, zero-padded. It is not collision resistant (it ignores every byte past the 32nd),
    which is what makes the hypotheses of the extractor satisfiable. -/
def canopyPrefixHash (x : ByteArray) : ByteArray :=
  ⟨⟨(x.data.toList ++ List.replicate 32 (0 : UInt8)).take 32⟩⟩

theorem canopyPrefixHash_length (x : ByteArray) :
    (canopyPrefixHash x).data.toList.length = 32 := by
  show ((x.data.toList ++ List.replicate 32 (0 : UInt8)).take 32).length = 32
  rw [List.length_take, List.length_append, List.length_replicate]
  omega

/-- The 32-byte digest whose bytes all equal `b`. -/
def canopyConstDigest (b : UInt8) : CanopyDigest32 :=
  ⟨⟨⟨List.replicate 32 b⟩⟩, List.length_replicate⟩

/-- Commitment of the two-leaf tree with leaf `0` equal to `canopyConstDigest 5` under
    `canopyPrefixHash`; the node frame keeps only 27 bytes of the left child, so the commitment
    does not depend on the right child. -/
def canopyAuditCommitment : CanopyDigest32 :=
  canopyRootHashOf canopyPrefixHash canopyPrefixHash_length 1
    (canopyNodeHashOf canopyPrefixHash canopyPrefixHash_length 1
      (canopyConstDigest 5) (canopyConstDigest 7))

private theorem canopyAudit_accepts (b : UInt8) :
    verifyCanopyMultiproof (canopyNodeHashOf canopyPrefixHash canopyPrefixHash_length)
      (canopyRootHashOf canopyPrefixHash canopyPrefixHash_length) 1 canopyAuditCommitment
      [(0, canopyConstDigest 5)] [canopyConstDigest b] = true := by
  rw [verifyCanopyMultiproof_one, decide_eq_true_eq]
  apply Subtype.ext
  simp only [canopyAuditCommitment, canopyRootHashOf_val, canopyNodeHashOf_val,
    canopyNodeFrame.public_eqs, canopyRootFrame.public_eqs, canopyPrefixHash, canopyConstDigest]
  rfl

/-- Inhabitedness witness for the transcript extractor over a `ByteArray → ByteArray` 32-byte
    digest: under `canopyPrefixHash`, two `CanopyMultiProof` openings of leaf `0` with different
    siblings are both accepted against `canopyAuditCommitment`, so the hypotheses of
    `extractHashCollisionFromCanopyTranscripts` are jointly satisfiable, and the extractor
    returns an explicit pair of distinct byte strings with equal digests. -/
theorem inhabited_canopy_collision_extractor :
    verifyCanopyMultiproof (canopyNodeHashOf canopyPrefixHash canopyPrefixHash_length)
        (canopyRootHashOf canopyPrefixHash canopyPrefixHash_length) 1 canopyAuditCommitment
        [(0, canopyConstDigest 5)] [canopyConstDigest 7] = true ∧
    verifyCanopyMultiproof (canopyNodeHashOf canopyPrefixHash canopyPrefixHash_length)
        (canopyRootHashOf canopyPrefixHash canopyPrefixHash_length) 1 canopyAuditCommitment
        [(0, canopyConstDigest 5)] [canopyConstDigest 8] = true ∧
    Nonempty (ExtractedHashCollision canopyPrefixHash) :=
  ⟨canopyAudit_accepts 7, canopyAudit_accepts 8,
    ⟨extractHashCollisionFromCanopyTranscripts canopyPrefixHash canopyPrefixHash_length 1
      canopyAuditCommitment [(0, canopyConstDigest 5)] [(0, canopyConstDigest 5)]
      [canopyConstDigest 7] [canopyConstDigest 8] rfl
        (canopyAudit_accepts 7) (canopyAudit_accepts 8) (by
          intro h
          have hs := congrArg Prod.snd h
          have hc := congrArg (fun d : CanopyDigest32 => d.val.data.toList) (List.cons.inj hs).1
          exact (by decide : List.replicate 32 (7 : UInt8) ≠ List.replicate 32 8) hc)⟩⟩

end Qsag
end

public section
namespace Qsag.ZkHem
open CommRingOps


end Qsag.ZkHem
end

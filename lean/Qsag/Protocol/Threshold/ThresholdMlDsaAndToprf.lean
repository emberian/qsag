module

public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf.Ext6RabinField
public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf.DkgAndSigning
public import Qsag.Math.GoldilocksEncoding
public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf.BlindVcSponge
public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf.BlindVcCircuit
public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf.BlindVcVerifier
public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf.BlindVcSimulation
public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf.CheckedSigning
public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf.ShamirAndSeedExpansion
import Qsag.Tactic.AssuranceKit

/-
# Threshold ML-DSA arithmetic, checked signing, TOPRF execution, and credential relations

Proved here, constructively:

* The 256-point negacyclic NTT with its inverse (`fips204InvNtt_ntt`, `fips204Ntt_invNtt`),
  field arithmetic, rounding identities, and a coset LDE that interpolates through the
  inverse NTT (`cosetLde204_ntt`) on a validated domain (`cosetDomain204_inhabited`).
* `mldsaVerify` is the parameterized algebraic core kept for the MIR bridge.
  `mldsaVerifyBytes204` is the standalone ML-DSA-44 verifier on wire bytes (SHAKE, ExpandA,
  SampleInBall, packing, strict signature and hint decoding); it fails closed when a
  rejection sampler exhausts its byte budget. Agreement with other implementations is an
  executed check, not a theorem.
* Signing consumes multiplication results through a transcript-computed sacrifice check
  (`rssSacrificedSignStep`): an accepted attempt equals the exact-product reference
  transition unless the challenge lies in a list of bad values fixed by the transcript
  (`rssSacrificedSignStep_refines`). `rssDurableSign204` reserves the aggregate nonce in a
  persistent ledger before anything is released and releases only a final signature;
  nonces of released signatures are pairwise distinct across signs, failed writes and
  crashes (`rssDurable204_released_nonces_distinct`).
* The DKG is a commit, freeze, reveal machine; after freezing, the share accepted at each
  position is fixed up to a hash collision (`dkg204_reveal_determined_at_freeze`).
* The TOPRF client output is derived through decoded holder messages at every
  multiplication of all 30 rounds, for the full-value transport unconditionally
  (`toprfActiveClient204_correct`) and for the digest transport up to a collision.
  `toprf_joint_view_simulation` gives one coin bijection for the input sharing and all
  gates together.

* The verification extension `F_q[X]/(X^6 - 7)` is a field: Frobenius acts on coordinates
  (`ext6Pow_frobenius`), every nonzero element has the executable inverse `ext6Inv`
  (`ext6Mul_inv_cancel`), products vanish only at zero (`ext6Mul_eq_zero`), and the modulus
  has no proper factorization (`ext6Modulus_irreducible`).

* Batching and folding coins of the multiplication check are extension elements; a
  discrepancy polynomial over the extension has at most degree-many roots among them
  (`rss_ext6_discrepancy_roots_le`).
* Replacing every key-expanded mask tape by an independent tape costs the number of keys
  times the single-key distinguishing bound (`prss_multi_key_hybrid`).

Companion security modules: `Qsag.Protocol.Threshold.ThresholdMlDsaSecurity` proves 3-party `(2, 3)` RSS
multiplication and repeated-sacrifice refinement (`rss3MulStep_recon`,
`rss3_repeated_sacrifice_pq256`, `rss_distributed_trace_refines_sacrificedSignStep`),
multi-attempt sealed-`w₁` abort-transcript zero-knowledge (`threshold_mldsa_abort_transcript_zk`),
and `ML-DSA-65`/`87` (`PQ128`) parameter bounds (`mlDsa_challenge_entropy_bounds`), while
`Qsag.Protocol.Credentials.BlindVcQromSecurity` proves `438`-repetition `BlindVC` QROM Fiat-Shamir soundness
(`blindVc_quantum128_qrom_fs_soundness`) and issuer `ML-DSA` root-attestation unforgeability
(`blindVc_presentation_reduces_to_issuer_mldsa`). The single-key PRF assumption on PRSS tape
expansion and Rust wire-bytes transcript equivalence remain external to the algebraic model.
-/

public section

namespace Qsag

set_option autoImplicit false

/-- A valid witness needs strictly ascending, in-range disclosed indices. -/
theorem BlindVcWitnessValid.strictAsc {stmt : BlindVcPublicStatement}
    {wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth}
    (h : BlindVcWitnessValid stmt wit) :
    vcCheckDisclosedStrictAsc stmt.schema.arity stmt.disclosedAttrs = true :=
  ((blindVcWitnessValid_iff stmt wit).mp h).1


#verify_constructive BlindVcWitnessValid.strictAsc

end Qsag
end

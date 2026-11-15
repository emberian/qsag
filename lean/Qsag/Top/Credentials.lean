module
/-
# Qsag.Top.Credentials — End-to-End Composed Anonymous Credential, Lattice, and PCG Security

Top-level composition module (zero `import all`) connecting:
1. Negacyclic `R_q = ℤ_{12289}[X]/(X^{1024}+1)` OT decryption, GGM wire-forest SPCOT correlation,
   and cyclotomic Module-SIS extraction boundaries (`LatticePreprocessingFull`, `RlweExtractionBoundary`),
2. Exact rational Dual-LPN regular-block bias (`GaussianHvzkAndDualLpn.ExactRat`, `DensePcgProductionTaps`)
   projected into canonical `Spec.RatBound` (`strictlyMoreThanBits 256`),
3. Threshold FIPS-204 `ML-DSA` rejection-sampling plateau shift-invariance, degree-6 extension
   (`𝔽_{q^6}`) repeated sacrifice soundness, and multi-key PRSS hybrid bounds
   (`ThresholdMlDsaSecurity`, `ThresholdMlDsaAndToprf`), and
4. `PiBlindVc` Fiat–Shamir rewound-transcript collision extraction (`BlindVcCollisionFinder`) paired
   with ideal selective-disclosure soundness and undisclosed-attribute privacy (`Spec.IdealCred`,
   `Spec.pqCredentialProfile`: `N = 256`, `33` repetitions over `GF(p^5)`).
-/

public import Qsag.Spec.Primitives
public import Qsag.Oracle.SpecRatBridges
public import Qsag.Spec.Parameters
public import Qsag.Spec.Refines
public import Qsag.Spec.GameBound
public import Qsag.Spec.Assumptions
public import Qsag.Spec.IdealCred
public import Qsag.Protocol.Threshold.LatticePreprocessingFull
public import Qsag.Protocol.Threshold.RlweExtractionBoundary
public import Qsag.Math.Lattices
public import Qsag.Protocol.Threshold.DensePcgProductionTaps
public import Qsag.Protocol.Threshold.ThresholdMlDsaSecurity
public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf
public import Qsag.Protocol.Credentials.BlindVcCollisionFinder
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Top

set_option autoImplicit false

/-! ## 1. Dual-LPN Regular-Block Bias Projected Into Canonical `Spec.RatBound` + Production PCG Taps -/

/-- **Dual-LPN Regular-Block Bias in Canonical `Spec.RatBound` (`pcg_dual_lpn_bias_in_spec_ratBound`)**:
    Unifies `GaussianHvzkAndDualLpn` (`ExactRat`) with `Spec.RatBound` and `DensePcgProductionTaps`:
    1. Projects `ExactRat.abs (parityBias ...)` via `Spec.RatBound.clampExactRat` to establish
       `strictlyMoreThanBits 256` (`< 2^{-256}`) for any 64 balanced regular-block weights,
    2. Certifies Stern–Dumer ISD work `> 2^{256}` (`pcg_dense_depth15_prange_and_stern_dumer_pq128`), and
    3. Connects concrete generated production rows (`lpnMatrixRow auditSession 0 1 15 0` and `543`)
       to their certified signed bias brackets! -/
theorem pcg_dual_lpn_bias_in_spec_ratBound
    (weights : List Nat) (hLen : weights.length = 64)
    (hBal : ∀ w ∈ weights, ((32768 : Int) - 2 * (w : Int)).natAbs ≤ 2047)
    (q l : Nat) (hq : q ≤ 32) :
    (Qsag.Spec.RatBound.clampExactRat
      (Qsag.ExactRat.abs
        (Qsag.parityBias (Qsag.regularBlockXorOneProb (weights.map Qsag.depth15TreeRate))))).strictlyMoreThanBits 256 ∧
    Qsag.sternDumerWorkExceedsPow2 Qsag.pcgDepth15Cols Qsag.pcgDenseRows Qsag.pcgDenseWeightT q l 256 ∧
    Qsag.lpnMatrixRow Qsag.auditSession 0 1 15 0 = Qsag.prodRow0Taps ∧
    (Qsag.noiseSignedSum 32768 (Qsag.rowTestFns (Qsag.lpnMatrixRow Qsag.auditSession 0 1 15 0)) false).natAbs *
      2 ^ 117 < 32768 ^ 64 := by
  have hBias := Qsag.pcg_dense_dual_lpn_linear_bias_lt_two_neg_256 weights hLen hBal
  have hClamp := Qsag.Spec.RatBound.clampExactRat_strictlyMoreThanBits_of_lt_twoNegPow hBias
  obtain ⟨hSd, _⟩ := Qsag.pcg_dense_depth15_prange_and_stern_dumer_pq128 q l hq
  obtain ⟨hRow0Lt, _⟩ := Qsag.generatedRow0_bias_bracket
  exact ⟨hClamp, hSd, Qsag.prodRow0Taps_eq_generator, hRow0Lt⟩

/-! ## 2. RLWE-1024 Preprocessing, SPCOT Peer Verification, and Cyclotomic SIS Boundary -/

/-- **RLWE-1024 Preprocessing, SPCOT Wire Verification, and Module-SIS Extraction Boundary
    (`rlwe_preprocessing_and_sis_boundary_chain`)**:
    Composes `LatticePreprocessingFull` (`checkWirePeer_sound`, `rlwe_pq24_grover_and_box_bridge`)
    with `RlweExtractionBoundary` (`rlweUnitSis_relation`, `rlweUnitSis_norm_le_half_modulus`). -/
theorem rlwe_preprocessing_and_sis_boundary_chain
    (fuel : Nat) (hdr : Qsag.DensePcgV3.SeedHeader)
    (peer : Qsag.DensePcgV3.PeerRecord hdr.treeDepth)
    (hPeerOk : Qsag.DensePcgV3.checkWirePeer fuel hdr peer = true)
    (A : Qsag.CycPolyZq 10 12289)
    (z : Qsag.PolyInt 1024) :
    (∃ vals, Qsag.DensePcgV3.receiverCheckValues fuel hdr peer = some vals) ∧
    2 ^ 128 ≤ Qsag.groverJointChallengeGrindCost Qsag.rlweZkpokPq256Reps 11 ∧
    Qsag.cycIntInfNorm (Qsag.rlweUnitSisError A) ≤ 6144 ∧
    Qsag.cycZqAdd (Qsag.cycZqMul A (Qsag.cycIntToZq 12289 (@Qsag.cycIntOne 1024)))
      (Qsag.cycIntToZq 12289 (Qsag.rlweUnitSisError A)) = Qsag.cycZqZero := by
  obtain ⟨vals, hVals, _⟩ := Qsag.DensePcgV3.checkWirePeer_sound fuel hdr peer hPeerOk
  obtain ⟨_, _, hGrover, _⟩ := Qsag.rlwe_pq24_grover_and_box_bridge z
  obtain ⟨_, _, hSisRel⟩ := Qsag.rlweUnitSis_relation A
  exact ⟨⟨vals, hVals⟩, hGrover, Qsag.rlweUnitSis_norm_le_half_modulus A, hSisRel⟩

/-! ## 3. Threshold FIPS-204 `ML-DSA` HVZK Plateau, `𝔽_{q^6}` Sacrifice, and Multi-Key PRSS Hybrid -/

/-- **Threshold `ML-DSA` HVZK Plateau, `𝔽_{q^6}` Sacrifice Soundness, and PRSS Hybrid Bound
    (`threshold_mldsa_hvzk_sacrifice_and_prss_chain`)**:
    Composes `ThresholdMlDsaSecurity` (`fips204_z_plateau_shift_invariant`, `rss3_repeated_sacrifice_pq256`)
    with `ThresholdMlDsaAndToprf` (`prss_multi_key_hybrid`) into a unified threshold-issuance theorem. -/
theorem threshold_mldsa_hvzk_sacrifice_and_prss_chain
    (gamma1 beta : Nat) (hLt : beta < gamma1) (cs1 zStar : Int)
    (hCs1 : -((beta : Int)) ≤ cs1 ∧ cs1 ≤ (beta : Int))
    (hOpen : Qsag.inOpenNormBox (gamma1 - beta) zStar = true)
    (x y : Qsag.Rss3Share) (r0 r1 deltaZ : Qsag.Fq204)
    (a : Qsag.Ext6Fq204) (b : Qsag.Rss3Share) (deltaC : Qsag.Ext6Fq204)
    (chis : List Qsag.Ext6Fq204) (hCheat : deltaZ ≠ Qsag.Fq204.zero)
    {O : Type} {N : Nat} (real ideal : Fin N → O) (m : Nat) (D : List O → Bool) (ε : Nat)
    (hPrf : Qsag.PrssSingleKeyBound real ideal D ε) :
    Qsag.qsum (2 * gamma1 - 1) (fun idx =>
      if Qsag.maskCoordAt gamma1 idx + cs1 = zStar then 1 else 0) = 1 ∧
    (Qsag.sacAcceptRepeated chis (Qsag.rss3ToSacGate x y r0 r1 deltaZ a b deltaC) = true →
      ∀ chi ∈ chis, chi = Qsag.sacBadChallenge204 (Qsag.rss3ToSacGate x y r0 r1 deltaZ a b deltaC)) ∧
    2 ^ 256 < Qsag.mldsaQ ^ 12 ∧
    Qsag.prssGap (Qsag.prssRealHits real m D) (Qsag.prssIdealHits ideal m D) ≤
      m * (N ^ (m - 1) * ε) := by
  have hPlat := Qsag.fips204_z_plateau_shift_invariant gamma1 beta hLt cs1 zStar hCs1 hOpen
  obtain ⟨hSac, hPow⟩ := Qsag.rss3_repeated_sacrifice_pq256 x y r0 r1 deltaZ a b deltaC chis hCheat
  have hPrss := Qsag.prss_multi_key_hybrid real ideal m D ε hPrf
  exact ⟨hPlat, hSac, hPow, hPrss⟩

/-! ## 4. `PiBlindVc` Selective-Disclosure Soundness & Fiat–Shamir Collision Extraction -/

/-- **Anonymous Credential Selective-Disclosure Soundness, Privacy, & Fiat–Shamir Extraction
    (`blindVc_presentation_and_collision_extraction_chain`)**:
    Composes `Spec.idealCredMachine_presentation_sound` (accumulator-pinned, anti-replay, hidden-witness
    selective disclosure with `N = 256` parties and `33` repetitions over `GF(p^5)` in
    `Spec.pqCredentialProfile`) with `BlindVcCollisionFinder.blindVc_fs_collisionFinder_mass_bound`
    and `vcRewoundCollisionFinder_honest`. -/
theorem blindVc_presentation_and_collision_extraction_chain
    {Attr : Type} [DecidableEq Attr]
    (pk₀ : Qsag.Spec.Bytes) (root₀ : Qsag.Spec.Digest256)
    (st st' : Qsag.Spec.IdealCredState Attr)
    (credId : Nat) (stmtCred : Qsag.Spec.CredentialStatement Attr)
    (hPresOk : (Qsag.Spec.idealCredMachine pk₀ root₀).step st (.present credId stmtCred) =
      some (st', .presentationVerdict true))
    {cardX k : Nat}
    (H : List UInt8 → List UInt8) (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Qsag.Vec UInt8 32 → Qsag.PartyGateCoins D)
    (stmtAt : Fin cardX → Qsag.BlindVcPublicStatement)
    (msgAt : Fin cardX → Qsag.BlindVcParallelMsg k)
    (O : Fin cardX → BitVec (64 * k)) (seeds : List (Fin cardX))
    (weight : Fin cardX → Nat)
    (nonce : Qsag.Vec UInt8 32) (idx : Nat) (tr : Qsag.BlindVcRepTriple) :
    (stmtCred.challengeNonce ∉ st.usedChallenges ∧
      Qsag.Spec.DisclosedIndicesValid stmtCred = true ∧
      ∃ attrs, st.enrolledCredentials[credId]? = some attrs ∧
        Qsag.Spec.CredentialMatchesAttributes stmtCred attrs = true) ∧
    (Qsag.Spec.pqCredentialProfile.sdLimboParties = 256 ∧
      Qsag.Spec.pqCredentialProfile.sdRepsQuantum = 33 ∧
      Qsag.Spec.pqCredentialProfile.sdExtDegree = 5) ∧
    (seeds.map (fun x => if Qsag.blindVcFsUnfilteredLiveAfter H prgExpand stmtAt msgAt O x
      then weight x else 0)).sum ≤
      (seeds.map (fun x => if (Qsag.blindVcTableCollisionFinder H hHLen (stmtAt x) (msgAt x)).isSome
        then weight x else 0)).sum +
      (seeds.map (fun x => if Qsag.blindVcFsLiveAfter H prgExpand stmtAt msgAt O x
        then weight x else 0)).sum ∧
    (Qsag.vcRewoundCollisionFinder H hHLen nonce idx
      (Qsag.openBlindVcRep H nonce idx tr 0)
      (Qsag.openBlindVcRep H nonce idx tr 1)
      (Qsag.openBlindVcRep H nonce idx tr 2)).isSome = false := by
  obtain ⟨_, _, hFresh, _, hIdxOk, hEnrolled⟩ :=
    Qsag.Spec.idealCredMachine_presentation_sound pk₀ root₀ st st' credId stmtCred hPresOk
  obtain ⟨_, _, hLimbo, hExt5, hReps33, _⟩ := Qsag.Spec.pqCredentialProfile_soundness_params
  exact ⟨⟨hFresh, hIdxOk, hEnrolled⟩,
         ⟨hLimbo, hReps33, hExt5⟩,
         Qsag.blindVc_fs_collisionFinder_mass_bound H hHLen prgExpand stmtAt msgAt O seeds weight,
         Qsag.vcRewoundCollisionFinder_honest H hHLen nonce idx tr⟩

#verify_constructive
  Qsag.Top.pcg_dual_lpn_bias_in_spec_ratBound
  Qsag.Top.rlwe_preprocessing_and_sis_boundary_chain
  Qsag.Top.threshold_mldsa_hvzk_sacrifice_and_prss_chain
  Qsag.Top.blindVc_presentation_and_collision_extraction_chain

end Qsag.Top
end

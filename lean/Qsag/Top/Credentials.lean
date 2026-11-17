module
public import Qsag.Protocol.Threshold.SacrificeFreezeSample
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
   with the authenticated-possession soundness of the ideal credential functionality
   (`Spec.IdealCred`, `Spec.pqCredentialProfile`: `N = 256`, `33` repetitions over `GF(p^5)`),
   the interactive cut-and-choose count discharged unconditionally over the concrete quintic field
   `GF(p)[T]/(T^5 - 3)` and `192 × 192` multiplication grid (`blindVc_cut_and_choose_gameBound`),
   and the QROM opening-round bound with `hDefect` discharged on `GF(p^5)`
   (`blindVc_concrete_fp5_qrom_opening_soundness`), and
5. The refinement obligation `CredentialImplementation` inhabited by the concrete SPDZ TOPRF +
   `PiBlindVc` protocol machine (`toprfCredentialImplementation` over `piToprfCredService`, paired
   with `piToprfCredMachine_dataRefines_idealCred`), plus the network-contract bridge
   `credPort_authenticated_by_channel_contract` tying `Spec.CredPort` caller labels to
   `Spec.AuthenticatedChannelContract`.
-/

public import Qsag.Spec.Primitives
public import Qsag.Oracle.SpecRatBridges
public import Qsag.Spec.Parameters
public import Qsag.Spec.Refines
public import Qsag.Spec.GameBound
public import Qsag.Spec.Assumptions
public import Qsag.Spec.IdealCred
public import Qsag.Protocol.Threshold.LatticePreprocessingFull
public import Qsag.Protocol.Threshold.RlweExtraction
public import Qsag.Math.TapRowParityBias
public import Qsag.Math.Lattices
public import Qsag.Protocol.Threshold.DensePcgTaps
public import Qsag.Protocol.Threshold.ThresholdMlDsaSecurity
public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf
public import Qsag.Protocol.Credentials.BlindVcCollisionFinder
public import Qsag.Protocol.Credentials.RepetitionCutAndChoose
public import Qsag.Protocol.Credentials.ToprfMachine
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Top

set_option autoImplicit false

/-! ## 1. Dual-LPN Regular-Block Bias Projected Into Canonical `Spec.RatBound` + Production PCG Taps -/

/-- The generated production row has bias strictly between `2^-118` and `2^-117`.
    This concrete row calculation and the Stern–Dumer work estimate use no balance premise. -/
theorem pcg_dual_lpn_bias_in_spec_ratBound
    (q l : Nat) (hq : q ≤ 32) :
    (Qsag.TapRowBias.imbalanceProd 32768 Qsag.TapRowBias.prodRow0Weights * 2 ^ 117 < 32768 ^ 64 ∧
      32768 ^ 64 < Qsag.TapRowBias.imbalanceProd 32768 Qsag.TapRowBias.prodRow0Weights * 2 ^ 118) ∧
    Qsag.sternDumerWorkExceedsPow2 Qsag.pcgDepth15Cols Qsag.pcgDenseRows Qsag.pcgDenseWeightT q l 256 ∧
    Qsag.lpnMatrixRow Qsag.auditSession 0 1 15 0 = Qsag.prodRow0Taps ∧
    (Qsag.noiseSignedSum 32768 (Qsag.rowTestFns (Qsag.lpnMatrixRow Qsag.auditSession 0 1 15 0)) false).natAbs *
      2 ^ 117 < 32768 ^ 64 := by
  obtain ⟨hSd, _⟩ := Qsag.pcg_dense_depth15_prange_and_stern_dumer_pq128 q l hq
  exact ⟨Qsag.TapRowBias.prodRow0_bias_bracket, hSd,
    Qsag.prodRow0Taps_eq_generator, Qsag.generatedRow0_bias_bracket.1⟩

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

/-- **Coin-After-Freeze `SacrificeFreezeSample` ↔ `rssSacrificedSignStep` Composition
    (`threshold_mldsa_frozen_sacrifice_sign_step_soundness`)**:
    Composes `SacrificeFreezeSample` (`FrozenChallenge.vectors SacrificeFreeze.fq204Elems 6`,
    freezing the prover's `(inp, T)` before sampling the 6-coordinate `Ext6Fq204` challenge) with
    threshold FIPS-204 `rssSacrificedSignStep` (`rssSacrificedSignStep_mldsaQ6_frozen_soundness`),
    proving that any forged multiplication product is accepted on at most `1` of `mldsaQ ^ 6`
    challenges (`< 2^-137`). -/
theorem threshold_mldsa_frozen_sacrifice_sign_step_soundness
    (chalHash : List UInt8 → (Fin 4 → Qsag.NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Qsag.Poly256)
    (st : Qsag.RssMlDsaSignerState)
    (A : Qsag.FrozenChallenge.Adversary
      (Qsag.RssMlDsaAttemptInput × Qsag.RssSacrificeTranscript204) Qsag.Fq204)
    (hForged : (A.commit []).1.products ≠
      Qsag.rssComputeProducts chalHash sampleInBall st (A.commit []).1.mu (A.commit []).1.ySubsets) :
    Qsag.FrozenChallenge.countIf
      (fun chis => Qsag.rssSignStepAcceptsSacrifice chalHash sampleInBall st
        (A.commit []).1 (Qsag.ext6OfList chis) (A.commit []).2)
      (Qsag.FrozenChallenge.vectors Qsag.SacrificeFreeze.fq204Elems 6) ≤ 1 ∧
    Qsag.FrozenChallenge.countIf
      (fun chis => Qsag.rssSignStepAcceptsSacrifice chalHash sampleInBall st
        (A.commit []).1 (Qsag.ext6OfList chis) (A.commit []).2)
      (Qsag.FrozenChallenge.vectors Qsag.SacrificeFreeze.fq204Elems 6) * 2 ^ 137 <
      Qsag.mldsaQ ^ 6 ∧
    (Qsag.FrozenChallenge.vectors Qsag.SacrificeFreeze.fq204Elems 6).length = Qsag.mldsaQ ^ 6 :=
  Qsag.rssSacrificedSignStep_mldsaQ6_frozen_soundness chalHash sampleInBall st A hForged

/-! ## 4. `PiBlindVc` Selective-Disclosure Soundness & Fiat–Shamir Collision Extraction -/

/-- **Roster of credential facts (`blindVc_presentation_provenance_and_collision_finder_roster`)**.
    Collects the four presentation and ZKBoo issuance properties below (see §7 for the concrete
    `piToprfCredService` / `LimboSdOpeningWire.verify33` refinement to `Spec.idealCredMachine`):
    1. Ideal machine (`Spec.idealCredMachine_presentation_sound`, `…_presentation_provenance`): an
       accepted presentation after a run from the initial state uses a fresh challenge for the
       current epoch, arrived on the holder's port (or on the adversary port with that holder
       corrupt in the current state), and is backed by a record owned by the presenting holder
       that an event of the run issued on the issuer port (or on the adversary port, the issuer
       being corrupt in the current state).
    2. Profile literals: `N = 256` parties, `33` repetitions, `GF(p^5)`.
    3. `BlindVcCollisionFinder.blindVc_fs_collisionFinder_mass_bound` (the 3-party ZKBoo issuance
       transcript model).
    4. `vcRewoundCollisionFinder_honest`. -/
theorem blindVc_presentation_provenance_and_collision_finder_roster
    {Attr O : Type} [DecidableEq Attr] (cfg : Qsag.Spec.IdealCredConfig O)
    {s₀ st st' : Qsag.Spec.IdealCredState Attr O}
    {trace : List (Qsag.Spec.IdealCredInput Attr × Qsag.Spec.IdealCredOutput O)}
    {port : Qsag.Spec.CredPort} {holder credId : Nat}
    (stmtCred : Qsag.Spec.CredentialStatement Attr)
    (hInit : (Qsag.Spec.idealCredMachine cfg).Init s₀)
    (hTrace : (Qsag.Spec.idealCredMachine cfg).ValidTrace s₀ trace st)
    (hPresOk : (Qsag.Spec.idealCredMachine cfg).step st (port, .present holder credId stmtCred) =
      some (st', .presentationVerdict true))
    {cardX k : Nat}
    (H : List UInt8 → List UInt8) (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Qsag.Vec UInt8 32 → Qsag.PartyGateCoins D)
    (stmtAt : Fin cardX → Qsag.BlindVcPublicStatement)
    (msgAt : Fin cardX → Qsag.BlindVcParallelMsg k)
    (O' : Fin cardX → BitVec (64 * k)) (seeds : List (Fin cardX))
    (weight : Fin cardX → Nat)
    (nonce : Qsag.Vec UInt8 32) (idx : Nat) (tr : Qsag.BlindVcRepTriple) :
    ((st.challengeLedgers stmtCred.verifier).accepts
        stmtCred.verifierScope stmtCred.challengeNonce stmtCred.verificationTime = true ∧
      stmtCred.epoch = st.epoch ∧
      Qsag.Spec.DisclosedIndicesValid stmtCred = true ∧
      (port = Qsag.Spec.CredPort.holder holder ∨
        (port = Qsag.Spec.CredPort.adversary ∧ holder ∈ st.corruptHolders)) ∧
      ∃ r ∈ st.records, r.credId = credId ∧ r.holder = holder ∧
        Qsag.Spec.CredentialMatchesAttributes stmtCred r.attrs = true ∧
        ∃ issuePort : Qsag.Spec.CredPort,
          ((issuePort, Qsag.Spec.CredCommand.issue holder r.attrs r.root),
            Qsag.Spec.IdealCredOutput.issued credId) ∈ trace ∧
          (issuePort = Qsag.Spec.CredPort.issuer ∨
            (issuePort = Qsag.Spec.CredPort.adversary ∧ st.issuerCorrupt = true))) ∧
    (Qsag.Spec.pqCredentialProfile.sdLimboParties = 256 ∧
      Qsag.Spec.pqCredentialProfile.sdRepsQuantum = 33 ∧
      Qsag.Spec.pqCredentialProfile.sdExtDegree = 5) ∧
    (seeds.map (fun x => if Qsag.blindVcFsUnfilteredLiveAfter H prgExpand stmtAt msgAt O' x
      then weight x else 0)).sum ≤
      (seeds.map (fun x => if (Qsag.blindVcTableCollisionFinder H hHLen (stmtAt x) (msgAt x)).isSome
        then weight x else 0)).sum +
      (seeds.map (fun x => if Qsag.blindVcFsLiveAfter H prgExpand stmtAt msgAt O' x
        then weight x else 0)).sum ∧
    (Qsag.vcRewoundCollisionFinder H hHLen nonce idx
      (Qsag.openBlindVcRep H nonce idx tr 0)
      (Qsag.openBlindVcRep H nonce idx tr 1)
      (Qsag.openBlindVcRep H nonce idx tr 2)).isSome = false := by
  obtain ⟨_, _, hEpoch, _, hFresh, _, hIdxOk, _⟩ :=
    Qsag.Spec.idealCredMachine_presentation_sound cfg hPresOk
  obtain ⟨hPort, _, r, hr, hId, hHolder, _, hMatch, hProv⟩ :=
    Qsag.Spec.idealCredMachine_presentation_provenance cfg hInit hTrace hPresOk
  obtain ⟨_, _, hLimbo, hExt5, hReps33, _⟩ := Qsag.Spec.pqCredentialProfile_soundness_params
  exact ⟨⟨hFresh, hEpoch, hIdxOk, hPort, r, hr, hId, hHolder, hMatch, hProv⟩,
         ⟨hLimbo, hReps33, hExt5⟩,
         Qsag.blindVc_fs_collisionFinder_mass_bound H hHLen prgExpand stmtAt msgAt O' seeds weight,
         Qsag.vcRewoundCollisionFinder_honest H hHLen nonce idx tr⟩

/-- **Deployed presentation profile: 256 parties, 33 repetitions, `GF(p^5)`
    (`credential_sd_limbo256_tau33_interactive_soundness`)**.
    1. The constants of the seed-tree model are those of `Spec.pqCredentialProfile`
       (`VC_SD_LIMBO_PARTIES = 256`, `VC_SD_GGM_DEPTH = 8`, `sd_repetitions = 33`, extension
       degree `5`).
    2. For a per-repetition verifier whose opening round is the hidden-party check on the
       repetition's check values (`CutAndChoose.DefectChecker`), and any prover whose second
       message may depend on all folding challenges and whose third on all folding challenges
       and evaluation points: fewer than a `2^-263` fraction of the challenge triples is
       accepted.
    Hypotheses, not proved from `blind_vc.rs`: `AlgebraicSound` (at most `dG` bad folding
    challenges with `dG / |G| ≤ 2^-300`, at most `384` bad evaluation points among the
    `p^5 - 1` nonzero ones, and a nonzero check value after good challenges). The count is for
    independent uniform challenges per repetition; the Fiat–Shamir transform and quantum
    adversaries are not covered. -/
theorem credential_sd_limbo256_tau33_interactive_soundness {C G B1 R B2 : Type}
    (K : Qsag.CutAndChoose.DefectChecker C G B1 R B2) (P : Qsag.CutAndChoose.Prover C G B1 R B2)
    (Gs : List G) (Rs : List R) (dG : Nat)
    (hS : K.AlgebraicSound P.commit Gs Rs dG Qsag.CutAndChoose.limboEvalDegree)
    (hRs : Rs.length = Qsag.CutAndChoose.fp5NonzeroCount) (hG : dG * 2 ^ 300 ≤ Gs.length)
    (hGpos : 0 < Gs.length) :
    (Qsag.credentialSdParties = Qsag.Spec.pqCredentialProfile.sdLimboParties ∧
      Qsag.credentialSdGgmDepth = Qsag.Spec.pqCredentialProfile.sdGgmDepth ∧
      Qsag.credentialSdRepetitions = Qsag.Spec.pqCredentialProfile.sdRepsQuantum ∧
      Qsag.Spec.pqCredentialProfile.sdExtDegree = 5) ∧
    Qsag.CutAndChoose.winCount K.toChecker Qsag.credentialSdRepetitions P Gs Rs
        Qsag.CutAndChoose.limboParties * 2 ^ 263 <
      Qsag.CutAndChoose.challengeCount Qsag.credentialSdRepetitions Gs Rs
        Qsag.CutAndChoose.limboParties :=
  ⟨⟨Qsag.credentialSdParties_eq.trans (by decide), Qsag.credentialSdGgmDepth_eq.trans (by decide),
      Qsag.credentialSdRepetitions_eq.trans (by decide), by decide⟩,
    Qsag.CutAndChoose.limbo256_tau33_defect_check_soundness K P Gs Rs dG hS hRs hG hGpos⟩

/-- **Opening round of the deployed presentation in the QROM, and seed-tree binding
    (`credential_sd_opening_round_qrom_and_seed_tree_binding`)**.
    1. For a `Q ≤ 2^60`-query quantum adversary against a uniform oracle with 33-byte outputs,
       the doomed-to-live flip mass of the hidden-party round is at most `(2Q + 1)^2 / 2^264`,
       which is below `2^-128`. A point is doomed only if its check-value table has a nonzero
       entry in each of the 33 repetitions (`hDefect`, a hypothesis).
    2. Two accepted openings of the same round-1 commitments `H ∘ encode` have the same digest
       at every party both open; if the reconstructed preimages differ there, the executable
       scan returns a collision of `H`.
    Not covered: the folding and evaluation Fiat–Shamir rounds in the QROM and their
    composition with this round. -/
theorem credential_sd_opening_round_qrom_and_seed_tree_binding
    {cardX cardAnc Q : Nat} (hQ : Q ≤ 2 ^ 60)
    (A : Qsag.QuantumAdv cardX (8 * 33) cardAnc Q)
    (defect : Fin cardX → Nat → Fin 256 → Qsag.CredentialFp5) (doomed : Fin cardX → Bool)
    (hDefect : ∀ x, doomed x = true → ∀ idx < 33,
      ∃ bad, defect x idx bad ≠ Qsag.credentialFp5Zero)
    (prg : Qsag.CredentialGgmPrg) (H : List UInt8 → List UInt8)
    (encode : Fin Qsag.credentialSdParties → Qsag.CredentialGgmSeed → List UInt8)
    (commitments : Fin Qsag.credentialSdParties → List UInt8) (a b : Qsag.CredentialGgmOpening)
    (ha : Qsag.verifyCredentialGgmOpening prg (fun p seed => H (encode p seed)) commitments a = true)
    (hb : Qsag.verifyCredentialGgmOpening prg (fun p seed => H (encode p seed)) commitments b = true)
    (party : Fin Qsag.credentialSdParties) (hpa : party ≠ a.hidden) (hpb : party ≠ b.hidden) :
    (Qsag.RatBound.le
      ⟨Qsag.uniformOracleSum (8 * 33) cardX
         (fun O => Qsag.qromOrdinaryFlipMass A O id (fun _ x => doomed x)
           (Qsag.credentialSdOpeningLiveAfter defect)),
       (2 ^ (8 * 33)) ^ cardX *
         (Qsag.prefixScale A Q (Nat.le_refl Q) * Qsag.QVec.stateNormSq A.init),
       Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos _))
         (Nat.mul_pos (Qsag.prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      ⟨(2 * Q + 1) ^ 2 * 1, 2 ^ (8 * 33), Nat.two_pow_pos _⟩ ∧
      (2 * Q + 1) ^ 2 * 2 ^ 128 < (256 : Nat) ^ 33) ∧
    H (Qsag.credentialGgmOpenedPreimage prg encode a party) =
      H (Qsag.credentialGgmOpenedPreimage prg encode b party) ∧
    (Qsag.credentialGgmOpenedPreimage prg encode a party ≠
        Qsag.credentialGgmOpenedPreimage prg encode b party →
      (Qsag.credentialGgmCollisionFinder H prg encode a b).isSome = true) := by
  obtain ⟨hMass, hBudget, _⟩ := Qsag.credentialSd_opening_round_qrom_bound hQ A defect doomed hDefect
  exact ⟨⟨hMass, hBudget⟩,
    Qsag.credentialGgmOpenedPreimage_same_digest H prg encode commitments a b ha hb party hpa hpb,
    fun hne => Qsag.credentialGgmCollisionFinder_complete H prg encode commitments a b ha hb
      party hpa hpb hne⟩

/-! ## 5. Refinement Obligation for a Concrete Credential Service -/

/-- What a concrete credential service `M` must provide to inherit the guarantees of
    `Spec.idealCredMachine cfg`.

    The input of `M` is `(sender, w)`: a raw wire message `w` (anything the network can carry)
    together with the channel endpoint `sender` that delivered it. The sender is supplied by the
    environment, not by the service and not by the extractor: honest parties deliver on their own
    ports, and everything the adversary delivers arrives on `.adversary`. That labelling is the
    authenticated-channel assumption of the model; it is not proved here.

    `extract` names only the *command* a wire message stands for. The ideal event is
    `(sender, cmd)` with the delivering sender, by construction: the extractor cannot choose the
    port.
    * `accept_ok`: whatever `M` accepts, the ideal machine accepts as a command of the delivering
      sender, with the same output.
    * `reject_ok`: a rejected message leaves the ideal state unchanged. `M` may reject more than
      the ideal machine does; availability is not claimed.

    A service that ignores who delivered a message is not an instance
    (`unauthenticatedCredService_not_implementation`).

    Inhabitant in the tree: the concrete SPDZ TOPRF + `PiBlindVc` protocol service
    `toprfCredentialImplementation` over `Qsag.piToprfCredService` (executing direct
    state-field validation, monotone SPDZ reservoir consumption, and 33-repetition `N = 256`
    Limbo GGM opening checks, paired with `Qsag.piToprfCredMachine_dataRefines_idealCred`). -/
structure CredentialImplementation {O S W : Type} (Attr : Type) [DecidableEq Attr]
    (cfg : Qsag.Spec.IdealCredConfig O)
    (M : Qsag.Spec.Machine S (Qsag.Spec.CredPort × W) (Qsag.Spec.IdealCredOutput O)) : Type where
  Rel : S → Qsag.Spec.IdealCredState Attr O → Prop
  extract : S → Qsag.Spec.CredPort → W → Option (Qsag.Spec.CredCommand Attr)
  init_ok : ∀ {c₀ : S}, M.Init c₀ → Rel c₀ (Qsag.Spec.IdealCredState.empty cfg)
  accept_ok : ∀ {c c' : S} {a : Qsag.Spec.IdealCredState Attr O} {sender : Qsag.Spec.CredPort}
    {w : W} {out : Qsag.Spec.IdealCredOutput O},
    Rel c a → M.step c (sender, w) = some (c', out) →
    ∃ (cmd : Qsag.Spec.CredCommand Attr) (a' : Qsag.Spec.IdealCredState Attr O),
      extract c sender w = some cmd ∧
      (Qsag.Spec.idealCredMachine cfg).step a (sender, cmd) = some (a', out) ∧ Rel c' a'
  reject_ok : ∀ {c : S} {a : Qsag.Spec.IdealCredState Attr O} {x : Qsag.Spec.CredPort × W},
    Rel c a → M.step c x = none → Rel (M.errStep c x) a

/-- What a run shows at the interface: per step, the delivering sender and the output. -/
def credSenderView {O W : Type}
    (tr : List ((Qsag.Spec.CredPort × W) × Qsag.Spec.IdealCredOutput O)) :
    List (Qsag.Spec.CredPort × Qsag.Spec.IdealCredOutput O) :=
  tr.map (fun e => (e.1.1, e.2))

private theorem credSenderView_mem {O W W' : Type}
    {aTr : List ((Qsag.Spec.CredPort × W') × Qsag.Spec.IdealCredOutput O)}
    {tr : List ((Qsag.Spec.CredPort × W) × Qsag.Spec.IdealCredOutput O)}
    (hView : credSenderView aTr = credSenderView tr)
    {p : Qsag.Spec.CredPort} {cmd : W'} {out : Qsag.Spec.IdealCredOutput O}
    (hMem : ((p, cmd), out) ∈ aTr) : ∃ w : W, ((p, w), out) ∈ tr := by
  have h1 : (p, out) ∈ credSenderView aTr := by
    unfold credSenderView
    exact List.mem_map.mpr ⟨((p, cmd), out), hMem, rfl⟩
  rw [hView] at h1
  unfold credSenderView at h1
  obtain ⟨e, he, hfe⟩ := List.mem_map.mp h1
  obtain ⟨⟨q, w⟩, o⟩ := e
  obtain ⟨hq, ho⟩ := Prod.mk.inj hfe
  have hq' : q = p := hq
  have ho' : o = out := ho
  subst hq'
  subst ho'
  exact ⟨w, he⟩

/-- Every run of an implementation from an initial state is matched by a run of the ideal machine
    from its initial state, with the same sender and the same output at every step, ending in a
    related state. -/
theorem CredentialImplementation.abstract_run {Attr O S W : Type} [DecidableEq Attr]
    {cfg : Qsag.Spec.IdealCredConfig O}
    {M : Qsag.Spec.Machine S (Qsag.Spec.CredPort × W) (Qsag.Spec.IdealCredOutput O)}
    (impl : CredentialImplementation Attr cfg M)
    {c₀ c : S} {tr : List ((Qsag.Spec.CredPort × W) × Qsag.Spec.IdealCredOutput O)}
    (hInit : M.Init c₀) (hTrace : M.ValidTrace c₀ tr c) :
    ∃ (a : Qsag.Spec.IdealCredState Attr O)
      (aTr : List (Qsag.Spec.IdealCredInput Attr × Qsag.Spec.IdealCredOutput O)),
      impl.Rel c a ∧
      (Qsag.Spec.idealCredMachine cfg).ValidTrace (Qsag.Spec.IdealCredState.empty cfg) aTr a ∧
      credSenderView aTr = credSenderView tr := by
  have hGen : ∀ {c₁ c₂ : S} {t : List ((Qsag.Spec.CredPort × W) × Qsag.Spec.IdealCredOutput O)},
      M.ValidTrace c₁ t c₂ → ∀ a₁ : Qsag.Spec.IdealCredState Attr O, impl.Rel c₁ a₁ →
      ∃ (a : Qsag.Spec.IdealCredState Attr O)
        (aTr : List (Qsag.Spec.IdealCredInput Attr × Qsag.Spec.IdealCredOutput O)),
        impl.Rel c₂ a ∧ (Qsag.Spec.idealCredMachine cfg).ValidTrace a₁ aTr a ∧
        credSenderView aTr = credSenderView t := by
    intro c₁ c₂ t hT
    induction hT with
    | nil s => exact fun a₁ hRel => ⟨a₁, [], hRel, .nil a₁, rfl⟩
    | @accept s s' sf inp out rest hStep _ ih =>
      intro a₁ hRel
      obtain ⟨sender, w⟩ := inp
      obtain ⟨cmd, a', _, hStepA, hRel'⟩ := impl.accept_ok hRel hStep
      obtain ⟨a, aTr, hRelF, hTrA, hOut⟩ := ih a' hRel'
      refine ⟨a, ((sender, cmd), out) :: aTr, hRelF, .accept hStepA hTrA, ?_⟩
      unfold credSenderView at hOut ⊢
      simp only [List.map_cons, hOut]
    | reject x hNone _ ih =>
      intro a₁ hRel
      exact ih a₁ (impl.reject_ok hRel hNone)
  exact hGen hTrace _ (impl.init_ok hInit)

/-- `a` is an ideal state reached by an ideal run from the initial state that shows the same
    senders and outputs as the service run `tr`, and it is related to the service state `c`.
    Corruption is adaptive in `Spec.idealCredMachine`, so who is corrupt "now" is a fact about
    this state, not about the configuration. -/
def CredentialImplementation.AbstractAt {Attr O S W : Type} [DecidableEq Attr]
    {cfg : Qsag.Spec.IdealCredConfig O}
    {M : Qsag.Spec.Machine S (Qsag.Spec.CredPort × W) (Qsag.Spec.IdealCredOutput O)}
    (impl : CredentialImplementation Attr cfg M)
    (tr : List ((Qsag.Spec.CredPort × W) × Qsag.Spec.IdealCredOutput O)) (c : S)
    (a : Qsag.Spec.IdealCredState Attr O) : Prop :=
  impl.Rel c a ∧
  ∃ aTr : List (Qsag.Spec.IdealCredInput Attr × Qsag.Spec.IdealCredOutput O),
    (Qsag.Spec.idealCredMachine cfg).ValidTrace (Qsag.Spec.IdealCredState.empty cfg) aTr a ∧
    credSenderView aTr = credSenderView tr

/-- **Issuance authentication for an implementation.** If the service answers `.issued credId`
    to a message, then there is an ideal state `a` matching the run in which: the message was
    delivered on the issuer port, or on the adversary port with the issuer corrupt in `a`; and it
    stands for the issuance of a credential with between `1` and `maxAttrs` attributes. -/
theorem credentialImplementation_issuance_authenticated {Attr O S W : Type} [DecidableEq Attr]
    {cfg : Qsag.Spec.IdealCredConfig O}
    {M : Qsag.Spec.Machine S (Qsag.Spec.CredPort × W) (Qsag.Spec.IdealCredOutput O)}
    (impl : CredentialImplementation Attr cfg M)
    {c₀ c c' : S} {tr : List ((Qsag.Spec.CredPort × W) × Qsag.Spec.IdealCredOutput O)}
    {sender : Qsag.Spec.CredPort} {w : W} {credId : Nat}
    (hInit : M.Init c₀) (hTrace : M.ValidTrace c₀ tr c)
    (hAccepted : M.step c (sender, w) = some (c', .issued credId)) :
    ∃ a : Qsag.Spec.IdealCredState Attr O, impl.AbstractAt tr c a ∧
      (sender = Qsag.Spec.CredPort.issuer ∨
        (sender = Qsag.Spec.CredPort.adversary ∧ a.issuerCorrupt = true)) ∧
      ∃ (holder : Nat) (attrs : List Attr) (newRoot : Qsag.Spec.Digest256),
        impl.extract c sender w = some (.issue holder attrs newRoot) ∧
        0 < attrs.length ∧ attrs.length ≤ Qsag.Spec.pqCredentialProfile.maxAttrs := by
  obtain ⟨a, aTr, hRel, hTrA, hView⟩ := impl.abstract_run hInit hTrace
  obtain ⟨cmd, a', hExt, hStepA, _⟩ := impl.accept_ok hRel hAccepted
  obtain ⟨holder, attrs, newRoot, hCmd⟩ := Qsag.Spec.idealCredStep_output_command hStepA
  subst hCmd
  obtain ⟨hPort, hPos, hMax⟩ := Qsag.Spec.idealCredMachine_issuance_authenticated cfg hStepA
  exact ⟨a, ⟨hRel, aTr, hTrA, hView⟩, hPort, holder, attrs, newRoot, hExt, hPos, hMax⟩

/-- **Possession provenance for an implementation.** If the service answers a message with the
    verdict `true`, then there is an ideal state `a` matching the run in which: the message
    stands for a presentation of some credential `credId` by some `holder`; it was delivered on
    that holder's port (or on the adversary port with that holder corrupt in `a`); the statement
    names the configured issuer key; and the run contains a message the service answered
    `.issued credId`, delivered on the issuer port, or on the adversary port with the issuer
    corrupt in `a`. -/
theorem credentialImplementation_presentation_provenance {Attr O S W : Type} [DecidableEq Attr]
    {cfg : Qsag.Spec.IdealCredConfig O}
    {M : Qsag.Spec.Machine S (Qsag.Spec.CredPort × W) (Qsag.Spec.IdealCredOutput O)}
    (impl : CredentialImplementation Attr cfg M)
    {c₀ c c' : S} {tr : List ((Qsag.Spec.CredPort × W) × Qsag.Spec.IdealCredOutput O)}
    {sender : Qsag.Spec.CredPort} {w : W}
    (hInit : M.Init c₀) (hTrace : M.ValidTrace c₀ tr c)
    (hAccepted : M.step c (sender, w) = some (c', .presentationVerdict true)) :
    ∃ a : Qsag.Spec.IdealCredState Attr O, impl.AbstractAt tr c a ∧
      ∃ (holder credId : Nat) (stmt : Qsag.Spec.CredentialStatement Attr),
        impl.extract c sender w = some (.present holder credId stmt) ∧
        (sender = Qsag.Spec.CredPort.holder holder ∨
          (sender = Qsag.Spec.CredPort.adversary ∧ holder ∈ a.corruptHolders)) ∧
        stmt.issuerPk = cfg.issuerPk ∧
        ∃ (issuePort : Qsag.Spec.CredPort) (w₀ : W),
          ((issuePort, w₀), Qsag.Spec.IdealCredOutput.issued credId) ∈ tr ∧
          (issuePort = Qsag.Spec.CredPort.issuer ∨
            (issuePort = Qsag.Spec.CredPort.adversary ∧ a.issuerCorrupt = true)) := by
  obtain ⟨a, aTr, hRel, hTrA, hView⟩ := impl.abstract_run hInit hTrace
  obtain ⟨cmd, a', hExt, hStepA, _⟩ := impl.accept_ok hRel hAccepted
  obtain ⟨holder, credId, stmt, hCmd⟩ := Qsag.Spec.idealCredStep_output_command hStepA
  subst hCmd
  obtain ⟨hPort, hPk, r, _, _, _, _, _, issuePort, hMem, hIssuePort⟩ :=
    Qsag.Spec.idealCredMachine_presentation_provenance cfg rfl hTrA hStepA
  obtain ⟨w₀, hw₀⟩ := credSenderView_mem hView hMem
  exact ⟨a, ⟨hRel, aTr, hTrA, hView⟩, holder, credId, stmt, hExt, hPort, hPk,
    issuePort, w₀, hw₀, hIssuePort⟩

/-- Tooth: if the issuer is not corrupt in any ideal state matching the run, the service never
    answers `.issued` to a message delivered on any port other than the issuer's — in particular
    to one the adversary delivered. -/
theorem credentialImplementation_rejects_foreign_issue {Attr O S W : Type} [DecidableEq Attr]
    {cfg : Qsag.Spec.IdealCredConfig O}
    {M : Qsag.Spec.Machine S (Qsag.Spec.CredPort × W) (Qsag.Spec.IdealCredOutput O)}
    (impl : CredentialImplementation Attr cfg M)
    {c₀ c c' : S} {tr : List ((Qsag.Spec.CredPort × W) × Qsag.Spec.IdealCredOutput O)}
    {sender : Qsag.Spec.CredPort} {w : W} {credId : Nat}
    (hInit : M.Init c₀) (hTrace : M.ValidTrace c₀ tr c)
    (hHonest : ∀ a : Qsag.Spec.IdealCredState Attr O, impl.AbstractAt tr c a →
      a.issuerCorrupt = false)
    (hSender : ¬ (sender = Qsag.Spec.CredPort.issuer)) :
    ¬ (M.step c (sender, w) = some (c', .issued credId)) := by
  intro hAccepted
  obtain ⟨a, hAt, hAuth, _⟩ :=
    credentialImplementation_issuance_authenticated impl hInit hTrace hAccepted
  rcases hAuth with hP | ⟨_, hC⟩
  · exact hSender hP
  · rw [hHonest a hAt] at hC
    cases hC

/-- Tooth: if no holder is corrupt in any ideal state matching the run, the service never
    answers the verdict `true` to a message the adversary delivered. -/
theorem credentialImplementation_rejects_foreign_presentation {Attr O S W : Type}
    [DecidableEq Attr] {cfg : Qsag.Spec.IdealCredConfig O}
    {M : Qsag.Spec.Machine S (Qsag.Spec.CredPort × W) (Qsag.Spec.IdealCredOutput O)}
    (impl : CredentialImplementation Attr cfg M)
    {c₀ c c' : S} {tr : List ((Qsag.Spec.CredPort × W) × Qsag.Spec.IdealCredOutput O)} {w : W}
    (hInit : M.Init c₀) (hTrace : M.ValidTrace c₀ tr c)
    (hHonest : ∀ a : Qsag.Spec.IdealCredState Attr O, impl.AbstractAt tr c a →
      a.corruptHolders = []) :
    ¬ (M.step c (Qsag.Spec.CredPort.adversary, w) = some (c', .presentationVerdict true)) := by
  intro hAccepted
  obtain ⟨a, hAt, holder, _, _, _, hAuth, _⟩ :=
    credentialImplementation_presentation_provenance impl hInit hTrace hAccepted
  rcases hAuth with hP | ⟨_, hC⟩
  · cases hP
  · rw [hHonest a hAt] at hC
    exact nomatch hC

/-- **TOPRF provenance for an implementation.** If every ideal state matching the run has at
    most `toprfMaxCorrupt` corrupt servers and the service answers a message with a TOPRF value,
    then there is such a state `a` in which: the message stands for an evaluation of some ticket
    and input, the value is the keyed-table value of `(keyId, epoch, input)`, and the run
    contains a message delivered on the port of a committee server not corrupt in `a` that the
    service answered `.toprfApproved`. -/
theorem credentialImplementation_toprf_provenance {Attr O S W : Type} [DecidableEq Attr]
    {cfg : Qsag.Spec.IdealCredConfig O}
    {M : Qsag.Spec.Machine S (Qsag.Spec.CredPort × W) (Qsag.Spec.IdealCredOutput O)}
    (impl : CredentialImplementation Attr cfg M)
    {c₀ c c' : S} {tr : List ((Qsag.Spec.CredPort × W) × Qsag.Spec.IdealCredOutput O)}
    {sender : Qsag.Spec.CredPort} {w : W} {v : O}
    (hInit : M.Init c₀) (hTrace : M.ValidTrace c₀ tr c)
    (hCorrupt : ∀ a : Qsag.Spec.IdealCredState Attr O, impl.AbstractAt tr c a →
      a.corruptServerCount ≤ Qsag.Spec.pqCredentialProfile.toprfMaxCorrupt)
    (hAccepted : M.step c (sender, w) = some (c', .toprfEvaluated v)) :
    ∃ a : Qsag.Spec.IdealCredState Attr O, impl.AbstractAt tr c a ∧
      ∃ (t : Qsag.Spec.ToprfTicket) (input : Qsag.Spec.Bytes),
        impl.extract c sender w = some (.evalToprf t input) ∧
        v = cfg.oprf ⟨t.keyId, t.epoch, input⟩ ∧
        ∃ (i : Nat) (w₀ : W),
          i < Qsag.Spec.pqCredentialProfile.toprfServers ∧ i ∉ a.corruptServers ∧
          ((Qsag.Spec.CredPort.server i, w₀), Qsag.Spec.IdealCredOutput.toprfApproved) ∈ tr := by
  obtain ⟨a, aTr, hRel, hTrA, hView⟩ := impl.abstract_run hInit hTrace
  have hAt : impl.AbstractAt tr c a := ⟨hRel, aTr, hTrA, hView⟩
  obtain ⟨cmd, a', hExt, hStepA, _⟩ := impl.accept_ok hRel hAccepted
  obtain ⟨t, input, hCmd⟩ := Qsag.Spec.idealCredStep_output_command hStepA
  subst hCmd
  obtain ⟨hVal, _, i, hi, hHonest, hMem, _⟩ :=
    Qsag.Spec.idealCredMachine_toprf_provenance cfg rfl hTrA (hCorrupt a hAt) hStepA
  obtain ⟨w₀, hw₀⟩ := credSenderView_mem hView hMem
  exact ⟨a, hAt, t, input, hExt, Qsag.Spec.IdealCredOutput.toprfEvaluated.inj hVal, i, w₀, hi,
    hHonest, hw₀⟩

/-! ### The unauthenticated service is not an implementation -/

/-- The port a command claims to come from. -/
def credCommandClaimedPort {Attr : Type} : Qsag.Spec.CredCommand Attr → Qsag.Spec.CredPort
  | .issue _ _ _ => .issuer
  | .advanceEpoch _ _ => .issuer
  | .present h _ _ => .holder h
  | .issueChallenge verifier _ _ _ => .verifier verifier
  | .approveToprf i _ => .server i
  | .evalToprf _ _ => .client
  | .corrupt _ => .adversary

/-- A service that authenticates nobody: it ignores who delivered a command and runs the ideal
    transition on the port the command claims. Any caller can issue invented attributes and
    present for any holder. -/
@[expose] def unauthenticatedCredService {Attr O : Type} [DecidableEq Attr]
    (cfg : Qsag.Spec.IdealCredConfig O) :
    Qsag.Spec.Machine (Qsag.Spec.IdealCredState Attr O)
      (Qsag.Spec.CredPort × Qsag.Spec.CredCommand Attr) (Qsag.Spec.IdealCredOutput O) where
  Init st := st = Qsag.Spec.IdealCredState.empty cfg
  step st x := Qsag.Spec.idealCredStep cfg st (credCommandClaimedPort x.2, x.2)
  errStep st _ := st

/-- The unauthenticated service answers an issuance of an invented attribute delivered by the
    adversary. -/
theorem unauthenticatedCredService_adversary_issues {Attr O : Type} [DecidableEq Attr]
    (cfg : Qsag.Spec.IdealCredConfig O) (holder : Nat) (attr : Attr)
    (newRoot : Qsag.Spec.Digest256) :
    ((unauthenticatedCredService cfg).step (Qsag.Spec.IdealCredState.empty cfg)
        (Qsag.Spec.CredPort.adversary, .issue holder [attr] newRoot)).map Prod.snd =
      some (.issued 0) :=
  Qsag.Spec.idealCredStep_issuer_issues_at_init cfg holder attr newRoot

/-- An ideal run with no accepted input ends in the state it started from. -/
private theorem idealCred_validTrace_nil {Attr O : Type} [DecidableEq Attr]
    (cfg : Qsag.Spec.IdealCredConfig O) {s a : Qsag.Spec.IdealCredState Attr O}
    {t : List (Qsag.Spec.IdealCredInput Attr × Qsag.Spec.IdealCredOutput O)}
    (h : (Qsag.Spec.idealCredMachine cfg).ValidTrace s t a) (ht : t = []) : a = s := by
  induction h with
  | nil _ => rfl
  | accept _ _ _ => cases ht
  | reject _ _ _ ih => exact ih ht

/-- Tooth (referee 3, N2): with an issuer that is not corrupt at the start, the unauthenticated
    service satisfies `CredentialImplementation` for no relation and no extractor. -/
theorem unauthenticatedCredService_not_implementation {Attr O : Type} [DecidableEq Attr]
    (cfg : Qsag.Spec.IdealCredConfig O) (hHonest : cfg.issuerCorrupt = false) (attr : Attr) :
    ¬ Nonempty (CredentialImplementation Attr cfg (unauthenticatedCredService (Attr := Attr) cfg)) := by
  intro hImpl
  obtain ⟨impl⟩ := hImpl
  have hIssues := unauthenticatedCredService_adversary_issues cfg 0 attr 0#256
  cases hStep : (unauthenticatedCredService cfg).step (Qsag.Spec.IdealCredState.empty cfg)
      (Qsag.Spec.CredPort.adversary, Qsag.Spec.CredCommand.issue 0 [attr] 0#256) with
  | none =>
    rw [hStep] at hIssues
    cases hIssues
  | some res =>
    obtain ⟨st', out⟩ := res
    rw [hStep] at hIssues
    have hOut : out = Qsag.Spec.IdealCredOutput.issued 0 := Option.some.inj hIssues
    subst hOut
    refine credentialImplementation_rejects_foreign_issue impl
      (c₀ := Qsag.Spec.IdealCredState.empty cfg) (tr := []) rfl (.nil _) ?_
      (by intro h; cases h) hStep
    intro a hAt
    obtain ⟨_, aTr, hTrA, hView⟩ := hAt
    have hNil : aTr = [] := List.map_eq_nil_iff.mp hView
    rw [idealCred_validTrace_nil cfg hTrA hNil]
    exact hHonest

#verify_constructive
  Qsag.Top.pcg_dual_lpn_bias_in_spec_ratBound
  Qsag.Top.rlwe_preprocessing_and_sis_boundary_chain
  Qsag.Top.threshold_mldsa_hvzk_sacrifice_and_prss_chain
  Qsag.Top.blindVc_presentation_provenance_and_collision_finder_roster
  Qsag.Top.credential_sd_limbo256_tau33_interactive_soundness
  Qsag.Top.credential_sd_opening_round_qrom_and_seed_tree_binding
  Qsag.Top.CredentialImplementation.abstract_run
  Qsag.Top.credentialImplementation_presentation_provenance
  Qsag.Top.credentialImplementation_issuance_authenticated
  Qsag.Top.credentialImplementation_toprf_provenance
  Qsag.Top.unauthenticatedCredService_adversary_issues

#tooth_pair Qsag.Top.credentialImplementation_issuance_authenticated vs
  Qsag.Top.credentialImplementation_rejects_foreign_issue
#tooth_pair Qsag.Top.credentialImplementation_presentation_provenance vs
  Qsag.Top.credentialImplementation_rejects_foreign_presentation
#tooth_pair Qsag.Top.credentialImplementation_issuance_authenticated vs
  Qsag.Top.unauthenticatedCredService_not_implementation


/-- One malicious server is corrected under collision freedom only on the finite digest
inputs associated with the consumed TOPRF cross-term calls. -/
theorem toprf_digest_correct_on_observed_inputs
    (H : List UInt8 → List UInt8) (ctx : List UInt8) (layer : UInt64)
    (hCtx : ctx.length < 2 ^ 20) (bad : Fin 5)
    (fault : ToprfVecFault204) (faultDigest : ToprfDigestFault204)
    (masks : ToprfPerm12Masks) (keys inputs : Fin 5 → Lane4)
    (forgedFinal : Option (Fin 5 → Lane4))
    (hFree : ∀ a ∈ toprfDigestObservedInputs204 H ctx layer bad fault faultDigest masks keys inputs,
      ∀ b ∈ toprfDigestObservedInputs204 H ctx layer bad fault faultDigest masks keys inputs,
      H a = H b → a = b) :
    toprfActiveClient204 bad (toprfDigestCross204 H ctx layer bad fault faultDigest)
        masks keys inputs forgedFinal =
      some (toprfPlaintext (sumLane4Shares5 keys) (sumLane4Shares5 inputs)) :=
  _root_.Qsag.toprfDigestClient204_correct_of_collision_free H ctx layer hCtx bad fault faultDigest
    masks keys inputs forgedFinal hFree

/-! ## 6. Concrete `GF(p^5)` (`T^5 - 3`, `192 × 192` Grid, `33 × 256`) Cut-and-Choose `GameBound` & QROM Soundness -/

private theorem blindVc_challengeCount_pos :
    0 < Qsag.CutAndChoose.challengeCount Qsag.credentialSdRepetitions
          Qsag.allBlindVcFp5 Qsag.nonzeroBlindVcFp5 Qsag.CutAndChoose.limboParties := by
  rw [Qsag.CutAndChoose.challengeCount_eq, Qsag.allBlindVcFp5_length,
      Qsag.nonzeroBlindVcFp5_length, Qsag.CutAndChoose.limboParties_length,
      Qsag.credentialSdRepetitions_eq]
  have hG : 0 < Qsag.goldilocksPrime ^ 5 :=
    Nat.pow_pos (by decide : 0 < Qsag.goldilocksPrime)
  have hR : 0 < Qsag.CutAndChoose.fp5NonzeroCount := by
    rw [Qsag.CutAndChoose.fp5NonzeroCount_eq]
    decide
  exact Nat.pow_pos (Nat.mul_pos (Nat.mul_pos hG hR) (by decide))

/-- Canonical `Spec.RatBound` winning probability of `P` in the concrete `33 × 256` `GF(p^5)`
    BlindVC cut-and-choose presentation game. -/
def blindVcCutAndChooseWinRat
    (P : Qsag.CutAndChoose.Prover Qsag.BlindVcCommittedProof Qsag.BlindVcFp5
      Qsag.BlindVcR2aMsg Qsag.BlindVcFp5 Qsag.BlindVcR2bMsg) : Qsag.Spec.RatBound :=
  ⟨Qsag.CutAndChoose.winCount Qsag.blindVcRepetitionKernel.toChecker
      Qsag.credentialSdRepetitions P Qsag.allBlindVcFp5 Qsag.nonzeroBlindVcFp5
      Qsag.CutAndChoose.limboParties,
   Qsag.CutAndChoose.challengeCount Qsag.credentialSdRepetitions
      Qsag.allBlindVcFp5 Qsag.nonzeroBlindVcFp5 Qsag.CutAndChoose.limboParties,
   blindVc_challengeCount_pos⟩

/-- **Concrete `GF(p^5)` (`T^5 - 3`, `33 × 256`, `192 × 192` Grid) Cut-and-Choose `GameBound`
    (`blindVc_cut_and_choose_gameBound`)**:
    Discharges `AlgebraicSound`, `dG = 36864` folding luck (`36864 * 2^300 ≤ p^5`), `dR = 384`
    evaluation degree, and `|GF(p^5)^×| = fp5NonzeroCount` unconditionally on the concrete quintic
    extension `BlindVcFp5 = GF(p)[T]/(T^5 - 3)`:
    for EVERY adaptive 3-round prover `P` whose Round-1 commitment has at least one multiplication
    gate fault per repetition (`∀ j, BlindVcRepHasGateFault P.commit j`),
    1. `blindVcRepetitionKernel.AlgebraicSound` holds over `allBlindVcFp5` and `nonzeroBlindVcFp5`,
    2. `winCount * 2^263 < challengeCount` (`strictlyMoreThanBits 263`), and
    3. `Spec.GameBound (blindVcCutAndChooseWinRat P) (Spec.RatBound.invPow2 263)` and
       `(blindVcCutAndChooseWinRat P).atLeastBits 263`! -/
theorem blindVc_cut_and_choose_gameBound
    (P : Qsag.CutAndChoose.Prover Qsag.BlindVcCommittedProof Qsag.BlindVcFp5
      Qsag.BlindVcR2aMsg Qsag.BlindVcFp5 Qsag.BlindVcR2bMsg)
    (hFault : ∀ j : Nat, Qsag.BlindVcRepHasGateFault P.commit j) :
    Qsag.blindVcRepetitionKernel.AlgebraicSound P.commit Qsag.allBlindVcFp5
      Qsag.nonzeroBlindVcFp5 Qsag.SD_GRID_GATES Qsag.CutAndChoose.limboEvalDegree ∧
    Qsag.CutAndChoose.winCount Qsag.blindVcRepetitionKernel.toChecker
        Qsag.credentialSdRepetitions P Qsag.allBlindVcFp5 Qsag.nonzeroBlindVcFp5
        Qsag.CutAndChoose.limboParties * 2 ^ 263 <
      Qsag.CutAndChoose.challengeCount Qsag.credentialSdRepetitions
        Qsag.allBlindVcFp5 Qsag.nonzeroBlindVcFp5 Qsag.CutAndChoose.limboParties ∧
    Qsag.Spec.GameBound (blindVcCutAndChooseWinRat P) (Qsag.Spec.RatBound.invPow2 263) ∧
    (blindVcCutAndChooseWinRat P).atLeastBits 263 := by
  have hAlg := Qsag.blindVcRepetitionKernel_algebraicSound P.commit hFault
    Qsag.allBlindVcFp5 Qsag.nonzeroBlindVcFp5 Qsag.allBlindVcFp5_nodup Qsag.nonzeroBlindVcFp5_nodup
  have hG : Qsag.SD_GRID_GATES * 2 ^ 300 ≤ Qsag.allBlindVcFp5.length := by
    rw [Qsag.allBlindVcFp5_length]
    exact Qsag.blindVc_grid_fold_luck
  have hGpos : 0 < Qsag.allBlindVcFp5.length := by
    rw [Qsag.allBlindVcFp5_length]
    exact Nat.pow_pos (by decide : 0 < Qsag.goldilocksPrime)
  obtain ⟨_, hWinLt⟩ := credential_sd_limbo256_tau33_interactive_soundness
    Qsag.blindVcRepetitionKernel P Qsag.allBlindVcFp5 Qsag.nonzeroBlindVcFp5
    Qsag.SD_GRID_GATES hAlg Qsag.nonzeroBlindVcFp5_length hG hGpos
  have hAtLeast : (blindVcCutAndChooseWinRat P).atLeastBits 263 := by
    change Qsag.CutAndChoose.winCount Qsag.blindVcRepetitionKernel.toChecker
        Qsag.credentialSdRepetitions P Qsag.allBlindVcFp5 Qsag.nonzeroBlindVcFp5
        Qsag.CutAndChoose.limboParties * 2 ^ 263 ≤
      Qsag.CutAndChoose.challengeCount Qsag.credentialSdRepetitions
        Qsag.allBlindVcFp5 Qsag.nonzeroBlindVcFp5 Qsag.CutAndChoose.limboParties
    exact Nat.le_of_lt hWinLt
  have hGb : Qsag.Spec.GameBound (blindVcCutAndChooseWinRat P) (Qsag.Spec.RatBound.invPow2 263) :=
    (Qsag.Spec.RatBound.atLeastBits_iff_le_invPow2 263 (blindVcCutAndChooseWinRat P)).mp hAtLeast
  exact ⟨hAlg, hWinLt, hGb, hAtLeast⟩

/-- **Concrete `GF(p^5)` Opening-Round QROM Soundness & Seed-Tree Binding
    (`blindVc_concrete_fp5_qrom_opening_soundness`)**:
    Instantiates `credential_sd_opening_round_qrom_and_seed_tree_binding` on the concrete
    `GF(p)[T]/(T^5 - 3)` per-party defect table `blindVcPartyDefect256` and `blindVcOpeningDoomed`,
    discharging `hDefect` (`∀ idx < 33, ∃ bad, defect x idx bad ≠ 0`) unconditionally via
    `blindVcOpeningDoomed_has_33_defects`! -/
theorem blindVc_concrete_fp5_qrom_opening_soundness
    {cardX cardAnc Q : Nat} (hQ : Q ≤ 2 ^ 60)
    (A : Qsag.QuantumAdv cardX (8 * 33) cardAnc Q)
    (cAt : Fin cardX → Qsag.BlindVcCommittedProof)
    (gammaAt : Fin cardX → Nat → Qsag.BlindVcFp5)
    (b1At : Fin cardX → Qsag.BlindVcR2aMsg)
    (rAt : Fin cardX → Nat → Qsag.BlindVcFp5)
    (b2At : Fin cardX → Qsag.BlindVcR2bMsg)
    (prg : Qsag.CredentialGgmPrg) (H : List UInt8 → List UInt8)
    (encode : Fin Qsag.credentialSdParties → Qsag.CredentialGgmSeed → List UInt8)
    (commitments : Fin Qsag.credentialSdParties → List UInt8) (a b : Qsag.CredentialGgmOpening)
    (ha : Qsag.verifyCredentialGgmOpening prg (fun p seed => H (encode p seed)) commitments a = true)
    (hb : Qsag.verifyCredentialGgmOpening prg (fun p seed => H (encode p seed)) commitments b = true)
    (party : Fin Qsag.credentialSdParties) (hpa : party ≠ a.hidden) (hpb : party ≠ b.hidden) :
    (Qsag.RatBound.le
      ⟨Qsag.uniformOracleSum (8 * 33) cardX
         (fun O => Qsag.qromOrdinaryFlipMass A O id
           (fun _ x => Qsag.blindVcOpeningDoomed cAt gammaAt b1At rAt x)
           (Qsag.credentialSdOpeningLiveAfter
             (fun x idx p => Qsag.blindVcPartyDefect256 (cAt x) idx (gammaAt x idx) (b1At x) (rAt x idx) (b2At x) p))),
       (2 ^ (8 * 33)) ^ cardX *
         (Qsag.prefixScale A Q (Nat.le_refl Q) * Qsag.QVec.stateNormSq A.init),
       Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos _))
         (Nat.mul_pos (Qsag.prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      ⟨(2 * Q + 1) ^ 2 * 1, 2 ^ (8 * 33), Nat.two_pow_pos _⟩ ∧
      (2 * Q + 1) ^ 2 * 2 ^ 128 < (256 : Nat) ^ 33) ∧
    H (Qsag.credentialGgmOpenedPreimage prg encode a party) =
      H (Qsag.credentialGgmOpenedPreimage prg encode b party) ∧
    (Qsag.credentialGgmOpenedPreimage prg encode a party ≠
        Qsag.credentialGgmOpenedPreimage prg encode b party →
      (Qsag.credentialGgmCollisionFinder H prg encode a b).isSome = true) :=
  credential_sd_opening_round_qrom_and_seed_tree_binding hQ A
    (fun x idx p => Qsag.blindVcPartyDefect256 (cAt x) idx (gammaAt x idx) (b1At x) (rAt x idx) (b2At x) p)
    (Qsag.blindVcOpeningDoomed cAt gammaAt b1At rAt)
    (Qsag.blindVcOpeningDoomed_has_33_defects cAt gammaAt b1At rAt b2At)
    prg H encode commitments a b ha hb party hpa hpb

/-! ## 7. Concrete Protocol Inhabitant `toprfCredentialImplementation` (`L-Ex-9`) -/

/-- **Real Protocol Inhabitant of `CredentialImplementation` (`toprfCredentialImplementation`)**:
    Instantiates `CredentialImplementation` on the concrete SPDZ TOPRF + `PiBlindVc` protocol
    machine `Qsag.piToprfCredService cfg` over `ToprfCredWire Attr` with non-identity state
    abstraction `Rel c a := c.abs = a` (collapsing `ToprfReservoir` cursors, quorum poisoning,
    server counter high-water marks, 3-phase audit logs, and `blindVcTag` onto `IdealCredState`).

    Scope. The transition function validates wire data on its own state: caller port, issuance
    arity, the 33-repetition Limbo opening, ticket quorum and counter window, reservoir cursors,
    and the SPDZ MAC equations on the three openings of an evaluation. It contains no call to
    `Spec.credExec` and reads no verdict bit from a wire. It is still a model of the gates, not
    of the arithmetic behind them: an accepted evaluation returns `cfg.oprf` at the ticket's
    point instead of a value reconstructed from shares, issuance stores the submitted attributes
    without a ZKBoo transcript, and the MAC key is a state field whose secrecy is not modelled.
    The refinement therefore shows that these gates admit no behaviour outside
    `Spec.idealCredMachine`; it does not show that the SPDZ circuit computes the PRF. -/
def toprfCredentialImplementation {O : Type} (Attr : Type) [DecidableEq Attr]
    (cfg : Qsag.Spec.IdealCredConfig O) :
    CredentialImplementation Attr cfg (Qsag.piToprfCredService (Attr := Attr) cfg) where
  Rel c a := c.abs = a
  extract _ _ w := some w.toCommand
  init_ok hInit := Qsag.piToprfCredService_init_abs cfg hInit
  accept_ok {c c' a sender w out} hRel hStep := by
    subst hRel
    exact ⟨w.toCommand, c'.abs, rfl, Qsag.piToprfCredService_accept_ok cfg hStep, rfl⟩
  reject_ok {c a x} hRel hNone := by
    subst hRel
    exact Qsag.piToprfCredService_reject_ok cfg hNone

/-- **Non-Triviality Witness for `toprfCredentialImplementation`**:
    1. Distinct concrete protocol states `c₁ ≠ c₂` with distinct SPDZ reservoirs (`c₁.reservoir ≠ c₂.reservoir`,
       `c₁.reservoir.poisoned = false`, `c₂.reservoir.poisoned = true`) map via `Rel` to the exact same
       `IdealCredState.empty cfg` (impossible under `Rel := Eq` in `CredentialImplementation.ideal`).
    2. A rejected wire step mutates concrete `errStep` state (`phaseAuditCount` increments from `0` to `1`)
       while preserving `Rel`! -/
theorem toprfCredentialImplementation_non_identity_state {Attr O : Type} [DecidableEq Attr]
    (cfg : Qsag.Spec.IdealCredConfig O) :
    (∃ c₁ c₂ : Qsag.PiToprfCredState Attr O,
      c₁ ≠ c₂ ∧
      c₁.reservoir ≠ c₂.reservoir ∧
      (toprfCredentialImplementation Attr cfg).Rel c₁ (Qsag.Spec.IdealCredState.empty cfg) ∧
      (toprfCredentialImplementation Attr cfg).Rel c₂ (Qsag.Spec.IdealCredState.empty cfg)) ∧
    ((Qsag.piToprfCredService (Attr := Attr) cfg).errStep (Qsag.PiToprfCredState.init cfg)
        (.client, .advanceEpochWire 0 0#256)).phaseAuditCount = 1 :=
  Qsag.piToprfCredService_non_identity_witness cfg

/-- **Stuttering `Spec.DataRefines` + Multi-Turn Reservoir Monotonicity for `piToprfCredMachine`
    (`piToprfCred_dataRefines_and_reservoir_monotone`)**:
    Exports the full `Spec.DataRefines` witness (`Qsag.piToprfCredMachine_dataRefines_idealCred`,
    handling internal `SpdzReservoir::prepare` turns via `visIn = none`) alongside multi-turn
    SPDZ reservoir monotonicity (`Qsag.piToprfCredService_reservoir_monotone`). -/
def piToprfCredMachine_dataRefines_ideal {Attr O : Type} [DecidableEq Attr]
    (cfg : Qsag.Spec.IdealCredConfig O) :
    Qsag.Spec.DataRefines (Qsag.piToprfCredMachine (Attr := Attr) cfg)
      (Qsag.Spec.idealCredMachine cfg)
      Qsag.toprfMachineVisIn (Qsag.toprfMachineVisOut .corrupted) :=
  Qsag.piToprfCredMachine_dataRefines_idealCred cfg

theorem piToprfCredService_reservoir_never_resets {Attr O : Type} [DecidableEq Attr]
    (cfg : Qsag.Spec.IdealCredConfig O) (c : Qsag.PiToprfCredState Attr O)
    (port : Qsag.Spec.CredPort) (w : Qsag.ToprfCredWire Attr) :
    Qsag.ReservoirStepMonotone c.reservoir
      ((Qsag.piToprfCredService cfg).errStep c (port, w)).reservoir ∧
    ∀ c' out, (Qsag.piToprfCredService cfg).step c (port, w) = some (c', out) →
      Qsag.ReservoirStepMonotone c.reservoir c'.reservoir :=
  Qsag.piToprfCredService_reservoir_monotone cfg c port w

/-- **No preprocessing session is rewound, internal turns included.** Every accepted step of the
    full machine `Qsag.piToprfCredMachine` (wire steps and `prepareReservoir` turns) either stays
    in the current session with cursors that only advance and an untouched session ledger, or
    installs a session identifier that is neither the current one nor a retired one, and retires
    the current one. -/
theorem piToprfCredMachine_reservoir_never_rewinds {Attr O : Type} [DecidableEq Attr]
    (cfg : Qsag.Spec.IdealCredConfig O) (c c' : Qsag.PiToprfCredState Attr O)
    (inp : Qsag.ToprfMachineInput Attr) (out : Option (Qsag.Spec.IdealCredOutput O))
    (hStep : (Qsag.piToprfCredMachine cfg).step c inp = some (c', out)) :
    (Qsag.ReservoirStepMonotone c.reservoir c'.reservoir ∧ c'.retiredSids = c.retiredSids ∧
      c'.spdzMacKey = c.spdzMacKey) ∨
    (c'.reservoir.preprocessSid ≠ c.reservoir.preprocessSid ∧
      c'.reservoir.preprocessSid ∉ c.retiredSids ∧
      c'.retiredSids = c.reservoir.preprocessSid :: c.retiredSids ∧
      c'.reservoir.pow7Cursor = 0 ∧ c'.reservoir.beaverCursor = 0) :=
  Qsag.piToprfCredMachine_reservoir_never_rewinds cfg c c' inp out hStep

/-- **An accepted TOPRF evaluation passed the checks computed from its wire data**: context equal
    to the granted ticket, canonical request word, the SPDZ MAC equation on all three openings
    under the MAC key in the machine state, zero dual-copy difference, equal output copies. The
    wire carries no verdict bit. What this does not say: the released value is `cfg.oprf` at the
    ticket's point; the machine does not recompute the PRF from shares, and the MAC key's secrecy
    is not modelled. -/
theorem piToprfCredService_eval_accept_checks {Attr O : Type} [DecidableEq Attr]
    (cfg : Qsag.Spec.IdealCredConfig O) (c c' : Qsag.PiToprfCredState Attr O)
    (port : Qsag.Spec.CredPort) (t : Qsag.Spec.ToprfTicket) (input : Qsag.Spec.Bytes)
    (online : Qsag.SpdzOnlineTranscript) (out : Qsag.Spec.IdealCredOutput O)
    (hStep : (Qsag.piToprfCredService cfg).step c (port, .evalToprfWire t input online) =
      some (c', out)) :
    online.context = t ∧ online.requestWord < Qsag.goldilocksPrime ∧
    online.inputBind.val = Qsag.Goldilocks.zero ∧
    online.inputBind.mac =
      Qsag.CommRingOps.mul c.spdzMacKey (Qsag.GoldilocksExt2.ofBase online.inputBind.val) ∧
    online.circuit.mac =
      Qsag.CommRingOps.mul c.spdzMacKey (Qsag.GoldilocksExt2.ofBase online.circuit.val) ∧
    online.output.mac =
      Qsag.CommRingOps.mul c.spdzMacKey (Qsag.GoldilocksExt2.ofBase online.output.val) ∧
    online.outputCopyA = online.outputCopyB :=
  Qsag.piToprfCredService_eval_accept_checks cfg c c' port t input online out hStep

/-- Concrete issuance authentication for `piToprfCredService`. -/
theorem piToprfCredService_issuance_authenticated {Attr O : Type} [DecidableEq Attr]
    (cfg : Qsag.Spec.IdealCredConfig O)
    {c₀ c c' : Qsag.PiToprfCredState Attr O}
    {tr : List ((Qsag.Spec.CredPort × Qsag.ToprfCredWire Attr) × Qsag.Spec.IdealCredOutput O)}
    {sender : Qsag.Spec.CredPort} {w : Qsag.ToprfCredWire Attr} {credId : Nat}
    (hInit : (Qsag.piToprfCredService cfg).Init c₀)
    (hTrace : (Qsag.piToprfCredService cfg).ValidTrace c₀ tr c)
    (hAccepted : (Qsag.piToprfCredService cfg).step c (sender, w) = some (c', .issued credId)) :
    ∃ a : Qsag.Spec.IdealCredState Attr O,
      (toprfCredentialImplementation Attr cfg).AbstractAt tr c a ∧
      (sender = Qsag.Spec.CredPort.issuer ∨
        (sender = Qsag.Spec.CredPort.adversary ∧ a.issuerCorrupt = true)) ∧
      ∃ (holder : Nat) (attrs : List Attr) (newRoot : Qsag.Spec.Digest256),
        w.toCommand = .issue holder attrs newRoot ∧
        0 < attrs.length ∧ attrs.length ≤ Qsag.Spec.pqCredentialProfile.maxAttrs := by
  obtain ⟨a, hAt, hPort, holder, attrs, newRoot, hExt, hPos, hMax⟩ :=
    credentialImplementation_issuance_authenticated (toprfCredentialImplementation Attr cfg)
      hInit hTrace hAccepted
  exact ⟨a, hAt, hPort, holder, attrs, newRoot, Option.some.inj hExt, hPos, hMax⟩

/-- Concrete selective-disclosure presentation provenance for `piToprfCredService`. -/
theorem piToprfCredService_presentation_provenance {Attr O : Type} [DecidableEq Attr]
    (cfg : Qsag.Spec.IdealCredConfig O)
    {c₀ c c' : Qsag.PiToprfCredState Attr O}
    {tr : List ((Qsag.Spec.CredPort × Qsag.ToprfCredWire Attr) × Qsag.Spec.IdealCredOutput O)}
    {sender : Qsag.Spec.CredPort} {w : Qsag.ToprfCredWire Attr}
    (hInit : (Qsag.piToprfCredService cfg).Init c₀)
    (hTrace : (Qsag.piToprfCredService cfg).ValidTrace c₀ tr c)
    (hAccepted : (Qsag.piToprfCredService cfg).step c (sender, w) = some (c', .presentationVerdict true)) :
    ∃ a : Qsag.Spec.IdealCredState Attr O,
      (toprfCredentialImplementation Attr cfg).AbstractAt tr c a ∧
      ∃ (holder credId : Nat) (stmt : Qsag.Spec.CredentialStatement Attr),
        w.toCommand = .present holder credId stmt ∧
        (sender = Qsag.Spec.CredPort.holder holder ∨
          (sender = Qsag.Spec.CredPort.adversary ∧ holder ∈ a.corruptHolders)) ∧
        stmt.issuerPk = cfg.issuerPk ∧
        ∃ (issuePort : Qsag.Spec.CredPort) (w₀ : Qsag.ToprfCredWire Attr),
          ((issuePort, w₀), Qsag.Spec.IdealCredOutput.issued credId) ∈ tr ∧
          (issuePort = Qsag.Spec.CredPort.issuer ∨
            (issuePort = Qsag.Spec.CredPort.adversary ∧ a.issuerCorrupt = true)) := by
  obtain ⟨a, hAt, holder, credId, stmt, hExt, hPort, hPk, issuePort, w₀, hw₀, hIssuePort⟩ :=
    credentialImplementation_presentation_provenance (toprfCredentialImplementation Attr cfg)
      hInit hTrace hAccepted
  exact ⟨a, hAt, holder, credId, stmt, Option.some.inj hExt, hPort, hPk,
    issuePort, w₀, hw₀, hIssuePort⟩

/-- Concrete SPDZ TOPRF evaluation provenance for `piToprfCredService`. -/
theorem piToprfCredService_toprf_provenance {Attr O : Type} [DecidableEq Attr]
    (cfg : Qsag.Spec.IdealCredConfig O)
    {c₀ c c' : Qsag.PiToprfCredState Attr O}
    {tr : List ((Qsag.Spec.CredPort × Qsag.ToprfCredWire Attr) × Qsag.Spec.IdealCredOutput O)}
    {sender : Qsag.Spec.CredPort} {w : Qsag.ToprfCredWire Attr} {v : O}
    (hInit : (Qsag.piToprfCredService cfg).Init c₀)
    (hTrace : (Qsag.piToprfCredService cfg).ValidTrace c₀ tr c)
    (hCorrupt : ∀ a : Qsag.Spec.IdealCredState Attr O,
      (toprfCredentialImplementation Attr cfg).AbstractAt tr c a →
      a.corruptServerCount ≤ Qsag.Spec.pqCredentialProfile.toprfMaxCorrupt)
    (hAccepted : (Qsag.piToprfCredService cfg).step c (sender, w) = some (c', .toprfEvaluated v)) :
    ∃ a : Qsag.Spec.IdealCredState Attr O,
      (toprfCredentialImplementation Attr cfg).AbstractAt tr c a ∧
      ∃ (t : Qsag.Spec.ToprfTicket) (input : Qsag.Spec.Bytes),
        w.toCommand = .evalToprf t input ∧
        v = cfg.oprf ⟨t.keyId, t.epoch, input⟩ ∧
        ∃ (i : Nat) (w₀ : Qsag.ToprfCredWire Attr),
          i < Qsag.Spec.pqCredentialProfile.toprfServers ∧ i ∉ a.corruptServers ∧
          ((Qsag.Spec.CredPort.server i, w₀), Qsag.Spec.IdealCredOutput.toprfApproved) ∈ tr := by
  obtain ⟨a, hAt, t, input, hExt, hv, i, w₀, hi, hHonest, hw₀⟩ :=
    credentialImplementation_toprf_provenance (toprfCredentialImplementation Attr cfg)
      hInit hTrace hCorrupt hAccepted
  exact ⟨a, hAt, t, input, Option.some.inj hExt, hv, i, w₀, hi, hHonest, hw₀⟩

/-! ## 8. Connecting `Spec.CredPort` Caller Labels to `Spec.AuthenticatedChannelContract` -/

/-- Canonical peer-channel endpoint identifier (`Spec.ChannelMsg.sender`) for each `Spec.CredParty`:
    * `0`: `.issuer`
    * `1`: reserved `.client` endpoint
    * `2 + i` (`i < toprfServers`): committee `.server i`
    * `2 + toprfServers + h`: `.holder h` -/
def credPartyEndpointId : Qsag.Spec.CredParty → Nat
  | .issuer => 0
  | .server i => 2 + i
  | .holder h => 2 + Qsag.Spec.pqCredentialProfile.toprfServers + h

/-- Map an authenticated channel sender ID (`Spec.ChannelMsg.sender`) onto `Spec.CredPort`,
    routing any sender in `adversaryIds` onto `.adversary`. -/
def credChannelEndpointPort (adversaryIds : List Nat) (senderId : Nat) : Qsag.Spec.CredPort :=
  if decide (senderId ∈ adversaryIds) then
    .adversary
  else if senderId = 0 then
    .issuer
  else if senderId = 1 then
    .client
  else if senderId < 2 + Qsag.Spec.pqCredentialProfile.toprfServers then
    .server (senderId - 2)
  else
    .holder (senderId - (2 + Qsag.Spec.pqCredentialProfile.toprfServers))

/-- Valid party bound on `CredParty` (committee servers satisfy `i < toprfServers`). -/
def CredPartyInCommittee : Qsag.Spec.CredParty → Prop
  | .issuer => True
  | .holder _ => True
  | .server i => i < Qsag.Spec.pqCredentialProfile.toprfServers

theorem credChannelEndpointPort_roundtrip
    (adversaryIds : List Nat) (party : Qsag.Spec.CredParty)
    (hBound : CredPartyInCommittee party)
    (hHonestEndpoint : credPartyEndpointId party ∉ adversaryIds) :
    credChannelEndpointPort adversaryIds (credPartyEndpointId party) = party.port := by
  cases party with
  | issuer =>
    unfold credPartyEndpointId at hHonestEndpoint ⊢
    unfold credChannelEndpointPort Qsag.Spec.CredParty.port
    rw [decide_eq_false hHonestEndpoint]
    rfl
  | server i =>
    have hi : i < Qsag.Spec.pqCredentialProfile.toprfServers := hBound
    unfold credPartyEndpointId at hHonestEndpoint ⊢
    unfold credChannelEndpointPort Qsag.Spec.CredParty.port
    rw [decide_eq_false hHonestEndpoint]
    have hNe0 : ¬ (2 + i = 0) := by omega
    have hNe1 : ¬ (2 + i = 1) := by omega
    have hLt : 2 + i < 2 + Qsag.Spec.pqCredentialProfile.toprfServers := by omega
    have hSub : 2 + i - 2 = i := by omega
    simp only [Bool.false_eq_true, ↓reduceIte, hNe0, hNe1, hLt, hSub]
  | holder h =>
    unfold credPartyEndpointId at hHonestEndpoint ⊢
    unfold credChannelEndpointPort Qsag.Spec.CredParty.port
    rw [decide_eq_false hHonestEndpoint]
    have hSrvPos : 0 < Qsag.Spec.pqCredentialProfile.toprfServers := by decide
    have hNe0 : ¬ (2 + Qsag.Spec.pqCredentialProfile.toprfServers + h = 0) := by omega
    have hNe1 : ¬ (2 + Qsag.Spec.pqCredentialProfile.toprfServers + h = 1) := by omega
    have hNotLt : ¬ (2 + Qsag.Spec.pqCredentialProfile.toprfServers + h <
        2 + Qsag.Spec.pqCredentialProfile.toprfServers) := by omega
    have hSub : 2 + Qsag.Spec.pqCredentialProfile.toprfServers + h -
        (2 + Qsag.Spec.pqCredentialProfile.toprfServers) = h := by omega
    simp only [Bool.false_eq_true, ↓reduceIte, hNe0, hNe1, hNotLt, hSub]

theorem credChannelEndpointPort_unique_sender
    (adversaryIds : List Nat) (senderId : Nat) (party : Qsag.Spec.CredParty)
    (_hBound : CredPartyInCommittee party)
    (hPortEq : credChannelEndpointPort adversaryIds senderId = party.port) :
    senderId ∉ adversaryIds ∧ senderId = credPartyEndpointId party := by
  unfold credChannelEndpointPort at hPortEq
  cases hAdv : decide (senderId ∈ adversaryIds) with
  | true =>
    rw [hAdv] at hPortEq
    simp only [↓reduceIte] at hPortEq
    cases party <;> cases hPortEq
  | false =>
    have hNotAdv : senderId ∉ adversaryIds := of_decide_eq_false hAdv
    rw [hAdv] at hPortEq
    simp only [Bool.false_eq_true, ↓reduceIte] at hPortEq
    refine ⟨hNotAdv, ?_⟩
    by_cases h0 : senderId = 0
    · rw [h0] at hPortEq ⊢
      simp only [↓reduceIte] at hPortEq
      cases party with
      | issuer => rfl
      | server _ => cases hPortEq
      | holder _ => cases hPortEq
    · simp only [h0, ↓reduceIte] at hPortEq
      by_cases h1 : senderId = 1
      · rw [h1] at hPortEq
        simp only [↓reduceIte] at hPortEq
        cases party <;> cases hPortEq
      · simp only [h1, ↓reduceIte] at hPortEq
        by_cases hLt : senderId < 2 + Qsag.Spec.pqCredentialProfile.toprfServers
        · simp only [hLt, ↓reduceIte] at hPortEq
          cases party with
          | issuer => cases hPortEq
          | holder _ => cases hPortEq
          | server i =>
            dsimp only [credPartyEndpointId]
            injection hPortEq with hiEq
            omega
        · simp only [hLt, ↓reduceIte] at hPortEq
          cases party with
          | issuer => cases hPortEq
          | server _ => cases hPortEq
          | holder h =>
            dsimp only [credPartyEndpointId]
            have hSrvPos : 0 < Qsag.Spec.pqCredentialProfile.toprfServers := by decide
            injection hPortEq with hhEq
            omega

/-- **`CredPort` Authenticated by `Spec.AuthenticatedChannelContract`
    (`credPort_authenticated_by_channel_contract`)**:
    Discharges the authenticated-port assumption of `CredentialImplementation` from
    `Spec.AuthenticatedChannelContract admits` (inhabited by `Spec.checkedChannel_contract`):
    whenever a network event `tr = pre ++ .deliver m :: post` admitted by `admits` maps onto an
    authenticated party port `credChannelEndpointPort adversaryIds m.sender = party.port`:
    1. `m.sender` is uniquely that honest party's endpoint `credPartyEndpointId party` and
       `m.sender ∉ adversaryIds`,
    2. `party` genuinely transmitted `.send m ∈ pre` earlier in the trace, and
    3. `.deliver m ∉ post` (strict replay protection — `m` is never re-delivered)! -/
theorem credPort_authenticated_by_channel_contract
    {admits : List Qsag.Spec.ChannelEvent → Prop}
    (hContract : Qsag.Spec.AuthenticatedChannelContract admits)
    (adversaryIds : List Nat)
    {tr pre post : List Qsag.Spec.ChannelEvent} {m : Qsag.Spec.ChannelMsg}
    (hAdmits : admits tr)
    (hSplit : tr = pre ++ .deliver m :: post)
    (party : Qsag.Spec.CredParty) (hBound : CredPartyInCommittee party)
    (hPort : credChannelEndpointPort adversaryIds m.sender = party.port) :
    m.sender ∉ adversaryIds ∧
    m.sender = credPartyEndpointId party ∧
    Qsag.Spec.ChannelEvent.send m ∈ pre ∧
    Qsag.Spec.ChannelEvent.deliver m ∉ post := by
  obtain ⟨hNotAdv, hSenderEq⟩ :=
    credChannelEndpointPort_unique_sender adversaryIds m.sender party hBound hPort
  exact ⟨hNotAdv, hSenderEq,
    hContract.peerAuthenticated tr hAdmits pre post m hSplit,
    hContract.replayProtected tr hAdmits pre post m hSplit⟩

/-- `#tooth` Without `AuthenticatedChannelContract` (on an open relay `admits := fun _ => True`),
    an unauthenticated delivery forged with `m.sender = 0` arrives on `.issuer` with `.send m ∉ pre`
    and can even be replayed twice in `post`! -/
theorem tooth_open_relay_spoofs_issuer_credPort :
    ∃ (tr : List Qsag.Spec.ChannelEvent) (m : Qsag.Spec.ChannelMsg),
      ¬ Qsag.Spec.AuthenticatedChannelContract (fun _ => True) ∧
      tr = [] ++ .deliver m :: [.deliver m] ∧
      credChannelEndpointPort [99] m.sender = Qsag.Spec.CredPort.issuer ∧
      Qsag.Spec.ChannelEvent.deliver m ∈ [.deliver m] ∧
      Qsag.Spec.ChannelEvent.send m ∉ ([] : List Qsag.Spec.ChannelEvent) := by
  let m : Qsag.Spec.ChannelMsg := ⟨0, 1, 0, [0x42]⟩
  have hPort : credChannelEndpointPort [99] m.sender = Qsag.Spec.CredPort.issuer :=
    credChannelEndpointPort_roundtrip [99] .issuer trivial (by decide)
  exact ⟨[.deliver m, .deliver m], m, Qsag.Spec.open_relay_has_no_channel_contract,
    rfl, hPort, List.Mem.head _, fun h => nomatch h⟩

/-! ## 9. Canonical `Spec.Assumptions` Lattice & Regular-Dual-LPN Preprocessing Locale Bridge -/

/-- **Preprocessing Hardness Composition over `Spec.Assumptions`
    (`credential_preprocessing_lattice_and_lpn_assumptions_bound`)**:
    Connects the three preprocessing hardness locales of `Qsag.Spec.Assumptions`—`DecisionRlweHard`
    (negacyclic `ℤ_q[X]/(X^N + 1)` OT encryption), `ModuleSisHard` (ZKPoK / commitment binding),
    and `RegularDualLpnHard` (fixed quasi-cyclic tap matrix `H` over regular block noise)—directly
    into `Top.Credentials` `GameBound` guarantees! -/
theorem credential_preprocessing_lattice_and_lpn_assumptions_bound
    {𝒜Rlwe : (List (List Nat × List Nat) → Bool) → Prop}
    {𝒜Sis : (List (List (List Nat)) → List (List Nat)) → Prop}
    {𝒜Lpn : (List Bool → Bool) → Prop}
    {N q m βRlwe rows cols βSis blocks blockLen : Nat}
    {H : List (List Bool)}
    {εRlwe εSis εLpn : Qsag.Spec.RatBound}
    (hRlwe : Qsag.Spec.DecisionRlweHard 𝒜Rlwe N q m βRlwe εRlwe)
    (hSis : Qsag.Spec.ModuleSisHard 𝒜Sis N q rows cols βSis εSis)
    (hLpn : Qsag.Spec.RegularDualLpnHard 𝒜Lpn H blocks blockLen εLpn)
    {n nC nA : Nat} (hPos : 0 < n) (π : Qsag.Spec.CoinSplit n nC nA)
    (sRlwe : Fin nC → Qsag.Spec.RlweSample)
    (hURlwe : Qsag.Spec.UniformOn (Qsag.Spec.RlweSampleOk N q m βRlwe) sRlwe)
    (dRlwe : Fin nA → List (List Nat × List Nat) → Bool)
    (hDRlwe : ∀ a, 𝒜Rlwe (dRlwe a))
    (mSis : Fin nC → List (List (List Nat)))
    (hUSis : Qsag.Spec.UniformOn (Qsag.Spec.SisMatrixOk N q rows cols) mSis)
    (aSis : Fin nA → List (List (List Nat)) → List (List Nat))
    (hASis : ∀ a, 𝒜Sis (aSis a))
    (sLpn : Fin nC → Qsag.Spec.RegularDualLpnSample)
    (hULpn : Qsag.Spec.UniformOn
      (fun x : Qsag.Spec.RegularDualLpnSample =>
        Qsag.Spec.regularNoiseOk blocks blockLen x.noise = true ∧ x.uniform.length = H.length)
      sLpn)
    (dLpn : Fin nA → List Bool → Bool)
    (hDLpn : ∀ a, 𝒜Lpn (dLpn a)) :
    Qsag.Spec.GameBound
      (Qsag.Spec.AdvDist (Qsag.Spec.rlweRealGame hPos π N q m sRlwe dRlwe)
        (Qsag.Spec.rlweUniformGame hPos π m sRlwe dRlwe))
      εRlwe ∧
    Qsag.Spec.GameBound
      (Qsag.Spec.moduleSisGame hPos N q cols βSis
        (fun ω => mSis (π.chal ω)) (fun ω => aSis (π.advc ω))).winProb
      εSis ∧
    Qsag.Spec.GameBound
      (Qsag.Spec.AdvDist
        (Qsag.Spec.FinGame.mk hPos (fun ω => dLpn (π.advc ω)
          (Qsag.Spec.lpnSyndrome H (sLpn (π.chal ω)).noise)))
        (Qsag.Spec.FinGame.mk hPos (fun ω => dLpn (π.advc ω) (sLpn (π.chal ω)).uniform)))
      εLpn :=
  ⟨hRlwe.bound n nC nA hPos π sRlwe hURlwe dRlwe hDRlwe,
   hSis.bound n nC nA hPos π mSis hUSis aSis hASis,
   hLpn.bound n nC nA hPos π sLpn hULpn dLpn hDLpn⟩

/-- `#tooth` Degenerate `0`-row Module-SIS (`rows = 0`) is refuted for every nontrivial bound
    `ε < 1` (`Spec.moduleSisHard_noRows_refuted`), confirming `ModuleSisHard` is non-vacuous! -/
theorem tooth_degenerate_moduleSis_noRows_refuted
    (𝒜 : (List (List (List Nat)) → List (List Nat)) → Prop)
    (h𝒜 : 𝒜 (fun _ => [[1]]))
    {ε : Qsag.Spec.RatBound} (hε : ε.num < ε.den) :
    ¬ Qsag.Spec.ModuleSisHard 𝒜 1 2 0 1 1 ε :=
  Qsag.Spec.moduleSisHard_noRows_refuted 𝒜 h𝒜 hε

theorem inhabited_blindVc_cut_and_choose_gameBound :
    ∃ P : Qsag.CutAndChoose.Prover Qsag.BlindVcCommittedProof Qsag.BlindVcFp5
      Qsag.BlindVcR2aMsg Qsag.BlindVcFp5 Qsag.BlindVcR2bMsg,
      ∀ j : Nat, Qsag.BlindVcRepHasGateFault P.commit j :=
  ⟨Qsag.faultyBlindVcProver, Qsag.faultyBlindVcProver_has_gate_fault⟩

theorem inhabited_piToprfCredService_issuance :
    ∃ (cfg : Qsag.Spec.IdealCredConfig Nat)
      (c₀ c' : Qsag.PiToprfCredState Nat Nat)
      (tr : List ((Qsag.Spec.CredPort × Qsag.ToprfCredWire Nat) × Qsag.Spec.IdealCredOutput Nat))
      (w : Qsag.ToprfCredWire Nat),
      (Qsag.piToprfCredService cfg).Init c₀ ∧
      (Qsag.piToprfCredService cfg).ValidTrace c₀ tr c₀ ∧
      (Qsag.piToprfCredService cfg).step c₀ (.issuer, w) = some (c', .issued 0) := by
  let cfg := Qsag.Spec.idealCredDemoConfig false
  obtain ⟨c', hInit, hStep⟩ :=
    Qsag.piToprfCredService_issuer_issues_at_init (Attr := Nat) cfg 1 11 1#256 0xCAFE#256
  exact ⟨cfg, Qsag.PiToprfCredState.init cfg, c', [], .issueWire 1 [11] 1#256 0xCAFE#256,
    hInit, .nil _, hStep⟩

#verify_constructive
  Qsag.Top.threshold_mldsa_frozen_sacrifice_sign_step_soundness
  Qsag.Top.blindVc_cut_and_choose_gameBound
  Qsag.Top.blindVc_concrete_fp5_qrom_opening_soundness
  Qsag.Top.toprfCredentialImplementation_non_identity_state
  Qsag.Top.piToprfCredService_reservoir_never_resets
  Qsag.Top.piToprfCredMachine_reservoir_never_rewinds
  Qsag.Top.piToprfCredService_eval_accept_checks
  Qsag.Top.piToprfCredService_issuance_authenticated
  Qsag.Top.piToprfCredService_presentation_provenance
  Qsag.Top.piToprfCredService_toprf_provenance
  Qsag.Top.credPort_authenticated_by_channel_contract
  Qsag.Top.tooth_open_relay_spoofs_issuer_credPort
  Qsag.Top.credential_preprocessing_lattice_and_lpn_assumptions_bound
  Qsag.Top.tooth_degenerate_moduleSis_noRows_refuted
  Qsag.Top.inhabited_blindVc_cut_and_choose_gameBound
  Qsag.Top.inhabited_piToprfCredService_issuance

#verify_inhabited Qsag.Top.blindVc_cut_and_choose_gameBound
  Qsag.Top.inhabited_blindVc_cut_and_choose_gameBound
#verify_inhabited Qsag.Top.piToprfCredService_issuance_authenticated
  Qsag.Top.inhabited_piToprfCredService_issuance

#tooth_pair Qsag.Top.credPort_authenticated_by_channel_contract vs
  Qsag.Top.tooth_open_relay_spoofs_issuer_credPort
#tooth_pair Qsag.Top.piToprfCredService_issuance_authenticated vs
  Qsag.Top.unauthenticatedCredService_not_implementation
#tooth_pair Qsag.Top.piToprfCredMachine_reservoir_never_rewinds vs
  Qsag.tooth_reprepare_same_session_refused
#tooth_pair Qsag.Top.credential_preprocessing_lattice_and_lpn_assumptions_bound vs
  Qsag.Top.tooth_degenerate_moduleSis_noRows_refuted
#tooth_pair Qsag.Top.threshold_mldsa_frozen_sacrifice_sign_step_soundness vs
  Qsag.tooth_rssSacrificedSignStep_swapped_order_forges

-- Equations used by `Tests/CredentialsTeeth`; no body is exposed.
#export_eqns CredPartyInCommittee credPartyEndpointId

end Qsag.Top
end

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
   with the authenticated-possession soundness of the ideal credential functionality
   (`Spec.IdealCred`, `Spec.pqCredentialProfile`: `N = 256`, `33` repetitions over `GF(p^5)`), and
5. The refinement obligation `CredentialImplementation` under which a concrete credential service
   inherits authenticated issuance, authenticated possession and the ideal TOPRF gate.
   The tree has no concrete `PiBlindVc` state machine yet; that refinement is an explicit
   hypothesis of the theorems of section 5, not something proved here.
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

/-- **Anonymous Credential Authenticated-Possession Soundness & Fiat–Shamir Extraction
    (`blindVc_presentation_and_collision_extraction_chain`)**:
    Composes `Spec.idealCredMachine_presentation_sound` and
    `Spec.idealCredMachine_presentation_authenticated` (an accepted presentation in a reachable
    ideal state names the current epoch, uses a fresh challenge, and is backed by an
    issuer-authorized record of that epoch which the presented secret opens; `N = 256` parties and
    `33` repetitions over `GF(p^5)` in `Spec.pqCredentialProfile`) with
    `BlindVcCollisionFinder.blindVc_fs_collisionFinder_mass_bound` and
    `vcRewoundCollisionFinder_honest`. -/
theorem blindVc_presentation_and_collision_extraction_chain
    {Attr : Type} [DecidableEq Attr] (A : Qsag.Spec.CredAuthority Attr)
    (pk₀ : Qsag.Spec.Bytes) (epoch₀ : Nat) (root₀ : Qsag.Spec.Digest256)
    (st st' : Qsag.Spec.IdealCredState A)
    (secret : A.HolderSecret) (stmtCred : Qsag.Spec.CredentialStatement Attr)
    (hReach : (Qsag.Spec.idealCredMachine A pk₀ epoch₀ root₀).Reachable st)
    (hPresOk : (Qsag.Spec.idealCredMachine A pk₀ epoch₀ root₀).step st (.present secret stmtCred) =
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
      stmtCred.epoch = st.epoch ∧
      Qsag.Spec.DisclosedIndicesValid stmtCred = true ∧
      ∃ r ∈ st.records,
        A.opens secret r.leaf = true ∧
        r.epoch = stmtCred.epoch ∧
        Qsag.Spec.CredentialMatchesAttributes stmtCred r.attrs = true ∧
        A.issuerAuthorizes pk₀
          (.issue r.epoch r.leafIndex r.prevRoot r.leaf r.attrs r.root) r.auth = true) ∧
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
  obtain ⟨_, hEpoch, _, hFresh, _, hIdxOk, _⟩ :=
    Qsag.Spec.idealCredMachine_presentation_sound A pk₀ epoch₀ root₀ st st' secret stmtCred hPresOk
  obtain ⟨_, r, hr, hOpen, hREpoch, hMatch, _, hAuth⟩ :=
    Qsag.Spec.idealCredMachine_presentation_authenticated A pk₀ epoch₀ root₀ st st' secret stmtCred
      hReach hPresOk
  obtain ⟨_, _, hLimbo, hExt5, hReps33, _⟩ := Qsag.Spec.pqCredentialProfile_soundness_params
  exact ⟨⟨hFresh, hEpoch, hIdxOk, r, hr, hOpen, hREpoch, hMatch, hAuth⟩,
         ⟨hLimbo, hReps33, hExt5⟩,
         Qsag.blindVc_fs_collisionFinder_mass_bound H hHLen prgExpand stmtAt msgAt O seeds weight,
         Qsag.vcRewoundCollisionFinder_honest H hHLen nonce idx tr⟩

/-! ## 5. Refinement Obligation for a Concrete Credential Service -/

/-- What a concrete credential service must provide to inherit the guarantees of
    `Spec.idealCredMachine`: a state machine over the ideal command and output alphabets and a
    forward simulation into the ideal machine. `Spec.Refines` forces equal accept/reject behaviour,
    so the implementation must reject exactly the issuer commands whose authorization
    `A.issuerAuthorizes` rejects and the TOPRF tickets `IdealCredState.toprfAccepts` rejects, and
    return the ideal verdict for every presentation. -/
structure CredentialImplementation {Attr : Type} [DecidableEq Attr]
    (A : Qsag.Spec.CredAuthority Attr) (pk₀ : Qsag.Spec.Bytes) (epoch₀ : Nat)
    (root₀ : Qsag.Spec.Digest256) : Type 1 where
  State : Type
  machine : Qsag.Spec.Machine State (Qsag.Spec.IdealCredInput A)
    (Qsag.Spec.IdealCredOutput A.OprfOut)
  refines : Qsag.Spec.Refines machine (Qsag.Spec.idealCredMachine A pk₀ epoch₀ root₀)

/-- The ideal machine implements itself, so `CredentialImplementation` is inhabited for every
    authority. -/
def CredentialImplementation.ideal {Attr : Type} [DecidableEq Attr]
    (A : Qsag.Spec.CredAuthority Attr) (pk₀ : Qsag.Spec.Bytes) (epoch₀ : Nat)
    (root₀ : Qsag.Spec.Digest256) : CredentialImplementation A pk₀ epoch₀ root₀ where
  State := Qsag.Spec.IdealCredState A
  machine := Qsag.Spec.idealCredMachine A pk₀ epoch₀ root₀
  refines := Qsag.Spec.Refines.refl _

/-- Every state an implementation reaches is related to a reachable ideal state. -/
theorem CredentialImplementation.abstract_reachable {Attr : Type} [DecidableEq Attr]
    {A : Qsag.Spec.CredAuthority Attr} {pk₀ : Qsag.Spec.Bytes} {epoch₀ : Nat}
    {root₀ : Qsag.Spec.Digest256} (impl : CredentialImplementation A pk₀ epoch₀ root₀)
    {c₀ c : impl.State}
    {tr : List (Qsag.Spec.IdealCredInput A × Qsag.Spec.IdealCredOutput A.OprfOut)}
    (hInit : impl.machine.Init c₀) (hTrace : impl.machine.ValidTrace c₀ tr c) :
    ∃ a : Qsag.Spec.IdealCredState A,
      impl.refines.Rel c a ∧ (Qsag.Spec.idealCredMachine A pk₀ epoch₀ root₀).Reachable a := by
  obtain ⟨hInitA, hRel₀⟩ := impl.refines.init_ok hInit
  obtain ⟨a, hTraceA, hRel⟩ := impl.refines.lift_validTrace hRel₀ hTrace
  exact ⟨a, hRel, impl.refines.absInit c₀, tr, hInitA, hTraceA⟩

/-- An accepted step of an implementation is an accepted step, with the same output, of every
    ideal state related to it. -/
theorem CredentialImplementation.abstract_step {Attr : Type} [DecidableEq Attr]
    {A : Qsag.Spec.CredAuthority Attr} {pk₀ : Qsag.Spec.Bytes} {epoch₀ : Nat}
    {root₀ : Qsag.Spec.Digest256} (impl : CredentialImplementation A pk₀ epoch₀ root₀)
    {c c' : impl.State} {a : Qsag.Spec.IdealCredState A}
    {inp : Qsag.Spec.IdealCredInput A} {out : Qsag.Spec.IdealCredOutput A.OprfOut}
    (hRel : impl.refines.Rel c a) (hStep : impl.machine.step c inp = some (c', out)) :
    ∃ a' : Qsag.Spec.IdealCredState A,
      (Qsag.Spec.idealCredMachine A pk₀ epoch₀ root₀).step a inp = some (a', out) ∧
      impl.refines.Rel c' a' := by
  have hOk := impl.refines.sim_ok hRel hStep
  cases hA : (Qsag.Spec.idealCredMachine A pk₀ epoch₀ root₀).step a inp with
  | none =>
    rw [hA] at hOk
    exact False.elim hOk
  | some pair =>
    rw [hA] at hOk
    obtain ⟨a', outA⟩ := pair
    obtain ⟨hOut, hRel'⟩ := hOk
    rw [hOut]
    exact ⟨a', rfl, hRel'⟩

/-- **Authenticated possession for an implementation.** Whenever a service refining the ideal
    credential machine accepts a presentation after any run from an initial state, the statement
    names the issuer key `pk₀`, and the related ideal state holds a record of the statement's
    epoch that the presented secret opens, whose attributes satisfy the statement, and whose
    issuance the issuer authorized. -/
theorem credentialImplementation_presentation_authenticated {Attr : Type} [DecidableEq Attr]
    {A : Qsag.Spec.CredAuthority Attr} {pk₀ : Qsag.Spec.Bytes} {epoch₀ : Nat}
    {root₀ : Qsag.Spec.Digest256} (impl : CredentialImplementation A pk₀ epoch₀ root₀)
    {c₀ c c' : impl.State}
    {tr : List (Qsag.Spec.IdealCredInput A × Qsag.Spec.IdealCredOutput A.OprfOut)}
    (secret : A.HolderSecret) (stmt : Qsag.Spec.CredentialStatement Attr)
    (hInit : impl.machine.Init c₀) (hTrace : impl.machine.ValidTrace c₀ tr c)
    (hAccepted : impl.machine.step c (.present secret stmt) =
      some (c', .presentationVerdict true)) :
    stmt.issuerPk = pk₀ ∧
    ∃ a : Qsag.Spec.IdealCredState A, impl.refines.Rel c a ∧ stmt.epoch = a.epoch ∧
      ∃ r ∈ a.records,
        A.opens secret r.leaf = true ∧
        r.epoch = stmt.epoch ∧
        Qsag.Spec.CredentialMatchesAttributes stmt r.attrs = true ∧
        0 < r.attrs.length ∧
        A.issuerAuthorizes pk₀
          (.issue r.epoch r.leafIndex r.prevRoot r.leaf r.attrs r.root) r.auth = true := by
  obtain ⟨a, hRel, hReach⟩ := impl.abstract_reachable hInit hTrace
  obtain ⟨a', hStepA, _⟩ := impl.abstract_step hRel hAccepted
  obtain ⟨_, hEpoch, _⟩ :=
    Qsag.Spec.idealCredMachine_presentation_sound A pk₀ epoch₀ root₀ a a' secret stmt hStepA
  obtain ⟨hPk, r, hr, hRest⟩ :=
    Qsag.Spec.idealCredMachine_presentation_authenticated A pk₀ epoch₀ root₀ a a' secret stmt
      hReach hStepA
  exact ⟨hPk, a, hRel, hEpoch, r, hr, hRest⟩

/-- **Authenticated issuance for an implementation.** A service refining the ideal credential
    machine accepts an issuance only with an authorization of that exact issuance under `pk₀` at
    the related ideal state's epoch, leaf index and accumulator root, and only for a credential
    with between `1` and `maxAttrs` attributes. -/
theorem credentialImplementation_issuance_authenticated {Attr : Type} [DecidableEq Attr]
    {A : Qsag.Spec.CredAuthority Attr} {pk₀ : Qsag.Spec.Bytes} {epoch₀ : Nat}
    {root₀ : Qsag.Spec.Digest256} (impl : CredentialImplementation A pk₀ epoch₀ root₀)
    {c₀ c c' : impl.State}
    {tr : List (Qsag.Spec.IdealCredInput A × Qsag.Spec.IdealCredOutput A.OprfOut)}
    (leaf : A.Leaf) (attrs : List Attr) (newRoot : Qsag.Spec.Digest256) (auth : A.IssuerAuth)
    (out : Qsag.Spec.IdealCredOutput A.OprfOut)
    (hInit : impl.machine.Init c₀) (hTrace : impl.machine.ValidTrace c₀ tr c)
    (hAccepted : impl.machine.step c (.issue leaf attrs newRoot auth) = some (c', out)) :
    ∃ a : Qsag.Spec.IdealCredState A, impl.refines.Rel c a ∧
      A.issuerAuthorizes pk₀
        (.issue a.epoch a.issuedThisEpoch a.accumulatorRoot leaf attrs newRoot) auth = true ∧
      0 < attrs.length ∧ attrs.length ≤ Qsag.Spec.pqCredentialProfile.maxAttrs := by
  obtain ⟨a, hRel, hReach⟩ := impl.abstract_reachable hInit hTrace
  obtain ⟨a', hStepA, _⟩ := impl.abstract_step hRel hAccepted
  obtain ⟨hAuth, hPos, hMax, _⟩ :=
    Qsag.Spec.idealCredMachine_issuance_authenticated A pk₀ epoch₀ root₀ a a' leaf attrs newRoot
      auth out hStepA
  rw [(Qsag.Spec.idealCredInv_reachable hReach).issuerPk_eq] at hAuth
  exact ⟨a, hRel, hAuth, hPos, hMax⟩

/-- Tooth: a service refining the ideal credential machine never accepts an issuance whose
    authorization the issuer relation rejects for every action, whatever attributes and
    accumulator root the caller chooses. -/
theorem credentialImplementation_rejects_unauthorized_issue {Attr : Type} [DecidableEq Attr]
    {A : Qsag.Spec.CredAuthority Attr} {pk₀ : Qsag.Spec.Bytes} {epoch₀ : Nat}
    {root₀ : Qsag.Spec.Digest256} (impl : CredentialImplementation A pk₀ epoch₀ root₀)
    {c₀ c c' : impl.State}
    {tr : List (Qsag.Spec.IdealCredInput A × Qsag.Spec.IdealCredOutput A.OprfOut)}
    (leaf : A.Leaf) (attrs : List Attr) (newRoot : Qsag.Spec.Digest256) (auth : A.IssuerAuth)
    (out : Qsag.Spec.IdealCredOutput A.OprfOut)
    (hInit : impl.machine.Init c₀) (hTrace : impl.machine.ValidTrace c₀ tr c)
    (hForged : ∀ action : Qsag.Spec.IssuerAction Attr A.Leaf,
      A.issuerAuthorizes pk₀ action auth = false) :
    ¬ (impl.machine.step c (.issue leaf attrs newRoot auth) = some (c', out)) := by
  intro hAccepted
  obtain ⟨a, _, hAuth, _⟩ :=
    credentialImplementation_issuance_authenticated impl leaf attrs newRoot auth out hInit hTrace
      hAccepted
  rw [hForged] at hAuth
  cases hAuth

/-- **Ideal TOPRF gate for an implementation.** A service refining the ideal credential machine
    releases, for an accepted evaluation, exactly the value of the keyed function at
    `(keyId, epoch, input)`, and only for a ticket approved by at least `toprfThreshold` distinct
    servers with index below `toprfServers`. -/
theorem credentialImplementation_toprf_evaluation {Attr : Type} [DecidableEq Attr]
    {A : Qsag.Spec.CredAuthority Attr} {pk₀ : Qsag.Spec.Bytes} {epoch₀ : Nat}
    {root₀ : Qsag.Spec.Digest256} (impl : CredentialImplementation A pk₀ epoch₀ root₀)
    {c₀ c c' : impl.State}
    {tr : List (Qsag.Spec.IdealCredInput A × Qsag.Spec.IdealCredOutput A.OprfOut)}
    (t : Qsag.Spec.ToprfTicket) (input : Qsag.Spec.Bytes)
    (approvals : List (Nat × A.ServerAuth)) (out : Qsag.Spec.IdealCredOutput A.OprfOut)
    (hInit : impl.machine.Init c₀) (hTrace : impl.machine.ValidTrace c₀ tr c)
    (hAccepted : impl.machine.step c (.evalToprf t input approvals) = some (c', out)) :
    out = .toprfEvaluated (A.oprf ⟨t.keyId, t.epoch, input⟩) ∧
    (approvals.map Prod.fst).Nodup ∧
    (∀ p ∈ approvals, p.1 < Qsag.Spec.pqCredentialProfile.toprfServers ∧
      A.serverApproves p.1 t p.2 = true) ∧
    Qsag.Spec.pqCredentialProfile.toprfThreshold ≤ approvals.length := by
  obtain ⟨a, hRel, hReach⟩ := impl.abstract_reachable hInit hTrace
  obtain ⟨a', hStepA, _⟩ := impl.abstract_step hRel hAccepted
  obtain ⟨hOut, hNodup, hServers, hThreshold, _⟩ :=
    Qsag.Spec.idealCredMachine_toprf_evaluation A pk₀ epoch₀ root₀ a a' t input approvals out
      hReach hStepA
  exact ⟨hOut, hNodup, hServers, hThreshold⟩

/-- Tooth: a service refining the ideal credential machine releases no TOPRF value for fewer
    approvals than `toprfThreshold`. -/
theorem credentialImplementation_toprf_rejects_below_threshold {Attr : Type} [DecidableEq Attr]
    {A : Qsag.Spec.CredAuthority Attr} {pk₀ : Qsag.Spec.Bytes} {epoch₀ : Nat}
    {root₀ : Qsag.Spec.Digest256} (impl : CredentialImplementation A pk₀ epoch₀ root₀)
    {c₀ c c' : impl.State}
    {tr : List (Qsag.Spec.IdealCredInput A × Qsag.Spec.IdealCredOutput A.OprfOut)}
    (t : Qsag.Spec.ToprfTicket) (input : Qsag.Spec.Bytes)
    (approvals : List (Nat × A.ServerAuth)) (out : Qsag.Spec.IdealCredOutput A.OprfOut)
    (hInit : impl.machine.Init c₀) (hTrace : impl.machine.ValidTrace c₀ tr c)
    (hFew : approvals.length < Qsag.Spec.pqCredentialProfile.toprfThreshold) :
    ¬ (impl.machine.step c (.evalToprf t input approvals) = some (c', out)) := by
  intro hAccepted
  obtain ⟨_, _, _, hThreshold⟩ :=
    credentialImplementation_toprf_evaluation impl t input approvals out hInit hTrace hAccepted
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hFew hThreshold)

#verify_constructive
  Qsag.Top.pcg_dual_lpn_bias_in_spec_ratBound
  Qsag.Top.rlwe_preprocessing_and_sis_boundary_chain
  Qsag.Top.threshold_mldsa_hvzk_sacrifice_and_prss_chain
  Qsag.Top.blindVc_presentation_and_collision_extraction_chain
  Qsag.Top.CredentialImplementation.abstract_reachable
  Qsag.Top.CredentialImplementation.abstract_step
  Qsag.Top.credentialImplementation_presentation_authenticated
  Qsag.Top.credentialImplementation_issuance_authenticated
  Qsag.Top.credentialImplementation_toprf_evaluation

#tooth_pair Qsag.Top.credentialImplementation_issuance_authenticated vs
  Qsag.Top.credentialImplementation_rejects_unauthorized_issue
#tooth_pair Qsag.Top.credentialImplementation_toprf_evaluation vs
  Qsag.Top.credentialImplementation_toprf_rejects_below_threshold

end Qsag.Top
end

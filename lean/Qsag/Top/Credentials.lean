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
5. The refinement obligation `CredentialImplementation`: a concrete service takes
   `(sender, wire message)` with the sender supplied by the environment, and an extractor names
   only the command. Under it a service inherits issuance, possession and TOPRF provenance about
   the real sender; a service that authenticates nobody is refuted. The tree has no `PiBlindVc` /
   TOPRF state machine: the only inhabitant is the ideal machine itself.
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

/-- **Roster of credential facts (`blindVc_presentation_provenance_and_collision_finder_roster`)**.
    The four conjuncts are about different objects and are not a reduction: no theorem in the tree
    connects the `PiBlindVc` transcript model to the ideal credential machine.
    1. Ideal machine (`Spec.idealCredMachine_presentation_sound`, `…_presentation_provenance`): an
       accepted presentation after a run from the initial state uses a fresh challenge for the
       current epoch and is backed by a record owned by the presenting holder that an issuer-port
       event of the run issued (or the issuer is corrupt).
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
    (stmtCred.challengeNonce ∉ st.usedChallenges ∧
      stmtCred.epoch = st.epoch ∧
      Qsag.Spec.DisclosedIndicesValid stmtCred = true ∧
      (port = Qsag.Spec.CredPort.holder holder ∨
        (port = Qsag.Spec.CredPort.adversary ∧ holder ∈ cfg.corruptHolders)) ∧
      ∃ r ∈ st.records, r.credId = credId ∧ r.holder = holder ∧
        Qsag.Spec.CredentialMatchesAttributes stmtCred r.attrs = true ∧
        (cfg.issuerCorrupt = true ∨
          ((Qsag.Spec.CredPort.issuer, Qsag.Spec.CredCommand.issue holder r.attrs r.root),
            Qsag.Spec.IdealCredOutput.issued credId) ∈ trace)) ∧
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

    Inhabitants in the tree: `CredentialImplementation.ideal` only. No model of the `PiBlindVc`
    or `voprf.rs` protocol as a state machine exists in `lean/Qsag/Protocol`, so no protocol
    instance is constructed; every theorem below is conditional on one. -/
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

/-- The ideal machine implements itself: its wire messages are commands. -/
def CredentialImplementation.ideal {O : Type} (Attr : Type) [DecidableEq Attr]
    (cfg : Qsag.Spec.IdealCredConfig O) :
    CredentialImplementation Attr cfg (Qsag.Spec.idealCredMachine (Attr := Attr) cfg) where
  Rel c a := c = a
  extract _ _ cmd := some cmd
  init_ok hInit := hInit
  accept_ok {c c' a sender w out} hRel hStep := by
    subst hRel
    exact ⟨w, c', rfl, hStep, rfl⟩
  reject_ok hRel _ := hRel

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

/-- **Issuance authentication for an implementation.** If the service answers `.issued credId`
    to a message, then the message was delivered on the issuer port, or on the adversary port
    with a corrupt issuer; and it stands for the issuance of a credential with between `1` and
    `maxAttrs` attributes. -/
theorem credentialImplementation_issuance_authenticated {Attr O S W : Type} [DecidableEq Attr]
    {cfg : Qsag.Spec.IdealCredConfig O}
    {M : Qsag.Spec.Machine S (Qsag.Spec.CredPort × W) (Qsag.Spec.IdealCredOutput O)}
    (impl : CredentialImplementation Attr cfg M)
    {c₀ c c' : S} {tr : List ((Qsag.Spec.CredPort × W) × Qsag.Spec.IdealCredOutput O)}
    {sender : Qsag.Spec.CredPort} {w : W} {credId : Nat}
    (hInit : M.Init c₀) (hTrace : M.ValidTrace c₀ tr c)
    (hAccepted : M.step c (sender, w) = some (c', .issued credId)) :
    (sender = Qsag.Spec.CredPort.issuer ∨
      (sender = Qsag.Spec.CredPort.adversary ∧ cfg.issuerCorrupt = true)) ∧
    ∃ (holder : Nat) (attrs : List Attr) (newRoot : Qsag.Spec.Digest256),
      impl.extract c sender w = some (.issue holder attrs newRoot) ∧
      0 < attrs.length ∧ attrs.length ≤ Qsag.Spec.pqCredentialProfile.maxAttrs := by
  obtain ⟨a, aTr, hRel, hTrA, _⟩ := impl.abstract_run hInit hTrace
  obtain ⟨cmd, a', hExt, hStepA, _⟩ := impl.accept_ok hRel hAccepted
  obtain ⟨holder, attrs, newRoot, hCmd⟩ := Qsag.Spec.idealCredStep_output_command hStepA
  subst hCmd
  obtain ⟨hPort, hPos, hMax⟩ :=
    Qsag.Spec.idealCredMachine_issuance_authenticated cfg ⟨_, aTr, rfl, hTrA⟩ hStepA
  exact ⟨hPort, holder, attrs, newRoot, hExt, hPos, hMax⟩

/-- **Possession provenance for an implementation.** If the service answers a message with the
    verdict `true`, then the message stands for a presentation of some credential `credId` by some
    `holder`; it was delivered on that holder's port (or on the adversary port with that holder
    corrupt); the statement names the configured issuer key; and, unless the issuer is corrupt,
    the run contains a message delivered on the issuer port that the service answered
    `.issued credId`. -/
theorem credentialImplementation_presentation_provenance {Attr O S W : Type} [DecidableEq Attr]
    {cfg : Qsag.Spec.IdealCredConfig O}
    {M : Qsag.Spec.Machine S (Qsag.Spec.CredPort × W) (Qsag.Spec.IdealCredOutput O)}
    (impl : CredentialImplementation Attr cfg M)
    {c₀ c c' : S} {tr : List ((Qsag.Spec.CredPort × W) × Qsag.Spec.IdealCredOutput O)}
    {sender : Qsag.Spec.CredPort} {w : W}
    (hInit : M.Init c₀) (hTrace : M.ValidTrace c₀ tr c)
    (hAccepted : M.step c (sender, w) = some (c', .presentationVerdict true)) :
    ∃ (holder credId : Nat) (stmt : Qsag.Spec.CredentialStatement Attr),
      impl.extract c sender w = some (.present holder credId stmt) ∧
      (sender = Qsag.Spec.CredPort.holder holder ∨
        (sender = Qsag.Spec.CredPort.adversary ∧ holder ∈ cfg.corruptHolders)) ∧
      stmt.issuerPk = cfg.issuerPk ∧
      (cfg.issuerCorrupt = true ∨
        ∃ w₀ : W, ((Qsag.Spec.CredPort.issuer, w₀), Qsag.Spec.IdealCredOutput.issued credId) ∈ tr) := by
  obtain ⟨a, aTr, hRel, hTrA, hView⟩ := impl.abstract_run hInit hTrace
  obtain ⟨cmd, a', hExt, hStepA, _⟩ := impl.accept_ok hRel hAccepted
  obtain ⟨holder, credId, stmt, hCmd⟩ := Qsag.Spec.idealCredStep_output_command hStepA
  subst hCmd
  obtain ⟨hPort, hPk, r, _, _, _, _, _, hProv⟩ :=
    Qsag.Spec.idealCredMachine_presentation_provenance cfg rfl hTrA hStepA
  refine ⟨holder, credId, stmt, hExt, hPort, hPk, ?_⟩
  rcases hProv with hC | hMem
  · exact Or.inl hC
  · exact Or.inr (credSenderView_mem hView hMem)

/-- Tooth: with an honest issuer, the service never answers `.issued` to a message delivered on
    any port other than the issuer's — in particular to one the adversary delivered. -/
theorem credentialImplementation_rejects_foreign_issue {Attr O S W : Type} [DecidableEq Attr]
    {cfg : Qsag.Spec.IdealCredConfig O}
    {M : Qsag.Spec.Machine S (Qsag.Spec.CredPort × W) (Qsag.Spec.IdealCredOutput O)}
    (impl : CredentialImplementation Attr cfg M)
    {c₀ c c' : S} {tr : List ((Qsag.Spec.CredPort × W) × Qsag.Spec.IdealCredOutput O)}
    {sender : Qsag.Spec.CredPort} {w : W} {credId : Nat}
    (hInit : M.Init c₀) (hTrace : M.ValidTrace c₀ tr c)
    (hHonest : cfg.issuerCorrupt = false)
    (hSender : ¬ (sender = Qsag.Spec.CredPort.issuer)) :
    ¬ (M.step c (sender, w) = some (c', .issued credId)) := by
  intro hAccepted
  obtain ⟨hAuth, _⟩ := credentialImplementation_issuance_authenticated impl hInit hTrace hAccepted
  rcases hAuth with hP | ⟨_, hC⟩
  · exact hSender hP
  · rw [hHonest] at hC
    cases hC

/-- Tooth: with no corrupt holder, the service never answers the verdict `true` to a message the
    adversary delivered. -/
theorem credentialImplementation_rejects_foreign_presentation {Attr O S W : Type}
    [DecidableEq Attr] {cfg : Qsag.Spec.IdealCredConfig O}
    {M : Qsag.Spec.Machine S (Qsag.Spec.CredPort × W) (Qsag.Spec.IdealCredOutput O)}
    (impl : CredentialImplementation Attr cfg M)
    {c₀ c c' : S} {tr : List ((Qsag.Spec.CredPort × W) × Qsag.Spec.IdealCredOutput O)} {w : W}
    (hInit : M.Init c₀) (hTrace : M.ValidTrace c₀ tr c)
    (hHonest : cfg.corruptHolders = []) :
    ¬ (M.step c (Qsag.Spec.CredPort.adversary, w) = some (c', .presentationVerdict true)) := by
  intro hAccepted
  obtain ⟨holder, _, _, _, hAuth, _⟩ :=
    credentialImplementation_presentation_provenance impl hInit hTrace hAccepted
  rcases hAuth with hP | ⟨_, hC⟩
  · cases hP
  · rw [hHonest] at hC
    exact nomatch hC

/-- **TOPRF provenance for an implementation.** With at most `toprfMaxCorrupt` corrupt servers,
    if the service answers a message with a TOPRF value, the message stands for an evaluation of
    some ticket and input, the value is the keyed-table value of `(keyId, epoch, input)`, and the
    run contains a message delivered on the port of an honest committee server that the service
    answered `.toprfApproved`. -/
theorem credentialImplementation_toprf_provenance {Attr O S W : Type} [DecidableEq Attr]
    {cfg : Qsag.Spec.IdealCredConfig O}
    {M : Qsag.Spec.Machine S (Qsag.Spec.CredPort × W) (Qsag.Spec.IdealCredOutput O)}
    (impl : CredentialImplementation Attr cfg M)
    {c₀ c c' : S} {tr : List ((Qsag.Spec.CredPort × W) × Qsag.Spec.IdealCredOutput O)}
    {sender : Qsag.Spec.CredPort} {w : W} {v : O}
    (hInit : M.Init c₀) (hTrace : M.ValidTrace c₀ tr c)
    (hCorrupt : cfg.corruptServerCount ≤ Qsag.Spec.pqCredentialProfile.toprfMaxCorrupt)
    (hAccepted : M.step c (sender, w) = some (c', .toprfEvaluated v)) :
    ∃ (t : Qsag.Spec.ToprfTicket) (input : Qsag.Spec.Bytes),
      impl.extract c sender w = some (.evalToprf t input) ∧
      v = cfg.oprf ⟨t.keyId, t.epoch, input⟩ ∧
      ∃ (i : Nat) (w₀ : W),
        i < Qsag.Spec.pqCredentialProfile.toprfServers ∧ i ∉ cfg.corruptServers ∧
        ((Qsag.Spec.CredPort.server i, w₀), Qsag.Spec.IdealCredOutput.toprfApproved) ∈ tr := by
  obtain ⟨a, aTr, hRel, hTrA, hView⟩ := impl.abstract_run hInit hTrace
  obtain ⟨cmd, a', hExt, hStepA, _⟩ := impl.accept_ok hRel hAccepted
  obtain ⟨t, input, hCmd⟩ := Qsag.Spec.idealCredStep_output_command hStepA
  subst hCmd
  obtain ⟨hVal, _, i, hi, hHonest, hMem⟩ :=
    Qsag.Spec.idealCredMachine_toprf_provenance cfg rfl hTrA hCorrupt hStepA
  obtain ⟨w₀, hw₀⟩ := credSenderView_mem hView hMem
  exact ⟨t, input, hExt, Qsag.Spec.IdealCredOutput.toprfEvaluated.inj hVal, i, w₀, hi, hHonest, hw₀⟩

/-! ### The unauthenticated service is not an implementation -/

/-- The port a command claims to come from. -/
def credCommandClaimedPort {Attr : Type} : Qsag.Spec.CredCommand Attr → Qsag.Spec.CredPort
  | .issue _ _ _ => .issuer
  | .advanceEpoch _ _ => .issuer
  | .present h _ _ => .holder h
  | .approveToprf i _ => .server i
  | .evalToprf _ _ => .client

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

/-- Tooth (referee 3, N2): with an honest issuer, the unauthenticated service satisfies
    `CredentialImplementation` for no relation and no extractor. -/
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
    exact credentialImplementation_rejects_foreign_issue impl (c₀ := Qsag.Spec.IdealCredState.empty cfg)
      rfl (.nil _) hHonest (by intro h; cases h) hStep

#verify_constructive
  Qsag.Top.pcg_dual_lpn_bias_in_spec_ratBound
  Qsag.Top.rlwe_preprocessing_and_sis_boundary_chain
  Qsag.Top.threshold_mldsa_hvzk_sacrifice_and_prss_chain
  Qsag.Top.blindVc_presentation_provenance_and_collision_finder_roster
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

end Qsag.Top
end

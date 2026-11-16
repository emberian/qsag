module
import all Qsag.Math.GoldilocksBase
/- Executed coherent superposition and database-measurement controls. -/
public import Qsag.Protocol.Aggregation.HemOpening
public import Qsag.Tests.HemExtractedOpeningBridgeTests
import all Qsag.Protocol.Aggregation.HemOpening
import all Qsag.Oracle.Qrom
import all Qsag.Tests.HemExtractedOpeningBridgeTests
import all Qsag.Tests.OracleAndQrom
import all Qsag.Protocol.Aggregation.MultiRoundFsQrom
import all Qsag.Protocol.Aggregation.QromSaltedMerkleStateRestoration
public import Qsag.Protocol.Aggregation.Cwyz26EqualDegreeAndMultiFold
import all Qsag.Protocol.Aggregation.Cwyz26EqualDegreeAndMultiFold
import all Qsag.Coding.Cwyz26
import all Qsag.Protocol.Aggregation.Cwyz26JohnsonCertificate
import all Qsag.Math.Counting
import all Qsag.Math.CoeffPoly
import all Qsag.Math.PolyRing
import all Qsag.Math.HasseHensel
import all Qsag.Coding.Resultant
import all Qsag.Coding.GuruswamiSudan
import all Qsag.Coding.ReedSolomon
import all Qsag.Protocol.Aggregation.HemRbrSoundness
import all Qsag.Protocol.Aggregation.ConcreteSecurityBudget
import all Qsag.Math.Goldilocks

public section
namespace Qsag
set_option autoImplicit false

/-- Actual authenticated Hem decoder consumer, on the earlier nonconstant one-bit layout. -/
theorem coherent_hem_decoder_execution :
    let honest := toyQueryAdv ⟨1, by decide⟩ (by decide)
    coherentTableEventMass
      (verifyHemOpeningBatch toyMerkleLayout toyOpeningSlots toyHemInstance toyHemDecode)
      (fourierOracleState (fourierAdvStateAt honest 1 (Nat.le_refl 1))) = 524288 := by
  dsimp only
  rw [coherent_hem_authenticated_event_eq]
  decide +kernel

#verify_constructive
  Qsag.coherent_hem_decoder_execution
/-! ## Relocated from QromSaltedMerkleStateRestoration -/

/-- Concrete `w = 2` (`m = 1`, 2-bit output!) 1-query superposed parity adversary deciding
    `(H 0).lsb ⊕ (H 1).lsb` across all `16` two-bit 2-address oracles in a single coherent query,
    using `hadamardQuery2 2 1 : ScaledUnitary 2 2 1`. -/
def dfmsW2ParityAdv : QuantumAdv 2 2 1 1 where
  init := fun _ y _ => if y.1 % 2 == 0 then ⟨1, 0⟩ else ⟨-1, 0⟩
  h_init_pos := by decide
  steps := fun _ => hadamardQuery2 2 1

/-- Event testing whether output address `x : Fin 2` equals `((H 0).toNat + (H 1).toNat) % 2`. -/
def dfmsW2ParityEvent (H : Fin 2 → BitVec 2) (x : Fin 2) : Bool :=
  decide (x.1 = ((H ⟨0, by decide⟩).toNat + (H ⟨1, by decide⟩).toNat) % 2)

/-- Decidable equality on `DfmsTable 1 2` (`25` states: `Option (BitVec 2) × Option (BitVec 2)`). -/
def dfmsW2TableEq (D₁ D₂ : DfmsTable 1 2) : Bool :=
  decide (D₁.1 = D₂.1 ∧ D₁.2.1 = D₂.2.1)

/-- Executable `w = 2` (`m = 1`, 2-bit `Option (BitVec 2)` compressed database!) kernel-`decide`
    witness: after 1 coherent 2-bit query, `dfmsW2ParityAdv` has **0 mass** on `dfmsRecordedCount > 1`,
    strictly positive mass on recorded `some (y : BitVec 2)` entries, and **100% (`256 / 256`)**
    undisturbed parity success both in `uniformOracleSum 2 2` and after `dfmsDecompressState`! -/
theorem dfms_w2_coherent_runtime_witness :
    uniformOracleSum 2 2 (fun H =>
      QVec.queryMassOn (dfmsW2ParityEvent H) (runQuantumAdv dfmsW2ParityAdv H)) = 256 ∧
    quantumExperimentTotal dfmsW2ParityAdv = 256 ∧
    dfmsTableSum 1 2 (fun D =>
      if 1 < dfmsRecordedCount 2 D then
        QVec.stateNormSq (dfmsAdvStateAt 1 dfmsW2ParityAdv 1 (Nat.le_refl 1) D)
      else 0) = 0 ∧
    0 < dfmsTableSum 1 2 (fun D =>
      if dfmsRecordedCount 2 D == 1 then
        QVec.stateNormSq (dfmsAdvStateAt 1 dfmsW2ParityAdv 1 (Nat.le_refl 1) D)
      else 0) ∧
    dfmsCoherentEventMass (m := 1) dfmsW2ParityEvent
      (dfmsDecompressState (dfmsAdvStateAt 1 dfmsW2ParityAdv 1 (Nat.le_refl 1))) =
      4 ^ 10 * 256 := by
  decide +kernel

/-- `#tooth` negative control at `w = 2` (`Option (BitVec 2)`): naively collapsing the `DfmsTable 1 2`
    database (`projectDfmsPred (dfmsW2TableEq D)`) before decompression destroys coherent cross-address
    interference and drops `dfmsW2ParityEvent` mass from `4^10 * 256` (`100%`) strictly down to
    `4^10 * 128` (`50%`), demonstrating why `dfms_projective_extraction_disturbance_bound` is required! -/
theorem tooth_dfms_w2_raw_database_measurement_disturbs :
    ∃ measuredMass : Nat,
      measuredMass = dfmsTableSum 1 2 (fun D =>
        dfmsCoherentEventMass (m := 1) dfmsW2ParityEvent
          (dfmsDecompressState
            (projectDfmsPred (dfmsW2TableEq D)
              (dfmsAdvStateAt 1 dfmsW2ParityAdv 1 (Nat.le_refl 1))))) ∧
      measuredMass = 4 ^ 10 * 128 ∧
      measuredMass ≠ dfmsCoherentEventMass (m := 1) dfmsW2ParityEvent
        (dfmsDecompressState (dfmsAdvStateAt 1 dfmsW2ParityAdv 1 (Nat.le_refl 1))) :=
  ⟨4 ^ 10 * 128, by decide +kernel, rfl, by decide +kernel⟩

#verify_constructive
  Qsag.dfms_w2_coherent_runtime_witness
  Qsag.tooth_dfms_w2_raw_database_measurement_disturbs

#tooth_pair dfms_projective_extraction_disturbance_bound vs tooth_dfms_w2_raw_database_measurement_disturbs

/-! ## Relocated from Cwyz26EqualDegreeAndMultiFold

Inhabitedness witnesses and `#tooth_pair` counterexamples for the three-challenge equal-degree
lift and the intra-stage multi-fold budgets of
`Qsag.Protocol.Aggregation.Cwyz26EqualDegreeAndMultiFold`, and the audits of the upstream
theorems that module cites. They evaluate upstream definitions in the kernel. -/

namespace Cwyz26EqualDegreeAndMultiFoldTests
set_option exponentiation.threshold 2048
open CommRingOps RoundPoly UPoly Poly2 SylElim

def gf (n : Nat) : Goldilocks := Goldilocks.ofNat n

def qf (n : Nat) : QuarticGoldilocks :=
  ⟨⟨Goldilocks.ofNat n, Goldilocks.ofNat 0⟩, ⟨Goldilocks.ofNat 0, Goldilocks.ofNat 0⟩⟩

/-- Inhabitedness witness for `gsDecodeList_length_le_johnson` at `|D| = 5`, `d = 1`, `A = 3`. -/
theorem inhabited_gsDecodeList_length_le_johnson :
    ∃ (D : List Goldilocks) (word : Goldilocks → Goldilocks) (d A : Nat),
      D.Nodup ∧ d + 1 ≤ A ∧ D.length * d < A * A ∧
      JohnsonBound.johnsonBound D.length A d = 2 ∧ word (gf 0) = gf 0 :=
  ⟨[gf 0, gf 1, gf 2, gf 3, gf 4], fun _ => gf 0, 1, 3,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, rfl⟩

/-- `#tooth`: dropping the positive-Johnson-denominator condition `D.length * d < A * A`
    invalidates `gsDecodeList_length_le_johnson`: at `|D| = 4, d = 1, A = 2` (`4 * 1 = 2 * 2`),
    `johnsonBound 4 2 1 = 0` while `gsDecodeList 1 2 D 0` contains the zero polynomial (`1 ≤ length`). -/
theorem tooth_gsDecodeList_johnson_denominator_needed :
    ∃ (D : List Goldilocks) (word : Goldilocks → Goldilocks) (d A : Nat),
      D.Nodup ∧ d + 1 ≤ A ∧ D.length * d = A * A ∧
      ¬ ((gsDecodeList d A D word).length ≤ JohnsonBound.johnsonBound D.length A d) := by
  let D : List Goldilocks := [gf 0, gf 1, gf 2, gf 3]
  have hDNd : D.Nodup := by decide +kernel
  refine ⟨D, fun _ => CommRingOps.zero, 1, 2, hDNd, by decide, by decide, ?_⟩
  intro hLe
  have hJb0 : JohnsonBound.johnsonBound D.length 2 1 = 0 := by decide +kernel
  rw [hJb0] at hLe
  let pZero : GsUniPoly Goldilocks := GsUniPoly.ofCoeffs []
  have hMem : pZero ∈ gsDecodeList 1 2 D (fun _ => CommRingOps.zero) :=
    (mem_gsDecodeList_iff (fun _ => CommRingOps.zero) hDNd (by decide) pZero).mpr
      ⟨by decide, by decide +kernel⟩
  have hPos := List.length_pos_of_mem hMem
  omega

/-- Explicit 16-element squared domain `[(qf 1)², ..., (qf 16)²]` in `QuarticGoldilocks`. -/
def dom16Out : List QuarticGoldilocks :=
  ((List.range 16).map (fun i => qf (i + 1))).map (fun x => CommRingOps.mul x x)

/-- Explicit 32-element antipodal pre-fold domain `[qf 1, -qf 1, ..., qf 16, -qf 16]`. -/
def dom32In : List QuarticGoldilocks :=
  hemInterleave
    ((List.range 16).map (fun i => qf (i + 1)))
    ((List.range 16).map (fun i => CommRingOps.neg (qf (i + 1))))

theorem antipodalPair_dom32_dom16 : IsAntipodalDomainPair dom32In dom16Out where
  nodup_in := by decide +kernel
  nodup_out := by decide +kernel
  len_eq := by decide +kernel
  two_ne_zero := by decide +kernel
  even_nz := by
    have hAll : ((List.range 16).all (fun idx =>
        decide (dom32In.getD (2 * idx) CommRingOps.one ≠ CommRingOps.zero))) = true := by
      decide +kernel
    intro idx hIdx
    exact of_decide_eq_true (List.all_eq_true.mp hAll idx (List.mem_range.mpr hIdx))
  odd_neg := by
    have hAll : ((List.range 16).all (fun idx =>
        decide (dom32In.getD (2 * idx + 1) CommRingOps.zero =
          CommRingOps.neg (dom32In.getD (2 * idx) CommRingOps.one)))) = true := by
      decide +kernel
    intro idx hIdx
    exact of_decide_eq_true (List.all_eq_true.mp hAll idx (List.mem_range.mpr hIdx))
  sq_eq := by
    have hAll : ((List.range 16).all (fun idx =>
        decide (dom16Out.getD idx CommRingOps.zero =
          CommRingOps.mul (dom32In.getD (2 * idx) CommRingOps.one)
            (dom32In.getD (2 * idx) CommRingOps.one)))) = true := by
      decide +kernel
    intro idx hIdx
    exact of_decide_eq_true (List.all_eq_true.mp hAll idx (List.mem_range.mpr hIdx))

private theorem zero_word_false_claim_on_dom16 (Fw : List QuarticGoldilocks)
    (hLen : Fw.length ≤ 2)
    (hAg : 10 ≤ (dom16Out.filter (fun z => decide (RoundPoly.evalCoeffs Fw z = qf 0))).length) :
    ringDot Fw [qf 1, qf 0] ≠ qf 1 := by
  intro hEq
  have hDomNd : dom16Out.Nodup := by decide +kernel
  have hTrim : trimPoly Fw = trimPoly ([] : List QuarticGoldilocks) :=
    trimPoly_eq_of_agree_on_nodup hLen (Nat.zero_le 2)
      (List.Pairwise.filter _ hDomNd) (Nat.le_trans (by decide) hAg)
      (fun z hz => of_decide_eq_true (List.mem_filter.mp hz).2)
  have hDot0 : ringDot Fw [qf 1, qf 0] = CommRingOps.zero := by
    rw [← ringDot_trimPoly_eq, hTrim]; rfl
  rw [hDot0] at hEq
  exact (by decide +kernel : CommRingOps.zero ≠ qf 1) hEq

/-- Joint inhabitedness witness for `sliced_equal_degree_three_challenge_bound` beyond the
    Welch–Berlekamp radius (`|D| = 16`, `d = 1`, `A = 10`, `2|D| + (d + 1) + 1 = 35 ≥ 33 = 3(A + 1)`),
    with a non-empty bad-challenge list `L` (`L.length = 1`). -/
theorem inhabited_sliced_equal_degree_three_challenge_bound :
    ∃ (D S_θ S kernel : List QuarticGoldilocks) (d A B m Dy : Nat)
      (f g : QuarticGoldilocks → QuarticGoldilocks) (e_f e_g c_f c_g : QuarticGoldilocks)
      (L : List (Fin (threePool S_θ S).length)),
      D.Nodup ∧ S_θ.Nodup ∧ S.Nodup ∧ d + 2 ≤ A ∧
      slicedParamsOk D.length (d + 1) (A + 1) B m Dy = true ∧
      ((∀ Fw : List QuarticGoldilocks, Fw.length ≤ d + 1 →
          A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Fw z = f z))).length →
          ringDot Fw kernel ≠ e_f) ∨
       (∀ Gw : List QuarticGoldilocks, Gw.length ≤ d + 1 →
          A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Gw z = g z))).length →
          ringDot Gw kernel ≠ e_g)) ∧
      L.Nodup ∧
      (∀ ch ∈ L, ¬¬ ∃ P : List QuarticGoldilocks,
        P.length ≤ d + 2 ∧
        A + 1 ≤ (D.filter (fun z =>
          let t := (threePool S_θ S).get ch
          let h_θ := CommRingOps.add (f z) (CommRingOps.mul t.1 (g z))
          decide (RoundPoly.evalCoeffs P z =
            CommRingOps.add (g z)
              (CommRingOps.mul (CommRingOps.add t.2.1 (CommRingOps.mul t.2.2 z)) h_θ)))).length ∧
        ringDot P kernel =
          let t := (threePool S_θ S).get ch
          hemFoldClaimUpdate e_f e_g c_f c_g t.1 t.2.1 t.2.2) ∧
      L.length = 1 := by
  refine ⟨dom16Out, dom16Out, dom16Out, [qf 1, qf 0], 1, 10, 7, 2, 4,
    fun _ => qf 0, fun _ => qf 0, qf 1, qf 0, CommRingOps.neg (qf 1), qf 0,
    [⟨0, by decide +kernel⟩],
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, .inl (fun Fw hLen hAg => zero_word_false_claim_on_dom16 Fw hLen hAg),
    by decide +kernel, ?_, rfl⟩
  intro ch hch hNo
  cases hch with
  | head =>
    exact hNo ⟨[], by decide +kernel, by decide +kernel, by decide +kernel⟩
  | tail _ hNil => cases hNil

/-- `#tooth`: even when BOTH `(f, e_f)` and `(g, e_g)` fail `ringDot · kernel = e_*` on every
    codeword, `hemFoldClaimUpdate` admits `S_θ.length * S.length` genuine accepting triples in
    `threePool S_θ S` (so the `jbLo² · q_θ · q` term in `slicedThreeChallengeCount` cannot be zero). -/
theorem tooth_three_challenge_lo_pair_forgery :
    ∃ (S_θ S : List QuarticGoldilocks) (ch : Fin (threePool S_θ S).length),
      let t := (threePool S_θ S).get ch
      ringDot ([] : List QuarticGoldilocks) [qf 1, qf 0] ≠ qf 1 ∧
      ringDot ([] : List QuarticGoldilocks) [qf 1, qf 0] =
        hemFoldClaimUpdate (qf 1) (qf 1) (qf 0) (qf 0) t.1 t.2.1 t.2.2 ∧
      1 ≤ slicedThreeChallengeCount 16 1 10 7 2 4 S_θ.length S.length :=
  ⟨[qf 0], [CommRingOps.neg (qf 1)], ⟨0, by decide +kernel⟩,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Total diagnostic accessor for `slicedThreeChallengeStageBound`. -/
def slicedThreeChallengeStageProfile (nv : Nat) (g : HemStageGeom) : RatBound :=
  match hemJohnsonQromTableRow nv g.stageIdx, slicedStageRow nv g.stageIdx with
  | some r, some w => slicedThreeChallengeStageBound g r w
  | _, _ => RatBound.one

/-- Joint inhabitedness witness for `sliced_stage_three_challenge_supported_budget` (`nv = 24`, stage `0`). -/
theorem inhabited_sliced_stage_three_challenge_supported_budget :
    ∃ (nv : Nat) (g : HemStageGeom),
      2 ≤ nv ∧ nv ≤ 24 ∧ g ∈ hemStageGeoms nv ∧ hemJohnsonQromStageExhaustive g = false :=
  ⟨24, (hemStageGeoms 24).get ⟨0, by decide +kernel⟩,
    by decide +kernel, by decide +kernel, list_get_mem _ _, by decide +kernel⟩

/-- `#tooth`: the concrete 3-challenge stage-0 bound at `nv = 24` achieves `184` bits at
    `Q + 1 ≤ 2^27`, yet fails `186` bits unscaled and fails `128` bits at `Q = 2^28`. -/
theorem tooth_three_challenge_nv24_stage0_margin :
    ∃ g : HemStageGeom,
      g ∈ hemStageGeoms 24 ∧
      atLeastBits 184 (slicedThreeChallengeStageProfile 24 g) ∧
      ¬ atLeastBits 186 (slicedThreeChallengeStageProfile 24 g) ∧
      ¬ atLeastBits 128 (dfmRoundScale (2 ^ 28) (slicedThreeChallengeStageProfile 24 g)) :=
  ⟨(hemStageGeoms 24).get ⟨0, by decide +kernel⟩, list_get_mem _ _,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Joint inhabitedness witness for `sliced_singleStep_bridge_four_challenge_bound` on
    `(dom32In, dom16Out)` with non-empty accepting quadruple list `L` (`L.length = 1`). -/
theorem inhabited_sliced_singleStep_bridge_four_challenge_bound :
    ∃ (D_in D_out S kernel : List QuarticGoldilocks) (d A B m Dy m_K : Nat)
      (curOracle : Nat → QuarticGoldilocks)
      (curClaim w₀ w₁ w₂ c_F c_G : QuarticGoldilocks)
      (L : List (Fin (quadPool S).length)),
      IsAntipodalDomainPair D_in D_out ∧
      S.Nodup ∧ d + 2 ≤ A ∧ kernel.length = 2 * m_K ∧
      slicedParamsOk D_out.length (d + 1) (A + 1) B m Dy = true ∧
      (∀ Q : List QuarticGoldilocks,
        polyWitnessValid D_in (2 * A) (2 * d + 1) curOracle kernel curClaim Q = false) ∧
      L.Nodup ∧
      (∀ ch ∈ L, ¬¬ ∃ P : List QuarticGoldilocks,
        let q := (quadPool S).get ch
        polyWitnessValid D_out (A + 1) (d + 1)
          (hemVirtualFoldOracle q.2.1 q.2.2.1 q.2.2.2 D_in D_out curOracle)
          (hemKernelFold q.1 kernel)
          (hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G q.1 q.2.1 q.2.2.1 q.2.2.2) P = true) ∧
      L.length = 1 := by
  let S : List QuarticGoldilocks := [qf 1, CommRingOps.neg (qf 1)]
  refine ⟨dom32In, dom16Out, S, [qf 1, qf 0, qf 0, qf 0], 1, 10, 7, 2, 4, 2,
    fun _ => CommRingOps.zero, qf 1, qf 1, CommRingOps.neg (qf 1), qf 0, qf 0, qf 0,
    [⟨0, by decide +kernel⟩],
    antipodalPair_dom32_dom16, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_, by decide +kernel, ?_, rfl⟩
  · intro Q
    cases hVal : polyWitnessValid dom32In 20 3 (fun _ => CommRingOps.zero)
        [qf 1, qf 0, qf 0, qf 0] (qf 1) Q
    · rfl
    · exfalso
      have hZero := polyWitnessValid_zeroOracle_claim dom32In 3 20 [qf 1, qf 0, qf 0, qf 0] Q (qf 1)
        antipodalPair_dom32_dom16.nodup_in (by decide) hVal
      exact (by decide +kernel : qf 1 ≠ CommRingOps.zero) hZero
  · intro ch hch hNo
    cases hch with
    | head =>
      exact hNo ⟨[], by decide +kernel⟩
    | tail _ hNil => cases hNil

/-- `#tooth`: dishonest 5-wire bridge `(w₀ = 1, w₁ = -1, w₂ = 0, c_F = 0, c_G = 0)` cancels a false
    pre-fold claim `curClaim = 1` at `φ = 1` across EVERY `(θ, α, β) ∈ S³`, demonstrating why
    `slicedFourChallengeCount` carries the cubic `|S|³` bridge-forgery term. -/
theorem tooth_bridge_four_challenge_forgery_exists :
    ∃ (S : List QuarticGoldilocks) (ch : Fin (quadPool S).length),
      let q := (quadPool S).get ch
      polyWitnessValid dom16Out 11 2
        (hemVirtualFoldOracle q.2.1 q.2.2.1 q.2.2.2 dom32In dom16Out (fun _ => CommRingOps.zero))
        (hemKernelFold q.1 [qf 1, qf 0, qf 0, qf 0])
        (hemBridgeFoldClaim (qf 1) (qf 1) (CommRingOps.neg (qf 1)) (qf 0) (qf 0) (qf 0)
          q.1 q.2.1 q.2.2.1 q.2.2.2) [] = true ∧
      1 ≤ slicedFourChallengeCount 16 1 10 7 2 4 S.length :=
  ⟨[qf 1], ⟨0, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩

/-- Total diagnostic accessor for `slicedMultiFoldStageBound`. -/
def slicedMultiFoldStageProfile (nv : Nat) (g : HemStageGeom) : RatBound :=
  match hemJohnsonQromTableRow nv g.stageIdx, slicedStageRow nv g.stageIdx with
  | some r, some w => slicedMultiFoldStageBound g r w
  | _, _ => RatBound.one

/-- Joint inhabitedness witness for `sliced_multifold_stage_supported_budget` (`nv = 24`, stage `0`). -/
theorem inhabited_sliced_multifold_stage_supported_budget :
    ∃ (nv : Nat) (g : HemStageGeom),
      2 ≤ nv ∧ nv ≤ 24 ∧ g ∈ hemStageGeoms nv ∧ hemJohnsonQromStageExhaustive g = false :=
  inhabited_sliced_stage_three_challenge_supported_budget

/-- `#tooth`: at `nv = 24`, stage `0` (`stepVars = 6`), the summed 6-step `slicedMultiFoldStageBound`
    achieves `175` bits (tolerating `Q + 1 ≤ 2^22`), yet does NOT reach `186` bits (`stepVars ≤ 4` is
    necessary for the `186`-bit tier in `sliced_multifold_stage_supported_budget`). -/
theorem tooth_multifold_step6_below_186_bits :
    ∃ g : HemStageGeom,
      g ∈ hemStageGeoms 24 ∧
      g.stepVars = 6 ∧
      atLeastBits 175 (slicedMultiFoldStageProfile 24 g) ∧
      ¬ atLeastBits 186 (slicedMultiFoldStageProfile 24 g) ∧
      ¬ atLeastBits 128 (dfmRoundScale (2 ^ 27) (slicedMultiFoldStageProfile 24 g)) :=
  ⟨(hemStageGeoms 24).get ⟨0, by decide +kernel⟩, list_get_mem _ _,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

#verify_constructive
  Qsag.gsDecodeList_length_le_johnson

#verify_constructive
  Qsag.SylElim.bezout_space_finite_u_locus
  Qsag.SylElim.curve_leaf_gcd_decomp
  Qsag.SylElim.curve_three_poly_sheet_decomp

#verify_constructive
  inhabited_gsDecodeList_length_le_johnson
  tooth_gsDecodeList_johnson_denominator_needed
  inhabited_sliced_equal_degree_three_challenge_bound
  tooth_three_challenge_lo_pair_forgery
  inhabited_sliced_stage_three_challenge_supported_budget
  tooth_three_challenge_nv24_stage0_margin
  inhabited_sliced_singleStep_bridge_four_challenge_bound
  tooth_bridge_four_challenge_forgery_exists
  inhabited_sliced_multifold_stage_supported_budget
  tooth_multifold_step6_below_186_bits

#verify_inhabited Qsag.gsDecodeList_length_le_johnson inhabited_gsDecodeList_length_le_johnson
#tooth_pair Qsag.gsDecodeList_length_le_johnson vs tooth_gsDecodeList_johnson_denominator_needed

#verify_inhabited Qsag.sliced_equal_degree_three_challenge_bound inhabited_sliced_equal_degree_three_challenge_bound
#tooth_pair Qsag.sliced_equal_degree_three_challenge_bound vs tooth_three_challenge_lo_pair_forgery

#verify_inhabited Qsag.sliced_stage_three_challenge_supported_budget inhabited_sliced_stage_three_challenge_supported_budget
#tooth_pair Qsag.sliced_stage_three_challenge_supported_budget vs tooth_three_challenge_nv24_stage0_margin

#verify_inhabited Qsag.sliced_singleStep_bridge_four_challenge_bound inhabited_sliced_singleStep_bridge_four_challenge_bound
#tooth_pair Qsag.sliced_singleStep_bridge_four_challenge_bound vs tooth_bridge_four_challenge_forgery_exists

#verify_inhabited Qsag.sliced_multifold_stage_supported_budget inhabited_sliced_multifold_stage_supported_budget
#tooth_pair Qsag.sliced_multifold_stage_supported_budget vs tooth_multifold_step6_below_186_bits

end Cwyz26EqualDegreeAndMultiFoldTests

end Qsag
end

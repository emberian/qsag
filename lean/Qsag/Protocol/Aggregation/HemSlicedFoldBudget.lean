module
/-
# Supported sliced fold counts and their quantitative boundary

The sliced decomposition proof is consumed by the claim-carrying binary fold theorem.
A fixed-theta specialization uses the actual equal-degree claim update, but exposes the
remaining invalid-mixture premise; it is not the three-challenge Theorem 5.1 lift.
The numerical stage profiles below concern one binary fold at each final-stage geometry.
They are never substituted into the multistage/QROM acceptance theorem.
-/
public import Qsag.Coding.Cwyz26DeployedStages
public import Qsag.Protocol.Aggregation.HemVerifierAcceptance
import all Qsag.Coding.Cwyz26DeployedStages
import all Qsag.Protocol.Aggregation.HemWhirRbrSoundness
import all Qsag.Protocol.Aggregation.HemVerifierAcceptance
import all Qsag.Oracle.MultiRoundFsQrom
import all Qsag.Oracle.ConcreteSecurityBudget
import all Qsag.Coding.AffineProximityGaps

public section
namespace Qsag
set_option autoImplicit false

/-- Direct claim-carrying consumer of the proved sliced incidence count. The additional
    list-product term is explicit and is not replaced by the smaller paper constant. -/
theorem sliced_claimFold_bad_pairs_bound
    (D S kernel : List QuarticGoldilocks) (d A B m Dy : Nat)
    (f g : QuarticGoldilocks → QuarticGoldilocks) (e_f e_g s_g : QuarticGoldilocks)
    (hD : D.Nodup) (hS : S.Nodup) (hdA : d + 2 ≤ A)
    (hParams : slicedParamsOk D.length (d + 1) (A + 1) B m Dy = true)
    (hInvalidG : ∀ G : List QuarticGoldilocks, G.length ≤ d + 1 →
      A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs G z = g z))).length →
      ringDot G kernel ≠ e_g)
    (L : List (Fin (prodPool S).length)) (hNd : L.Nodup)
    (hFlip : ∀ ch ∈ L, ¬¬ ∃ P : List QuarticGoldilocks,
      affineMcaAccepts D S (d + 1) (A + 1) (f, g) ch.1 P = true ∧
      ringDot P kernel = CommRingOps.add e_f
        (CommRingOps.add (CommRingOps.mul ((prodPool S).get ch).1 e_g)
          (CommRingOps.mul ((prodPool S).get ch).2 s_g))) :
    L.length ≤ Dy + slicedRest D.length (d + 1) (A + 1) B (m * (A + 1) - Dy) Dy S.length +
      (gsDecodeList (d + 1) A D f).length * (gsDecodeList d A D g).length * S.length := by
  exact claimFold_bad_pairs_bound D S kernel d A _ f g e_f e_g s_g hD hS hdA
    (slicedParamsOk_sound D.length (d + 1) (A + 1) B m Dy hParams D S hD hS rfl)
    hInvalidG L hNd hFlip

/-- Fixed-theta component of the actual `g + (alpha + beta X)(f + theta g)` combiner.
    `hInvalidMix` is a real remaining obligation: invalid input claims alone do not imply
    it for every theta. Counting its exceptional theta values and handling intermediate
    geometries is required before claiming the full equal-degree lift. -/
theorem sliced_equal_degree_fixed_theta_bound
    (D S kernel : List QuarticGoldilocks) (d A B m Dy : Nat)
    (f g : QuarticGoldilocks → QuarticGoldilocks) (e_f e_g c_f c_g θ : QuarticGoldilocks)
    (hD : D.Nodup) (hS : S.Nodup) (hdA : d + 2 ≤ A)
    (hParams : slicedParamsOk D.length (d + 1) (A + 1) B m Dy = true)
    (hInvalidMix : ∀ G : List QuarticGoldilocks, G.length ≤ d + 1 →
      A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs G z =
        CommRingOps.add (f z) (CommRingOps.mul θ (g z))))).length →
      ringDot G kernel ≠ CommRingOps.add e_f (CommRingOps.mul θ e_g))
    (L : List (Fin (prodPool S).length)) (hNd : L.Nodup)
    (hFlip : ∀ ch ∈ L, ¬¬ ∃ P : List QuarticGoldilocks,
      affineMcaAccepts D S (d + 1) (A + 1)
        (g, fun z => CommRingOps.add (f z) (CommRingOps.mul θ (g z))) ch.1 P = true ∧
      ringDot P kernel = hemFoldClaimUpdate e_f e_g c_f c_g θ
        ((prodPool S).get ch).1 ((prodPool S).get ch).2) :
    L.length ≤ Dy + slicedRest D.length (d + 1) (A + 1) B (m * (A + 1) - Dy) Dy S.length +
      (gsDecodeList (d + 1) A D g).length *
        (gsDecodeList d A D (fun z => CommRingOps.add (f z) (CommRingOps.mul θ (g z)))).length *
        S.length :=
  sliced_claimFold_bad_pairs_bound D S kernel d A B m Dy g
    (fun z => CommRingOps.add (f z) (CommRingOps.mul θ (g z))) e_g
    (CommRingOps.add e_f (CommRingOps.mul θ e_g))
    (CommRingOps.add c_f (CommRingOps.mul θ c_g)) hD hS hdA hParams hInvalidMix L hNd hFlip

/-- The fixed-theta invalid-mixture premise cannot be dropped: two identical zero words
    with false claim one have a valid zero claim after theta=-1 mixing. This is a witness
    to the need for a theta-exception argument, not a counterexample to a bounded lift. -/
theorem tooth_equal_degree_invalid_mixture :
    let D : List QuarticGoldilocks := [CommRingOps.zero, CommRingOps.one]
    (∀ P : List QuarticGoldilocks,
      polyWitnessValid D 2 0 (fun _ => CommRingOps.zero) [CommRingOps.one] CommRingOps.one P = false) ∧
    polyWitnessValid D 2 0
      (fun _ => CommRingOps.add CommRingOps.zero
        (CommRingOps.mul (CommRingOps.sub CommRingOps.zero CommRingOps.one) CommRingOps.zero))
      [CommRingOps.one]
      (CommRingOps.add CommRingOps.one
        (CommRingOps.mul (CommRingOps.sub CommRingOps.zero CommRingOps.one) CommRingOps.one)) [] = true := by
  refine ⟨?_, by decide⟩
  intro P
  cases hv : polyWitnessValid [CommRingOps.zero, CommRingOps.one] 2 0
      (fun _ => (CommRingOps.zero : QuarticGoldilocks)) [CommRingOps.one] CommRingOps.one P with
  | false => rfl
  | true =>
    have h0 := polyWitnessValid_zeroOracle_claim [CommRingOps.zero, CommRingOps.one] 0 2
      [CommRingOps.one] P CommRingOps.one (by decide) (by decide) hv
    exact False.elim ((by decide : (CommRingOps.one : QuarticGoldilocks) ≠ CommRingOps.zero) h0)

/-- Count divided by the actual challenge-pair cardinality. This is a binary decomposition
    budget, without the claim-list term or any three-challenge/multi-fold lift. -/
def slicedBinaryStageBound (g : HemStageGeom) (r : Nat × Nat × Nat × Nat × Nat)
    (w : Nat × Nat × Nat × Nat) : RatBound :=
  ⟨slicedStageCount goldilocksExt4Card g r w, goldilocksExt4Card * goldilocksExt4Card,
    Nat.mul_pos goldilocksExt4Card_pos goldilocksExt4Card_pos⟩

/-- Pure arithmetic: a 184-bit input tolerates this explicit DFM query budget. It does not
    assert that DFM applies to any particular protocol execution. -/
theorem dfm184_budget_at_2pow27 (b : RatBound) (hb : atLeastBits 184 b)
    (Q : Nat) (hQ : Q + 1 ≤ 2 ^ 27) : atLeastBits 128 (dfmRoundScale Q b) := by
  have hScale : (2 * Q + 1) ^ 2 ≤ 2 ^ 56 := by
    have hbase : 2 * Q + 1 ≤ 2 ^ 28 := by omega
    exact Nat.le_trans (Nat.pow_le_pow_left hbase 2) (by decide)
  change (2 * Q + 1) ^ 2 * b.num * 2 ^ 128 ≤ b.den
  have h := Nat.mul_le_mul_right (b.num * 2 ^ 128) hScale
  have he : 2 ^ 56 * (b.num * 2 ^ 128) = b.num * 2 ^ 184 := by
    calc 2 ^ 56 * (b.num * 2 ^ 128) = b.num * (2 ^ 56 * 2 ^ 128) := Nat.mul_left_comm _ _ _
         _ = b.num * 2 ^ 184 := by rw [show 2 ^ 56 * 2 ^ 128 = 2 ^ 184 from by decide]
  rw [Nat.mul_assoc]
  have hb' : 2 ^ 56 * (b.num * 2 ^ 128) ≤ b.den := by
    rw [he]
    exact hb
  exact Nat.le_trans h hb'

/-- Every non-exhaustive canonical row supplies an actual proved binary decomposition
    count and a 184-bit rational budget. DFM scaling remains an explicitly arithmetic
    conclusion at Q+1 <= 2^27, not an assertion of a QROM experiment reduction. -/
theorem sliced_stage_supported_budget (nv : Nat) (h2 : 2 ≤ nv) (h24 : nv ≤ 24)
    (g : HemStageGeom) (hg : g ∈ hemStageGeoms nv)
    (hne : hemJohnsonQromStageExhaustive g = false) :
    ∃ (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat),
      hemJohnsonQromTableRow nv g.stageIdx = some r ∧ slicedStageRow nv g.stageIdx = some w ∧
      (∀ D S : List QuarticGoldilocks, D.Nodup → S.Nodup → D.length = g.n →
        AffineFoldDecompBound D S g.d r.2.2.1 (slicedStageCount S.length g r w)) ∧
      atLeastBits 184 (slicedBinaryStageBound g r w) ∧
      (∀ Q : Nat, Q + 1 ≤ 2 ^ 27 → atLeastBits 128 (dfmRoundScale Q (slicedBinaryStageBound g r w))) := by
  obtain ⟨r, w, hr, hw, hd, hb, hbits⟩ := sliced_stage_decomp_bound nv h2 h24 g hg hne
  have hb184 : atLeastBits 184 (slicedBinaryStageBound g r w) :=
    Nat.le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hbits)) hb
  exact ⟨r, w, hr, hw, hd, hb184, fun Q hQ => dfm184_budget_at_2pow27 _ hb184 Q hQ⟩

/-- Total diagnostic accessor. Missing/exhaustive rows get no soundness credit. -/
def slicedBinaryStageProfile (nv : Nat) (g : HemStageGeom) : RatBound :=
  match hemJohnsonQromTableRow nv g.stageIdx, slicedStageRow nv g.stageIdx with
  | some r, some w => slicedBinaryStageBound g r w
  | _, _ => RatBound.one

/-- The actual proved nv24 stage-0 expression cannot replace the much smaller paper input.
    Nor does widening commitment digests repair this DFM-scaled arithmetic term. These
    are counterexamples about bounds, not attacks achieving their upper bounds. -/
theorem tooth_sliced_nv24_profile_margin :
    let g := (hemStageGeoms 24).get ⟨0, by decide⟩
    let b := slicedBinaryStageProfile 24 g
    atLeastBits 185 b ∧ ¬ atLeastBits 186 b ∧ ¬ atLeastBits 244 b ∧
    ¬ atLeastBits 128 (dfmRoundScale (2 ^ 28) b) ∧
    ¬ atLeastBits 128 (dfmRoundScale (2 ^ 40) b) ∧
    ¬ atLeastBits 128 (dfmRoundScale (2 ^ 56) b) ∧
    ¬ RatBound.le b (whirAffineEqualDegreeCommitFoldBound
      ((whirAffineStageWitnesses 24 true).get ⟨0, by decide⟩)) := by
  decide +kernel

/-- The Q+1 convention matters: the universal 184-bit guarantee fails at Q=2^27,
    although particular table rows can be stronger than that universal floor. -/
theorem tooth_dfm184_query_boundary :
    let b : RatBound := ⟨1, 2 ^ 184, by decide⟩
    atLeastBits 128 (dfmRoundScale (2 ^ 27 - 1) b) ∧
    ¬ atLeastBits 128 (dfmRoundScale (2 ^ 27) b) := by
  decide +kernel

#verify_constructive
  Qsag.sliced_claimFold_bad_pairs_bound
  Qsag.sliced_equal_degree_fixed_theta_bound
  Qsag.tooth_equal_degree_invalid_mixture
  Qsag.dfm184_budget_at_2pow27
  Qsag.sliced_stage_supported_budget
  Qsag.tooth_sliced_nv24_profile_margin
  Qsag.tooth_dfm184_query_boundary
end Qsag
end

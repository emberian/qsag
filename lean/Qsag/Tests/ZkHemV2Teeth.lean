module
public import Qsag.Protocol.Aggregation.ZkHemV2
/-
Teeth and inhabitedness witnesses for `Qsag.Protocol.Aggregation.ZkHemV2` (zk-Hem v2,
`crates/qsag-agg/SECURITY.md` section V2.2).

* Mask line (Lemma V2.4): at `β = 0` the word is `P`.
* Fold scalars (Lemma V2.3 (c)): `φ = 0`, a repeated point and four points in place of five
  each break the bijection.
* Blinding count (Lemma V2.2): a point of the base field, two conjugate points and a sixth
  coefficient for one point each break the bijection.
* Roster: the v1 and v2 wire tags are disjoint; four mask points give a smaller blinder count.
* `witness_*`: the hypotheses of the three lemmas hold for concrete data over `Goldilocks` and
  `QuinticGoldilocks`.
-/

public section
namespace Qsag
namespace ZkHemV2Teeth

set_option autoImplicit false
open CommRingOps RoundPoly Qsag.ZkHemV2
open QuinticGoldilocks (frob ofBase xBasis)

/-! ## Explicit Frobenius -/

theorem zeta_eq : QuinticGoldilocks.zeta = Goldilocks.ofNat 1041288259238279555 :=
  Goldilocks.ext (by rw [QuinticGoldilocks.zeta_val]; decide)

theorem frob_explicit (z : QuinticGoldilocks) :
    frob z =
      ⟨z.c0, mul (Goldilocks.ofNat 1041288259238279555) z.c1,
        mul (mul (Goldilocks.ofNat 1041288259238279555)
          (Goldilocks.ofNat 1041288259238279555)) z.c2,
        mul (mul (mul (Goldilocks.ofNat 1041288259238279555)
          (Goldilocks.ofNat 1041288259238279555)) (Goldilocks.ofNat 1041288259238279555)) z.c3,
        mul (mul (mul (Goldilocks.ofNat 1041288259238279555)
          (Goldilocks.ofNat 1041288259238279555))
          (mul (Goldilocks.ofNat 1041288259238279555)
            (Goldilocks.ofNat 1041288259238279555))) z.c4⟩ := by
  apply QuinticGoldilocks.ext
  · exact QuinticGoldilocks.frob_c0 z
  · rw [QuinticGoldilocks.frob_c1, zeta_eq]
  · rw [QuinticGoldilocks.frob_c2, zeta_eq]
  · rw [QuinticGoldilocks.frob_c3, zeta_eq]
  · rw [QuinticGoldilocks.frob_c4, zeta_eq]

/-! ## Witnesses -/

/-- Two base points and `X` with its four conjugates are pairwise distinct. -/
theorem witness_blind_points_nodup :
    ∃ (qs : List Goldilocks) (ys : List QuinticGoldilocks), (blindPoints qs ys).Nodup :=
  ⟨[Goldilocks.ofNat 1, Goldilocks.ofNat 2], [xBasis], by
    show ([ofBase (Goldilocks.ofNat 1), ofBase (Goldilocks.ofNat 2), xBasis, frob xBasis,
      frob (frob xBasis), frob (frob (frob xBasis)), frob (frob (frob (frob xBasis)))] :
        List QuinticGoldilocks).Nodup
    simp only [frob_explicit]
    decide +kernel⟩

/-- Five distinct nonzero points, nonzero weights and a nonzero fold challenge. -/
theorem witness_fold_scalar_hypotheses :
    ∃ (φ : Goldilocks) (xs : List Goldilocks), xs.Nodup ∧ (∀ x ∈ xs, x ≠ zero) ∧ φ ≠ zero ∧
      xs.length = 5 ∧ (foldScalars φ xs xs xs).length = 5 :=
  ⟨Goldilocks.ofNat 1,
    [Goldilocks.ofNat 1, Goldilocks.ofNat 2, Goldilocks.ofNat 3, Goldilocks.ofNat 4,
      Goldilocks.ofNat 5],
    by decide +kernel, by decide +kernel, by decide +kernel, rfl, rfl⟩

/-- A nonzero mask challenge. -/
theorem witness_mask_challenge : ∃ β : Goldilocks, β ≠ zero ∧
    maskLine β (fun _ : Unit => zero) (fun _ => one) () = β :=
  ⟨Goldilocks.ofNat 7, by decide +kernel, by decide +kernel⟩

/-- Concrete `s = 1`, `qs = [1, 2]`, `ωs = [X]` witness satisfying `(G2)` (`MaskRootsValid 1 [X]`):
    `X^2 ∉ F_p`, so all hypotheses of `v2_blinding_residue_ring_bijective` and
    `v2_blinding_residue_ring_perfectly_simulated` hold. -/
theorem witness_residue_ring_hypotheses :
    ∃ (s shiftDeg : Nat) (qs : List Goldilocks) (ωs : List QuinticGoldilocks),
      qs.Nodup ∧ (∀ q ∈ qs, q ≠ zero) ∧ MaskRootsValid s ωs ∧ shiftDeg = 4 := by
  refine ⟨1, 4, [Goldilocks.ofNat 1, Goldilocks.ofNat 2], [xBasis],
    by decide +kernel, by decide +kernel, ?_, rfl⟩
  rw [MaskRootsValid.public_eqs]
  refine ⟨by decide, ?_, List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil⟩
  intro ω hω
  rcases List.mem_singleton.mp hω with rfl
  simp only [fpow.public_eqs, frob_explicit]
  decide +kernel

/-- Base-field `ω ∈ F_p` violates `MaskRootsValid` and breaks residue-ring surjectivity:
    every remainder of `B(X)` modulo `X^2 - a^2` (`a ∈ F_p`) has coefficients in `F_p`, so no
    base-field `B` can realize `[xBasis, zero]` in `E[X] / (X^2 - 1)`. -/
theorem tooth_residue_ring_base_field_not_surjective :
    ¬ ∃ cs : List Goldilocks,
      blindingResidueView 1 0 [] [ofBase one] cs = ([], [[xBasis, zero]]) := by
  rintro ⟨cs, h⟩
  rw [blindingResidueView.public_eqs] at h
  have h2 := (Prod.mk.inj h).2
  dsimp only [List.map] at h2
  have hRem := (List.cons.inj h2).1
  have hBaseRem : ∀ P : List Goldilocks,
      ∃ r0 r1 : Goldilocks,
        (divModBinomial 1 (fpow (ofBase one) 2) (shiftMonomial 0 (P.map ofBase))).1 =
          [ofBase r0, ofBase r1] := by
    intro P
    have hZ : fpow (ofBase one) 2 = ofBase one := by
      simp only [fpow.public_eqs, QuinticGoldilocks.ofBase_one, LawfulCommRing.one_mul]
    rw [hZ, shiftMonomial.public_eqs.1]
    induction P with
    | nil =>
      rw [List.map_nil, divModBinomial.public_eqs.1]
      exact ⟨zero, zero, by simp [QuinticGoldilocks.ofBase_zero]⟩
    | cons c rest ih =>
      obtain ⟨a0, a1, hRest⟩ := ih
      rw [List.map_cons, divModBinomial.public_eqs.2]
      dsimp only
      rw [hRest]
      dsimp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
        List.take]
      refine ⟨add c a1, a0, ?_⟩
      rw [QuinticGoldilocks.ofBase_one, LawfulCommRing.one_mul, QuinticGoldilocks.ofBase_add]
  obtain ⟨r0, r1, hR⟩ := hBaseRem cs
  rw [hR] at hRem
  have hc0 := (List.cons.inj hRem).1
  exact LawfulField.zero_ne_one (F := Goldilocks) (congrArg QuinticGoldilocks.c1 hc0)

/-! ## Teeth -/

/-- One point of `E` with six base-field coefficients: `X⁵ - 3` vanishes at `X`, so the map of
    `v2_blinding_count` with one coefficient too many is not injective. -/
theorem tooth_blinding_six_coefficients_not_injective :
    ∃ cs cs' : List Goldilocks, cs.length = 6 ∧ cs'.length = 6 ∧ ¬ (cs = cs') ∧
      blindingView [] [xBasis] cs = blindingView [] [xBasis] cs' :=
  ⟨[neg (Goldilocks.ofNat 3), zero, zero, zero, zero, one], [zero, zero, zero, zero, zero, zero],
    rfl, rfl, by decide +kernel, by decide +kernel⟩

/-- With four mask points the layout would reserve fewer blinders than `blindCells`. -/
theorem tooth_four_mask_points_blind_cells_short (s q : Nat) :
    ¬ ((q + limbs * 4) * 2 ^ s = blindCells s q) := by
  intro h
  have h' : (q + 20) * 2 ^ s = (q + 25) * 2 ^ s := h
  have h2 := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos s) h'
  omega

/-- A concrete instance of `Qsag.ZkHemV2.tooth_four_mask_points_not_surjective`. -/
theorem tooth_four_mask_points_concrete :
    ¬ ∃ fs : List Goldilocks,
      foldScalars (Goldilocks.ofNat 1)
        [Goldilocks.ofNat 1, Goldilocks.ofNat 2, Goldilocks.ofNat 3, Goldilocks.ofNat 4]
        [Goldilocks.ofNat 1, Goldilocks.ofNat 1, Goldilocks.ofNat 1, Goldilocks.ofNat 1] fs =
        [zero, zero, zero, one, zero] :=
  tooth_four_mask_points_not_surjective _ _ _ _ _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _

#tooth_pair Qsag.ZkHemV2.v2_mask_line_perfectly_simulated vs
  Qsag.ZkHemV2.tooth_zero_mask_challenge_reveals_word
#tooth_pair Qsag.ZkHemV2.v2_mask_claim_determined vs
  Qsag.ZkHemV2.tooth_zero_mask_challenge_reveals_word
#tooth_pair Qsag.ZkHemV2.v2_mask_symbol_determined vs
  Qsag.ZkHemV2.tooth_zero_mask_challenge_reveals_word

#tooth_pair Qsag.ZkHemV2.v2_fold_scalar_matrix_bijective vs
  Qsag.ZkHemV2.tooth_zero_fold_challenge_not_surjective
#tooth_pair Qsag.ZkHemV2.v2_fold_scalar_matrix_bijective vs
  Qsag.ZkHemV2.tooth_repeated_mask_point_not_injective
#tooth_pair Qsag.ZkHemV2.v2_fold_scalar_matrix_bijective vs
  Qsag.ZkHemV2.tooth_four_mask_points_not_surjective
#tooth_pair Qsag.ZkHemV2.v2_fold_scalar_matrix_bijective vs
  Qsag.ZkHemV2Teeth.tooth_four_mask_points_concrete
#tooth_pair Qsag.ZkHemV2.v2_fold_scalars_perfectly_simulated vs
  Qsag.ZkHemV2.tooth_zero_fold_challenge_not_surjective
#tooth_pair Qsag.ZkHemV2.v2_fold_scalars_perfectly_simulated vs
  Qsag.ZkHemV2.tooth_repeated_mask_point_not_injective
#tooth_pair Qsag.ZkHemV2.v2_fold_scalars_perfectly_simulated vs
  Qsag.ZkHemV2.tooth_four_mask_points_not_surjective

#tooth_pair Qsag.ZkHemV2.v2_blinding_count vs
  Qsag.ZkHemV2.tooth_blinding_base_field_point_not_surjective
#tooth_pair Qsag.ZkHemV2.v2_blinding_count vs
  Qsag.ZkHemV2.tooth_blinding_conjugate_points_not_surjective
#tooth_pair Qsag.ZkHemV2.v2_blinding_count vs
  Qsag.ZkHemV2Teeth.tooth_blinding_six_coefficients_not_injective
#tooth_pair Qsag.ZkHemV2.v2_opened_symbols_and_mask_values_perfectly_simulated vs
  Qsag.ZkHemV2.tooth_blinding_base_field_point_not_surjective
#tooth_pair Qsag.ZkHemV2.v2_opened_symbols_and_mask_values_perfectly_simulated vs
  Qsag.ZkHemV2.tooth_blinding_conjugate_points_not_surjective
#tooth_pair Qsag.ZkHemV2.v2_blinding_count_scaled vs
  Qsag.ZkHemV2.tooth_blinding_conjugate_points_not_surjective
#tooth_pair Qsag.ZkHemV2.v2_blinding_residue_ring_bijective vs
  Qsag.ZkHemV2Teeth.tooth_residue_ring_base_field_not_surjective
#tooth_pair Qsag.ZkHemV2.v2_blinding_residue_ring_perfectly_simulated vs
  Qsag.ZkHemV2Teeth.tooth_residue_ring_base_field_not_surjective

#tooth_pair Qsag.ZkHemV2.ZkHemV2Profile.ofWireTag_wireTag vs
  Qsag.ZkHemV2.ZkHemV2Profile.ofWireTag_v1_tag
#tooth_pair Qsag.ZkHemV2.ZkHemV2Profile.wireTag_of_ofWireTag vs
  Qsag.ZkHemV2.ZkHemV2Profile.wireTag_ne_v1_tag
#tooth_pair Qsag.ZkHemV2.blindCells_eq vs
  Qsag.ZkHemV2Teeth.tooth_four_mask_points_blind_cells_short

#verify_inhabited Qsag.ZkHemV2.v2_blinding_count
  Qsag.ZkHemV2Teeth.witness_blind_points_nodup
#verify_inhabited Qsag.ZkHemV2.v2_opened_symbols_and_mask_values_perfectly_simulated
  Qsag.ZkHemV2Teeth.witness_blind_points_nodup
#verify_inhabited Qsag.ZkHemV2.v2_fold_scalar_matrix_bijective
  Qsag.ZkHemV2Teeth.witness_fold_scalar_hypotheses
#verify_inhabited Qsag.ZkHemV2.v2_fold_scalars_perfectly_simulated
  Qsag.ZkHemV2Teeth.witness_fold_scalar_hypotheses
#verify_inhabited Qsag.ZkHemV2.v2_mask_line_perfectly_simulated
  Qsag.ZkHemV2Teeth.witness_mask_challenge
#verify_inhabited Qsag.ZkHemV2.v2_blinding_residue_ring_bijective
  Qsag.ZkHemV2Teeth.witness_residue_ring_hypotheses
#verify_inhabited Qsag.ZkHemV2.v2_blinding_residue_ring_perfectly_simulated
  Qsag.ZkHemV2Teeth.witness_residue_ring_hypotheses

#verify_constructive
  Qsag.ZkHemV2Teeth.tooth_blinding_six_coefficients_not_injective
  Qsag.ZkHemV2Teeth.tooth_four_mask_points_blind_cells_short
  Qsag.ZkHemV2Teeth.tooth_four_mask_points_concrete
  Qsag.ZkHemV2Teeth.tooth_residue_ring_base_field_not_surjective
  Qsag.ZkHemV2Teeth.witness_blind_points_nodup
  Qsag.ZkHemV2Teeth.witness_fold_scalar_hypotheses
  Qsag.ZkHemV2Teeth.witness_mask_challenge
  Qsag.ZkHemV2Teeth.witness_residue_ring_hypotheses

end ZkHemV2Teeth
end Qsag

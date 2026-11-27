module
public import Qsag.Math.MlDsaField
public import Qsag.Math.MlDsaNtt
public import Qsag.Math.CyclotomicRlwe
public import Qsag.Math.GoldilocksBase
public import Qsag.Math.Lattices
public import Qsag.Coding.AffineProximity
public import Qsag.Coding.Resultant
public import Qsag.Math.EllipticCurves
public import Qsag.Math.Counting
public import Qsag.Math.CoeffPoly
public import Qsag.Math.PolyRing
public import Qsag.Math.HasseHensel
public import Qsag.Math.Primality
public import Qsag.Math.Gf2Pow128
public import Qsag.Tactic.Prelude
public import Qsag.Math.Algebra
public import Qsag.Math.Goldilocks
public import Qsag.Math.GoldilocksEncoding
public import Qsag.Math.QuinticExt5
public import Qsag.Coding.ReedSolomon
public import Qsag.Coding.GuruswamiSudan
public import Qsag.Coding.Cwyz26
public section
namespace Qsag
open CommRingOps RoundPoly
set_option autoImplicit false
set_option exponentiation.threshold 512
set_option linter.unusedSimpArgs false
/-- `decide +kernel`, named so that it can close a `first` alternative. -/
macro "kernel_decide" : tactic => `(tactic| decide +kernel)
/-- Evaluates a closed polynomial-stack statement by rewriting with the kernel-checked defining equations that
    the owning modules export (`#export_eqns`; no body is exposed) and deciding the residual field
    arithmetic. The bracket lists the fixtures of the statement at hand. -/
macro "poly_eval" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| first | kernel_decide | ((simp (config := {decide := true}) [$ls,*, UPoly.eq_iff_coeffs, UPoly.coeffs_zero, UPoly.coeffs_one,
    UPoly.coeffs_add, UPoly.coeffs_mul, UPoly.coeffs_neg, UPoly.coeffs_sub, UPoly.coeffs_ofList,
    SylElim.Dual.eq_iff_fst_snd, SylElim.Dual.zero_eq, SylElim.Dual.one_eq, SylElim.Dual.add_eq,
    SylElim.Dual.mul_eq, SylElim.Dual.neg_eq, SylElim.Dual.sub_eq, SylElim.Dual.inl_toFun,
    SylElim.Dual.map_toFun,
    Qsag.affineDistinctTuples.public_eqs,
    Qsag.eraseFirst.public_eqs,
    Qsag.prodPool.public_eqs,
    Qsag.JohnsonBound.elemBool.public_eqs,
    Qsag.JohnsonBound.johnsonBound.public_eqs,
    Qsag.UPoly.lead.public_eqs,
    Qsag.RoundPoly.eval.public_eqs,
    Qsag.monomial.public_eqs,
    Qsag.solveHomogeneous.public_eqs,
    Qsag.insertIdxVal.public_eqs,
    Qsag.subVec.public_eqs,
    Qsag.dropIdx.public_eqs,
    Qsag.scaleVec.public_eqs,
    Qsag.RoundPoly.subCoeffs.public_eqs,
    Qsag.vanishingPoly.public_eqs,
    Qsag.pSub.public_eqs,
    Qsag.pAdd.public_eqs,
    Qsag.pNeg.public_eqs,
    Qsag.rawNegCoeffs.public_eqs,
    Qsag.findNonzeroIdx.public_eqs,
    Qsag.SylElim.monom.public_eqs,
    Qsag.PreFrac.Rel.public_eqs,
    Qsag.Frac.mk.public_eqs,
    Qsag.UPoly.wdegFrom.public_eqs,
    Qsag.Mat.det.public_eqs,
    Qsag.Mat.minor.public_eqs,
    Qsag.Mat.skipIdx.public_eqs,
    Qsag.Mat.rangeSum.public_eqs,
    Qsag.Mat.signed.public_eqs,
    Qsag.UPoly.prodList.public_eqs,
    Qsag.Mat.idMat.public_eqs,
    Qsag.Mat.matMul.public_eqs,
    Qsag.Hensel.num.public_eqs,
    Qsag.Hensel.iter.public_eqs,
    Qsag.Hensel.phi.public_eqs,
    Qsag.Hensel.sep.public_eqs,
    Qsag.Hensel.e12.public_eqs,
    Qsag.Hensel.evW.public_eqs,
    Qsag.UPoly.shiftDown.public_eqs,
    Qsag.Hensel.e2.public_eqs,
    Qsag.Hensel.e11.public_eqs,
    Qsag.Hensel.evG.public_eqs,
    Qsag.Poly3.henselNum.public_eqs,
    Qsag.Poly3.henselG.public_eqs,
    Qsag.Poly3.liftXY.public_eqs,
    Qsag.Poly3.jetV.public_eqs,
    Qsag.Poly3.liftX.public_eqs,
    Qsag.Poly3.C3.public_eqs,
    Qsag.Poly3.c3Hom.public_eqs,
    Qsag.Poly3.jetY.public_eqs,
    Qsag.Poly3.shiftHom.public_eqs,
    Qsag.Poly3.yLine.public_eqs,
    Qsag.UPoly.taylorShift.public_eqs,
    Qsag.Poly3.triples.public_eqs,
    Qsag.rows.public_eqs,
    Qsag.Poly3.cons.public_eqs,
    Qsag.Poly3.coeff3.public_eqs,
    Qsag.Poly3.comb.public_eqs,
    Qsag.Poly3.hasseZ.public_eqs,
    Qsag.UPoly.hasse.public_eqs,
    Qsag.Poly3.eval3.public_eqs,
    Qsag.Poly3.ptHom.public_eqs,
    Qsag.Poly3.triCount.public_eqs,
    Qsag.Poly3.jetHom.public_eqs,
    Qsag.Poly3.evalAffineLine.public_eqs,
    Qsag.Poly3.affineLineHom.public_eqs,
    Qsag.Poly3.degZ.public_eqs,
    Qsag.Poly3.henselSep.public_eqs,
    Qsag.Hensel.res.public_eqs,
    Qsag.SylElim.modPoly2Hom.public_eqs,
    Qsag.SylElim.remM.public_eqs,
    Qsag.SylElim.divModLead.public_eqs,
    Qsag.SylElim.divModLeadAux.public_eqs,
    Qsag.SylElim.quotM.public_eqs,
    Qsag.Poly2.mono.public_eqs,
    Qsag.SylElim.embedUZ.public_eqs,
    Qsag.Poly2.resZ.public_eqs,
    Qsag.Poly2.eliminant.public_eqs,
    Qsag.Poly2.elimV.public_eqs,
    Qsag.Poly2.lincomb.public_eqs,
    Qsag.Poly2.elimIdx.public_eqs,
    Qsag.Poly2.elimVec.public_eqs,
    Qsag.Poly2.nullVec.public_eqs,
    Qsag.Poly2.coeff2.public_eqs,
    Qsag.Poly2.elimGens.public_eqs,
    Qsag.Poly2.elimCons.public_eqs,
    Qsag.Poly2.elimDeg.public_eqs,
    Qsag.Poly2.elimU.public_eqs,
    Qsag.Poly2.swapVZ.public_eqs,
    Qsag.Poly2.innerHom.public_eqs,
    Qsag.SylElim.dualPerturb.public_eqs,
    Qsag.Poly3.explainer.public_eqs,
    Qsag.Poly3.consRows.public_eqs,
    Qsag.Poly3.gens.public_eqs,
    Qsag.Poly3.mono3.public_eqs,
    Qsag.Poly3.lineSpec.public_eqs,
    Qsag.Poly3.Excluded.public_eqs,
    Qsag.Poly3.sepElim.public_eqs,
    Qsag.Poly3.liftK.public_eqs,
    Qsag.Poly3.factored.public_eqs,
    Qsag.poleWords.public_eqs,
    Qsag.AffineMcaBound,
    Qsag.Frac,
    Qsag.Goldilocks.add,
    Qsag.Goldilocks.inv,
    Qsag.Goldilocks.mul,
    Qsag.Goldilocks.neg,
    Qsag.Goldilocks.ofNat,
    Qsag.Goldilocks.one,
    Qsag.Goldilocks.sub,
    Qsag.Goldilocks.zero,
    Qsag.GoldilocksExt2.add,
    Qsag.GoldilocksExt2.inv,
    Qsag.GoldilocksExt2.mul,
    Qsag.GoldilocksExt2.neg,
    Qsag.GoldilocksExt2.nonResidue,
    Qsag.GoldilocksExt2.one,
    Qsag.GoldilocksExt2.sub,
    Qsag.GoldilocksExt2.zero,
    Qsag.GsUniPoly,
    Qsag.GsUniPoly.ofCoeffs,
    Qsag.GsUniPoly.val,
    Qsag.HasAffineWitnessS1,
    Qsag.HasCorrelatedAgreement,
    Qsag.HasPolynomialExplanation,
    Qsag.IsPersistent,
    Qsag.NonExcludedBound,
    Qsag.Poly2,
    Qsag.Poly2.CoprimeZ,
    Qsag.Poly2.IsPrimY,
    Qsag.Poly2.eval2,
    Qsag.Poly2.liftFY,
    Qsag.Poly2.tdeg,
    Qsag.Poly2.vCoeff,
    Qsag.Poly3,
    Qsag.Poly3.deg11d,
    Qsag.Poly3.degYZ,
    Qsag.Poly3.line,
    Qsag.RatFunc,
    Qsag.RingHom.comp,
    Qsag.RingHom.id,
    Qsag.RoundPoly.evalCoeffs,
    Qsag.SimpleEquiv.refl,
    Qsag.SylElim.Dual.eps,
    Qsag.SylElim.sylMat,
    Qsag.SylElim.sylRes,
    Qsag.SylElim.sylResDeriv,
    Qsag.UPoly.C,
    Qsag.UPoly.CHom,
    Qsag.UPoly.X,
    Qsag.UPoly.eval,
    Qsag.UPoly.evalHom,
    Qsag.UPoly.eval₂,
    Qsag.UPoly.eval₂Hom,
    Qsag.UPoly.mapHom,
    Qsag.UPoly.natDeg,
    Qsag.UPoly.ofList,
    Qsag.UPoly.wdeg,
    Qsag.affineFallingFactorial,
    Qsag.affineMcaAccepts,
    Qsag.checkWhirAffineWitness,
    Qsag.coeffAt,
    Qsag.dotVec,
    Qsag.foldAgree,
    Qsag.foldAgreePt,
    Qsag.goldOfInt,
    Qsag.goldP,
    Qsag.goldilocksAddSpec,
    Qsag.goldilocksReduce128Spec,
    Qsag.goldilocksSubSpec,
    Qsag.gsMonomialCount,
    Qsag.gsUniHasse,
    Qsag.interpEquationsAux,
    Qsag.interpUnknownsAux,
    Qsag.natCeilDiv,
    Qsag.pMul,
    Qsag.quadExtMulMod,
    Qsag.rawAddCoeffs,
    Qsag.rawMul,
    Qsag.slicedParamsOk,
    Qsag.sumTo,
    Qsag.trimPoly]) <;> kernel_decide))
/-- `poly_eval` with no fixtures. -/
macro "poly_eval" : tactic => `(tactic| poly_eval [UPoly.coeffs_zero])
/-- Dropping the parity bit loses injectivity at every order above two: `[1]G` and
    `[n - 1]G` are distinct multiples with one `x`-coordinate. -/
theorem TaprootCurveProjection.tooth_xonly_not_injective {n : Nat} {XCoord : Type}
    (proj : TaprootCurveProjection n XCoord) (hn : 2 < n) :
    ∃ s1 s2, 0 < s1 ∧ s1 < n ∧ 0 < s2 ∧ s2 < n ∧ s1 ≠ s2 ∧ proj.xOf s1 = proj.xOf s2 :=
  ⟨1, n - 1, by omega, by omega, by omega, by omega, by omega,
    (proj.sameX_iff 1 (n - 1) (by omega) (by omega) (by omega) (by omega)).mpr (Or.inr rfl)⟩

#tooth_pair
  Qsag.TaprootCurveProjection.compressed_injective
  vs
  Qsag.TaprootCurveProjection.tooth_xonly_not_injective


/-- **`#tooth` Taproot `x`-Only Non-Injectivity Without `y[0]` Parity**: without
    `ownership.rs:282` (`c.output(y[0])`), `proj.xOf` is not injective on the canonical
    `secp256k1` scalars `[1, SECP_N - 1]`: `1#256` and `secpNegScalar 1#256` are distinct
    canonical scalars sharing one `x`-coordinate. -/
theorem tooth_taproot_xonly_not_injective_without_y_parity
    {XCoord : Type} (proj : TaprootCurveProjection SECP256K1_ORDER_N XCoord) :
    ∃ s1 s2 : BitVec 256,
      requireCanonicalScalar .Secp256k1 s1 = true ∧
      requireCanonicalScalar .Secp256k1 s2 = true ∧
      s1 ≠ s2 ∧
      taprootXOnlySameX s1 s2 ∧
      proj.xOf s1.toNat = proj.xOf s2.toNat := by
  have h1Canon : requireCanonicalScalar .Secp256k1 1#256 = true := by
    unfold requireCanonicalScalar ScalarGroup.orderNat SECP256K1_ORDER_N
    decide
  obtain ⟨_, h2Canon, _, hNe, hSameX⟩ := secpNegScalar_props h1Canon
  exact ⟨1#256, secpNegScalar 1#256, h1Canon, h2Canon, hNe, hSameX,
    (proj.sameX_iff_canonical 1#256 (secpNegScalar 1#256) h1Canon h2Canon).mpr hSameX⟩


#tooth_pair
  Qsag.taproot_even_y_parity_restores_canonical_injectivity
  vs
  Qsag.tooth_taproot_xonly_not_injective_without_y_parity


namespace Weierstrass
#tooth_pair
  Qsag.Weierstrass.Curve.PrimeOrderGroup.xonly_parity_laws_of_groupLaws
  vs
  Qsag.Weierstrass.tooth_two_torsion_point_is_its_own_negative


end Weierstrass

#tooth_pair
  Qsag.slip0010_ed25519_clamped_canonical_nonzero
  vs
  Qsag.tooth_ed25519_clamped_wraps_mod_order_non_injective


#tooth_pair Qsag.checkPrattStep_sound vs Qsag.tooth_carmichael_561_passes_fermat_but_fails_pratt
#verify_constructive Qsag.tooth_carmichael_561_passes_fermat_but_fails_pratt


#tooth_pair Qsag.bls381G1_onCurve_and_prime_subgroup_order vs Qsag.tooth_bls381_torsion3_onCurve_but_off_subgroup
#verify_constructive Qsag.tooth_bls381_torsion3_onCurve_but_off_subgroup


namespace Poly3.Tests
open UPoly

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

/-- `Q = Z` in `Goldilocks[X][Y][Z]`, and `P = X²`. -/
def qZ : Poly3 Goldilocks := X
def pSq : UPoly Goldilocks := ofList [g 0, g 0, g 1]

/-- The hypothesis of `deg_evalAffineLine_le` is satisfiable with the bound attained:
    `Q = Z`, `P = X²` gives degree exactly `2 = deg11d 2 Q`. -/
theorem inhabited_deg_evalAffineLine :
    ∃ (Q : Poly3 Goldilocks) (P : UPoly Goldilocks) (d : Nat), P.natDeg ≤ d ∧
      (Q.evalAffineLine (g 3) (g 5) P).natDeg = 2 ∧ Q.deg11d d = 2 :=
  ⟨qZ, pSq, 2, by poly_eval [qZ, pSq, g], by poly_eval [qZ, pSq, g], by poly_eval [qZ, pSq, g]⟩

/-- The `Z`-weight cannot be lowered below `deg P`: with weight `1` the bound fails. -/
theorem tooth_deg_evalAffineLine_weight :
    ∃ (Q : Poly3 Goldilocks) (P : UPoly Goldilocks), P.natDeg ≤ 2 ∧
      ¬ (Q.evalAffineLine (g 3) (g 5) P).natDeg ≤ Q.deg11d 1 :=
  ⟨qZ, pSq, by decide, by poly_eval [g, qZ, pSq]⟩

/-- Taylor's formula on a concrete cubic: `p = 1 + 2X + 3X² + 4X³` at `b = 5` has first
    Hasse derivative `2 + 6·5 + 12·25 = 332`. -/
theorem taylor_cubic_example :
    coeffAt ((taylorShift (g 5)).toFun (ofList [g 1, g 2, g 3, g 4])).coeffs 1 = g 332 ∧
      (hasse 1 (ofList [g 1, g 2, g 3, g 4])).coeffs = [g 2, g 6, g 12] := by
  poly_eval [g, qZ, pSq]

#verify_constructive deg_evalAffineLine_le UPoly.coeffAt_taylorShift UPoly.eval_taylorShift
#verify_constructive UPoly.degFn_wdeg UPoly.natDeg_mul UPoly.eval_hasse taylor_cubic_example
#tooth_pair deg_evalAffineLine_le vs tooth_deg_evalAffineLine_weight
#verify_inhabited deg_evalAffineLine_le inhabited_deg_evalAffineLine

end Poly3.Tests


namespace MatrixDetTests
open Mat

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n
def matA : Nat → Nat → Goldilocks | 0, 0 => g 2 | 0, 1 => g 3 | 1, 0 => g 5 | 1, 1 => g 7 | _, _ => zero
def matB : Nat → Nat → Goldilocks | 0, 0 => g 11 | 0, 1 => g 13 | 1, 0 => g 17 | 1, 1 => g 19 | _, _ => zero

theorem inhabited_det_matMul :
    ∃ (k : Nat) (A B : Nat → Nat → Goldilocks),
      det k A ≠ zero ∧ det k B ≠ zero ∧
      det k (matMul k A B) = g 12 ∧ det k (matMul k A B) = mul (det k A) (det k B) :=
  ⟨2, matA, matB, by poly_eval [matA, matB, g], by poly_eval [matA, matB, g], by poly_eval [matA, matB, g], det_matMul 2 matA matB⟩

theorem tooth_det_not_entrywise_mul :
    ∃ (k : Nat) (A B : Nat → Nat → Goldilocks),
      det k (fun i j => mul (A i j) (B i j)) ≠ mul (det k A) (det k B) :=
  ⟨2, idMat, fun _ _ => one, by poly_eval [g, matA, matB]⟩

theorem inhabited_degFn_det_weighted_le :
    ∃ (M : Nat → Nat → UPoly Goldilocks),
      DegFn (UPoly.natDeg (R := Goldilocks)) ∧
      UPoly.natDeg (one : UPoly Goldilocks) = 0 ∧
      (∀ i, i < 2 → ∀ j, j < 2 → M i j ≠ zero → UPoly.natDeg (M i j) + j ≤ 1 + i) ∧
      det 2 M ≠ zero := by
  let M : Nat → Nat → UPoly Goldilocks
    | 0, 0 => UPoly.X | 0, 1 => one | 1, 0 => zero | 1, 1 => UPoly.X | _, _ => zero
  refine ⟨M, UPoly.degFn_natDeg, by decide +kernel, ?_, by poly_eval [g, matA, matB]⟩
  intro i hi j hj hne
  match i, j with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 => dsimp [M] at hne ⊢; decide +kernel
  | i + 2, _ | _, j + 2 => omega

#verify_constructive Mat.map_det Mat.det_col0_unit Mat.det_lower_tri_one Mat.det_idMat
#verify_constructive Mat.degFn_det_weighted_le Mat.det_perm_rows Mat.det_matMul
#verify_constructive inhabited_det_matMul inhabited_degFn_det_weighted_le tooth_det_not_entrywise_mul
#tooth_pair Mat.det_matMul vs tooth_det_not_entrywise_mul
#verify_inhabited Mat.degFn_det_weighted_le inhabited_degFn_det_weighted_le

end MatrixDetTests

/-- **`#tooth` Proth-Shaped Composite Counterexample (`tooth_proth16_65281_not_prime`)**. -/
theorem tooth_proth16_65281_not_prime :
    ∃ N : Nat, N = 2 ^ 16 - 2 ^ 8 + 1 ∧ N = 97 * 673 ∧
      checkLucasBlsCert N 7 [(2, 8), (3, 1), (5, 1), (17, 1)] = false ∧ ¬ IsPrimeNat N :=
  ⟨65281, by decide, by decide, by decide, fun hp => by
    rcases hp.2 97 ⟨673, by decide⟩ with h1 | h2 <;> omega⟩

/-- **`#tooth` Carmichael Pseudoprime Refusal (`tooth_carmichael_561_rejected`)**. -/
theorem tooth_carmichael_561_rejected :
    ∃ N : Nat, N = 561 ∧ powMod 2 (N - 1) N = 1 ∧
      checkLucasBlsCert N 2 [(2, 4), (5, 1), (7, 1)] = false ∧ ¬ IsPrimeNat N :=
  ⟨561, rfl, by decide, by decide, fun hp => by
    rcases hp.2 3 ⟨187, by decide⟩ with h1 | h2 <;> omega⟩

#tooth_pair
  Qsag.verifyPrimeCert_sound
  vs
  Qsag.tooth_carmichael_561_rejected_by_pocklington

#verify_inhabited
  Qsag.verifyPrimeCert_sound
  Qsag.inhabited_verifyPrimeCert

#verify_constructive
  Qsag.verifyPrimeCert_sound
  Qsag.secp256k1FieldPrime_isPrime
  Qsag.secp256k1OrderPrime_isPrime
  Qsag.tooth_carmichael_561_rejected_by_pocklington


/-- **`#tooth` Non-Trivial Zero-Divisor Modulo $29$ (`tooth_mod29_seven_residue_zero_divisor`)**:
    Modulo $29$, $7 \equiv 6^2 \pmod{29}$, so $(6 - u)(6 + u) = 0$ in $(\mathbb{Z}/29\mathbb{Z})[u]/(u^2 - 7)$. -/
theorem tooth_mod29_seven_residue_zero_divisor :
    ∃ x y : Nat × Nat, x = (6, 28) ∧ y = (6, 1) ∧ x ≠ (0, 0) ∧ y ≠ (0, 0) ∧
      quadExtMulMod 29 7 x y = (0, 0) :=
  ⟨(6, 28), (6, 1), rfl, rfl, by decide, by decide, by decide⟩


/-! ## 4. Inhabitedness Witnesses & `#tooth_pair` / `#verify_constructive` Assurance Gates -/

theorem witness_goldilocks_nonzero_element :
    ∃ x : Goldilocks, x ≠ Goldilocks.zero ∧ Goldilocks.inv x ≠ Goldilocks.zero :=
  ⟨⟨7, by decide⟩, by decide, by decide⟩

theorem witness_goldilocks_bezout_nonzero :
    ∃ x : Goldilocks, x ≠ Goldilocks.zero ∧ Goldilocks.invBezout x ≠ Goldilocks.zero :=
  ⟨⟨7, by decide⟩, by decide, by rw [goldilocks_invBezout_eq_inv]; decide⟩

theorem tooth_goldilocks_zero_has_no_inverse :
    CommRingOps.mul Goldilocks.zero (Goldilocks.inv Goldilocks.zero) ≠ CommRingOps.one := by
  rw [show CommRingOps.mul Goldilocks.zero (Goldilocks.inv Goldilocks.zero) = Goldilocks.zero from
        LawfulCommRing.zero_mul _]
  decide

theorem tooth_monic_quad_factor_zero_at_origin :
    ¬ IsMonicQuadFactorOfV4Sub7 Goldilocks.zero Goldilocks.zero Goldilocks.zero Goldilocks.zero :=
  v_pow4_sub_seven_irreducible.2 _ _ _ _

#verify_constructive Qsag.goldilocksPrime_is_prime Qsag.goldilocks_lucas_fermat_witnesses
  Qsag.goldilocks_seven_primitive_root Qsag.goldilocks_universal_mul_inv_cancel
  Qsag.goldilocks_invBezout_eq_inv Qsag.v_pow4_sub_seven_irreducible

#verify_inhabited Qsag.checkLucasBlsCert_sound Qsag.witness_lucas_bls_goldilocks
#verify_inhabited Qsag.goldilocks_universal_mul_inv_cancel Qsag.witness_goldilocks_nonzero_element
#verify_inhabited Qsag.goldilocks_mul_invBezout_cancel Qsag.witness_goldilocks_bezout_nonzero


#tooth_pair Qsag.checkLucasBlsCert_sound vs Qsag.tooth_proth16_65281_not_prime
#tooth_pair Qsag.checkLucasBlsCert_sound vs Qsag.tooth_carmichael_561_rejected
#tooth_pair Qsag.goldilocks_universal_mul_inv_cancel vs Qsag.tooth_goldilocks_zero_has_no_inverse
#tooth_pair Qsag.goldilocks_quadExtMulMod_no_zero_divisors vs Qsag.tooth_mod29_seven_residue_zero_divisor
#tooth_pair Qsag.v_pow4_sub_seven_irreducible vs Qsag.tooth_monic_quad_factor_zero_at_origin


end Qsag

namespace Qsag
open RoundPoly
/-! ## §2. Constructive `#tooth` Lower Bounds (`Proposition 6.1` Scalar & `Proposition 6.2` $s=0$ Affine) -/

/-- Lookup index of `x` in `D` (`none` if absent). -/
private def indexOf? {α : Type} [DecidableEq α] (x : α) : List α → Option Nat
  | [] => none
  | y :: ys => if x = y then some 0 else (indexOf? x ys).map (· + 1)

private theorem indexOf?_of_getElem? {α : Type} [DecidableEq α] :
    ∀ {D : List α} {i : Nat} {x : α}, D.Nodup → D[i]? = some x → indexOf? x D = some i
  | [], _, _, _, h => by simp at h
  | y :: ys, 0, x, _, h => by
    simp at h; subst h; simp [indexOf?]
  | y :: ys, i + 1, x, .cons hnot hnd, h => by
    simp only [List.getElem?_cons_succ] at h
    have hxMem : x ∈ ys := List.mem_of_getElem? h
    have hne : x ≠ y := fun heq => hnot x hxMem heq.symm
    simp [indexOf?, hne, indexOf?_of_getElem? hnd h]

/-- Adversarial received-word pair `(f, g)` for `[CWYZ26]` Proposition 6.1 (`prop:scfloor`). -/
def scalarFloorWords
    {F : Type} [LawfulField F] [DecidableEq F]
    (D gammas : List F) (A s : Nat) : (F → F) × (F → F) :=
  let cLen := A - s - 1
  let C := D.take cLen
  let gFn := fun z => RoundPoly.evalCoeffs (vanishingPoly C) z
  let fFn := fun z =>
    match indexOf? z D with
    | none => CommRingOps.zero
    | some idx =>
      if idx < cLen then CommRingOps.zero
      else
        let blk := (idx - cLen) / (s + 1)
        if blk < gammas.length ∧ cLen + (blk + 1) * (s + 1) ≤ D.length then
          CommRingOps.neg (CommRingOps.mul (gammas.getD blk CommRingOps.zero) (gFn z))
        else
          CommRingOps.zero
  (fFn, gFn)

private theorem getElem_inj_of_nodup {α : Type} :
    ∀ {xs : List α}, xs.Nodup → ∀ (i j : Nat) (hi : i < xs.length) (hj : j < xs.length),
      xs[i] = xs[j] → i = j
  | [], _, _, _, hi, _, _ => by simp at hi
  | _ :: _, _, 0, 0, _, _, _ => rfl
  | _ :: xs, .cons hnot _, 0, j + 1, _, hj, heq => by
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
    have hj' : j < xs.length := by simp at hj; omega
    exact False.elim (hnot (xs[j]'hj') (List.getElem_mem hj') heq)
  | _ :: xs, .cons hnot _, i + 1, 0, hi, _, heq => by
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
    have hi' : i < xs.length := by simp at hi; omega
    exact False.elim (hnot (xs[i]'hi') (List.getElem_mem hi') heq.symm)
  | _ :: xs, .cons _ hnd, i + 1, j + 1, hi, hj, heq => by
    simp only [List.getElem_cons_succ] at heq
    exact congrArg (· + 1) (getElem_inj_of_nodup hnd i j
      (by simp at hi; omega) (by simp at hj; omega) heq)

/-- **`#tooth` Proposition 6.1 (`tooth_scalar_combiner_linear_n_over_q_floor`)**:
    For ANY degree `d`, loss `s`, threshold `A` (`d + s + 1 < A`, `A ≤ D.length`), and ANY list
    `gammas` of `1 + (D.length - A) / (s + 1)` distinct non-zero challenges in `S`:
    every `γ ∈ gammas` is a pairwise-distinct non-zero challenge making `f + γ g` vanish on
    **at least `A` points of `D`** (`P = 0`), yet **NO polynomial `G_poly` of degree `≤ d`** agrees
    with `g` on `≥ A - s` of those points — proving scalar combiners incur
    `≥ (1 + ⌊(n - A)/(s + 1)⌋) / |S| = Ω(n/q)` error even for `s ≥ 1`! -/
theorem tooth_scalar_combiner_linear_n_over_q_floor
    {F : Type} [LawfulField F] [DecidableEq F]
    (D gammas : List F) (d s A : Nat)
    (hD : D.Nodup)
    (hGammas : gammas.Nodup)
    (hGammasNz : ∀ γ ∈ gammas, γ ≠ CommRingOps.zero)
    (hA_lo : d + s + 1 < A)
    (hA_hi : A ≤ D.length)
    (hGammasLen : gammas.length = 1 + (D.length - A) / (s + 1)) :
    let (f, g) := scalarFloorWords D gammas A s
    (∀ i j : Fin gammas.length, i ≠ j → gammas[i] ≠ gammas[j]) ∧
    ∀ r : Fin gammas.length,
      let γ := gammas[r]
      let S_γ := D.filter (fun z =>
        decide (CommRingOps.add (f z) (CommRingOps.mul γ (g z)) = CommRingOps.zero))
      γ ≠ CommRingOps.zero ∧
      A ≤ S_γ.length ∧
      ∀ G_poly : List F, G_poly.length ≤ d + 1 →
        (S_γ.filter (fun z => decide (RoundPoly.evalCoeffs G_poly z = g z))).length < A - s := by
  dsimp only
  refine ⟨fun i j hij heq => hij (Fin.ext (getElem_inj_of_nodup hGammas i.1 j.1 i.2 j.2 heq)), ?_⟩
  intro r
  let cLen := A - s - 1
  have hcLen : cLen = A - s - 1 := rfl
  let C := D.take cLen
  let blkStart := cLen + r.1 * (s + 1)
  have hblkStart : blkStart = cLen + r.1 * (s + 1) := rfl
  let T := (D.drop blkStart).take (s + 1)
  let fg := scalarFloorWords D gammas A s
  have hBlockFit : cLen + (r.1 + 1) * (s + 1) ≤ D.length := by
    have hrLt : r.1 < 1 + (D.length - A) / (s + 1) := by omega
    have hrLe : r.1 ≤ (D.length - A) / (s + 1) := by omega
    have hmul := Nat.mul_le_mul_right (s + 1) hrLe
    have hdiv := Nat.div_mul_le_self (D.length - A) (s + 1)
    have hexp : (r.1 + 1) * (s + 1) = r.1 * (s + 1) + (s + 1) := Nat.add_one_mul r.1 (s + 1)
    omega
  have hSubCT : ∀ z ∈ C ++ T, z ∈ D.filter (fun z =>
      decide (CommRingOps.add (fg.1 z) (CommRingOps.mul gammas[r] (fg.2 z)) =
              CommRingOps.zero)) := by
    intro z hz
    rw [List.mem_append] at hz
    rcases hz with hzC | hzT
    · have hzD : z ∈ D := List.mem_of_mem_take hzC
      rw [List.mem_filter]
      refine ⟨hzD, decide_eq_true ?_⟩
      rcases List.getElem?_of_mem hzC with ⟨i, hi⟩
      have hiLt : i < cLen := by
        have hlt := lt_length_of_getElem?_eq_some hi
        rw [List.length_take] at hlt
        omega
      have hiD : D[i]? = some z := by
        rw [List.getElem?_take_of_lt hiLt] at hi
        exact hi
      have hidx := indexOf?_of_getElem? hD hiD
      have hg0 : fg.2 z = CommRingOps.zero := eval_vanishingPoly_eq_zero_of_mem hzC
      have hf0 : fg.1 z = CommRingOps.zero := by
        dsimp [fg, scalarFloorWords]
        rw [hidx]
        simp [cLen, hiLt]
      rw [hf0, hg0, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    · rcases List.getElem?_of_mem hzT with ⟨j, hj⟩
      have hjLt : j < s + 1 := by
        have hlt := lt_length_of_getElem?_eq_some hj
        rw [List.length_take] at hlt
        omega
      rw [List.getElem?_take_of_lt hjLt, List.getElem?_drop] at hj
      have hzD : z ∈ D := List.mem_of_getElem? hj
      have hidx := indexOf?_of_getElem? hD hj
      have hgeC : ¬ (blkStart + j < cLen) := by omega
      have hblkEq : (blkStart + j - cLen) / (s + 1) = r.1 := by
        have h1 : blkStart + j - cLen = j + r.1 * (s + 1) := by omega
        rw [h1, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hjLt, Nat.zero_add]
      have hgetGamma : gammas.getD r.1 CommRingOps.zero = gammas[r] := by
        simp [List.getD, r.2]
      have hfVal : fg.1 z = CommRingOps.neg (CommRingOps.mul gammas[r] (fg.2 z)) := by
        dsimp [fg, scalarFloorWords]
        rw [hidx]
        simp only [cLen, hgeC, ↓reduceIte, hblkEq, r.2, hBlockFit, and_self, hgetGamma]
        rfl
      rw [List.mem_filter]
      refine ⟨hzD, decide_eq_true ?_⟩
      rw [hfVal, LawfulCommRing.add_left_neg]
  have hndCT : (C ++ T).Nodup := by
    have hSubD : List.Sublist (C ++ T) (D.take cLen ++ D.drop cLen) := by
      apply List.Sublist.append (List.Sublist.refl _)
      have h1 : T = ((D.drop cLen).drop (r.1 * (s + 1))).take (s + 1) := by
        dsimp [T, blkStart]
        rw [List.drop_drop, Nat.add_comm cLen]
      rw [h1]
      exact List.Sublist.trans (List.take_sublist _ _) (List.drop_sublist _ _)
    rw [List.take_append_drop] at hSubD
    exact hSubD.nodup hD
  have hLenC : C.length = cLen := List.length_take_of_le (by omega)
  have hLenT : T.length = s + 1 := by
    dsimp [T]
    apply List.length_take_of_le
    rw [List.length_drop]
    have hexp : (r.1 + 1) * (s + 1) = r.1 * (s + 1) + (s + 1) := Nat.add_one_mul r.1 (s + 1)
    omega
  have hLenCT : (C ++ T).length = A := by
    rw [List.length_append, hLenC, hLenT]
    omega
  refine ⟨hGammasNz gammas[r] (List.getElem_mem r.2), ?_, ?_⟩
  · have hle := nodup_length_le_of_subset hndCT hSubCT
    rw [hLenCT] at hle
    exact hle
  · intro G_poly hGLen
    let S_γ := D.filter (fun z =>
      decide (CommRingOps.add (fg.1 z) (CommRingOps.mul gammas[r] (fg.2 z)) = CommRingOps.zero))
    let diff := RoundPoly.subCoeffs (vanishingPoly C) G_poly
    have hpLen : (vanishingPoly C).length = cLen + 1 := by
      rw [vanishingPoly_length, hLenC]
    have hGLtP : G_poly.length < (vanishingPoly C).length := by rw [hpLen]; omega
    have hDiffLen : diff.length = cLen + 1 := by
      dsimp [diff]
      rw [RoundPoly.subCoeffs_length, hpLen]
      exact Nat.max_eq_left (by omega)
    have hVanLast : (vanishingPoly C).getD cLen CommRingOps.zero = CommRingOps.one := by
      rw [← hLenC]
      exact vanishingPoly_last_one C
    have hDiffLast : diff.getD cLen CommRingOps.zero = CommRingOps.one := by
      have h := last_subCoeffs_vanishingPoly (vanishingPoly C) G_poly
        (by rw [hpLen]; omega) (by rwa [hpLen, Nat.add_sub_cancel]) hGLtP
      rwa [hpLen, Nat.add_sub_cancel] at h
    rcases exists_nonroot_of_monic_len cLen diff D hDiffLen hDiffLast hD (by omega)
      with ⟨x₀, _, hx₀Ne⟩
    have hndS : S_γ.Nodup := List.Pairwise.filter _ hD
    have hRoots := @RoundPoly.roots_nodup_length_le F _ _ (LawfulField.toNoZeroDivisors F)
      cLen diff S_γ hndS (by omega) ⟨x₀, hx₀Ne⟩
    have hSubAgree := filter_sub_length_le
      (fun z => decide (RoundPoly.evalCoeffs G_poly z = fg.2 z))
      (fun z => decide (RoundPoly.evalCoeffs diff z = CommRingOps.zero))
      (fun z hz => by
        have hEq : RoundPoly.evalCoeffs G_poly z = fg.2 z := of_decide_eq_true hz
        dsimp [diff, fg, scalarFloorWords] at hEq ⊢
        rw [RoundPoly.evalCoeffs_sub, hEq, LawfulCommRing.sub_self]
        exact decide_eq_true rfl)
      S_γ
    have hLeC : (S_γ.filter (fun z => decide (RoundPoly.evalCoeffs G_poly z = fg.2 z))).length ≤ cLen :=
      Nat.le_trans hSubAgree hRoots
    change (S_γ.filter (fun z => decide (RoundPoly.evalCoeffs G_poly z = fg.2 z))).length < A - s
    omega

private theorem filter_eq_singleton_of_nodup_iff {α : Type} (p : α → Bool) (z₀ : α) :
    ∀ {xs : List α}, xs.Nodup → z₀ ∈ xs → (∀ x ∈ xs, p x = true ↔ x = z₀) → xs.filter p = [z₀]
  | [], _, hz, _ => by cases hz
  | x :: xs, .cons hnot hnd, hz, hiff => by
    simp only [List.filter]
    cases hpx : p x
    · have hne : z₀ ≠ x := by
        intro heq; subst heq
        have ht := (hiff z₀ (.head _)).mpr rfl
        rw [hpx] at ht; cases ht
      cases hz with
      | head => exact False.elim (hne rfl)
      | tail _ hzs =>
        exact filter_eq_singleton_of_nodup_iff p z₀ hnd hzs (fun y hy => hiff y (.tail _ hy))
    · have hxEq : x = z₀ := (hiff x (.head _)).mp hpx
      subst hxEq
      rw [filter_eq_nil_of_all_false p xs]
      intro y hy
      cases hpy : p y
      · rfl
      · exact False.elim (hnot y hy ((hiff y (.tail _ hy)).mp hpy).symm)

private theorem zeroLossRow_nodup
    {F : Type} [LawfulField F] (z₀ : F) :
    ∀ {bs : List F}, bs.Nodup →
      (bs.map (fun β => (CommRingOps.neg (CommRingOps.mul β z₀), β))).Nodup
  | [], _ => .nil
  | b :: bs, .cons hnb hndb => by
    simp only [List.map]
    refine .cons ?_ (zeroLossRow_nodup z₀ hndb)
    intro q hq heq
    rw [List.mem_map] at hq
    rcases hq with ⟨b', hb', rfl⟩
    have hbEq : b = b' := (Prod.mk.inj heq).2
    exact hnb b' hb' hbEq

private theorem zeroLossBadPairs_nodup
    {F : Type} [LawfulField F] [DecidableEq F]
    {S_nz : List F} (hSnz : S_nz.Nodup) (hSnzNe : ∀ β ∈ S_nz, β ≠ CommRingOps.zero) :
    ∀ {zs : List F}, zs.Nodup →
      (zs.flatMap (fun z₀ => S_nz.map (fun β => (CommRingOps.neg (CommRingOps.mul β z₀), β)))).Nodup
  | [], _ => .nil
  | z₀ :: zs, .cons hnot hnd => by
    simp only [List.flatMap_cons]
    rw [List.nodup_append]
    refine ⟨zeroLossRow_nodup z₀ hSnz, zeroLossBadPairs_nodup hSnz hSnzNe hnd, ?_⟩
    intro p₁ hp₁ p₂ hp₂ heq
    subst heq
    rw [List.mem_map] at hp₁
    rw [List.mem_flatMap] at hp₂
    rcases hp₁ with ⟨β₁, hβ₁Mem, rfl⟩
    rcases hp₂ with ⟨z₁, hz₁Mem, hp₂'⟩
    rw [List.mem_map] at hp₂'
    rcases hp₂' with ⟨β₂, _, heq'⟩
    have hβEq : β₂ = β₁ := (Prod.mk.inj heq').2
    subst hβEq
    have hβNe := hSnzNe β₂ hβ₁Mem
    have hmulEq : CommRingOps.mul β₂ z₁ = CommRingOps.mul β₂ z₀ := by
      have hn := congrArg CommRingOps.neg (Prod.mk.inj heq').1
      simpa [LawfulCommRing.neg_neg] using hn
    have hzEq : z₁ = z₀ := by
      have hm := congrArg (CommRingOps.mul (LawfulField.inv β₂)) hmulEq
      simpa [← LawfulCommRing.mul_assoc, LawfulField.inv_mul_cancel hβNe,
             LawfulCommRing.one_mul] using hm
    exact hnot z₁ hz₁Mem hzEq.symm

private theorem exists_nonroot_or_all_roots
    {F : Type} [CommRingOps F] [DecidableEq F] (G : List F) :
    ∀ (C : List F),
      (∃ c ∈ C, RoundPoly.evalCoeffs G c ≠ CommRingOps.zero) ∨
      (∀ c ∈ C, RoundPoly.evalCoeffs G c = CommRingOps.zero)
  | [] => .inr (fun _ h => by cases h)
  | c :: cs =>
    if hc : RoundPoly.evalCoeffs G c = CommRingOps.zero then
      match exists_nonroot_or_all_roots G cs with
      | .inl ⟨x, hx, hne⟩ => .inl ⟨x, .tail _ hx, hne⟩
      | .inr hall => .inr (fun y hy => by
          cases hy with
          | head => exact hc
          | tail _ hm => exact hall y hm)
    else
      .inl ⟨c, .head _, hc⟩

/-- Adversarial received-word pair `(f = 0, g = 1_{D \ C})` for `[CWYZ26]` Proposition 6.2 (`s = 0`). -/
def zeroLossAffineWords
    {F : Type} [CommRingOps F] [DecidableEq F]
    (D : List F) (A : Nat) : (F → F) × (F → F) :=
  let C := D.take (A - 1)
  (fun _ => CommRingOps.zero, fun z => if z ∈ C then CommRingOps.zero else CommRingOps.one)

/-- **`#tooth` Proposition 6.2 (`tooth_affine_combiner_zero_loss_linear_floor`)**:
    When **zero** agreement loss ($s = 0$) is demanded, affine combiners revert to $\Omega(n / q)$:
    for ANY `d + 1 < A ≤ D.length` and ANY list `S_nz` of distinct non-zero challenges `β`:
    1. All `(D.length - A + 1) * S_nz.length` challenge pairs `(α, β) = (-β z₀, β)` (`z₀ ∈ D.drop (A - 1)`,
       `β ∈ S_nz`) are **pairwise distinct** (`Nodup`),
    2. Every such pair makes `f(z) + (α + β z) g(z)` vanish on **at least `A` points** of `D` (`P = 0`),
    3. **NO polynomial `G_poly` of degree `≤ d - 1`** agrees with `g` on all `A` points (`s = 0` FAILS!),
    4. Yet `(F = 0, G = 0)` agrees on `A - 1` points (**`s = 1` SUCCEEDS**), proving $s = 1$ is necessary! -/
theorem tooth_affine_combiner_zero_loss_linear_floor
    {F : Type} [LawfulField F] [DecidableEq F]
    (D S_nz : List F) (d A : Nat)
    (hD : D.Nodup)
    (hSnz : S_nz.Nodup)
    (hSnzNe : ∀ β ∈ S_nz, β ≠ CommRingOps.zero)
    (hA_lo : d + 1 < A)
    (hA_hi : A ≤ D.length) :
    let (f, g) := zeroLossAffineWords D A
    let restD := D.drop (A - 1)
    let badPairs := restD.flatMap (fun z₀ => S_nz.map (fun β => (CommRingOps.neg (CommRingOps.mul β z₀), β)))
    badPairs.length = (D.length - A + 1) * S_nz.length ∧
    badPairs.Nodup ∧
    ∀ p ∈ badPairs,
      let S_p := D.filter (fun z =>
        decide (CommRingOps.add (f z)
          (CommRingOps.mul (CommRingOps.add p.1 (CommRingOps.mul p.2 z)) (g z)) = CommRingOps.zero))
      A ≤ S_p.length ∧
      (∀ G_poly : List F, G_poly.length ≤ d →
        ∃ z ∈ S_p, RoundPoly.evalCoeffs G_poly z ≠ g z) ∧
      (S_p.filter (fun z => !(decide (CommRingOps.zero = f z) && decide (CommRingOps.zero = g z)))).length ≤ 1 := by
  dsimp only
  let C := D.take (A - 1)
  let restD := D.drop (A - 1)
  let fg := zeroLossAffineWords D A
  let badPairs := restD.flatMap (fun z₀ => S_nz.map (fun β => (CommRingOps.neg (CommRingOps.mul β z₀), β)))
  have hLenRest : restD.length = D.length - A + 1 := by
    dsimp [restD]; rw [List.length_drop]; omega
  have hBadLen : badPairs.length = (D.length - A + 1) * S_nz.length := by
    have aux : ∀ (zs : List F),
        (zs.flatMap (fun z₀ => S_nz.map (fun β => (CommRingOps.neg (CommRingOps.mul β z₀), β)))).length =
        zs.length * S_nz.length := by
      intro zs
      induction zs with
      | nil => simp
      | cons _ tl ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, ih]
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [aux restD, hLenRest]
  have hndRest : restD.Nodup := (List.drop_sublist (A - 1) D).nodup hD
  have hBadNodup : badPairs.Nodup := zeroLossBadPairs_nodup hSnz hSnzNe hndRest
  refine ⟨hBadLen, hBadNodup, ?_⟩
  intro p hp
  rw [List.mem_flatMap] at hp
  rcases hp with ⟨z₀, hz₀Rest, hpMap⟩
  rw [List.mem_map] at hpMap
  rcases hpMap with ⟨β, hβMem, rfl⟩
  have hβNe := hSnzNe β hβMem
  have hDisjCRest : ∀ x ∈ C, x ∉ restD := by
    have hApp : C ++ restD = D := List.take_append_drop (A - 1) D
    have hndApp : (C ++ restD).Nodup := hApp ▸ hD
    rw [List.nodup_append] at hndApp
    intro x hxC hxR
    exact hndApp.2.2 x hxC x hxR rfl
  have hz₀NotC : z₀ ∉ C := fun hC => hDisjCRest z₀ hC hz₀Rest
  let predP := fun z =>
    decide (CommRingOps.add (fg.1 z)
      (CommRingOps.mul
        (CommRingOps.add (CommRingOps.neg (CommRingOps.mul β z₀)) (CommRingOps.mul β z))
        (fg.2 z)) = CommRingOps.zero)
  have hFiltC : C.filter predP = C := by
    apply filter_eq_self_of_all predP C
    intro z hzC
    dsimp [predP, fg, zeroLossAffineWords]
    simp [C, hzC, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  have hFiltRest : restD.filter predP = [z₀] := by
    apply filter_eq_singleton_of_nodup_iff predP z₀ hndRest hz₀Rest
    intro z hzR
    have hzNotC : z ∉ C := fun hC => hDisjCRest z hC hzR
    dsimp [predP, fg, zeroLossAffineWords]
    simp only [C, hzNotC, ↓reduceIte, LawfulCommRing.zero_add, LawfulCommRing.mul_one,
               decide_eq_true_eq]
    rw [LawfulCommRing.add_comm, ← LawfulCommRing.sub_eq_add_neg, ← LawfulCommRing.mul_sub]
    constructor
    · intro h0
      rcases LawfulField.mul_eq_zero h0 with hb0 | hz0
      · exact False.elim (hβNe hb0)
      · exact LawfulCommRing.sub_eq_zero_iff.mp hz0
    · intro heq; subst heq
      rw [LawfulCommRing.sub_self, LawfulCommRing.mul_zero]
  have hSpEq : D.filter predP = C ++ [z₀] := by
    have hApp : D = C ++ restD := (List.take_append_drop (A - 1) D).symm
    conv => lhs; rw [hApp]
    rw [List.filter_append, hFiltC, hFiltRest]
  have hLenC : C.length = A - 1 := by
    dsimp [C]; exact List.length_take_of_le (by omega)
  refine ⟨?_, ?_, ?_⟩
  · change A ≤ (D.filter predP).length
    rw [hSpEq, List.length_append, hLenC, List.length_singleton]
    omega
  · intro G_poly hGLen
    change ∃ z ∈ D.filter predP, RoundPoly.evalCoeffs G_poly z ≠ fg.2 z
    rcases exists_nonroot_or_all_roots G_poly C with ⟨c, hcMem, hcNe⟩ | hAllRoots
    · have hgc : fg.2 c = CommRingOps.zero := by
        dsimp [fg, zeroLossAffineWords]; simp [C, hcMem]
      refine ⟨c, by rw [hSpEq, List.mem_append]; exact .inl hcMem, ?_⟩
      rwa [hgc]
    · refine ⟨z₀, by rw [hSpEq, List.mem_append]; exact .inr (.head _), ?_⟩
      have hgz₀ : fg.2 z₀ = CommRingOps.one := by
        dsimp [fg, zeroLossAffineWords]; simp [C, hz₀NotC]
      rw [hgz₀]
      if hz0Eq : RoundPoly.evalCoeffs G_poly z₀ = CommRingOps.zero then
        rw [hz0Eq]
        exact LawfulField.zero_ne_one
      else
        have hFiltAll :
            C.filter (fun c => decide (RoundPoly.evalCoeffs G_poly c = CommRingOps.zero)) = C :=
          filter_eq_self_of_all _ C (fun c hc => decide_eq_true (hAllRoots c hc))
        have hndC : C.Nodup := (List.take_sublist (A - 1) D).nodup hD
        cases d with
        | zero =>
          have hNil : G_poly = [] := by
            cases G_poly with
            | nil => rfl
            | cons _ _ => simp at hGLen
          subst hNil
          exact False.elim (hz0Eq rfl)
        | succ d' =>
          have hRoots := @RoundPoly.roots_nodup_length_le F _ _ (LawfulField.toNoZeroDivisors F)
            d' G_poly C hndC hGLen ⟨z₀, hz0Eq⟩
          rw [hFiltAll, hLenC] at hRoots
          omega
  · let lossPred := fun z =>
      !(decide (CommRingOps.zero = fg.1 z) && decide (CommRingOps.zero = fg.2 z))
    change ((D.filter predP).filter lossPred).length ≤ 1
    rw [hSpEq, List.filter_append]
    have hCZero : C.filter lossPred = [] := by
      apply filter_eq_nil_of_all_false lossPred C
      intro z hzC
      dsimp [lossPred, fg, zeroLossAffineWords]
      simp [C, hzC]
    rw [hCZero, List.nil_append]
    simp only [List.filter]
    cases lossPred z₀ <;> simp


/-- **Non-Vacuous Inhabitedness Witness (`inhabited_affine_proximity_gaps`)**:
    Instantiates `welch_berlekamp_affine_proximity_gap` over `Goldilocks` with `d = 1, A = 5`,
    `D = [0, 1, 2, 3, 4, 5]` (`n = 6`, `2 * 6 + 1 + 1 = 14 < 15 = 3 * 5`), `S = [0, 1, 2, 3, 4, 5, 6]`,
    and a **strictly non-empty** exceptional list `badPairs = [(0, 1)]` (`P = 0`) where two accidental
    agreements at `z = 4` (`f(4) = -4, g(4) = 1`) and `z = 5` (`f(5) = -5, g(5) = 1`) genuinely
    defeat every `s = 1` witness (`¬ HasAffineWitnessS1`) while satisfying the proximity-gap bound! -/
theorem inhabited_affine_proximity_gaps :
    let g0 := Goldilocks.ofNat 0
    let g1 := Goldilocks.ofNat 1
    let g2 := Goldilocks.ofNat 2
    let g3 := Goldilocks.ofNat 3
    let g4 := Goldilocks.ofNat 4
    let g5 := Goldilocks.ofNat 5
    let g6 := Goldilocks.ofNat 6
    let D : List Goldilocks := [g0, g1, g2, g3, g4, g5]
    let S : List Goldilocks := [g0, g1, g2, g3, g4, g5, g6]
    let f : Goldilocks → Goldilocks := fun z =>
      if z = g4 then CommRingOps.neg g4
      else if z = g5 then CommRingOps.neg g5
      else g0
    let g : Goldilocks → Goldilocks := fun z =>
      if z = g4 ∨ z = g5 then g1 else g0
    let badPairs : List (Goldilocks × Goldilocks) := [(g0, g1)]
    0 < badPairs.length ∧
    (∀ p ∈ badPairs, ¬ HasAffineWitnessS1 1 f g D p.1 p.2 []) ∧
    badPairs.length ≤ Nat.max S.length (D.length * (D.length - 1) / 2) := by
  dsimp only
  let g0 := Goldilocks.ofNat 0
  let g1 := Goldilocks.ofNat 1
  let g2 := Goldilocks.ofNat 2
  let g3 := Goldilocks.ofNat 3
  let g4 := Goldilocks.ofNat 4
  let g5 := Goldilocks.ofNat 5
  let g6 := Goldilocks.ofNat 6
  let D : List Goldilocks := [g0, g1, g2, g3, g4, g5]
  let S : List Goldilocks := [g0, g1, g2, g3, g4, g5, g6]
  let f : Goldilocks → Goldilocks := fun z =>
    if z = g4 then CommRingOps.neg g4
    else if z = g5 then CommRingOps.neg g5
    else g0
  let g : Goldilocks → Goldilocks := fun z =>
    if z = g4 ∨ z = g5 then g1 else g0
  have hExc01 : ¬ HasAffineWitnessS1 1 f g D g0 g1 [] := by
    rintro ⟨F_poly, G_poly, _, hGLen, _, hLoss⟩
    have hGConst : ∀ x y : Goldilocks,
        RoundPoly.evalCoeffs G_poly x = RoundPoly.evalCoeffs G_poly y := by
      rcases G_poly with _ | ⟨c, _ | _⟩
      · intro _ _; rfl
      · intro _ _; simp [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero]
      · simp at hGLen
    have hSpEq : D.filter (fun z =>
        decide (RoundPoly.evalCoeffs ([] : List Goldilocks) z =
          CommRingOps.add (f z)
            (CommRingOps.mul (CommRingOps.add g0 (CommRingOps.mul g1 z)) (g z)))) = D := by
      decide
    rw [hSpEq] at hLoss
    if hc0 : RoundPoly.evalCoeffs G_poly g0 = g0 then
      have h4 : RoundPoly.evalCoeffs G_poly g4 = g0 := (hGConst g4 g0).trans hc0
      have h5 : RoundPoly.evalCoeffs G_poly g5 = g0 := (hGConst g5 g0).trans hc0
      have hg4 : g g4 = g1 := by decide
      have hg5 : g g5 = g1 := by decide
      have h10 : g0 ≠ g1 := by decide
      have hSub : ∀ z ∈ ([g4, g5] : List Goldilocks),
          z ∈ D.filter (fun w =>
            !(decide (RoundPoly.evalCoeffs F_poly w = f w) &&
              decide (RoundPoly.evalCoeffs G_poly w = g w))) := by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · rw [List.mem_filter]; refine ⟨by decide, ?_⟩; simp [h4, hg4, h10]
        · rw [List.mem_filter]; refine ⟨by decide, ?_⟩; simp [h5, hg5, h10]
      have hge2 := nodup_length_le_of_subset (L := ([g4, g5] : List Goldilocks)) (by decide) hSub
      simp only [List.length_cons, List.length_nil] at hge2; omega
    else
      have h1 : RoundPoly.evalCoeffs G_poly g1 = RoundPoly.evalCoeffs G_poly g0 := hGConst g1 g0
      have hg0 : g g0 = g0 := by decide
      have hg1 : g g1 = g0 := by decide
      have hSub : ∀ z ∈ ([g0, g1] : List Goldilocks),
          z ∈ D.filter (fun w =>
            !(decide (RoundPoly.evalCoeffs F_poly w = f w) &&
              decide (RoundPoly.evalCoeffs G_poly w = g w))) := by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · rw [List.mem_filter]; refine ⟨by decide, ?_⟩; simp [hg0, hc0]
        · rw [List.mem_filter]; refine ⟨by decide, ?_⟩; simp [hg1, h1, hc0]
      have hge2 := nodup_length_le_of_subset (L := ([g0, g1] : List Goldilocks)) (by decide) hSub
      simp only [List.length_cons, List.length_nil] at hge2; omega
  have hExcAll : ∀ p ∈ ([(g0, g1)] : List (Goldilocks × Goldilocks)),
      ¬ HasAffineWitnessS1 1 f g D p.1 p.2 [] := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact hExc01
  refine ⟨by decide, hExcAll, ?_⟩
  exact welch_berlekamp_affine_proximity_gap f g D S 1 5 [(g0, g1)] (fun _ => [])
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro p hp; simp at hp; subst hp; poly_eval [indexOf?, scalarFloorWords, zeroLossAffineWords])
    (by intro _ _; simp)
    (by intro p hp; simp at hp; subst hp; decide)
    hExcAll


/-- **`#tooth` & Beyond-Sudan `m = 2` Inhabitedness Witness
    (`tooth_guruswami_sudan_m2_beyond_sudan_and_sharp_threshold`)**:
    Over `Goldilocks` on `domain = [0, 1, 2, 3, 4, 5]` (`n = 6, d = 2, D = 3`):
    1. **Strictly beyond unique decoding AND beyond `m = 1` Sudan**: at `A = 4` (`2 * A = 8 ≤ n + d`),
       `m = 1` Sudan fails for EVERY `D` (`gsMonomialCount 4 2 D ≤ 6`), two distinct degree-`≤ 2`
       polynomials (`0` and `X(X - 1)`) simultaneously agree with a single received word on `4` points,
       and `m = 2` `guruswami_sudan_unconditional_list_bound` proves `polys.length ≤ 3`;
    2. **Sharp `#tooth` threshold sensitivity (`A = 4 → A = 3`)**: dropping the agreement threshold
       by ONE to `A = 3` exhibits **4 > 3 = D** distinct canonical degree-`≤ 2` polynomials
       (`0`, `-X + X^2`, `-3 + 3X`, `-28 + 18X - 2X^2`) all agreeing with `w = [0, 0, 0, 6, 12, 12]`
       on `3` distinct points of `domain`! -/
theorem tooth_guruswami_sudan_m2_beyond_sudan_and_sharp_threshold :
    let g := Goldilocks.ofNat
    let dom : List Goldilocks := [g 0, g 1, g 2, g 3, g 4, g 5]
    -- Part 1: `m = 1` Sudan fails (`≤ 6` monomials for all `D`), `2` distinct close polys at `A = 4`, `m = 2` bounds `≤ 3`
    (∀ D : Nat, gsMonomialCount 4 2 D ≤ 6) ∧
    dom.length * (2 * (2 + 1) / 2) < gsMonomialCount (2 * 4) 2 3 ∧
    (∃ (wordAtFour : Goldilocks → Goldilocks) (twoPolys : List (GsUniPoly Goldilocks)),
      twoPolys.Nodup ∧ twoPolys.length = 2 ∧
      (∀ P ∈ twoPolys, P.coeffs.length ≤ 2 + 1 ∧
        ∃ xs : List Goldilocks, xs.Nodup ∧ 4 ≤ xs.length ∧
          ∀ x ∈ xs, x ∈ dom ∧ evalCoeffs P.coeffs x = wordAtFour x) ∧
      twoPolys.length ≤ 3) ∧
    -- Part 2 (`#tooth`): at `A = 3` (`A - 1`), `4 > 3` distinct degree-`≤ 2` polys agree on `3` points!
    (∃ (w3 : Goldilocks → Goldilocks) (fourPolys : List (GsUniPoly Goldilocks)),
      fourPolys.Nodup ∧ 3 < fourPolys.length ∧
      ∀ P ∈ fourPolys, P.coeffs.length ≤ 2 + 1 ∧
        ∃ xs : List Goldilocks, xs.Nodup ∧ 3 ≤ xs.length ∧
          ∀ x ∈ xs, x ∈ dom ∧ evalCoeffs P.coeffs x = w3 x) := by
  dsimp only
  let g := Goldilocks.ofNat
  let dom : List Goldilocks := [g 0, g 1, g 2, g 3, g 4, g 5]
  refine ⟨?_, by decide, ?_, ?_⟩
  · intro D
    have hZeroTail : ∀ (k start : Nat), 2 ≤ start →
        ((List.range k).map (fun j => 4 - (start + j) * 2)).sum = 0 := by
      intro k
      induction k with
      | zero => intro _ _; rfl
      | succ k' ih =>
        intro start hs
        rw [gs_range_succ_map, List.map_cons, List.sum_cons, List.map_map]
        have hhead : 4 - (start + 0) * 2 = 0 := by omega
        have htail : (List.range k').map ((fun j => 4 - (start + j) * 2) ∘ (· + 1)) =
            (List.range k').map (fun j => 4 - ((start + 1) + j) * 2) := by
          apply List.map_congr_left
          intro j _
          dsimp only [Function.comp]
          have heq : start + (j + 1) = (start + 1) + j := by omega
          rw [heq]
        rw [hhead, htail, ih (start + 1) (by omega)]
    rcases D with _ | ⟨_ | D'⟩
    · decide
    · decide
    · unfold gsMonomialCount
      rw [gs_range_succ_map, List.map_cons, List.sum_cons, List.map_map,
          gs_range_succ_map, List.map_cons, List.sum_cons, List.map_map]
      have htail : (List.range (D' + 1)).map (((fun j => 4 - j * 2) ∘ (· + 1)) ∘ (· + 1)) =
          (List.range (D' + 1)).map (fun j => 4 - (2 + j) * 2) := by
        apply List.map_congr_left
        intro j _
        dsimp only [Function.comp]
        have heq : j + 1 + 1 = 2 + j := by omega
        rw [heq]
      rw [htail, hZeroTail (D' + 1) 2 (Nat.le_refl 2)]
      decide
  · let wordAtFour : Goldilocks → Goldilocks := fun x =>
      if x = g 4 then g 12 else if x = g 5 then g 20 else g 0
    let p0 : GsUniPoly Goldilocks := GsUniPoly.ofCoeffs []
    let p1 : GsUniPoly Goldilocks := GsUniPoly.ofCoeffs [g 0, CommRingOps.neg (g 1), g 1]
    have hnd : ([p0, p1] : List (GsUniPoly Goldilocks)).Nodup := by decide
    have hClose : ∀ P ∈ ([p0, p1] : List (GsUniPoly Goldilocks)),
        P.coeffs.length ≤ 2 + 1 ∧
        ∃ xs : List Goldilocks, xs.Nodup ∧ 4 ≤ xs.length ∧
          ∀ x ∈ xs, x ∈ dom ∧ evalCoeffs P.coeffs x = wordAtFour x := by
      intro P hP
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl
      · refine ⟨by decide, [g 0, g 1, g 2, g 3], by decide, by decide, ?_⟩
        intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> decide
      · refine ⟨by decide, [g 0, g 1, g 4, g 5], by decide, by decide, ?_⟩
        intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> decide
    exact ⟨wordAtFour, [p0, p1], hnd, rfl, hClose,
      guruswami_sudan_unconditional_list_bound dom wordAtFour 2 4 3 2 (by decide)
        [p0, p1] hnd hClose⟩
  · let w3 : Goldilocks → Goldilocks := fun x =>
      if x = g 3 then g 6 else if x = g 4 ∨ x = g 5 then g 12 else g 0
    let q0 : GsUniPoly Goldilocks := GsUniPoly.ofCoeffs []
    let q1 : GsUniPoly Goldilocks := GsUniPoly.ofCoeffs [g 0, CommRingOps.neg (g 1), g 1]
    let q2 : GsUniPoly Goldilocks := GsUniPoly.ofCoeffs [CommRingOps.neg (g 3), g 3]
    let q3 : GsUniPoly Goldilocks :=
      GsUniPoly.ofCoeffs [CommRingOps.neg (g 28), g 18, CommRingOps.neg (g 2)]
    refine ⟨w3, [q0, q1, q2, q3], by decide, by decide, ?_⟩
    intro P hP
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl | rfl | rfl
    · refine ⟨by decide, [g 0, g 1, g 2], by decide, by decide, ?_⟩
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide
    · refine ⟨by decide, [g 0, g 3, g 4], by decide, by decide, ?_⟩
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide
    · refine ⟨by decide, [g 1, g 3, g 5], by decide, by decide, ?_⟩
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide
    · refine ⟨by decide, [g 2, g 4, g 5], by decide, by decide, ?_⟩
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide


#verify_constructive tooth_scalar_combiner_linear_n_over_q_floor
#verify_constructive tooth_affine_combiner_zero_loss_linear_floor
#verify_constructive inhabited_affine_proximity_gaps
#verify_constructive tooth_guruswami_sudan_m2_beyond_sudan_and_sharp_threshold

end Qsag

namespace Qsag
open CommRingOps RoundPoly UPoly Poly3

/-- The bound `k < p` cannot be dropped: `p = 0` in `Goldilocks`. -/
theorem tooth_natCast_prime_eq_zero :
    ∃ k : Nat, 1 ≤ k ∧ ¬ (CRing.natCast k : Goldilocks) ≠ zero :=
  ⟨goldilocksPrime, by decide, fun h => h (Goldilocks.ext (by
    rw [Goldilocks.natCast_val, Nat.mod_self]; rfl))⟩


namespace IncidenceTests
open UPoly Poly3

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

def dom : List Goldilocks := [g 0, g 1, g 2]
def pool : List Goldilocks := [g 0, g 1]

/-- The hypotheses of `affineMcaBound_ge_card` hold together: in the unique-decoding regime
    `2|D| + d + 1 < 3A` the Welch–Berlekamp bound `max(|S|, |D|(|D|-1)/2) = 3` is a valid
    bound, and it is indeed at least `|S| = 2`. -/
theorem inhabited_affineMcaBound_ge_card :
    ∃ (D S : List Goldilocks) (d A bad : Nat), AffineMcaBound D S d A bad ∧ D.Nodup ∧
      S.Nodup ∧ neg one ∉ D ∧ 1 ≤ d ∧ d + 2 ≤ A ∧ A ≤ D.length :=
  ⟨dom, pool, 1, 3, _,
    affineMcaBound_welch_berlekamp dom pool 1 3 (by decide) (by decide) (by decide) (by decide),
    by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The threshold hypothesis `d + 2 ≤ A` is needed: at `A = 1` every pair of words has
    correlated agreement `≥ 0`, so `bad = 0` is a valid bound although `|S| = 2`. -/
theorem tooth_ge_card_needs_threshold :
    ∃ (D S : List Goldilocks) (d A bad : Nat), D.Nodup ∧ S.Nodup ∧ neg one ∉ D ∧ 1 ≤ d ∧
      A ≤ D.length ∧ AffineMcaBound D S d A bad ∧ ¬ S.length ≤ bad :=
  ⟨dom, pool, 1, 1, 0, by decide, by decide, by decide, by decide, by decide,
    fun _ hFar => absurd ⟨[], [], Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩ hFar, by decide⟩

/-- A concrete failure of a field-independent bound: with `Dg = 0` the bound `0` is refuted
    on `|D| = 3`, `|S| = 2`, `d = 1`, `A = 3`. -/
theorem field_independent_bound_fails_example :
    ¬ AffineMcaBound dom pool 1 3 (0 ^ 2 + 2 * 1 * 0) :=
  affineMcaBound_without_field_term_fails dom pool 1 3 0 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

#verify_constructive affineMcaBound_ge_card affineMcaBound_without_field_term_fails
#verify_constructive Poly3.roots_on_line_card_le poleWords_far poleWords_accept
#verify_constructive Poly3.jet_cover Poly3.jet_hyps UPoly.mapHom_hasse
#verify_constructive tooth_ge_card_needs_threshold field_independent_bound_fails_example
#tooth_pair affineMcaBound_ge_card vs tooth_ge_card_needs_threshold
#verify_inhabited affineMcaBound_ge_card inhabited_affineMcaBound_ge_card


#verify_constructive tooth_natCast_prime_eq_zero
#tooth_pair Goldilocks.natCast_ne_zero vs tooth_natCast_prime_eq_zero

end IncidenceTests

namespace BivariateGaussTests
open UPoly Poly2

private theorem isPrimY_monic_deg1 (c : UPoly Goldilocks) :
    IsPrimY (ofList [c, one] : Poly2 Goldilocks) := by
  have hc1 : coeffAt (ofList [c, one] : Poly2 Goldilocks).coeffs 1 = one := by
    rw [coeffAt_ofList]; rfl
  refine ⟨fun e => NontrivialRing.one_ne_zero (by
    rw [← hc1, e, coeffs_zero, coeffAt_nil]), fun g hg => ?_⟩
  obtain ⟨q, hq⟩ := hg 1
  rw [hc1] at hq
  have hg0 : g ≠ zero := fun e => NontrivialRing.one_ne_zero (by rw [hq, e, LawfulCommRing.zero_mul])
  have hq0 : q ≠ zero := fun e => NontrivialRing.one_ne_zero (by rw [hq, e, LawfulCommRing.mul_zero])
  have hd := UPoly.natDeg_mul hg0 hq0
  rw [← hq, natDeg_one] at hd; omega

/-- Witness that `isPrimY_mul` and `tdeg_mul` are inhabited: `Z + Y` and `Z - Y` are `Y`-primitive
    and their product `Z² - Y²` is `Y`-primitive of total degree `2`. -/
theorem inhabited_isPrimY_mul :
    ∃ A B : Poly2 Goldilocks,
      IsPrimY A ∧ IsPrimY B ∧ IsPrimY (mul A B) ∧ tdeg (mul A B) = 2 := by
  let A : Poly2 Goldilocks := ofList [X, one]
  let B : Poly2 Goldilocks := ofList [neg X, one]
  have hA : IsPrimY A := isPrimY_monic_deg1 X
  have hB : IsPrimY B := isPrimY_monic_deg1 (neg X)
  exact ⟨A, B, hA, hB, isPrimY_mul hA hB, by poly_eval [A, B]⟩

/-- `#tooth`: dropping `IsPrimY A` invalidates `isPrimY_mul`: `A = Y · 1` (`C X`) and `B = Z` (`X`)
    satisfy `A ≠ 0 ∧ IsPrimY B`, yet `mul A B = Y · Z` is divisible by `Y` (`natDeg = 1 ≠ 0`). -/
theorem tooth_isPrimY_needs_prim :
    ∃ A B : Poly2 Goldilocks,
      A ≠ zero ∧ IsPrimY B ∧ ¬ IsPrimY (mul A B) := by
  let A : Poly2 Goldilocks := C X
  let B : Poly2 Goldilocks := ofList [zero, one]
  refine ⟨A, B, by decide +kernel, isPrimY_monic_deg1 zero, fun hPrim => ?_⟩
  have hAll : ∀ k, ∃ q : UPoly Goldilocks, coeffAt (mul A B).coeffs k = mul X q := fun k => by
    dsimp [A]
    rw [coeffAt_C_mul]
    exact ⟨coeffAt B.coeffs k, rfl⟩
  have hd0 := hPrim.2 X hAll
  have hd1 : (X : UPoly Goldilocks).natDeg = 1 := by decide +kernel
  omega

#verify_constructive Poly2.tdeg_mul Poly2.tdeg_C Poly2.contY_mul_primY Poly2.isPrimY_mul
#verify_constructive inhabited_isPrimY_mul tooth_isPrimY_needs_prim
#tooth_pair Poly2.isPrimY_mul vs tooth_isPrimY_needs_prim
#verify_inhabited Poly2.isPrimY_mul inhabited_isPrimY_mul

end BivariateGaussTests

namespace NonpersistentIncidence
open Poly2 SylElim
namespace Tests
private def coordEquation (z : Goldilocks) : Poly2 Goldilocks := C (ofList [neg z, one])
private def twoPts : List (Goldilocks × Goldilocks) := [(zero, zero), (one, zero)]
private def twoCoords : List Goldilocks := [zero, one]
private theorem primitive_X : IsPrimY (X : Poly2 Goldilocks) :=
  BivariateGaussTests.isPrimY_monic_deg1 zero

/-- A sharp two-point instance of the curve count: `Z=0` meets `Y=0` and `Y=1`,
with one incident coordinate per point and no shared incident coordinate. -/
theorem inhabited_curve_incidence :
    ∃ (C : Poly2 Goldilocks) (D : List Goldilocks) (equation : Goldilocks → Poly2 Goldilocks)
      (pts : List (Goldilocks × Goldilocks)) (M A B : Nat),
      IsPrimY C ∧ 1 ≤ C.natDeg ∧ D.Nodup ∧ B < A ∧
      (∀ z ∈ D, tdeg (equation z) ≤ M) ∧
      (∀ z ∈ D, (∃ Q, equation z = mul C Q) ∨ CoprimeZ C (equation z)) ∧
      pts.Nodup ∧ (∀ p ∈ pts, C.eval2 p.1 p.2 = zero) ∧
      (∀ p ∈ pts, A ≤ (D.filter (fun z => decide ((equation z).eval2 p.1 p.2 = zero))).length) ∧
      (∀ p ∈ pts, ∀ q ∈ pts, p ≠ q →
        (D.filter (fun z => decide ((equation z).eval2 p.1 p.2 = zero) &&
          decide ((equation z).eval2 q.1 q.2 = zero))).length ≤ B) ∧
      pts.length = 2 ∧ pts.length = Nat.max 1 ((D.length * (tdeg C * M * C.natDeg)) / (A-B)) := by
  refine ⟨X, twoCoords, coordEquation, twoPts, 1, 1, 0, primitive_X,
    by decide +kernel, by decide +kernel, by decide, by poly_eval [coordEquation, twoPts, twoCoords], ?_,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    rfl, by poly_eval [coordEquation, twoPts, twoCoords]⟩
  intro z hz
  right
  refine ⟨zero, one, ofList [neg z, one], ?_, ?_⟩
  · have hz' : z = zero ∨ z = one := by
      simpa only [twoCoords, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using hz
    rcases hz' with rfl | rfl <;> decide +kernel
  · rw [LawfulCommRing.zero_mul, LawfulCommRing.one_mul, LawfulCommRing.zero_add]
    rfl

/-- At `A=B`, every coordinate may contain the whole curve. The nonzero denominator
hypothesis cannot be removed, even with a primitive curve and a valid refinement. -/
theorem tooth_curve_incidence_needs_gap :
    ∃ (C : Poly2 Goldilocks) (D : List Goldilocks) (equation : Goldilocks → Poly2 Goldilocks)
      (pts : List (Goldilocks × Goldilocks)) (M A B : Nat),
      IsPrimY C ∧ 1 ≤ C.natDeg ∧ D.Nodup ∧
      (∀ z ∈ D, tdeg (equation z) ≤ M) ∧
      (∀ z ∈ D, (∃ Q, equation z = mul C Q) ∨ CoprimeZ C (equation z)) ∧
      pts.Nodup ∧ (∀ p ∈ pts, C.eval2 p.1 p.2 = zero) ∧
      (∀ p ∈ pts, A ≤ (D.filter (fun z => decide ((equation z).eval2 p.1 p.2 = zero))).length) ∧
      (∀ p ∈ pts, ∀ q ∈ pts, p ≠ q →
        (D.filter (fun z => decide ((equation z).eval2 p.1 p.2 = zero) &&
          decide ((equation z).eval2 q.1 q.2 = zero))).length ≤ B) ∧
      ¬ pts.length ≤ Nat.max 1 ((D.length * (tdeg C * M * C.natDeg)) / (A-B)) := by
  refine ⟨X, [zero], (fun _ => zero), twoPts, 0, 1, 1, primitive_X,
    by decide +kernel, by decide +kernel, by poly_eval [coordEquation, twoPts, twoCoords],
    (fun _ _ => .inl ⟨zero, (LawfulCommRing.mul_zero _).symm⟩),
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

private def mixedWords : (Goldilocks → Goldilocks) × (Goldilocks → Goldilocks) :=
  (fun _ => zero, fun z => if z = zero ∨ z = one then zero else one)
private def fourCoords : List Goldilocks :=
  [zero, one, Goldilocks.ofNat 2, Goldilocks.ofNat 3]

/-- An actually accepted nonpersistent candidate: the zero challenge and zero polynomial
agree everywhere, but a constant numerator cannot explain three coordinates when `g` is
zero on two positions and one on two positions. -/
theorem inhabited_nonpersistent_candidate :
    ∃ (x : (Goldilocks → Goldilocks) × (Goldilocks → Goldilocks)) (D : List Goldilocks)
      (d A B : Nat) (α β : Goldilocks) (P : UPoly Goldilocks),
      D.Nodup ∧ d + 1 ≤ B ∧ B < A ∧ P.natDeg ≤ d ∧
      A ≤ (D.filter (foldAgreePt x α β P)).length ∧ ¬ IsPersistent x D d B α β P := by
  refine ⟨mixedWords, fourCoords, 0, 4, 3, zero, zero, zero,
    by decide +kernel, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  rintro ⟨H, L, _, _, hdeg, hsize⟩
  let c := coeffAt H.coeffs 0
  have hH : H = C c := by
    apply ext_coeffAt
    intro k
    cases k with
    | zero => rw [coeffAt_C_zero]
    | succ k => rw [coeffAt_C_succ, H.coeffAt_eq_zero_of_natDeg_lt (by omega)]
  have heval : ∀ z, H.eval z = c := fun z => by rw [hH, eval_C]
  let good := fourCoords.filter (fun z => decide (L.eval z ≠ zero) &&
    foldAgreePt mixedWords zero zero zero z && decide (H.eval z = mul (mixedWords.2 z) (L.eval z)))
  have hnd : good.Nodup := nodup_filter _ fourCoords (by decide +kernel)
  have hbound : good.length ≤ 2 := by
    if hc : c = zero then
      have hsub : ∀ z ∈ good, z ∈ fourCoords.filter (fun z => decide (mixedWords.2 z = zero)) := by
        intro z hz
        obtain ⟨hzD, hgood⟩ := List.mem_filter.mp hz
        obtain ⟨hleft, hHL⟩ := Bool.and_eq_true_iff.mp hgood
        obtain ⟨hL, _⟩ := Bool.and_eq_true_iff.mp hleft
        have hmul := (of_decide_eq_true hHL).symm
        rw [heval z, hc] at hmul
        have hg := (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hmul).resolve_right
          (of_decide_eq_true hL)
        exact List.mem_filter.mpr ⟨hzD, decide_eq_true hg⟩
      have hb := nodup_length_le_of_subset hnd hsub
      have hn : (fourCoords.filter (fun z => decide (mixedWords.2 z = zero))).length = 2 :=
        by decide +kernel
      omega
    else
      have hsub : ∀ z ∈ good, z ∈ fourCoords.filter (fun z => decide (mixedWords.2 z ≠ zero)) := by
        intro z hz
        obtain ⟨hzD, hgood⟩ := List.mem_filter.mp hz
        have hHL := of_decide_eq_true (Bool.and_eq_true_iff.mp hgood).2
        have hg : mixedWords.2 z ≠ zero := fun hg => hc (by
          rw [heval z, hg, LawfulCommRing.zero_mul] at hHL
          exact hHL)
        exact List.mem_filter.mpr ⟨hzD, decide_eq_true hg⟩
      have hb := nodup_length_le_of_subset hnd hsub
      have hn : (fourCoords.filter (fun z => decide (mixedWords.2 z ≠ zero))).length = 2 :=
        by decide +kernel
      omega
  change 3 ≤ good.length at hsize
  omega

#verify_constructive inhabited_nonpersistent_candidate
#verify_constructive inhabited_curve_incidence tooth_curve_incidence_needs_gap
#verify_inhabited curve_incidence_card_le inhabited_curve_incidence
#tooth_pair curve_incidence_card_le vs tooth_curve_incidence_needs_gap
end Tests
end NonpersistentIncidence

namespace GapTests
open UPoly Poly3

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

/-- The hypotheses of the assembly theorem hold together (with an empty challenge set, where
    the residual count is `0`). -/
theorem inhabited_assembly :
    ∃ (D S : List Goldilocks) (d A m Wx Dy rest : Nat), NonExcludedBound D S d A m Wx Dy rest ∧
      D.Nodup ∧ S.Nodup ∧ D.length * triCount 1 m Dy m < triCount d Wx Dy (Dy + 1) ∧
      Wx + Dy ≤ m * A :=
  ⟨[g 0, g 1], [], 1, 3, 1, 2, 1, 0, (fun _ _ L _ h => by
      cases L with
      | nil => exact Nat.le_refl 0
      | cons p _ =>
        exact absurd (h p (.head _)).1 (by simp [prodPool.public_eqs])),
    by decide, by decide, by poly_eval [g], by decide⟩

def dom11 : List Goldilocks :=
  [g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7, g 8, g 9, g 10]

/-- The hypotheses of `cwyz26_affineMcaBound_sliced` hold together at `|D| = 11`, `d = 1`,
    `A = 8`, with `A ≤ |D|` and outside the Welch–Berlekamp regime `2|D| + d + 1 < 3A` of
    `affineMcaBound_welch_berlekamp`. -/
theorem inhabited_sliced :
    ∃ (D S : List Goldilocks) (d A B m Wx Dy : Nat), D.Nodup ∧ S.Nodup ∧
      D.length * triCount 1 m Dy m < triCount d Wx Dy (Dy + 1) ∧ Wx + Dy ≤ m * A ∧
      1 ≤ d ∧ 1 ≤ Dy ∧ d + 1 ≤ B ∧ D.length * (d + 1) < B * B ∧ B < A ∧
      (∀ k, 1 ≤ k → k ≤ Dy → (CRing.natCast k : Goldilocks) ≠ zero) ∧
      A ≤ D.length ∧ ¬ 2 * D.length + d + 1 < 3 * A := by
  have hchar : ∀ k, k ≤ 4 → 1 ≤ k → (CRing.natCast k : Goldilocks) ≠ zero := by decide +kernel
  exact ⟨dom11, dom11, 1, 8, 5, 2, 12, 4, by decide +kernel, by decide +kernel, by poly_eval [g, dom11],
    by decide, by decide, by decide, by decide, by decide, by decide,
    fun k h1 h2 => hchar k h2 h1, by decide, by decide⟩

/-- The residual term cannot be dropped: `Dy + rest = 0` is not a valid bound on
    `|D| = 3`, `|S| = 2`, `d = 1`, `A = 3`, where the diagonal challenges are exceptional. -/
theorem tooth_assembly_needs_rest :
    ∃ (D S : List Goldilocks) (d A : Nat), D.Nodup ∧ S.Nodup ∧ ¬ AffineMcaBound D S d A (0 + 0) :=
  ⟨IncidenceTests.dom, IncidenceTests.pool, 1, 3, by decide, by decide,
    IncidenceTests.field_independent_bound_fails_example⟩


#verify_constructive inhabited_assembly
#verify_inhabited cwyz26_affineMcaBound_of_nonExcluded inhabited_assembly
#verify_constructive inhabited_sliced
#verify_inhabited cwyz26_affineMcaBound_sliced inhabited_sliced
#verify_constructive tooth_assembly_needs_rest
#tooth_pair cwyz26_affineMcaBound_of_nonExcluded vs tooth_assembly_needs_rest

end GapTests


end Qsag

public section
namespace Qsag


/-! ## 6. Constructive Witness Inhabitedness & `#tooth_pair` Assurance Gates -/

theorem witness_dual_lpn_bias :
    ∃ weights : List Nat, weights.length = 64 ∧
      (∀ w ∈ weights, ((32768 : Int) - 2 * (w : Int)).natAbs ≤ 2047) ∧
      ExactRat.lt (ExactRat.abs (parityBias (regularBlockXorOneProb (weights.map depth15TreeRate)))) (ExactRat.twoNegPow 256) :=
  ⟨List.replicate 64 16384, by decide, fun _ hw => by rw [List.eq_of_mem_replicate hw]; decide,
   pcg_dense_dual_lpn_linear_bias_lt_two_neg_256 (List.replicate 64 16384) (by decide)
     (fun _ hw => by rw [List.eq_of_mem_replicate hw]; decide)⟩

theorem witness_depth15_isd :
    ∃ q l : Nat, q ≤ 32 ∧ sternDumerWorkExceedsPow2 pcgDepth15Cols pcgDenseRows pcgDenseWeightT q l 256 :=
  ⟨2, 52, by decide, (pcg_dense_depth15_prange_and_stern_dumer_pq128 2 52 (by decide)).1⟩


theorem witness_dual_lpn_11tap_bias_135 :
    ∃ weights : List Nat, weights.length = 64 ∧
      (∀ w ∈ weights, ((32768 : Int) - 2 * (w : Int)).natAbs ≤ 7593) ∧
      ExactRat.lt (ExactRat.abs (parityBias (regularBlockXorOneProb (weights.map depth15TreeRate))))
        (ExactRat.twoNegPow 135) :=
  ⟨List.replicate 64 12588, by decide, fun _ hw => by rw [List.eq_of_mem_replicate hw]; decide,
   pcg_dense_11tap_all_rows_bias_lt_two_neg_135 (List.replicate 64 12588) (by decide)
     (fun _ hw => by rw [List.eq_of_mem_replicate hw]; decide)⟩

#verify_constructive tooth_pcg_dense_depth14_stern_dumer_below_256
#tooth_pair Qsag.pcg_dense_depth15_prange_and_stern_dumer_pq128 vs Qsag.tooth_pcg_dense_depth14_stern_dumer_below_256
#verify_constructive tooth_omitting_accumulator_collapses_dual_lpn_bias
#tooth_pair Qsag.pcg_dense_dual_lpn_linear_bias_lt_two_neg_256 vs Qsag.tooth_omitting_accumulator_collapses_dual_lpn_bias
#verify_constructive tooth_omitting_accumulator_collapses_dual_lpn_bias_135
#tooth_pair Qsag.pcg_dense_11tap_all_rows_bias_lt_two_neg_135 vs Qsag.tooth_omitting_accumulator_collapses_dual_lpn_bias_135
#verify_constructive tooth_omitting_rejection_scaling_breaks_hvzk
#tooth_pair Qsag.acceptProbExact_safe_cancels_shift vs Qsag.tooth_omitting_rejection_scaling_breaks_hvzk
#verify_constructive tooth_tight_clipping_loses_boundary_preimage
#tooth_pair Qsag.rlwe_accept_box_preimage_in_proposal_box vs Qsag.tooth_tight_clipping_loses_boundary_preimage
#verify_constructive witness_accept_box_preimage
#verify_inhabited Qsag.rlwe_accept_box_preimage_in_proposal_box Qsag.witness_accept_box_preimage
#verify_constructive witness_acceptProb_cancellation
#verify_inhabited Qsag.acceptProbExact_safe_cancels_shift Qsag.witness_acceptProb_cancellation
#verify_constructive witness_dual_lpn_bias
#verify_inhabited Qsag.pcg_dense_dual_lpn_linear_bias_lt_two_neg_256 Qsag.witness_dual_lpn_bias
#verify_constructive witness_dual_lpn_11tap_bias_135
#verify_inhabited Qsag.pcg_dense_11tap_all_rows_bias_lt_two_neg_135 Qsag.witness_dual_lpn_11tap_bias_135
#verify_constructive witness_depth15_isd
#verify_inhabited Qsag.pcg_dense_depth15_prange_and_stern_dumer_pq128 Qsag.witness_depth15_isd

end Qsag
end

public section
namespace Qsag
open CommRingOps RoundPoly

/-! ## Assurance Witnesses -/

namespace PersistentPairsTests
open UPoly Poly3

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

def dom4 : List Goldilocks := [g 0, g 1, g 2, g 3]
def pool2 : List Goldilocks := [g 1, g 2]

/-! The evaluated facts of the two persistent-pair witnesses, each stated once. The witnesses cite them, so
    the inhabitedness audit re-checks an application of a proved lemma, not the evaluation inside it. -/
private theorem poleWords_dom4_far : ¬ HasCorrelatedAgreement 1 (4 - 1) poleWords.1 poleWords.2 dom4 :=
  poleWords_far dom4 1 4 (by decide) (by decide +kernel) (by decide) (by decide)

private theorem diag11_mem_pool2 : ∀ p ∈ [(g 1, g 1)], p ∈ prodPool pool2 := by
  poly_eval [g, dom4, pool2]

private theorem diag11_natDeg : (C (g 1) : UPoly Goldilocks).natDeg ≤ 1 := by decide +kernel

private theorem diag11_agree :
    4 ≤ (dom4.filter (foldAgreePt poleWords (g 1, g 1).1 (g 1, g 1).2 (C (g 1)))).length := by
  poly_eval [g, dom4, pool2]

private theorem diag11_persistent :
    IsPersistent poleWords dom4 1 3 (g 1, g 1).1 (g 1, g 1).2 (C (g 1)) :=
  ⟨one, ofList [one, one], by decide +kernel, by decide +kernel, by decide +kernel,
    by poly_eval [g, dom4, pool2]⟩

/-- Witness that `persistent_pairs_card_le` is inhabited on `Goldilocks` (`|D| = 4`, `d = 1`,
    `B = 3`, `A = 4`, where `4 * 2 = 8 < 9 = 3^2`, using `poleWords` which has no correlated
    agreement `≥ 3` while diagonal challenges `(β, β)` have rational explanation `H = 1, L = X + 1`). -/
theorem inhabited_persistent_pairs_card_le :
    ∃ (x : (Goldilocks → Goldilocks) × (Goldilocks → Goldilocks))
      (D S : List Goldilocks) (d A B : Nat) (L : List (Goldilocks × Goldilocks)),
      D.Nodup ∧ S.Nodup ∧ D.length * (d + 1) < B * B ∧
      ¬ HasCorrelatedAgreement d (A - 1) x.1 x.2 D ∧
      L.Nodup ∧ (∀ p ∈ L, p ∈ prodPool S) ∧ 1 ≤ L.length ∧
      (∀ p ∈ L, ∃ P : UPoly Goldilocks, P.natDeg ≤ d ∧
        A ≤ (D.filter (foldAgreePt x p.1 p.2 P)).length ∧
        IsPersistent x D d B p.1 p.2 P) := by
  refine ⟨poleWords, dom4, pool2, 1, 4, 3, [(g 1, g 1)],
    by decide, by decide, by decide, poleWords_dom4_far,
    by decide, diag11_mem_pool2, by decide, ?_⟩
  intro p hp
  rw [List.mem_singleton.mp hp]
  exact ⟨C (g 1), diag11_natDeg, diag11_agree, diag11_persistent⟩

/-- `#tooth`: dropping `¬ HasCorrelatedAgreement d (A - 1) f g D` invalidates Lemma 4.5:
    for `f = 0, g = 0` on `D = [0, 1, 2, 3]`, `S = [0, 1, 2]` (`|S| = 3`), `d = 1, B = 3, A = 4`,
    ALL `|S|² = 9` challenges admit `P = 0` (persistent via `H = 0, L = 1`), exceeding
    `ℓ · max(|S|, n(n-1)/2) = (4·1 / 1) · max(3, 6)` at `S = [0, 1, 2, 3, 4, 5, 6]` (`49 > 4 · 7 = 28`). -/
theorem tooth_persistent_needs_far :
    ∃ (x : (Goldilocks → Goldilocks) × (Goldilocks → Goldilocks))
      (D S : List Goldilocks) (d A B : Nat) (L : List (Goldilocks × Goldilocks)),
      D.Nodup ∧ S.Nodup ∧ D.length * (d + 1) < B * B ∧
      L.Nodup ∧ (∀ p ∈ L, p ∈ prodPool S) ∧
      (∀ p ∈ L, ∃ P : UPoly Goldilocks, P.natDeg ≤ d ∧
        A ≤ (D.filter (foldAgreePt x p.1 p.2 P)).length ∧
        IsPersistent x D d B p.1 p.2 P) ∧
      ¬ (L.length ≤ ((D.length * (B - (d + 1))) / (B * B - D.length * (d + 1))) *
          Nat.max S.length (D.length * (D.length - 1) / 2)) := by
  let S7 : List Goldilocks := [g 0, g 1, g 2, g 3, g 4, g 5, g 6]
  refine ⟨(fun _ => zero, fun _ => zero), dom4, S7, 1, 4, 3, prodPool S7,
    by decide, by decide, by decide, prodPool_nodup (by decide), fun _ h => h, ?_, by poly_eval [g, dom4, pool2]⟩
  intro p _
  have hz0 : ∀ z : Goldilocks, (zero : UPoly Goldilocks).eval z = zero := fun _ => rfl
  have hAgAll : dom4.filter (foldAgreePt (fun _ => zero, fun _ => zero) p.1 p.2 zero) = dom4 :=
    filter_eq_self_of_all _ dom4 (fun z _ => decide_eq_true (by
      show (zero : UPoly Goldilocks).eval z = add zero (mul (add p.1 (mul p.2 z)) zero)
      rw [hz0 z, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]))
  have hPersAll : dom4.filter (fun z =>
      decide ((one : UPoly Goldilocks).eval z ≠ zero) &&
      foldAgreePt (fun _ => zero, fun _ => zero) p.1 p.2 zero z &&
      decide ((zero : UPoly Goldilocks).eval z = mul zero ((one : UPoly Goldilocks).eval z))) = dom4 :=
    filter_eq_self_of_all _ dom4 (fun z _ => by
      simp only [Bool.and_eq_true]
      have h1 : (one : UPoly Goldilocks).eval z = one := by rw [one_eq_C, eval_C]
      refine ⟨⟨decide_eq_true (by rw [h1]; exact LawfulField.one_ne_zero), ?_⟩,
        decide_eq_true (by rw [hz0 z, LawfulCommRing.zero_mul])⟩
      exact decide_eq_true (by
        show (zero : UPoly Goldilocks).eval z = add zero (mul (add p.1 (mul p.2 z)) zero)
        rw [hz0 z, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]))
  refine ⟨zero, by decide +kernel, ?_, zero, one, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  · rw [hAgAll]; decide
  · rw [hPersAll]; decide

/-- The candidate-specific theorem has the same nonempty pole-word instance, including
an explicit selected polynomial for every counted challenge. -/
theorem inhabited_exceptional_persistent_pairs :
    ∃ (x : (Goldilocks → Goldilocks) × (Goldilocks → Goldilocks))
      (D S : List Goldilocks) (d A B : Nat) (L : List (Goldilocks × Goldilocks)),
      D.Nodup ∧ S.Nodup ∧ D.length * (d + 1) < B * B ∧
      L.Nodup ∧ (∀ p ∈ L, p ∈ prodPool S) ∧ 1 ≤ L.length ∧
      (∀ p ∈ L, ∃ P : UPoly Goldilocks, P.natDeg ≤ d ∧
        A ≤ (D.filter (foldAgreePt x p.1 p.2 P)).length ∧
        IsPersistent x D d B p.1 p.2 P ∧
        ¬ HasPolynomialExplanation x D d (A - 1) p.1 p.2 P) := by
  refine ⟨poleWords, dom4, pool2, 1, 4, 3, [(g 1, g 1)],
    by decide, by decide, by decide, by decide, diag11_mem_pool2, by decide, ?_⟩
  intro p hp
  rw [List.mem_singleton.mp hp]
  refine ⟨C (g 1), diag11_natDeg, diag11_agree, diag11_persistent, ?_⟩
  rintro ⟨Fp, Gp, hF, hG, hAgree, _⟩
  exact poleWords_dom4_far ⟨Fp, Gp, hF, hG, hAgree⟩

/-- Pool membership decided through `mem_prodPool_iff` (the body of `prodPool` is sealed here). The
    inhabitedness audits below bind `S := D` by first match and decide `∀ p ∈ L, p ∈ prodPool D`, as they
    did when the body was visible. -/
local instance (priority := high) prodPoolMemDecidable {α : Type} [DecidableEq α] (S : List α)
    (p : α × α) : Decidable (p ∈ prodPool S) :=
  decidable_of_iff (p.1 ∈ S ∧ p.2 ∈ S) mem_prodPool_iff.symm

#verify_constructive inhabited_exceptional_persistent_pairs
#verify_inhabited exceptional_persistent_pairs_card_le inhabited_exceptional_persistent_pairs
#tooth_pair exceptional_persistent_pairs_card_le vs tooth_persistent_needs_far
#verify_constructive nonpersistent_common_agree_le rat_pair_collinear_or_polys
#verify_constructive exceptional_persistent_challenges_per_witness_le exceptional_persistent_pairs_card_le
#verify_constructive persistent_challenges_per_witness_le persistent_pairs_card_le
#verify_constructive inhabited_persistent_pairs_card_le tooth_persistent_needs_far
#tooth_pair persistent_pairs_card_le vs tooth_persistent_needs_far
#verify_inhabited persistent_pairs_card_le inhabited_persistent_pairs_card_le

end PersistentPairsTests

end Qsag
end

public section
namespace Qsag
namespace SlicedJetTests

set_option autoImplicit false

open CommRingOps RoundPoly UPoly Poly3

local instance : NoZeroDivisors Goldilocks := LawfulField.toNoZeroDivisors Goldilocks

def two : Goldilocks := Goldilocks.ofNat 2
def three : Goldilocks := Goldilocks.ofNat 3

/-- `f = 0`, `g = (0, 0, 1, 1)` on `D = {0, 1, 2, 3}`. -/
def stepWords : (Goldilocks → Goldilocks) × (Goldilocks → Goldilocks) :=
  (fun _ => zero, fun z => if z = zero ∨ z = one then zero else one)
def zeroWords : (Goldilocks → Goldilocks) × (Goldilocks → Goldilocks) :=
  (fun _ => zero, fun _ => zero)
def dom : List Goldilocks := [zero, one, two, three]
def tenPts : List Goldilocks :=
  [zero, one, two, three, Goldilocks.ofNat 4, Goldilocks.ofNat 5, Goldilocks.ofNat 6,
    Goldilocks.ofNat 7, Goldilocks.ofNat 8, Goldilocks.ofNat 9]

/-- The surface `Z = 0`. -/
def zSurface : Poly3 Goldilocks := X

private theorem three_of_four (p : Goldilocks → Bool) (h : 3 ≤ (dom.filter p).length) :
    (p zero = true ∧ p one = true ∧ (p two = true ∨ p three = true)) ∨
    (p two = true ∧ p three = true ∧ (p zero = true ∨ p one = true)) := by
  unfold dom at h
  cases h0 : p zero <;> cases h1 : p one <;> cases h2 : p two <;> cases h3 : p three <;>
    first
    | exact .inl ⟨rfl, rfl, .inl rfl⟩
    | exact .inl ⟨rfl, rfl, .inr rfl⟩
    | exact .inr ⟨rfl, rfl, .inl rfl⟩
    | exact .inr ⟨rfl, rfl, .inr rfl⟩
    | (exfalso
       simp only [List.filter, h0, h1, h2, h3, List.length_cons, List.length_nil] at h
       exact absurd h (by decide))

private theorem natDeg_sub_le_max {R : Type} [LawfulCommRing R] [DecidableEq R]
    (p q : UPoly R) (B : Nat) (hp : p.natDeg ≤ B) (hq : q.natDeg ≤ B) :
    (sub p q).natDeg ≤ B := by
  rw [LawfulCommRing.sub_eq_add_neg]
  have h1 := (degFn_natDeg (R := R)).add_le p (neg q)
  have h2 := (degFn_natDeg (R := R)).neg_le q
  omega

private theorem eval_sub_eq {R : Type} [LawfulCommRing R] [DecidableEq R]
    (p q : UPoly R) (z : R) : (sub p q).eval z = sub (p.eval z) (q.eval z) := by
  simpa only [evalHom_apply] using RingHom.map_sub (evalHom z) p q

private theorem eq_zero_of_two_roots (H : UPoly Goldilocks) (hd : H.natDeg ≤ 1)
    (a b : Goldilocks) (hab : a ≠ b) (ha : H.eval a = zero) (hb : H.eval b = zero) :
    H = zero := by
  apply Decidable.byContradiction
  intro hne
  have hr := UPoly.roots_length_le_natDeg H hne [a, b]
    (List.pairwise_cons.mpr ⟨(fun c hc => by rw [List.mem_singleton.mp hc]; exact hab),
      List.pairwise_cons.mpr ⟨(fun _ hc => absurd hc List.not_mem_nil), List.Pairwise.nil⟩⟩)
    (fun z hz => by
      rcases List.mem_cons.mp hz with e | hz'
      · rw [e]; exact ha
      · rw [List.mem_singleton.mp hz']; exact hb)
  exact absurd (Nat.le_trans hr hd) (Nat.not_succ_le_self 1)

/-- The candidate `(α, β, P) = (0, 0, 0)` agrees with the fold of `stepWords` everywhere and
    has no rational explanation `H / L` on three coordinates. -/
theorem stepWords_nonpersistent :
    ¬ IsPersistent stepWords dom 1 3 zero zero (zero : UPoly Goldilocks) := by
  rintro ⟨H, L, _, hLd, hHd, hsize⟩
  have hmem : ∀ z : Goldilocks, (decide (L.eval z ≠ zero) &&
      foldAgreePt stepWords zero zero zero z &&
      decide (H.eval z = mul (stepWords.2 z) (L.eval z))) = true →
      L.eval z ≠ zero ∧ H.eval z = mul (stepWords.2 z) (L.eval z) := fun z hz => by
    obtain ⟨hl, hh⟩ := Bool.and_eq_true_iff.mp hz
    exact ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp hl).1, of_decide_eq_true hh⟩
  have hlow : ∀ z : Goldilocks, stepWords.2 z = zero → (decide (L.eval z ≠ zero) &&
      foldAgreePt stepWords zero zero zero z &&
      decide (H.eval z = mul (stepWords.2 z) (L.eval z))) = true →
      L.eval z ≠ zero ∧ H.eval z = zero := fun z hg hz => by
    obtain ⟨h1, h2⟩ := hmem z hz
    rw [hg, LawfulCommRing.zero_mul] at h2
    exact ⟨h1, h2⟩
  have hhigh : ∀ z : Goldilocks, stepWords.2 z = one → (decide (L.eval z ≠ zero) &&
      foldAgreePt stepWords zero zero zero z &&
      decide (H.eval z = mul (stepWords.2 z) (L.eval z))) = true →
      L.eval z ≠ zero ∧ H.eval z = L.eval z := fun z hg hz => by
    obtain ⟨h1, h2⟩ := hmem z hz
    rw [hg, LawfulCommRing.one_mul] at h2
    exact ⟨h1, h2⟩
  have g0 : stepWords.2 zero = zero := by decide +kernel
  have g1 : stepWords.2 one = zero := by decide +kernel
  have g2 : stepWords.2 two = one := by decide +kernel
  have g3 : stepWords.2 three = one := by decide +kernel
  rcases three_of_four _ hsize with ⟨h0, h1, h23⟩ | ⟨h2, h3, h01⟩
  · have hH : H = zero := eq_zero_of_two_roots H hHd zero one (by decide +kernel)
      (hlow zero g0 h0).2 (hlow one g1 h1).2
    have hcontra : ∀ w : Goldilocks, L.eval w ≠ zero ∧ H.eval w = L.eval w → False :=
      fun w hw => hw.1 (by rw [← hw.2, hH]; rfl)
    rcases h23 with h | h
    · exact hcontra two (hhigh two g2 h)
    · exact hcontra three (hhigh three g3 h)
  · have hsub : sub H L = zero := eq_zero_of_two_roots (sub H L)
      (natDeg_sub_le_max H L 1 hHd hLd) two three (by decide +kernel)
      (by rw [eval_sub_eq, (hhigh two g2 h2).2, LawfulCommRing.sub_self])
      (by rw [eval_sub_eq, (hhigh three g3 h3).2, LawfulCommRing.sub_self])
    have hHL : H = L := LawfulCommRing.sub_eq_zero_iff.mp hsub
    have hcontra : ∀ u : Goldilocks, L.eval u ≠ zero ∧ H.eval u = zero → False :=
      fun u hu => hu.1 (by rw [← hHL]; exact hu.2)
    rcases h01 with h | h
    · exact hcontra zero (hlow zero g0 h)
    · exact hcontra one (hlow one g1 h)

/-- No pair `(F, G)` with `G` constant agrees with `stepWords` on three coordinates. -/
theorem stepWords_unexplained :
    ¬ HasPolynomialExplanation stepWords dom 1 (4 - 1) zero zero (zero : UPoly Goldilocks) := by
  rintro ⟨Fp, Gp, _, hG, hAg, _⟩
  have hdomNd : dom.Nodup := by decide +kernel
  obtain ⟨c, hc⟩ : ∃ c : Goldilocks, ∀ z, evalCoeffs Gp z = c := by
    match Gp, hG with
    | [], _ => exact ⟨zero, fun _ => rfl⟩
    | [c], _ =>
      exact ⟨c, fun z => by
        show add c (mul z zero) = c
        rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]⟩
    | _ :: _ :: _, h => exact absurd (Nat.le_of_succ_le_succ h) (Nat.not_succ_le_zero _)
  have hb : (dom.filter (fun z => decide (evalCoeffs Fp z = stepWords.1 z) &&
      decide (evalCoeffs Gp z = stepWords.2 z))).length ≤
      (dom.filter (fun z => decide (stepWords.2 z = c))).length :=
    nodup_length_le_of_subset (nodup_filter _ dom hdomNd) (fun z hz => by
      obtain ⟨hzD, hpair⟩ := List.mem_filter.mp hz
      have he : evalCoeffs Gp z = stepWords.2 z :=
        of_decide_eq_true (Bool.and_eq_true_iff.mp hpair).2
      exact List.mem_filter.mpr ⟨hzD, decide_eq_true (he.symm.trans (hc z))⟩)
  have h2 : (dom.filter (fun z => decide (stepWords.2 z = c))).length ≤ 2 := by
    if h0 : c = zero then
      rw [h0]; decide +kernel
    else
      have hs : (dom.filter (fun z => decide (stepWords.2 z = c))).length ≤
          (dom.filter (fun z => decide (stepWords.2 z ≠ zero))).length :=
        nodup_length_le_of_subset (nodup_filter _ dom hdomNd) (fun z hz => by
          obtain ⟨hzD, he⟩ := List.mem_filter.mp hz
          have he' : stepWords.2 z = c := of_decide_eq_true he
          exact List.mem_filter.mpr ⟨hzD, decide_eq_true (fun e => h0 (he'.symm.trans e))⟩)
      have hn : (dom.filter (fun z => decide (stepWords.2 z ≠ zero))).length = 2 := by
        decide +kernel
      rw [hn] at hs
      exact hs
  exact absurd (Nat.le_trans hAg (Nat.le_trans hb h2)) (by decide)

/-- The hypotheses of `slice_card_le` hold on a nonempty slice. -/
theorem inhabited_slice :
    ∃ (x : (Goldilocks → Goldilocks) × (Goldilocks → Goldilocks)) (D : List Goldilocks)
      (d A B h : Nat) (R : Poly3 Goldilocks) (β : Goldilocks) (as : List Goldilocks),
      D.Nodup ∧ 1 ≤ d ∧ 1 ≤ h ∧ B < A ∧ d + 1 ≤ B ∧ R.degYZ ≤ h ∧ R.degZ ≤ 1 ∧
      (∀ a ∈ as, ∃ P : UPoly Goldilocks, P.natDeg ≤ d ∧
        A ≤ (D.filter (foldAgreePt x a β P)).length ∧ evalAffineLine R a β P = zero ∧
        evalAffineLine (hasseZ 1 R) a β P ≠ zero ∧ ¬ IsPersistent x D d B a β P) ∧
      as.Nodup ∧ as.length = 1 := by
  refine ⟨stepWords, dom, 1, 4, 3, 1, zSurface, zero, [zero], by decide +kernel, by decide,
    by decide, by decide, by decide, by poly_eval [two, three, stepWords, zeroWords, dom, tenPts, zSurface], by poly_eval [two, three, stepWords, zeroWords, dom, tenPts, zSurface], ?_,
    by decide +kernel, rfl⟩
  intro a ha
  rw [List.mem_singleton.mp ha]
  exact ⟨zero, by decide +kernel, by decide +kernel, by poly_eval [two, three, stepWords, zeroWords, dom, tenPts, zSurface], by poly_eval [two, three, stepWords, zeroWords, dom, tenPts, zSurface],
    stepWords_nonpersistent⟩

/-- Without nonpersistence the slice bound fails: all ten intercepts are accepted for the
    zero words, against a bound of `9`. -/
theorem tooth_slice_needs_nonpersistent :
    ∃ (x : (Goldilocks → Goldilocks) × (Goldilocks → Goldilocks)) (D : List Goldilocks)
      (d A B h : Nat) (R : Poly3 Goldilocks) (β : Goldilocks) (as : List Goldilocks),
      D.Nodup ∧ 1 ≤ d ∧ 1 ≤ h ∧ B < A ∧ d + 1 ≤ B ∧ R.degYZ ≤ h ∧ R.degZ ≤ 1 ∧
      (∀ a ∈ as, ∃ P : UPoly Goldilocks, P.natDeg ≤ d ∧
        A ≤ (D.filter (foldAgreePt x a β P)).length ∧ evalAffineLine R a β P = zero ∧
        evalAffineLine (hasseZ 1 R) a β P ≠ zero) ∧
      as.Nodup ∧ ¬ as.length ≤ h * (D.length * (1 * (2 * d * h)) / (A - B) + 1) := by
  have key : ∀ a ∈ tenPts, (zero : UPoly Goldilocks).natDeg ≤ 1 ∧
      4 ≤ (dom.filter (foldAgreePt zeroWords a zero zero)).length ∧
      evalAffineLine zSurface a zero zero = zero ∧
      evalAffineLine (hasseZ 1 zSurface) a zero zero ≠ zero := by poly_eval [two, three, stepWords, zeroWords, dom, tenPts, zSurface]
  exact ⟨zeroWords, dom, 1, 4, 3, 1, zSurface, zero, tenPts, by decide +kernel, by decide,
    by decide, by decide, by decide, by poly_eval [two, three, stepWords, zeroWords, dom, tenPts, zSurface], by poly_eval [two, three, stepWords, zeroWords, dom, tenPts, zSurface],
    fun a ha => ⟨zero, key a ha⟩, by decide +kernel, by decide⟩

/-- The hypotheses of `nonExcluded_pairs_card_le` hold together with a counted challenge. -/
theorem inhabited_nonExcluded_pairs :
    ∃ (x : (Goldilocks → Goldilocks) × (Goldilocks → Goldilocks)) (D S : List Goldilocks)
      (d A B h : Nat) (Q : Poly3 Goldilocks) (L : List (Goldilocks × Goldilocks)),
      D.Nodup ∧ S.Nodup ∧ 1 ≤ d ∧ 1 ≤ h ∧ B < A ∧ d + 1 ≤ B ∧
      D.length * (d + 1) < B * B ∧ Q.degYZ ≤ h ∧ Q.deg11d d ≤ 1 ∧
      (∀ k, 1 ≤ k → k ≤ Q.degZ → (CRing.natCast k : Goldilocks) ≠ zero) ∧ L.Nodup ∧
      (∀ p ∈ L, p ∈ prodPool S ∧ lineSpec Q p.1 p.2 ≠ zero ∧
        ∃ P : UPoly Goldilocks, P.natDeg ≤ d ∧
          A ≤ (D.filter (foldAgreePt x p.1 p.2 P)).length ∧
          evalAffineLine Q p.1 p.2 P = zero ∧
          ¬ HasPolynomialExplanation x D d (A - 1) p.1 p.2 P) ∧
      L.length = 1 := by
  have hdz : zSurface.degZ = 1 := by poly_eval [two, three, stepWords, zeroWords, dom, tenPts, zSurface]
  refine ⟨stepWords, dom, dom, 1, 4, 3, 1, zSurface, [(zero, zero)], by decide +kernel,
    by decide +kernel, by decide, by decide, by decide, by decide, by decide +kernel,
    by poly_eval [two, three, stepWords, zeroWords, dom, tenPts, zSurface], by poly_eval [two, three, stepWords, zeroWords, dom, tenPts, zSurface], ?_, by decide +kernel, ?_, rfl⟩
  · intro k h1 h2
    rw [hdz] at h2
    rw [Nat.le_antisymm h2 h1]
    exact LawfulField.one_ne_zero
  · intro p hp
    rw [List.mem_singleton.mp hp]
    exact ⟨by poly_eval [two, three, stepWords, zeroWords, dom, tenPts, zSurface], by poly_eval [two, three, stepWords, zeroWords, dom, tenPts, zSurface], zero, by decide +kernel, by decide +kernel,
      by poly_eval [two, three, stepWords, zeroWords, dom, tenPts, zSurface], stepWords_unexplained⟩

#verify_constructive Poly3.jetEq_pt Poly3.deg_jetEq_le Poly3.primY_liftK_eval
#verify_constructive Poly3.slice_card_le Poly3.nonExcluded_pairs_card_le
#verify_constructive SlicedJet.cover_count SlicedJet.leaf_bound_arith
#verify_constructive stepWords_nonpersistent stepWords_unexplained
#verify_constructive inhabited_slice tooth_slice_needs_nonpersistent inhabited_nonExcluded_pairs
#verify_inhabited Poly3.slice_card_le inhabited_slice
#tooth_pair Poly3.slice_card_le vs tooth_slice_needs_nonpersistent
#verify_inhabited Poly3.nonExcluded_pairs_card_le inhabited_nonExcluded_pairs

end SlicedJetTests
end Qsag
end

public section
namespace Qsag
open CommRingOps RoundPoly UPoly
namespace ShearedCurveGcdTests
open UPoly Poly2 SylElim

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

private theorem isPrimY_monic_deg1_loc (p : UPoly Goldilocks) :
    IsPrimY (ofList [p, one] : Poly2 Goldilocks) := by
  refine ⟨by
    intro h0
    have hc := congrArg (fun q : Poly2 Goldilocks => coeffAt q.coeffs 1) h0
    rw [coeffAt_ofList, coeffAt_cons_succ, coeffAt_cons_zero, coeffs_zero, coeffAt_nil] at hc
    exact NontrivialRing.one_ne_zero hc, fun f hf => ?_⟩
  obtain ⟨q, hq⟩ := hf 1
  rw [coeffAt_ofList, coeffAt_cons_succ, coeffAt_cons_zero] at hq
  have hf0 : f ≠ zero := fun e => NontrivialRing.one_ne_zero (by rw [hq, e, LawfulCommRing.zero_mul])
  have hq0 : q ≠ zero := fun e => NontrivialRing.one_ne_zero (by rw [hq, e, LawfulCommRing.mul_zero])
  have hd := UPoly.natDeg_mul hf0 hq0
  rw [← hq, natDeg_one] at hd; omega

/-- `E = W - U` (`ofList [neg X, one]`) is `U`-primitive with `tdeg E = 1` and `1 ≤ E.natDeg`. -/
theorem inhabited_primY_natDeg_pos :
    ∃ E : Poly2 Goldilocks, IsPrimY E ∧ 1 ≤ tdeg E ∧ 1 ≤ E.natDeg :=
  let E : Poly2 Goldilocks := ofList [neg X, one]
  ⟨E, isPrimY_monic_deg1_loc (neg X), by poly_eval [E, g],
    primY_natDeg_pos (isPrimY_monic_deg1_loc (neg X)) (by poly_eval [E, g])⟩

/-- `#tooth`: dropping `IsPrimY E` invalidates `primY_natDeg_pos`: `E = C X` (`U · 1`) has
    `tdeg E = 1 ≥ 1` yet `E.natDeg = 0`! -/
theorem tooth_natDeg_pos_needs_primY :
    ∃ E : Poly2 Goldilocks, E ≠ zero ∧ 1 ≤ tdeg E ∧ ¬ (1 ≤ E.natDeg) :=
  ⟨C X, by decide +kernel, by poly_eval [g], by decide +kernel⟩

/-- The curve `W = 0` divides `Res_Z(Z, W) = W`, while its derivative resultant is `1`.
This exercises the common-root branch with a nonzero resultant and a nonempty curve. -/
theorem inhabited_curve_leaf_root_decomp :
    ∃ (C₁ E : Poly2 Goldilocks) (P₀ : UPoly (Poly2 Goldilocks)),
      C₁.natDeg ≤ 1 ∧ coeffAt C₁.coeffs 1 = one ∧ P₀.natDeg ≤ 0 ∧
      IsPrimY E ∧ 1 ≤ tdeg E ∧
      (∃ Q_res, sylRes 1 0 (embedUZ.toFun C₁) P₀ = mul E Q_res) ∧
      sylRes 1 0 (embedUZ.toFun C₁) P₀ ≠ zero ∧
      sylResDeriv 1 0 (embedUZ.toFun C₁) P₀ one = one := by
  refine ⟨X, X, C X, by decide +kernel, by decide +kernel, by decide +kernel,
    isPrimY_monic_deg1_loc zero, by poly_eval [g], ⟨one, by poly_eval [g]⟩,
    by poly_eval [g], by poly_eval [g]⟩

/-- Applying the decomposition to `Res_Z(Z,W)` produces an actual common-root leaf. -/
theorem inhabited_curve_common_root :
    ∃ (E : Poly2 Goldilocks) (hP : IsPrimY E) (hD : 1 ≤ E.natDeg)
      (ζ : ModMonic (monicFY E hP hD)),
      ((mapHom (modPoly2Hom E hP hD)).toFun (embedUZ.toFun (X : Poly2 Goldilocks))).eval ζ = zero ∧
      ((mapHom (modPoly2Hom E hP hD)).toFun (C (X : Poly2 Goldilocks))).eval ζ = zero := by
  obtain ⟨Es, _, hCover, hLeaves⟩ :=
    curve_leaf_root_decomp (h_C := 1) (H₀ := 0) (C₁ := (X : Poly2 Goldilocks))
      (P₀ := C X) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      X (isPrimY_monic_deg1_loc zero) (by poly_eval [g]) ⟨one, by poly_eval [g]⟩
  obtain ⟨E, hMem, _⟩ := hCover zero zero (by decide +kernel)
  obtain ⟨hP, hD, hDiv | hRoot⟩ := hLeaves E hMem
  · obtain ⟨Q, hQ⟩ := hDiv
    have hDeriv : sylResDeriv 1 0 (embedUZ.toFun (X : Poly2 Goldilocks)) (C X) one = one :=
      by poly_eval [g]
    rw [hDeriv] at hQ
    have hQne : Q ≠ zero := fun e => NontrivialRing.one_ne_zero (by rw [hQ, e, LawfulCommRing.mul_zero])
    have hDegree := UPoly.natDeg_mul hP.1 hQne
    rw [← hQ, natDeg_one] at hDegree
    exfalso
    omega
  · obtain ⟨ζ, hC, hP₀⟩ := hRoot.2
    exact ⟨E, hP, hD, ζ, hC, hP₀⟩

/-- Without resultant divisibility, `C₁=Z`, `P₀=1`, and the curve `W=0` cannot
have the asserted decomposition: neither a derivative-divisor leaf nor a common root exists. -/
theorem tooth_curve_leaf_root_decomp_needs_divisibility :
    ∃ (C₁ E : Poly2 Goldilocks) (P₀ : UPoly (Poly2 Goldilocks)),
      C₁.natDeg ≤ 1 ∧ coeffAt C₁.coeffs 1 = one ∧ P₀.natDeg ≤ 0 ∧
      IsPrimY E ∧ 1 ≤ tdeg E ∧
      ¬ ∃ Es : List (Poly2 Goldilocks),
        (Es.map tdeg).sum = tdeg E ∧
        (∀ u w, E.eval2 u w = zero → ∃ Ej ∈ Es, Ej.eval2 u w = zero) ∧
        ∀ Ej ∈ Es, ∃ (hPj : IsPrimY Ej) (hDj : 1 ≤ Ej.natDeg),
          (∃ Qg, sylResDeriv 1 0 (embedUZ.toFun C₁) P₀ one = mul Ej Qg) ∨
          (CoprimeZ Ej (sylResDeriv 1 0 (embedUZ.toFun C₁) P₀ one) ∧
            ∃ ζ : ModMonic (monicFY Ej hPj hDj),
              ((mapHom (modPoly2Hom Ej hPj hDj)).toFun (embedUZ.toFun C₁)).eval ζ = zero ∧
              ((mapHom (modPoly2Hom Ej hPj hDj)).toFun P₀).eval ζ = zero) := by
  refine ⟨X, X, one, by decide +kernel, by decide +kernel, by decide +kernel,
    isPrimY_monic_deg1_loc zero, by poly_eval [g], ?_⟩
  rintro ⟨Es, _, hCover, hLeaves⟩
  obtain ⟨E, hMem, _⟩ := hCover zero zero (by decide +kernel)
  obtain ⟨hP, hD, hDiv | hRoot⟩ := hLeaves E hMem
  · obtain ⟨Q, hQ⟩ := hDiv
    have hDeriv : sylResDeriv 1 0 (embedUZ.toFun (X : Poly2 Goldilocks)) one one = one :=
      by poly_eval [g]
    rw [hDeriv] at hQ
    have hQne : Q ≠ zero := fun e => NontrivialRing.one_ne_zero (by rw [hQ, e, LawfulCommRing.mul_zero])
    have hDegree := UPoly.natDeg_mul hP.1 hQne
    rw [← hQ, natDeg_one] at hDegree
    omega
  · obtain ⟨ζ, _, hP₀⟩ := hRoot.2
    rw [RingHom.map_one, one_eq_C, eval_C] at hP₀
    exact NontrivialRing.one_ne_zero hP₀

#verify_constructive SylElim.modPoly2Hom_eq_zero_iff SylElim.modPoly2Hom_unit_of_coprimeZ SylElim.curve_pullback_dvd_iff
#verify_constructive SylElim.primY_natDeg_pos SylElim.modUnitOrSplit SylElim.d5_xgcd_mod SylElim.curve_leaf_root_decomp
#verify_constructive inhabited_primY_natDeg_pos tooth_natDeg_pos_needs_primY
#tooth_pair SylElim.primY_natDeg_pos vs tooth_natDeg_pos_needs_primY
#verify_inhabited SylElim.primY_natDeg_pos inhabited_primY_natDeg_pos
#verify_constructive inhabited_curve_leaf_root_decomp inhabited_curve_common_root
#verify_inhabited SylElim.curve_leaf_root_decomp inhabited_curve_leaf_root_decomp
#verify_constructive tooth_curve_leaf_root_decomp_needs_divisibility
#tooth_pair SylElim.curve_leaf_root_decomp vs tooth_curve_leaf_root_decomp_needs_divisibility

end ShearedCurveGcdTests

end Qsag
end

public section
namespace Qsag
open CommRingOps RoundPoly UPoly
namespace ModMonicAlgebraTests
open UPoly SylElim

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

/-- Double common factor `G = X² - 1` (`d_G = 2`) dividing `C1 = G` and `P0 = G`:
    `sylResDeriv 2 2 G G 1 = 0`. -/
theorem inhabited_sylResDeriv_eq_zero_of_common_factor_ge_two :
    ∃ (m N d_G : Nat) (C1 P0 G Q_C Q_P : UPoly Goldilocks),
      2 ≤ d_G ∧ d_G ≤ m ∧ C1.natDeg ≤ m ∧ P0.natDeg ≤ N ∧
      G.natDeg ≤ d_G ∧ coeffAt G.coeffs d_G = one ∧
      C1 = mul G Q_C ∧ Q_C.natDeg ≤ m - d_G ∧ P0 = mul G Q_P ∧
      sylResDeriv m N C1 P0 one = zero :=
  let G : UPoly Goldilocks := ofList [neg (g 1), g 0, g 1]
  ⟨2, 2, 2, mul G one, mul G one, G, one, one,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, rfl, by decide +kernel, rfl, by poly_eval [G, g]⟩

/-- `#tooth`: dropping `2 ≤ d_G` (`d_G = 1`, simple common factor `G = X - 3` of `C1 = (X - 3)(X - 5)`
    and `P0 = X - 3`) makes `sylResDeriv 2 1 C1 P0 1 = -2 ≠ 0`! -/
theorem tooth_sylResDeriv_nonzero_for_deg_one_gcd :
    ∃ (m N d_G : Nat) (C1 P0 G Q_C Q_P : UPoly Goldilocks),
      1 ≤ d_G ∧ d_G ≤ m ∧ C1.natDeg ≤ m ∧ P0.natDeg ≤ N ∧
      G.natDeg ≤ d_G ∧ coeffAt G.coeffs d_G = one ∧
      C1 = mul G Q_C ∧ Q_C.natDeg ≤ m - d_G ∧ P0 = mul G Q_P ∧
      sylResDeriv m N C1 P0 one ≠ zero :=
  let G : UPoly Goldilocks := ofList [neg (g 3), g 1]
  let QC : UPoly Goldilocks := ofList [neg (g 5), g 1]
  ⟨2, 1, 1, mul G QC, mul G one, G, QC, one,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, rfl, by decide +kernel, rfl, by poly_eval [G, QC, g]⟩

/-- A simple common root has nonzero derivative resultant and is uniquely recovered. -/
theorem inhabited_common_root_unique :
    ∃ (m N : Nat) (C1 P0 : UPoly Goldilocks) (z z' : Goldilocks),
      1 ≤ m ∧ 1 ≤ N ∧ C1.natDeg ≤ m ∧ P0.natDeg ≤ N ∧
      C1.eval z = zero ∧ P0.eval z = zero ∧ C1.eval z' = zero ∧ P0.eval z' = zero ∧
      sylResDeriv m N C1 P0 one ≠ zero ∧ z = z' := by
  refine ⟨1, 1, ofList [neg (g 1), g 1], ofList [neg (g 1), g 1], g 1, g 1,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by poly_eval [g], rfl⟩

/-- Without the derivative condition, even a squarefree first polynomial has two common roots. -/
theorem tooth_common_root_unique_needs_derivative :
    ∃ (m N : Nat) (C1 P0 : UPoly Goldilocks) (z z' : Goldilocks),
      1 ≤ m ∧ 1 ≤ N ∧ C1.natDeg ≤ m ∧ P0.natDeg ≤ N ∧
      C1.eval z = zero ∧ P0.eval z = zero ∧ C1.eval z' = zero ∧ P0.eval z' = zero ∧
      z ≠ z' := by
  refine ⟨2, 1, ofList [neg (g 1), g 0, g 1], zero, g 1, neg (g 1),
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

#verify_constructive inhabited_common_root_unique tooth_common_root_unique_needs_derivative
#verify_inhabited SylElim.common_root_unique_of_sylResDeriv_ne_zero inhabited_common_root_unique
#tooth_pair SylElim.common_root_unique_of_sylResDeriv_ne_zero vs tooth_common_root_unique_needs_derivative

#verify_constructive SylElim.homEvalCoeffs_mul SylElim.map_homEvalCoeffs SylElim.homEvalCoeffs_map_root SylElim.homEvalCoeffs_map_zero_iff SylElim.degFn_homEvalCoeffs_le
#verify_constructive SylElim.degFn_homEvalCoeffs_poly_le
#verify_constructive SylElim.sylResDeriv_X_common_root SylElim.sylResDeriv_X_mapped_common_root SylElim.homEvalCoeffs_resultant_root
#verify_constructive SylElim.common_root_unique_of_sylResDeriv_ne_zero
#verify_constructive SylElim.wdeg_divModLead_rem_le SylElim.ModMonic.eval_modGen_eq_zero
#verify_constructive SylElim.sylResDeriv_eq_zero_of_common_factor_ge_two
#verify_constructive inhabited_sylResDeriv_eq_zero_of_common_factor_ge_two tooth_sylResDeriv_nonzero_for_deg_one_gcd
#tooth_pair SylElim.sylResDeriv_eq_zero_of_common_factor_ge_two vs tooth_sylResDeriv_nonzero_for_deg_one_gcd
#verify_inhabited SylElim.sylResDeriv_eq_zero_of_common_factor_ge_two inhabited_sylResDeriv_eq_zero_of_common_factor_ge_two

end ModMonicAlgebraTests

end Qsag
end

public section
namespace Qsag
open CommRingOps RoundPoly UPoly


end Qsag
end

public section
namespace Qsag
open CommRingOps RoundPoly UPoly
namespace BivariateFactorSplitTests
open UPoly Poly2

/-- Witness that `coprimeZ_const_of_vCoeff` is inhabited: `p(Z) = Z` and `A(V, Z) = V + Z`
    have `vCoeff A 1 = 1`, certifying `CoprimeZ (mapHom CHom X) (C X + X)`. -/
theorem inhabited_coprimeZ_const_of_vCoeff :
    ∃ (p : UPoly Goldilocks) (A : Poly2 Goldilocks) (k₀ : Nat) (u0 v0 : UPoly Goldilocks),
      1 ≤ p.natDeg ∧
      add (mul u0 p) (mul v0 (vCoeff A k₀)) = one ∧
      CoprimeZ ((UPoly.mapHom CHom).toFun p) A := by
  let p : UPoly Goldilocks := X
  let A : Poly2 Goldilocks := add (C X) X
  have hp : 1 ≤ p.natDeg := by decide +kernel
  have hv1 : vCoeff A 1 = one := by poly_eval [A]
  have hbez : add (mul zero p) (mul one (vCoeff A 1)) = one := by
    rw [hv1, LawfulCommRing.zero_mul, LawfulCommRing.zero_add, LawfulCommRing.mul_one]
  exact ⟨p, A, 1, zero, one, hp, hbez, coprimeZ_const_of_vCoeff p A hp 1 zero one hbez⟩

/-- `#tooth`: without a coprime `V`-coefficient, `coprimeZ_const_of_vCoeff`'s conclusion fails:
    for `p(Z) = Z` and `A(V, Z) = V · Z` (`vCoeff A 1 = Z`, sharing root `0` with `p`),
    `CoprimeZ (mapHom CHom p) A` is false because `(0, 0)` is a common zero at `c(0) = 0`?
    Even stronger: in `RatFunc Goldilocks[Z]`, `Z` divides both `Z` and `V · Z`! -/
theorem tooth_coprimeZ_needs_coprime_vCoeff :
    ∃ (p : UPoly Goldilocks) (A : Poly2 Goldilocks),
      1 ≤ p.natDeg ∧ vCoeff A 1 ≠ zero ∧ ¬ CoprimeZ ((UPoly.mapHom CHom).toFun p) A := by
  let p : UPoly Goldilocks := X
  let A : Poly2 Goldilocks := mul (C X) X
  refine ⟨p, A, by decide +kernel, by poly_eval [A], ?_⟩
  rintro ⟨U, V, c, hc, hbez⟩
  have hPZ : (UPoly.mapHom CHom).toFun p = (X : Poly2 Goldilocks) := by poly_eval [p]
  rw [hPZ] at hbez
  have h0 := congrArg (fun Q : Poly2 Goldilocks => coeffAt Q.coeffs 0) hbez
  have hUX : coeffAt (mul U X).coeffs 0 = zero := by
    rw [LawfulCommRing.mul_comm, coeffAt_X_mul_zero]
  have hVA : coeffAt (mul V A).coeffs 0 = zero := by
    dsimp [A]
    have : mul V (mul (C X) X) = mul X (mul V (C X)) := by constructive_ring
    rw [this, coeffAt_X_mul_zero]
  rw [coeffAt_add, hUX, hVA, LawfulCommRing.add_zero, coeffAt_C_zero] at h0
  exact hc h0.symm

#verify_constructive Poly2.primY_dvd_of_dvd_FY Poly2.d5_split_prim
#verify_constructive Poly2.splitAgainstList Poly2.coprimeZ_const_of_vCoeff
#verify_constructive inhabited_coprimeZ_const_of_vCoeff tooth_coprimeZ_needs_coprime_vCoeff
#tooth_pair Poly2.coprimeZ_const_of_vCoeff vs tooth_coprimeZ_needs_coprime_vCoeff
#verify_inhabited Poly2.coprimeZ_const_of_vCoeff inhabited_coprimeZ_const_of_vCoeff

end BivariateFactorSplitTests


end Qsag
end

public section
namespace Qsag
open CommRingOps RoundPoly UPoly
namespace Poly2.Tests
open Poly2

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

/-- `A = Z² - Y` and `B = Z - 1`, meeting only at `(1, 1)`. -/
def pA : Poly2 Goldilocks := ofList [ofList [g 0, neg (g 1)], zero, one]
def pB : Poly2 Goldilocks := ofList [ofList [neg (g 1)], one]

/-- `Z - Y`, which shares the whole diagonal with itself. -/
def pDiag : Poly2 Goldilocks := ofList [ofList [g 0, neg (g 1)], one]

/-! The eliminant of `pA`, `pB` executed in stages, each over the exported equations of its owner: the
    degree budget (`Coding/Resultant`), the constraint matrix of the four generators `A, B, Y·B, Z·B`
    (`Coding/Resultant`), the Gaussian solve of that matrix (`Math/CoeffPoly`). -/
private theorem parabolaLine_degrees :
    pA.natDeg = 2 ∧ pB.natDeg = 1 ∧ tdeg pA = 2 ∧ tdeg pB = 1 ∧ elimDeg pA pB = 2 := by
  poly_eval [g, pA, pB]

private theorem parabolaLine_gens_length : (elimGens pA pB 2 2 1 2 1).length = 4 := by
  poly_eval [g, pA, pB]

private theorem parabolaLine_rows :
    (elimCons 2 2).map (fun p => (elimGens pA pB 2 2 1 2 1).map (fun q => coeff2 q p.1 p.2)) =
      [[g 0, g 1, g 0, neg (g 1)], [g 0, g 0, g 1, g 0], [g 1, g 0, g 0, g 1]] := by
  poly_eval [g, pA, pB, (by decide : List.range 2 = [0, 1]), (by decide : List.range 1 = [0])]

private theorem parabolaLine_inv_one : (LawfulField.inv (g 1) : Goldilocks) = g 1 := by decide +kernel

set_option maxRecDepth 100000 in
private theorem parabolaLine_solve :
    solveHomogeneous 4 [[g 0, g 1, g 0, neg (g 1)], [g 0, g 0, g 1, g 0], [g 1, g 0, g 0, g 1]] =
      [neg (g 1), g 1, g 0, g 1] := by
  poly_eval [parabolaLine_inv_one]

/-- The computed eliminant of `Z² - Y` and `Z - 1` is a nonzero linear polynomial vanishing
    at `Y = 1`: the Gaussian solve, the Bézout identity and the degree budget all execute. -/
theorem resZ_parabola_line :
    resZ pA pB ≠ zero ∧ (resZ pA pB).natDeg = 1 ∧ (resZ pA pB).eval (g 1) = zero ∧
      add (mul (eliminant pA pB).1 pA) (mul (eliminant pA pB).2.1 pB) = C (resZ pA pB) := by
  have hvec : elimVec pA pB 2 2 1 2 1 = [neg (g 1), g 1, g 0, g 1] := by
    rw [Qsag.Poly2.elimVec.public_eqs, Qsag.Poly2.nullVec.public_eqs, parabolaLine_gens_length,
      parabolaLine_rows, parabolaLine_solve]
  have hE : eliminant pA pB =
      (elimU pA pB 2 2 1 2 1, elimV pA pB 2 2 1 2 1,
        coeffAt (add (mul (elimU pA pB 2 2 1 2 1) pA) (mul (elimV pA pB 2 2 1 2 1) pB)).coeffs 0) := by
    rw [Qsag.Poly2.eliminant.public_eqs, parabolaLine_degrees.1, parabolaLine_degrees.2.1,
      parabolaLine_degrees.2.2.1, parabolaLine_degrees.2.2.2.1, parabolaLine_degrees.2.2.2.2]
  have hU : elimU pA pB 2 2 1 2 1 = C (C (neg (g 1))) := by
    rw [Qsag.Poly2.elimU.public_eqs, hvec]; poly_eval [g, pA, pB]
  have hV : elimV pA pB 2 2 1 2 1 = ofList [one, one] := by
    rw [Qsag.Poly2.elimV.public_eqs, hvec]
    poly_eval [g, pA, pB, (by decide : List.range 2 = [0, 1]), (by decide : List.range 1 = [0])]
  rw [Qsag.Poly2.resZ.public_eqs, hE, hU, hV]
  poly_eval [g, pA, pB]

/-- The hypotheses of `common_roots_card_le_mul_deg` are jointly satisfiable:
    `1·A - (Z + 1)·B = 1 - Y` certifies coprimality and `(1, 1)` is a common zero. -/
theorem inhabited_common_roots :
    ∃ (A B : Poly2 Goldilocks) (pts : List (Goldilocks × Goldilocks)),
      1 ≤ A.natDeg ∧ B ≠ zero ∧ CoprimeZ A B ∧ (pts.map Prod.fst).Nodup ∧
      (∀ p ∈ pts, A.eval2 p.1 p.2 = zero ∧ B.eval2 p.1 p.2 = zero) ∧ pts.length = 1 :=
  ⟨pA, pB, [(g 1, g 1)], by decide, by decide,
    ⟨one, ofList [ofList [neg (g 1)], ofList [neg (g 1)]], ofList [g 1, neg (g 1)],
      by decide, by poly_eval [g, pA, pB, pDiag]⟩, by decide, by decide, rfl⟩

/-- Without coprimality the bound fails: `Z - Y` and itself share two points with distinct
    ordinates, more than `1 · 1`. -/
theorem tooth_common_roots_needs_coprime :
    ∃ (A B : Poly2 Goldilocks) (pts : List (Goldilocks × Goldilocks)),
      1 ≤ A.natDeg ∧ B ≠ zero ∧ (pts.map Prod.fst).Nodup ∧
      (∀ p ∈ pts, A.eval2 p.1 p.2 = zero ∧ B.eval2 p.1 p.2 = zero) ∧
      ¬ pts.length ≤ tdeg A * tdeg B :=
  ⟨pDiag, pDiag, [(g 0, g 0), (g 1, g 1)], by decide, by decide, by decide, by decide,
    by poly_eval [g, pA, pB, pDiag]⟩

#verify_constructive eliminant_bezout natDeg_resZ_le resZ_ne_zero_iff eval_resZ_eq_zero
#verify_constructive common_roots_card_le_mul_deg resZ_parabola_line
#tooth_pair common_roots_card_le_mul_deg vs tooth_common_roots_needs_coprime
#verify_inhabited common_roots_card_le_mul_deg inhabited_common_roots

end Poly2.Tests


end Qsag
end

public section
namespace Qsag
open CommRingOps RoundPoly UPoly
namespace PlaneBezoutTests
open Poly2
private theorem primitive_of_monic (A : Poly2 Goldilocks) (k : Nat)
    (hk : coeffAt A.coeffs k = one) : IsPrimY A := by
  refine ⟨fun he => NontrivialRing.one_ne_zero (by
    rw [← hk, he, coeffs_zero, coeffAt_nil]), fun g hg => ?_⟩
  obtain ⟨q, hq⟩ := hg k
  rw [hk] at hq
  have hg0 : g ≠ zero := fun e => NontrivialRing.one_ne_zero (by
    rw [hq, e, LawfulCommRing.zero_mul])
  have hq0 : q ≠ zero := fun e => NontrivialRing.one_ne_zero (by
    rw [hq, e, LawfulCommRing.mul_zero])
  have hd := UPoly.natDeg_mul hg0 hq0
  rw [← hq, natDeg_one] at hd
  omega

/-- Two intersections sharing their first coordinate: the new theorem applies where
`common_roots_card_le_mul_deg`'s distinct-projection premise does not. -/
theorem inhabited_primitive_common_roots :
    ∃ (A B : Poly2 Goldilocks) (pts : List (Goldilocks × Goldilocks)),
      IsPrimY A ∧ 1 ≤ A.natDeg ∧ B ≠ zero ∧ CoprimeZ A B ∧ pts.Nodup ∧
      (∀ p ∈ pts, A.eval2 p.1 p.2 = zero ∧ B.eval2 p.1 p.2 = zero) ∧
      pts.length = 2 ∧ ¬ (pts.map Prod.fst).Nodup := by
  let A : Poly2 Goldilocks := ofList [zero, neg one, one]
  let B : Poly2 Goldilocks := C X
  refine ⟨A, B, [(zero, zero), (zero, one)],
    primitive_of_monic A 2 (by decide +kernel), by decide +kernel,
    by decide +kernel, ?_, by decide +kernel, by poly_eval [A, B], rfl, by decide +kernel⟩
  refine ⟨zero, one, X, by decide +kernel, ?_⟩
  rw [LawfulCommRing.zero_mul, LawfulCommRing.one_mul, LawfulCommRing.zero_add]

/-- Vertical common components show why coprimality over the rational-function field
alone cannot bound finite plane intersections. -/
theorem tooth_common_roots_needs_primitive :
    ∃ (A B : Poly2 Goldilocks) (pts : List (Goldilocks × Goldilocks)),
      1 ≤ A.natDeg ∧ B ≠ zero ∧ CoprimeZ A B ∧ pts.Nodup ∧
      (∀ p ∈ pts, A.eval2 p.1 p.2 = zero ∧ B.eval2 p.1 p.2 = zero) ∧
      ¬ pts.length ≤ tdeg A * tdeg B * A.natDeg := by
  let A : Poly2 Goldilocks := ofList [zero, X]
  let B : Poly2 Goldilocks := C X
  refine ⟨A, B, [(zero, zero), (zero, one), (zero, Goldilocks.ofNat 2)],
    by decide +kernel, by decide +kernel, ?_, by decide +kernel,
    by decide +kernel, by poly_eval [A, B]⟩
  refine ⟨zero, one, X, by decide +kernel, ?_⟩
  rw [LawfulCommRing.zero_mul, LawfulCommRing.one_mul, LawfulCommRing.zero_add]

#verify_constructive inhabited_primitive_common_roots tooth_common_roots_needs_primitive
#verify_inhabited primitive_common_roots_card_le inhabited_primitive_common_roots
#tooth_pair primitive_common_roots_card_le vs tooth_common_roots_needs_primitive
end PlaneBezoutTests

end Qsag
end

public section
namespace Qsag
open CommRingOps RoundPoly UPoly
namespace SylvesterEliminationTests
open UPoly SylElim

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

/-- `(X - 3)(X - 5)` and `F = X + 2`, `ζ = 3`:
    `sylRes 2 1 ((X - 3)(X - 5)) (X + 2) = F(3) * sylRes 1 1 (X - 5) (X + 2) = 5 * 7 = 35`. -/
theorem inhabited_sylRes_mul_X_sub :
    ∃ (m' N : Nat) (ζ : Goldilocks) (Q F : UPoly Goldilocks),
      Q.natDeg ≤ m' ∧ F.natDeg ≤ N ∧
      sylRes (m' + 1) N (mul (sub X (C ζ)) Q) F = g 35 :=
  ⟨1, 1, g 3, ofList [neg (g 5), g 1], ofList [g 2, g 1],
    by decide +kernel, by decide +kernel, by
      rw [sylRes_mul_X_sub 1 1 (g 3) _ _ (by decide +kernel) (by decide +kernel)]
      poly_eval [g]⟩

/-- `#tooth`: dropping `B.eval ζ = 0` invalidates `sylRes_eq_zero_of_common_root`
    (`A = X - 3`, `B = X - 5`, `ζ = 3` gives `sylRes 1 1 A B = -2 ≠ 0`). -/
theorem tooth_sylRes_needs_both_roots :
    ∃ (m N : Nat) (A B : UPoly Goldilocks) (ζ : Goldilocks),
      1 ≤ m ∧ A.natDeg ≤ m ∧ B.natDeg ≤ N ∧ A.eval ζ = zero ∧
      sylRes m N A B ≠ zero :=
  ⟨1, 1, ofList [neg (g 3), g 1], ofList [neg (g 5), g 1], g 3,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by poly_eval [g]⟩

#verify_constructive SylElim.sylRes_mul_X_sub SylElim.sylRes_eq_zero_of_common_root
#verify_constructive SylElim.divModLead_spec SylElim.isUnit_sylRes_of_bezout SylElim.degFn_sylRes_le
#verify_constructive inhabited_sylRes_mul_X_sub tooth_sylRes_needs_both_roots
#tooth_pair SylElim.sylRes_eq_zero_of_common_root vs tooth_sylRes_needs_both_roots
#verify_inhabited SylElim.sylRes_mul_X_sub inhabited_sylRes_mul_X_sub

end SylvesterEliminationTests

end Qsag
end

public section
namespace Qsag
open CommRingOps RoundPoly UPoly
namespace Poly3.HenselTests
open UPoly Poly3

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

/-- `R = Z² - Y`: on the line `Y = 1` the root `P = 1` has separant `2 ≠ 0`. -/
def rPar : Poly3 Goldilocks := ofList [ofList [zero, neg one], zero, one]

/-- `R = Z² - X²`, with the two roots `±X` crossing at `X = 0`. -/
def rCross : Poly3 Goldilocks := ofList [ofList [ofList [g 0, g 0, neg (g 1)]], zero, one]

/-- The hypotheses of `root_unique_of_jet` are jointly satisfiable. -/
theorem inhabited_root_unique_of_jet :
    ∃ (R : Poly3 Goldilocks) (α β t₀ : Goldilocks) (P P' : UPoly Goldilocks),
      evalAffineLine R α β P = zero ∧ evalAffineLine R α β P' = zero ∧
      P.eval t₀ = P'.eval t₀ ∧
      ((hasseZ 1 R).evalAffineLine α β (C (P.eval t₀))).eval t₀ ≠ zero :=
  ⟨rPar, g 1, g 0, g 0, one, one, (by poly_eval [g, rPar, rCross]), (by poly_eval [g, rPar, rCross]), rfl,
    (by poly_eval [g, rPar, rCross])⟩

/-- The separant condition is needed: `X` and `-X` are distinct roots of `Z² - X²` with the
    same value at `t₀ = 0`, where the separant `2Z` vanishes. -/
theorem tooth_root_unique_needs_separant :
    ∃ (R : Poly3 Goldilocks) (α β t₀ : Goldilocks) (P P' : UPoly Goldilocks),
      evalAffineLine R α β P = zero ∧ evalAffineLine R α β P' = zero ∧
      P.eval t₀ = P'.eval t₀ ∧ P ≠ P' :=
  ⟨rCross, g 0, g 0, g 0, ofList [g 0, g 1], ofList [g 0, neg (g 1)], (by poly_eval [g, rPar, rCross]),
    (by poly_eval [g, rPar, rCross]), (by decide +kernel), (by decide +kernel)⟩

/-- For `R = Z² - Y` the first numerator is `N₁ = V` and the separant is `2Z`:
    `c₁ = V / (2Z)`, the derivative of `√Y` along `Y + V·W`. -/
theorem henselNum_parabola :
    henselNum rPar (g 0) 1 = jetV ∧ henselSep rPar (g 0) = mul (C3 (g 2)) X := by
  poly_eval [g, rPar, rCross]

/-- The hypotheses of `henselNum_spec` hold together: `R = Z² - Y` at the jet
    `(y, v, z) = (1, 1, 1)` with the first-order root `e = W/2` of `(1 + e)² = 1 + W`. -/
theorem inhabited_henselNum_spec :
    ∃ (R : Poly3 Goldilocks) (t₀ y v z : Goldilocks) (e : UPoly Goldilocks) (n : Nat),
      e.eval zero = zero ∧ eval3 R t₀ y z = zero ∧ eval3 (hasseZ 1 R) t₀ y z ≠ zero ∧
      (∀ k, k ≤ n → coeffAt (eval₂ (jetHom t₀ y v) (add (C z) e) R).coeffs k = zero) :=
  ⟨rPar, g 0, g 1, g 1, g 1, ofList [g 0, LawfulField.inv (g 2)], 1, by decide +kernel,
    by poly_eval [g, rPar, rCross], by poly_eval [g, rPar, rCross], fun k hk => by
      have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl <;> poly_eval [g, rPar, rCross]⟩

/-- The separant hypothesis of `henselNum_spec` is needed: `R = Z² - X²` at the origin has
    the root `e = W` with vanishing separant, and its first numerator `0` does not see it. -/
theorem tooth_henselNum_needs_separant :
    ∃ (R : Poly3 Goldilocks) (t₀ y v z : Goldilocks) (e : UPoly Goldilocks),
      e.eval zero = zero ∧ eval3 R t₀ y z = zero ∧
      eval₂ (jetHom t₀ y v) (add (C z) e) R = zero ∧
      (ptHom y v z).toFun (henselNum R t₀ 1) ≠ coeffAt e.coeffs 1 :=
  ⟨rCross, g 0, g 0, g 0, g 0, X, by decide +kernel, by poly_eval [g, rPar, rCross], by poly_eval [g, rPar, rCross],
    by poly_eval [g, rPar, rCross]⟩

#verify_constructive henselNum_spec deg_henselNum_le reconCoeff_spec deg_reconCoeff_le
#verify_constructive henselNum_parabola tooth_henselNum_needs_separant
#tooth_pair henselNum_spec vs tooth_henselNum_needs_separant
#verify_inhabited henselNum_spec inhabited_henselNum_spec
#verify_constructive UPoly.trunc_cancel UPoly.hensel_unique UPoly.taylorShift_neg_cancel
#verify_constructive root_unique_of_jet
#tooth_pair root_unique_of_jet vs tooth_root_unique_needs_separant
#verify_inhabited root_unique_of_jet inhabited_root_unique_of_jet

end Poly3.HenselTests


end Qsag
end

public section
namespace Qsag
open CommRingOps RoundPoly UPoly
namespace JohnsonBoundTests
open JohnsonBound

/-- Witness that `johnson_set_system_card_le` is inhabited and tight: `3` subsets of `{0, 1, 2}`
    of size `B = 2` intersecting in `t = 1` point achieve `johnsonBound 3 2 1 = 3`. -/
theorem inhabited_johnson_set_system :
    ∃ (D : List Nat) (fam : List (List Nat)) (mem : List Nat → Nat → Bool) (B t : Nat),
      D.Nodup ∧
      (∀ s ∈ fam, B ≤ (D.filter (fun z => mem s z)).length) ∧
      fam.Pairwise (fun s₁ s₂ => (D.filter (fun z => mem s₁ z && mem s₂ z)).length ≤ t) ∧
      D.length * t < B * B ∧
      fam.length = 3 ∧
      fam.length = johnsonBound D.length B t :=
  ⟨[0, 1, 2], [[0, 1], [1, 2], [0, 2]], fun s z => elemBool z s, 2, 1,
    by decide, by poly_eval, by poly_eval, by decide, rfl, by poly_eval⟩

/-- `#tooth`: without the Johnson denominator hypothesis `D.length * t < B * B`, the bound fails:
    at `D = [0, 1, 2, 3]`, `B = 2`, `t = 1` (`4 * 1 = 2 * 2`), `6` pairs of size `2` exist while
    `johnsonBound 4 2 1 = 0` fails to bound `6`. -/
theorem tooth_johnson_needs_pos_denom :
    ∃ (D : List Nat) (fam : List (List Nat)) (mem : List Nat → Nat → Bool) (B t : Nat),
      D.Nodup ∧
      (∀ s ∈ fam, B ≤ (D.filter (fun z => mem s z)).length) ∧
      fam.Pairwise (fun s₁ s₂ => (D.filter (fun z => mem s₁ z && mem s₂ z)).length ≤ t) ∧
      ¬ (fam.length ≤ johnsonBound D.length B t) :=
  ⟨[0, 1, 2, 3], [[0, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 3]], fun s z => elemBool z s, 2, 1,
    by decide, by poly_eval, by poly_eval, by poly_eval⟩

#verify_constructive JohnsonBound.nat_cauchy_schwarz JohnsonBound.count_partition_le
#verify_constructive JohnsonBound.johnson_set_system_mul_le JohnsonBound.johnson_set_system_card_le
#verify_constructive inhabited_johnson_set_system tooth_johnson_needs_pos_denom
#tooth_pair JohnsonBound.johnson_set_system_card_le vs tooth_johnson_needs_pos_denom
#verify_inhabited JohnsonBound.johnson_set_system_card_le inhabited_johnson_set_system

end JohnsonBoundTests


end Qsag
end

public section
namespace Qsag
open CommRingOps RoundPoly UPoly
namespace Poly3.ExplainerTests
open UPoly Poly3

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

/-- The count hypothesis is satisfiable: two points, multiplicity one, `Dy = 1`, `Wx = 2`
    give `5` unknowns against `4` equations. -/
theorem inhabited_explainer :
    ∃ (f g' : Goldilocks → Goldilocks) (Dm : List Goldilocks) (m d Wx Dy : Nat),
      Dm.length * triCount 1 m Dy m < triCount d Wx Dy (Dy + 1) ∧
      explainer f g' Dm m d Wx Dy ≠ zero :=
  ⟨fun _ => g 0, fun _ => g 1, [g 0, g 1], 1, 1, 2, 1, by poly_eval [g],
    (explainer_spec _ _ _ 1 1 2 1 (by poly_eval [g])).1⟩

/-- `Q = Z - Y` meets the order-one constraint at `z = 0` for `f(0) = 0`, `g(0) = 1`. -/
def qTooth : Poly3 Goldilocks := ofList [ofList [zero, neg one], one]

/-- The degree hypothesis of `evalAffineLine_eq_zero_of_agree` is needed: `Q = Z - Y`
    satisfies the constraint at the single point `0` and `P = X` agrees with the fold there
    (`α = β = 0`), yet `Q(X, 0, X) = X ≠ 0`; here `deg_{1,1,1} Q = 1 = m·|zs|`. -/
theorem tooth_agree_needs_degree :
    ∃ (Q : Poly3 Goldilocks) (f g' : Goldilocks → Goldilocks) (α β : Goldilocks)
      (P : UPoly Goldilocks) (zs : List Goldilocks), zs.Nodup ∧
      (∀ z ∈ zs, ∀ r t s, r + s < 1 → cons z (f z) (g' z) r t s Q = zero) ∧
      (∀ z ∈ zs, P.eval z = add (f z) (mul (add α (mul β z)) (g' z))) ∧ P.natDeg ≤ 1 ∧
      evalAffineLine Q α β P ≠ zero := by
  refine ⟨qTooth, fun _ => g 0, fun _ => g 1, g 0, g 0, X, [g 0], by decide, ?_, ?_,
    by decide, by poly_eval [g, qTooth]⟩
  · intro z hz r t s hrs
    rw [List.mem_singleton.mp hz]
    obtain ⟨rfl, rfl⟩ : r = 0 ∧ s = 0 := ⟨by omega, by omega⟩
    have e : (shiftHom (g 0) (g 0) (g 1)).toFun qTooth = X := by poly_eval [g, qTooth]
    rw [Poly3.cons_eq, Poly3.coeff3_eq]
    show coeffAt (coeffAt (coeffAt ((shiftHom (g 0) (g 0) (g 1)).toFun qTooth).coeffs 0).coeffs
      t).coeffs 0 = zero
    rw [e]
    show coeffAt (coeffAt (zero : UPoly (UPoly Goldilocks)).coeffs t).coeffs 0 = zero
    rw [coeffs_zero, coeffAt_nil, coeffs_zero, coeffAt_nil]
  · intro z hz
    rw [List.mem_singleton.mp hz]
    decide +kernel

#verify_constructive exists_trivariate_affine_explainer explainer_spec explainer_vanishes
#verify_constructive evalAffineLine_eq_zero_of_agree inPow_affine_of_cons unshift_shift
#verify_constructive tooth_agree_needs_degree inhabited_explainer
#tooth_pair evalAffineLine_eq_zero_of_agree vs tooth_agree_needs_degree
#verify_inhabited exists_trivariate_affine_explainer inhabited_explainer

end Poly3.ExplainerTests


end Qsag
end

public section
namespace Qsag
open CommRingOps RoundPoly UPoly
namespace Hensel.Tests
open UPoly Hensel

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

/-- `G(W, U) = (1 + U)² - (1 + W)`: the root series is `√(1 + W) - 1 = W/2 - W²/8 + …`. -/
def gSqrt : UPoly (UPoly Goldilocks) :=
  ofList [ofList [g 0, neg (g 1)], ofList [g 2], ofList [g 1]]

/-- The numerators of `√(1 + W) - 1`: `N₁ = 1`, `N₂ = -1`, with separant `2`, so
    `c₁ = 1/2` and `c₂ = -1/2³`. -/
theorem num_sqrt : sep gSqrt = g 2 ∧ num gSqrt 1 = g 1 ∧ num gSqrt 2 = neg (g 1) := by
  poly_eval [g, gSqrt]

/-- The hypotheses of `num_spec` hold for `G = (1 + U)² - (1 + W)` and the truncation
    `e = W/2` of its root, to first order. -/
theorem inhabited_num_spec :
    ∃ (G : UPoly (UPoly Goldilocks)) (e : UPoly Goldilocks) (n : Nat), e.eval zero = zero ∧
      res G = zero ∧ sep G ≠ zero ∧
      (∀ k, k ≤ n → coeffAt (G.eval e).coeffs k = zero) :=
  ⟨gSqrt, ofList [g 0, LawfulField.inv (g 2)], 1, by decide +kernel, by poly_eval [g, gSqrt],
    by poly_eval [g, gSqrt], fun k hk => by
      have hk' : k = 0 ∨ k = 1 := by omega
      have hinv : (LawfulField.inv (g 2) : Goldilocks) = g 9223372034707292161 := by decide +kernel
      rw [hinv]
      rcases hk' with rfl | rfl <;> poly_eval [g, gSqrt]⟩

/-- The separant hypothesis is needed: `G = U² - W²` has the root `e = W` with residue and
    separant both zero, and the conclusion `s·N₁ = s²·e₁` degenerates to `0 = 0` while the
    numerator carries no information: `N₁ = 0 ≠ e₁`. -/
theorem tooth_num_needs_separant :
    ∃ (G : UPoly (UPoly Goldilocks)) (e : UPoly Goldilocks), res G = zero ∧
      coeffAt e.coeffs 0 = zero ∧ G.eval e = zero ∧ num G 1 ≠ coeffAt e.coeffs 1 :=
  ⟨ofList [ofList [g 0, g 0, neg (g 1)], zero, one], X, by poly_eval [g, gSqrt], by decide +kernel,
    by poly_eval [g, gSqrt], by poly_eval [g, gSqrt]⟩

#verify_constructive Hensel.num_spec Hensel.delta_num_le Hensel.phi_contract Hensel.evG_eq
#verify_constructive Hensel.map_num num_sqrt tooth_num_needs_separant
#tooth_pair Hensel.num_spec vs tooth_num_needs_separant
#verify_inhabited Hensel.num_spec inhabited_num_spec

end Hensel.Tests


end Qsag
end

public section
namespace Qsag
open CommRingOps RoundPoly UPoly
namespace Poly3.SplitTests
open UPoly Poly3

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

/-- `R = Z² - Y`. -/
def rPar : Poly3 Goldilocks := ofList [ofList [zero, neg one], zero, one]

/-- `C = Y - (3 + 5X)`, vanishing exactly on the line `(α, β) = (3, 5)`. -/
def cLine : UPoly (UPoly Goldilocks) := ofList [neg (line (g 3) (g 5)), one]

/-- `2·R - Z·∂_Z R = -2Y` certifies that `Z² - Y` is squarefree in `Z`. -/
theorem sqFactor_rPar : SqFactor rPar :=
  SqFactor.of_cert (by poly_eval [g, rPar, cLine]) (ofList [ofList [ofList [g 2]]]) (ofList [zero, neg one])
    (ofList [zero, ofList [neg (g 2)]]) (by decide) (by poly_eval [g, rPar, cLine])

/-- The hypotheses of `excluded_pairs_card_le` hold together, with a genuinely excluded pair. -/
theorem inhabited_excluded_pairs :
    ∃ (Cc : UPoly (UPoly Goldilocks)) (Rs : List (Poly3 Goldilocks)) (D : Nat)
      (E : List (Goldilocks × Goldilocks)), Cc ≠ zero ∧ (∀ R ∈ Rs, SqFactor R) ∧
      Cc.natDeg + (Rs.map degYZ).sum ≤ D ∧ E.Nodup ∧
      (∀ p ∈ E, Excluded Cc Rs p.1 p.2) ∧ E.length = 1 :=
  ⟨cLine, [rPar], 3, [(g 3, g 5)], (by decide),
    (fun R hR => by rw [List.mem_singleton.mp hR]; exact sqFactor_rPar), (by poly_eval [g, rPar, cLine]),
    (by decide),
    (fun p hp => by
      rw [List.mem_singleton.mp hp, Qsag.Poly3.Excluded.public_eqs]
      exact Or.inl (by poly_eval [g, cLine])), rfl⟩

/-- The content must be nonzero: with `C = 0` every pair is excluded, so no bound holds. -/
theorem tooth_excluded_needs_content :
    ∃ (Rs : List (Poly3 Goldilocks)) (D : Nat) (E : List (Goldilocks × Goldilocks)),
      (∀ R ∈ Rs, SqFactor R) ∧
      (zero : UPoly (UPoly Goldilocks)).natDeg + (Rs.map degYZ).sum ≤ D ∧ E.Nodup ∧
      (∀ p ∈ E, Excluded zero Rs p.1 p.2) ∧ ¬ E.length ≤ D ^ 2 :=
  ⟨[], 0, [(g 0, g 0), (g 1, g 1)], (fun _ h => by cases h), (by decide), (by decide),
    (fun _ _ => by rw [Qsag.Poly3.Excluded.public_eqs]; exact Or.inl (UPoly.eval₂_zero _ _)), (by decide)⟩

local instance : NoZeroDivisors (RatFunc Goldilocks) := LawfulField.toNoZeroDivisors (RatFunc Goldilocks)

private theorem rPar_facts :
    rPar.natDeg = 2 ∧ (hasseZ 1 rPar).natDeg = 1 ∧ rPar.degYZ ≤ 2 ∧ (hasseZ 1 rPar).degYZ ≤ 1 ∧
      evalAffineLine rPar (g 1) (g 0) zero ≠ zero ∧
      evalAffineLine (hasseZ 1 rPar) (g 1) (g 0) zero = zero ∧
      coeffAt (hasseZ 1 rPar).coeffs 0 = zero ∧ (one : UPoly (UPoly Goldilocks)).eval (line (g 1) (g 0)) ≠ zero := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> poly_eval [g, rPar]

private theorem elimIdx_221 : Poly2.elimIdx 2 2 1 = [(0, 0)] := by
  poly_eval [(by decide : List.range 1 = [0])]
local notation "fracOf" => (Frac.of (D := UPoly Goldilocks))
local notation "yPt" => (RingHom.toFun fracOf (line (g 1) (g 0)))
local notation "evPt" => (UPoly.eval₂Hom (UPoly.evalHom yPt) (zero : RatFunc Goldilocks))

/-- The separant eliminant of `Z² - Y` does not vanish on the line `Y = 1`. The eliminant lives over
    `F(X)`; instead of running the Gaussian solve there, the Bézout identity is specialised at
    `(Y, Z) = (1, 0)` and at `Z = 0`, with the cofactor of `R` confined to the span of `mono 0 0`. -/
private theorem sepElim_rPar_eval_ne : (sepElim rPar).eval yPt ≠ zero := by
  intro h0
  obtain ⟨hm, hn, hdA, hdB, hcA, hcB, hB0, -⟩ := rPar_facts
  have hSq := sqFactor_rPar
  have hA1 := hSq.natDeg_liftK
  have hne := sepElim_ne_zero hSq
  rw [Qsag.Poly3.sepElim.public_eqs] at h0 hne
  have hL : ∀ Q : Poly3 Goldilocks,
      liftK.toFun Q = (UPoly.mapHom (UPoly.mapHom fracOf)).toFun Q := fun Q => by
    rw [Qsag.Poly3.liftK.public_eqs]
  have hmK : (liftK.toFun rPar).natDeg = 2 := by
    rw [hL, UPoly.natDeg_mapHom _ map_of_inj rPar, hm]
  have hnK : (liftK.toFun (hasseZ 1 rPar)).natDeg = 1 := by
    rw [hL, UPoly.natDeg_mapHom _ map_of_inj (hasseZ 1 rPar), hn]
  have ha : Poly2.tdeg (liftK.toFun rPar) = 2 := by
    have h1 : Poly2.tdeg (liftK.toFun rPar) ≤ rPar.degYZ := by
      rw [hL]; exact UPoly.wdeg_mapHom_mapHom_le _ rPar
    have h2 := Poly2.natDeg_le_tdeg (liftK.toFun rPar)
    omega
  have hb : Poly2.tdeg (liftK.toFun (hasseZ 1 rPar)) = 1 := by
    have h1 : Poly2.tdeg (liftK.toFun (hasseZ 1 rPar)) ≤ (hasseZ 1 rPar).degYZ := by
      rw [hL]; exact UPoly.wdeg_mapHom_mapHom_le _ (hasseZ 1 rPar)
    have h2 := Poly2.natDeg_le_tdeg (liftK.toFun (hasseZ 1 rPar))
    omega
  have hT : Poly2.elimDeg (liftK.toFun rPar) (liftK.toFun (hasseZ 1 rPar)) = 2 := by
    rw [Qsag.Poly2.elimDeg.public_eqs, hmK, hnK, ha, hb]
  have hbez := Poly2.eliminant_bezout (liftK.toFun rPar) (liftK.toFun (hasseZ 1 rPar)) hA1
  have hU : (Poly2.eliminant (liftK.toFun rPar) (liftK.toFun (hasseZ 1 rPar))).1 =
      Poly2.elimU (liftK.toFun rPar) (liftK.toFun (hasseZ 1 rPar)) 2 2 1 2 1 := by
    rw [Qsag.Poly2.eliminant.public_eqs, hT, hmK, hnK, ha, hb]
  have hEvA : (evPt).toFun (liftK.toFun rPar) = (fracOf).toFun (evalAffineLine rPar (g 1) (g 0) zero) := by
    rw [UPoly.eval₂Hom_apply, hL, evalAffineLine_eq_eval₂]
    have h := UPoly.eval₂_mapHom_mapHom fracOf rPar (line (g 1) (g 0)) zero
    rw [RingHom.map_zero] at h
    exact h
  have hEvB : (evPt).toFun (liftK.toFun (hasseZ 1 rPar)) = zero := by
    rw [UPoly.eval₂Hom_apply, hL]
    have h := UPoly.eval₂_mapHom_mapHom fracOf (hasseZ 1 rPar) (line (g 1) (g 0)) zero
    rw [RingHom.map_zero, ← evalAffineLine_eq_eval₂, hcB, RingHom.map_zero] at h
    exact h
  have hEvC : ∀ r : UPoly (RatFunc Goldilocks), (evPt).toFun (UPoly.C r) = r.eval yPt := fun r => by
    rw [UPoly.eval₂Hom_apply, UPoly.eval₂_C, UPoly.evalHom_apply]
  have hEvCC : ∀ x : RatFunc Goldilocks, (evPt).toFun (UPoly.C (UPoly.C x)) = x := fun x => by
    rw [hEvC, UPoly.eval_C]
  have hEvMono : (evPt).toFun (Poly2.mono 0 0) = one := by
    rw [UPoly.eval₂Hom_apply, Qsag.Poly2.mono.public_eqs]
    simp [Qsag.monomial.public_eqs, UPoly.eval₂_ofList, UPoly.evalHom_apply,
      LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    exact UPoly.eval_C (one : RatFunc Goldilocks) _
  have hUz : (Poly2.eliminant (liftK.toFun rPar) (liftK.toFun (hasseZ 1 rPar))).1 = zero := by
    have hΨ := congrArg (evPt).toFun hbez
    rw [RingHom.map_add, RingHom.map_mul, RingHom.map_mul, hEvA, hEvB, hEvC, h0,
      LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at hΨ
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hΨ with hu | hc
    · rw [hU, Qsag.Poly2.elimU.public_eqs, elimIdx_221] at hu ⊢
      simp only [List.length_singleton, List.map_cons, List.map_nil] at hu ⊢
      generalize List.take 1 (Poly2.elimVec (liftK.toFun rPar) (liftK.toFun (hasseZ 1 rPar)) 2 2 1 2 1) = xs
        at hu ⊢
      cases xs with
      | nil => simp only [Qsag.Poly2.lincomb.public_eqs]
      | cons x xs' =>
        simp only [Qsag.Poly2.lincomb.public_eqs, Poly2.lincomb_nil] at hu ⊢
        rw [RingHom.map_add, RingHom.map_mul, RingHom.map_zero, LawfulCommRing.add_zero, hEvCC,
          hEvMono, LawfulCommRing.mul_one] at hu
        rw [hu, UPoly.C_zero_eq, UPoly.C_zero_eq, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
    · exact absurd (Frac.of_injective (hc.trans (fracOf).map_zero.symm)) hcA
  rw [hUz, LawfulCommRing.zero_mul, LawfulCommRing.zero_add] at hbez
  have h3 := congrArg (UPoly.evalHom (zero : UPoly (RatFunc Goldilocks))).toFun hbez
  rw [RingHom.map_mul] at h3
  simp only [UPoly.evalHom_apply] at h3
  rw [UPoly.eval_C, UPoly.eval_zero_eq (liftK.toFun (hasseZ 1 rPar)), hL (hasseZ 1 rPar), UPoly.coeffAt_mapHom, hB0,
    RingHom.map_zero, LawfulCommRing.mul_zero] at h3
  rw [hL (hasseZ 1 rPar)] at hne
  exact hne h3.symm
/-- A root on a non-excluded line: on `Y = 1` the factor `Z² - 1` has the simple root
    `P = 1`. The separant eliminant is computed over `F(X)` by the kernel. -/
theorem inhabited_simple_root :
    ∃ (Cc : UPoly (UPoly Goldilocks)) (Rs : List (Poly3 Goldilocks))
      (e : Poly3 Goldilocks → Nat) (α β : Goldilocks) (P : UPoly Goldilocks),
      (∀ R ∈ Rs, SqFactor R) ∧ ¬ Excluded Cc Rs α β ∧
      evalAffineLine (factored Cc Rs e) α β P = zero :=
  ⟨one, [rPar], fun _ => 1, g 1, g 0, ofList [g 1],
    (fun R hR => by rw [List.mem_singleton.mp hR]; exact sqFactor_rPar),
    (by
      rw [Qsag.Poly3.Excluded.public_eqs]
      rintro (h | ⟨R, hR, h⟩)
      · exact rPar_facts.2.2.2.2.2.2.2 h
      · rw [List.mem_singleton.mp hR] at h; exact sepElim_rPar_eval_ne h),
    (by poly_eval [g, rPar, cLine, CRing.npow])⟩

#verify_constructive excluded_pairs_card_le simple_root_of_not_excluded sepElim_ne_zero
#verify_constructive natDeg_sepElim_le sqFactor_rPar Frac.of_injective UPoly.d5_split
#tooth_pair excluded_pairs_card_le vs tooth_excluded_needs_content
#verify_inhabited excluded_pairs_card_le inhabited_excluded_pairs
#verify_inhabited simple_root_of_not_excluded inhabited_simple_root

end Poly3.SplitTests


end Qsag
end

public section
namespace Qsag
open CommRingOps RoundPoly UPoly
namespace SylvesterDerivTests
open UPoly SylElim

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

/-- Common root `ζ = 3` of `C1 = (X - 3)(X - 5)` (`ofList [15, -8, 1]`) and `P0 = X - 3`, `B = X + 2`:
    `sylResDeriv 2 1 C1 P0 B = B(3) * sylResDeriv 2 1 C1 P0 1 = 5 * (-2)`. -/
theorem inhabited_sylResDeriv_common_root :
    ∃ (m N : Nat) (C1 P0 B : UPoly Goldilocks) (ζ : Goldilocks),
      1 ≤ m ∧ C1.natDeg ≤ m ∧ P0.natDeg ≤ N ∧ B.natDeg ≤ N ∧
      C1.eval ζ = zero ∧ P0.eval ζ = zero ∧
      sylResDeriv m N C1 P0 B ≠ zero :=
  ⟨2, 1, ofList [g 15, neg (g 8), g 1], ofList [neg (g 3), g 1], ofList [g 2, g 1], g 3,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by poly_eval [g]⟩

/-- `#tooth`: dropping `P0.eval ζ = 0` invalidates `sylResDeriv_common_root`
    (`C1 = (X - 3)(X - 5)`, `P0 = X - 7`, `B = X`, `ζ = 3`). -/
theorem tooth_sylResDeriv_needs_P0_root :
    ∃ (m N : Nat) (C1 P0 B : UPoly Goldilocks) (ζ : Goldilocks),
      1 ≤ m ∧ C1.natDeg ≤ m ∧ P0.natDeg ≤ N ∧ B.natDeg ≤ N ∧ C1.eval ζ = zero ∧
      sylResDeriv m N C1 P0 B ≠ mul (B.eval ζ) (sylResDeriv m N C1 P0 one) :=
  ⟨2, 1, ofList [g 15, neg (g 8), g 1], ofList [neg (g 7), g 1], X, g 3,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by poly_eval [g]⟩

#verify_constructive SylElim.sylResDeriv_of_factor SylElim.sylResDeriv_common_root SylElim.degFn_sylResDeriv_le
#verify_constructive inhabited_sylResDeriv_common_root tooth_sylResDeriv_needs_P0_root
#tooth_pair SylElim.sylResDeriv_common_root vs tooth_sylResDeriv_needs_P0_root
#verify_inhabited SylElim.sylResDeriv_common_root inhabited_sylResDeriv_common_root

end SylvesterDerivTests

end Qsag
end

public section
namespace Qsag
open CommRingOps RoundPoly UPoly
namespace Poly3.StratTests
open UPoly Poly3

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

/-- `Q = (Z - X)²`, with the double root `P = X` on every line. -/
def qDouble : Poly3 Goldilocks :=
  ofList [ofList [ofList [g 0, g 0, g 1]], ofList [ofList [g 0, neg (g 2)]], one]

/-- `Q = Z·(Y - X)`, which vanishes identically on the line `Y = X`. -/
def qLine : Poly3 Goldilocks := ofList [zero, ofList [ofList [g 0, neg (g 1)], one]]

/-- The hypotheses of `simple_root_of_hasse` hold together for the double root of `(Z - X)²`. -/
theorem inhabited_simple_root_of_hasse :
    ∃ (Q : Poly3 Goldilocks) (α β : Goldilocks) (P : UPoly Goldilocks),
      (∀ k, 1 ≤ k → k ≤ Q.degZ → (CRing.natCast k : Goldilocks) ≠ zero) ∧
      lineSpec Q α β ≠ zero ∧ evalAffineLine Q α β P = zero :=
  ⟨qDouble, g 3, g 5, X, fun k h1 h2 => by
      have hk : k = 1 ∨ k = 2 := by
        have : qDouble.degZ = 2 := by poly_eval [g, qDouble, qLine]
        omega
      rcases hk with rfl | rfl <;> decide +kernel,
    by poly_eval [g, qDouble, qLine], by poly_eval [g, qDouble, qLine]⟩

/-- The double root is found at multiplicity two: `∂_Z Q = 2(Z - X)` vanishes at `P = X` and
    its derivative `2` does not. -/
theorem double_root_stratum :
    evalAffineLine (hasseZ 1 qDouble) (g 3) (g 5) X = zero ∧
      evalAffineLine (hasseZ 1 (hasseZ 1 qDouble)) (g 3) (g 5) X ≠ zero := by
  poly_eval [g, qDouble, qLine]

/-- The non-vanishing hypothesis is needed: `Q = Z·(Y - X)` has every `P` as a root on the
    line `Y = X`, and none of them is a simple root of a Hasse derivative of `Q`. -/
theorem tooth_simple_root_needs_nonvanishing :
    ∃ (Q : Poly3 Goldilocks) (α β : Goldilocks) (P : UPoly Goldilocks),
      evalAffineLine Q α β P = zero ∧
      ¬ ∃ μ, 1 ≤ μ ∧ μ ≤ Q.degZ ∧ evalAffineLine (hasseZ (μ - 1) Q) α β P = zero ∧
        evalAffineLine (hasseZ 1 (hasseZ (μ - 1) Q)) α β P ≠ zero :=
  ⟨qLine, g 0, g 1, X, by poly_eval [g, qDouble, qLine], fun ⟨μ, h1, h2, _, h4⟩ => by
    have hd : qLine.degZ = 1 := by poly_eval [g, qDouble, qLine]
    rw [hd] at h2
    have hμ : μ = 1 := Nat.le_antisymm h2 h1
    subst hμ
    exact h4 (by poly_eval [g, qDouble, qLine])⟩

#verify_constructive simple_root_of_hasse exists_multiplicity lineSpec_zero_card_le
#verify_constructive UPoly.hasse_one_hasse double_root_stratum
#verify_constructive tooth_simple_root_needs_nonvanishing
#tooth_pair simple_root_of_hasse vs tooth_simple_root_needs_nonvanishing
#verify_inhabited simple_root_of_hasse inhabited_simple_root_of_hasse

end Poly3.StratTests


end Qsag
end

public section
namespace Qsag.Cwyz26EqualDegreeAndMultiFoldTests
open CommRingOps RoundPoly UPoly Poly2 SylElim
private theorem isPrimY_W : IsPrimY (X : Poly2 Goldilocks) := by
  refine ⟨by decide +kernel, fun f hf => ?_⟩
  obtain ⟨q, hq⟩ := hf 1
  have h1 : coeffAt (X : Poly2 Goldilocks).coeffs 1 = one := by decide +kernel
  rw [h1] at hq
  have hf0 : f ≠ zero := fun e => NontrivialRing.one_ne_zero (by rw [hq, e, LawfulCommRing.zero_mul])
  have hq0 : q ≠ zero := fun e => NontrivialRing.one_ne_zero (by rw [hq, e, LawfulCommRing.mul_zero])
  have hd := UPoly.natDeg_mul hf0 hq0
  rw [← hq, natDeg_one] at hd; omega

/-- Joint inhabitedness witness for `SylElim.curve_leaf_gcd_decomp` on the smooth 2-sheet cylinder
    `C₁ = Z² - 1`, `P₀ = W` (`C X`), `E = W` (`X`). -/
theorem inhabited_curve_leaf_gcd_decomp :
    ∃ (h_C H₀ : Nat) (C₁ E : Poly2 Goldilocks) (P₀ : UPoly (Poly2 Goldilocks)),
      C₁.natDeg ≤ h_C ∧ coeffAt C₁.coeffs h_C = one ∧ P₀.natDeg ≤ H₀ ∧
      IsPrimY E ∧ 1 ≤ tdeg E ∧
      (∃ Q_res, sylRes h_C H₀ (embedUZ.toFun C₁) P₀ = mul E Q_res) ∧
      sylRes h_C H₀ (embedUZ.toFun C₁) P₀ ≠ zero :=
  let C₁ : Poly2 Goldilocks := ofList [neg one, zero, one]
  ⟨2, 1, C₁, X, C X,
    by decide +kernel, by decide +kernel, by decide +kernel,
    isPrimY_W, by poly_eval [C₁], ⟨X, by poly_eval [C₁]⟩, by poly_eval [C₁]⟩

/-- `#tooth`: even when `C₁ = Z² - 1` is monic AND separable in `Z` (`sylRes 2 1 C₁ (hasse 1 C₁) ≠ 0`),
    over `E = W` (`P₀ = W`) BOTH sheets `Z = ±1` vanish simultaneously, forcing `Gj.deg = 2` and
    `Ej ∣ g₁` in `curve_leaf_gcd_decomp` (proving constructively that the `Ej ∣ g₁` multi-sheet
    branch is algebraically realizable for smooth separable `C₁`!). -/
theorem tooth_multisheet_smooth_cylinder_divides_g1 :
    ∃ (C₁ : Poly2 Goldilocks) (P₀ : UPoly (Poly2 Goldilocks))
      (Ej : Poly2 Goldilocks) (hPj : IsPrimY Ej) (hDj : 1 ≤ Ej.natDeg)
      (Gj : MonicPoly (ModMonic (monicFY Ej hPj hDj))),
      sylRes 2 1 C₁ (UPoly.hasse 1 C₁) ≠ zero ∧
      Gj.deg = 2 ∧
      ∃ Qg, sylResDeriv 2 1 (embedUZ.toFun C₁) P₀ one = mul Ej Qg := by
  let C₁ : Poly2 Goldilocks := ofList [neg one, zero, one]
  let P₀ : UPoly (Poly2 Goldilocks) := C X
  obtain ⟨Es, _, hCover, hLeaves⟩ :=
    SylElim.curve_leaf_gcd_decomp (h_C := 2) (H₀ := 1) (C₁ := C₁) (P₀ := P₀)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      X isPrimY_W (by poly_eval [C₁, P₀]) ⟨X, by poly_eval [C₁, P₀]⟩
  obtain ⟨Ej, hMem, _⟩ := hCover zero zero (by decide +kernel)
  obtain ⟨hPj, hDj, Gj, ⟨QE, hXE⟩, hDegLe2, ⟨U0, V0, hBez⟩, _, _, _, _, hDichot, _⟩ :=
    hLeaves Ej hMem
  rcases hDichot with ⟨hDeg1, _⟩ | ⟨hDeg2, hDivG1⟩
  · exfalso
    let φ := modPoly2Hom Ej hPj hDj
    have hX0 : φ.toFun X = zero := (modPoly2Hom_eq_zero_iff Ej hPj hDj X).mpr ⟨QE, hXE⟩
    have hP0_0 : (mapHom φ).toFun P₀ = zero := by
      dsimp only [P₀]; rw [mapHom_C, hX0]; exact CHom.map_zero
    rw [hP0_0, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at hBez
    let C1_mod := (mapHom φ).toFun (embedUZ.toFun C₁)
    have hC1_deg : C1_mod.natDeg ≤ 2 :=
      Nat.le_trans (natDeg_mapHom_le φ _)
        (Nat.le_trans (by rw [Qsag.SylElim.embedUZ.public_eqs]; exact natDeg_mapHom_le CHom C₁)
          (by decide +kernel))
    have hC1_mon : coeffAt C1_mod.coeffs 2 = one := by
      dsimp only [C1_mod]
      rw [Qsag.SylElim.embedUZ.public_eqs]
      have hTop : coeffAt C₁.coeffs 2 = one := by decide +kernel
      rw [coeffAt_mapHom, coeffAt_mapHom, hTop, CHom.map_one, φ.map_one]
    let M_C1 : MonicPoly (ModMonic (monicFY Ej hPj hDj)) := ⟨C1_mod, 2, by decide, hC1_deg, hC1_mon⟩
    have hLt2 : (mul U0 M_C1.poly).natDeg < M_C1.deg := by
      change (mul U0 C1_mod).natDeg < 2
      rw [hBez]
      exact Nat.lt_of_le_of_lt Gj.natDeg_le (by omega)
    have hU0 := eq_zero_of_mul_monic_lt M_C1 hLt2
    rw [hU0, LawfulCommRing.zero_mul] at hBez
    have h10 : (one : ModMonic (monicFY Ej hPj hDj)) = zero := by
      rw [← Gj.coeff_deg, ← hBez, coeffs_zero, coeffAt_nil]
    exact NontrivialRing.one_ne_zero h10
  · exact ⟨C₁, P₀, Ej, hPj, hDj, Gj, by poly_eval [C₁, P₀], by omega, hDivG1⟩

/-- Joint inhabitedness witness for `SylElim.curve_three_poly_sheet_decomp` (`C₁ = Z² - 1`,
    `P₀ = W`, `H = Z`, `E = W`). -/
theorem inhabited_curve_three_poly_sheet_decomp :
    ∃ (h_C H₀ : Nat) (C₁ E : Poly2 Goldilocks) (P₀ H : UPoly (Poly2 Goldilocks)),
      C₁.natDeg ≤ h_C ∧ coeffAt C₁.coeffs h_C = one ∧ P₀.natDeg ≤ H₀ ∧ H.natDeg ≤ 1 ∧
      IsPrimY E ∧ 1 ≤ tdeg E ∧
      (∃ Q_res, sylRes h_C H₀ (embedUZ.toFun C₁) P₀ = mul E Q_res) :=
  let C₁ : Poly2 Goldilocks := ofList [neg one, zero, one]
  ⟨2, 1, C₁, X, C X, X,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    isPrimY_W, by poly_eval [C₁], ⟨X, by poly_eval [C₁]⟩⟩

/-- `#tooth`: without resultant divisibility (`E ∤ sylRes`), `curve_three_poly_sheet_decomp` fails
    on `C₁ = Z`, `P₀ = 1`, `H = Z`, `E = W`: no leaf can have a positive-degree common `Z`-gcd `Gj`. -/
theorem tooth_three_poly_sheet_needs_divisibility :
    ∃ (C₁ E : Poly2 Goldilocks) (P₀ H : UPoly (Poly2 Goldilocks)),
      C₁.natDeg ≤ 1 ∧ coeffAt C₁.coeffs 1 = one ∧ P₀.natDeg ≤ 0 ∧ H.natDeg ≤ 1 ∧
      IsPrimY E ∧ 1 ≤ tdeg E ∧
      ¬ ∃ Es : List (Poly2 Goldilocks),
        (Es.map tdeg).sum = tdeg E ∧
        (∀ u w, E.eval2 u w = zero → ∃ Ej ∈ Es, Ej.eval2 u w = zero) ∧
        ∀ Ej ∈ Es, ∃ (hPj : IsPrimY Ej) (hDj : 1 ≤ Ej.natDeg)
          (Gj : MonicPoly (ModMonic (monicFY Ej hPj hDj))),
          (∃ Q_P, ((mapHom (modPoly2Hom Ej hPj hDj)).toFun P₀) = mul Gj.poly Q_P) := by
  refine ⟨X, X, one, X, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, isPrimY_W, by poly_eval, ?_⟩
  rintro ⟨Es, _, hCover, hLeaves⟩
  obtain ⟨Ej, hMem, _⟩ := hCover zero zero (by decide +kernel)
  obtain ⟨hPj, hDj, Gj, ⟨QP, hQP⟩⟩ := hLeaves Ej hMem
  rw [RingHom.map_one] at hQP
  have hQPNe : QP ≠ zero := fun e => NontrivialRing.one_ne_zero (by rw [hQP, e, LawfulCommRing.mul_zero])
  have hz : coeffAt (one : UPoly (ModMonic (monicFY Ej hPj hDj))).coeffs (Gj.deg + QP.natDeg) = zero := by
    have hd1 : (one : UPoly (ModMonic (monicFY Ej hPj hDj))).natDeg = 0 := natDeg_one
    have hPos : 1 ≤ Gj.deg := Gj.deg_pos
    exact UPoly.coeffAt_eq_zero_of_natDeg_lt _ (by omega)
  have hGjDegEq : Gj.poly.natDeg = Gj.deg := by
    apply Nat.le_antisymm Gj.natDeg_le
    apply Decidable.byContradiction; intro hNot
    have hc := Gj.poly.coeffAt_eq_zero_of_natDeg_lt (Nat.lt_of_not_le hNot)
    rw [Gj.coeff_deg] at hc
    exact NontrivialRing.one_ne_zero hc
  rw [hQP, ← hGjDegEq, (coeffAt_mul_top Gj.poly QP).2] at hz
  rw [UPoly.lead_eq Gj.poly] at hz
  rw [hGjDegEq, Gj.coeff_deg, LawfulCommRing.one_mul] at hz
  exact lead_ne_zero hQPNe hz


#verify_constructive inhabited_curve_leaf_gcd_decomp
#verify_inhabited Qsag.SylElim.curve_leaf_gcd_decomp inhabited_curve_leaf_gcd_decomp
#verify_constructive tooth_multisheet_smooth_cylinder_divides_g1
#tooth_pair Qsag.SylElim.curve_leaf_gcd_decomp vs tooth_multisheet_smooth_cylinder_divides_g1
#verify_constructive inhabited_curve_three_poly_sheet_decomp
#verify_inhabited Qsag.SylElim.curve_three_poly_sheet_decomp inhabited_curve_three_poly_sheet_decomp
#verify_constructive tooth_three_poly_sheet_needs_divisibility
#tooth_pair Qsag.SylElim.curve_three_poly_sheet_decomp vs tooth_three_poly_sheet_needs_divisibility

end Qsag.Cwyz26EqualDegreeAndMultiFoldTests
end

public section
namespace Qsag
open CommRingOps RoundPoly UPoly Poly3
namespace JohnsonCertTests


end JohnsonCertTests

namespace DeployedStageTests
open JohnsonCertTests


/-- The check refuses a persistence threshold at the agreement threshold (`B = A`), and one
    below the Johnson radius (`n·(d + 1) ≥ B²`), on the deployed `(9, 1)` geometry. -/
theorem tooth_slicedParamsOk_rejects :
    slicedParamsOk 256 18 127 127 1 20 = false ∧ slicedParamsOk 256 18 127 69 1 20 = false ∧
      slicedParamsOk 256 18 127 70 1 20 = true := by
  decide +kernel

#verify_constructive sumTo_le_of_le slicedParamsOk_sound


#verify_constructive tooth_slicedParamsOk_rejects


end DeployedStageTests


end Qsag
end

public section
namespace Qsag.MigrationExecution
end Qsag.MigrationExecution
namespace Qsag
open MigrationExecution
#verify_constructive tooth_packTower_is_not_the_poly_basis

end Qsag
end

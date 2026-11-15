module
public import Qsag.Math.Lattices
import all Qsag.Math.Lattices
import all Qsag.Coding.AffineProximity
import all Qsag.Coding.Resultant
import all Qsag.Math.EllipticCurves
import all Qsag.Math.Algebra
import all Qsag.Math.Primality
import all Qsag.Math.Gf2Pow128
public import Qsag.Tactic.Prelude
public import Qsag.Math.EllipticCurves
public import Qsag.Math.Algebra
public import Qsag.Math.Primality
public import Qsag.Math.Gf2Pow128
public import Qsag.Math.Goldilocks
import all Qsag.Math.Goldilocks
public import Qsag.Math.QuarticExt4
import all Qsag.Math.QuarticExt4
public import Qsag.Coding.ReedSolomon
import all Qsag.Coding.ReedSolomon
import all Qsag.Coding.GuruswamiSudan
public import Qsag.Coding.Cwyz26
import all Qsag.Coding.Cwyz26
public section
namespace Qsag
open CommRingOps RoundPoly
set_option autoImplicit false
set_option exponentiation.threshold 512
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
/-- A point of order two keeps its parity under negation: on `y² = x³ + 7` over `ℤ/7`
    the point `(0, 0)` is its own negative. `PrimeOrderGroup.n_odd` excludes this. -/
theorem tooth_two_torsion_point_is_its_own_negative :
    ∃ (C : Curve) (P : Point), C.OnCurve P ∧ P ≠ none ∧ C.p % 2 = 1 ∧
      Point.yOdd (C.neg P) = Point.yOdd P ∧ C.smul 2 P = none := by
  refine ⟨⟨7, 0, 7⟩, some (0, 0), ?_, ?_, ?_, ?_, ?_⟩ <;> decide

#tooth_pair
  Qsag.Weierstrass.Curve.PrimeOrderGroup.xonly_parity_laws
  vs
  Qsag.Weierstrass.tooth_two_torsion_point_is_its_own_negative


end Weierstrass

/-- **`#tooth` Ed25519 Clamped Scalars Exceed `ED_ORDER` & Wrap Non-Injectively (`tooth_ed25519_clamped_wraps_mod_order_non_injective`)**:
    1. Every clamped value `c = clampEd25519Bytes32 raw` satisfies `ED25519_ORDER_L < c.toNat`, so
       feeding `c` directly into `requireCanonicalScalar .Ed25519` **always fails** (`= false`), and
       `reduceEd25519Order c ≠ c`.
    2. Distinct values `≥ ED_ORDER` (`x1 = BitVec.ofNat 256 (2^254)` and
       `x2 = BitVec.ofNat 256 (2^254 - ED25519_ORDER_L)`, both `> ED25519_ORDER_L`) wrap to the
       **same** canonical scalar modulo `ED_ORDER`, proving `reduceEd25519Order`,
       `clampEd25519Bytes32`, and `normalizeSlip0010Ed25519Scalar` are all non-injective! -/
theorem tooth_ed25519_clamped_wraps_mod_order_non_injective :
    ∃ x1 x2 : BitVec 256,
      (∀ raw : BitVec 256,
        ED25519_ORDER_L < (clampEd25519Bytes32 raw).toNat ∧
        requireCanonicalScalar .Ed25519 (clampEd25519Bytes32 raw) = false ∧
        reduceEd25519Order (clampEd25519Bytes32 raw) ≠ clampEd25519Bytes32 raw) ∧
      ED25519_ORDER_L ≤ x1.toNat ∧
      ED25519_ORDER_L ≤ x2.toNat ∧
      x1 ≠ x2 ∧
      reduceEd25519Order x1 = reduceEd25519Order x2 ∧
      ¬ Function.Injective clampEd25519Bytes32 ∧
      ¬ Function.Injective reduceEd25519Order ∧
      ¬ Function.Injective normalizeSlip0010Ed25519Scalar := by
  have hOrd := curve_orders_match_le_limbs_and_bounds
  have hOrdLt253 : ED25519_ORDER_L < 2 ^ 253 := hOrd.2.2.2.2.2.2.1
  have h253_254 : (2 : Nat) ^ 254 = 2 * (2 ^ 253) := by decide
  have h254Lt256 : (2 : Nat) ^ 254 < 2 ^ 256 := by decide
  have hAllWrap : ∀ raw : BitVec 256,
      ED25519_ORDER_L < (clampEd25519Bytes32 raw).toNat ∧
      requireCanonicalScalar .Ed25519 (clampEd25519Bytes32 raw) = false ∧
      reduceEd25519Order (clampEd25519Bytes32 raw) ≠ clampEd25519Bytes32 raw := by
    intro raw
    have hb := clampEd25519Bytes32_bits_and_range raw
    have hGtOrd : ED25519_ORDER_L < (clampEd25519Bytes32 raw).toNat := by omega
    have hNotCanon : requireCanonicalScalar .Ed25519 (clampEd25519Bytes32 raw) = false := by
      unfold requireCanonicalScalar ScalarGroup.orderNat
      have hNotLt : ¬ ((clampEd25519Bytes32 raw).toNat < ED25519_ORDER_L) := by omega
      rw [decide_eq_false hNotLt, Bool.and_false]
    have hRedNe : reduceEd25519Order (clampEd25519Bytes32 raw) ≠ clampEd25519Bytes32 raw := by
      intro hEq
      have hv := congrArg BitVec.toNat hEq
      unfold reduceEd25519Order at hv
      have hModLt : (clampEd25519Bytes32 raw).toNat % ED25519_ORDER_L < ED25519_ORDER_L :=
        Nat.mod_lt _ (by omega)
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hv
      omega
    exact ⟨hGtOrd, hNotCanon, hRedNe⟩
  let x1 : BitVec 256 := clampEd25519Bytes32 0#256
  let x2 : BitVec 256 := BitVec.ofNat 256 (x1.toNat - ED25519_ORDER_L)
  have hx1Val : x1.toNat = 2 ^ 254 := by
    change clampEd25519Nat 0 = 2 ^ 254
    unfold clampEd25519Nat
    simp
  have hx2Val : x2.toNat = 2 ^ 254 - ED25519_ORDER_L := by
    dsimp [x2]
    rw [hx1Val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx1Ge : ED25519_ORDER_L ≤ x1.toNat := by omega
  have hx2Ge : ED25519_ORDER_L ≤ x2.toNat := by omega
  have hx1NeX2 : x1 ≠ x2 := by
    intro hEq
    have hv := congrArg BitVec.toNat hEq
    omega
  have hRedEq : reduceEd25519Order x1 = reduceEd25519Order x2 := by
    unfold reduceEd25519Order
    apply congrArg (BitVec.ofNat 256)
    rw [hx1Val, hx2Val]
    have hSplit : 2 ^ 254 = (2 ^ 254 - ED25519_ORDER_L) + ED25519_ORDER_L * 1 := by omega
    conv => lhs; rw [hSplit]
    rw [Nat.add_mul_mod_self_left]
  have hClamp01 : clampEd25519Bytes32 0#256 = clampEd25519Bytes32 1#256 := by
    apply BitVec.eq_of_toNat_eq
    change clampEd25519Nat 0 = clampEd25519Nat 1
    unfold clampEd25519Nat
    have h1Mod : 1 % (2 ^ 254) = 1 := Nat.mod_eq_of_lt (by decide)
    rw [h1Mod]
  have h0Ne1 : (0#256 : BitVec 256) ≠ 1#256 := by decide
  exact ⟨x1, x2, hAllWrap, hx1Ge, hx2Ge, hx1NeX2, hRedEq,
    fun hInj => h0Ne1 (hInj hClamp01),
    fun hInj => hx1NeX2 (hInj hRedEq),
    fun hInj => h0Ne1 (hInj (congrArg reduceEd25519Order hClamp01))⟩

#tooth_pair
  Qsag.slip0010_ed25519_clamped_canonical_nonzero
  vs
  Qsag.tooth_ed25519_clamped_wraps_mod_order_non_injective


/-- `#tooth` Carmichael `561` passes `2^560 ≡ 1 (mod 561)` yet `checkPrattStep` deterministically rejects it. -/
theorem tooth_carmichael_561_passes_fermat_but_fails_pratt :
    ∃ c : PrattCert, c.n = 561 ∧ lucasPowMod 384 c.g (c.n - 1) c.n = 1 ∧
      checkPrattStep [2, 3, 5, 7] c = false ∧ ¬ IsPrimeMod c.n := by
  refine ⟨⟨561, 2, [(2, 4), (5, 1), (7, 1)]⟩, rfl, by decide +kernel, by decide +kernel, fun hPrime => ?_⟩
  dsimp only at hPrime; rcases hPrime.2 3 ⟨187, by decide⟩ with h1 | h561 <;> omega

#tooth_pair Qsag.checkPrattStep_sound vs Qsag.tooth_carmichael_561_passes_fermat_but_fails_pratt


def bls381Torsion3Point : SwPoint := some (0, 2)

/-- `#tooth` `BLS12-381` 3-torsion point `(0, 2)` lies on `y^2 = x^3 + 4` yet fails `[r_bls381]P = O`. -/
theorem tooth_bls381_torsion3_onCurve_but_off_subgroup :
    ∃ P : SwPoint, bls381Curve.onCurve P = true ∧
      isProjIdentity p_bls381 (rcbSmul p_bls381 12 (toRcbProj P) 3) = true ∧
      isProjIdentity p_bls381 (rcbSmul p_bls381 12 (toRcbProj P) r_bls381) = false :=
  ⟨bls381Torsion3Point, by decide +kernel, by decide +kernel, by decide +kernel⟩

#tooth_pair Qsag.bls381G1_onCurve_and_prime_subgroup_order vs Qsag.tooth_bls381_torsion3_onCurve_but_off_subgroup


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
  ⟨qZ, pSq, 2, by decide, by decide, by decide⟩

/-- The `Z`-weight cannot be lowered below `deg P`: with weight `1` the bound fails. -/
theorem tooth_deg_evalAffineLine_weight :
    ∃ (Q : Poly3 Goldilocks) (P : UPoly Goldilocks), P.natDeg ≤ 2 ∧
      ¬ (Q.evalAffineLine (g 3) (g 5) P).natDeg ≤ Q.deg11d 1 :=
  ⟨qZ, pSq, by decide, by decide⟩

/-- Taylor's formula on a concrete cubic: `p = 1 + 2X + 3X² + 4X³` at `b = 5` has first
    Hasse derivative `2 + 6·5 + 12·25 = 332`. -/
theorem taylor_cubic_example :
    coeffAt ((taylorShift (g 5)).toFun (ofList [g 1, g 2, g 3, g 4])).coeffs 1 = g 332 ∧
      (hasse 1 (ofList [g 1, g 2, g 3, g 4])).coeffs = [g 2, g 6, g 12] := by
  decide

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
  ⟨2, matA, matB, by decide +kernel, by decide +kernel, by decide +kernel, det_matMul 2 matA matB⟩

theorem tooth_det_not_entrywise_mul :
    ∃ (k : Nat) (A B : Nat → Nat → Goldilocks),
      det k (fun i j => mul (A i j) (B i j)) ≠ mul (det k A) (det k B) :=
  ⟨2, idMat, fun _ _ => one, by decide +kernel⟩

theorem inhabited_degFn_det_weighted_le :
    ∃ (M : Nat → Nat → UPoly Goldilocks),
      DegFn (UPoly.natDeg (R := Goldilocks)) ∧
      UPoly.natDeg (one : UPoly Goldilocks) = 0 ∧
      (∀ i, i < 2 → ∀ j, j < 2 → M i j ≠ zero → UPoly.natDeg (M i j) + j ≤ 1 + i) ∧
      det 2 M ≠ zero := by
  let M : Nat → Nat → UPoly Goldilocks
    | 0, 0 => UPoly.X | 0, 1 => one | 1, 0 => zero | 1, 1 => UPoly.X | _, _ => zero
  refine ⟨M, UPoly.degFn_natDeg, by decide +kernel, ?_, by decide +kernel⟩
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

/-- Mutation-sensitivity witness: the Carmichael number `561 = 3 · 11 · 17` passes the naive
    base-2 Fermat pseudoprime test `2^560 ≡ 1 (mod 561)`, yet `checkPocklingtonStep` rejects it
    because `gcd(2^(560 / 17) - 1, 561) ≠ 1`. -/
theorem tooth_carmichael_561_rejected_by_pocklington :
    ∃ (chain : List PocklingtonStep) (target : Nat),
      powModFuel 256 2 (target - 1) target = 1 ∧
      verifyPrimeCert chain target = false ∧
      ¬ Weierstrass.IsPrime target := by
  refine ⟨[⟨3, 2, [(2, 1)]⟩, ⟨11, 2, [(2, 1), (5, 1)]⟩, ⟨561, 2, [(17, 1), (11, 1)]⟩],
    561, by decide +kernel, by decide +kernel, fun ⟨_, hdiv⟩ => ?_⟩
  rcases hdiv 3 ⟨187, by decide⟩ with h1 | h561 <;> omega

theorem inhabited_verifyPrimeCert :
    ∃ (chain : List PocklingtonStep) (target : Nat),
      verifyPrimeCert chain target = true ∧ Weierstrass.IsPrime target :=
  ⟨[⟨3, 2, [(2, 1)]⟩], 3, by decide +kernel,
    verifyPrimeCert_sound (chain := [⟨3, 2, [(2, 1)]⟩]) (by decide +kernel)⟩

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


namespace GoldilocksField.GoldilocksExt4
/-- **`#tooth` Zero-Element Inversion Boundary (`tooth_ext4_zero_has_no_inverse`)**. -/
theorem tooth_ext4_zero_has_no_inverse : zero * zero⁻¹ ≠ one := by
  intro hEq
  have hZero : zero * zero⁻¹ = zero := LawfulCommRing.zero_mul (zero⁻¹)
  rw [hZero] at hEq; exact absurd hEq (by decide)


end GoldilocksField.GoldilocksExt4
/-! ## 4. Inhabitedness Witnesses & `#tooth_pair` / `#verify_constructive` Assurance Gates -/

theorem witness_lucas_bls_goldilocks :
    ∃ (N g : Nat) (facs : List (Nat × Nat)),
      N - 1 < 2 ^ 64 ∧ (∀ qe ∈ facs, IsPrimeNat qe.1) ∧ checkLucasBlsCert N g facs = true :=
  ⟨Goldilocks.p, 7, goldilocksTotientFactors, by decide,
   goldilocksTotientFactors_all_prime, goldilocks_lucas_cert_valid⟩

theorem witness_goldilocks_nonzero_element :
    ∃ x : Goldilocks, x ≠ Goldilocks.zero ∧ Goldilocks.inv x ≠ Goldilocks.zero :=
  ⟨⟨7, by decide⟩, by decide, by decide⟩

theorem witness_goldilocks_bezout_nonzero :
    ∃ x : Goldilocks, x ≠ Goldilocks.zero ∧ Goldilocks.invBezout x ≠ Goldilocks.zero :=
  ⟨⟨7, by decide⟩, by decide, by rw [goldilocks_invBezout_eq_inv]; decide⟩

theorem witness_ext4_nontrivial_element :
    ∃ z : GoldilocksField.GoldilocksExt4, z ≠ GoldilocksField.GoldilocksExt4.zero ∧
      z⁻¹ ≠ GoldilocksField.GoldilocksExt4.zero :=
  ⟨⟨⟨⟨3, by decide⟩, ⟨0, by decide⟩⟩, ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩⟩, by decide, by decide⟩

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
  Qsag.GoldilocksField.GoldilocksExt4.ext4_mul_inv_cancel
  Qsag.GoldilocksField.GoldilocksExt4.towerToPoly_mul_hom

#verify_inhabited Qsag.checkLucasBlsCert_sound Qsag.witness_lucas_bls_goldilocks
#verify_inhabited Qsag.goldilocks_universal_mul_inv_cancel Qsag.witness_goldilocks_nonzero_element
#verify_inhabited Qsag.goldilocks_mul_invBezout_cancel Qsag.witness_goldilocks_bezout_nonzero
#verify_inhabited Qsag.GoldilocksField.GoldilocksExt4.ext4_mul_inv_cancel Qsag.witness_ext4_nontrivial_element

#tooth_pair Qsag.checkLucasBlsCert_sound vs Qsag.tooth_proth16_65281_not_prime
#tooth_pair Qsag.checkLucasBlsCert_sound vs Qsag.tooth_carmichael_561_rejected
#tooth_pair Qsag.goldilocks_universal_mul_inv_cancel vs Qsag.tooth_goldilocks_zero_has_no_inverse
#tooth_pair Qsag.goldilocks_quadExtMulMod_no_zero_divisors vs Qsag.tooth_mod29_seven_residue_zero_divisor
#tooth_pair Qsag.v_pow4_sub_seven_irreducible vs Qsag.tooth_monic_quad_factor_zero_at_origin
#tooth_pair Qsag.GoldilocksField.GoldilocksExt4.ext4_mul_inv_cancel vs Qsag.GoldilocksField.GoldilocksExt4.tooth_ext4_zero_has_no_inverse

/-- A limb equal to `p` (non-canonical encoding of `0`) is rejected. -/
theorem decodeExt4Bytes32_rejects_noncanonical_limb :
    decodeExt4Bytes32
      ([1, 0, 0, 0, 255, 255, 255, 255] ++ List.replicate 24 (0 : UInt8)) = none ∧
    decodeExt4Bytes32 (List.replicate 32 (0 : UInt8)) = some GoldilocksExt4.zero := by
  decide

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

private theorem filter_eq_nil_of_all_false {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (∀ x ∈ xs, p x = false) → xs.filter p = []
  | [], _ => rfl
  | x :: xs, h => by
    simp [List.filter, h x (.head _), filter_eq_nil_of_all_false p xs (fun y hy => h y (.tail _ hy))]

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
    (by intro p hp; simp at hp; subst hp; decide)
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

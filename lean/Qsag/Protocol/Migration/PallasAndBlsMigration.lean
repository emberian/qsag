module
/-
# Qsag.Protocol.Migration.PallasAndBlsMigration — Zcash Orchard (`Pallas` / `RedPallas`) & Ethereum Beacon (`BLS12-381`) PQ Ownership Migration

Items 1–3 are defined and proved in `Qsag.Math.EllipticCurves` and audited here; items 4–5 are this module.
1. Exact `Pallas` (`y^2 = x^3 + 5`, `p_pallas`, `q_pallas`, `orchardSpendAuthG`) and `BLS12-381` (`y^2 = x^3 + 4`, `p_bls381`, `r_bls381`, `bls381G1`) parameters matching `pallas.rs` and `bls12_381.rs`.
2. Constructive Lucas–Pratt primality verifier (`checkPrattStep_sound`, `checkPrattDAG_sound`) via binary `lucasPowMod`, certifying `p_pallas`, `q_pallas`, `r_bls381`, `p_bls381`, paired with Carmichael `561` (`#tooth`).
3. The projective RCB addition program (`rcbAdd`, `rcbSmul`), curve membership, and kernel evaluations of `rcbSmul` at the prime scalar moduli (output is a projective identity for `SpendAuthG` at `q_pallas` and for `G_1` at `r_bls381`; the bridge from `rcbSmul` to scalar multiplication in the curve group is not proved), paired with the `BLS12-381` 3-torsion point `(0, 2)` (`#tooth`).
4. 3-party ZKBoo 2-of-3 discrete-log extraction (`zkboo_two_challenge_extraction_sound`) and Zcash Orchard RedPallas rerandomized `rk = [ask + alpha] SpendAuthG` binding extraction & unlinkability (`#tooth`).
-/

public import Qsag.Math.EllipticCurves
public import Qsag.Tactic.AssuranceKit

public section
namespace Qsag
set_option autoImplicit false
set_option exponentiation.threshold 512

/-! ## 4. 3-Party ZKBoo 2-of-3 Knowledge Extraction & RedPallas Rerandomized `rk` Unlinkability -/

structure PrimeSubgroup (C : SwCurve) (G : SwPoint) (ord : Nat) where
  add : SwPoint → SwPoint → SwPoint
  smul : Nat → SwPoint
  p_prime : IsPrimeMod C.p
  ord_prime : IsPrimeMod ord
  gen_onCurve : C.onCurve G = true
  smul_onCurve : ∀ k, C.onCurve (smul k) = true
  add_none_left : ∀ P, add none P = P
  smul_add : ∀ a b, smul (a + b) = add (smul a) (smul b)
  smul_ord : smul ord = none
  exact_ord : ∀ k, 0 < k → k < ord → smul k ≠ none

/-- **Bridge from `Weierstrass.Curve.PrimeOrderGroup` to `PrimeSubgroup` (`PrimeSubgroup.ofPrimeOrderGroup`)**:
    Ties `PrimeSubgroup`'s `add` and `smul` directly to short-Weierstrass chord-tangent curve
    arithmetic `C.add` and `C.smul · G` on `SwCurve`, discharging `p_prime`, `ord_prime`,
    `gen_onCurve`, `smul_onCurve`, `add_none_left`, `smul_add`, `smul_ord`, and `exact_ord`. -/
def PrimeSubgroup.ofPrimeOrderGroup {C : SwCurve} {G : SwPoint} {ord : Nat}
    (h : C.PrimeOrderGroup G ord) : PrimeSubgroup C G ord where
  add := C.add
  smul k := C.smul k G
  p_prime := h.p_prime
  ord_prime := h.n_prime
  gen_onCurve := by
    have h1 : C.OnCurve (C.smul 1 G) := h.onCurve 1
    rw [Weierstrass.Curve.smul_one] at h1
    exact SwCurve.onCurve_of_OnCurve h1
  smul_onCurve k := SwCurve.onCurve_of_OnCurve (h.onCurve k)
  add_none_left := Weierstrass.Curve.add_none_left C
  smul_add := h.smul_add
  smul_ord := h.order
  exact_ord := h.exact

/-- **Unconditional Concrete `SwCurve` Inhabitant (`secp7Mod43_primeSubgroup`)**:
    Instantiates `PrimeSubgroup` with actual affine chord-tangent curve arithmetic on
    `y² = x³ + 7` over `ℤ/43` (`G = (2, 12)` of prime order `31`). -/
def secp7Mod43_primeSubgroup :
    PrimeSubgroup Weierstrass.secp7Mod43 Weierstrass.secp7Mod43G 31 :=
  PrimeSubgroup.ofPrimeOrderGroup Weierstrass.secp7Mod43_group

theorem secp7Mod43_primeSubgroup_smul_eq (k : Nat) :
    secp7Mod43_primeSubgroup.smul k = Weierstrass.secp7Mod43.smul k Weierstrass.secp7Mod43G := by
  rfl

/-- **`secp256k1` `PrimeSubgroup` on `SwCurve` (`secp256k1_primeSubgroup`)**:
    Instantiates `PrimeSubgroup` at `SECP256K1_ORDER_N` from `Weierstrass.Secp256k1GroupLaws`
    (whose field and order primality are discharged by Pocklington certificates). -/
def secp256k1_primeSubgroup (h : Weierstrass.Secp256k1GroupLaws) :
    PrimeSubgroup Weierstrass.secp256k1Curve Weierstrass.secp256k1G SECP256K1_ORDER_N :=
  PrimeSubgroup.ofPrimeOrderGroup h

/-- **`Pallas` (`Orchard SpendAuthG`) `PrimeOrderGroup` Constructor (`pallasGroupLaws_of_group_facts`)**:
    Discharges `p_pallas` and `q_pallas` primality via Lucas–Pratt certificates (`p_pallas_isPrime`,
    `q_pallas_isPrime`) and oddness via `pallas_and_bls381_limbs_and_bit_bounds`, leaving only the
    four affine chord-tangent subgroup closure laws. -/
theorem pallasGroupLaws_of_group_facts
    (onCurve : ∀ k, pallasCurve.OnCurve (pallasCurve.smul k orchardSpendAuthG))
    (smul_add : ∀ a b, pallasCurve.smul (a + b) orchardSpendAuthG =
      pallasCurve.add (pallasCurve.smul a orchardSpendAuthG) (pallasCurve.smul b orchardSpendAuthG))
    (order : pallasCurve.smul q_pallas orchardSpendAuthG = none)
    (exact : ∀ k, 0 < k → k < q_pallas → pallasCurve.smul k orchardSpendAuthG ≠ none) :
    pallasCurve.PrimeOrderGroup orchardSpendAuthG q_pallas where
  p_prime := by rw [pallasCurve_p]; exact p_pallas_isPrime
  p_odd := by rw [pallasCurve_p]; exact pallas_and_bls381_limbs_and_bit_bounds.2.2.2.2.2.2.1
  n_prime := q_pallas_isPrime
  n_odd := pallas_and_bls381_limbs_and_bit_bounds.2.2.2.2.2.2.2.2.2.1
  onCurve := onCurve
  smul_add := smul_add
  order := order
  exact := exact

/-- **`Pallas` `PrimeSubgroup` on `SwCurve` (`pallas_primeSubgroup`)**. -/
def pallas_primeSubgroup (h : pallasCurve.PrimeOrderGroup orchardSpendAuthG q_pallas) :
    PrimeSubgroup pallasCurve orchardSpendAuthG q_pallas :=
  PrimeSubgroup.ofPrimeOrderGroup h

/-- **`BLS12-381` (`G_1`) `PrimeOrderGroup` Constructor (`bls381GroupLaws_of_group_facts`)**:
    Discharges `p_bls381` and `r_bls381` primality via Lucas–Pratt certificates (`p_bls381_isPrime`,
    `r_bls381_isPrime`) and oddness via `pallas_and_bls381_limbs_and_bit_bounds`, leaving only the
    four affine chord-tangent subgroup closure laws. -/
theorem bls381GroupLaws_of_group_facts
    (onCurve : ∀ k, bls381Curve.OnCurve (bls381Curve.smul k bls381G1))
    (smul_add : ∀ a b, bls381Curve.smul (a + b) bls381G1 =
      bls381Curve.add (bls381Curve.smul a bls381G1) (bls381Curve.smul b bls381G1))
    (order : bls381Curve.smul r_bls381 bls381G1 = none)
    (exact : ∀ k, 0 < k → k < r_bls381 → bls381Curve.smul k bls381G1 ≠ none) :
    bls381Curve.PrimeOrderGroup bls381G1 r_bls381 where
  p_prime := by rw [bls381Curve_p]; exact p_bls381_isPrime
  p_odd := by
    rw [bls381Curve_p]
    have h4 := pallas_and_bls381_limbs_and_bit_bounds.2.2.2.2.2.2.2.2.2.2.2.2.1
    omega
  n_prime := r_bls381_isPrime
  n_odd := pallas_and_bls381_limbs_and_bit_bounds.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  onCurve := onCurve
  smul_add := smul_add
  order := order
  exact := exact

/-- **`BLS12-381` `PrimeSubgroup` on `SwCurve` (`bls381_primeSubgroup`)**. -/
def bls381_primeSubgroup (h : bls381Curve.PrimeOrderGroup bls381G1 r_bls381) :
    PrimeSubgroup bls381Curve bls381G1 r_bls381 :=
  PrimeSubgroup.ofPrimeOrderGroup h

theorem PrimeSubgroup.smul_injective {C : SwCurve} {G : SwPoint} {ord : Nat}
    (grp : PrimeSubgroup C G ord) {a b : Nat} (ha : a < ord) (hb : b < ord) (hEq : grp.smul a = grp.smul b) :
    a = b := by
  have hNeLt : ∀ {u v : Nat}, u < v → v < ord → grp.smul u ≠ grp.smul v := fun {u v} huv hv heq => by
    have h1 : grp.smul ((ord - u) + v) = none := by
      rw [grp.smul_add, ← heq, ← grp.smul_add, show (ord - u) + u = ord by omega, grp.smul_ord]
    have h2 : grp.smul ((ord - u) + v) = grp.smul (v - u) := by
      rw [show (ord - u) + v = ord + (v - u) by omega, grp.smul_add, grp.smul_ord, grp.add_none_left]
    exact grp.exact_ord (v - u) (by omega) (by omega) (h2.symm.trans h1)
  rcases Nat.lt_trichotomy a b with hlt | heq | hgt
  · exact False.elim (hNeLt hlt hb hEq)
  · exact heq
  · exact False.elim (hNeLt hgt ha hEq.symm)

/-- Every canonical nonzero scalar `0 < sk < ord` in a `PrimeSubgroup C G ord` produces a finite
    canonical affine curve key `CanonicalSwPk C` (`x < C.p`, `y < C.p`, `C.onCurve = true`). -/
def PrimeSubgroup.smulCanonicalPk {C : SwCurve} {G : SwPoint} {ord : Nat}
    (grp : PrimeSubgroup C G ord) (sk : Nat) (hPos : 0 < sk) (hLt : sk < ord) :
    CanonicalSwPk C :=
  match hPt : grp.smul sk with
  | none => False.elim (grp.exact_ord sk hPos hLt hPt)
  | some (x, y) => ⟨x, y, hPt ▸ grp.smul_onCurve sk⟩

theorem PrimeSubgroup.smulCanonicalPk_toSwPoint {C : SwCurve} {G : SwPoint} {ord : Nat}
    (grp : PrimeSubgroup C G ord) (sk : Nat) (hPos : 0 < sk) (hLt : sk < ord) :
    (grp.smulCanonicalPk sk hPos hLt).toSwPoint = grp.smul sk := by
  unfold PrimeSubgroup.smulCanonicalPk
  split
  · next hNone => exact False.elim (grp.exact_ord sk hPos hLt hNone)
  · next x y hSome => 
                        exact Eq.trans (CanonicalSwPk.toSwPoint_eq _) hSome.symm

theorem PrimeSubgroup.smulCanonicalPk_injective {C : SwCurve} {G : SwPoint} {ord s₁ s₂ : Nat}
    (grp : PrimeSubgroup C G ord) (hp₁ : 0 < s₁) (hl₁ : s₁ < ord)
    (hp₂ : 0 < s₂) (hl₂ : s₂ < ord)
    (hEq : grp.smulCanonicalPk s₁ hp₁ hl₁ = grp.smulCanonicalPk s₂ hp₂ hl₂) : s₁ = s₂ := by
  have hPt : grp.smul s₁ = grp.smul s₂ := by
    rw [← grp.smulCanonicalPk_toSwPoint s₁ hp₁ hl₁, ← grp.smulCanonicalPk_toSwPoint s₂ hp₂ hl₂, hEq]
  exact grp.smul_injective hl₁ hl₂ hPt

def zkbooReconstructScalar (ord s0 s1 s2 : Nat) : Nat := (s0 + s1 + s2) % ord

theorem zkbooReconstructScalar_eq (ord s0 s1 s2 : Nat) :
    zkbooReconstructScalar ord s0 s1 s2 = (s0 + s1 + s2) % ord := by
  rfl
def zkbooOpenedPair (shares : Fin 3 → Nat) (e : Fin 3) : Nat × Nat :=
  (shares e, shares ⟨(e.val + 1) % 3, Nat.mod_lt _ (by decide)⟩)

def extractThreeShares (e1 e2 : Fin 3) (p1 p2 : Nat × Nat) : Nat × Nat × Nat :=
  match e1.val, e2.val with
  | 0, 1 => (p1.1, p1.2, p2.2) | 0, _ => (p1.1, p1.2, p2.1)
  | 1, 0 => (p2.1, p1.1, p1.2) | 1, _ => (p2.2, p1.1, p1.2)
  | _, 0 => (p1.2, p2.2, p1.1) | _, _ => (p1.2, p2.1, p1.1)

theorem extractThreeShares_zero_one (p1 p2 : Nat × Nat) :
    extractThreeShares 0 1 p1 p2 = (p1.1, p1.2, p2.2) := by
  rfl

theorem extractThreeShares_complete (shares : Fin 3 → Nat) (e1 e2 : Fin 3) (hNe : e1 ≠ e2) :
    extractThreeShares e1 e2 (zkbooOpenedPair shares e1) (zkbooOpenedPair shares e2) =
      (shares 0, shares 1, shares 2) := by
  rcases e1 with ⟨v1, hv1⟩; rcases e2 with ⟨v2, hv2⟩
  have hNeVal : v1 ≠ v2 := fun h => hNe (Fin.ext h)
  have mk3 : ∀ {i0 i1 i2 : Fin 3}, i0.val = 0 → i1.val = 1 → i2.val = 2 →
      (shares i0, shares i1, shares i2) = (shares 0, shares 1, shares 2) := fun h0 h1 h2 =>
    Prod.ext (congrArg shares (Fin.ext h0))
      (Prod.ext (congrArg shares (Fin.ext h1)) (congrArg shares (Fin.ext h2)))
  dsimp only [extractThreeShares, zkbooOpenedPair]
  match v1, hv1, v2, hv2 with
  | 0, _, 0, _ => exact False.elim (hNeVal rfl)
  | 0, _, 1, _ => exact mk3 rfl rfl rfl | 0, _, 2, _ => exact mk3 rfl rfl rfl
  | 1, _, 0, _ => exact mk3 rfl rfl rfl | 1, _, 1, _ => exact False.elim (hNeVal rfl)
  | 1, _, 2, _ => exact mk3 rfl rfl rfl | 2, _, 0, _ => exact mk3 rfl rfl rfl
  | 2, _, 1, _ => exact mk3 rfl rfl rfl | 2, _, 2, _ => exact False.elim (hNeVal rfl)
  | _ + 3, hv, _, _ => omega | 0, _, _ + 3, hv => omega | 1, _, _ + 3, hv => omega | 2, _, _ + 3, hv => omega

def ZkBooDlogCommitted {C : SwCurve} {G : SwPoint} {ord : Nat}
    (grp : PrimeSubgroup C G ord) (pk : SwPoint) (shares : Fin 3 → Nat) : Prop :=
  let sk := zkbooReconstructScalar ord (shares 0) (shares 1) (shares 2)
  0 < sk ∧ sk < ord ∧ grp.smul sk = pk

theorem zkboo_two_challenge_extraction_sound {C : SwCurve} {G pk : SwPoint} {ord : Nat}
    (grp : PrimeSubgroup C G ord) (shares : Fin 3 → Nat) (e1 e2 : Fin 3) (hNe : e1 ≠ e2)
    (hValid : ZkBooDlogCommitted grp pk shares) :
    let (s0, s1, s2) := extractThreeShares e1 e2 (zkbooOpenedPair shares e1) (zkbooOpenedPair shares e2)
    let sk := zkbooReconstructScalar ord s0 s1 s2
    0 < sk ∧ sk < ord ∧ grp.smul sk = pk ∧ (∀ sk' : Nat, sk' < ord → grp.smul sk' = pk → sk' = sk) := by
  rw [extractThreeShares_complete shares e1 e2 hNe]
  dsimp only [ZkBooDlogCommitted] at hValid ⊢; obtain ⟨hPos, hLt, hSmul⟩ := hValid
  exact ⟨hPos, hLt, hSmul, fun sk' hLt' hSmul' => grp.smul_injective hLt' hLt (hSmul'.trans hSmul.symm)⟩

/-- `#tooth` A single ZKBoo challenge `(s0, s1)` information-theoretically hides `sk`. -/
theorem tooth_zkboo_single_challenge_information_theoretically_hides_witness
    {ord s0 s1 skA skB : Nat} (hA : skA < ord) (hB : skB < ord) (hNe : skA ≠ skB) :
    ∃ s2A s2B : Nat, s2A < ord ∧ s2B < ord ∧ s2A ≠ s2B ∧
      zkbooReconstructScalar ord s0 s1 s2A = skA ∧ zkbooReconstructScalar ord s0 s1 s2B = skB := by
  have hOrdPos : 0 < ord := by omega
  let sum01 := (s0 + s1) % ord
  have hSumLt : sum01 < ord := Nat.mod_lt _ hOrdPos
  have hSolve : ∀ {sk : Nat}, sk < ord → zkbooReconstructScalar ord s0 s1 ((sk + ord - sum01) % ord) = sk :=
    fun {sk} hSk => by
      unfold zkbooReconstructScalar
      rw [Nat.add_mod_mod, ← Nat.mod_add_mod,
          show (s0 + s1) % ord + (sk + ord - sum01) = ord + sk by dsimp only [sum01]; omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt hSk]
  have hRecA := hSolve hA; have hRecB := hSolve hB
  refine ⟨(skA + ord - sum01) % ord, (skB + ord - sum01) % ord,
    Nat.mod_lt _ hOrdPos, Nat.mod_lt _ hOrdPos, fun hEq => ?_, hRecA, hRecB⟩
  rw [hEq, hRecB] at hRecA; exact hNe hRecA.symm

#tooth_pair Qsag.zkboo_two_challenge_extraction_sound vs
  Qsag.tooth_zkboo_single_challenge_information_theoretically_hides_witness

@[expose] def redpallasEffectiveScalar (ord ask alpha : Nat) : Nat := (ask + alpha) % ord
@[expose] def redpallasSolveAlpha (ord rsk ask : Nat) : Nat := (rsk + ord - (ask % ord)) % ord

theorem primeSubgroup_smul_add_mod {C : SwCurve} {G : SwPoint} {ord : Nat}
    (grp : PrimeSubgroup C G ord) {ask alpha : Nat} (hAsk : ask < ord) (hAlpha : alpha < ord) :
    grp.smul (redpallasEffectiveScalar ord ask alpha) = grp.add (grp.smul ask) (grp.smul alpha) := by
  unfold redpallasEffectiveScalar; rw [← grp.smul_add]
  if hLt : ask + alpha < ord then rw [Nat.mod_eq_of_lt hLt]
  else
    have hMod : (ask + alpha) % ord = ask + alpha - ord := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hMod]
    conv => rhs; rw [show ask + alpha = ord + (ask + alpha - ord) by omega, grp.smul_add, grp.smul_ord, grp.add_none_left]

theorem orchard_redpallas_rerandomized_extraction_sound {C : SwCurve} {G rk : SwPoint}
    (grp : PrimeSubgroup C G q_pallas) (askShares alphaShares : Fin 3 → Nat) (e1 e2 : Fin 3) (hNe : e1 ≠ e2)
    (hAskRange : 0 < zkbooReconstructScalar q_pallas (askShares 0) (askShares 1) (askShares 2) ∧
                 zkbooReconstructScalar q_pallas (askShares 0) (askShares 1) (askShares 2) < q_pallas)
    (hAlphaRange : zkbooReconstructScalar q_pallas (alphaShares 0) (alphaShares 1) (alphaShares 2) < q_pallas)
    (hRskPos : 0 < redpallasEffectiveScalar q_pallas
      (zkbooReconstructScalar q_pallas (askShares 0) (askShares 1) (askShares 2))
      (zkbooReconstructScalar q_pallas (alphaShares 0) (alphaShares 1) (alphaShares 2)))
    (hCurve : grp.smul (redpallasEffectiveScalar q_pallas
      (zkbooReconstructScalar q_pallas (askShares 0) (askShares 1) (askShares 2))
      (zkbooReconstructScalar q_pallas (alphaShares 0) (alphaShares 1) (alphaShares 2))) = rk) :
    let (a0, a1, a2) := extractThreeShares e1 e2 (zkbooOpenedPair askShares e1) (zkbooOpenedPair askShares e2)
    let (r0, r1, r2) := extractThreeShares e1 e2 (zkbooOpenedPair alphaShares e1) (zkbooOpenedPair alphaShares e2)
    let ask := zkbooReconstructScalar q_pallas a0 a1 a2
    let alpha := zkbooReconstructScalar q_pallas r0 r1 r2
    let rsk := redpallasEffectiveScalar q_pallas ask alpha
    0 < ask ∧ ask < q_pallas ∧ alpha < q_pallas ∧ 0 < rsk ∧ rsk < q_pallas ∧
    grp.add (grp.smul ask) (grp.smul alpha) = rk ∧
    (∀ ask' alpha' : Nat, ask' < q_pallas → alpha' < q_pallas →
      grp.add (grp.smul ask') (grp.smul alpha') = rk → redpallasEffectiveScalar q_pallas ask' alpha' = rsk) := by
  rw [extractThreeShares_complete askShares e1 e2 hNe, extractThreeShares_complete alphaShares e1 e2 hNe]
  dsimp only; have hQPos : 0 < q_pallas := by decide
  have hRskLt := Nat.mod_lt (zkbooReconstructScalar q_pallas (askShares 0) (askShares 1) (askShares 2) +
    zkbooReconstructScalar q_pallas (alphaShares 0) (alphaShares 1) (alphaShares 2)) hQPos
  have hHom := primeSubgroup_smul_add_mod grp hAskRange.2 hAlphaRange
  refine ⟨hAskRange.1, hAskRange.2, hAlphaRange, hRskPos, hRskLt, hHom.symm.trans hCurve, ?_⟩
  intro ask' alpha' hAsk' hAlpha' hRk'
  exact grp.smul_injective (Nat.mod_lt _ hQPos) hRskLt
    (((primeSubgroup_smul_add_mod grp hAsk' hAlpha').trans hRk').trans hCurve.symm)

theorem orchard_redpallas_rk_perfect_unlinkability {ord rsk ask : Nat} (hRsk : rsk < ord) (hAsk : ask < ord) :
    let alpha := redpallasSolveAlpha ord rsk ask
    alpha < ord ∧ redpallasEffectiveScalar ord ask alpha = rsk ∧
    (∀ alpha' : Nat, alpha' < ord → redpallasEffectiveScalar ord ask alpha' = rsk → alpha' = alpha) := by
  have hOrdPos : 0 < ord := by omega
  dsimp only; have hAskMod : ask % ord = ask := Nat.mod_eq_of_lt hAsk
  have hHit : redpallasEffectiveScalar ord ask (redpallasSolveAlpha ord rsk ask) = rsk := by
    unfold redpallasEffectiveScalar redpallasSolveAlpha
    rw [hAskMod, Nat.add_mod_mod, show ask + (rsk + ord - ask) = ord + rsk by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt hRsk]
  refine ⟨Nat.mod_lt _ hOrdPos, hHit, fun alpha' hAlpha' hEq' => ?_⟩
  unfold redpallasEffectiveScalar at hEq'; unfold redpallasSolveAlpha; rw [hAskMod, ← hEq']
  if hSumLt : ask + alpha' < ord then
    rw [Nat.mod_eq_of_lt hSumLt, show ask + alpha' + ord - ask = ord + alpha' by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt hAlpha']
  else
    have hModSub : (ask + alpha') % ord = ask + alpha' - ord := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hModSub, show ask + alpha' - ord + ord - ask = alpha' by omega, Nat.mod_eq_of_lt hAlpha']

/-- `#tooth` Setting `alpha = 0` collapses RedPallas unlinkability (`redpallasEffectiveScalar q_pallas ask 0 = ask`). -/
theorem tooth_redpallas_zero_alpha_links_ak :
    ∃ ask1 ask2 : Nat, 0 < ask1 ∧ ask1 < q_pallas ∧ 0 < ask2 ∧ ask2 < q_pallas ∧ ask1 ≠ ask2 ∧
      redpallasEffectiveScalar q_pallas ask1 0 ≠ redpallasEffectiveScalar q_pallas ask2 0 ∧
      redpallasSolveAlpha q_pallas ask1 ask2 ≠ 0 :=
  ⟨1, 2, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

#tooth_pair Qsag.orchard_redpallas_rk_perfect_unlinkability vs Qsag.tooth_redpallas_zero_alpha_links_ak

/-! ## 5. Unified Active Field Checks (`35`), Shipped Bit-Check Numerator (`63`) & Canonical Scalar Guards -/

def migrationSecp256k1P : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f
def migrationSecp256k1N : Nat := 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
def migrationEd25519P   : Nat := 2 ^ 255 - 19
def migrationEd25519L   : Nat := 2 ^ 252 + 27742317777372353535851937790883648493
def migrationGoldilocksP : Nat := 0xffffffff00000001

def ActiveFieldCheckBound (num k modulus : Nat) : Prop :=
  num * 2 ^ k < modulus - 1

/-- Synchronized active field-check soundness across all five migration domains (`outer_mpc.rs:40`):
`secp256k1` (`< 2^-250`), `Ed25519` and `BLS12-381` (`< 2^-249`), `Pallas` (`< 2^-248`), and
Goldilocks `GF(p^3)` (`< 2^-186`). -/
theorem migration_active_field_check_exact_bounds :
    ActiveFieldCheckBound 35 250 migrationSecp256k1P ∧
    ActiveFieldCheckBound 35 249 migrationEd25519P ∧
    ActiveFieldCheckBound 35 249 p_bls381 ∧
    ActiveFieldCheckBound 35 249 r_bls381 ∧
    ActiveFieldCheckBound 35 248 p_pallas ∧
    ActiveFieldCheckBound 35 248 q_pallas ∧
    ActiveFieldCheckBound 35 186 (migrationGoldilocksP ^ 3) := by
  unfold ActiveFieldCheckBound
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- `#tooth` On `Pallas` (`p_pallas, q_pallas ≈ 2^254 + 2^125.1`), `35 / (p - 1) ≈ 2^-248.87`
exceeds `2^-249`, refuting a uniform `< 2^-249` active field-check claim across all curves. -/
theorem tooth_pallas_field_check_exceeds_two_neg_249 :
    ¬ (ActiveFieldCheckBound 35 249 p_pallas ∨ ActiveFieldCheckBound 35 249 q_pallas) := by
  unfold ActiveFieldCheckBound
  decide

#tooth_pair Qsag.migration_active_field_check_exact_bounds vs Qsag.tooth_pallas_field_check_exceeds_two_neg_249

def BitCheckInstancesBound (num instances k fieldSize : Nat) : Prop :=
  num ^ instances * 2 ^ k < (fieldSize - 1) ^ instances

/-- Shipped `BIT_CHECK_NUMERATOR = 63` (`outer_mpc.rs:33-49`): `7` degree-7 combiner roots +
`6 × 3` ternary sumcheck roots + `18 × 2` binary halving roots + `2` base check = `63`, with
exact union numerator `61 * (n - 1) + 2 * n < 63 * n` and two-instance error `< 2^-244`. -/
theorem migration_shipped_bit_check_numerator_63_sound (n : Nat) (hn : 2 ≤ n) :
    7 + 3 * 6 + 2 * 18 + 2 = 63 ∧
    61 * (n - 1) + 2 * n < 63 * n ∧
    BitCheckInstancesBound 63 2 244 (2 ^ 128) := by
  refine ⟨by decide, by omega, ?_⟩
  unfold BitCheckInstancesBound
  decide

/-- `#tooth` A single `GF(2^128)` bit-check instance at numerator `63` fails the `< 2^-123` bound. -/
theorem tooth_single_instance_bit_check_63_fails_pq128 :
    ¬ BitCheckInstancesBound 63 1 123 (2 ^ 128) := by
  unfold BitCheckInstancesBound
  decide

#tooth_pair Qsag.migration_shipped_bit_check_numerator_63_sound vs Qsag.tooth_single_instance_bit_check_63_fails_pq128

/-- Canonical `< ord` check on 256-bit witness scalars guarantees unique curve preimages across
all four legacy curves (`secp256k1`, `Ed25519`, `Pallas`, `BLS12-381`). -/
theorem canonical_legacy_scalar_unique {C : SwCurve} {G : SwPoint} {ord s₁ s₂ : Nat}
    (grp : PrimeSubgroup C G ord) (hs₁ : s₁ < ord) (hs₂ : s₂ < ord)
    (hPk : grp.smul s₁ = grp.smul s₂) : s₁ = s₂ :=
  grp.smul_injective hs₁ hs₂ hPk

/-- `#tooth` Every supported curve order satisfies `1 + ord < 2^256`, so omitting the canonical
`< ord` wire guard admits distinct 256-bit bit-vectors `1 ≠ 1 + ord` with identical curve point
`[1] G = [(1 + ord) mod ord] G` and distinct 256-bit nullifier preimage. -/
theorem tooth_unreduced_256bit_scalar_alias_all_four_curves
    {C : SwCurve} {G : SwPoint} {ord : Nat} (grp : PrimeSubgroup C G ord) (hOrd : 0 < ord) :
    ∃ s₁ s₂ : Nat,
      s₁ ≠ s₂ ∧ grp.smul (s₁ % ord) = grp.smul (s₂ % ord) ∧
      1 + migrationSecp256k1N < 2 ^ 256 ∧
      1 + migrationEd25519L < 2 ^ 256 ∧
      1 + q_pallas < 2 ^ 256 ∧
      1 + r_bls381 < 2 ^ 256 := by
  refine ⟨1, 1 + ord, by omega, ?_, by decide, by decide, by decide, by decide⟩
  exact congrArg grp.smul (Nat.add_mod_right 1 ord).symm

#tooth_pair Qsag.canonical_legacy_scalar_unique vs Qsag.tooth_unreduced_256bit_scalar_alias_all_four_curves

/-! ## 6. Constructive Axiom Audit (`#verify_constructive`) -/

#verify_constructive
  Qsag.PrimeSubgroup.smul_injective
  Qsag.bls381GroupLaws_of_group_facts
  Qsag.PrimeSubgroup.smulCanonicalPk_toSwPoint
  Qsag.PrimeSubgroup.smulCanonicalPk_injective
  Qsag.extractThreeShares_complete
  Qsag.zkboo_two_challenge_extraction_sound
  Qsag.tooth_zkboo_single_challenge_information_theoretically_hides_witness
  Qsag.primeSubgroup_smul_add_mod Qsag.orchard_redpallas_rerandomized_extraction_sound
  Qsag.orchard_redpallas_rk_perfect_unlinkability Qsag.tooth_redpallas_zero_alpha_links_ak
  Qsag.migration_active_field_check_exact_bounds Qsag.tooth_pallas_field_check_exceeds_two_neg_249
  Qsag.migration_shipped_bit_check_numerator_63_sound Qsag.tooth_single_instance_bit_check_63_fails_pq128
  Qsag.canonical_legacy_scalar_unique Qsag.tooth_unreduced_256bit_scalar_alias_all_four_curves

end Qsag

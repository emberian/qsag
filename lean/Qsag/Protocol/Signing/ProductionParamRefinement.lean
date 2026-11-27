module


public import Qsag.Protocol.Signing.HulsingFullOverlay
public import Qsag.Protocol.Signing.PorsFpSecurity
public import Qsag.Protocol.Signing.Fips205
public import Qsag.Oracle.Qrom
public import Qsag.Spec.IdealSign
import Qsag.Tactic.AssuranceKit

public section
attribute [-instance] Fin.instLinearOrderPackage
namespace Qsag
open scoped Qsag.Spec

set_option autoImplicit false
set_option exponentiation.threshold 2048

/-! ## §1. Canonical Production Parameter Profiles, Accounting & `RandomizedSigScheme` Refinement -/

/-- Production stateful `Jorts` (`Poseidon2`) parameter profile (`w = 4, ell1 = 128, h' = 16, d = 1`). -/
abbrev jortsProdParams : PqHashParams := jortsPoseidon2Params

/-- Production stateless `Baggy-TSW-128f` parameter profile (`w = 4, ell1 = 128, h' = 2, d = 16, k = 33, a = 6`). -/
abbrev baggyProdParams : PqHashParams := baggy128fParams

/-- Production stateless `Corduroy-Custody-128` parameter profile (`w = 4, ell1 = 128, h' = 4, d = 7, k = 33, a = 6`). -/
abbrev corduroyProdParams : PqHashParams := corduroyCustody128Params

/-- Official NIST FIPS 205 Category-1 `SLH-DSA-SHAKE-128s` profile (`7,856`B wire signature). -/
abbrev fips205SlhDsa128sParams : Fips205Params := slhDsaShake128s

/-- Official NIST FIPS 205 Category-1 `SLH-DSA-SHAKE-128f` profile (`17,088`B wire signature). -/
abbrev fips205SlhDsa128fParams : Fips205Params := slhDsaShake128f

/-- Exposed per-signature secret-preimage slot count (`FORS` leaves + `WOTS+C` chain steps). -/
@[expose] def prodPreCandidateBudget (params : PqHashParams) : Nat :=
  params.forsTrees + params.numLayers * (params.ell1 * (params.w - 1))

/-- Exact kernel-verified parameter validity, wire size, and query/target budgets for `jortsProdParams`. -/
theorem jortsProdParams_accounting :
    jortsProdParams.productionWellFormed = true ∧ jortsProdParams.statefulJorts = true ∧
    jortsProdParams.wireSigBytes = 4661 ∧
    prodPathTargetCount jortsProdParams (2 ^ 16) = 131474 ∧
    prodPreCandidateBudget jortsProdParams = 384 ∧
    prfSecPerSignBudget jortsProdParams = 8388608 ∧
    prfSecQueryBudget jortsProdParams (2 ^ 16) = 549764202496 := by
  refine ⟨jortsPoseidon2_productionWellFormed, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [jortsProdParams, jortsPoseidon2Params_eq]
  · rw [jortsProdParams, PqHashParams.wireSigBytes_eq, jortsPoseidon2Params_eq]; decide +kernel
  · rw [jortsProdParams, prodPathTargetCount_eq, jortsPoseidon2Params_eq]; decide +kernel
  · unfold prodPreCandidateBudget; rw [jortsProdParams, jortsPoseidon2Params_eq]; decide +kernel
  · unfold prfSecPerSignBudget; rw [jortsProdParams, jortsPoseidon2Params_eq]; decide +kernel
  · unfold prfSecQueryBudget prfSecPerSignBudget
    rw [jortsProdParams, jortsPoseidon2Params_eq]; decide +kernel

/-- Exact kernel-verified parameter validity, wire sizes, and query/target budgets for
    `baggyProdParams` (`Baggy-TSW-128f`) and `PorsFpSecurity.BaggySha3_128f` (`Baggy` `PORS+FP`). -/
theorem baggyProdParams_accounting :
    baggyProdParams.productionWellFormed = true ∧ baggyProdParams.statefulJorts = false ∧
    baggyProdParams.wireSigBytes = 74065 ∧
    prodPathTargetCount baggyProdParams (2 ^ 16) = 1120503 ∧
    prodPreCandidateBudget baggyProdParams = 6177 ∧
    prfSecPerSignBudget baggyProdParams = 10304 ∧
    prfSecQueryBudget baggyProdParams (2 ^ 16) = 675283456 ∧
    PorsFpSecurity.BaggySha3_128f.wellFormed = true ∧
    PorsFpSecurity.BaggySha3_128f.totalHeight = 32 ∧
    PorsFpSecurity.BaggySha3_128f.sigBytesMax = 71654 := by
  have hParity := PorsFpSecurity.baggySha3_128f_parity
  refine ⟨baggy128f_productionWellFormed, ?_, ?_, ?_, ?_, ?_, ?_,
    hParity.1, hParity.2.1, hParity.2.2.1⟩
  · rw [baggyProdParams, baggy128fParams_eq]
  · rw [baggyProdParams, PqHashParams.wireSigBytes_eq, baggy128fParams_eq]; decide +kernel
  · rw [baggyProdParams, prodPathTargetCount_eq, baggy128fParams_eq]; decide +kernel
  · unfold prodPreCandidateBudget; rw [baggyProdParams, baggy128fParams_eq]; decide +kernel
  · unfold prfSecPerSignBudget; rw [baggyProdParams, baggy128fParams_eq]; decide +kernel
  · unfold prfSecQueryBudget prfSecPerSignBudget
    rw [baggyProdParams, baggy128fParams_eq]; decide +kernel

/-- Exact kernel-verified parameter validity, wire size, and query/target budgets for `corduroyProdParams`. -/
theorem corduroyProdParams_accounting :
    corduroyProdParams.productionWellFormed = true ∧ corduroyProdParams.statefulJorts = false ∧
    corduroyProdParams.wireSigBytes = 37037 ∧
    prodPathTargetCount corduroyProdParams (2 ^ 12) = 35690 ∧
    prodPreCandidateBudget corduroyProdParams = 2721 ∧
    prfSecPerSignBudget corduroyProdParams = 16448 ∧
    prfSecQueryBudget corduroyProdParams (2 ^ 12) = 67373056 := by
  refine ⟨corduroyCustody128_productionWellFormed, ?_, ?_,
    corduroyCustody128_target_pool_budget.1, ?_, ?_, ?_⟩
  · rw [corduroyProdParams, corduroyCustody128Params_eq]
  · rw [corduroyProdParams, PqHashParams.wireSigBytes_eq, corduroyCustody128Params_eq]; decide +kernel
  · unfold prodPreCandidateBudget; rw [corduroyProdParams, corduroyCustody128Params_eq]; decide +kernel
  · unfold prfSecPerSignBudget; rw [corduroyProdParams, corduroyCustody128Params_eq]; decide +kernel
  · unfold prfSecQueryBudget prfSecPerSignBudget
    rw [corduroyProdParams, corduroyCustody128Params_eq]; decide +kernel

/-- Exact kernel-verified validity and wire byte lengths (`7,856`B and `17,088`B) for NIST FIPS 205
    Category-1 `SLH-DSA-SHAKE-128s` and `SLH-DSA-SHAKE-128f`. -/
theorem fips205ProdParams_accounting :
    fips205SlhDsa128sParams.wellFormed = true ∧ fips205SlhDsa128sParams.sigBytes = 7856 ∧
    fips205SlhDsa128fParams.wellFormed = true ∧ fips205SlhDsa128fParams.sigBytes = 17088 :=
  ⟨slhDsaShake128s_wellFormed, slhDsaShake128s_sigBytes,
   slhDsaShake128f_wellFormed, slhDsaShake128f_sigBytes⟩

/-- Production `Spec.RandomizedSigScheme` binding caller/adversary-chosen per-request `optRand`
    directly to `prodSignQuery` and `verifyProductionPqHashSig`. -/
@[expose] def productionRandomizedSigScheme (suite : TweakableHashSuite) (params : PqHashParams)
    (maxGrind : Nat) : Spec.RandomizedSigScheme PqPublicKey PqSecretKey PqHashSig where
  derivePk := derivePublicKey suite params
  sign sk ep optRand msg := prodSignQuery suite params sk ⟨msg, optRand, ep, maxGrind⟩
  verify := verifyProductionPqHashSig suite params
  correct sk ep optRand msg sig h :=
    prodSignQuery_verifies suite params sk ⟨msg, optRand, ep, maxGrind⟩ sig h

/-- **Forward Refinement (`⊑`) of the Latched Production Randomized Signer to `Spec.idealRandomizedSignMachine`.**
    Established via `Spec.latchedRandomizedSigner_refines_ideal`. -/
def productionLatchedRandomizedSigner_refines_idealSign
    (suite : TweakableHashSuite) (params : PqHashParams) (maxGrind : Nat)
    (sk : PqSecretKey) (maxWindow : Nat) :
    Spec.latchedRandomizedSignerMachine (productionRandomizedSigScheme suite params maxGrind)
      sk params.statefulJorts maxWindow ⊑
    Spec.idealRandomizedSignMachine (productionRandomizedSigScheme suite params maxGrind)
      (derivePublicKey suite params sk) params.statefulJorts maxWindow
      (fun req => prodSignQuery suite params sk ⟨req.message, req.optRand, req.epoch, maxGrind⟩) :=
  Spec.latchedRandomizedSigner_refines_ideal
    (productionRandomizedSigScheme suite params maxGrind) sk params.statefulJorts maxWindow

/-- Every trace admitted by the concrete latched production randomized signer is admitted by
    `Spec.idealRandomizedSignMachine`. -/
theorem productionLatchedRandomizedSigner_admitsTrace_ideal
    (suite : TweakableHashSuite) (params : PqHashParams) (maxGrind : Nat)
    (sk : PqSecretKey) (maxWindow : Nat) {tr : List (Spec.RandomizedSignRequest × PqHashSig)}
    (hAdmits : (Spec.latchedRandomizedSignerMachine
      (productionRandomizedSigScheme suite params maxGrind)
      sk params.statefulJorts maxWindow).AdmitsTrace tr) :
    (Spec.idealRandomizedSignMachine (productionRandomizedSigScheme suite params maxGrind)
      (derivePublicKey suite params sk) params.statefulJorts maxWindow
      (fun req => prodSignQuery suite params sk ⟨req.message, req.optRand, req.epoch, maxGrind⟩)
      ).AdmitsTrace tr :=
  (productionLatchedRandomizedSigner_refines_idealSign suite params maxGrind sk maxWindow
    ).preserve_admitsTrace hAdmits

/-- **Trace Safety of the Stateful Latched Production Randomized Signer.**
    Established via `Spec.latchedRandomizedSigner_trace_safe`. -/
theorem productionLatchedRandomizedSigner_trace_safe
    (suite : TweakableHashSuite) (params : PqHashParams) (maxGrind : Nat)
    (sk : PqSecretKey) (maxWindow : Nat) (hStateful : params.statefulJorts = true)
    {tr : List (Spec.RandomizedSignRequest × PqHashSig)}
    (hAdmits : (Spec.latchedRandomizedSignerMachine
      (productionRandomizedSigScheme suite params maxGrind)
      sk params.statefulJorts maxWindow).AdmitsTrace tr) :
    (∀ p ∈ tr,
      verifyProductionPqHashSig suite params (derivePublicKey suite params sk) p.1.message p.2 =
        true) ∧
    tr.Pairwise (fun a b => a.1.epoch < b.1.epoch) := by
  rw [hStateful] at hAdmits
  exact Spec.latchedRandomizedSigner_trace_safe
    (productionRandomizedSigScheme suite params maxGrind) sk maxWindow hAdmits

/-! ## §2. Explicit Classical (`256`-Bit) & Post-Quantum (`QROM` / Grover) Budgets + QROM Bridges -/

/-- Classical `256`-bit random-oracle / ideal-tweakable-hash single-target query budget `(qEval + 1) / 2^256`. -/
@[expose] def classical256PrimEps (qEval : Nat) : Spec.RatBound :=
  ⟨qEval + 1, 2 ^ 256, by decide⟩

/-- Post-quantum `QROM` (`[BBBV97]` / `[AHU19]` / Grover) `256`-bit single-target query budget
    `8 * (qEval + 1)^2 / 2^256`. -/
@[expose] def pqQrom256PrimEps (qEval : Nat) : Spec.RatBound :=
  ⟨8 * (qEval + 1) ^ 2, 2 ^ 256, by decide⟩

theorem classical256PrimEps_mono {q₁ q₂ : Nat} (h : q₁ ≤ q₂) :
    (classical256PrimEps q₁).le (classical256PrimEps q₂) :=
  Nat.mul_le_mul_right (2 ^ 256) (Nat.add_le_add_right h 1)

theorem pqQrom256PrimEps_mono {q₁ q₂ : Nat} (h : q₁ ≤ q₂) :
    (pqQrom256PrimEps q₁).le (pqQrom256PrimEps q₂) :=
  Nat.mul_le_mul_right (2 ^ 256)
    (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 2))

private theorem qrom_quad_dominates (Q : Nat) :
    2 * Q ≤ 8 * (Q + 1) ^ 2 ∧ 4 * Q ≤ 8 * (Q + 1) ^ 2 ∧ 2 * (Q * Q + 1) ≤ 8 * (Q + 1) ^ 2 := by
  rw [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_add]
  exact ⟨Decidable.byContradiction (fun _ => by omega),
    Decidable.byContradiction (fun _ => by omega),
    Decidable.byContradiction (fun _ => by omega)⟩

/-- **QROM Keyed-PRF Hiding Bridge (`qrom_hidingAdv_deployed_le_pqQrom256PrimEps`).**
    Connects `hidingAdv_le_deployed` on both `deployedCardBitVec256` and `deployedCardGoldilocks4`
    directly to `pqQrom256PrimEps Q`. -/
theorem qrom_hidingAdv_deployed_le_pqQrom256PrimEps {TagDom Cod : Type} (Q : Nat)
    (baseBv : Fin deployedCardBitVec256 × TagDom → Cod)
    (baseGl : Fin deployedCardGoldilocks4 × TagDom → Cod) (secFn : TagDom → Cod)
    (Abv : OracleComp (Fin deployedCardBitVec256 × TagDom) Cod Bool)
    (Agl : OracleComp (Fin deployedCardGoldilocks4 × TagDom) Cod Bool)
    (hBv : QueryBounded Q Abv) (hGl : QueryBounded Q Agl) :
    let hGlPos : 0 < deployedCardGoldilocks4 := by unfold deployedCardGoldilocks4; decide
    let bvAdv : Spec.RatBound :=
      ⟨natAbsDiff (keyedPrfRealAccept deployedCardBitVec256 baseBv secFn Abv)
                  (keyedPrfIdealAccept deployedCardBitVec256 baseBv Abv),
       deployedCardBitVec256, by unfold deployedCardBitVec256; decide⟩
    let glAdv : Spec.RatBound :=
      ⟨natAbsDiff (keyedPrfRealAccept deployedCardGoldilocks4 baseGl secFn Agl)
                  (keyedPrfIdealAccept deployedCardGoldilocks4 baseGl Agl),
       deployedCardGoldilocks4, hGlPos⟩
    bvAdv.le (pqQrom256PrimEps Q) ∧ glAdv.le (pqQrom256PrimEps Q) := by
  obtain ⟨hBvRat, hGlRat⟩ := hidingAdv_le_deployed Q baseBv baseGl secFn Abv Agl hBv hGl
  have hGlGt : 2 ^ 255 < deployedCardGoldilocks4 := deployedCardGoldilocks4_ne_bitVec256.2.1
  have hGl2 : 2 ^ 256 ≤ 2 * deployedCardGoldilocks4 := by
    have hPow : 2 ^ 256 = 2 * 2 ^ 255 := by decide
    exact Decidable.byContradiction (fun _ => by omega)
  refine ⟨?_, ?_⟩
  · unfold pqQrom256PrimEps Spec.RatBound.le; dsimp only
    have hB := hBvRat.2.2; unfold deployedCardBitVec256 at hB ⊢
    exact Nat.le_trans hB (Nat.mul_le_mul_right (2 ^ 256) (qrom_quad_dominates Q).1)
  · unfold pqQrom256PrimEps Spec.RatBound.le; dsimp only
    have hG := Nat.le_of_mul_le_mul_right hGlRat.2.2 hGlRat.1
    calc natAbsDiff _ _ * 2 ^ 256
      _ ≤ (2 * Q) * (2 * deployedCardGoldilocks4) := Nat.mul_le_mul hG hGl2
      _ = (4 * Q) * deployedCardGoldilocks4 := by
            have h4 : 2 * Q * 2 = 4 * Q := Decidable.byContradiction (fun _ => by omega)
            rw [← Nat.mul_assoc, h4]
      _ ≤ (8 * (Q + 1) ^ 2) * deployedCardGoldilocks4 :=
            Nat.mul_le_mul_right _ (qrom_quad_dominates Q).2.1

/-- **QROM Unified Merkle Tree Birthday Bridge (`qrom_unifiedTree_birthday_le_pqQrom256PrimEps`).**
    Connects `unifiedTreeGame_birthday_le` on both `2^256` and `Goldilocks^4` to `pqQrom256PrimEps Q`. -/
theorem qrom_unifiedTree_birthday_le_pqQrom256PrimEps {LeafBlock Digest32 : Type}
    (Q depth : Nat) (hWalk : merkleWalkQueries depth ≤ Q)
    (stepHistBv : (i : Nat) → i < Q → List (Fin deployedCardBitVec256))
    (hHistBv : ∀ i (hi : i < Q), (stepHistBv i hi).length ≤ i)
    (stepHistGl : (i : Nat) → i < Q → List (Fin deployedCardGoldilocks4))
    (hHistGl : ∀ i (hi : i < Q), (stepHistGl i hi).length ≤ i)
    (leafA : LeafBlock) (nodeB : Digest32 × Digest32) :
    let hBvPos : 0 < deployedCardBitVec256 := by unfold deployedCardBitVec256; decide
    let hGlPos : 0 < deployedCardGoldilocks4 := by unfold deployedCardGoldilocks4; decide
    let bvBday : Spec.RatBound :=
      ⟨1 + qsum Q (fun idx => stepCollisionHits deployedCardBitVec256 (stepHistBv idx.val idx.isLt)),
       deployedCardBitVec256, hBvPos⟩
    let glBday : Spec.RatBound :=
      ⟨1 + qsum Q (fun idx => stepCollisionHits deployedCardGoldilocks4 (stepHistGl idx.val idx.isLt)),
       deployedCardGoldilocks4, hGlPos⟩
    (Sum.inl leafA : UnifiedTreeDom LeafBlock Digest32) ≠ Sum.inr nodeB ∧
    cumulativeBirthdayBound (merkleWalkQueries depth) ≤ Q * Q + 1 ∧
    bvBday.le (pqQrom256PrimEps Q) ∧ glBday.le (pqQrom256PrimEps Q) := by
  have hBvPos : 0 < deployedCardBitVec256 := by unfold deployedCardBitVec256; decide
  have hGlPos : 0 < deployedCardGoldilocks4 := by unfold deployedCardGoldilocks4; decide
  obtain ⟨hDisj, hBvR, hCum⟩ :=
    unifiedTreeGame_birthday_le deployedCardBitVec256 Q depth hBvPos hWalk stepHistBv hHistBv leafA nodeB
  obtain ⟨_, hGlR, _⟩ :=
    unifiedTreeGame_birthday_le deployedCardGoldilocks4 Q depth hGlPos hWalk stepHistGl hHistGl leafA nodeB
  have hGl2 : 2 ^ 256 ≤ 2 * deployedCardGoldilocks4 := by
    have hGt := deployedCardGoldilocks4_ne_bitVec256.2.1
    have hPow : 2 ^ 256 = 2 * 2 ^ 255 := by decide
    exact Decidable.byContradiction (fun _ => by omega)
  refine ⟨hDisj, hCum, ?_, ?_⟩
  · unfold pqQrom256PrimEps Spec.RatBound.le; dsimp only
    have hB := hBvR.2.2; unfold deployedCardBitVec256 at hB ⊢
    have h1 : Q * Q + 1 ≤ 8 * (Q + 1) ^ 2 :=
      Decidable.byContradiction (fun _ => by have h2 := (qrom_quad_dominates Q).2.2; omega)
    exact Nat.le_trans hB (Nat.mul_le_mul_right (2 ^ 256) h1)
  · unfold pqQrom256PrimEps Spec.RatBound.le; dsimp only
    have hG := Nat.le_of_mul_le_mul_right hGlR.2.2 hGlPos
    calc (1 + qsum Q _) * 2 ^ 256
      _ ≤ (Q * Q + 1) * (2 * deployedCardGoldilocks4) := Nat.mul_le_mul hG hGl2
      _ = (2 * (Q * Q + 1)) * deployedCardGoldilocks4 := by
            rw [← Nat.mul_assoc, Nat.mul_comm (Q * Q + 1) 2]
      _ ≤ (8 * (Q + 1) ^ 2) * deployedCardGoldilocks4 :=
            Nat.mul_le_mul_right _ (qrom_quad_dominates Q).2.2


/-! ## §3. Multi-Hop (`Hop 1` `PRF_msg` + `Hop 2` `PRF` + Ideal-PRF Slot Extraction) EUF-CMA Engine -/

/-- Constructive coin-space reassociation routing `sampleSec` as challenger coordinate for Hop 2. -/
def reassocHop2CoinSplit {n nC1 nRest nC2 nA : Nat}
    (π1 : Spec.CoinSplit n nC1 nRest) (π2 : Spec.CoinSplit nRest nC2 nA) :
    Spec.CoinSplit n nC2 (nC1 * nA) :=
  let sp := Spec.CoinSplit.prod nC1 nA
  { chal := fun ω => π2.chal (π1.advc ω)
    advc := fun ω => sp.pair (π1.chal ω) (π2.advc (π1.advc ω))
    pair := fun c2 b => π1.pair (sp.chal b) (π2.pair c2 (sp.advc b))
    chal_pair := fun c2 b => by rw [π1.advc_pair, π2.chal_pair]
    advc_pair := fun c2 b => by rw [π1.chal_pair, π1.advc_pair, π2.advc_pair, sp.pair_eta]
    pair_eta := fun ω => by rw [sp.chal_pair, sp.advc_pair, π2.pair_eta, π1.pair_eta] }

/-- Ideal-PRF run outcome packaged as a `ProdEufCmaOutcome` under `fullIdealOverlaySuite`. -/
abbrev idealPrfOverlaySuite := fullIdealOverlaySuite

def idealPrfOutcome {qHash qSign : Nat} (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (rfMsg rfSec : Spec.Bytes → Spec.Bytes)
    (A : SeedWithheldEufCmaAdv qHash qSign) : ProdEufCmaOutcome :=
  let run := evalLatchedAdaptiveTree true suite.rawHash
    (signQueryIdealPrf suite params pkSeed rfMsg rfSec)
    ((canonicalizeAdvOptRand A).run (derivePublicKeyIdealPrf suite params pkSeed rfSec)) 0
  ⟨⟨[], [], pkSeed⟩, run.2, run.1.1, run.1.2⟩

/-- Decidable check for whether candidate slot `slot` of `prodPathTargets` carries the extracted
    on-path target-collision witness of `idealPrfOutcome`. -/
def idealPrfTcrSlotWin {qHash qSign : Nat} (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (pkSeed : List UInt8)
    (rfMsg rfSec : Spec.Bytes → Spec.Bytes) (A : SeedWithheldEufCmaAdv qHash qSign) (slot : Nat) : Bool :=
  let ov := idealPrfOverlaySuite suite pkSeed rfMsg rfSec
  let o := idealPrfOutcome suite params pkSeed rfMsg rfSec A
  let log := productionSigningLog ov params o.sk o.queries
  let idxs := prodSigForsIdxs ov params (derivePublicKey ov params o.sk) o.msgStar o.sigStar
  match prodTcrOutput ov params hw o (fun _ => evalLatchedAdaptiveTree_oneTime suite.rawHash _ _ 0) with
  | none => false
  | some (t, forged) =>
    decide ((prodPathTargets params log o.sigStar.leafGlobalIdx idxs)[slot]? = some t) &&
      prodTcrCheck ov params o.sk o.sigStar.leafGlobalIdx t forged

/-- Decidable check for whether candidate slot `slot < prodPreCandidateBudget params` carries an
    unopened `FORS` leaf or `WOTS+C` chain-step preimage on `idealPrfOutcome`. -/
def idealPrfPreSlotWin {qHash qSign : Nat} (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (rfMsg rfSec : Spec.Bytes → Spec.Bytes)
    (A : SeedWithheldEufCmaAdv qHash qSign) (slot : Nat) : Bool :=
  let ov := idealPrfOverlaySuite suite pkSeed rfMsg rfSec
  let o := idealPrfOutcome suite params pkSeed rfMsg rfSec A
  let pk := derivePublicKey ov params o.sk
  let log := productionSigningLog ov params o.sk o.queries
  let leaf := o.sigStar.leafGlobalIdx
  let idxs := prodSigForsIdxs ov params pk o.msgStar o.sigStar
  if slot < params.forsTrees then
    let j := slot; let u := idxs.getD j 0
    decide ((leaf, j, u) ∉ prodLogForsLeaves ov params pk log) &&
    decide (forsIndexedLeafHash ov pkSeed (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight))
      (leaf % 2 ^ params.subtreeHeight) j u (o.sigStar.forsOpenings.getD j ⟨[], []⟩).secretVal =
      forsIndexedLeafFn ov o.sk (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight))
        (leaf % 2 ^ params.subtreeHeight) j u)
  else
    let rem := slot - params.forsTrees; let stride := params.ell1 * (params.w - 1)
    if stride = 0 then false else
      let i := rem / stride; let rem2 := rem % stride
      let r := rem2 / (params.w - 1); let step := rem2 % (params.w - 1)
      let tree := UInt64.ofNat (leaf / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight)
      let kp := leaf / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight
      decide (i < params.numLayers) && decide (r < params.ell1) && decide (step + 1 ≤ params.w - 1) &&
      decide (thChainF ov pkSeed
        ⟨UInt32.ofNat i, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat step⟩
        ((o.sigStar.layerSigs.getD i ⟨0, [], []⟩).wotsChains.getD r []) =
        honestChainNode ov o.sk (UInt32.ofNat i) tree kp r (step + 1)) &&
      log.all (fun e => decide (e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) =
        leaf / 2 ^ (i * params.subtreeHeight) →
        step < (prodLogLayerDigits ov params o.sk e i).getD r 0))

/-- Decidable `FORS` subset-cover indicator on `idealPrfOutcome` (`false` in stateful `Jorts` mode). -/
def idealPrfItsrWin {qHash qSign : Nat} (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (pkSeed : List UInt8)
    (rfMsg rfSec : Spec.Bytes → Spec.Bytes) (A : SeedWithheldEufCmaAdv qHash qSign) : Bool :=
  prodItsrEvent (idealPrfOverlaySuite suite pkSeed rfMsg rfSec) params hw
    (idealPrfOutcome suite params pkSeed rfMsg rfSec A)
    (fun _ => evalLatchedAdaptiveTree_oneTime suite.rawHash _ _ 0)

theorem idealPrfItsrWin_of_forsTrees_zero {qHash qSign : Nat}
    (suite : TweakableHashSuite) (params : PqHashParams) (hw : params.w = 4 ∨ params.w = 16)
    (hZero : params.forsTrees = 0) (pkSeed : List UInt8)
    (rfMsg rfSec : Spec.Bytes → Spec.Bytes) (A : SeedWithheldEufCmaAdv qHash qSign) :
    idealPrfItsrWin suite params hw pkSeed rfMsg rfSec A = false := by
  cases hEv : idealPrfItsrWin suite params hw pkSeed rfMsg rfSec A with
  | false => rfl
  | true =>
    have hBrk := prodItsrEvent_sound _ params hw _ _ hEv
    exact absurd hBrk.trees_pos (by rw [hZero]; exact Nat.lt_irrefl 0)

private theorem idealPrf_win_classified_slots {qHash qSign : Nat}
    (suite : TweakableHashSuite) (params : PqHashParams) (hw : params.w = 4 ∨ params.w = 16)
    (pkSeed : List UInt8) (rfMsg rfSec : Spec.Bytes → Spec.Bytes)
    (hRf32 : ∀ x, x.length = 65 → (rfMsg x).length = 32) (A : SeedWithheldEufCmaAdv qHash qSign)
    (hWin : (ExecEufCmaIdealPrfGame true Nat.one_pos suite params (fun _ => pkSeed)
      (fun _ => rfMsg) (fun _ => rfSec) (fun _ => A)).win ⟨0, Nat.one_pos⟩ = true) :
    idealPrfItsrWin suite params hw pkSeed rfMsg rfSec A = true ∨
    (∃ slot : Fin (prodPathTargetCount params qSign),
      idealPrfTcrSlotWin suite params hw pkSeed rfMsg rfSec A slot.val = true) ∨
    (∃ slot : Fin (prodPreCandidateBudget params),
      idealPrfPreSlotWin suite params pkSeed rfMsg rfSec A slot.val = true) := by
  let ov := idealPrfOverlaySuite suite pkSeed rfMsg rfSec
  let o := idealPrfOutcome suite params pkSeed rfMsg rfSec A
  have hPkEq : derivePublicKey ov params o.sk = derivePublicKeyIdealPrf suite params pkSeed rfSec :=
    fullIdealOverlaySuite_derivePublicKey_eq suite params pkSeed rfMsg rfSec
  have hOptAll : ∀ q ∈ o.queries, q.randomness = [] ∨ q.randomness.length = 32 := by
    intro q hq; dsimp only [o, idealPrfOutcome] at hq
    rw [canonicalizeAdvOptRand_run] at hq
    exact evalLatched_canonicalize_log_optRand true suite.rawHash _ _ 0 q hq
  have hLogEq : productionSigningLog ov params o.sk o.queries =
      signLogFromOracle (signQueryIdealPrf suite params pkSeed rfMsg rfSec) o.queries :=
    fullIdealOverlaySuite_productionSigningLog_eq suite params pkSeed rfMsg rfSec hRf32
      o.queries hOptAll
  have hWinOv : prodEufCmaWin ov params o = true := by
    rw [ExecEufCmaIdealPrfGame_win] at hWin; dsimp only at hWin
    rw [prodEufCmaWin_eq, fullIdealOverlaySuite_verify_eq, hPkEq, hLogEq]
    exact hWin
  let hOT : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q' :=
    fun _ => evalLatchedAdaptiveTree_oneTime suite.rawHash _ _ 0
  rcases prodEufCmaWin_classified ov params hw o hOT hWinOv with hItsr | hTcr | hPre
  · exact .inl hItsr
  · refine .inr (.inl ?_)
    rw [prodTcrEvent_eq] at hTcr
    cases hOut : prodTcrOutput ov params hw o hOT with
    | none => rw [hOut] at hTcr; cases hTcr
    | some pair =>
      rcases pair with ⟨t, forged⟩; rw [hOut] at hTcr
      obtain ⟨_, hOnPath, _, _⟩ := prodTcrOutput_sound ov params hw o hOT t forged hOut
      have hMem := ProdTargetIdx.mem_pathTargets params
        (productionSigningLog ov params o.sk o.queries) o.sigStar.leafGlobalIdx
        (prodSigForsIdxs ov params (derivePublicKey ov params o.sk) o.msgStar o.sigStar) t hOnPath
      obtain ⟨idx, hIdxLt, hIdxEq⟩ := List.mem_iff_getElem.mp hMem
      have hQsLe := evalLatchedAdaptiveTree_log_length true suite.rawHash
        (signQueryIdealPrf suite params pkSeed rfMsg rfSec)
        ((canonicalizeAdvOptRand A).run (derivePublicKeyIdealPrf suite params pkSeed rfSec)) 0
        ((canonicalizeAdvOptRand A).bounded _)
      have hLogLe := Nat.le_trans (productionSigningLog_length_le ov params o.sk o.queries) hQsLe
      have hBound : idx < prodPathTargetCount params qSign := by
        rw [prodPathTargets_length] at hIdxLt
        exact Nat.lt_of_lt_of_le hIdxLt (prodPathTargetCount_mono params hLogLe)
      refine ⟨⟨idx, hBound⟩, ?_⟩
      unfold idealPrfTcrSlotWin; dsimp only [ov, o]; rw [hOut, Bool.and_eq_true]
      exact ⟨decide_eq_true ((List.getElem?_eq_getElem hIdxLt).trans (congrArg some hIdxEq)), hTcr⟩
  · refine .inr (.inr ?_)
    cases prodPreEvent_sound ov params hw o hOT hPre with
    | fors j hj hUnrev hInv =>
      refine ⟨⟨j, Decidable.byContradiction (fun h => by unfold prodPreCandidateBudget at h; omega)⟩, ?_⟩
      unfold idealPrfPreSlotWin; rw [ite_eq_left hj]
      exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hUnrev, decide_eq_true hInv⟩
    | wots i hi r hr step hstep hInv hUnrev =>
      have hw1Pos : 0 < params.w - 1 := Decidable.byContradiction (fun _ => by omega)
      have hStepLt : step < params.w - 1 := Decidable.byContradiction (fun _ => by omega)
      let W1 := params.w - 1; let stride := params.ell1 * W1
      have hStridePos : 0 < stride := Nat.mul_pos (Nat.lt_of_le_of_lt (Nat.zero_le r) hr) hw1Pos
      have hRem2Lt : r * W1 + step < stride := Decidable.byContradiction (fun _ => by
        have h1 := Nat.mul_le_mul_right W1 hr; rw [Nat.succ_mul] at h1; omega)
      have hOffLt : i * stride + (r * W1 + step) < params.numLayers * stride :=
        Decidable.byContradiction (fun _ => by
          have h1 := Nat.mul_le_mul_right stride hi; rw [Nat.succ_mul] at h1; omega)
      let slotNat := params.forsTrees + (i * stride + (r * W1 + step))
      dsimp only [W1, stride] at hStridePos hRem2Lt hOffLt
      refine ⟨⟨slotNat, Decidable.byContradiction (fun h => by
        unfold prodPreCandidateBudget at h; dsimp only [slotNat, stride, W1] at h; omega)⟩, ?_⟩
      unfold idealPrfPreSlotWin
      dsimp only
      rw [ite_eq_right (by intro h; dsimp only [slotNat] at h; omega : ¬ slotNat < params.forsTrees),
        ite_eq_right (Nat.ne_of_gt hStridePos)]
      have hSub : slotNat - params.forsTrees =
          i * (params.ell1 * (params.w - 1)) + (r * (params.w - 1) + step) :=
        Nat.add_sub_cancel_left params.forsTrees _
      have hDivI : (i * (params.ell1 * (params.w - 1)) + (r * (params.w - 1) + step)) /
          (params.ell1 * (params.w - 1)) = i := by
        rw [Nat.mul_comm i _, Nat.mul_add_div hStridePos, Nat.div_eq_of_lt hRem2Lt, Nat.add_zero]
      have hModI : (i * (params.ell1 * (params.w - 1)) + (r * (params.w - 1) + step)) %
          (params.ell1 * (params.w - 1)) = r * (params.w - 1) + step := by
        rw [Nat.mul_comm i _, Nat.mul_add_mod, Nat.mod_eq_of_lt hRem2Lt]
      have hDivR : (r * (params.w - 1) + step) / (params.w - 1) = r := by
        rw [Nat.mul_comm r _, Nat.mul_add_div hw1Pos, Nat.div_eq_of_lt hStepLt, Nat.add_zero]
      have hModR : (r * (params.w - 1) + step) % (params.w - 1) = step := by
        rw [Nat.mul_comm r _, Nat.mul_add_mod, Nat.mod_eq_of_lt hStepLt]
      rw [hSub, hDivI, hModI, hDivR, hModR]
      refine Bool.and_eq_true_iff.mpr ⟨?_, List.all_eq_true.mpr fun e he => decide_eq_true (hUnrev e he)⟩
      refine Bool.and_eq_true_iff.mpr ⟨?_, decide_eq_true hInv⟩
      refine Bool.and_eq_true_iff.mpr ⟨?_, decide_eq_true hstep⟩
      exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hi, decide_eq_true hr⟩

/-- Real key generator induced by `(sampleMsg, sampleSec, pkSeedA)` across `π1` and `π2`. -/
abbrev multiHopKeygen {n nC1 nRest nC2 nA : Nat}
    (π1 : Spec.CoinSplit n nC1 nRest) (π2 : Spec.CoinSplit nRest nC2 nA)
    (sampleMsg : Fin nC1 → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (sampleSec : Fin nC2 → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (pkSeedA : Fin nA → List UInt8) (ω : Fin n) : PqSecretKey :=
  ⟨(sampleSec (π2.chal (π1.advc ω))).1, (sampleMsg (π1.chal ω)).1, pkSeedA (π2.advc (π1.advc ω))⟩

/-- Real canonicalized adversary family routed across `π1` and `π2`. -/
abbrev multiHopAdv {n nC1 nRest nC2 nA qHash qSign : Nat}
    (π1 : Spec.CoinSplit n nC1 nRest) (π2 : Spec.CoinSplit nRest nC2 nA)
    (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign) (ω : Fin n) :
    SeedWithheldEufCmaAdv qHash qSign :=
  canonicalizeAdvOptRand (adv (π2.advc (π1.advc ω)))

/-- Ideal-PRF `ITSR` game on `(π1, π2, sampleMsg, sampleSec, pkSeedA, adv)`. -/
abbrev idealSlotItsrGame {n nC1 nRest nC2 nA qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams) (hw : params.w = 4 ∨ params.w = 16)
    (π1 : Spec.CoinSplit n nC1 nRest) (π2 : Spec.CoinSplit nRest nC2 nA)
    (sampleMsg : Fin nC1 → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (sampleSec : Fin nC2 → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (pkSeedA : Fin nA → List UInt8) (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign) :
    Spec.FinGame n :=
  ⟨hPos, fun ω => idealPrfItsrWin suite params hw (pkSeedA (π2.advc (π1.advc ω)))
    (sampleMsg (π1.chal ω)).2 (sampleSec (π2.chal (π1.advc ω))).2 (adv (π2.advc (π1.advc ω)))⟩

/-- Ideal-PRF single-slot path-collision (`TCR`) game at `slot`. -/
abbrev idealSlotTcrGame {n nC1 nRest nC2 nA qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams) (hw : params.w = 4 ∨ params.w = 16)
    (π1 : Spec.CoinSplit n nC1 nRest) (π2 : Spec.CoinSplit nRest nC2 nA)
    (sampleMsg : Fin nC1 → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (sampleSec : Fin nC2 → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (pkSeedA : Fin nA → List UInt8) (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    (slot : Nat) : Spec.FinGame n :=
  ⟨hPos, fun ω => idealPrfTcrSlotWin suite params hw (pkSeedA (π2.advc (π1.advc ω)))
    (sampleMsg (π1.chal ω)).2 (sampleSec (π2.chal (π1.advc ω))).2 (adv (π2.advc (π1.advc ω))) slot⟩

/-- Ideal-PRF single-slot secret-preimage (`PRE`) game at `slot`. -/
abbrev idealSlotPreGame {n nC1 nRest nC2 nA qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (π1 : Spec.CoinSplit n nC1 nRest) (π2 : Spec.CoinSplit nRest nC2 nA)
    (sampleMsg : Fin nC1 → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (sampleSec : Fin nC2 → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (pkSeedA : Fin nA → List UInt8) (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    (slot : Nat) : Spec.FinGame n :=
  ⟨hPos, fun ω => idealPrfPreSlotWin suite params (pkSeedA (π2.advc (π1.advc ω)))
    (sampleMsg (π1.chal ω)).2 (sampleSec (π2.chal (π1.advc ω))).2 (adv (π2.advc (π1.advc ω))) slot⟩

/-- **Master Multi-Hop (`PRF_msg` + `PRF` + Ideal-PRF Slot Union) Production EUF-CMA Bound.**
    Composes `hulsing_hop1_prfMsg_idealization` and `hulsing_hop2_prfSec_idealization` with
    constructive slot extraction over `prodPathTargetCount params qSign` collision targets and
    `prodPreCandidateBudget params` secret-preimage slots. -/
theorem hulsing_multiHop_idealSlot_euf_cma_bound {n nC1 nRest nC2 nA qHash qSign : Nat}
    (hPos : 0 < n) (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (seedLen keyLen qPrfMsg qPrfSec : Nat)
    (hSeedPos : 0 < seedLen) (hqPrfMsg : qSign ≤ qPrfMsg)
    (hqPrfSec : prfSecQueryBudget params qSign ≤ qPrfSec)
    (π1 : Spec.CoinSplit n nC1 nRest) (π2 : Spec.CoinSplit nRest nC2 nA)
    (sampleMsg : Fin nC1 → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSampleMsg : Spec.UniformOn (Spec.PrfSampleOk keyLen 65 32) sampleMsg)
    (sampleSec : Fin nC2 → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSampleSec : Spec.UniformOn (Spec.PrfSampleOk keyLen (seedLen + 32) 32) sampleSec)
    (pkSeedA : Fin nA → List UInt8) (hSeedLen : ∀ a, (pkSeedA a).length = seedLen)
    (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    {𝒜Msg 𝒜Sec : Spec.Code Spec.byteOracleIface Bool → Prop}
    (hClassMsg : ∀ r : Fin nRest, 𝒜Msg (prfMsgHopDistinguisher true suite params
      (pkSeedA (π2.advc r)) (sampleSec (π2.chal r)).1 (adv (π2.advc r))))
    (hClassSec : ∀ b : Fin (nC1 * nA),
      let sp := Spec.CoinSplit.prod nC1 nA
      𝒜Sec (prfSecHopDistinguisher true suite params (pkSeedA (sp.advc b))
        (sampleMsg (sp.chal b)).2 (adv (sp.advc b))))
    {εPrfMsg εPrfSec εItsr εTcr εPre : Spec.RatBound}
    (hPrfMsg : Spec.PrfHard 𝒜Msg (suitePrfMsg65 suite) keyLen 65 32 qPrfMsg εPrfMsg)
    (hPrfSec : Spec.PrfHard 𝒜Sec (suitePrfSec seedLen suite) keyLen (seedLen + 32) 32 qPrfSec εPrfSec)
    (hItsrB : Spec.GameBound
      (idealSlotItsrGame hPos suite params hw π1 π2 sampleMsg sampleSec pkSeedA adv).winProb εItsr)
    (hTcrB : ∀ slot : Fin (prodPathTargetCount params qSign), Spec.GameBound
      (idealSlotTcrGame hPos suite params hw π1 π2 sampleMsg sampleSec pkSeedA adv slot.val).winProb εTcr)
    (hPreB : ∀ slot : Fin (prodPreCandidateBudget params), Spec.GameBound
      (idealSlotPreGame hPos suite params π1 π2 sampleMsg sampleSec pkSeedA adv slot.val).winProb εPre) :
    Spec.GameBound
      (ExecEufCmaGame hPos suite params
        (multiHopKeygen π1 π2 sampleMsg sampleSec pkSeedA) (multiHopAdv π1 π2 adv)).winProb
      ((((εItsr.add (Spec.RatBound.scale (prodPathTargetCount params qSign) εTcr)).add
          (Spec.RatBound.scale (prodPreCandidateBudget params) εPre)).add εPrfSec).add εPrfMsg) := by
  let _ := hSeedPos
  have hHop1 := hulsing_hop1_prfMsg_idealization true hPos suite params keyLen qPrfMsg hqPrfMsg
    π1 sampleMsg hSampleMsg (fun r => pkSeedA (π2.advc r)) (fun r => (sampleSec (π2.chal r)).1)
    (fun r => adv (π2.advc r)) hClassMsg hPrfMsg
  let sp := Spec.CoinSplit.prod nC1 nA; let πHop2 := reassocHop2CoinSplit π1 π2
  have hHop2Raw := hulsing_hop2_prfSec_idealization true hPos suite params seedLen keyLen qPrfSec
    hqPrfSec πHop2 sampleSec hSampleSec (fun b => pkSeedA (sp.advc b)) (fun b => hSeedLen (sp.advc b))
    (fun b => (sampleMsg (sp.chal b)).2) (fun b => adv (sp.advc b)) hClassSec hPrfSec
  let gHop1 := ExecEufCmaRandIdealGame true hPos suite params
    (fun ω => pkSeedA (π2.advc (π1.advc ω))) (fun ω => (sampleSec (π2.chal (π1.advc ω))).1)
    (fun ω => (sampleMsg (π1.chal ω)).2) (fun ω => adv (π2.advc (π1.advc ω)))
  let gHop2 := ExecEufCmaIdealPrfGame true hPos suite params
    (fun ω => pkSeedA (π2.advc (π1.advc ω))) (fun ω => (sampleMsg (π1.chal ω)).2)
    (fun ω => (sampleSec (π2.chal (π1.advc ω))).2) (fun ω => adv (π2.advc (π1.advc ω)))
  have hG1Eq : ExecEufCmaRandIdealGame true hPos suite params
      (fun ω => pkSeedA (sp.advc (πHop2.advc ω))) (fun ω => (sampleSec (πHop2.chal ω)).1)
      (fun ω => (sampleMsg (sp.chal (πHop2.advc ω))).2) (fun ω => adv (sp.advc (πHop2.advc ω))) =
      gHop1 := by
    apply Spec.FinGame.ext_win; intro ω; dsimp only [πHop2, reassocHop2CoinSplit, gHop1]
    rw [ExecEufCmaRandIdealGame_win, ExecEufCmaRandIdealGame_win, sp.chal_pair, sp.advc_pair]
  have hG2Eq : ExecEufCmaIdealPrfGame true hPos suite params
      (fun ω => pkSeedA (sp.advc (πHop2.advc ω))) (fun ω => (sampleMsg (sp.chal (πHop2.advc ω))).2)
      (fun ω => (sampleSec (πHop2.chal ω)).2) (fun ω => adv (sp.advc (πHop2.advc ω))) = gHop2 := by
    apply Spec.FinGame.ext_win; intro ω; dsimp only [πHop2, reassocHop2CoinSplit, gHop2]
    rw [ExecEufCmaIdealPrfGame_win, ExecEufCmaIdealPrfGame_win, sp.chal_pair, sp.advc_pair]
  have hHop2 : Spec.GameBound gHop1.winProb (gHop2.winProb.add εPrfSec) := by
    dsimp only at hHop2Raw; rwa [hG1Eq, hG2Eq] at hHop2Raw
  let tcrFam : Fin (prodPathTargetCount params qSign) → Spec.FinGame n := fun slot =>
    idealSlotTcrGame hPos suite params hw π1 π2 sampleMsg sampleSec pkSeedA adv slot.val
  let preFam : Fin (prodPreCandidateBudget params) → Spec.FinGame n := fun slot =>
    idealSlotPreGame hPos suite params π1 π2 sampleMsg sampleSec pkSeedA adv slot.val
  have hG2Bound : Spec.GameBound gHop2.winProb
      ((εItsr.add (Spec.RatBound.scale (prodPathTargetCount params qSign) εTcr)).add
        (Spec.RatBound.scale (prodPreCandidateBudget params) εPre)) := by
    refine Spec.event_le_three_reductions gHop2 _
      (Spec.FinGame.mk hPos (anySlotWins _ tcrFam)) (Spec.FinGame.mk hPos (anySlotWins _ preFam))
      (fun ω hW => ?_) hItsrB (anySlotWins_bound hPos _ tcrFam hTcrB)
      (anySlotWins_bound hPos _ preFam hPreB)
    have hMem := (Spec.PrfSampleOk_eq keyLen 65 32 _).mp (hSampleMsg.mem (π1.chal ω))
    have hRf32 : ∀ x : Spec.Bytes, x.length = 65 → ((sampleMsg (π1.chal ω)).2 x).length = 32 :=
      fun x hx => (hMem.2 x).1 hx
    have hWin1 : (ExecEufCmaIdealPrfGame true Nat.one_pos suite params
        (fun _ => pkSeedA (π2.advc (π1.advc ω))) (fun _ => (sampleMsg (π1.chal ω)).2)
        (fun _ => (sampleSec (π2.chal (π1.advc ω))).2)
        (fun _ => adv (π2.advc (π1.advc ω)))).win ⟨0, Nat.one_pos⟩ = true := by
      rw [ExecEufCmaIdealPrfGame_win]; rw [ExecEufCmaIdealPrfGame_win] at hW; exact hW
    rcases idealPrf_win_classified_slots suite params hw _ _ _ hRf32 _ hWin1 with
      hI | ⟨sT, hT⟩ | ⟨sP, hP⟩
    · exact .inl hI
    · exact .inr (.inl (anySlotWins_of_win _ tcrFam ω sT hT))
    · exact .inr (.inr (anySlotWins_of_win _ preFam ω sP hP))
  exact Spec.RatBound.le_trans hHop1
    (Spec.RatBound.add_le_add
      (Spec.RatBound.le_trans hHop2
        (Spec.RatBound.add_le_add hG2Bound (Spec.RatBound.le_refl εPrfSec)))
      (Spec.RatBound.le_refl εPrfMsg))

/-! ## §4. Negative Teeth & Assurance Audits -/

/-- `#tooth` At `2^64` Grover quantum queries against a `256`-bit primitive, `pqQrom256PrimEps`
    exceeds `2^{-128}`. -/
theorem tooth_pq_grover_2pow64_exceeds_128bit_bound :
    ¬ (pqQrom256PrimEps (2 ^ 64)).lt ⟨1, 2 ^ 128, by decide⟩ := by decide +kernel

/-- `#tooth` At `2^128` classical queries against a `256`-bit primitive, `classical256PrimEps`
    exceeds `2^{-128}`. -/
theorem tooth_classical_2pow128_exceeds_128bit_bound :
    ¬ (classical256PrimEps (2 ^ 128)).lt ⟨1, 2 ^ 128, by decide⟩ := by decide +kernel

/-- `#tooth` Disabling the stateful epoch latch (`stateful₀ = false`) on `productionRandomizedSigScheme`
    admits a valid two-signature trace reusing `epoch = 0`, violating strict epoch monotonicity. -/
theorem tooth_unlatched_stateful_signer_reuses_epoch :
    ¬ (∀ tr : List (Spec.RandomizedSignRequest × PqHashSig),
        (Spec.latchedRandomizedSignerMachine
          (productionRandomizedSigScheme poly257MultiLeafSuite multiLeaf4JortsParams 1)
          ⟨List.replicate 24 0x00, [], [0x00]⟩ false 0).AdmitsTrace tr →
        tr.Pairwise (fun a b => a.1.epoch < b.1.epoch)) := by
  intro hAll
  let sk0 : PqSecretKey := ⟨List.replicate 24 0x00, [], [0x00]⟩
  have hS0 := prodSignQuery_poly257MultiLeaf_valid sk0 (by decide : 0 < 4) (by decide : 0 < 3)
    Nat.one_pos [0xAA]
  have hS1 := prodSignQuery_poly257MultiLeaf_valid sk0 (by decide : 0 < 4) (by decide : 1 < 3)
    Nat.one_pos [0xBB]
  let req0 : Spec.RandomizedSignRequest := ⟨0, [0xAA], [0, 0]⟩
  let req1 : Spec.RandomizedSignRequest := ⟨0, [0xBB], [0, 1]⟩
  let M := Spec.latchedRandomizedSignerMachine
    (productionRandomizedSigScheme poly257MultiLeafSuite multiLeaf4JortsParams 1) sk0 false 0
  have hStep0 : M.step ⟨0⟩ req0 = some (⟨1⟩, honestMultiLeafSig sk0 0 0) :=
    Spec.latchedRandomizedSignerMachine_step_of_valid _ sk0 false 0 ⟨0⟩ req0 _ rfl hS0
  have hStep1 : M.step ⟨1⟩ req1 = some (⟨1⟩, honestMultiLeafSig sk0 0 1) :=
    Spec.latchedRandomizedSignerMachine_step_of_valid _ sk0 false 0 ⟨1⟩ req1 _ rfl hS1
  have hPw := hAll _ ⟨⟨0⟩, ⟨1⟩, Spec.latchedRandomizedSignerMachine_init _ sk0 false 0,
    .accept hStep0 (.accept hStep1 (.nil _))⟩
  exact Nat.lt_irrefl 0 ((List.pairwise_cons.mp hPw).1 _ (List.mem_cons.mpr (.inl rfl)))

/-- `#tooth` Mutating `jortsProdParams` with `forsTrees = 1` fails `productionWellFormed`. -/
theorem tooth_jortsProd_nonzero_fors_rejected :
    ({ jortsProdParams with forsTrees := 1 } : PqHashParams).productionWellFormed = false := by
  rw [PqHashParams.productionWellFormed_eq, jortsProdParams, jortsPoseidon2Params_eq]; decide +kernel

/-- `#tooth` Mutating `fips205SlhDsa128fParams` with `m = 30` fails `Fips205Params.wellFormed`. -/
theorem tooth_fips205_128f_bad_hmsg_rejected :
    ({ fips205SlhDsa128fParams with m := 30 } : Fips205Params).wellFormed = false := by
  rw [Fips205Params.wellFormed_eq, Fips205Params.mdBytes_eq,
    Fips205Params.treeBytes_eq, Fips205Params.leafBytes_eq]
  decide

/-- Joint inhabitedness witness for `productionLatchedRandomizedSigner_trace_safe`. -/
theorem inhabited_productionLatchedRandomizedSigner_trace_safe :
    ∃ (suite : TweakableHashSuite) (params : PqHashParams) (maxGrind : Nat)
      (sk : PqSecretKey) (maxWindow : Nat) (tr : List (Spec.RandomizedSignRequest × PqHashSig)),
      params.statefulJorts = true ∧
      (Spec.latchedRandomizedSignerMachine
        (productionRandomizedSigScheme suite params maxGrind)
        sk params.statefulJorts maxWindow).AdmitsTrace tr := by
  let sk0 : PqSecretKey := ⟨List.replicate 24 0x00, [], [0x00]⟩
  have hSt : multiLeaf4JortsParams.statefulJorts = true := by rw [multiLeaf4JortsParams.public_eqs]
  have hS0 := prodSignQuery_poly257MultiLeaf_valid sk0 (by decide : 0 < 4) (by decide : 0 < 3)
    Nat.one_pos [0xAA]
  let req0 : Spec.RandomizedSignRequest := ⟨0, [0xAA], [0, 0]⟩
  refine ⟨poly257MultiLeafSuite, multiLeaf4JortsParams, 1, sk0, 0,
    [(req0, honestMultiLeafSig sk0 0 0)], hSt, ⟨0⟩, ⟨1⟩,
    Spec.latchedRandomizedSignerMachine_init _ sk0 _ 0, .accept ?_ (.nil _)⟩
  exact Spec.latchedRandomizedSignerMachine_step_of_valid _ sk0 _ 0 ⟨0⟩ req0 _
    (by rw [hSt]; rfl) hS0

#verify_kernel
  Qsag.productionRandomizedSigScheme
  Qsag.productionLatchedRandomizedSigner_refines_idealSign
  Qsag.reassocHop2CoinSplit

#verify_constructive Qsag.jortsProdParams_accounting
  Qsag.baggyProdParams_accounting
  Qsag.corduroyProdParams_accounting
  Qsag.fips205ProdParams_accounting
  Qsag.productionLatchedRandomizedSigner_admitsTrace_ideal
  Qsag.productionLatchedRandomizedSigner_trace_safe
  Qsag.classical256PrimEps_mono
  Qsag.pqQrom256PrimEps_mono
  Qsag.qrom_hidingAdv_deployed_le_pqQrom256PrimEps
  Qsag.qrom_unifiedTree_birthday_le_pqQrom256PrimEps
  Qsag.idealPrfItsrWin_of_forsTrees_zero
  Qsag.hulsing_multiHop_idealSlot_euf_cma_bound
  Qsag.tooth_pq_grover_2pow64_exceeds_128bit_bound
  Qsag.tooth_classical_2pow128_exceeds_128bit_bound
  Qsag.tooth_unlatched_stateful_signer_reuses_epoch
  Qsag.tooth_jortsProd_nonzero_fors_rejected
  Qsag.tooth_fips205_128f_bad_hmsg_rejected
  Qsag.inhabited_productionLatchedRandomizedSigner_trace_safe

#verify_inhabited
  Qsag.productionLatchedRandomizedSigner_trace_safe
  Qsag.inhabited_productionLatchedRandomizedSigner_trace_safe


#tooth_pair Qsag.productionLatchedRandomizedSigner_trace_safe vs
  Qsag.tooth_unlatched_stateful_signer_reuses_epoch
#tooth_pair Qsag.jortsProdParams_accounting vs
  Qsag.tooth_jortsProd_nonzero_fors_rejected
#tooth_pair Qsag.fips205ProdParams_accounting vs
  Qsag.tooth_fips205_128f_bad_hmsg_rejected

end Qsag
end

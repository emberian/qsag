module
/-
# Qsag.Top.Signing — End-to-End Composed Post-Quantum Signing Reductions and Refinements

Top-level composition module (zero `import all`) connecting:
1. Standard-model tweakable-hash `EUF-CMA` collision extraction & target-budget accounting
   (`ProdCollisionEvents`, `ProdCollisionAccounting`, `ProdCollisionExtraction`) into `Spec.GameBound`
   and `Spec.HashSigAssumptions`,
2. Upper-hypertree cache observational equivalence (`SignatureOutputAndCacheLaws`) lifted into a
   constructive `Spec.Refines` (`waistbandCachedMachine ⊑ statelessSignMachine`) witness,
3. `cSHAKE256` sponge domain separation (`SpongeFramingAndDomainSep`) and polynomial-basis SPN
   tweakable chain evaluation (`ParallelSeededSpnPolyBasis` + `Math.Gf2Pow128`), and
4. Constant-time assembly / translation-validation / speculative-safety guarantees
   (`ElfFunctionalEquiv`, `ConstantTimeIsa`, `SydTvTranslationValidation`, `FaultAndSpeculativeSafety`).
-/

public import Qsag.Spec.Primitives
public import Qsag.Spec.Refines
public import Qsag.Spec.GameBound
public import Qsag.Spec.Assumptions
public import Qsag.Spec.IdealSign
public import Qsag.Math.Gf2Pow128
public import Qsag.ProdCollisionEvents
public import Qsag.ProdCollisionAccounting
public import Qsag.ProdCollisionExtraction
public import Qsag.ProdAdaptiveTcrReduction
public import Qsag.AdvancedMpcAndCreds
public import Qsag.BaggyAndRss256Security
public import Qsag.HybridAddrPolicyAndFullPresetSecurity
public import Qsag.ProductionCoinReduction
public import Qsag.SpongeFramingAndDomainSep
public import Qsag.ParallelSeededSpnPolyBasis
public import Qsag.ParallelSeededPublicPermutation
public import Qsag.ParallelSeededPublicPermutationGame
public import Qsag.QromPreprocessingGame
public import Qsag.SpnCommittedDifferential
public import Qsag.SpnWalshHull
public import Qsag.SignatureOutputAndCacheLaws
public import Qsag.ElfFunctionalEquiv
public import Qsag.ConstantTimeIsa
public import Qsag.IsaCosim
public import Qsag.SydTvTranslationValidation
public import Qsag.FaultAndSpeculativeSafety
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Top

open scoped Qsag.Spec

set_option autoImplicit false

/-! ## 1. Standard-Model `EUF-CMA` Reduction to `ITSR + SM-DT-TCR + SM-DT-PRE` in `Spec.GameBound` -/

/-- **End-to-End Production `EUF-CMA` Concrete `GameBound` (`production_euf_cma_gameBound`)**:
    Composes `ProdCollisionEvents.prodEufCmaWin_classified` and `ProdCollisionAccounting.prodTcrOutput_target_budget`
    with `Spec.HashSigAssumptions.forger_bound` over any finite coin space `Fin n`:
    1. Bounds `forgerGame.winProb ≤ A.totalBound` (`εItsr + εTcr + εPre`) in canonical `Spec.RatBound`, and
    2. Certifies that whenever `prodTcrOutput` extracts a target-collision pair `(t, forged)` on tape `ω`,
       `t` belongs to the explicit `prodPathTargets` candidate set of size `≤ prodPathTargetCount` and
       passes `prodTcrCheck = true`! -/
theorem production_euf_cma_gameBound {n : Nat}
    (hPos : 0 < n)
    (suite : Qsag.TweakableHashSuite) (params : Qsag.PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16)
    (game : Fin n → Qsag.ProdEufCmaOutcome)
    (hOneTime : ∀ ω : Fin n, params.statefulJorts = true →
      ∀ q, q ∈ (game ω).queries → ∀ q', q' ∈ (game ω).queries → q.epoch = q'.epoch → q = q')
    (εItsr εTcr εPre : Qsag.Spec.RatBound)
    (hItsr : Qsag.Spec.GameBound
      (Qsag.Spec.FinGame.mk hPos (fun ω => Qsag.prodItsrEvent suite params hw (game ω) (hOneTime ω))).winProb
      εItsr)
    (hTcr : Qsag.Spec.GameBound
      (Qsag.Spec.FinGame.mk hPos (fun ω => Qsag.prodTcrEvent suite params hw (game ω) (hOneTime ω))).winProb
      εTcr)
    (hPre : Qsag.Spec.GameBound
      (Qsag.Spec.FinGame.mk hPos (fun ω => Qsag.prodPreEvent suite params hw (game ω) (hOneTime ω))).winProb
      εPre) :
    let forgerGame : Qsag.Spec.FinGame n :=
      Qsag.Spec.FinGame.mk hPos (fun ω => Qsag.prodEufCmaWin suite params (game ω))
    Qsag.Spec.GameBound forgerGame.winProb ((εItsr.add εTcr).add εPre) ∧
    (∀ (ω : Fin n) (t : Qsag.ProdTargetIdx) (forged : List UInt8),
      Qsag.prodTcrOutput suite params hw (game ω) (hOneTime ω) = some (t, forged) →
      (prodPathTargets params (Qsag.productionSigningLog suite params (game ω).sk (game ω).queries)
        (game ω).sigStar.leafGlobalIdx
        (Qsag.prodSigForsIdxs suite params (Qsag.derivePublicKey suite params (game ω).sk)
          (game ω).msgStar (game ω).sigStar)).length ≤
        Qsag.prodPathTargetCount params (game ω).queries.length ∧
      Qsag.prodTcrCheck suite params (game ω).sk (game ω).sigStar.leafGlobalIdx t forged = true) := by
  intro forgerGame
  let assumptions : Qsag.Spec.HashSigAssumptions n :=
    { itsr := ⟨0, εItsr, Qsag.Spec.FinGame.mk hPos (fun ω => Qsag.prodItsrEvent suite params hw (game ω) (hOneTime ω)), hItsr⟩
      tcr  := ⟨0, εTcr,  Qsag.Spec.FinGame.mk hPos (fun ω => Qsag.prodTcrEvent suite params hw (game ω) (hOneTime ω)), hTcr⟩
      pre  := ⟨0, εPre,  Qsag.Spec.FinGame.mk hPos (fun ω => Qsag.prodPreEvent suite params hw (game ω) (hOneTime ω)), hPre⟩ }
  have hBound : Qsag.Spec.GameBound forgerGame.winProb assumptions.totalBound :=
    assumptions.forger_bound forgerGame
      (fun ω hWin => Qsag.prodEufCmaWin_classified suite params hw (game ω) (hOneTime ω) hWin)
  refine ⟨hBound, ?_⟩
  intro ω t forged hOut
  obtain ⟨_, hLenLe, hChk⟩ :=
    Qsag.prodTcrOutput_target_budget suite params hw (game ω) (hOneTime ω) t forged hOut
  exact ⟨hLenLe, hChk⟩

/-! ## 2. Upper-Hypertree Cache Refinement (`waistbandCachedMachine ⊑ statelessSignMachine`) -/

/-- Input tuple `(msg, optRand, leafGlobalIdx)` for single-step hypertree signing. -/
structure SingleSignInput where
  msg : List UInt8
  optRand : List UInt8
  leafGlobalIdx : Nat

/-- Concrete `Spec.Machine` executing cached upper-hypertree signing (`evalWaistbandSignStep`). -/
def waistbandCachedSignMachine
    (suite : Qsag.TweakableHashSuite) (params : Qsag.PqHashParams)
    (sk : Qsag.PqSecretKey) (maxGrind topL : Nat) :
    Qsag.Spec.Machine Qsag.WaistbandTopLCache SingleSignInput (Option Qsag.PqHashSig) where
  Init c := c = Qsag.WaistbandTopLCache.empty
  step c inp :=
    let res := Qsag.evalWaistbandSignStep suite params sk inp.msg inp.optRand inp.leafGlobalIdx maxGrind topL c
    some res
  errStep c _ := c

/-- Abstract stateless `Spec.Machine` recomputing every hypertree layer from scratch (`evalSingleSign`). -/
def statelessReferenceSignMachine
    (suite : Qsag.TweakableHashSuite) (params : Qsag.PqHashParams)
    (sk : Qsag.PqSecretKey) (maxGrind : Nat) :
    Qsag.Spec.Machine Unit SingleSignInput (Option Qsag.PqHashSig) where
  Init _ := True
  step _ inp :=
    some ((), Qsag.evalSingleSign suite params sk inp.msg inp.optRand inp.leafGlobalIdx maxGrind)
  errStep _ _ := ()

/-- **Upper-Hypertree Cache Forward Refinement (`waistbandCache_refines_stateless`)**:
    When `topL < params.numLayers`, the stateful top-`L` cache machine refines the stateless
    reference machine (`waistbandCachedSignMachine ... ⊑ statelessReferenceSignMachine ...`),
    preserving exact outputs across arbitrary multi-turn signing traces! -/
def waistbandCache_refines_stateless
    (suite : Qsag.TweakableHashSuite) (params : Qsag.PqHashParams)
    (sk : Qsag.PqSecretKey) (maxGrind topL : Nat)
    (hTopL : topL < params.numLayers) :
    waistbandCachedSignMachine suite params sk maxGrind topL ⊑
      statelessReferenceSignMachine suite params sk maxGrind :=
  Qsag.Spec.LockstepSim.toRefines
    { Inv := fun cache =>
        Qsag.WaistbandCacheSound suite params sk (Qsag.derivePublicKey suite params sk).pkRoot maxGrind topL cache
      abs := fun _ => ()
      init_inv := fun {c₀} hInit => by
        rw [hInit]
        exact ⟨Qsag.waistbandCacheSound_empty suite params sk
          (Qsag.derivePublicKey suite params sk).pkRoot maxGrind topL hTopL, trivial⟩
      step_eq := fun {cache} inp hSound => by
        dsimp only [waistbandCachedSignMachine, statelessReferenceSignMachine]
        obtain ⟨hSound', hOutEq⟩ :=
          Qsag.evalWaistbandSignStep_eq_evalSingleSign suite params sk
            inp.msg inp.optRand inp.leafGlobalIdx maxGrind topL cache hSound
        exact ⟨hSound', congrArg (fun o => some ((), o)) hOutEq.symm⟩ }

theorem waistbandCache_preserves_multiturn_traces
    (suite : Qsag.TweakableHashSuite) (params : Qsag.PqHashParams)
    (sk : Qsag.PqSecretKey) (maxGrind topL : Nat)
    (hTopL : topL < params.numLayers)
    {tr : List (SingleSignInput × Option Qsag.PqHashSig)}
    (hAdmits : (waistbandCachedSignMachine suite params sk maxGrind topL).AdmitsTrace tr) :
    (statelessReferenceSignMachine suite params sk maxGrind).AdmitsTrace tr :=
  (waistbandCache_refines_stateless suite params sk maxGrind topL hTopL).preserve_admitsTrace hAdmits

/-! ## 3. Sponge Domain Separation, SPN Polynomial-Basis Bridge, and Constant-Time ISA Safety -/

/-- **Sponge Domain Disjointness + Polynomial-Basis SPN + Five-Way `𝔽_{2^{128}}` Agreement
    (`sponge_and_spn_poly_basis_composition`)**:
    Connects `SpongeFramingAndDomainSep.qsag_tags_sponge_domains_disjoint`,
    `ParallelSeededSpnPolyBasis.rustParallelChainStep_eq_tower`, and
    `Math.gf2Pow128_five_way_mul_agreement` into one unified hash-primitive theorem. -/
theorem sponge_and_spn_poly_basis_composition
    (m₁ m₂ : List UInt8)
    (hash32 : List UInt8 → List (List UInt8) → List UInt8)
    (pkSeed : List UInt8) (epoch chainIdx : Nat) (step : UInt8) (cur : List UInt8)
    (a b : BitVec 128) :
    Qsag.absorbPayload 136 Qsag.domCshake256 (Qsag.cshakePrefix [] Qsag.qsagTagCanopyLeaf ++ m₁) ≠
      Qsag.absorbPayload 136 Qsag.domCshake256 (Qsag.cshakePrefix [] Qsag.qsagTagCanopyNode ++ m₂) ∧
    Qsag.absorbPayload 136 Qsag.domCshake256 (Qsag.cshakePrefix [] Qsag.qsagTagCanopyLeaf ++ m₁) ≠
      Qsag.absorbPayload 136 Qsag.domCshake256 (Qsag.cshakePrefix [] Qsag.qsagTagFiatShamir ++ m₂) ∧
    Qsag.rustParallelChainStep hash32 pkSeed epoch chainIdx step cur =
      Qsag.rustLanesToBytes32 (Qsag.psiTower128Pair
        (Qsag.spnDaviesMeyer48 Qsag.gf128MdsATower Qsag.gf128MdsBTower
          (fun i => Qsag.polyToTower128Pair
            (Qsag.rustSpnRoundConstants hash32
              (Qsag.rustDeriveChainTweak hash32 pkSeed epoch chainIdx step) i))
          (Qsag.polyToTower128Pair (Qsag.rustBytes32ToLanes cur)))) ∧
    (Qsag.Math.Gf2Pow128.mul ⟨a⟩ ⟨b⟩).bits =
      Qsag.SimdBinaryEquiv.fastRemainder (Qsag.pclmulqdqFourProduct256 a b) := by
  obtain ⟨hD1, hD2, _⟩ := Qsag.qsag_tags_sponge_domains_disjoint m₁ m₂
  have hSpn := Qsag.rustParallelChainStep_eq_tower hash32 pkSeed epoch chainIdx step cur
  obtain ⟨_, _, _, hClmul, _⟩ := Qsag.Math.gf2Pow128_five_way_mul_agreement a b
  exact ⟨hD1, hD2, hSpn, hClmul⟩

/-- **Translation-Validated Zeroization & Constant-Time Stack-Return Non-Interference
    (`isa_zeroize_and_ret_ct_composition`)**:
    Composes `SydTv.ctMemzeroX86PosCert_flattened` (Sewell-style cut-graph loop translation validation
    for x86-64 `ct_memzero` with matching leakage trace) with `ConstantTimeIsa.checkX86RetStackPop_sound`
    (public `rsp` stack-return leakage non-interference). -/
theorem isa_zeroize_and_ret_ct_composition
    (sLoop : Qsag.X86State) (n : Nat) (hn : 0 < n) (hbound : n < 2 ^ 64)
    (memPol : BitVec 64 → Qsag.ConstantTimeIsa.SecLabel)
    (τ τ' : Qsag.ConstantTimeIsa.X86TaintState) (pc : Nat)
    (hCheck : Qsag.ConstantTimeIsa.checkX86RetStackPop τ = some τ')
    (s₁ s₂ : Qsag.ConstantTimeIsa.X86State)
    (hLow : Qsag.ConstantTimeIsa.X86LowEq memPol τ s₁ s₂)
    (hRetPub : memPol (s₁.gpr .rsp) = .pub) :
    Qsag.SydTv.FlattenedLoopRefines (Qsag.SydTv.ctMemzeroX86PosCert sLoop n hn hbound) ∧
    (Qsag.ConstantTimeIsa.execX86RetStackPop pc s₁).2 =
      (Qsag.ConstantTimeIsa.execX86RetStackPop pc s₂).2 :=
  ⟨Qsag.SydTv.ctMemzeroX86PosCert_flattened sLoop n hn hbound,
   (Qsag.ConstantTimeIsa.checkX86RetStackPop_sound memPol τ τ' pc hCheck s₁ s₂ hLow hRetPub).1⟩

/-! ## 4. Adaptive Tree Query Budgets, Prefix-Free Frontier FTS, and Production Coin Toss -/

/-- **Adaptive Tree Query Budgets, Prefix-Free Frontier FTS, and Coin-Toss Composition
    (`adaptive_within_and_compact1122_signing_chain`)**:
    Composes `ProdAdaptiveTcrReduction` (`evalProdAdaptiveTree_budgets`, `corduroyCustody128_target_pool_budget`),
    `AdvancedMpcAndCreds.frontierAntichain_paths_prefixFree`,
    `HybridSecurity.all_frontier_profiles`, and
    `ProductionCoinReduction` (`program_bound`, `honest_concrete`). -/
theorem adaptive_within_and_compact1122_signing_chain
    {qh qs_max : Nat}
    {α : Type} (rawHash : List UInt8 → List UInt8)
    (signOracle : Qsag.ProdSigningQuery → Option Qsag.PqHashSig)
    {prog : Qsag.ProdAdaptiveTree α} (hDual : Qsag.ProdDualBounded qh qs_max prog)
    (antichain : Qsag.FrontierAntichain)
    (fProf : Qsag.HybridSecurity.FrontierProfile)
    (coinCtx : Qsag.ProductionCoinContext)
    (coinEntries : List Qsag.ProductionCoinReduction.Entry)
    (hCoinHonest : ∀ e ∈ coinEntries, e.opened = e.share) :
    ((Qsag.evalProdAdaptiveTree rawHash signOracle prog).2.1.length ≤ qh ∧
     (Qsag.evalProdAdaptiveTree rawHash signOracle prog).2.2.length ≤ qs_max ∧
     Qsag.prodPathTargetCount Qsag.corduroyCustody128Params (2 ^ 12) = 35690) ∧
    (Qsag.IsPrefixFreeAntichain antichain.paths ∧
     ((Qsag.HybridSecurity.frontierParams fProf).len + 1) *
       (Qsag.HybridSecurity.frontierParams fProf).nodeBytes +
       ((Qsag.HybridSecurity.frontierParams fProf).counterBits + 7) / 8 =
       Qsag.HybridSecurity.frontierWireBytes fProf) ∧
    (Qsag.QueryBounded (coinEntries.length + (coinEntries.length + 1))
       (Qsag.ProductionCoinReduction.program coinCtx coinEntries) ∧
     Qsag.ProductionCoinReduction.run Qsag.ProductionCoinReduction.concrete coinCtx coinEntries =
       some (Qsag.productionCoinDerive coinCtx
         (Qsag.ProductionCoinReduction.combinedShares coinEntries 0))) := by
  have hTree := Qsag.evalProdAdaptiveTree_budgets rawHash signOracle hDual
  obtain ⟨hCordPool, _⟩ := Qsag.corduroyCustody128_target_pool_budget
  have hPf := Qsag.frontierAntichain_paths_prefixFree antichain
  obtain ⟨hWire, _⟩ := Qsag.HybridSecurity.all_frontier_profiles fProf
  exact ⟨⟨hTree.1, hTree.2, hCordPool⟩,
         ⟨hPf, hWire⟩,
         ⟨Qsag.ProductionCoinReduction.program_bound coinCtx coinEntries,
          Qsag.ProductionCoinReduction.honest_concrete coinCtx coinEntries hCoinHonest⟩⟩

/-! ## 5. Public-Permutation QROM Game, Salted Preprocessing, SPN Cryptanalysis, and x86 Strict Cosim -/

set_option exponentiation.threshold 512 in
/-- **Public-Permutation QROM Isometry, Salted Preprocessing, 48-Round SPN Hull, and Strict x86 Cosim
    (`public_spn_qrom_differential_walsh_and_isa_cosim`)**:
    Composes `ParallelSeededPublicPermutation` + `ParallelSeededPublicPermutationGame`,
    `QromPreprocessingGame.freshSalt_node_requests_bound`,
    `SpnCommittedDifferential.spn48_davies_meyer_committed_pair_collision_atLeast_250_bits`,
    `SpnWalshHull.walsh_trail_product_below_parseval_floor`, and
    `IsaCosim.run_verified_code_is_strict`. -/
theorem public_spn_qrom_differential_walsh_and_isa_cosim
    {anc q kSalt : Nat}
    (hash32 : List UInt8 → List (List UInt8) → List UInt8)
    (addr : Qsag.PublicChainAddress) (cur : List UInt8)
    (perm : Qsag.PublicPermutation Qsag.PublicSpnState)
    (qState : Qsag.QVec (2 ^ 257) 256 anc)
    (spnAdv : Qsag.PublicSpnPreimageAdversary anc q)
    (challenge : Qsag.PublicSpnState)
    (seeds : Fin kSalt → List UInt8) (suite : Qsag.TweakableHashSuite) (adrs : Qsag.HashAdrs)
    (table : List (Fin kSalt × ((List UInt8 × List UInt8) × (List UInt8 × List UInt8))))
    (mds : Qsag.ValidSpnMdsPair 7) (keys : List Qsag.Tower128) (hNd : keys.Nodup)
    (s₁ s₂ : Qsag.Tower128 × Qsag.Tower128) (hNe : s₁ ≠ s₂)
    (fuel : Nat) (code : List UInt8) (x86St : Qsag.X86State) (flags : IsaCosim.Flags)
    (decodedProg : List (Qsag.DecodedInstr Qsag.X86Instr))
    (hDec : Qsag.decodeX86Stream code = some decodedProg) :
    (Qsag.rustParallelChainStep hash32 addr.pkSeed addr.epoch.val addr.chainIdx.val addr.step cur =
      Qsag.rustLanesToBytes32
        (Qsag.publicSpnFeedForward (Qsag.publicChainPermutation hash32 addr)
          (Qsag.rustBytes32ToLanes cur)) ∧
     Qsag.QVec.stateNormSq (Qsag.publicSpnCoherentQuery perm qState) = Qsag.QVec.stateNormSq qState ∧
     (Qsag.Spec.RatBound.ofBudget
       (Qsag.publicSpnPreimageProbability perm spnAdv challenge)).le
       (Qsag.Spec.RatBound.ofBudget Qsag.RatBound.one)) ∧
    (Qsag.qsum kSalt
       (Qsag.PreprocessingGame.tableWin (fun salt pair => decide
         (pair.1 ≠ pair.2 ∧
           Qsag.thNodeH suite (seeds salt) adrs pair.1.1 pair.1.2 =
           Qsag.thNodeH suite (seeds salt) adrs pair.2.1 pair.2.2)) table) ≤ table.length) ∧
    (Qsag.spnDmCollisionCount keys mds.mdsA mds.mdsB s₁ s₂ ≤
       36 * (keys.length * keys.length) * (keys.length * keys.length) ^ 46 ∧
     36 ^ 72 * 2 ^ 256 < (2 ^ 128) ^ 72 ∧
     IsaCosim.run fuel code x86St flags = IsaCosim.runWith false fuel code x86St flags) := by
  have hFeed := Qsag.rustParallelChainStep_eq_publicFeedForward hash32 addr cur
  have hIso := Qsag.publicSpnCoherentQuery_isometry perm qState
  have hProbLe := (Qsag.Spec.RatBound.ofBudget_le_iff _ Qsag.RatBound.one).mpr
    (Qsag.publicSpnPreimageProbability_le_one perm spnAdv challenge)
  exact ⟨⟨hFeed, hIso, hProbLe⟩,
         Qsag.PreprocessingGame.freshSalt_node_requests_bound seeds suite adrs table,
         ⟨Qsag.spn48_davies_meyer_committed_pair_collision_count_le mds keys hNd s₁ s₂ hNe,
          Qsag.walsh_trail_product_below_parseval_floor,
          IsaCosim.run_verified_code_is_strict fuel code x86St flags decodedProg hDec⟩⟩

#verify_constructive
  Qsag.Top.production_euf_cma_gameBound
  Qsag.Top.waistbandCache_preserves_multiturn_traces
  Qsag.Top.sponge_and_spn_poly_basis_composition
  Qsag.Top.isa_zeroize_and_ret_ct_composition
  Qsag.Top.adaptive_within_and_compact1122_signing_chain
  Qsag.Top.public_spn_qrom_differential_walsh_and_isa_cosim

end Qsag.Top
end

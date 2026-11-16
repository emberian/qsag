module
public import Qsag.Protocol.Signing.PorsFpSecurity
public import Qsag.Exec.Rss256OneCorruptViewPrivacy
public import Qsag.Exec.RssSlhFullSecurityUc
public import Qsag.Machine.Gf128ClmulLoopAgreement
/-
# Qsag.Top.Signing — End-to-End Composed Post-Quantum Signing Reductions and Refinements

Top-level composition module (zero `import all`) connecting:
1. Tweakable-hash `EUF-CMA` collision extraction & target-budget accounting
   (`ProdCollisionEvents`, `ProdCollisionAccounting`, `ProdCollisionExtraction`) into `Spec.GameBound`
   through `Spec.event_le_three_reductions`: the forger's winning probability is at most the sum
   of the probabilities of three extractor events on the same run (no reduction of those events
   to hardness experiments),
2. Upper-hypertree cache observational equivalence (`SignatureOutputAndCacheLaws`) lifted into a
   constructive `Spec.Refines` (`waistbandCachedMachine ⊑ statelessSignMachine`) witness,
3. Encoding separation of the `cSHAKE256` customization tags (`Oracle.Sponge`: the complete
   padded block sequences absorbed under different `QSAG.*` tags differ; this is a statement
   about encodings, not about disjoint permutation queries and not a sponge or
   ideal-permutation security reduction) and polynomial-basis SPN tweakable chain evaluation
   (`Oracle.Spn` + `Math.Gf2Pow128`), and
4. Constant-time assembly / translation-validation / speculative-safety guarantees
   (`ElfFunctionalEquiv`, `ConstantTimeIsa`, `SydTvTranslationValidation`, `FaultAndSpeculativeSafety`),
5. The production signer and verifier as a `Spec.SigScheme` (`productionSigScheme`) and the
   refinement of the epoch-latched production signer into `Spec.idealSignMachine`
   (`productionLatchedSigner_refines_idealSign`): every emitted signature is accepted by
   `verifyProductionPqHashSig` under the derived public key, epochs are strictly increasing in
   stateful mode, and a failed signing consumes its epoch.
-/

public import Qsag.Spec.Primitives
public import Qsag.Spec.Refines
public import Qsag.Spec.GameBound
public import Qsag.Spec.Assumptions
public import Qsag.Spec.IdealSign
public import Qsag.Math.Gf2Pow128
public import Qsag.Protocol.Signing.ProdCollision
public import Qsag.Protocol.Signing.ProdHashReductions
public import Qsag.Protocol.Signing.ExecEufCmaClosedGame
public import Qsag.Protocol.Signing.PreprocessingSeedSeparation
public import Qsag.Protocol.Signing.FrontierCompact1122AndCorduroySecurity
public import Qsag.Protocol.Credentials.AdvancedMpcAndCreds
public import Qsag.Protocol.Threshold.BaggyAndRss256Security
public import Qsag.Protocol.Signing.HybridAddrPolicyAndFullPresetSecurity
public import Qsag.Protocol.Threshold.ProductionCoinReduction
public import Qsag.Oracle.Sponge
public import Qsag.Oracle.Spn
public import Qsag.Oracle.Qrom
public import Qsag.Protocol.Signing.SignatureOutputAndCacheLaws
public import Qsag.Machine.ElfFunctionalEquiv
public import Qsag.Machine.ConstantTimeIsa
public import Qsag.Machine.IsaCosim
public import Qsag.Machine.SydTvTranslationValidation
public import Qsag.Machine.FaultAndSpeculativeSafety
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Top

open scoped Qsag.Spec

set_option autoImplicit false

/-! ## 1. Production `EUF-CMA`: the Forger Is Bounded by Three Extractor-Event Probabilities

The three events are the outputs of the collision extractor on the forger's own run
(`prodItsrEvent`, `prodTcrEvent`, `prodPreEvent`). The hypotheses `hItsr`, `hTcr`, `hPre` bound
the probabilities of those events. They are not the `ITSR`, `SM-DT-TCR` and `SM-DT-PRE`
experiments of `Spec.Assumptions`, and nothing in this section reduces an event to one of them.
The bound by adversaries that see only the public key and the oracles is
`jorts_baggy_closed_euf_cma_keyed_target_bound` (`Protocol.Signing.ExecEufCmaClosedGame`,
restated in `Top.ClosedProtocolReductions`). -/

/-- **End-to-End Production `EUF-CMA` Concrete `GameBound` (`production_euf_cma_gameBound`)**:
    Composes `ProdCollisionEvents.prodEufCmaWin_classified` and `ProdCollisionAccounting.prodTcrOutput_target_budget`
    with `Spec.event_le_three_reductions` over any finite coin space `Fin n`:
    1. Bounds `forgerGame.winProb ≤ εItsr + εTcr + εPre` in canonical `Spec.RatBound`, where the
       three `ε` bound the probabilities of the three extractor events on the same run, and
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
      Qsag.prodTcrCheck suite params (game ω).sk (game ω).sigStar.leafGlobalIdx t forged = true ∧
      (params.statefulJorts = false →
        (prodPathTargets params (Qsag.productionSigningLog suite params (game ω).sk (game ω).queries)
          (game ω).sigStar.leafGlobalIdx
          (Qsag.prodSigForsIdxs suite params (Qsag.derivePublicKey suite params (game ω).sk)
            (game ω).msgStar (game ω).sigStar)).length ≤
          Qsag.prodPathTargetCount params (game ω).queries.length)) := by
  intro forgerGame
  have hBound : Qsag.Spec.GameBound forgerGame.winProb ((εItsr.add εTcr).add εPre) :=
    Qsag.Spec.event_le_three_reductions forgerGame
      (Qsag.Spec.FinGame.mk hPos (fun ω => Qsag.prodItsrEvent suite params hw (game ω) (hOneTime ω)))
      (Qsag.Spec.FinGame.mk hPos (fun ω => Qsag.prodTcrEvent suite params hw (game ω) (hOneTime ω)))
      (Qsag.Spec.FinGame.mk hPos (fun ω => Qsag.prodPreEvent suite params hw (game ω) (hOneTime ω)))
      (fun ω hWin => Qsag.prodEufCmaWin_classified suite params hw (game ω) (hOneTime ω) hWin)
      hItsr hTcr hPre
  refine ⟨hBound, ?_⟩
  intro ω t forged hOut
  obtain ⟨_, hLenLe, hChk⟩ :=
    Qsag.prodTcrOutput_target_budget suite params hw (game ω) (hOneTime ω) t forged hOut
  exact ⟨hChk, fun _ => hLenLe⟩

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

/-! ## 3. Customization-Tag Encoding Separation, SPN Polynomial-Basis Bridge, and Constant-Time ISA Safety -/

/-- **Customization-Tag Encoding Separation + Polynomial-Basis SPN + Five-Way `𝔽_{2^{128}}`
    Agreement (`sponge_and_spn_poly_basis_composition`)**:
    Connects `Qsag.qsag_tags_sponge_domains_disjoint` (`Oracle.Sponge`),
    `Qsag.rustParallelChainStep_eq_tower` (`Oracle.Spn`), and
    `Math.gf2Pow128_five_way_mul_agreement`. The first two conjuncts say that the complete
    padded `cSHAKE256` block sequences absorbed under the `CANOPY.LEAF`, `CANOPY.NODE` and
    `FS` tags are different for all payloads. They do not say that the permutation queries
    made while absorbing them are disjoint, and they are not a sponge or ideal-permutation
    indifferentiability statement. -/
theorem sponge_and_spn_poly_basis_composition
    (m₁ m₂ : List UInt8)
    (hash32 : List UInt8 → List (List UInt8) → Nat → List UInt8)
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
     Qsag.corduroyCustody128Params.productionWellFormed = true ∧
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
  obtain ⟨_, _, hCordWf, _⟩ := Qsag.corduroy_real_profiles_audit
  obtain ⟨hCordPool, _⟩ := Qsag.corduroyCustody128_target_pool_budget
  have hPf := Qsag.frontierAntichain_paths_prefixFree antichain
  obtain ⟨hWire, _⟩ := Qsag.HybridSecurity.all_frontier_profiles fProf
  exact ⟨⟨hTree.1, hTree.2, hCordWf, hCordPool⟩,
         ⟨hPf, hWire⟩,
         ⟨Qsag.ProductionCoinReduction.program_bound coinCtx coinEntries,
          Qsag.ProductionCoinReduction.honest_concrete coinCtx coinEntries hCoinHonest⟩⟩

/-! ## 5. Public-Permutation QROM Game, Salted Preprocessing, SPN Cryptanalysis, and x86 Strict Cosim -/

set_option exponentiation.threshold 512 in
/-- **Public-Permutation QROM Isometry, Salted Preprocessing, 48-Round SPN Hull, and Strict x86 Cosim
    (`public_spn_qrom_differential_walsh_and_isa_cosim`)**:
    Composes the public-permutation feed-forward (`Oracle.Spn`) and coherent-query isometry
    (`Oracle.Qrom`),
    `PreprocessingGame.freshSalt_node_requests_bound` (`Protocol.Signing.PreprocessingSeedSeparation`),
    `spn48_davies_meyer_committed_pair_collision_count_le` and
    `walsh_trail_product_below_parseval_floor` (`Oracle.Spn`), and
    `IsaCosim.run_verified_code_is_strict`. -/
theorem public_spn_qrom_differential_walsh_and_isa_cosim
    {anc q kSalt : Nat}
    (hash32 : List UInt8 → List (List UInt8) → Nat → List UInt8)
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

/-! ## 6. The Epoch-Latched Production Signer Refines `Spec.idealSignMachine` -/

/-- The production hash-signature scheme as a `Spec.SigScheme`, at fixed signer randomness
    `optRand` and grind limit `maxGrind`: key derivation `derivePublicKey`, signer
    `prodSignQuery`, verifier `verifyProductionPqHashSig`. Correctness is
    `prodSignQuery_verifies`.

    The scheme uses the one value `optRand` for every signature: `Spec.SigScheme.sign` has no
    randomness argument, so per-request signer randomness is not modelled and the refinement
    below is stated for each fixed `optRand` (the deterministic variant when `optRand` is the
    public seed). -/
@[expose] def productionSigScheme
    (suite : Qsag.TweakableHashSuite) (params : Qsag.PqHashParams)
    (optRand : List UInt8) (maxGrind : Nat) :
    Qsag.Spec.SigScheme Qsag.PqPublicKey Qsag.PqSecretKey Qsag.PqHashSig where
  derivePk := Qsag.derivePublicKey suite params
  sign sk ep msg := Qsag.prodSignQuery suite params sk ⟨msg, optRand, ep, maxGrind⟩
  verify := Qsag.verifyProductionPqHashSig suite params
  correct sk ep msg sig h :=
    Qsag.prodSignQuery_verifies suite params sk ⟨msg, optRand, ep, maxGrind⟩ sig h

/-- **The epoch-latched production signer refines the ideal signing machine.** The concrete
    machine runs `prodSignQuery` behind the latch `nextEpoch ≤ epoch ≤ nextEpoch + maxWindow`
    (all epochs when `stateful = false`) and moves the latch to `epoch + 1` on every admitted
    request. The ideal machine emits a candidate only when `verifyProductionPqHashSig` accepts
    it under `derivePublicKey suite params sk`. Accept/reject behaviour, outputs and epoch
    consumption on failure agree. -/
def productionLatchedSigner_refines_idealSign
    (suite : Qsag.TweakableHashSuite) (params : Qsag.PqHashParams)
    (optRand : List UInt8) (maxGrind : Nat) (sk : Qsag.PqSecretKey)
    (stateful : Bool) (maxWindow : Nat) :
    Qsag.Spec.latchedSignerMachine (productionSigScheme suite params optRand maxGrind) sk
        stateful maxWindow ⊑
      Qsag.Spec.idealSignMachine (productionSigScheme suite params optRand maxGrind)
        ((productionSigScheme suite params optRand maxGrind).derivePk sk) stateful maxWindow
        (fun req => (productionSigScheme suite params optRand maxGrind).sign sk req.epoch
          req.message) :=
  Qsag.Spec.latchedSigner_refines_ideal (productionSigScheme suite params optRand maxGrind) sk
    stateful maxWindow

/-- Every initialized trace of the stateful latched production signer consists of signatures
    accepted by `verifyProductionPqHashSig` under the derived public key, at strictly increasing
    epochs. -/
theorem productionLatchedSigner_trace_safe
    (suite : Qsag.TweakableHashSuite) (params : Qsag.PqHashParams)
    (optRand : List UInt8) (maxGrind : Nat) (sk : Qsag.PqSecretKey) (maxWindow : Nat)
    {tr : List (Qsag.Spec.SignRequest × Qsag.PqHashSig)}
    (hAdmits : (Qsag.Spec.latchedSignerMachine (productionSigScheme suite params optRand maxGrind)
      sk true maxWindow).AdmitsTrace tr) :
    (∀ p ∈ tr, Qsag.verifyProductionPqHashSig suite params (Qsag.derivePublicKey suite params sk)
      p.1.message p.2 = true) ∧
    tr.Pairwise (fun a b => a.1.epoch < b.1.epoch) :=
  Qsag.Spec.latchedSigner_trace_safe (productionSigScheme suite params optRand maxGrind) sk
    maxWindow hAdmits

#verify_constructive
  Qsag.Top.production_euf_cma_gameBound
  Qsag.Top.productionLatchedSigner_trace_safe
  Qsag.Top.waistbandCache_preserves_multiturn_traces
  Qsag.Top.sponge_and_spn_poly_basis_composition
  Qsag.Top.isa_zeroize_and_ret_ct_composition
  Qsag.Top.adaptive_within_and_compact1122_signing_chain
  Qsag.Top.public_spn_qrom_differential_walsh_and_isa_cosim

open Qsag

open CommRingOps

-- BEGIN COMPARATOR ROSTER
theorem hypertree_forgery_break_of_signingLog (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (queries : List PqSigningQuery) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hGeom : (params.w = 4 ∧ params.ell1 = 128) ∨ (params.w = 16 ∧ params.ell1 = 64))
    (hStateless : params.statefulJorts = false)
    (hLayers : params.numLayers ≤ 2 ^ 32)
    (hFresh : ∀ e ∈ signingOracleLog suite params sk queries, e.1 ≠ msgStar)
    (hAccept : verifyPqHashSig suite params (derivePublicKey suite params sk) msgStar sigStar = true) :
    ForsItsrBreak suite params (derivePublicKey suite params sk)
      (signingOracleLog suite params sk queries) msgStar sigStar ∨
    SmTcrBreak suite params sk (signingOracleLog suite params sk queries) ∨
    PreimageBreak suite params sk (signingOracleLog suite params sk queries) msgStar sigStar :=
  _root_.Qsag.hypertree_forgery_break_of_signingLog suite params sk queries msgStar sigStar hGeom hStateless hLayers hFresh hAccept

theorem hypertree_euf_cma_advantage_bound {Ω : Type} (suite : TweakableHashSuite)
    (params : PqHashParams)
    (hGeom : (params.w = 4 ∧ params.ell1 = 128) ∨ (params.w = 16 ∧ params.ell1 = 64))
    (hStateless : params.statefulJorts = false) (hLayers : params.numLayers ≤ 2 ^ 32)
    (coins : List Ω) (game : Ω → EufCmaOutcome) (isItsr isTcr isPre : Ω → Bool)
    (hItsr : ∀ ω, ForsItsrBreak suite params (derivePublicKey suite params (game ω).sk)
      (signingOracleLog suite params (game ω).sk (game ω).queries) (game ω).msgStar (game ω).sigStar →
      isItsr ω = true)
    (hTcr : ∀ ω, SmTcrBreak suite params (game ω).sk
      (signingOracleLog suite params (game ω).sk (game ω).queries) → isTcr ω = true)
    (hPre : ∀ ω, PreimageBreak suite params (game ω).sk
      (signingOracleLog suite params (game ω).sk (game ω).queries) (game ω).msgStar (game ω).sigStar →
      isPre ω = true) :
    hitCount (fun ω => eufCmaWin suite params (game ω)) coins ≤
      hitCount isItsr coins + hitCount isTcr coins + hitCount isPre coins :=
  _root_.Qsag.hypertree_euf_cma_advantage_bound suite params hGeom hStateless hLayers coins game isItsr isTcr isPre hItsr hTcr hPre

theorem forsItsrBreak_empty_log (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (msgStar : List UInt8) (sigStar : PqHashSig) :
    ¬ ForsItsrBreak suite params pk [] msgStar sigStar :=
  _root_.Qsag.forsItsrBreak_empty_log suite params pk msgStar sigStar

theorem eufCmaWin_rejects_signed_message (suite : TweakableHashSuite) (params : PqHashParams)
    (o : EufCmaOutcome) (sig : PqHashSig)
    (hSigned : (o.msgStar, sig) ∈ signingOracleLog suite params o.sk o.queries) :
    eufCmaWin suite params o = false :=
  _root_.Qsag.eufCmaWin_rejects_signed_message suite params o sig hSigned

theorem thresholdStatelessCheckedSign_eq_evalStatelessCheckedSign
    (suite : TweakableHashSuite) (params : PqHashParams)
    (o : PqHashMpcOracles) (sk : PqSecretKey) (msg optRand : List UInt8) (maxGrind : Nat)
    (hMatch : o.MatchesKey suite sk) :
    thresholdStatelessCheckedSign suite params o (derivePublicKeyMpc suite params o sk.pkSeed)
      msg optRand maxGrind =
      evalStatelessCheckedSign suite params sk msg optRand maxGrind :=
  _root_.Qsag.thresholdStatelessCheckedSign_eq_evalStatelessCheckedSign suite params o sk msg optRand maxGrind hMatch

theorem threshold_sig_perfectly_indistinguishable_from_single_signer
    (p : Fips205Params) (hWf : p.wellFormed = true) {skSeed skPrf pkSeed : List UInt8}
    (r₁ r₂ : SlhThresholdRun p skSeed skPrf pkSeed) (msgPrime optRand : List UInt8) :
    r₁.signBytes msgPrime optRand =
      encodeSlhSig (slhSignInternal p msgPrime (slhKeygenInternal p skSeed skPrf pkSeed).1 optRand) ∧
    r₁.signBytes msgPrime optRand = r₂.signBytes msgPrime optRand ∧
    slhKeygenMpc p r₁.oracles pkSeed = (slhKeygenInternal p skSeed skPrf pkSeed).2 ∧
    slhVerifyInternal p msgPrime
      (slhSignMpc p r₁.oracles msgPrime (slhKeygenMpc p r₁.oracles pkSeed) optRand)
      (slhKeygenInternal p skSeed skPrf pkSeed).2 = true :=
  _root_.Qsag.threshold_sig_perfectly_indistinguishable_from_single_signer p hWf r₁ r₂ msgPrime optRand

theorem rss_threshold_sig_independent_of_quorum_and_sharing
    (p : Fips205Params) (hWf : p.wellFormed = true) (q₁ q₂ : RssQuorum)
    {seed₁ prf₁ seed₂ prf₂ : RssByteShares}
    (hS₁ : seed₁.WellFormed) (hP₁ : prf₁.WellFormed) (hS₂ : seed₂.WellFormed) (hP₂ : prf₂.WellFormed)
    (hSeed : reconstructRssBytes seed₁ = reconstructRssBytes seed₂)
    (hPrf : reconstructRssBytes prf₁ = reconstructRssBytes prf₂)
    (pkSeed : List UInt8) (tape₁ tape₂ : Nat → Nat → Nat → Nat → RssPrfZeroSeeds)
    (msgPrime optRand : List UInt8) :
    rssQuorumSlhSignBytes p q₁ (q₁.views seed₁) (q₁.views prf₁) pkSeed tape₁ msgPrime optRand =
      encodeSlhSig (slhSignInternal p msgPrime
        (slhKeygenInternal p (reconstructRssBytes seed₁) (reconstructRssBytes prf₁) pkSeed).1 optRand) ∧
    rssQuorumSlhSignBytes p q₁ (q₁.views seed₁) (q₁.views prf₁) pkSeed tape₁ msgPrime optRand =
      rssQuorumSlhSignBytes p q₂ (q₂.views seed₂) (q₂.views prf₂) pkSeed tape₂ msgPrime optRand :=
  _root_.Qsag.rss_threshold_sig_independent_of_quorum_and_sharing p hWf q₁ q₂ hS₁ hP₁ hS₂ hP₂ hSeed hPrf pkSeed tape₁ tape₂ msgPrime optRand

theorem shamir_threshold_sig_independent_of_threshold_quorum_and_sharing
    {R₁ R₂ : Type} [LawfulCommRing R₁] [LawfulCommRing R₂]
    (p : Fips205Params) (hWf : p.wellFormed = true)
    (decode₁ : R₁ → UInt8) (t₁ : Nat) (Q₁ : ShamirQuorum R₁ t₁) (seedPolys₁ prfPolys₁ : List (List R₁))
    (hSD₁ : ∀ c ∈ seedPolys₁, c.length ≤ t₁) (hPD₁ : ∀ c ∈ prfPolys₁, c.length ≤ t₁)
    (decode₂ : R₂ → UInt8) (t₂ : Nat) (Q₂ : ShamirQuorum R₂ t₂) (seedPolys₂ prfPolys₂ : List (List R₂))
    (hSD₂ : ∀ c ∈ seedPolys₂, c.length ≤ t₂) (hPD₂ : ∀ c ∈ prfPolys₂, c.length ≤ t₂)
    (hSeed : shamirSecretBytes decode₁ seedPolys₁ = shamirSecretBytes decode₂ seedPolys₂)
    (hPrf : shamirSecretBytes decode₁ prfPolys₁ = shamirSecretBytes decode₂ prfPolys₂)
    (pkSeed : List UInt8) (o₁ o₂ : SlhMpcOracles)
    (hO₁ : o₁.MatchesKey p
      (shamirReconstructBytes decode₁ Q₁.lambdas (shamirQuorumShares Q₁.pts seedPolys₁))
      (shamirReconstructBytes decode₁ Q₁.lambdas (shamirQuorumShares Q₁.pts prfPolys₁)) pkSeed)
    (hO₂ : o₂.MatchesKey p
      (shamirReconstructBytes decode₂ Q₂.lambdas (shamirQuorumShares Q₂.pts seedPolys₂))
      (shamirReconstructBytes decode₂ Q₂.lambdas (shamirQuorumShares Q₂.pts prfPolys₂)) pkSeed)
    (msgPrime optRand : List UInt8) :
    thresholdSlhSignBytes p o₁ msgPrime (slhKeygenMpc p o₁ pkSeed) optRand =
      encodeSlhSig (slhSignInternal p msgPrime
        (slhKeygenInternal p (shamirSecretBytes decode₁ seedPolys₁)
          (shamirSecretBytes decode₁ prfPolys₁) pkSeed).1 optRand) ∧
    thresholdSlhSignBytes p o₁ msgPrime (slhKeygenMpc p o₁ pkSeed) optRand =
      thresholdSlhSignBytes p o₂ msgPrime (slhKeygenMpc p o₂ pkSeed) optRand :=
  _root_.Qsag.shamir_threshold_sig_independent_of_threshold_quorum_and_sharing p hWf decode₁ t₁ Q₁ seedPolys₁ prfPolys₁ hSD₁ hPD₁ decode₂ t₂ Q₂ seedPolys₂ prfPolys₂ hSD₂ hPD₂ hSeed hPrf pkSeed o₁ o₂ hO₁ hO₂ msgPrime optRand

theorem threshold_sig_hedged_statistical_distance_zero
    (p : Fips205Params) (hWf : p.wellFormed = true) {skSeed skPrf pkSeed : List UInt8}
    (N : Nat) (run : Fin N → SlhThresholdRun p skSeed skPrf pkSeed)
    (hedge : Fin N → List UInt8) (msgPrime : List UInt8) (D : List UInt8 → Bool) :
    natAbsDiff
      (qsum N (fun i => if D ((run i).signBytes msgPrime (hedge i)) then 1 else 0))
      (qsum N (fun i => if D (encodeSlhSig (slhSignInternal p msgPrime
        (slhKeygenInternal p skSeed skPrf pkSeed).1 (hedge i))) then 1 else 0)) = 0 :=
  _root_.Qsag.threshold_sig_hedged_statistical_distance_zero p hWf N run hedge msgPrime D

theorem parseArMember_subslice (rlib : Bytes) (m : ArMember)
    (hm : m ∈ parseArArchive rlib) : ArPayloadOk rlib m :=
  _root_.Qsag.parseArMember_subslice rlib m hm

theorem extractAllRlibFuncs_provenance (rlib : Bytes) (slice : ElfFuncSlice)
    (hMem : slice ∈ extractAllRlibFuncs rlib) :
    ∃ m ∈ parseArArchive rlib,
      m.payloadOffset + m.payloadSize ≤ rlib.len ∧
      slice.symSize > 0 ∧
      slice.symValue + slice.symSize ≤ slice.textSize ∧
      slice.textFileOffset + slice.textSize ≤ m.payloadSize ∧
      slice.code =
        rlib.slice (m.payloadOffset + (slice.textFileOffset + slice.symValue)) slice.symSize :=
  _root_.Qsag.extractAllRlibFuncs_provenance rlib slice hMem

theorem x86_rlib_extracted_slices :
    extractAllRlibFuncs x86RlibArchiveBytes = x86ExtractedSlices :=
  _root_.Qsag.x86_rlib_extracted_slices

theorem aarch64_rlib_extracted_slices :
    extractAllRlibFuncs aarch64RlibArchiveBytes = aarch64ExtractedSlices :=
  _root_.Qsag.aarch64_rlib_extracted_slices

theorem x86_rlib_extraction_detects_code_flip :
    (extractAllRlibFuncs
        (Bytes.ofNat x86RlibArchiveLen (x86RlibArchiveNat ^^^ (1 <<< (8 * 400))))).map
        ElfFuncSlice.code ≠
      x86ExtractedSlices.map ElfFuncSlice.code :=
  _root_.Qsag.x86_rlib_extraction_detects_code_flip

theorem checkElfSliceWithCert_sound {slice : ElfFuncSlice} {c : FuncContract} {cert : InvCert}
    (hCheck : checkElfSliceWithCert slice c cert = true) :
    ElfSliceThreeWayNISafe slice c :=
  _root_.Qsag.checkElfSliceWithCert_sound hCheck

theorem mutant_secret_branch_rejected :
    checkX86ThreeWayNI
      [0x48, 0x89, 0xF8, 0x48, 0x29, 0xF0, 0x74, 0x01, 0x90, 0xC3]
      (mkContract "mutant_secret_branch" [4]) = false :=
  _root_.Qsag.mutant_secret_branch_rejected

theorem mutant_secret_lut_rejected :
    checkX86ThreeWayNI
      [0x0F, 0xB6, 0x04, 0x37, 0xC3]
      (mkContract "mutant_secret_lut" [4, 7]) = false :=
  _root_.Qsag.mutant_secret_lut_rejected

theorem mutant_variable_shift_rejected :
    checkX86ThreeWayNI [0x48, 0xD3, 0xE0, 0xC3] (mkContract "mutant_shl_cl" [4]) = false ∧
    checkArm64ThreeWayNI
      [0x00, 0x20, 0xC1, 0x9A, 0xC0, 0x03, 0x5F, 0xD6]
      (mkContract "mutant_lslv" []) = false :=
  _root_.Qsag.mutant_variable_shift_rejected

theorem rlib_x86_every_symbol_three_way_ni_sound :
    (extractAllRlibFuncs x86RlibArchiveBytes).length = x86SymbolContracts.length ∧
    ∀ i : Nat, (hs : i < (extractAllRlibFuncs x86RlibArchiveBytes).length) →
      (hc : i < x86SymbolContracts.length) →
      ((extractAllRlibFuncs x86RlibArchiveBytes)[i]'hs).name =
        (x86SymbolContracts[i]'hc).symName ∧
      ElfSliceThreeWayNISafe ((extractAllRlibFuncs x86RlibArchiveBytes)[i]'hs)
        (x86SymbolContracts[i]'hc) :=
  _root_.Qsag.rlib_x86_every_symbol_three_way_ni_sound

theorem rlib_aarch64_every_symbol_three_way_ni_sound :
    (extractAllRlibFuncs aarch64RlibArchiveBytes).length = aarch64SymbolContracts.length ∧
    ∀ i : Nat, (hs : i < (extractAllRlibFuncs aarch64RlibArchiveBytes).length) →
      (hc : i < aarch64SymbolContracts.length) →
      ((extractAllRlibFuncs aarch64RlibArchiveBytes)[i]'hs).name =
        (aarch64SymbolContracts[i]'hc).symName ∧
      ElfSliceThreeWayNISafe ((extractAllRlibFuncs aarch64RlibArchiveBytes)[i]'hs)
        (aarch64SymbolContracts[i]'hc) :=
  _root_.Qsag.rlib_aarch64_every_symbol_three_way_ni_sound

theorem genuine_certificate_rejects_unwiped_neon_mutant :
    (match aarch64ExtractedSlices[3]? with
     | none => true
     | some slice =>
       checkArm64WithInv (patchBytesAt slice.code 0x104 [0x1F, 0x20, 0x03, 0xD5])
         (mkContract "qsag_asm_tower128_bdoz_mac_pmull" [0, 1, 2, 3]) aarch64InvCert03) = false :=
  _root_.Qsag.genuine_certificate_rejects_unwiped_neon_mutant

theorem certificate_not_transferable :
    certSliceAt x86ExtractedSlices x86SymbolContracts (x86InvCerts.drop 1) 0 = false :=
  _root_.Qsag.certificate_not_transferable

theorem ct_eq_32_x86_64_mc_refines :
    ∃ slice prog, findSliceByNameBytes x86ExtractedSlices ctEq32X86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 20 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        (runX86 prog fuel s).1.gpr.get 0 =
          (if ∀ i : Nat, i < 32 →
              s.mem (s.gpr.get 7 + UInt64.ofNat i) = s.mem (s.gpr.get 6 + UInt64.ofNat i)
            then 1 else 0) ∧
        (runX86 prog fuel s).1.mem = s.mem ∧
        (runX86 prog fuel s).1.gpr.get 1 = 0 ∧ (runX86 prog fuel s).1.gpr.get 2 = 0 ∧
        (runX86 prog fuel s).1.gpr.get 8 = 0 :=
  _root_.Qsag.ct_eq_32_x86_64_mc_refines

theorem ct_eq_32_aarch64_mc_refines :
    ∃ slice prog, findSliceByNameBytes aarch64ExtractedSlices ctEq32ArmName = some slice ∧
      decodeArm64Stream slice.code = some prog ∧
      ∀ (s : Arm64State) (fuel : Nat), s.pc = 0 → s.halted = false → 22 ≤ fuel →
        (runArm64 prog fuel s).1.halted = true ∧
        (runArm64 prog fuel s).1.gpr.get 0 =
          (if ∀ i : Nat, i < 32 →
              s.mem (s.gpr.get 0 + UInt64.ofNat i) = s.mem (s.gpr.get 1 + UInt64.ofNat i)
            then 1 else 0) ∧
        (runArm64 prog fuel s).1.mem = s.mem ∧
        (∀ r : Nat, 2 ≤ r → r ≤ 7 → (runArm64 prog fuel s).1.gpr.get r = 0) :=
  _root_.Qsag.ct_eq_32_aarch64_mc_refines

theorem ct_memzero_x86_64_mc_refines :
    ∃ slice prog, findSliceByNameBytes x86ExtractedSlices ctMemzeroX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 0 < (s.gpr.get 6).toNat →
        4 * (s.gpr.get 6).toNat + 4 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        (∀ i : Nat, i < (s.gpr.get 6).toNat →
          (runX86 prog fuel s).1.mem (s.gpr.get 7 + UInt64.ofNat i) = 0) ∧
        (∀ a : UInt64, (∀ i : Nat, i < (s.gpr.get 6).toNat → a ≠ s.gpr.get 7 + UInt64.ofNat i) →
          (runX86 prog fuel s).1.mem a = s.mem a) :=
  _root_.Qsag.ct_memzero_x86_64_mc_refines

theorem ct_memzero_aarch64_mc_refines :
    ∃ slice prog, findSliceByNameBytes aarch64ExtractedSlices ctMemzeroArmName = some slice ∧
      decodeArm64Stream slice.code = some prog ∧
      ∀ (s : Arm64State) (fuel : Nat), s.pc = 0 → s.halted = false → 0 < (s.gpr.get 1).toNat →
        3 * (s.gpr.get 1).toNat + 2 ≤ fuel →
        (runArm64 prog fuel s).1.halted = true ∧
        (∀ i : Nat, i < (s.gpr.get 1).toNat →
          (runArm64 prog fuel s).1.mem (s.gpr.get 0 + UInt64.ofNat i) = 0) ∧
        (∀ a : UInt64, (∀ i : Nat, i < (s.gpr.get 1).toNat → a ≠ s.gpr.get 0 + UInt64.ofNat i) →
          (runArm64 prog fuel s).1.mem a = s.mem a) :=
  _root_.Qsag.ct_memzero_aarch64_mc_refines

theorem ct_eq_bytes_x86_64_mc_refines :
    ∃ slice prog, findSliceByNameBytes x86ExtractedSlices ctEqBytesX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 0 < (s.gpr.get 2).toNat →
        8 * (s.gpr.get 2).toNat + 7 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        (runX86 prog fuel s).1.gpr.get 0 =
          (if ∀ i : Nat, i < (s.gpr.get 2).toNat →
              s.mem (s.gpr.get 7 + UInt64.ofNat i) = s.mem (s.gpr.get 6 + UInt64.ofNat i)
            then 1 else 0) ∧
        (runX86 prog fuel s).1.mem = s.mem ∧
        (runX86 prog fuel s).1.gpr.get 8 = 0 ∧ (runX86 prog fuel s).1.gpr.get 9 = 0 :=
  _root_.Qsag.ct_eq_bytes_x86_64_mc_refines

theorem goldilocks_add_ct_x86_64_mc_refines :
    ∃ slice prog, findSliceByNameBytes x86ExtractedSlices goldAddX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 17 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        ((runX86 prog fuel s).1.gpr.get 0).toNat =
          ((s.gpr.get 7).toNat + (s.gpr.get 6).toNat) % goldilocksPrime ∧
        (runX86 prog fuel s).1.mem = s.mem ∧
        (runX86 prog fuel s).1.gpr.get 1 = 0 ∧ (runX86 prog fuel s).1.gpr.get 8 = 0 ∧
        (runX86 prog fuel s).1.gpr.get 9 = 0 ∧ (runX86 prog fuel s).1.gpr.get 10 = 0 :=
  _root_.Qsag.goldilocks_add_ct_x86_64_mc_refines

theorem goldilocks_sub_ct_x86_64_mc_refines :
    ∃ slice prog, findSliceByNameBytes x86ExtractedSlices goldSubX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 23 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        ((runX86 prog fuel s).1.gpr.get 0).toNat =
          ((s.gpr.get 7).toNat + goldilocksPrime - (s.gpr.get 6).toNat % goldilocksPrime) %
            goldilocksPrime ∧
        (runX86 prog fuel s).1.mem = s.mem ∧
        (runX86 prog fuel s).1.gpr.get 1 = 0 ∧ (runX86 prog fuel s).1.gpr.get 6 = 0 ∧
        (runX86 prog fuel s).1.gpr.get 8 = 0 ∧ (runX86 prog fuel s).1.gpr.get 9 = 0 ∧
        (runX86 prog fuel s).1.gpr.get 10 = 0 :=
  _root_.Qsag.goldilocks_sub_ct_x86_64_mc_refines

theorem goldilocks_mul_ct_x86_64_mc_refines :
    ∃ slice prog, findSliceByNameBytes x86ExtractedSlices goldMulX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 25 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        ((runX86 prog fuel s).1.gpr.get 0).toNat =
          ((s.gpr.get 7).toNat * (s.gpr.get 6).toNat) % goldilocksPrime ∧
        (runX86 prog fuel s).1.mem = s.mem ∧
        (runX86 prog fuel s).1.gpr.get 1 = 0 ∧ (runX86 prog fuel s).1.gpr.get 2 = 0 ∧
        (runX86 prog fuel s).1.gpr.get 8 = 0 ∧ (runX86 prog fuel s).1.gpr.get 9 = 0 :=
  _root_.Qsag.goldilocks_mul_ct_x86_64_mc_refines

theorem goldilocks_mul_ct_aarch64_mc_refines :
    ∃ slice prog, findSliceByNameBytes aarch64ExtractedSlices goldMulArmName = some slice ∧
      decodeArm64Stream slice.code = some prog ∧
      ∀ (s : Arm64State) (fuel : Nat), s.pc = 0 → s.halted = false → 29 ≤ fuel →
        (runArm64 prog fuel s).1.halted = true ∧
        ((runArm64 prog fuel s).1.gpr.get 0).toNat =
          ((s.gpr.get 0).toNat * (s.gpr.get 1).toNat) % goldilocksPrime ∧
        (runArm64 prog fuel s).1.mem = s.mem ∧
        (∀ r : Nat, 2 ≤ r → r ≤ 8 → (runArm64 prog fuel s).1.gpr.get r = 0) :=
  _root_.Qsag.goldilocks_mul_ct_aarch64_mc_refines

theorem ct_eq_32_x86_64_mutant_refuted :
    ((findSliceByNameBytes x86ExtractedSlices ctEq32X86Name).bind
        (fun sl => decodeX86Stream (patchBytesAt sl.code 52 [0x83, 0xF0, 0x00]))).any
      (fun p => (runX86 p 20 (x86Init 0 64 0 0 0)).1.halted &&
        (runX86 p 20 (x86Init 0 64 0 0 0)).1.gpr.get 0 == 0) = true ∧
    (∀ i : Nat, i < 32 →
      (x86Init 0 64 0 0 0).mem ((x86Init 0 64 0 0 0).gpr.get 7 + UInt64.ofNat i) =
      (x86Init 0 64 0 0 0).mem ((x86Init 0 64 0 0 0).gpr.get 6 + UInt64.ofNat i)) :=
  _root_.Qsag.ct_eq_32_x86_64_mutant_refuted

theorem ct_eq_32_x86_64_secret_branch_rejected :
    (findSliceByNameBytes x86ExtractedSlices ctEq32X86Name).map
        (fun sl => (checkX86ThreeWayNI sl.code
            (mkContract "qsag_asm_ct_eq_32_x86_64" [4, 7, 6] [] [1, 2, 8]),
          checkX86ThreeWayNI (patchBytesAt sl.code 30 [0x74, 0x01, 0x90])
            (mkContract "qsag_asm_ct_eq_32_x86_64" [4, 7, 6] [] [1, 2, 8])))
      = some (true, false) :=
  _root_.Qsag.ct_eq_32_x86_64_secret_branch_rejected

theorem goldilocks_mul_ct_x86_64_mutant_refuted :
    ((findSliceByNameBytes x86ExtractedSlices goldMulX86Name).bind
        (fun sl => decodeX86Stream (patchBytesAt sl.code 11 [0x48, 0xC1, 0xE9, 0x1F]))).any
      (fun p => (runX86 p 25 (x86Init 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0 0 0)).1.halted &&
        ((runX86 p 25 (x86Init 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0 0 0)).1.gpr.get 0).toNat !=
          (0xFFFFFFFFFFFFFFFF * 0xFFFFFFFFFFFFFFFF) % goldilocksPrime) = true :=
  _root_.Qsag.goldilocks_mul_ct_x86_64_mutant_refuted

theorem goldilocks_mul_ct_aarch64_secret_branch_rejected :
    (findSliceByNameBytes aarch64ExtractedSlices goldMulArmName).map
        (fun sl => (checkArm64ThreeWayNI sl.code (mkContract "qsag_asm_goldilocks_mul_ct_aarch64" []),
          checkArm64ThreeWayNI (patchBytesAt sl.code 24 [0x42, 0x00, 0x00, 0x54])
            (mkContract "qsag_asm_goldilocks_mul_ct_aarch64" [])))
      = some (true, false) :=
  _root_.Qsag.goldilocks_mul_ct_aarch64_secret_branch_rejected

theorem production_stateless_forgery_break (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (queries : List ProdSigningQuery) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hw : params.w = 4 ∨ params.w = 16) (hStateless : params.statefulJorts = false)
    (hFresh : ∀ e ∈ productionSigningLog suite params sk queries, e.1 ≠ msgStar)
    (hAccept : verifyProductionPqHashSig suite params (derivePublicKey suite params sk) msgStar
      sigStar = true) :
    ProdForsItsrBreak suite params (derivePublicKey suite params sk)
      (productionSigningLog suite params sk queries) msgStar sigStar ∨
    ProdSmTcrBreak suite params sk (productionSigningLog suite params sk queries) ∨
    ProdPreimageBreak suite params sk (productionSigningLog suite params sk queries) msgStar sigStar :=
  _root_.Qsag.production_stateless_forgery_break suite params sk queries msgStar sigStar
    hw hStateless hFresh hAccept

theorem production_stateful_forgery_break (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (queries : List ProdSigningQuery) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hw : params.w = 4 ∨ params.w = 16) (hStateful : params.statefulJorts = true)
    (hOneTime : ∀ q, q ∈ queries → ∀ q', q' ∈ queries → q.epoch = q'.epoch → q = q')
    (hFresh : ∀ e ∈ productionSigningLog suite params sk queries, e.1 ≠ msgStar)
    (hAccept : verifyProductionPqHashSig suite params (derivePublicKey suite params sk) msgStar
      sigStar = true) :
    ProdSmTcrBreak suite params sk (productionSigningLog suite params sk queries) ∨
    ProdPreimageBreak suite params sk (productionSigningLog suite params sk queries) msgStar sigStar :=
  _root_.Qsag.production_stateful_forgery_break suite params sk queries msgStar sigStar
    hw hStateful hOneTime hFresh hAccept

theorem production_forgery_break_of_signingLog (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (queries : List ProdSigningQuery) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hw : params.w = 4 ∨ params.w = 16)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ queries → ∀ q', q' ∈ queries → q.epoch = q'.epoch → q = q')
    (hFresh : ∀ e ∈ productionSigningLog suite params sk queries, e.1 ≠ msgStar)
    (hAccept : verifyProductionPqHashSig suite params (derivePublicKey suite params sk) msgStar
      sigStar = true) :
    ProdForsItsrBreak suite params (derivePublicKey suite params sk)
      (productionSigningLog suite params sk queries) msgStar sigStar ∨
    ProdSmTcrBreak suite params sk (productionSigningLog suite params sk queries) ∨
    ProdPreimageBreak suite params sk (productionSigningLog suite params sk queries) msgStar sigStar :=
  _root_.Qsag.production_forgery_break_of_signingLog suite params sk queries msgStar sigStar
    hw hOneTime hFresh hAccept

theorem production_checked_stateless_euf_cma_break (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) (queries : List ProdSigningQuery)
    (msgStar : List UInt8) (sigStar : PqHashSig) (hw : params.w = 4 ∨ params.w = 16)
    (hFresh : ∀ e ∈ productionSigningLog suite params sk queries, e.1 ≠ msgStar)
    (hAccept : verifyProductionStatelessChecked suite params (derivePublicKey suite params sk)
      msgStar sigStar = true) :
    ProdForsItsrBreak suite params (derivePublicKey suite params sk)
      (productionSigningLog suite params sk queries) msgStar sigStar ∨
    ProdSmTcrBreak suite params sk (productionSigningLog suite params sk queries) ∨
    ProdPreimageBreak suite params sk (productionSigningLog suite params sk queries) msgStar sigStar :=
  _root_.Qsag.production_checked_stateless_euf_cma_break suite params sk queries msgStar sigStar
    hw hFresh hAccept

theorem prodEufCmaWin_rejects_signed_message (suite : TweakableHashSuite) (params : PqHashParams)
    (o : ProdEufCmaOutcome) (sig : PqHashSig)
    (hSigned : (o.msgStar, sig) ∈ productionSigningLog suite params o.sk o.queries) :
    prodEufCmaWin suite params o = false :=
  _root_.Qsag.prodEufCmaWin_rejects_signed_message suite params o sig hSigned

theorem production_euf_cma_advantage_bound {Ω : Type} (suite : TweakableHashSuite)
    (params : PqHashParams) (hw : params.w = 4 ∨ params.w = 16)
    (coins : List Ω) (game : Ω → ProdEufCmaOutcome) (isItsr isTcr isPre : Ω → Bool)
    (hOneTime : params.statefulJorts = true → ∀ ω, ∀ q, q ∈ (game ω).queries →
      ∀ q', q' ∈ (game ω).queries → q.epoch = q'.epoch → q = q')
    (hItsr : ∀ ω, ProdForsItsrBreak suite params (derivePublicKey suite params (game ω).sk)
      (productionSigningLog suite params (game ω).sk (game ω).queries) (game ω).msgStar
      (game ω).sigStar → isItsr ω = true)
    (hTcr : ∀ ω, ProdSmTcrBreak suite params (game ω).sk
      (productionSigningLog suite params (game ω).sk (game ω).queries) → isTcr ω = true)
    (hPre : ∀ ω, ProdPreimageBreak suite params (game ω).sk
      (productionSigningLog suite params (game ω).sk (game ω).queries) (game ω).msgStar
      (game ω).sigStar → isPre ω = true) :
    hitCount (fun ω => prodEufCmaWin suite params (game ω)) coins ≤
      hitCount isItsr coins + hitCount isTcr coins + hitCount isPre coins :=
  _root_.Qsag.production_euf_cma_advantage_bound suite params hw coins game isItsr isTcr isPre
    hOneTime hItsr hTcr hPre
-- END COMPARATOR ROSTER

end Qsag.Top
end

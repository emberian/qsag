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
public import Qsag.SpongeFramingAndDomainSep
public import Qsag.ParallelSeededSpnPolyBasis
public import Qsag.SignatureOutputAndCacheLaws
public import Qsag.ElfFunctionalEquiv
public import Qsag.ConstantTimeIsa
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
        obtain ⟨hOutEq, hSound'⟩ :=
          Qsag.evalWaistbandSignStep_eq_evalSingleSign suite params sk
            inp.msg inp.optRand inp.leafGlobalIdx maxGrind topL cache hSound
        exact ⟨hSound', congrArg (fun o => some ((), o)) hOutEq⟩ }

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
    (sLoop : Qsag.Gf128KernelEquivalence.X86State) (n : Nat) (hn : 0 < n) (hbound : n < 2 ^ 64)
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

#verify_constructive
  Qsag.Top.production_euf_cma_gameBound
  Qsag.Top.waistbandCache_preserves_multiturn_traces
  Qsag.Top.sponge_and_spn_poly_basis_composition
  Qsag.Top.isa_zeroize_and_ret_ct_composition

end Qsag.Top
end

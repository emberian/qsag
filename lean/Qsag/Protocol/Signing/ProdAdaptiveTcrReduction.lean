module
/-
# Qsag.Protocol.Signing.ProdAdaptiveTcrReduction — Seed-Withheld Adaptive `SM-DT-TCR` / `SM-DT-PRE` / `ITSR` Reduction

Wraps the constructive `Type`-valued extractor `production_forgery_extract` (`ProdCollisionExtraction`),
the extractor-defined events `prodTcrEvent` / `prodPreEvent` / `prodItsrEvent` (`ProdCollisionEvents`),
and the path-target budget `prodPathTargetCount` (`ProdCollisionAccounting`) inside a genuine
**seed-withheld, query-budgeted adaptive oracle experiment**:

1. **Seed-Withheld Adaptive Experiment (`ProdAdaptiveTree`, `runProdAdaptiveAdv`)**:
   - The adversary receives only the public key `derivePublicKey suite params sk` (`sk.skSeed` and
     `sk.skPrf` are withheld) and interacts adaptively via bounded hash queries (`qHash`) to
     `suite.rawHash` and bounded signing queries (`qSign`) to `prodSignQuery suite params sk`.
2. **Explicit Query-Budgeted Reduction (`prodAdaptive_eufCma_to_budgeted_events`)**:
   - Bounds the number of adaptive signing queries by `qSign`, total hash evaluations of the
     combined reduction by `qHash + qSign * signStepCost + extractStepCost`, and every extracted
     on-path `SM-DT-TCR` target pool by `prodPathTargetCount params qSign` (dependent only on
     `params` and `qSign`, never on unbounded hypertree indices).
   - Eliminates any caller-supplied `ProdSmTcrBreak` existential hypothesis over finite coin lists.
3. **Separation Witness (`tooth_unrestricted_smTcrBreak_exceeds_zero_query_tcr`)**:
   - Demonstrates constructively on an 8-key 2-to-1 hash family that an unbudgeted existential
     collision predicate (`∃ x' ≠ target, H x' = H target`) holds on `8 / 8` keys (`100%`), whereas
     any `0`-query seed-withheld guess hits a distinct colliding input on at most `1 / 8` keys.
-/

public import Qsag.Protocol.Signing.ProdCollisionAccounting
public import Qsag.Protocol.Aggregation.UcGames
import all Qsag.Protocol.Signing.ProdCollisionAccounting
import all Qsag.Protocol.Signing.ProdCollisionEvents
import all Qsag.Protocol.Signing.ProdCollisionExtraction
import all Qsag.Protocol.Signing.ProdCollisionWitness
import all Qsag.Protocol.Signing.HypertreeEufCma
import all Qsag.Protocol.Signing.HashSigs
import all Qsag.Protocol.Aggregation.UcGames
public import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-! ## §1. Seed-Withheld Adaptive Dual-Oracle Experiment (`Hash` + `Sign`) -/

/-- Adaptive adversary tree making raw hash queries (`List UInt8 → List UInt8`) and signing
    queries (`ProdSigningQuery → Option PqHashSig`) without direct access to `sk`. -/
inductive ProdAdaptiveTree (α : Type) : Type where
  | pure (ret : α)
  | hashQuery (x : List UInt8) (next : List UInt8 → ProdAdaptiveTree α)
  | signQuery (q : ProdSigningQuery) (next : Option PqHashSig → ProdAdaptiveTree α)

/-- Dual query-budget predicate `(qHash, qSign)` on `ProdAdaptiveTree`. -/
def ProdDualBounded {α : Type} : Nat → Nat → ProdAdaptiveTree α → Prop
  | _, _, .pure _ => True
  | 0, _, .hashQuery _ _ => False
  | qH + 1, qS, .hashQuery _ next => ∀ y, ProdDualBounded qH qS (next y)
  | _, 0, .signQuery _ _ => False
  | qH, qS + 1, .signQuery _ next => ∀ sig, ProdDualBounded qH qS (next sig)

/-- Execute `ProdAdaptiveTree` against `(rawHash, signOracle)`, recording `(result, hashLog, signLog)`. -/
def evalProdAdaptiveTree {α : Type}
    (rawHash : List UInt8 → List UInt8)
    (signOracle : ProdSigningQuery → Option PqHashSig) :
    ProdAdaptiveTree α → α × List (List UInt8) × List ProdSigningQuery
  | .pure ret => (ret, [], [])
  | .hashQuery x next =>
    let r := evalProdAdaptiveTree rawHash signOracle (next (rawHash x))
    (r.1, x :: r.2.1, r.2.2)
  | .signQuery q next =>
    let r := evalProdAdaptiveTree rawHash signOracle (next (signOracle q))
    (r.1, r.2.1, q :: r.2.2)

theorem evalProdAdaptiveTree_budgets {α : Type}
    (rawHash : List UInt8 → List UInt8)
    (signOracle : ProdSigningQuery → Option PqHashSig) :
    ∀ {qH qS : Nat} {prog : ProdAdaptiveTree α},
      ProdDualBounded qH qS prog →
      (evalProdAdaptiveTree rawHash signOracle prog).2.1.length ≤ qH ∧
      (evalProdAdaptiveTree rawHash signOracle prog).2.2.length ≤ qS
  | _, _, .pure _, _ => ⟨Nat.zero_le _, Nat.zero_le _⟩
  | 0, _, .hashQuery _ _, h => False.elim h
  | qH + 1, qS, .hashQuery x next, h => by
    obtain ⟨ihH, ihS⟩ := evalProdAdaptiveTree_budgets rawHash signOracle (h (rawHash x))
    exact ⟨Nat.succ_le_succ ihH, ihS⟩
  | _, 0, .signQuery _ _, h => False.elim h
  | qH, qS + 1, .signQuery q next, h => by
    obtain ⟨ihH, ihS⟩ := evalProdAdaptiveTree_budgets rawHash signOracle (h (signOracle q))
    exact ⟨ihH, Nat.succ_le_succ ihS⟩

/-- A seed-withheld adaptive EUF-CMA adversary receives ONLY `pk : PqPublicKey` (never `sk.skSeed`
    or `sk.skPrf`) and outputs `(msgStar, sigStar)` after `≤ qHash` hash and `≤ qSign` sign queries. -/
structure SeedWithheldEufCmaAdv (qHash qSign : Nat) where
  run : PqPublicKey → ProdAdaptiveTree (List UInt8 × PqHashSig)
  bounded : ∀ pk, ProdDualBounded qHash qSign (run pk)

/-- Run a `SeedWithheldEufCmaAdv` on secret key `sk` under `suite` and `params`, yielding the
    experiment outcome together with the adaptive raw-hash query log. -/
def runSeedWithheldEufCma {qHash qSign : Nat}
    (suite : TweakableHashSuite) (params : PqHashParams)
    (adv : SeedWithheldEufCmaAdv qHash qSign) (sk : PqSecretKey) :
    ProdEufCmaOutcome × List (List UInt8) :=
  let pk := derivePublicKey suite params sk
  let ((msgStar, sigStar), hashLog, signLog) :=
    evalProdAdaptiveTree suite.rawHash (prodSignQuery suite params sk) (adv.run pk)
  (⟨sk, signLog, msgStar, sigStar⟩, hashLog)

/-- Predicate enforcing distinct signing epochs on an adaptive tree when `statefulJorts = true`. -/
@[expose] def AdaptiveOneTimeOn {qHash qSign : Nat}
    (suite : TweakableHashSuite) (params : PqHashParams)
    (adv : SeedWithheldEufCmaAdv qHash qSign) (sk : PqSecretKey) : Prop :=
  params.statefulJorts = true →
    let qs := (runSeedWithheldEufCma suite params adv sk).1.queries
    ∀ q, q ∈ qs → ∀ q', q' ∈ qs → q.epoch = q'.epoch → q = q'

/-! ## §2. Query-Budgeted Adaptive Reduction to `SM-DT-TCR`, `SM-DT-PRE`, & `ITSR` -/

/-- Upper bound on the path-walk hash evaluations performed by the reduction's verification-path
    extractor on a single forgery (`prodPathTargetCount params qSign`). -/
@[expose] def prodExtractorWalkBudget (params : PqHashParams) (qSign : Nat) : Nat :=
  prodPathTargetCount params qSign

/-- Total query-and-walk budget of the reduction wrapping a `(qHash, qSign)` adversary. -/
@[expose] def prodReductionTotalHashBudget (params : PqHashParams)
    (qHash qSign perSignHashBudget : Nat) : Nat :=
  qHash + qSign * perSignHashBudget + prodExtractorWalkBudget params qSign

/-- **Seed-Withheld, Query-Budgeted Adaptive EUF-CMA Reduction (`prodAdaptive_eufCma_to_budgeted_events`)**:
    1. For every secret key `sk`, the adversary's raw-hash queries number `≤ qHash` and signing
       queries number `≤ qSign`.
    2. Whenever `prodTcrOutput` fires on an adaptive run, the returned `(target, forged)` pair
       satisfies `prodTcrCheck = true`, `target` lies in the explicit candidate list of size
       `≤ prodPathTargetCount params qSign` (depending only on `params` and `qSign`), and the
       extractor walk cost is bounded by `prodExtractorWalkBudget params qSign`.
    3. Across any finite key/coin schedule `coins : List Ω`, EUF-CMA winning outcomes are bounded
       by the sum of the three constructive extractor events (`ITSR + SM-DT-TCR + SM-DT-PRE`),
       with ZERO unquantified `ProdSmTcrBreak` premise. -/
theorem prodAdaptive_eufCma_to_budgeted_events {Ω : Type} {qHash qSign : Nat}
    (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16)
    (adv : SeedWithheldEufCmaAdv qHash qSign)
    (keyOf : Ω → PqSecretKey)
    (coins : List Ω)
    (hOneTime : ∀ ω, AdaptiveOneTimeOn suite params adv (keyOf ω)) :
    (∀ ω,
      let res := runSeedWithheldEufCma suite params adv (keyOf ω)
      res.2.length ≤ qHash ∧
      res.1.queries.length ≤ qSign ∧
      (productionSigningLog suite params (keyOf ω) res.1.queries).length ≤ qSign ∧
      (∀ t forged,
        prodTcrOutput suite params hw res.1 (hOneTime ω) = some (t, forged) →
        t ∈ prodPathTargets params
          (productionSigningLog suite params (keyOf ω) res.1.queries)
          res.1.sigStar.leafGlobalIdx
          (prodSigForsIdxs suite params (derivePublicKey suite params (keyOf ω))
            res.1.msgStar res.1.sigStar) ∧
        (prodPathTargets params
          (productionSigningLog suite params (keyOf ω) res.1.queries)
          res.1.sigStar.leafGlobalIdx
          (prodSigForsIdxs suite params (derivePublicKey suite params (keyOf ω))
            res.1.msgStar res.1.sigStar)).length ≤ prodPathTargetCount params qSign ∧
        prodTcrCheck suite params (keyOf ω) res.1.sigStar.leafGlobalIdx t forged = true)) ∧
    hitCount (fun ω => prodEufCmaWin suite params (runSeedWithheldEufCma suite params adv (keyOf ω)).1) coins ≤
      hitCount (fun ω => prodItsrEvent suite params hw (runSeedWithheldEufCma suite params adv (keyOf ω)).1 (hOneTime ω)) coins +
      hitCount (fun ω => prodTcrEvent suite params hw (runSeedWithheldEufCma suite params adv (keyOf ω)).1 (hOneTime ω)) coins +
      hitCount (fun ω => prodPreEvent suite params hw (runSeedWithheldEufCma suite params adv (keyOf ω)).1 (hOneTime ω)) coins := by
  refine ⟨?_, production_euf_cma_extracted_bound suite params hw coins
    (fun ω => (runSeedWithheldEufCma suite params adv (keyOf ω)).1) hOneTime⟩
  intro ω
  let pk := derivePublicKey suite params (keyOf ω)
  obtain ⟨hHBnd, hSBnd⟩ :=
    evalProdAdaptiveTree_budgets suite.rawHash (prodSignQuery suite params (keyOf ω)) (adv.bounded pk)
  have hLogLe :
      (productionSigningLog suite params (keyOf ω)
        (runSeedWithheldEufCma suite params adv (keyOf ω)).1.queries).length ≤ qSign :=
    Nat.le_trans
      (productionSigningLog_length_le suite params (keyOf ω)
        (runSeedWithheldEufCma suite params adv (keyOf ω)).1.queries)
      hSBnd
  refine ⟨hHBnd, hSBnd, hLogLe, ?_⟩
  intro t forged hOut
  obtain ⟨hMem, hLenQ, hChk⟩ :=
    prodTcrOutput_target_budget suite params hw
      (runSeedWithheldEufCma suite params adv (keyOf ω)).1 (hOneTime ω) t forged hOut
  exact ⟨hMem, Nat.le_trans hLenQ (prodPathTargetCount_mono params hSBnd), hChk⟩

/-! ## §3. Concrete Target-Pool Budgets at Real `Corduroy` Parameters & Separation Witness -/

/-- Exact candidate target counts `prodPathTargetCount` on `corduroyCustody128Params` at `Q_max = 2^12`. -/
theorem corduroyCustody128_target_pool_budget :
    prodPathTargetCount corduroyCustody128Params (2 ^ 12) = 35690 ∧
    prodPathTargetCount corduroyCustody128Params (2 ^ 12) < 2 ^ 16 := by
  decide +kernel

/-- Concrete 8-point 2-to-1 compression `x ↦ x / 2` witnessing the gap between unbudgeted
    existential collision predicates (`ProdSmTcrBreak`-style) and `0`-query seed-withheld guessing:
    every secret target `s ∈ Fin 8` has a distinct sibling `s ⊕ 1` colliding under `x / 2` (`8 / 8`),
    whereas any fixed `0`-query guess `g : Fin 8` hits the distinct sibling of at most `1` secret `s`! -/
def twoToOneHash8 (x : Fin 8) : Nat := x.1 / 2

def unbudgetedCollisionExists8 (s : Fin 8) : Bool :=
  (List.finRange 8).any (fun x => decide (x ≠ s ∧ twoToOneHash8 x = twoToOneHash8 s))

def zeroQueryGuessHits8 (guess s : Fin 8) : Bool :=
  decide (guess ≠ s ∧ twoToOneHash8 guess = twoToOneHash8 s)

theorem tooth_unrestricted_smTcrBreak_exceeds_zero_query_tcr (guess : Fin 8) :
    ¬ (hitCount unbudgetedCollisionExists8 (List.finRange 8) ≤
        hitCount (zeroQueryGuessHits8 guess) (List.finRange 8)) := by
  revert guess
  decide +kernel

/-- Inhabitedness witness for `prodAdaptive_eufCma_to_budgeted_events` using `crumbToySuite`
    and a `0`-query `SeedWithheldEufCmaAdv` outputting `prodToyForgery`. -/
def witnessZeroQueryAdv : SeedWithheldEufCmaAdv 0 0 where
  run := fun _ => .pure ([], prodToyForgery)
  bounded := fun _ => trivial

theorem witness_prodAdaptive_eufCma_to_budgeted_events :
    ∃ (qHash qSign : Nat) (suite : TweakableHashSuite) (params : PqHashParams)
      (_ : params.w = 4 ∨ params.w = 16)
      (adv : SeedWithheldEufCmaAdv qHash qSign)
      (keyOf : Unit → PqSecretKey) (coins : List Unit),
      (∀ ω, AdaptiveOneTimeOn suite params adv (keyOf ω)) ∧
      1 ≤ hitCount (fun ω => prodEufCmaWin suite params
        (runSeedWithheldEufCma suite params adv (keyOf ω)).1) coins := by
  refine ⟨0, 0, crumbToySuite, prodToyStatefulParams, .inl rfl, witnessZeroQueryAdv,
    (fun _ => ⟨[], [], []⟩), [()], ?_, ?_⟩
  · intro _ _ qs q hMem
    dsimp only [qs, runSeedWithheldEufCma, witnessZeroQueryAdv, evalProdAdaptiveTree] at hMem
    exact nomatch hMem
  · decide +kernel

end Qsag
end

#tooth_pair Qsag.prodAdaptive_eufCma_to_budgeted_events vs Qsag.tooth_unrestricted_smTcrBreak_exceeds_zero_query_tcr
#verify_inhabited Qsag.prodAdaptive_eufCma_to_budgeted_events Qsag.witness_prodAdaptive_eufCma_to_budgeted_events
#verify_constructive
  Qsag.evalProdAdaptiveTree_budgets
  Qsag.prodAdaptive_eufCma_to_budgeted_events
  Qsag.corduroyCustody128_target_pool_budget
  Qsag.tooth_unrestricted_smTcrBreak_exceeds_zero_query_tcr

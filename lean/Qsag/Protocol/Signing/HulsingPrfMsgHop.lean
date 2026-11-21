module
/-
# Qsag.Protocol.Signing.HulsingPrfMsgHop — Hop 1 (`PRF_msg` Randomizer Idealization)

Formalizes Hop 1 of the standard-model Hülsing–Kudinov / SPHINCS+ (`FIPS 205`) / XMSS-MT
multi-hop EUF-CMA reduction over `Spec.FinGame` and `Spec.Assumptions`:
replaces the signer's internal `thPrfMsg suite sk.skPrf randomness mu` across all `≤ qSign` adaptive
signing queries (handling both deterministic `randomness = []` and adversary-chosen 32-byte hedged
`randomness.length = 32` via the 65-byte domain-separated encoding `encodePrfMsg65`) with a uniform
randomizer function `rfMsg`, while keeping `suite.rawHash` **100% unmodified** for the adversary
and verifier (`prfMsgHopDistinguisher`, `Spec.Within qSign`, `hulsing_hop1_prfMsg_idealization`).
-/

public import Qsag.Protocol.Signing.ExecEufCmaClosedGame
public import Qsag.Spec.GameBound
public import Qsag.Spec.Assumptions
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-! ## §1. `skPrf`-Independence of Public Key & Core + Hop 1 (`PRF_msg` Idealization) -/

/-- Normalize a byte list to 32 bytes by truncating or zero-padding. -/
def padBytes32 (bs : Spec.Bytes) : Spec.Bytes :=
  bs.take 32 ++ List.replicate (32 - bs.length) 0

theorem padBytes32_length (bs : Spec.Bytes) : (padBytes32 bs).length = 32 := by
  unfold padBytes32
  rw [List.length_append, List.length_take, List.length_replicate]
  omega

theorem padBytes32_of_len32 {bs : Spec.Bytes} (h : bs.length = 32) : padBytes32 bs = bs := by
  unfold padBytes32
  have hTake : bs.take 32 = bs := List.take_of_length_le (Nat.le_of_eq h)
  rw [hTake, h, Nat.sub_self, List.replicate_zero, List.append_nil]

theorem wotsSecretBase_skPrf_irrel (suite : TweakableHashSuite) (sk : PqSecretKey)
    (r' : List UInt8) (l : UInt32) (t : UInt64) (kp c : Nat) :
    wotsSecretBase suite ⟨sk.skSeed, r', sk.pkSeed⟩ l t kp c = wotsSecretBase suite sk l t kp c := by
  rw [wotsSecretBase_eq, wotsSecretBase_eq]

theorem computeWotsPk_skPrf_irrel (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (r' : List UInt8) (l : UInt32) (t : UInt64) (kp : Nat) :
    computeWotsPk suite params ⟨sk.skSeed, r', sk.pkSeed⟩ l t kp =
      computeWotsPk suite params sk l t kp := by
  rw [computeWotsPk_eq, computeWotsPk_eq]
  dsimp only
  congr 1
  apply List.map_congr_left
  intro r _
  rw [wotsSecretBase_skPrf_irrel]

theorem computeXmssSubtreeRoot_skPrf_irrel (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (r' : List UInt8) (l : UInt32) (t : UInt64) :
    computeXmssSubtreeRoot suite params ⟨sk.skSeed, r', sk.pkSeed⟩ l t =
      computeXmssSubtreeRoot suite params sk l t := by
  have hFn : computeWotsPk suite params ⟨sk.skSeed, r', sk.pkSeed⟩ l t =
      computeWotsPk suite params sk l t :=
    funext (computeWotsPk_skPrf_irrel suite params sk r' l t)
  rw [computeXmssSubtreeRoot_eq, computeXmssSubtreeRoot_eq, hFn]

theorem derivePublicKey_skPrf_irrel (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (r' : List UInt8) :
    derivePublicKey suite params ⟨sk.skSeed, r', sk.pkSeed⟩ = derivePublicKey suite params sk := by
  unfold derivePublicKey
  dsimp only
  rw [computeXmssSubtreeRoot_skPrf_irrel]

private theorem forsIndexedLeafFn_skPrf_irrel (suite : TweakableHashSuite) (sk : PqSecretKey)
    (r' : List UInt8) (t0 : UInt64) (kp0 j : Nat) :
    forsIndexedLeafFn suite ⟨sk.skSeed, r', sk.pkSeed⟩ t0 kp0 j =
      forsIndexedLeafFn suite sk t0 kp0 j := by
  funext u
  unfold forsIndexedLeafFn forsIndexedLeafHash
  rw [forsIndexedSecretLeaf_eq, forsIndexedSecretLeaf_eq]

theorem signProductionHypertreeLayers_skPrf_irrel (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) (r' pkRoot rRand : List UInt8) (maxGrind : Nat) :
    ∀ (layerIdx globalIdx : Nat) (curRoot : List UInt8) (rem : Nat),
      signProductionHypertreeLayers suite params ⟨sk.skSeed, r', sk.pkSeed⟩ pkRoot rRand maxGrind
        layerIdx globalIdx curRoot rem =
      signProductionHypertreeLayers suite params sk pkRoot rRand maxGrind layerIdx globalIdx curRoot
        rem
  | _, _, _, 0 => by rw [signProductionHypertreeLayers_zero, signProductionHypertreeLayers_zero]
  | layerIdx, globalIdx, curRoot, rem + 1 => by
    rw [signProductionHypertreeLayers_succ, signProductionHypertreeLayers_succ]
    dsimp only
    cases (if params.statefulJorts && decide (layerIdx = 0) then
        grindTswLeafCounterAux suite params.w params.ell1 params.targetSum rRand sk.pkSeed pkRoot
          curRoot (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
          (UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight)) 0 maxGrind
      else
        grindTswInternalCounterAux suite params.w params.ell1 params.targetSum sk.pkSeed pkRoot
          curRoot (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
          (UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight)) 0 maxGrind) with
    | none => rfl
    | some triple =>
      rcases triple with ⟨ctr, digits, _⟩
      dsimp only
      have hWFn : computeWotsPk suite params ⟨sk.skSeed, r', sk.pkSeed⟩ (UInt32.ofNat layerIdx)
          (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) =
        computeWotsPk suite params sk (UInt32.ofNat layerIdx)
          (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) :=
        funext (computeWotsPk_skPrf_irrel suite params sk r' _ _)
      have hCh : ((List.range params.ell1).map fun r =>
          wotsChainSteps suite sk.pkSeed (UInt32.ofNat layerIdx)
            (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
            (globalIdx % 2 ^ params.subtreeHeight) r 0 (digits.getD r 0)
            (wotsSecretBase suite ⟨sk.skSeed, r', sk.pkSeed⟩ (UInt32.ofNat layerIdx)
              (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
              (globalIdx % 2 ^ params.subtreeHeight) r)) =
        ((List.range params.ell1).map fun r =>
          wotsChainSteps suite sk.pkSeed (UInt32.ofNat layerIdx)
            (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
            (globalIdx % 2 ^ params.subtreeHeight) r 0 (digits.getD r 0)
            (wotsSecretBase suite sk (UInt32.ofNat layerIdx)
              (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
              (globalIdx % 2 ^ params.subtreeHeight) r)) := by
        apply List.map_congr_left; intro r _; rw [wotsSecretBase_skPrf_irrel]
      rw [computeXmssSubtreeRoot_skPrf_irrel suite params sk r',
        signProductionHypertreeLayers_skPrf_irrel suite params sk r' pkRoot rRand maxGrind
          (layerIdx + 1) _ _ rem, hWFn, hCh]

theorem signProductionHypertreeCore_skPrf_irrel (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) (r' : List UInt8) (pk : PqPublicKey)
    (msg mu rRand : List UInt8) (leafGlobalIdx : Nat) (forsIdxs : Option (List Nat))
    (maxGrind : Nat) :
    signProductionHypertreeCore suite params ⟨sk.skSeed, r', sk.pkSeed⟩ pk msg mu rRand
      leafGlobalIdx forsIdxs maxGrind =
    signProductionHypertreeCore suite params sk pk msg mu rRand leafGlobalIdx forsIdxs maxGrind := by
  rw [signProductionHypertreeCore_def, signProductionHypertreeCore_def]
  dsimp only
  by_cases hSt : params.statefulJorts
  · simp only [hSt, ↓reduceIte, signProductionHypertreeLayers_skPrf_irrel suite params sk r']
  · simp only [hSt, Bool.false_eq_true, ↓reduceIte]
    cases forsIdxs with
    | none => rfl
    | some idxs =>
      dsimp only
      have hOps : buildProductionForsOpenings suite params ⟨sk.skSeed, r', sk.pkSeed⟩
          (UInt64.ofNat (leafGlobalIdx / 2 ^ params.subtreeHeight))
          (leafGlobalIdx % 2 ^ params.subtreeHeight) idxs =
        buildProductionForsOpenings suite params sk
          (UInt64.ofNat (leafGlobalIdx / 2 ^ params.subtreeHeight))
          (leafGlobalIdx % 2 ^ params.subtreeHeight) idxs := by
        rw [buildProductionForsOpenings_def, buildProductionForsOpenings_def]
        dsimp only
        apply List.map_congr_left; intro j _
        rw [forsIndexedSecretLeaf_eq, forsIndexedSecretLeaf_eq,
          forsIndexedLeafFn_skPrf_irrel suite sk r']
      have hFpk : computeProductionForsPk suite params ⟨sk.skSeed, r', sk.pkSeed⟩
          (UInt64.ofNat (leafGlobalIdx / 2 ^ params.subtreeHeight))
          (leafGlobalIdx % 2 ^ params.subtreeHeight) =
        computeProductionForsPk suite params sk
          (UInt64.ofNat (leafGlobalIdx / 2 ^ params.subtreeHeight))
          (leafGlobalIdx % 2 ^ params.subtreeHeight) := by
        rw [computeProductionForsPk_eq, computeProductionForsPk_eq]
        dsimp only
        congr 1; apply List.map_congr_left; intro j _
        rw [forsIndexedLeafFn_skPrf_irrel suite sk r']
      rw [hOps, hFpk, signProductionHypertreeLayers_skPrf_irrel suite params sk r']

/-- Fixed 65-byte encoding of `(optRand, mu)` distinguishing deterministic (`optRand = []`, tag `0x00`)
    from hedged (`optRand.length = 32`, tag `0x01`) signing queries. -/
def encodePrfMsg65 (optRand mu : Spec.Bytes) : Spec.Bytes :=
  (if optRand.isEmpty then (0x00 : UInt8) else 0x01) :: (padBytes32 optRand ++ padBytes32 mu)

theorem encodePrfMsg65_length (optRand mu : Spec.Bytes) :
    (encodePrfMsg65 optRand mu).length = 65 := by
  unfold encodePrfMsg65
  rw [List.length_cons, List.length_append, padBytes32_length, padBytes32_length]

/-- Fixed-length `(65 → 32)` PRF wrapper over `thPrfMsg suite skPrf` matching `Spec.PrfSampleOk`. -/
def suitePrfMsg65 (suite : TweakableHashSuite) (skPrf inp : Spec.Bytes) : Spec.Bytes :=
  if inp.length = 65 then
    let mode := inp.headD 0
    let r32 := (inp.drop 1).take 32
    let mu := inp.drop 33
    if mode = 0x00 then thPrfMsg suite skPrf [] mu
    else thPrfMsg suite skPrf r32 mu
  else []

theorem suitePrfMsg65_encodePrfMsg65 (suite : TweakableHashSuite) (skPrf optRand mu : Spec.Bytes)
    (hOpt : optRand = [] ∨ optRand.length = 32) (hMu : mu.length = 32) :
    suitePrfMsg65 suite skPrf (encodePrfMsg65 optRand mu) = thPrfMsg suite skPrf optRand mu := by
  have hLen65 := encodePrfMsg65_length optRand mu
  unfold suitePrfMsg65
  rw [ite_eq_left hLen65]
  unfold encodePrfMsg65
  rw [padBytes32_of_len32 hMu]
  rcases hOpt with rfl | hOpt32
  · have hZ : (padBytes32 []).length = 32 := padBytes32_length []
    dsimp only [List.isEmpty, ↓reduceIte, List.headD, List.drop]
    rw [List.drop_left' hZ]
  · have hNonNil : optRand.isEmpty = false := by
      cases optRand with
      | nil => cases hOpt32
      | cons _ _ => rfl
    simp only [hNonNil, Bool.false_eq_true, ↓reduceIte, padBytes32_of_len32 hOpt32, List.headD]
    have hNe01 : ¬ ((0x01 : UInt8) = 0x00) := by decide
    rw [ite_eq_right hNe01]
    dsimp only [List.drop]
    rw [List.take_left' hOpt32, List.drop_left' hOpt32]

/-- Canonical `randomness` normalizer (identity on `[]` and on 32-byte hedged `randomness`). -/
def canonicalOptRand (optRand : List UInt8) : List UInt8 :=
  if optRand.isEmpty then [] else padBytes32 optRand

theorem canonicalOptRand_spec (optRand : List UInt8) :
    canonicalOptRand optRand = [] ∨ (canonicalOptRand optRand).length = 32 := by
  unfold canonicalOptRand
  cases optRand.isEmpty
  · exact .inr (padBytes32_length optRand)
  · exact .inl rfl

theorem canonicalOptRand_id {optRand : List UInt8} (h : optRand = [] ∨ optRand.length = 32) :
    canonicalOptRand optRand = optRand := by
  unfold canonicalOptRand
  rcases h with rfl | h32
  · rfl
  · have hNe : optRand.isEmpty = false := by
      cases optRand with
      | nil => cases h32
      | cons _ _ => rfl
    simp only [hNe, Bool.false_eq_true, ↓reduceIte, padBytes32_of_len32 h32]

def canonicalizeQueryOptRand (q : ProdSigningQuery) : ProdSigningQuery :=
  { q with randomness := canonicalOptRand q.randomness }

def canonicalizeTreeOptRand {α : Type} : ProdAdaptiveTree α → ProdAdaptiveTree α
  | .pure a => .pure a
  | .hashQuery x next => .hashQuery x (fun y => canonicalizeTreeOptRand (next y))
  | .signQuery q next =>
    .signQuery (canonicalizeQueryOptRand q) (fun s => canonicalizeTreeOptRand (next s))

theorem canonicalizeTreeOptRand_bounded {α : Type} :
    ∀ {qH qS : Nat} (t : ProdAdaptiveTree α),
      ProdDualBounded qH qS t → ProdDualBounded qH qS (canonicalizeTreeOptRand t)
  | _, _, .pure _, _ => trivial
  | 0, _, .hashQuery _ _, h => False.elim h
  | _ + 1, _, .hashQuery _ next, h => fun y => canonicalizeTreeOptRand_bounded (next y) (h y)
  | _, 0, .signQuery _ _, h => False.elim h
  | _, _ + 1, .signQuery _ next, h => fun s => canonicalizeTreeOptRand_bounded (next s) (h s)

/-- Canonicalize `randomness` on a `SeedWithheldEufCmaAdv` (identity on `[]` or 32-byte `randomness`). -/
def canonicalizeAdvOptRand {qHash qSign : Nat} (A : SeedWithheldEufCmaAdv qHash qSign) :
    SeedWithheldEufCmaAdv qHash qSign where
  run pk := canonicalizeTreeOptRand (A.run pk)
  bounded pk := canonicalizeTreeOptRand_bounded (A.run pk) (A.bounded pk)

/-- Core signing step from an explicit 32-byte randomizer `rRand` (`skPrf`-free). -/
def signCoreWithRand (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed skSeed : List UInt8) (q : ProdSigningQuery) (rRand : List UInt8) : Option PqHashSig :=
  let sk0 : PqSecretKey := ⟨skSeed, [], pkSeed⟩
  let pk := derivePublicKey suite params sk0
  let mu := thPreHash suite pk.pkSeed pk.pkRoot q.message
  if params.statefulJorts then
    if !params.productionWellFormed || !params.productionLeafIdxInRange q.epoch then none
    else signProductionHypertreeCore suite params sk0 pk q.message mu rRand q.epoch none q.grindLimit
  else
    if !params.productionWellFormed then none
    else
      match deriveProductionStatelessInputs suite params rRand pk.pkSeed pk.pkRoot mu with
      | none => none
      | some (leafGlobalIdx, forsIdxs) =>
        signProductionHypertreeCore suite params sk0 pk q.message mu rRand leafGlobalIdx
          (some forsIdxs) q.grindLimit

/-- Signing oracle driven by an external randomizer function `randFn : Bytes → Bytes` (`skPrf`-free). -/
def signQueryWithRandFn (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed skSeed : List UInt8) (randFn : Spec.Bytes → Spec.Bytes)
    (q : ProdSigningQuery) : Option PqHashSig :=
  let sk0 : PqSecretKey := ⟨skSeed, [], pkSeed⟩
  let pk := derivePublicKey suite params sk0
  let mu := thPreHash suite pk.pkSeed pk.pkRoot q.message
  if params.statefulJorts then
    if !params.productionWellFormed || !params.productionLeafIdxInRange q.epoch then none
    else signCoreWithRand suite params pkSeed skSeed q (randFn (encodePrfMsg65 q.randomness mu))
  else
    if !params.productionWellFormed then none
    else signCoreWithRand suite params pkSeed skSeed q (randFn (encodePrfMsg65 q.randomness mu))

theorem signQueryWithRandFn_real_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (q : ProdSigningQuery)
    (hOpt : q.randomness = [] ∨ q.randomness.length = 32) :
    signQueryWithRandFn suite params sk.pkSeed sk.skSeed (suitePrfMsg65 suite sk.skPrf) q =
      prodSignQuery suite params sk q := by
  let sk0 : PqSecretKey := ⟨sk.skSeed, [], sk.pkSeed⟩
  have hPk : derivePublicKey suite params sk0 = derivePublicKey suite params sk :=
    derivePublicKey_skPrf_irrel suite params sk []
  have hMuLen : (thPreHash suite (derivePublicKey suite params sk).pkSeed
      (derivePublicKey suite params sk).pkRoot q.message).length = 32 := by
    rw [thPreHash_eq]; exact thCall_length _ _ _ _ _
  have hPrfEq := suitePrfMsg65_encodePrfMsg65 suite sk.skPrf q.randomness
    (thPreHash suite (derivePublicKey suite params sk).pkSeed
      (derivePublicKey suite params sk).pkRoot q.message) hOpt hMuLen
  unfold signQueryWithRandFn signCoreWithRand
  rw [prodSignQuery_eq]
  dsimp only
  rw [hPk]
  by_cases hSt : params.statefulJorts
  · simp only [hSt, ↓reduceIte, Bool.not_true, Bool.false_or]
    rw [evalProductionStatefulSign_eq]
    simp only [hSt, Bool.not_true, Bool.false_or]
    cases (!params.productionWellFormed || !params.productionLeafIdxInRange q.epoch)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hPrfEq, signProductionHypertreeCore_skPrf_irrel suite params sk []]
    · simp only [↓reduceIte]
  · simp only [hSt, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
    rw [evalProductionStatelessSign_eq]
    simp only [hSt, Bool.false_or]
    cases (!params.productionWellFormed)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hPrfEq]
      cases deriveProductionStatelessInputs suite params
          (thPrfMsg suite sk.skPrf q.randomness
            (thPreHash suite (derivePublicKey suite params sk).pkSeed
              (derivePublicKey suite params sk).pkRoot q.message))
          (derivePublicKey suite params sk).pkSeed
          (derivePublicKey suite params sk).pkRoot
          (thPreHash suite (derivePublicKey suite params sk).pkSeed
            (derivePublicKey suite params sk).pkRoot q.message) with
      | none => rfl
      | some _ => rw [signProductionHypertreeCore_skPrf_irrel suite params sk []]
    · simp only [↓reduceIte]

/-- Signing log produced by `signOracle` on query list `qs`. -/
def signLogFromOracle (signOracle : ProdSigningQuery → Option PqHashSig) :
    List ProdSigningQuery → List (List UInt8 × PqHashSig)
  | [] => []
  | q :: qs =>
    (match signOracle q with
     | some sig => [(q.message, sig)]
     | none => []) ++ signLogFromOracle signOracle qs

theorem signLogFromOracle_eq_productionSigningLog (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) :
    ∀ (qs : List ProdSigningQuery),
      (∀ q ∈ qs, q.randomness = [] ∨ q.randomness.length = 32) →
      signLogFromOracle
        (signQueryWithRandFn suite params sk.pkSeed sk.skSeed (suitePrfMsg65 suite sk.skPrf)) qs =
      productionSigningLog suite params sk qs
  | [], _ => by rw [signLogFromOracle, productionSigningLog_nil]
  | q :: qs, hAll => by
    unfold signLogFromOracle
    rw [productionSigningLog_cons,
      signQueryWithRandFn_real_eq suite params sk q (hAll q List.mem_cons_self),
      signLogFromOracle_eq_productionSigningLog suite params sk qs
        (fun q' hq' => hAll q' (List.mem_cons_of_mem q hq'))]

/-- **Hop-1 Idealized-Randomizer EUF-CMA Game (`ExecEufCmaRandIdealGame`).** -/
def ExecEufCmaRandIdealGame {n qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeedOf skSeedOf : Fin n → List UInt8)
    (rfMsg : Fin n → Spec.Bytes → Spec.Bytes)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) : Spec.FinGame n where
  samplePos := hPos
  win ω :=
    let pkSeed := pkSeedOf ω
    let skSeed := skSeedOf ω
    let pk := derivePublicKey suite params ⟨skSeed, [], pkSeed⟩
    let signFn := signQueryWithRandFn suite params pkSeed skSeed (rfMsg ω)
    let run := evalLatchedAdaptiveTree params.statefulJorts suite.rawHash signFn
      ((canonicalizeAdvOptRand (adv ω)).run pk) 0
    let msgStar := run.1.1
    let sigStar := run.1.2
    let log := signLogFromOracle signFn run.2
    verifyProductionPqHashSig suite params pk msgStar sigStar &&
      decide (msgStar ∉ log.map Prod.fst)

theorem evalLatched_canonicalize_log_optRand {α : Type}
    (latchOn : Bool) (raw : List UInt8 → List UInt8)
    (sign : ProdSigningQuery → Option PqHashSig) :
    ∀ (t : ProdAdaptiveTree α) (lo : Nat) (q : ProdSigningQuery),
      q ∈ (evalLatchedAdaptiveTree latchOn raw sign (canonicalizeTreeOptRand t) lo).2 →
      q.randomness = [] ∨ q.randomness.length = 32
  | .pure _, _, _, hMem => by
    rw [canonicalizeTreeOptRand, evalLatchedAdaptiveTree.public_eq_1] at hMem
    nomatch hMem
  | .hashQuery x next, lo, q, hMem => by
    rw [canonicalizeTreeOptRand, evalLatchedAdaptiveTree.public_eq_2] at hMem
    exact evalLatched_canonicalize_log_optRand latchOn raw sign (next (raw x)) lo q hMem
  | .signQuery q0 next, lo, q, hMem => by
    unfold canonicalizeTreeOptRand at hMem
    rw [evalLatchedAdaptiveTree_sign] at hMem
    by_cases hAdmit : latchOn = false ∨ lo ≤ (canonicalizeQueryOptRand q0).epoch
    · rw [ite_eq_left hAdmit] at hMem
      rcases List.mem_cons.mp hMem with rfl | hTail
      · exact canonicalOptRand_spec q0.randomness
      · exact evalLatched_canonicalize_log_optRand latchOn raw sign _ _ q hTail
    · rw [ite_eq_right hAdmit] at hMem
      exact evalLatched_canonicalize_log_optRand latchOn raw sign (next none) lo q hMem

/-- **Interactive `Code byteOracleIface Bool` Distinguisher for Hop 1 (`prfMsgHopTreeCode`).** -/
def prfMsgHopTreeCode (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed skSeed : List UInt8) (pk : PqPublicKey) :
    ProdAdaptiveTree (List UInt8 × PqHashSig) → Nat → List (List UInt8 × PqHashSig) →
    Spec.Code Spec.byteOracleIface Bool
  | .pure (msgStar, sigStar), _, log =>
    .ret (verifyProductionPqHashSig suite params pk msgStar sigStar &&
      decide (msgStar ∉ log.map Prod.fst))
  | .hashQuery x next, lo, log =>
    prfMsgHopTreeCode suite params pkSeed skSeed pk (next (suite.rawHash x)) lo log
  | .signQuery q next, lo, log =>
    if params.statefulJorts = false ∨ lo ≤ q.epoch then
      let guardFail :=
        if params.statefulJorts then
          !params.productionWellFormed || !params.productionLeafIdxInRange q.epoch
        else !params.productionWellFormed
      let lo' := if params.statefulJorts then q.epoch + 1 else lo
      if guardFail then
        prfMsgHopTreeCode suite params pkSeed skSeed pk (next none) lo' log
      else
        let mu := thPreHash suite pk.pkSeed pk.pkRoot q.message
        .call (encodePrfMsg65 q.randomness mu) (fun rRand =>
          let sigOpt := signCoreWithRand suite params pkSeed skSeed q rRand
          let log' := match sigOpt with
            | some sig => log ++ [(q.message, sig)]
            | none => log
          prfMsgHopTreeCode suite params pkSeed skSeed pk (next sigOpt) lo' log')
    else
      prfMsgHopTreeCode suite params pkSeed skSeed pk (next none) lo log

/-- **Hop-1 PRF Distinguisher (`prfMsgHopDistinguisher`)** making at most `qSign` queries to
    `Spec.byteOracleIface`. -/
def prfMsgHopDistinguisher {qHash qSign : Nat} (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed skSeed : List UInt8) (A : SeedWithheldEufCmaAdv qHash qSign) :
    Spec.Code Spec.byteOracleIface Bool :=
  let pk := derivePublicKey suite params ⟨skSeed, [], pkSeed⟩
  prfMsgHopTreeCode suite params pkSeed skSeed pk ((canonicalizeAdvOptRand A).run pk) 0 []

private theorem prfMsgHopTreeCode_within (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed skSeed : List UInt8) (pk : PqPublicKey) :
    ∀ {qH qS : Nat} (t : ProdAdaptiveTree (List UInt8 × PqHashSig)) (lo : Nat)
      (log : List (List UInt8 × PqHashSig)),
      ProdDualBounded qH qS t →
      Spec.Within qS (prfMsgHopTreeCode suite params pkSeed skSeed pk t lo log)
  | _, qS, .pure (_, _), _, _, _ => .ret qS _
  | 0, _, .hashQuery _ _, _, _, h => False.elim h
  | _ + 1, _, .hashQuery x next, lo, log, h =>
    prfMsgHopTreeCode_within suite params pkSeed skSeed pk (next (suite.rawHash x)) lo log (h _)
  | _, 0, .signQuery _ _, _, _, h => False.elim h
  | _, qS + 1, .signQuery q next, lo, log, h => by
    unfold prfMsgHopTreeCode
    by_cases hAdm : params.statefulJorts = false ∨ lo ≤ q.epoch
    · rw [ite_eq_left hAdm]
      dsimp only
      split
      · exact Spec.Within.mono (Nat.le_succ qS)
          (prfMsgHopTreeCode_within suite params pkSeed skSeed pk (next none) _ log (h none))
      · exact .call (E := Spec.byteOracleIface) _ _ (fun _ =>
          prfMsgHopTreeCode_within suite params pkSeed skSeed pk _ _ _ (h _))
    · rw [ite_eq_right hAdm]
      exact Spec.Within.mono (Nat.le_succ qS)
        (prfMsgHopTreeCode_within suite params pkSeed skSeed pk (next none) lo log (h none))

theorem prfMsgHopDistinguisher_within {qHash qSign : Nat} (suite : TweakableHashSuite)
    (params : PqHashParams) (pkSeed skSeed : List UInt8) (A : SeedWithheldEufCmaAdv qHash qSign) :
    Spec.Within qSign (prfMsgHopDistinguisher suite params pkSeed skSeed A) :=
  prfMsgHopTreeCode_within suite params pkSeed skSeed _ _ 0 []
    ((canonicalizeAdvOptRand A).bounded _)

private theorem prfMsgHopTreeCode_play (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed skSeed : List UInt8) (f : Spec.Bytes → Spec.Bytes) (qPrf : Nat) :
    ∀ {qH qS : Nat} (t : ProdAdaptiveTree (List UInt8 × PqHashSig)) (lo used : Nat)
      (log : List (List UInt8 × PqHashSig)),
      ProdDualBounded qH qS t →
      used + qS ≤ qPrf →
      (Spec.Code.play (Spec.budgetedFunOracle f qPrf)
        (prfMsgHopTreeCode suite params pkSeed skSeed
          (derivePublicKey suite params ⟨skSeed, [], pkSeed⟩) t lo log) used).1 =
      (verifyProductionPqHashSig suite params
          (derivePublicKey suite params ⟨skSeed, [], pkSeed⟩)
          (evalLatchedAdaptiveTree params.statefulJorts suite.rawHash
            (signQueryWithRandFn suite params pkSeed skSeed f) t lo).1.1
          (evalLatchedAdaptiveTree params.statefulJorts suite.rawHash
            (signQueryWithRandFn suite params pkSeed skSeed f) t lo).1.2 &&
        decide ((evalLatchedAdaptiveTree params.statefulJorts suite.rawHash
            (signQueryWithRandFn suite params pkSeed skSeed f) t lo).1.1 ∉
          (log ++ signLogFromOracle (signQueryWithRandFn suite params pkSeed skSeed f)
            (evalLatchedAdaptiveTree params.statefulJorts suite.rawHash
              (signQueryWithRandFn suite params pkSeed skSeed f) t lo).2).map Prod.fst))
  | _, _, .pure (msgStar, sigStar), _, used, log, _, _ => by
    unfold prfMsgHopTreeCode
    rw [Spec.Code.play_ret, evalLatchedAdaptiveTree.public_eq_1]
    dsimp only [signLogFromOracle]
    rw [List.append_nil]
  | 0, _, .hashQuery _ _, _, _, _, hB, _ => False.elim hB
  | _ + 1, _, .hashQuery x next, lo, used, log, hB, hUsed => by
    unfold prfMsgHopTreeCode
    rw [evalLatchedAdaptiveTree.public_eq_2]
    exact prfMsgHopTreeCode_play suite params pkSeed skSeed f qPrf (next (suite.rawHash x)) lo used
      log (hB _) hUsed
  | _, 0, .signQuery _ _, _, _, _, hB, _ => False.elim hB
  | _, qS + 1, .signQuery q next, lo, used, log, hB, hUsed => by
    unfold prfMsgHopTreeCode
    rw [evalLatchedAdaptiveTree_sign]
    by_cases hAdm : params.statefulJorts = false ∨ lo ≤ q.epoch
    · rw [ite_eq_left hAdm, ite_eq_left hAdm]
      dsimp only
      let pk := derivePublicKey suite params ⟨skSeed, [], pkSeed⟩
      let signFn := signQueryWithRandFn suite params pkSeed skSeed f
      let lo' := if params.statefulJorts then q.epoch + 1 else lo
      have hGuardSplit :
          ((if params.statefulJorts then
              !params.productionWellFormed || !params.productionLeafIdxInRange q.epoch
            else !params.productionWellFormed) = true ∧ signFn q = none) ∨
          ((if params.statefulJorts then
              !params.productionWellFormed || !params.productionLeafIdxInRange q.epoch
            else !params.productionWellFormed) = false ∧
            signFn q = signCoreWithRand suite params pkSeed skSeed q
              (f (encodePrfMsg65 q.randomness (thPreHash suite pk.pkSeed pk.pkRoot q.message)))) := by
        dsimp only [signFn]
        unfold signQueryWithRandFn
        by_cases hSt : params.statefulJorts
        · simp only [hSt, ↓reduceIte]
          cases (!params.productionWellFormed || !params.productionLeafIdxInRange q.epoch)
          · exact .inr ⟨rfl, rfl⟩
          · exact .inl ⟨rfl, rfl⟩
        · simp only [hSt, Bool.false_eq_true, ↓reduceIte]
          cases (!params.productionWellFormed)
          · exact .inr ⟨rfl, rfl⟩
          · exact .inl ⟨rfl, rfl⟩
      rcases hGuardSplit with ⟨hGTrue, hSignNone⟩ | ⟨hGFalse, hSignSome⟩
      · rw [hGTrue]
        dsimp only [↓reduceIte]
        have ih := prfMsgHopTreeCode_play suite params pkSeed skSeed f qPrf (next none) lo' used log
          (hB none) (by omega)
        change _ = (verifyProductionPqHashSig suite params pk _ _ &&
          decide (_ ∉ (log ++ signLogFromOracle signFn (q :: _)).map Prod.fst))
        unfold signLogFromOracle
        rw [hSignNone, List.nil_append, hSignNone]
        exact ih
      · rw [hGFalse]
        dsimp only [Bool.false_eq_true, ↓reduceIte]
        rw [Spec.Code.play_call]
        have hLtQ : used < qPrf := by omega
        have hOracle : Spec.budgetedFunOracle f qPrf used
            (encodePrfMsg65 q.randomness (thPreHash suite pk.pkSeed pk.pkRoot q.message)) =
            (f (encodePrfMsg65 q.randomness (thPreHash suite pk.pkSeed pk.pkRoot q.message)),
             used + 1) := by
          rw [Spec.budgetedFunOracle.public_eqs, ite_eq_left hLtQ]
        rw [hOracle]
        dsimp only
        change _ = (verifyProductionPqHashSig suite params pk _ _ &&
          decide (_ ∉ (log ++ signLogFromOracle signFn (q :: _)).map Prod.fst))
        rw [← hSignSome]
        have ih := prfMsgHopTreeCode_play suite params pkSeed skSeed f qPrf (next (signFn q)) lo'
          (used + 1)
          (match signFn q with | some sig => log ++ [(q.message, sig)] | none => log)
          (hB (signFn q)) (by omega)
        rw [ih]
        unfold signLogFromOracle
        cases signFn q <;> simp [List.append_assoc]
    · rw [ite_eq_right hAdm, ite_eq_right hAdm]
      exact prfMsgHopTreeCode_play suite params pkSeed skSeed f qPrf (next none) lo used log
        (hB none) (by omega)

/-- **Hop 1 Theorem (`hulsing_hop1_prfMsg_idealization`).**
    Replaces `thPrfMsg suite sk.skPrf` across all `≤ qSign` adaptive signing queries (both
    deterministic `[]` and adversary-chosen 32-byte `randomness`) with uniform `rfMsg`, paying
    at most `+ εPrfMsg` under `Spec.PrfHard` while leaving `suite.rawHash` 100% untouched. -/
theorem hulsing_hop1_prfMsg_idealization {n nC nA qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (keyLen qPrf : Nat) (hqPrf : qSign ≤ qPrf)
    (π : Spec.CoinSplit n nC nA)
    (sampleMsg : Fin nC → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSampleMsg : Spec.UniformOn (Spec.PrfSampleOk keyLen 65 32) sampleMsg)
    (pkSeedA skSeedA : Fin nA → List UInt8)
    (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    {𝒜Msg : Spec.Code Spec.byteOracleIface Bool → Prop}
    (hClassMsg : ∀ a : Fin nA,
      𝒜Msg (prfMsgHopDistinguisher suite params (pkSeedA a) (skSeedA a) (adv a)))
    {εPrfMsg : Spec.RatBound}
    (hPrfMsg : Spec.PrfHard 𝒜Msg (suitePrfMsg65 suite) keyLen 65 32 qPrf εPrfMsg) :
    let keygenReal : Fin n → PqSecretKey := fun ω =>
      ⟨skSeedA (π.advc ω), (sampleMsg (π.chal ω)).1, pkSeedA (π.advc ω)⟩
    let advReal : Fin n → SeedWithheldEufCmaAdv qHash qSign := fun ω =>
      canonicalizeAdvOptRand (adv (π.advc ω))
    let gIdeal := ExecEufCmaRandIdealGame hPos suite params
      (fun ω => pkSeedA (π.advc ω)) (fun ω => skSeedA (π.advc ω))
      (fun ω => (sampleMsg (π.chal ω)).2) (fun ω => adv (π.advc ω))
    Spec.GameBound
      (ExecEufCmaGame hPos suite params keygenReal advReal).winProb
      (gIdeal.winProb.add εPrfMsg) := by
  intro keygenReal advReal gIdeal
  let D : Fin nA → Spec.Code Spec.byteOracleIface Bool := fun a =>
    prfMsgHopDistinguisher suite params (pkSeedA a) (skSeedA a) (adv a)
  have hRealEq : ∀ ω : Fin n,
      (ExecEufCmaGame hPos suite params keygenReal advReal).win ω =
      (Spec.prfRealGame hPos (suitePrfMsg65 suite) qPrf
        (fun z => (sampleMsg (π.chal z)).1) (fun z => D (π.advc z))).win ω := by
    intro ω
    rw [Spec.prfRealGame.public_eqs]
    dsimp only [D, prfMsgHopDistinguisher]
    have hPlay := prfMsgHopTreeCode_play suite params (pkSeedA (π.advc ω)) (skSeedA (π.advc ω))
      (suitePrfMsg65 suite (sampleMsg (π.chal ω)).1) qPrf
      ((advReal ω).run (derivePublicKey suite params ⟨skSeedA (π.advc ω), [], pkSeedA (π.advc ω)⟩))
      0 0 [] ((advReal ω).bounded _) (by omega)
    rw [List.nil_append] at hPlay
    rw [hPlay]
    rw [ExecEufCmaGame, execEufCmaGameWith_win, prodEufCmaWin_eq]
    unfold execEufCmaOutcome
    dsimp only [keygenReal]
    have hPkEq : derivePublicKey suite params ⟨skSeedA (π.advc ω), [], pkSeedA (π.advc ω)⟩ =
        derivePublicKey suite params
          ⟨skSeedA (π.advc ω), (sampleMsg (π.chal ω)).1, pkSeedA (π.advc ω)⟩ :=
      (derivePublicKey_skPrf_irrel suite params
        ⟨skSeedA (π.advc ω), (sampleMsg (π.chal ω)).1, pkSeedA (π.advc ω)⟩ []).symm
    let t := (advReal ω).run
      (derivePublicKey suite params ⟨skSeedA (π.advc ω), [], pkSeedA (π.advc ω)⟩)
    have hTreeEq :
        evalLatchedAdaptiveTree params.statefulJorts suite.rawHash
          (signQueryWithRandFn suite params (pkSeedA (π.advc ω)) (skSeedA (π.advc ω))
            (suitePrfMsg65 suite (sampleMsg (π.chal ω)).1)) t 0 =
        evalLatchedAdaptiveTree params.statefulJorts suite.rawHash
          (prodSignQuery suite params
            ⟨skSeedA (π.advc ω), (sampleMsg (π.chal ω)).1, pkSeedA (π.advc ω)⟩) t 0 := by
      refine evalLatchedAdaptiveTree_congr_on_log suite.rawHash _ _ t 0 (fun q hq => ?_)
      have hOpt := evalLatched_canonicalize_log_optRand params.statefulJorts suite.rawHash _
        ((adv (π.advc ω)).run _) 0 q hq
      exact signQueryWithRandFn_real_eq suite params
        ⟨skSeedA (π.advc ω), (sampleMsg (π.chal ω)).1, pkSeedA (π.advc ω)⟩ q hOpt
    have hLogOpt : ∀ q ∈ (evalLatchedAdaptiveTree params.statefulJorts suite.rawHash
        (prodSignQuery suite params
          ⟨skSeedA (π.advc ω), (sampleMsg (π.chal ω)).1, pkSeedA (π.advc ω)⟩) t 0).2,
        q.randomness = [] ∨ q.randomness.length = 32 := fun q hq =>
      evalLatched_canonicalize_log_optRand params.statefulJorts suite.rawHash _ _ 0 q hq
    change _ = (verifyProductionPqHashSig suite params _
      (evalLatchedAdaptiveTree _ _ _ ((advReal ω).run _) 0).1.1
      (evalLatchedAdaptiveTree _ _ _ ((advReal ω).run _) 0).1.2 && _)
    rw [← hPkEq]
    change (verifyProductionPqHashSig suite params _
        (evalLatchedAdaptiveTree _ _ _ t 0).1.1
        (evalLatchedAdaptiveTree _ _ _ t 0).1.2 &&
      decide (_ ∉ (signLogFromOracle _ (evalLatchedAdaptiveTree _ _ _ t 0).2).map Prod.fst)) = _
    rw [hTreeEq, signLogFromOracle_eq_productionSigningLog suite params
      ⟨skSeedA (π.advc ω), (sampleMsg (π.chal ω)).1, pkSeedA (π.advc ω)⟩ _ hLogOpt]
  have hIdealEq : ∀ ω : Fin n,
      gIdeal.win ω =
      (Spec.prfIdealGame hPos qPrf
        (fun z => (sampleMsg (π.chal z)).2) (fun z => D (π.advc z))).win ω := by
    intro ω
    rw [Spec.prfIdealGame.public_eqs]
    dsimp only [D, gIdeal, ExecEufCmaRandIdealGame, prfMsgHopDistinguisher]
    have hPlay := prfMsgHopTreeCode_play suite params (pkSeedA (π.advc ω)) (skSeedA (π.advc ω))
      ((sampleMsg (π.chal ω)).2) qPrf
      ((canonicalizeAdvOptRand (adv (π.advc ω))).run
        (derivePublicKey suite params ⟨skSeedA (π.advc ω), [], pkSeedA (π.advc ω)⟩))
      0 0 [] ((canonicalizeAdvOptRand (adv (π.advc ω))).bounded _) (by omega)
    rw [List.nil_append] at hPlay
    exact hPlay.symm
  have hDist : Spec.GameBound
      (Spec.AdvDist (ExecEufCmaGame hPos suite params keygenReal advReal) gIdeal) εPrfMsg := by
    rw [Spec.FinGame.ext_win hRealEq, Spec.FinGame.ext_win hIdealEq]
    exact hPrfMsg n nC nA hPos π sampleMsg hSampleMsg D hClassMsg
  exact Spec.RatBound.le_trans
    (winProb_le_add_advDist (ExecEufCmaGame hPos suite params keygenReal advReal) gIdeal)
    (Spec.RatBound.add_le_add (Spec.RatBound.le_refl _) hDist)

/-- `#tooth` A constant empty randomizer fails `PrfHard` whenever `suitePrfMsg65` is replaced by
    `fun _ _ => []` (`outLen = 32`). -/
theorem prfMsg_empty_refuted {nC : Nat} (hPos : 0 < nC) (keyLen q : Nat) (hq : 0 < q)
    (sample : Fin nC → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hU : Spec.UniformOn (Spec.PrfSampleOk keyLen 65 32) sample)
    (𝒜 : Spec.Code Spec.byteOracleIface Bool → Prop)
    (h𝒜 : 𝒜 (Spec.emptyOutputDistinguisher 65))
    {ε : Spec.RatBound} (hε : ε.num < ε.den) :
    ¬ Spec.PrfHard 𝒜 (fun _ _ => []) keyLen 65 32 q ε :=
  Spec.prfHard_emptyOutput_refuted hPos keyLen 65 32 q sample hU 𝒜 h𝒜 (by decide) hq hε

#verify_constructive
  Qsag.derivePublicKey_skPrf_irrel
  Qsag.signProductionHypertreeCore_skPrf_irrel
  Qsag.suitePrfMsg65_encodePrfMsg65
  Qsag.signQueryWithRandFn_real_eq
  Qsag.prfMsgHopDistinguisher_within
  Qsag.hulsing_hop1_prfMsg_idealization
  Qsag.prfMsg_empty_refuted

#tooth_pair Qsag.hulsing_hop1_prfMsg_idealization vs Qsag.prfMsg_empty_refuted

end Qsag
end

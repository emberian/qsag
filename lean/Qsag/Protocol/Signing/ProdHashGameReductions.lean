module
public import Qsag.Protocol.Signing.ProdCollisionAccounting
import all Qsag.Protocol.Signing.ProdCollisionAccounting
import all Qsag.Protocol.Signing.ProdCollisionEvents
import all Qsag.Protocol.Signing.ProdCollisionExtraction
import all Qsag.Protocol.Signing.ProdCollisionLayers
import all Qsag.Protocol.Signing.ProdCollisionWitness
import all Qsag.Protocol.Signing.HypertreeEufCma
import all Qsag.Protocol.Signing.HashSigs
import all Qsag.Oracle.UcGames
import Qsag.Tactic.AssuranceKit

/-!
# Qsag.Protocol.Signing.ProdHashGameReductions — Seed-Withheld `Within` Hash-Signature Game Reductions

`ProdCollisionWitness`, `ProdCollisionLayers`, `ProdCollisionExtraction`, `ProdCollisionEvents`,
and `ProdCollisionAccounting` classify an accepted production forgery into FORS index coverage, a
returned `ProdTcrWitness` along the verification path, or `ProdPreimageBreak`, and bound the number
of candidate on-path targets per forgery by `prodPathTargetCount params q_sign`. Those modules are
deterministic over outcomes containing the full secret key `sk` and do not model hash or signing
access as query-bounded oracles.

This module constructs explicit seed-withheld, query-counted challenger games and reduction
algorithms (`HashSignAdv`, `Within q_hash q_sign`):

1. **Seed-Withheld Two-Oracle Model (`HashSignAdv`, `Within`, `challengerSignStep`):**
   Adversaries have type `PqPublicKey → HashSignAdv Out`: they receive only
   `pk = derivePublicKey suite params sk` (`pkSeed`, `pkRoot`). Secret seeds `sk.skSeed` and
   `sk.skPrf` are syntactically absent from the adversary's input (`runHashSignAdv_seed_withheld`)
   and enter only through `challengerSignStep`, which enforces stateful Jorts one-time epoch
   discipline (`runHashSignAdv_queries_oneTime`) while permitting idempotent retries.
2. **Public Oracle Verifier & Candidate Collectors (`0` Secret-Seed Access):**
   `advVerifyProductionPqHashSig`, `advCollectTcrCandidates`, and `advCollectPreCandidates`
   execute the production verifier walk using only `queryHash` calls (`Within
   (prodVerifierHashBudget params) 0`), producing candidate lists of bounded sizes
   `prodPathTargetCount params q_sign` and `prodPreCandidateCount params` without touching `sk`.
3. **Explicit `Within` Challenger Games & Reductions (`PRF`, `SM_DT_UD`, `ITSR`, `SM_DT_TCR`,
   `SM_DT_PRE`):**
   * `prfExtractorAdv` and `udExtractorAdv` bound the distinguishing hops from the real keyed
     suite (`pubSuite`) to the PRF-idealized suite (`prfSuite`) and chain-undetectability suite
     (`udSuite`) within `q_hash + prodVerifierHashBudget params` hash queries and `q_sign`
     signing queries.
   * `itsrExtractorAdv`, `tcrExtractorAdv`, and `preExtractorAdv` reduce terminal forgeries in
     the idealized experiment to explicit `Within`-bounded `ITSR`, `SM_DT_TCR`, and `SM_DT_PRE`
     challenger games, constructively discharging `ProdSmTcrBreak`
     (`smDtTcrWithinWin_discharges_prodSmTcrBreak`) and proving the concrete advantage sum bound
     `production_euf_cma_within_game_reduction_bound`.
-/

public section
namespace Qsag

set_option autoImplicit false

/-! ## 1. Seed-Withheld Two-Oracle Decision Trees (`HashSignAdv` & `Within`) -/

/-- Adaptive decision tree making raw tweakable-hash queries and signing queries.
    An adversary of type `PqPublicKey → HashSignAdv Out` receives only `pk` (`pkSeed`, `pkRoot`);
    `sk.skSeed` and `sk.skPrf` are withheld from its view. -/
inductive HashSignAdv (Out : Type) : Type where
  | done (out : Out)
  | queryHash (x : List UInt8) (k : List UInt8 → HashSignAdv Out)
  | querySign (q : ProdSigningQuery) (k : Option PqHashSig → HashSignAdv Out)

def HashSignAdv.bind {α β : Type} : HashSignAdv α → (α → HashSignAdv β) → HashSignAdv β
  | .done a, f => f a
  | .queryHash x k, f => .queryHash x (fun h => (k h).bind f)
  | .querySign q k, f => .querySign q (fun s => (k s).bind f)

def HashSignAdv.map {α β : Type} (f : α → β) (m : HashSignAdv α) : HashSignAdv β :=
  m.bind (fun a => .done (f a))

/-- Worst-case adaptive query budget: at most `qh` raw-hash queries and `qs` signing queries. -/
def HashSignAdv.Within {Out : Type} : Nat → Nat → HashSignAdv Out → Prop
  | _, _, .done _ => True
  | 0, _, .queryHash _ _ => False
  | qh + 1, qs, .queryHash _ k => ∀ y, (k y).Within qh qs
  | _, 0, .querySign _ _ => False
  | qh, qs + 1, .querySign _ k => ∀ s, (k s).Within qh qs

theorem HashSignAdv.Within.done {Out : Type} (out : Out) (qh qs : Nat) :
    (HashSignAdv.done out).Within qh qs :=
  trivial

theorem HashSignAdv.Within.mono {Out : Type} {qh₁ qh₂ qs₁ qs₂ : Nat} {m : HashSignAdv Out}
    (h : m.Within qh₁ qs₁) (hh : qh₁ ≤ qh₂) (hs : qs₁ ≤ qs₂) : m.Within qh₂ qs₂ := by
  induction m generalizing qh₁ qh₂ qs₁ qs₂ with
  | done _ => trivial
  | queryHash _ _ ih =>
    cases qh₁ with
    | zero => cases h
    | succ _ =>
      cases qh₂ with
      | zero => omega
      | succ _ =>
        intro y
        exact ih y (h y) (by omega) hs
  | querySign _ _ ih =>
    cases qs₁ with
    | zero => cases h
    | succ _ =>
      cases qs₂ with
      | zero => omega
      | succ _ =>
        intro s
        exact ih s (h s) hh (by omega)

theorem HashSignAdv.Within.bind {α β : Type} {qh₁ qh₂ qs₁ qs₂ : Nat}
    {m : HashSignAdv α} {f : α → HashSignAdv β}
    (hm : m.Within qh₁ qs₁) (hf : ∀ a, (f a).Within qh₂ qs₂) :
    (m.bind f).Within (qh₁ + qh₂) (qs₁ + qs₂) := by
  induction m generalizing qh₁ qs₁ with
  | done a =>
    exact (hf a).mono (by omega) (by omega)
  | queryHash _ _ ih =>
    cases qh₁ with
    | zero => cases hm
    | succ _ =>
      rw [Nat.succ_add]
      intro y
      exact ih y (hm y)
  | querySign _ _ ih =>
    cases qs₁ with
    | zero => cases hm
    | succ _ =>
      rw [Nat.succ_add]
      intro s
      exact ih s (hm s)

theorem HashSignAdv.Within.bind_le {α β : Type} {qh₁ qh₂ qh qs₁ qs₂ qs : Nat}
    {m : HashSignAdv α} {f : α → HashSignAdv β}
    (hm : m.Within qh₁ qs₁) (hf : ∀ a, (f a).Within qh₂ qs₂)
    (hh : qh₁ + qh₂ ≤ qh) (hs : qs₁ + qs₂ ≤ qs) :
    (m.bind f).Within qh qs :=
  (HashSignAdv.Within.bind hm hf).mono hh hs

theorem HashSignAdv.Within.map {α β : Type} {qh qs : Nat} (f : α → β) {m : HashSignAdv α}
    (hm : m.Within qh qs) : (m.map f).Within qh qs := by
  unfold HashSignAdv.map
  exact HashSignAdv.Within.bind_le (qh₂ := 0) (qs₂ := 0) hm
    (fun a => HashSignAdv.Within.done (f a) 0 0) (Nat.le_refl qh) (Nat.le_refl qs)

def advRawHash (x : List UInt8) : HashSignAdv (List UInt8) :=
  .queryHash x .done

def advThCall (roleTag pkSeed : List UInt8) (adrs : HashAdrs) (args : List (List UInt8)) :
    HashSignAdv (List UInt8) :=
  advRawHash (thPreimage roleTag pkSeed adrs args)

theorem advRawHash_within (x : List UInt8) : (advRawHash x).Within 1 0 :=
  fun _ => trivial

theorem advThCall_within (roleTag pkSeed : List UInt8) (adrs : HashAdrs)
    (args : List (List UInt8)) : (advThCall roleTag pkSeed adrs args).Within 1 0 :=
  fun _ => trivial

/-! ## 2. Stateful One-Time Challenger Signing Step & Seed Withholding -/

deriving instance DecidableEq for ProdSigningQuery
deriving instance DecidableEq for ProdTargetIdx

/-- Decidable check for a conflicting stateful epoch request: in `statefulJorts` mode, an epoch
    already bound to a distinct `ProdSigningQuery` is refused; identical crash-retries are allowed. -/
def challengerEpochConflict (params : PqHashParams) (qs : List ProdSigningQuery)
    (q : ProdSigningQuery) : Bool :=
  params.statefulJorts && qs.any (fun q₀ => decide (q₀.epoch = q.epoch ∧ q₀ ≠ q))

/-- Challenger signing oracle transition maintaining accepted non-conflicting queries `qs`. -/
def challengerSignStep (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (qs : List ProdSigningQuery) (q : ProdSigningQuery) :
    Option PqHashSig × List ProdSigningQuery :=
  if challengerEpochConflict params qs q then
    (none, qs)
  else
    (prodSignQuery suite params sk q, q :: qs)

/-- Execute a `HashSignAdv` tree against `(suite, params, sk)`, returning `(out, acceptedQueries)`. -/
def runHashSignAdv {Out : Type} (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) : List ProdSigningQuery → HashSignAdv Out → Out × List ProdSigningQuery
  | qs, .done out => (out, qs)
  | qs, .queryHash x k => runHashSignAdv suite params sk qs (k (suite.rawHash x))
  | qs, .querySign q k =>
    let step := challengerSignStep suite params sk qs q
    runHashSignAdv suite params sk step.2 (k step.1)

theorem runHashSignAdv_bind {α β : Type} (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (qs : List ProdSigningQuery) (m : HashSignAdv α)
    (f : α → HashSignAdv β) :
    runHashSignAdv suite params sk qs (m.bind f) =
      let r := runHashSignAdv suite params sk qs m
      runHashSignAdv suite params sk r.2 (f r.1) := by
  induction m generalizing qs with
  | done _ => rfl
  | queryHash x _ ih => exact ih (suite.rawHash x) qs
  | querySign q _ ih =>
    exact ih (challengerSignStep suite params sk qs q).1
      (challengerSignStep suite params sk qs q).2

/-- Semantic seed withholding: any adversary `A : PqPublicKey → HashSignAdv Out` depends on `sk`
    exclusively through `derivePublicKey` and the oracle responses along its queried transcript. -/
theorem runHashSignAdv_seed_withheld {Out : Type} (suite₁ suite₂ : TweakableHashSuite)
    (params : PqHashParams) (sk₁ sk₂ : PqSecretKey)
    (A : PqPublicKey → HashSignAdv Out)
    (hPk : derivePublicKey suite₁ params sk₁ = derivePublicKey suite₂ params sk₂)
    (hHash : ∀ x, suite₁.rawHash x = suite₂.rawHash x)
    (hSign : ∀ q, prodSignQuery suite₁ params sk₁ q = prodSignQuery suite₂ params sk₂ q) :
    runHashSignAdv suite₁ params sk₁ [] (A (derivePublicKey suite₁ params sk₁)) =
      runHashSignAdv suite₂ params sk₂ [] (A (derivePublicKey suite₂ params sk₂)) := by
  rw [hPk]
  generalize A (derivePublicKey suite₂ params sk₂) = m
  suffices ∀ qs, runHashSignAdv suite₁ params sk₁ qs m = runHashSignAdv suite₂ params sk₂ qs m from
    this []
  induction m with
  | done _ => intro _; rfl
  | queryHash x _ ih =>
    intro qs
    simp only [runHashSignAdv, hHash x]
    exact ih _ _
  | querySign q _ ih =>
    intro qs
    simp only [runHashSignAdv, challengerSignStep, hSign q]
    exact ih _ _

/-- One-time stateful epoch invariant on a list of queries. -/
abbrev QueriesOneTime (params : PqHashParams) (qs : List ProdSigningQuery) : Prop :=
  params.statefulJorts = true → ∀ q, q ∈ qs → ∀ q', q' ∈ qs → q.epoch = q'.epoch → q = q'

theorem challengerSignStep_preserves_oneTime (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) {qs : List ProdSigningQuery} (q : ProdSigningQuery)
    (hOT : QueriesOneTime params qs) :
    QueriesOneTime params (challengerSignStep suite params sk qs q).2 := by
  unfold challengerSignStep
  cases hConf : challengerEpochConflict params qs q
  · simp only [Bool.false_eq_true, ↓reduceIte]
    intro hSt a ha b hb hEp
    have hNoAny : qs.any (fun q₀ => decide (q₀.epoch = q.epoch ∧ q₀ ≠ q)) = false := by
      unfold challengerEpochConflict at hConf
      rw [hSt, Bool.true_and] at hConf
      exact hConf
    have hCompat : ∀ q₀ ∈ qs, q₀.epoch = q.epoch → q₀ = q := by
      intro q₀ hMem hE
      by_cases hEq : q₀ = q
      · exact hEq
      · exfalso
        have hTrue : qs.any (fun r => decide (r.epoch = q.epoch ∧ r ≠ q)) = true :=
          List.any_eq_true.mpr ⟨q₀, hMem, decide_eq_true ⟨hE, hEq⟩⟩
        rw [hNoAny] at hTrue
        cases hTrue
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact (hCompat b hb' hEp.symm).symm
    · exact hCompat a ha' hEp
    · exact hOT hSt a ha' b hb' hEp
  · simp only [↓reduceIte]
    exact hOT

theorem runHashSignAdv_preserves_oneTime {Out : Type} (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) :
    ∀ (qs : List ProdSigningQuery) (m : HashSignAdv Out),
      QueriesOneTime params qs →
      QueriesOneTime params (runHashSignAdv suite params sk qs m).2
  | _, .done _, hOT => hOT
  | qs, .queryHash x k, hOT =>
    runHashSignAdv_preserves_oneTime suite params sk qs (k (suite.rawHash x)) hOT
  | qs, .querySign q k, hOT =>
    runHashSignAdv_preserves_oneTime suite params sk _
      (k (challengerSignStep suite params sk qs q).1)
      (challengerSignStep_preserves_oneTime suite params sk q hOT)

theorem runHashSignAdv_queries_oneTime {Out : Type} (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) (m : HashSignAdv Out) :
    QueriesOneTime params (runHashSignAdv suite params sk [] m).2 :=
  runHashSignAdv_preserves_oneTime suite params sk [] m (fun _ _ h => by cases h)

theorem runHashSignAdv_queries_length_le {Out : Type} (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) :
    ∀ {qh qs_max : Nat} (qs : List ProdSigningQuery) (m : HashSignAdv Out),
      m.Within qh qs_max →
      (runHashSignAdv suite params sk qs m).2.length ≤ qs.length + qs_max
  | _, _, qs, .done _, _ => Nat.le_add_right _ _
  | 0, _, _, .queryHash _ _, hW => absurd hW id
  | _ + 1, _, qs, .queryHash x k, hW =>
    runHashSignAdv_queries_length_le suite params sk qs (k (suite.rawHash x)) (hW (suite.rawHash x))
  | _, 0, _, .querySign _ _, hW => absurd hW id
  | _, qs_max + 1, qs, .querySign q k, hW => by
    dsimp only [runHashSignAdv]
    have hStepLen : (challengerSignStep suite params sk qs q).2.length ≤ qs.length + 1 := by
      unfold challengerSignStep
      cases challengerEpochConflict params qs q <;> simp
    have ih := runHashSignAdv_queries_length_le suite params sk
      (challengerSignStep suite params sk qs q).2
      (k (challengerSignStep suite params sk qs q).1)
      (hW (challengerSignStep suite params sk qs q).1)
    omega

/-- Wrap an adversary tree to record its public `(message, sig)` signing transcript without
    accessing `sk` and without issuing any extra oracle queries. -/
def advTrackSignLog {Out : Type} :
    List (List UInt8 × PqHashSig) → HashSignAdv Out →
    HashSignAdv (Out × List (List UInt8 × PqHashSig))
  | log, .done out => .done (out, log)
  | log, .queryHash x k => .queryHash x (fun h => advTrackSignLog log (k h))
  | log, .querySign q k =>
    .querySign q (fun resp =>
      let log' := match resp with
        | none => log
        | some sig => (q.message, sig) :: log
      advTrackSignLog log' (k resp))

theorem advTrackSignLog_within {Out : Type} {qh qs : Nat}
    (log : List (List UInt8 × PqHashSig)) {m : HashSignAdv Out}
    (hm : m.Within qh qs) : (advTrackSignLog log m).Within qh qs := by
  induction m generalizing qh qs log with
  | done _ => trivial
  | queryHash _ _ ih =>
    cases qh with
    | zero => cases hm
    | succ _ => intro y; exact ih y log (hm y)
  | querySign _ _ ih =>
    cases qs with
    | zero => cases hm
    | succ _ => intro s; exact ih s _ (hm s)

theorem runHashSignAdv_advTrackSignLog {Out : Type} (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) :
    ∀ (qs : List ProdSigningQuery) (log : List (List UInt8 × PqHashSig)) (m : HashSignAdv Out),
      log = productionSigningLog suite params sk qs →
      let r := runHashSignAdv suite params sk qs m
      runHashSignAdv suite params sk qs (advTrackSignLog log m) =
        ((r.1, productionSigningLog suite params sk r.2), r.2)
  | qs, log, .done _, hLog => by simp [advTrackSignLog, runHashSignAdv, hLog]
  | qs, log, .queryHash x k, hLog =>
    runHashSignAdv_advTrackSignLog suite params sk qs log (k (suite.rawHash x)) hLog
  | qs, log, .querySign q k, hLog => by
    dsimp only [advTrackSignLog, runHashSignAdv]
    apply runHashSignAdv_advTrackSignLog
    unfold challengerSignStep
    cases challengerEpochConflict params qs q
    · simp only [Bool.false_eq_true, ↓reduceIte, productionSigningLog]
      cases prodSignQuery suite params sk q <;> simp [hLog]
    · simp [hLog]

/-! ## 3. Public Oracle Verifier & Candidate Collectors (`0` Secret-Seed Access) -/

/-- Explicit hash-query budgets for public stateless XOF derivation, FORS recovery, and hypertree
    layer verification. -/
def prodXofHashBudget (params : PqHashParams) : Nat :=
  if params.statefulJorts then 0
  else
    let forsBytes := (params.forsTrees * params.forsHeight + 7) / 8
    let treeBytes := (params.numLayers * params.subtreeHeight + 7) / 8
    (forsBytes + treeBytes + 31) / 32

def prodForsHashBudget (params : PqHashParams) : Nat :=
  if params.statefulJorts then 0
  else params.forsTrees * (1 + params.forsHeight) + 1

def prodLayerHashBudget (params : PqHashParams) : Nat :=
  1 + params.ell1 * (params.w - 1) + 1 + params.subtreeHeight

def prodVerifierHashBudget (params : PqHashParams) : Nat :=
  1 + prodXofHashBudget params + prodForsHashBudget params +
    params.numLayers * prodLayerHashBudget params

/-- Number of candidate preimage targets carried by one signature (`FORS` leaves + `WOTS` steps). -/
def prodPreCandidateCount (params : PqHashParams) : Nat :=
  params.forsTrees + params.numLayers * (params.ell1 * (params.w - 1))

/-- Single-pass WOTS chain evaluator recording each `(step, preimage)` queried along the chain. -/
def wotsChainWithCands (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp chain : Nat) :
    Nat → Nat → List UInt8 → List UInt8 × List (Nat × List UInt8)
  | _, 0, cur => (cur, [])
  | startStep, k + 1, cur =>
    let adrs : HashAdrs :=
      ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat chain, UInt32.ofNat startStep⟩
    let pre := thPreimage tagThF pkSeed adrs [cur]
    let nextVal := suite.rawHash pre
    let sub := wotsChainWithCands suite pkSeed layer tree kp chain (startStep + 1) k nextVal
    (sub.1, (startStep, pre) :: sub.2)

def advWotsChainWithCands (pkSeed : List UInt8) (layer : UInt32) (tree : UInt64)
    (kp chain : Nat) : Nat → Nat → List UInt8 → HashSignAdv (List UInt8 × List (Nat × List UInt8))
  | _, 0, cur => .done (cur, [])
  | startStep, k + 1, cur =>
    let adrs : HashAdrs :=
      ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat chain, UInt32.ofNat startStep⟩
    let pre := thPreimage tagThF pkSeed adrs [cur]
    (advRawHash pre).bind fun nextVal =>
      (advWotsChainWithCands pkSeed layer tree kp chain (startStep + 1) k nextVal).map fun sub =>
        (sub.1, (startStep, pre) :: sub.2)

theorem wotsChainWithCands_fst (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp chain : Nat) :
    ∀ (s k : Nat) (cur : List UInt8),
      (wotsChainWithCands suite pkSeed layer tree kp chain s k cur).1 =
        wotsChainSteps suite pkSeed layer tree kp chain s k cur
  | _, 0, _ => rfl
  | s, k + 1, cur => by
    simp only [wotsChainWithCands, wotsChainSteps, thChainF_eq, thCall_eq]
    exact wotsChainWithCands_fst suite pkSeed layer tree kp chain (s + 1) k _

theorem wotsChainWithCands_cands_length (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp chain : Nat) :
    ∀ (s k : Nat) (cur : List UInt8),
      (wotsChainWithCands suite pkSeed layer tree kp chain s k cur).2.length = k
  | _, 0, _ => rfl
  | s, k + 1, cur => by
    simp only [wotsChainWithCands, List.length_cons,
      wotsChainWithCands_cands_length suite pkSeed layer tree kp chain (s + 1) k]

theorem advWotsChainWithCands_within (pkSeed : List UInt8) (layer : UInt32) (tree : UInt64)
    (kp chain : Nat) :
    ∀ (s k : Nat) (cur : List UInt8),
      (advWotsChainWithCands pkSeed layer tree kp chain s k cur).Within k 0
  | _, 0, _ => trivial
  | s, k + 1, cur => by
    unfold advWotsChainWithCands
    refine HashSignAdv.Within.bind_le (qh₂ := k) (qs₂ := 0) (advRawHash_within _)
      (fun nextVal => ?_) (by omega) (Nat.le_refl 0)
    exact HashSignAdv.Within.map _
      (advWotsChainWithCands_within pkSeed layer tree kp chain (s + 1) k nextVal)

theorem runHashSignAdv_advWotsChainWithCands (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkSeed : List UInt8) (layer : UInt32) (tree : UInt64) (kp chain : Nat) :
    ∀ (s k : Nat) (cur : List UInt8) (qs : List ProdSigningQuery),
      runHashSignAdv suite params sk qs
          (advWotsChainWithCands pkSeed layer tree kp chain s k cur) =
        (wotsChainWithCands suite pkSeed layer tree kp chain s k cur, qs)
  | _, 0, _, _ => rfl
  | s, k + 1, cur, qs => by
    unfold advWotsChainWithCands wotsChainWithCands HashSignAdv.map
    rw [runHashSignAdv_bind]
    dsimp only [advRawHash, runHashSignAdv]
    rw [runHashSignAdv_bind,
      runHashSignAdv_advWotsChainWithCands suite params sk pkSeed layer tree kp chain (s + 1) k _ qs]
    rfl

/-- Evaluate chains `0 .. m-1`, collecting endpoints and `(r, step, preimage)` candidates. -/
def allWotsChainsWithCands (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (layer : UInt32) (tree : UInt64) (kp : Nat)
    (digF : List Nat) (chains : List (List UInt8)) :
    Nat → List (List UInt8) × List (Nat × Nat × List UInt8)
  | 0 => ([], [])
  | m + 1 =>
    let prev := allWotsChainsWithCands suite params pkSeed layer tree kp digF chains m
    let d := digF.getD m 0
    let rem := params.w - 1 - d
    let ch := wotsChainWithCands suite pkSeed layer tree kp m d rem (chains.getD m [])
    (prev.1 ++ [ch.1], prev.2 ++ ch.2.map (fun sp => (m, sp.1, sp.2)))

def advAllWotsChainsWithCands (params : PqHashParams) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp : Nat) (digF : List Nat) (chains : List (List UInt8)) :
    Nat → HashSignAdv (List (List UInt8) × List (Nat × Nat × List UInt8))
  | 0 => .done ([], [])
  | m + 1 =>
    (advAllWotsChainsWithCands params pkSeed layer tree kp digF chains m).bind fun prev =>
      let d := digF.getD m 0
      let rem := params.w - 1 - d
      (advWotsChainWithCands pkSeed layer tree kp m d rem (chains.getD m [])).map fun ch =>
        (prev.1 ++ [ch.1], prev.2 ++ ch.2.map (fun sp => (m, sp.1, sp.2)))

theorem allWotsChainsWithCands_fst (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (layer : UInt32) (tree : UInt64) (kp : Nat)
    (digF : List Nat) (chains : List (List UInt8)) :
    ∀ m : Nat,
      (allWotsChainsWithCands suite params pkSeed layer tree kp digF chains m).1 =
        (List.range m).map fun r =>
          wotsChainSteps suite pkSeed layer tree kp r (digF.getD r 0)
            (params.w - 1 - digF.getD r 0) (chains.getD r [])
  | 0 => rfl
  | m + 1 => by
    simp only [allWotsChainsWithCands, List.range_succ, List.map_append, List.map_cons,
      List.map_nil, allWotsChainsWithCands_fst suite params pkSeed layer tree kp digF chains m,
      wotsChainWithCands_fst]

theorem allWotsChainsWithCands_cands_length_le (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (layer : UInt32) (tree : UInt64) (kp : Nat)
    (digF : List Nat) (chains : List (List UInt8)) :
    ∀ m : Nat,
      (allWotsChainsWithCands suite params pkSeed layer tree kp digF chains m).2.length ≤
        m * (params.w - 1)
  | 0 => by simp [allWotsChainsWithCands]
  | m + 1 => by
    simp only [allWotsChainsWithCands, List.length_append, List.length_map,
      wotsChainWithCands_cands_length, Nat.succ_mul]
    have ih := allWotsChainsWithCands_cands_length_le suite params pkSeed layer tree kp digF chains m
    omega

theorem advAllWotsChainsWithCands_within (params : PqHashParams) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp : Nat) (digF : List Nat) (chains : List (List UInt8)) :
    ∀ m : Nat,
      (advAllWotsChainsWithCands params pkSeed layer tree kp digF chains m).Within
        (m * (params.w - 1)) 0
  | 0 => trivial
  | m + 1 => by
    unfold advAllWotsChainsWithCands
    have hPrev := advAllWotsChainsWithCands_within params pkSeed layer tree kp digF chains m
    have hStep : ∀ prev : List (List UInt8) × List (Nat × Nat × List UInt8),
        ((advWotsChainWithCands pkSeed layer tree kp m (digF.getD m 0)
          (params.w - 1 - digF.getD m 0) (chains.getD m [])).map
          (fun ch => (prev.1 ++ [ch.1], prev.2 ++ ch.2.map (fun sp => (m, sp.1, sp.2))))).Within
          (params.w - 1) 0 := by
      intro prev
      exact (HashSignAdv.Within.map _ (advWotsChainWithCands_within _ _ _ _ _ _ _ _)).mono
        (by omega) (Nat.le_refl 0)
    exact (HashSignAdv.Within.bind hPrev hStep).mono
      (by rw [Nat.succ_mul]; exact Nat.le_refl _) (Nat.le_refl 0)

theorem runHashSignAdv_advAllWotsChainsWithCands (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkSeed : List UInt8) (layer : UInt32) (tree : UInt64) (kp : Nat)
    (digF : List Nat) (chains : List (List UInt8)) :
    ∀ (m : Nat) (qs : List ProdSigningQuery),
      runHashSignAdv suite params sk qs
          (advAllWotsChainsWithCands params pkSeed layer tree kp digF chains m) =
        (allWotsChainsWithCands suite params pkSeed layer tree kp digF chains m, qs)
  | 0, _ => rfl
  | m + 1, qs => by
    unfold advAllWotsChainsWithCands allWotsChainsWithCands HashSignAdv.map
    rw [runHashSignAdv_bind,
      runHashSignAdv_advAllWotsChainsWithCands suite params sk pkSeed layer tree kp digF chains m qs]
    dsimp only
    rw [runHashSignAdv_bind, runHashSignAdv_advWotsChainWithCands]
    rfl

/-- Key-pair-addressed Merkle auth-path walker recording `(h, d, localBase, preimage)` candidates. -/
def walkMerkleKpWithCands (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kind : AdrsKind) (kp : UInt32) :
    Nat → Nat → Nat → Nat → Nat → List UInt8 → List (List UInt8) →
    Option (List UInt8) × List (Nat × Nat × Nat × List UInt8)
  | 0, _, _, _, _, leaf, [] => (some leaf, [])
  | 0, _, _, _, _, _, _ :: _ => (none, [])
  | _ + 1, _, _, _, _, _, [] => (none, [])
  | h + 1, d, nodeIdx, localBase, localIdx, leaf, sib :: rest =>
    if localIdx < 2 ^ h then
      let sub := walkMerkleKpWithCands suite pkSeed layer tree kind kp h (d + 1)
        (2 * nodeIdx) (2 * localBase) localIdx leaf rest
      match sub.1 with
      | none => (none, sub.2)
      | some sVal =>
        let pre := thPreimage tagThH pkSeed
          ⟨layer, tree, kind, kp, UInt32.ofNat (h + 1), UInt32.ofNat nodeIdx⟩ [sVal, sib]
        (some (suite.rawHash pre), (h, d, localBase, pre) :: sub.2)
    else
      let sub := walkMerkleKpWithCands suite pkSeed layer tree kind kp h (d + 1)
        (2 * nodeIdx + 1) (2 * localBase + 1) (localIdx - 2 ^ h) leaf rest
      match sub.1 with
      | none => (none, sub.2)
      | some sVal =>
        let pre := thPreimage tagThH pkSeed
          ⟨layer, tree, kind, kp, UInt32.ofNat (h + 1), UInt32.ofNat nodeIdx⟩ [sib, sVal]
        (some (suite.rawHash pre), (h, d, localBase, pre) :: sub.2)

def advWalkMerkleKpWithCands (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kind : AdrsKind) (kp : UInt32) :
    Nat → Nat → Nat → Nat → Nat → List UInt8 → List (List UInt8) →
    HashSignAdv (Option (List UInt8) × List (Nat × Nat × Nat × List UInt8))
  | 0, _, _, _, _, leaf, [] => .done (some leaf, [])
  | 0, _, _, _, _, _, _ :: _ => .done (none, [])
  | _ + 1, _, _, _, _, _, [] => .done (none, [])
  | h + 1, d, nodeIdx, localBase, localIdx, leaf, sib :: rest =>
    if localIdx < 2 ^ h then
      (advWalkMerkleKpWithCands pkSeed layer tree kind kp h (d + 1)
        (2 * nodeIdx) (2 * localBase) localIdx leaf rest).bind fun sub =>
        match sub.1 with
        | none => .done (none, sub.2)
        | some sVal =>
          let pre := thPreimage tagThH pkSeed
            ⟨layer, tree, kind, kp, UInt32.ofNat (h + 1), UInt32.ofNat nodeIdx⟩ [sVal, sib]
          (advRawHash pre).map fun top => (some top, (h, d, localBase, pre) :: sub.2)
    else
      (advWalkMerkleKpWithCands pkSeed layer tree kind kp h (d + 1)
        (2 * nodeIdx + 1) (2 * localBase + 1) (localIdx - 2 ^ h) leaf rest).bind fun sub =>
        match sub.1 with
        | none => .done (none, sub.2)
        | some sVal =>
          let pre := thPreimage tagThH pkSeed
            ⟨layer, tree, kind, kp, UInt32.ofNat (h + 1), UInt32.ofNat nodeIdx⟩ [sib, sVal]
          (advRawHash pre).map fun top => (some top, (h, d, localBase, pre) :: sub.2)

theorem walkMerkleKpWithCands_fst (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kind : AdrsKind) (kp : UInt32) :
    ∀ (h d nodeIdx localBase localIdx : Nat) (leaf : List UInt8) (path : List (List UInt8)),
      (walkMerkleKpWithCands suite pkSeed layer tree kind kp h d nodeIdx localBase localIdx leaf path).1 =
        walkMerkleAuthPathKp suite pkSeed layer tree kind kp h nodeIdx localIdx leaf path
  | 0, _, _, _, _, _, [] => rfl
  | 0, _, _, _, _, _, _ :: _ => rfl
  | _ + 1, _, _, _, _, _, [] => rfl
  | h + 1, d, nodeIdx, localBase, localIdx, leaf, sib :: rest => by
    unfold walkMerkleKpWithCands walkMerkleAuthPathKp
    by_cases hHalf : localIdx < 2 ^ h
    · simp only [hHalf, ↓reduceIte,
        walkMerkleKpWithCands_fst suite pkSeed layer tree kind kp h (d + 1)
          (2 * nodeIdx) (2 * localBase) localIdx leaf rest]
      cases walkMerkleAuthPathKp suite pkSeed layer tree kind kp h (2 * nodeIdx) localIdx leaf rest <;>
        rfl
    · simp only [hHalf, ↓reduceIte,
        walkMerkleKpWithCands_fst suite pkSeed layer tree kind kp h (d + 1)
          (2 * nodeIdx + 1) (2 * localBase + 1) (localIdx - 2 ^ h) leaf rest]
      cases walkMerkleAuthPathKp suite pkSeed layer tree kind kp h (2 * nodeIdx + 1)
        (localIdx - 2 ^ h) leaf rest <;> rfl

theorem walkMerkleKpWithCands_cands_length_le (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kind : AdrsKind) (kp : UInt32) :
    ∀ (h d nodeIdx localBase localIdx : Nat) (leaf : List UInt8) (path : List (List UInt8)),
      (walkMerkleKpWithCands suite pkSeed layer tree kind kp h d nodeIdx localBase localIdx leaf path).2.length ≤ h
  | 0, _, _, _, _, _, [] => Nat.le_refl 0
  | 0, _, _, _, _, _, _ :: _ => Nat.le_refl 0
  | _ + 1, _, _, _, _, _, [] => Nat.zero_le _
  | h + 1, d, nodeIdx, localBase, localIdx, leaf, sib :: rest => by
    unfold walkMerkleKpWithCands
    by_cases hHalf : localIdx < 2 ^ h
    · simp only [hHalf, ↓reduceIte]
      have ih := walkMerkleKpWithCands_cands_length_le suite pkSeed layer tree kind kp h (d + 1)
        (2 * nodeIdx) (2 * localBase) localIdx leaf rest
      cases (walkMerkleKpWithCands suite pkSeed layer tree kind kp h (d + 1)
        (2 * nodeIdx) (2 * localBase) localIdx leaf rest).1 <;> simp <;> omega
    · simp only [hHalf, ↓reduceIte]
      have ih := walkMerkleKpWithCands_cands_length_le suite pkSeed layer tree kind kp h (d + 1)
        (2 * nodeIdx + 1) (2 * localBase + 1) (localIdx - 2 ^ h) leaf rest
      cases (walkMerkleKpWithCands suite pkSeed layer tree kind kp h (d + 1)
        (2 * nodeIdx + 1) (2 * localBase + 1) (localIdx - 2 ^ h) leaf rest).1 <;> simp <;> omega

theorem advWalkMerkleKpWithCands_within (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kind : AdrsKind) (kp : UInt32) :
    ∀ (h d nodeIdx localBase localIdx : Nat) (leaf : List UInt8) (path : List (List UInt8)),
      (advWalkMerkleKpWithCands pkSeed layer tree kind kp h d nodeIdx localBase localIdx leaf path).Within h 0
  | 0, _, _, _, _, _, [] => trivial
  | 0, _, _, _, _, _, _ :: _ => trivial
  | _ + 1, _, _, _, _, _, [] => trivial
  | h + 1, d, nodeIdx, localBase, localIdx, leaf, sib :: rest => by
    unfold advWalkMerkleKpWithCands
    by_cases hHalf : localIdx < 2 ^ h
    · simp only [hHalf, ↓reduceIte]
      have ih := advWalkMerkleKpWithCands_within pkSeed layer tree kind kp h (d + 1)
        (2 * nodeIdx) (2 * localBase) localIdx leaf rest
      refine HashSignAdv.Within.bind_le (qh₂ := 1) (qs₂ := 0) ih (fun sub => ?_)
        (Nat.le_refl _) (by omega)
      cases sub.1 with
      | none => exact HashSignAdv.Within.done _ 1 0
      | some _ => exact HashSignAdv.Within.map _ (advRawHash_within _)
    · simp only [hHalf, ↓reduceIte]
      have ih := advWalkMerkleKpWithCands_within pkSeed layer tree kind kp h (d + 1)
        (2 * nodeIdx + 1) (2 * localBase + 1) (localIdx - 2 ^ h) leaf rest
      refine HashSignAdv.Within.bind_le (qh₂ := 1) (qs₂ := 0) ih (fun sub => ?_)
        (Nat.le_refl _) (by omega)
      cases sub.1 with
      | none => exact HashSignAdv.Within.done _ 1 0
      | some _ => exact HashSignAdv.Within.map _ (advRawHash_within _)

theorem runHashSignAdv_advWalkMerkleKpWithCands (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkSeed : List UInt8) (layer : UInt32) (tree : UInt64)
    (kind : AdrsKind) (kp : UInt32) :
    ∀ (h d nodeIdx localBase localIdx : Nat) (leaf : List UInt8) (path : List (List UInt8))
      (qs : List ProdSigningQuery),
      runHashSignAdv suite params sk qs
          (advWalkMerkleKpWithCands pkSeed layer tree kind kp h d nodeIdx localBase localIdx leaf path) =
        (walkMerkleKpWithCands suite pkSeed layer tree kind kp h d nodeIdx localBase localIdx leaf path, qs)
  | 0, _, _, _, _, _, [], _ => rfl
  | 0, _, _, _, _, _, _ :: _, _ => rfl
  | _ + 1, _, _, _, _, _, [], _ => rfl
  | h + 1, d, nodeIdx, localBase, localIdx, leaf, sib :: rest, qs => by
    unfold advWalkMerkleKpWithCands walkMerkleKpWithCands
    by_cases hHalf : localIdx < 2 ^ h
    · simp only [hHalf, ↓reduceIte]
      rw [runHashSignAdv_bind, runHashSignAdv_advWalkMerkleKpWithCands]
      dsimp only
      cases (walkMerkleKpWithCands suite pkSeed layer tree kind kp h (d + 1)
          (2 * nodeIdx) (2 * localBase) localIdx leaf rest).1 <;> rfl
    · simp only [hHalf, ↓reduceIte]
      rw [runHashSignAdv_bind, runHashSignAdv_advWalkMerkleKpWithCands]
      dsimp only
      cases (walkMerkleKpWithCands suite pkSeed layer tree kind kp h (d + 1)
          (2 * nodeIdx + 1) (2 * localBase + 1) (localIdx - 2 ^ h) leaf rest).1 <;> rfl

/-- FORS root recovery recording `(ProdTargetIdx, forgedPreimage)` candidates. -/
def forsRootsWithCands (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (tree0 : UInt64) (kp0 : Nat)
    (idxs : List Nat) (ops : List ForsTreeOpening) :
    Nat → Nat → Option (List (List UInt8)) × List (ProdTargetIdx × List UInt8)
  | _, 0 => (some [], [])
  | j, rem + 1 =>
    let u := idxs.getD j 0
    let op := ops.getD j ⟨[], []⟩
    let leafH := forsIndexedLeafHash suite pkSeed tree0 kp0 j u op.secretVal
    let w := walkMerkleKpWithCands suite pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0)
      params.forsHeight 0 j 0 u leafH op.authPath
    let nodeCands := w.2.map fun q => (ProdTargetIdx.forsNode j q.1 q.2.1 q.2.2.1, q.2.2.2)
    match w.1 with
    | none => (none, nodeCands)
    | some rJ =>
      let rest := forsRootsWithCands suite params pkSeed tree0 kp0 idxs ops (j + 1) rem
      match rest.1 with
      | none => (none, nodeCands ++ rest.2)
      | some rs => (some (rJ :: rs), nodeCands ++ rest.2)

def advForsRootsWithCands (params : PqHashParams) (pkSeed : List UInt8)
    (tree0 : UInt64) (kp0 : Nat) (idxs : List Nat) (ops : List ForsTreeOpening) :
    Nat → Nat → HashSignAdv (Option (List (List UInt8)) × List (ProdTargetIdx × List UInt8))
  | _, 0 => .done (some [], [])
  | j, rem + 1 =>
    let u := idxs.getD j 0
    let op := ops.getD j ⟨[], []⟩
    let adrsLeaf : HashAdrs :=
      ⟨0, tree0, .forsTree, UInt32.ofNat kp0, UInt32.ofNat j, UInt32.ofNat u⟩
    (advThCall tagThF pkSeed adrsLeaf [op.secretVal]).bind fun leafH =>
      (advWalkMerkleKpWithCands pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0)
        params.forsHeight 0 j 0 u leafH op.authPath).bind fun w =>
        let nodeCands := w.2.map fun q => (ProdTargetIdx.forsNode j q.1 q.2.1 q.2.2.1, q.2.2.2)
        match w.1 with
        | none => .done (none, nodeCands)
        | some rJ =>
          (advForsRootsWithCands params pkSeed tree0 kp0 idxs ops (j + 1) rem).map fun rest =>
            match rest.1 with
            | none => (none, nodeCands ++ rest.2)
            | some rs => (some (rJ :: rs), nodeCands ++ rest.2)

theorem forsRootsWithCands_fst (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (tree0 : UInt64) (kp0 : Nat)
    (idxs : List Nat) (ops : List ForsTreeOpening) :
    ∀ (j rem : Nat),
      (forsRootsWithCands suite params pkSeed tree0 kp0 idxs ops j rem).1 =
        recoverProductionForsTreeRoots suite params pkSeed tree0 kp0 idxs ops j rem
  | _, 0 => rfl
  | j, rem + 1 => by
    unfold forsRootsWithCands
    dsimp only
    rw [recoverProductionForsTreeRoots_succ, walkMerkleKpWithCands_fst]
    dsimp only
    cases walkMerkleAuthPathKp suite pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0)
        params.forsHeight j (idxs.getD j 0)
        (forsIndexedLeafHash suite pkSeed tree0 kp0 j (idxs.getD j 0)
          (ops.getD j ⟨[], []⟩).secretVal)
        (ops.getD j ⟨[], []⟩).authPath with
    | none => rfl
    | some rJ =>
      dsimp only
      rw [forsRootsWithCands_fst suite params pkSeed tree0 kp0 idxs ops (j + 1) rem]
      cases recoverProductionForsTreeRoots suite params pkSeed tree0 kp0 idxs ops (j + 1) rem <;> rfl

theorem forsRootsWithCands_cands_length_le (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (tree0 : UInt64) (kp0 : Nat)
    (idxs : List Nat) (ops : List ForsTreeOpening) :
    ∀ (j rem : Nat),
      (forsRootsWithCands suite params pkSeed tree0 kp0 idxs ops j rem).2.length ≤
        rem * params.forsHeight
  | _, 0 => by simp [forsRootsWithCands]
  | j, rem + 1 => by
    unfold forsRootsWithCands
    dsimp only
    have hW := walkMerkleKpWithCands_cands_length_le suite pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0)
      params.forsHeight 0 j 0 (idxs.getD j 0)
      (forsIndexedLeafHash suite pkSeed tree0 kp0 j (idxs.getD j 0) (ops.getD j ⟨[], []⟩).secretVal)
      (ops.getD j ⟨[], []⟩).authPath
    have ih := forsRootsWithCands_cands_length_le suite params pkSeed tree0 kp0 idxs ops (j + 1) rem
    rw [Nat.succ_mul]
    cases (walkMerkleKpWithCands suite pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0)
        params.forsHeight 0 j 0 (idxs.getD j 0)
        (forsIndexedLeafHash suite pkSeed tree0 kp0 j (idxs.getD j 0) (ops.getD j ⟨[], []⟩).secretVal)
        (ops.getD j ⟨[], []⟩).authPath).1 with
    | none => simp only [List.length_map]; omega
    | some _ =>
      cases (forsRootsWithCands suite params pkSeed tree0 kp0 idxs ops (j + 1) rem).1 <;>
        (simp only [List.length_append, List.length_map]; omega)

theorem advForsRootsWithCands_within (params : PqHashParams) (pkSeed : List UInt8)
    (tree0 : UInt64) (kp0 : Nat) (idxs : List Nat) (ops : List ForsTreeOpening) :
    ∀ (j rem : Nat),
      (advForsRootsWithCands params pkSeed tree0 kp0 idxs ops j rem).Within
        (rem * (1 + params.forsHeight)) 0
  | _, 0 => trivial
  | j, rem + 1 => by
    unfold advForsRootsWithCands
    have hLeaf := advThCall_within tagThF pkSeed
      ⟨0, tree0, .forsTree, UInt32.ofNat kp0, UInt32.ofNat j, UInt32.ofNat (idxs.getD j 0)⟩
      [(ops.getD j ⟨[], []⟩).secretVal]
    refine HashSignAdv.Within.bind_le
      (qh₂ := params.forsHeight + rem * (1 + params.forsHeight)) (qs₂ := 0)
      hLeaf (fun leafH => ?_) (by rw [Nat.succ_mul]; omega) (by omega)
    have hW := advWalkMerkleKpWithCands_within pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0)
      params.forsHeight 0 j 0 (idxs.getD j 0) leafH (ops.getD j ⟨[], []⟩).authPath
    refine HashSignAdv.Within.bind_le (qh₂ := rem * (1 + params.forsHeight)) (qs₂ := 0)
      hW (fun w => ?_) (Nat.le_refl _) (by omega)
    cases w.1 with
    | none => exact HashSignAdv.Within.done _ _ 0
    | some _ =>
      exact HashSignAdv.Within.map _
        (advForsRootsWithCands_within params pkSeed tree0 kp0 idxs ops (j + 1) rem)

theorem runHashSignAdv_advForsRootsWithCands (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkSeed : List UInt8) (tree0 : UInt64) (kp0 : Nat)
    (idxs : List Nat) (ops : List ForsTreeOpening) :
    ∀ (j rem : Nat) (qs : List ProdSigningQuery),
      runHashSignAdv suite params sk qs
          (advForsRootsWithCands params pkSeed tree0 kp0 idxs ops j rem) =
        (forsRootsWithCands suite params pkSeed tree0 kp0 idxs ops j rem, qs)
  | _, 0, _ => rfl
  | j, rem + 1, qs => by
    unfold advForsRootsWithCands forsRootsWithCands
    rw [runHashSignAdv_bind]
    dsimp only [advThCall, advRawHash, runHashSignAdv]
    rw [ ← thCall_eq, ← thChainF_eq, ← forsIndexedLeafHash_eq,
      runHashSignAdv_bind, runHashSignAdv_advWalkMerkleKpWithCands]
    dsimp only
    cases (walkMerkleKpWithCands suite pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0)
        params.forsHeight 0 j 0 (idxs.getD j 0)
        (forsIndexedLeafHash suite pkSeed tree0 kp0 j (idxs.getD j 0) (ops.getD j ⟨[], []⟩).secretVal)
        (ops.getD j ⟨[], []⟩).authPath).1 with
    | none => rfl
    | some rJ =>
      dsimp only [HashSignAdv.map]
      rw [runHashSignAdv_bind, runHashSignAdv_advForsRootsWithCands]
      rfl

/-- Public specification of counter-mode HXOF blocks matching `thXofMsg`. -/
def publicXofMsgBlocks (suite : TweakableHashSuite) (rRand pkSeed pkRoot mu : List UInt8)
    (first : Nat) : Nat → List UInt8
  | 0 => []
  | n + 1 =>
    thCall suite tagHXof pkSeed
      ⟨0, 0, .forsRoots, 0, 0, UInt32.ofNat first⟩ [rRand, pkRoot, mu, be 4 first] ++
      publicXofMsgBlocks suite rRand pkSeed pkRoot mu (first + 1) n

theorem thXofMsg_eq_publicXofMsgBlocks (suite : TweakableHashSuite)
    (rRand pkSeed pkRoot mu : List UInt8) (outLen : Nat) :
    thXofMsg suite rRand pkSeed pkRoot mu outLen =
      (publicXofMsgBlocks suite rRand pkSeed pkRoot mu 0 ((outLen + 31) / 32)).take outLen := by
  unfold thXofMsg
  congr 1
  generalize (outLen + 31) / 32 = k
  generalize (0 : Nat) = f
  induction k generalizing f with
  | zero => rfl
  | succ _ ih =>
    dsimp only [publicXofMsgBlocks]
    rw [← ih (f + 1)]
    rfl

/-- Public oracle XOF block evaluator (`0` secret-seed access). -/
def advThXofMsgBlocks (rRand pkSeed pkRoot mu : List UInt8) :
    Nat → Nat → HashSignAdv (List UInt8)
  | _, 0 => .done []
  | first, n + 1 =>
    (advThCall tagHXof pkSeed ⟨0, 0, .forsRoots, 0, 0, UInt32.ofNat first⟩
      [rRand, pkRoot, mu, be 4 first]).bind fun b0 =>
      (advThXofMsgBlocks rRand pkSeed pkRoot mu (first + 1) n).map fun rest =>
        b0 ++ rest

theorem advThXofMsgBlocks_within (rRand pkSeed pkRoot mu : List UInt8) :
    ∀ (first n : Nat), (advThXofMsgBlocks rRand pkSeed pkRoot mu first n).Within n 0
  | _, 0 => trivial
  | first, n + 1 => by
    unfold advThXofMsgBlocks
    refine HashSignAdv.Within.bind_le (qh₂ := n) (qs₂ := 0) (advThCall_within _ _ _ _)
      (fun _ => HashSignAdv.Within.map _
        (advThXofMsgBlocks_within rRand pkSeed pkRoot mu (first + 1) n))
      (by omega) (by omega)

theorem runHashSignAdv_advThXofMsgBlocks (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (rRand pkSeed pkRoot mu : List UInt8) :
    ∀ (first n : Nat) (qs : List ProdSigningQuery),
      runHashSignAdv suite params sk qs (advThXofMsgBlocks rRand pkSeed pkRoot mu first n) =
        (publicXofMsgBlocks suite rRand pkSeed pkRoot mu first n, qs)
  | _, 0, _ => rfl
  | first, n + 1, qs => by
    unfold advThXofMsgBlocks publicXofMsgBlocks HashSignAdv.map
    rw [runHashSignAdv_bind]
    dsimp only [advThCall, advRawHash, runHashSignAdv]
    rw [← thCall_eq, runHashSignAdv_bind, runHashSignAdv_advThXofMsgBlocks]
    rfl

def advDeriveProductionStatelessInputs (params : PqHashParams)
    (rRand pkSeed pkRoot mu : List UInt8) : HashSignAdv (Option (Nat × List Nat)) :=
  if !params.productionWellFormed || params.statefulJorts then .done none
  else
    let forsBytes := (params.forsTrees * params.forsHeight + 7) / 8
    let treeBits := params.numLayers * params.subtreeHeight
    let treeBytes := (treeBits + 7) / 8
    let outLen := forsBytes + treeBytes
    (advThXofMsgBlocks rRand pkSeed pkRoot mu 0 ((outLen + 31) / 32)).map fun blocks =>
      let digest := blocks.take outLen
      let forsSlice := digest.take forsBytes
      let treeSlice := digest.drop forsBytes
      some (extractBitWindow treeSlice 0 treeBits,
        (List.range params.forsTrees).map fun j =>
          extractBitWindow forsSlice (j * params.forsHeight) params.forsHeight)

theorem advDeriveProductionStatelessInputs_within (params : PqHashParams)
    (rRand pkSeed pkRoot mu : List UInt8) :
    (advDeriveProductionStatelessInputs params rRand pkSeed pkRoot mu).Within
      (prodXofHashBudget params) 0 := by
  unfold advDeriveProductionStatelessInputs prodXofHashBudget
  cases hSt : params.statefulJorts
  · cases params.productionWellFormed
    · exact HashSignAdv.Within.done _ _ 0
    · simp only [Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
      exact HashSignAdv.Within.map _ (advThXofMsgBlocks_within _ _ _ _ _ _)
  · simp only [Bool.or_true, ↓reduceIte]
    exact HashSignAdv.Within.done _ _ 0

theorem runHashSignAdv_advDeriveProductionStatelessInputs (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) (rRand pkSeed pkRoot mu : List UInt8)
    (qs : List ProdSigningQuery) :
    runHashSignAdv suite params sk qs
        (advDeriveProductionStatelessInputs params rRand pkSeed pkRoot mu) =
      (deriveProductionStatelessInputs suite params rRand pkSeed pkRoot mu, qs) := by
  unfold advDeriveProductionStatelessInputs deriveProductionStatelessInputs
  split
  · rfl
  · unfold HashSignAdv.map
    rw [runHashSignAdv_bind, runHashSignAdv_advThXofMsgBlocks]
    dsimp only [runHashSignAdv]
    rw [← thXofMsg_eq_publicXofMsgBlocks]

/-- Single-pass hypertree layer verifier recording `(ProdTargetIdx, forgedPreimage)` candidates. -/
def hypertreeLayersWithCands (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed pkRoot rRand : List UInt8) (log : List (List UInt8 × PqHashSig)) :
    Nat → Nat → List UInt8 → List LayerXmssSig →
    Option (List UInt8) × List (ProdTargetIdx × List UInt8)
  | _, _, curRoot, [] => (some curRoot, [])
  | layerIdx, globalIdx, curRoot, lsig :: rest =>
    if !(decide (lsig.tswCtr < 2 ^ 32)) then (none, [])
    else
      let subLeaves := 2 ^ params.subtreeHeight
      let kpIdx := globalIdx % subLeaves
      let kpU32 := UInt32.ofNat kpIdx
      let treeIdxNat := globalIdx / subLeaves
      let treeIdx := UInt64.ofNat treeIdxNat
      let layerU32 := UInt32.ofNat layerIdx
      let layerPre := prodLayerPreimage params rRand pkSeed pkRoot curRoot layerIdx treeIdx kpU32
        lsig.tswCtr
      let hmsg := suite.rawHash layerPre
      let digCands := log.map fun e => (ProdTargetIdx.signedDigest e layerIdx, layerPre)
      match extractBaseWDigitsChecked params.w params.ell1 hmsg with
      | none => (none, digCands)
      | some digits =>
        if !(checkTargetSum params.w params.ell1 params.targetSum digits) then (none, digCands)
        else if lsig.wotsChains.length ≠ params.ell1 then (none, digCands)
        else
          let ch := allWotsChainsWithCands suite params pkSeed layerU32 treeIdx kpIdx digits
            lsig.wotsChains params.ell1
          let chainCands := ch.2.map fun rsp =>
            (ProdTargetIdx.chainStep layerIdx rsp.1 rsp.2.1, rsp.2.2)
          let wotsPre := thPreimage tagThTl pkSeed
            ⟨layerU32, treeIdx, .wotsPk, kpU32, 0, 0⟩ ch.1
          let wotsPk := suite.rawHash wotsPre
          let wotsCand := (ProdTargetIdx.wotsPk layerIdx, wotsPre)
          let mw := walkMerkleKpWithCands suite pkSeed layerU32 treeIdx .tree 0
            params.subtreeHeight 0 0 0 kpIdx wotsPk lsig.authPath
          let xmssCands := mw.2.map fun q => (ProdTargetIdx.xmssNode layerIdx q.1 q.2.2.1, q.2.2.2)
          let here := digCands ++ (wotsCand :: (chainCands ++ xmssCands))
          match mw.1 with
          | none => (none, here)
          | some nextRoot =>
            let up := hypertreeLayersWithCands suite params pkSeed pkRoot rRand log
              (layerIdx + 1) treeIdxNat nextRoot rest
            (up.1, here ++ up.2)

def advHypertreeLayersWithCands (params : PqHashParams)
    (pkSeed pkRoot rRand : List UInt8) (log : List (List UInt8 × PqHashSig)) :
    Nat → Nat → List UInt8 → List LayerXmssSig →
    HashSignAdv (Option (List UInt8) × List (ProdTargetIdx × List UInt8))
  | _, _, curRoot, [] => .done (some curRoot, [])
  | layerIdx, globalIdx, curRoot, lsig :: rest =>
    if !(decide (lsig.tswCtr < 2 ^ 32)) then .done (none, [])
    else
      let subLeaves := 2 ^ params.subtreeHeight
      let kpIdx := globalIdx % subLeaves
      let kpU32 := UInt32.ofNat kpIdx
      let treeIdxNat := globalIdx / subLeaves
      let treeIdx := UInt64.ofNat treeIdxNat
      let layerU32 := UInt32.ofNat layerIdx
      let layerPre := prodLayerPreimage params rRand pkSeed pkRoot curRoot layerIdx treeIdx kpU32
        lsig.tswCtr
      let digCands := log.map fun e => (ProdTargetIdx.signedDigest e layerIdx, layerPre)
      (advRawHash layerPre).bind fun hmsg =>
        match extractBaseWDigitsChecked params.w params.ell1 hmsg with
        | none => .done (none, digCands)
        | some digits =>
          if !(checkTargetSum params.w params.ell1 params.targetSum digits) then
            .done (none, digCands)
          else if lsig.wotsChains.length ≠ params.ell1 then
            .done (none, digCands)
          else
            (advAllWotsChainsWithCands params pkSeed layerU32 treeIdx kpIdx digits
              lsig.wotsChains params.ell1).bind fun ch =>
              let chainCands := ch.2.map fun rsp =>
                (ProdTargetIdx.chainStep layerIdx rsp.1 rsp.2.1, rsp.2.2)
              let wotsPre := thPreimage tagThTl pkSeed
                ⟨layerU32, treeIdx, .wotsPk, kpU32, 0, 0⟩ ch.1
              let wotsCand := (ProdTargetIdx.wotsPk layerIdx, wotsPre)
              (advRawHash wotsPre).bind fun wotsPk =>
                (advWalkMerkleKpWithCands pkSeed layerU32 treeIdx .tree 0
                  params.subtreeHeight 0 0 0 kpIdx wotsPk lsig.authPath).bind fun mw =>
                  let xmssCands := mw.2.map fun q =>
                    (ProdTargetIdx.xmssNode layerIdx q.1 q.2.2.1, q.2.2.2)
                  let here := digCands ++ (wotsCand :: (chainCands ++ xmssCands))
                  match mw.1 with
                  | none => .done (none, here)
                  | some nextRoot =>
                    (advHypertreeLayersWithCands params pkSeed pkRoot rRand log
                      (layerIdx + 1) treeIdxNat nextRoot rest).map fun up =>
                      (up.1, here ++ up.2)

theorem hypertreeLayersWithCands_fst (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed pkRoot rRand : List UInt8) (log : List (List UInt8 × PqHashSig)) :
    ∀ (layerIdx globalIdx : Nat) (curRoot : List UInt8) (sigs : List LayerXmssSig),
      (hypertreeLayersWithCands suite params pkSeed pkRoot rRand log layerIdx globalIdx curRoot sigs).1 =
        verifyProductionHypertreeLayers suite params pkSeed pkRoot rRand layerIdx globalIdx curRoot sigs
  | _, _, _, [] => rfl
  | layerIdx, globalIdx, curRoot, lsig :: rest => by
    unfold hypertreeLayersWithCands
    rw [verifyProductionHypertreeLayers_cons]
    by_cases hCtr : decide (lsig.tswCtr < 2 ^ 32) = true
    · simp only [hCtr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [← productionLayerDigest_rawHash]
      cases extractBaseWDigitsChecked params.w params.ell1
          (productionLayerDigest suite params rRand pkSeed pkRoot curRoot layerIdx
            (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight)) lsig.tswCtr) with
      | none => rfl
      | some digits =>
        dsimp only
        split
        · rfl
        · split
          · rfl
          · have hWotsEq :
                suite.rawHash (thPreimage tagThTl pkSeed
                  ⟨UInt32.ofNat layerIdx, UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight),
                   .wotsPk, UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight), 0, 0⟩
                  (allWotsChainsWithCands suite params pkSeed (UInt32.ofNat layerIdx)
                    (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
                    (globalIdx % 2 ^ params.subtreeHeight) digits lsig.wotsChains params.ell1).1) =
                recoverWotsPkFromSig suite params pkSeed (UInt32.ofNat layerIdx)
                  (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
                  (globalIdx % 2 ^ params.subtreeHeight) digits lsig.wotsChains := by
              rw [allWotsChainsWithCands_fst, recoverWotsPkFromSig_eq, recoverWotsEndpoints_eq,
                thTweakTl_eq, thCall_eq]
            rw [hWotsEq, walkMerkleKpWithCands_fst]
            cases walkMerkleAuthPathKp suite pkSeed (UInt32.ofNat layerIdx)
                (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) .tree 0 params.subtreeHeight 0
                (globalIdx % 2 ^ params.subtreeHeight)
                (recoverWotsPkFromSig suite params pkSeed (UInt32.ofNat layerIdx)
                  (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
                  (globalIdx % 2 ^ params.subtreeHeight) digits lsig.wotsChains) lsig.authPath with
            | none => rfl
            | some nextRoot =>
              exact hypertreeLayersWithCands_fst suite params pkSeed pkRoot rRand log
                (layerIdx + 1) (globalIdx / 2 ^ params.subtreeHeight) nextRoot rest
    · simp [hCtr]

theorem hypertreeLayersWithCands_cands_length_le (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed pkRoot rRand : List UInt8) (log : List (List UInt8 × PqHashSig)) :
    ∀ (layerIdx globalIdx : Nat) (curRoot : List UInt8) (sigs : List LayerXmssSig),
      (hypertreeLayersWithCands suite params pkSeed pkRoot rRand log layerIdx globalIdx curRoot sigs).2.length ≤
        sigs.length * (log.length + 1 + params.ell1 * (params.w - 1) + params.subtreeHeight)
  | _, _, _, [] => by simp [hypertreeLayersWithCands]
  | layerIdx, globalIdx, curRoot, lsig :: rest => by
    unfold hypertreeLayersWithCands
    rw [List.length_cons, Nat.succ_mul]
    by_cases hCtr : decide (lsig.tswCtr < 2 ^ 32) = true
    · simp only [hCtr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases extractBaseWDigitsChecked params.w params.ell1 _ with
      | none => simp only [List.length_map]; omega
      | some digits =>
        dsimp only
        split
        · simp only [List.length_map]; omega
        · split
          · simp only [List.length_map]; omega
          · have hCh := allWotsChainsWithCands_cands_length_le suite params pkSeed
              (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
              (globalIdx % 2 ^ params.subtreeHeight) digits lsig.wotsChains params.ell1
            have hMw := walkMerkleKpWithCands_cands_length_le suite pkSeed (UInt32.ofNat layerIdx)
              (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) .tree 0 params.subtreeHeight 0 0 0
              (globalIdx % 2 ^ params.subtreeHeight)
              (suite.rawHash (thPreimage tagThTl pkSeed
                ⟨UInt32.ofNat layerIdx, UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight),
                 .wotsPk, UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight), 0, 0⟩
                (allWotsChainsWithCands suite params pkSeed (UInt32.ofNat layerIdx)
                  (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
                  (globalIdx % 2 ^ params.subtreeHeight) digits lsig.wotsChains params.ell1).1))
              lsig.authPath
            cases hW : (walkMerkleKpWithCands suite pkSeed (UInt32.ofNat layerIdx)
                (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) .tree 0 params.subtreeHeight 0 0 0
                (globalIdx % 2 ^ params.subtreeHeight)
                (suite.rawHash (thPreimage tagThTl pkSeed
                  ⟨UInt32.ofNat layerIdx, UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight),
                   .wotsPk, UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight), 0, 0⟩
                  (allWotsChainsWithCands suite params pkSeed (UInt32.ofNat layerIdx)
                    (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
                    (globalIdx % 2 ^ params.subtreeHeight) digits lsig.wotsChains params.ell1).1))
                lsig.authPath).1 with
            | none =>
              simp only [List.length_append, List.length_cons, List.length_map]
              omega
            | some nextRoot =>
              have ih' := hypertreeLayersWithCands_cands_length_le suite params pkSeed pkRoot
                rRand log (layerIdx + 1) (globalIdx / 2 ^ params.subtreeHeight) nextRoot rest
              simp only [List.length_append, List.length_cons, List.length_map]
              omega
    · simp [hCtr]

theorem advHypertreeLayersWithCands_within (params : PqHashParams)
    (pkSeed pkRoot rRand : List UInt8) (log : List (List UInt8 × PqHashSig)) :
    ∀ (layerIdx globalIdx : Nat) (curRoot : List UInt8) (sigs : List LayerXmssSig),
      (advHypertreeLayersWithCands params pkSeed pkRoot rRand log layerIdx globalIdx curRoot sigs).Within
        (sigs.length * prodLayerHashBudget params) 0
  | _, _, _, [] => trivial
  | layerIdx, globalIdx, curRoot, lsig :: rest => by
    unfold advHypertreeLayersWithCands prodLayerHashBudget
    rw [List.length_cons, Nat.succ_mul]
    by_cases hCtr : decide (lsig.tswCtr < 2 ^ 32) = true
    · simp only [hCtr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      let remB := params.ell1 * (params.w - 1) + 1 + params.subtreeHeight +
        rest.length * prodLayerHashBudget params
      refine HashSignAdv.Within.bind_le (qh₂ := remB) (qs₂ := 0) (advRawHash_within _)
        (fun hmsg => ?_) (by unfold remB prodLayerHashBudget; omega) (by omega)
      cases extractBaseWDigitsChecked params.w params.ell1 hmsg with
      | none => exact HashSignAdv.Within.done _ _ 0
      | some digits =>
        dsimp only
        split
        · exact HashSignAdv.Within.done _ _ 0
        · split
          · exact HashSignAdv.Within.done _ _ 0
          · refine HashSignAdv.Within.bind_le
              (qh₂ := 1 + params.subtreeHeight + rest.length * prodLayerHashBudget params)
              (qs₂ := 0)
              (advAllWotsChainsWithCands_within _ _ _ _ _ _ _ _)
              (fun _ => ?_) (by unfold remB; omega) (by omega)
            refine HashSignAdv.Within.bind_le
              (qh₂ := params.subtreeHeight + rest.length * prodLayerHashBudget params)
              (qs₂ := 0)
              (advRawHash_within _) (fun _ => ?_) (by omega) (by omega)
            refine HashSignAdv.Within.bind_le
              (qh₂ := rest.length * prodLayerHashBudget params) (qs₂ := 0)
              (advWalkMerkleKpWithCands_within _ _ _ _ _ _ _ _ _ _ _ _)
              (fun mw => ?_) (by omega) (by omega)
            cases mw.1 with
            | none => exact HashSignAdv.Within.done _ _ 0
            | some nextRoot =>
              exact HashSignAdv.Within.map _
                (advHypertreeLayersWithCands_within params pkSeed pkRoot rRand log
                  (layerIdx + 1) (globalIdx / 2 ^ params.subtreeHeight) nextRoot rest)
    · simp only [hCtr, Bool.not_false, ↓reduceIte]
      exact HashSignAdv.Within.done _ _ 0

theorem runHashSignAdv_advHypertreeLayersWithCands (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey)
    (pkSeed pkRoot rRand : List UInt8) (log : List (List UInt8 × PqHashSig)) :
    ∀ (layerIdx globalIdx : Nat) (curRoot : List UInt8) (sigs : List LayerXmssSig)
      (qs : List ProdSigningQuery),
      runHashSignAdv suite params sk qs
          (advHypertreeLayersWithCands params pkSeed pkRoot rRand log layerIdx globalIdx curRoot sigs) =
        (hypertreeLayersWithCands suite params pkSeed pkRoot rRand log layerIdx globalIdx curRoot sigs, qs)
  | _, _, _, [], _ => rfl
  | layerIdx, globalIdx, curRoot, lsig :: rest, qs => by
    unfold advHypertreeLayersWithCands hypertreeLayersWithCands
    by_cases hCtr : decide (lsig.tswCtr < 2 ^ 32) = true
    · simp only [hCtr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [runHashSignAdv_bind]
      dsimp only [advRawHash, runHashSignAdv]
      cases extractBaseWDigitsChecked params.w params.ell1 _ with
      | none => rfl
      | some digits =>
        dsimp only
        split
        · rfl
        · split
          · rfl
          · rw [runHashSignAdv_bind, runHashSignAdv_advAllWotsChainsWithCands]
            dsimp only
            rw [runHashSignAdv_bind]
            dsimp only [advRawHash, runHashSignAdv]
            rw [runHashSignAdv_bind, runHashSignAdv_advWalkMerkleKpWithCands]
            dsimp only
            cases (walkMerkleKpWithCands suite pkSeed (UInt32.ofNat layerIdx)
                (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) .tree 0 params.subtreeHeight 0 0 0
                (globalIdx % 2 ^ params.subtreeHeight) _ lsig.authPath).1 with
            | none => rfl
            | some nextRoot =>
              dsimp only [HashSignAdv.map]
              rw [runHashSignAdv_bind, runHashSignAdv_advHypertreeLayersWithCands]
              rfl
    · simp [hCtr, runHashSignAdv]

/-- Full public verifier + TCR candidate collector (pure specification, `pk`-only, `0` `sk` access). -/
def publicVerifierWithTcrCands (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (log : List (List UInt8 × PqHashSig))
    (msg : List UInt8) (sig : PqHashSig) :
    Bool × List (ProdTargetIdx × List UInt8) :=
  if !params.productionWellFormed || !params.productionLeafIdxInRange sig.leafGlobalIdx then
    (false, [])
  else if sig.layerSigs.length ≠ params.numLayers || sig.msgTswCtr ≠ 0 then
    (false, [])
  else
    let preHashInput := thPreimage tagHPre pk.pkSeed zeroAdrs [pk.pkRoot, msg]
    let mu := suite.rawHash preHashInput
    let preHashCands := log.map fun e => (ProdTargetIdx.preHash e, preHashInput)
    if params.statefulJorts then
      if !sig.forsOpenings.isEmpty then (false, preHashCands)
      else
        let ht := hypertreeLayersWithCands suite params pk.pkSeed pk.pkRoot sig.rRand log
          0 sig.leafGlobalIdx mu sig.layerSigs
        let ok := match ht.1 with
          | some computedTopRoot => decide (computedTopRoot = pk.pkRoot)
          | none => false
        (ok, preHashCands ++ ht.2)
    else
      if sig.forsOpenings.length ≠ params.forsTrees then (false, preHashCands)
      else
        match deriveProductionStatelessInputs suite params sig.rRand pk.pkSeed pk.pkRoot mu with
        | none => (false, preHashCands)
        | some (derivedLeafIdx, idxs) =>
          if sig.leafGlobalIdx ≠ derivedLeafIdx then (false, preHashCands)
          else
            let subLeaves := 2 ^ params.subtreeHeight
            let kp0 := sig.leafGlobalIdx % subLeaves
            let tree0 := UInt64.ofNat (sig.leafGlobalIdx / subLeaves)
            let fr := forsRootsWithCands suite params pk.pkSeed tree0 kp0 idxs sig.forsOpenings
              0 params.forsTrees
            match fr.1 with
            | none => (false, preHashCands ++ fr.2)
            | some roots =>
              let forsPre := thPreimage tagThTl pk.pkSeed
                ⟨0, tree0, .forsRoots, UInt32.ofNat kp0, 0, 0⟩ roots
              let forsPk := suite.rawHash forsPre
              let forsCand := (ProdTargetIdx.forsRoots, forsPre)
              let ht := hypertreeLayersWithCands suite params pk.pkSeed pk.pkRoot sig.rRand log
                0 sig.leafGlobalIdx forsPk sig.layerSigs
              let ok := match ht.1 with
                | some computedTopRoot => decide (computedTopRoot = pk.pkRoot)
                | none => false
              (ok, preHashCands ++ (forsCand :: (fr.2 ++ ht.2)))

/-- Seed-withheld `HashSignAdv` execution of `publicVerifierWithTcrCands`. -/
def advVerifyWithTcrCands (params : PqHashParams) (pk : PqPublicKey)
    (log : List (List UInt8 × PqHashSig)) (msg : List UInt8) (sig : PqHashSig) :
    HashSignAdv (Bool × List (ProdTargetIdx × List UInt8)) :=
  if !params.productionWellFormed || !params.productionLeafIdxInRange sig.leafGlobalIdx then
    .done (false, [])
  else if sig.layerSigs.length ≠ params.numLayers || sig.msgTswCtr ≠ 0 then
    .done (false, [])
  else
    let preHashInput := thPreimage tagHPre pk.pkSeed zeroAdrs [pk.pkRoot, msg]
    let preHashCands := log.map fun e => (ProdTargetIdx.preHash e, preHashInput)
    (advRawHash preHashInput).bind fun mu =>
      if params.statefulJorts then
        if !sig.forsOpenings.isEmpty then .done (false, preHashCands)
        else
          (advHypertreeLayersWithCands params pk.pkSeed pk.pkRoot sig.rRand log
            0 sig.leafGlobalIdx mu sig.layerSigs).map fun ht =>
            let ok := match ht.1 with
              | some computedTopRoot => decide (computedTopRoot = pk.pkRoot)
              | none => false
            (ok, preHashCands ++ ht.2)
      else
        if sig.forsOpenings.length ≠ params.forsTrees then .done (false, preHashCands)
        else
          (advDeriveProductionStatelessInputs params sig.rRand pk.pkSeed pk.pkRoot mu).bind fun dOpt =>
            match dOpt with
            | none => .done (false, preHashCands)
            | some (derivedLeafIdx, idxs) =>
              if sig.leafGlobalIdx ≠ derivedLeafIdx then .done (false, preHashCands)
              else
                let subLeaves := 2 ^ params.subtreeHeight
                let kp0 := sig.leafGlobalIdx % subLeaves
                let tree0 := UInt64.ofNat (sig.leafGlobalIdx / subLeaves)
                (advForsRootsWithCands params pk.pkSeed tree0 kp0 idxs sig.forsOpenings
                  0 params.forsTrees).bind fun fr =>
                  match fr.1 with
                  | none => .done (false, preHashCands ++ fr.2)
                  | some roots =>
                    let forsPre := thPreimage tagThTl pk.pkSeed
                      ⟨0, tree0, .forsRoots, UInt32.ofNat kp0, 0, 0⟩ roots
                    let forsCand := (ProdTargetIdx.forsRoots, forsPre)
                    (advRawHash forsPre).bind fun forsPk =>
                      (advHypertreeLayersWithCands params pk.pkSeed pk.pkRoot sig.rRand log
                        0 sig.leafGlobalIdx forsPk sig.layerSigs).map fun ht =>
                        let ok := match ht.1 with
                          | some computedTopRoot => decide (computedTopRoot = pk.pkRoot)
                          | none => false
                        (ok, preHashCands ++ (forsCand :: (fr.2 ++ ht.2)))

def advVerifyProductionPqHashSig (params : PqHashParams) (pk : PqPublicKey)
    (msg : List UInt8) (sig : PqHashSig) : HashSignAdv Bool :=
  (advVerifyWithTcrCands params pk [] msg sig).map Prod.fst

theorem publicVerifierWithTcrCands_fst (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (log : List (List UInt8 × PqHashSig))
    (msg : List UInt8) (sig : PqHashSig) :
    (publicVerifierWithTcrCands suite params pk log msg sig).1 =
      verifyProductionPqHashSig suite params pk msg sig := by
  unfold publicVerifierWithTcrCands
  rw [verifyProductionPqHashSig_eq]
  split
  · rfl
  · split
    · rfl
    · dsimp only
      have hMu : suite.rawHash (thPreimage tagHPre pk.pkSeed zeroAdrs [pk.pkRoot, msg]) =
          thPreHash suite pk.pkSeed pk.pkRoot msg := rfl
      rw [hMu]
      cases hSt : params.statefulJorts
      · simp only [Bool.false_eq_true, ↓reduceIte]
        split
        · rfl
        · cases hD : deriveProductionStatelessInputs suite params sig.rRand pk.pkSeed pk.pkRoot
              (thPreHash suite pk.pkSeed pk.pkRoot msg) with
          | none => rfl
          | some pr =>
            rcases pr with ⟨derivedLeafIdx, idxs⟩
            have hIdxsLen : idxs.length = params.forsTrees :=
              (deriveProductionStatelessInputs_bounds suite params sig.rRand pk.pkSeed pk.pkRoot
                (thPreHash suite pk.pkSeed pk.pkRoot msg) derivedLeafIdx idxs hD).2.2.2.1
            dsimp only
            split
            · rfl
            · rw [recoverProductionForsPk_eq]
              have hLenEq : sig.forsOpenings.length = params.forsTrees := by
                rename_i hNotNe _
                exact Decidable.of_not_not hNotNe
              simp only [hLenEq, hIdxsLen, ne_eq, not_true_eq_false, decide_false, Bool.or_self,
                Bool.false_eq_true, ↓reduceIte]
              rw [forsRootsWithCands_fst]
              cases recoverProductionForsTreeRoots suite params pk.pkSeed
                  (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
                  (sig.leafGlobalIdx % 2 ^ params.subtreeHeight) idxs sig.forsOpenings
                  0 params.forsTrees with
              | none => rfl
              | some roots =>
                dsimp only
                have hFpk : suite.rawHash (thPreimage tagThTl pk.pkSeed
                    ⟨0, UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight),
                     .forsRoots, UInt32.ofNat (sig.leafGlobalIdx % 2 ^ params.subtreeHeight), 0, 0⟩
                    roots) =
                  thTweakTl suite pk.pkSeed
                    ⟨0, UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight),
                     .forsRoots, UInt32.ofNat (sig.leafGlobalIdx % 2 ^ params.subtreeHeight), 0, 0⟩
                    roots := rfl
                rw [hFpk, hypertreeLayersWithCands_fst]
                rfl
      · simp only [↓reduceIte]
        split
        · rfl
        · dsimp only
          rw [hypertreeLayersWithCands_fst]
          rfl

theorem publicVerifierWithTcrCands_cands_length_le (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (log : List (List UInt8 × PqHashSig))
    (msg : List UInt8) (sig : PqHashSig) :
    (publicVerifierWithTcrCands suite params pk log msg sig).2.length ≤
      prodPathTargetCount params log.length := by
  unfold publicVerifierWithTcrCands prodPathTargetCount
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · rename_i hG2
      have hLsLen : sig.layerSigs.length = params.numLayers := by
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hG2
        exact Decidable.of_not_not hG2.1
      have hMulDist :
          params.numLayers * (log.length + 1 + params.ell1 * (params.w - 1) + params.subtreeHeight) =
          log.length * params.numLayers + params.numLayers +
            params.numLayers * (params.ell1 * (params.w - 1)) +
            params.numLayers * params.subtreeHeight := by
        have d1 := Nat.mul_add params.numLayers (log.length + 1 + params.ell1 * (params.w - 1))
          params.subtreeHeight
        have d2 := Nat.mul_add params.numLayers (log.length + 1) (params.ell1 * (params.w - 1))
        have d3 := Nat.mul_add params.numLayers log.length 1
        have d4 := Nat.mul_comm params.numLayers log.length
        omega
      cases hSt : params.statefulJorts
      · simp only [Bool.false_eq_true, ↓reduceIte]
        split
        · simp only [List.length_map]; omega
        · cases deriveProductionStatelessInputs suite params sig.rRand pk.pkSeed pk.pkRoot _ with
          | none => simp only [List.length_map]; omega
          | some pr =>
            rcases pr with ⟨derivedLeafIdx, idxs⟩
            dsimp only
            split
            · simp only [List.length_map]; omega
            · have hFr := forsRootsWithCands_cands_length_le suite params pk.pkSeed
                (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
                (sig.leafGlobalIdx % 2 ^ params.subtreeHeight) idxs sig.forsOpenings
                0 params.forsTrees
              cases (forsRootsWithCands suite params pk.pkSeed
                  (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
                  (sig.leafGlobalIdx % 2 ^ params.subtreeHeight) idxs sig.forsOpenings
                  0 params.forsTrees).1 with
              | none =>
                simp only [List.length_append, List.length_map]
                omega
              | some roots =>
                have hHt := hypertreeLayersWithCands_cands_length_le suite params pk.pkSeed
                  pk.pkRoot sig.rRand log 0 sig.leafGlobalIdx
                  (suite.rawHash (thPreimage tagThTl pk.pkSeed
                    ⟨0, UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight),
                     .forsRoots, UInt32.ofNat (sig.leafGlobalIdx % 2 ^ params.subtreeHeight), 0, 0⟩
                    roots)) sig.layerSigs
                rw [hLsLen, hMulDist] at hHt
                simp only [List.length_append, List.length_cons, List.length_map]
                omega
      · simp only [↓reduceIte]
        split
        · simp only [List.length_map]; omega
        · have hHt := hypertreeLayersWithCands_cands_length_le suite params pk.pkSeed
            pk.pkRoot sig.rRand log 0 sig.leafGlobalIdx
            (suite.rawHash (thPreimage tagHPre pk.pkSeed zeroAdrs [pk.pkRoot, msg])) sig.layerSigs
          rw [hLsLen, hMulDist] at hHt
          simp only [List.length_append, List.length_map]
          omega

theorem advVerifyWithTcrCands_within (params : PqHashParams) (pk : PqPublicKey)
    (log : List (List UInt8 × PqHashSig)) (msg : List UInt8) (sig : PqHashSig) :
    (advVerifyWithTcrCands params pk log msg sig).Within (prodVerifierHashBudget params) 0 := by
  unfold advVerifyWithTcrCands prodVerifierHashBudget
  split
  · exact HashSignAdv.Within.done _ _ 0
  · split
    · exact HashSignAdv.Within.done _ _ 0
    · rename_i hG2
      have hLsLen : sig.layerSigs.length = params.numLayers := by
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hG2
        exact Decidable.of_not_not hG2.1
      refine HashSignAdv.Within.bind_le
        (qh₂ := prodXofHashBudget params + prodForsHashBudget params +
          params.numLayers * prodLayerHashBudget params) (qs₂ := 0)
        (advRawHash_within _) (fun mu => ?_) (by omega) (by omega)
      cases hSt : params.statefulJorts
      · simp only [Bool.false_eq_true, ↓reduceIte, prodXofHashBudget, prodForsHashBudget, hSt]
        split
        · exact HashSignAdv.Within.done _ _ 0
        · have hXof : (advDeriveProductionStatelessInputs params sig.rRand pk.pkSeed pk.pkRoot mu).Within
              (((params.forsTrees * params.forsHeight + 7) / 8 +
                (params.numLayers * params.subtreeHeight + 7) / 8 + 31) / 32) 0 := by
            have h := advDeriveProductionStatelessInputs_within params sig.rRand pk.pkSeed pk.pkRoot mu
            simpa only [prodXofHashBudget, hSt, Bool.false_eq_true, ↓reduceIte] using h
          refine HashSignAdv.Within.bind_le
            (qh₂ := (params.forsTrees * (1 + params.forsHeight) + 1) +
              params.numLayers * prodLayerHashBudget params) (qs₂ := 0)
            hXof (fun dOpt => ?_) (by omega) (by omega)
          cases dOpt with
          | none => exact HashSignAdv.Within.done _ _ 0
          | some pr =>
            rcases pr with ⟨derivedLeafIdx, idxs⟩
            dsimp only
            split
            · exact HashSignAdv.Within.done _ _ 0
            · refine HashSignAdv.Within.bind_le
                (qh₂ := 1 + params.numLayers * prodLayerHashBudget params) (qs₂ := 0)
                (advForsRootsWithCands_within _ _ _ _ _ _ _ _) (fun fr => ?_) (by omega) (by omega)
              cases fr.1 with
              | none => exact HashSignAdv.Within.done _ _ 0
              | some _ =>
                refine HashSignAdv.Within.bind_le
                  (qh₂ := params.numLayers * prodLayerHashBudget params) (qs₂ := 0)
                  (advRawHash_within _) (fun forsPk => ?_) (by omega) (by omega)
                have hHt := advHypertreeLayersWithCands_within params pk.pkSeed pk.pkRoot sig.rRand log
                  0 sig.leafGlobalIdx forsPk sig.layerSigs
                rw [hLsLen] at hHt
                exact HashSignAdv.Within.map _ hHt
      · simp only [↓reduceIte, prodXofHashBudget, prodForsHashBudget, hSt]
        split
        · exact HashSignAdv.Within.done _ _ 0
        · have hHt := advHypertreeLayersWithCands_within params pk.pkSeed pk.pkRoot sig.rRand log
            0 sig.leafGlobalIdx mu sig.layerSigs
          rw [hLsLen] at hHt
          exact (HashSignAdv.Within.map _ hHt).mono (by omega) (by omega)

theorem runHashSignAdv_advVerifyWithTcrCands (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pk : PqPublicKey) (log : List (List UInt8 × PqHashSig))
    (msg : List UInt8) (sig : PqHashSig) (qs : List ProdSigningQuery) :
    runHashSignAdv suite params sk qs (advVerifyWithTcrCands params pk log msg sig) =
      (publicVerifierWithTcrCands suite params pk log msg sig, qs) := by
  unfold advVerifyWithTcrCands publicVerifierWithTcrCands
  split
  · rfl
  · split
    · rfl
    · rw [runHashSignAdv_bind]
      dsimp only [advRawHash, runHashSignAdv]
      cases hSt : params.statefulJorts
      · simp only [Bool.false_eq_true, ↓reduceIte]
        split
        · rfl
        · rw [runHashSignAdv_bind, runHashSignAdv_advDeriveProductionStatelessInputs]
          dsimp only
          cases deriveProductionStatelessInputs suite params sig.rRand pk.pkSeed pk.pkRoot _ with
          | none => rfl
          | some pr =>
            rcases pr with ⟨derivedLeafIdx, idxs⟩
            dsimp only
            split
            · rfl
            · rw [runHashSignAdv_bind, runHashSignAdv_advForsRootsWithCands]
              dsimp only
              cases (forsRootsWithCands suite params pk.pkSeed
                  (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
                  (sig.leafGlobalIdx % 2 ^ params.subtreeHeight) idxs sig.forsOpenings
                  0 params.forsTrees).1 with
              | none => rfl
              | some roots =>
                dsimp only
                rw [runHashSignAdv_bind]
                dsimp only [advRawHash, runHashSignAdv, HashSignAdv.map]
                rw [runHashSignAdv_bind, runHashSignAdv_advHypertreeLayersWithCands]
                rfl
      · simp only [↓reduceIte]
        split
        · rfl
        · dsimp only [HashSignAdv.map]
          rw [runHashSignAdv_bind, runHashSignAdv_advHypertreeLayersWithCands]
          rfl

theorem advVerifyProductionPqHashSig_within (params : PqHashParams) (pk : PqPublicKey)
    (msg : List UInt8) (sig : PqHashSig) :
    (advVerifyProductionPqHashSig params pk msg sig).Within (prodVerifierHashBudget params) 0 :=
  HashSignAdv.Within.map _ (advVerifyWithTcrCands_within params pk [] msg sig)

theorem runHashSignAdv_advVerifyProductionPqHashSig (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) (pk : PqPublicKey)
    (msg : List UInt8) (sig : PqHashSig) (qs : List ProdSigningQuery) :
    runHashSignAdv suite params sk qs (advVerifyProductionPqHashSig params pk msg sig) =
      (verifyProductionPqHashSig suite params pk msg sig, qs) := by
  unfold advVerifyProductionPqHashSig HashSignAdv.map
  rw [runHashSignAdv_bind, runHashSignAdv_advVerifyWithTcrCands, ← publicVerifierWithTcrCands_fst]
  rfl


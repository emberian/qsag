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

/-! ## 4. Completeness of `publicVerifierWithTcrCands` on `prodTcrOutput` -/

private theorem prodWalkMerkleExtract_mem_cands (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kind : AdrsKind) (leafFn : Nat → List UInt8)
    (U H : Nat) (C : Type)
    (mkCol : ∀ (h n : Nat) (a b : List UInt8),
      h + 1 ≤ H → n * 2 ^ (h + 1) ≤ U → U < (n + 1) * 2 ^ (h + 1) →
      thPreimage tagThH pkSeed ⟨layer, tree, kind, 0, UInt32.ofNat (h + 1), UInt32.ofNat n⟩ [a, b] ≠
        thPreimage tagThH pkSeed ⟨layer, tree, kind, 0, UInt32.ofNat (h + 1), UInt32.ofNat n⟩
          [computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * n),
           computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * n + 1)] →
      suite.rawHash
          (thPreimage tagThH pkSeed ⟨layer, tree, kind, 0, UInt32.ofNat (h + 1), UInt32.ofNat n⟩
            [a, b]) =
        suite.rawHash
          (thPreimage tagThH pkSeed ⟨layer, tree, kind, 0, UInt32.ofNat (h + 1), UInt32.ofNat n⟩
            [computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * n),
             computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * n + 1)]) → C)
    (proj : C → Nat × Nat × List UInt8)
    (hProj : ∀ h n a b hLe hLo hHi hNe hHash,
      proj (mkCol h n a b hLe hLo hHi hNe hHash) =
        (h, n, thPreimage tagThH pkSeed
          ⟨layer, tree, kind, 0, UInt32.ofNat (h + 1), UInt32.ofNat n⟩ [a, b])) :
    ∀ (h d nodeIdx localIdx : Nat) (leaf : List UInt8) (path : List (List UInt8))
      (hLe : h ≤ H) (hLt : localIdx < 2 ^ h) (hU : nodeIdx * 2 ^ h + localIdx = U)
      (hW : walkMerkleAuthPath suite pkSeed layer tree kind h nodeIdx localIdx leaf path =
        some (computeMerkleNode suite pkSeed layer tree kind leafFn h nodeIdx)) (c : C),
      prodWalkMerkleExtract suite pkSeed layer tree kind leafFn U H C mkCol
        h nodeIdx localIdx leaf path hLe hLt hU hW = .inr c →
      ∃ d', (proj c).1 = (proj c).1 ∧
        ((proj c).1, d', (proj c).2.1, (proj c).2.2) ∈
          (walkMerkleKpWithCands suite pkSeed layer tree kind 0 h d nodeIdx nodeIdx localIdx leaf path).2
  | 0, _, _, _, _, [], _, _, _, _, _, hEx => by cases hEx
  | 0, _, _, _, _, _ :: _, _, _, _, hW, _, _ => by simp [walkMerkleAuthPath] at hW
  | _ + 1, _, _, _, _, [], _, _, _, hW, _, _ => by simp [walkMerkleAuthPath] at hW
  | h + 1, d, nodeIdx, localIdx, leaf, sib :: rest, hLe, hLt, hU, hW, c, hEx => by
    simp only [prodWalkMerkleExtract] at hEx
    unfold walkMerkleKpWithCands
    by_cases hHalf : localIdx < 2 ^ h
    · simp only [hHalf, ↓reduceDIte, ↓reduceIte] at hEx ⊢
      split at hEx
      · rename_i hSub
        exfalso
        have hW' := hW
        simp only [walkMerkleAuthPath, hHalf, ↓reduceIte] at hW'
        rw [hSub] at hW'
        cases hW'
      · rename_i sub hSub
        have hSubKp : (walkMerkleKpWithCands suite pkSeed layer tree kind 0 h (d + 1)
            (2 * nodeIdx) (2 * nodeIdx) localIdx leaf rest).1 = some sub := by
          rw [walkMerkleKpWithCands_fst, walkMerkleAuthPathKp_zero_eq]; exact hSub
        rw [hSubKp]
        dsimp only at hEx ⊢
        split at hEx
        · obtain ⟨d', _, hMem⟩ := prodWalkMerkleExtract_mem_cands suite pkSeed layer tree kind
            leafFn U H C mkCol proj hProj h (d + 1) (2 * nodeIdx) localIdx leaf rest
            _ _ _ _ c hEx
          exact ⟨d', trivial, List.mem_cons_of_mem _ hMem⟩
        · injection hEx with hC
          subst hC
          rw [hProj]
          exact ⟨d, trivial, List.mem_cons_self⟩
    · simp only [hHalf, ↓reduceDIte, ↓reduceIte] at hEx ⊢
      split at hEx
      · rename_i hSub
        exfalso
        have hW' := hW
        simp only [walkMerkleAuthPath, hHalf, ↓reduceIte] at hW'
        rw [hSub] at hW'
        cases hW'
      · rename_i sub hSub
        have hSubKp : (walkMerkleKpWithCands suite pkSeed layer tree kind 0 h (d + 1)
            (2 * nodeIdx + 1) (2 * nodeIdx + 1) (localIdx - 2 ^ h) leaf rest).1 = some sub := by
          rw [walkMerkleKpWithCands_fst, walkMerkleAuthPathKp_zero_eq]; exact hSub
        rw [hSubKp]
        dsimp only at hEx ⊢
        split at hEx
        · obtain ⟨d', _, hMem⟩ := prodWalkMerkleExtract_mem_cands suite pkSeed layer tree kind
            leafFn U H C mkCol proj hProj h (d + 1) (2 * nodeIdx + 1) (localIdx - 2 ^ h) leaf rest
            _ _ _ _ c hEx
          exact ⟨d', trivial, List.mem_cons_of_mem _ hMem⟩
        · injection hEx with hC
          subst hC
          rw [hProj]
          exact ⟨d, trivial, List.mem_cons_self⟩

private theorem prodWalkMerkleExtract_inr_prop (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kind : AdrsKind) (leafFn : Nat → List UInt8)
    (U H : Nat) (C : Type)
    (mkCol : ∀ (h n : Nat) (a b : List UInt8),
      h + 1 ≤ H → n * 2 ^ (h + 1) ≤ U → U < (n + 1) * 2 ^ (h + 1) →
      thPreimage tagThH pkSeed ⟨layer, tree, kind, 0, UInt32.ofNat (h + 1), UInt32.ofNat n⟩ [a, b] ≠
        thPreimage tagThH pkSeed ⟨layer, tree, kind, 0, UInt32.ofNat (h + 1), UInt32.ofNat n⟩
          [computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * n),
           computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * n + 1)] →
      suite.rawHash
          (thPreimage tagThH pkSeed ⟨layer, tree, kind, 0, UInt32.ofNat (h + 1), UInt32.ofNat n⟩
            [a, b]) =
        suite.rawHash
          (thPreimage tagThH pkSeed ⟨layer, tree, kind, 0, UInt32.ofNat (h + 1), UInt32.ofNat n⟩
            [computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * n),
             computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * n + 1)]) → C)
    (P : C → Prop)
    (hMk : ∀ h n a b hLe hLo hHi hNe hHash, P (mkCol h n a b hLe hLo hHi hNe hHash)) :
    ∀ (h nodeIdx localIdx : Nat) (leaf : List UInt8) (path : List (List UInt8))
      (hLe : h ≤ H) (hLt : localIdx < 2 ^ h) (hU : nodeIdx * 2 ^ h + localIdx = U)
      (hW : walkMerkleAuthPath suite pkSeed layer tree kind h nodeIdx localIdx leaf path =
        some (computeMerkleNode suite pkSeed layer tree kind leafFn h nodeIdx)) (c : C),
      prodWalkMerkleExtract suite pkSeed layer tree kind leafFn U H C mkCol
        h nodeIdx localIdx leaf path hLe hLt hU hW = .inr c → P c
  | 0, _, _, _, [], _, _, _, _, _, hEx => by cases hEx
  | 0, _, _, _, _ :: _, _, _, _, hW, _, _ => by simp [walkMerkleAuthPath] at hW
  | _ + 1, _, _, _, [], _, _, _, hW, _, _ => by simp [walkMerkleAuthPath] at hW
  | h + 1, nodeIdx, localIdx, leaf, sib :: rest, hLe, hLt, hU, hW, c, hEx => by
    simp only [prodWalkMerkleExtract] at hEx
    by_cases hHalf : localIdx < 2 ^ h
    · simp only [hHalf, ↓reduceDIte] at hEx
      split at hEx
      · rename_i hSub
        exfalso; have hW' := hW
        simp only [walkMerkleAuthPath, hHalf, ↓reduceIte] at hW'
        rw [hSub] at hW'; cases hW'
      · split at hEx
        · exact prodWalkMerkleExtract_inr_prop suite pkSeed layer tree kind leafFn U H C mkCol P hMk
            h (2 * nodeIdx) localIdx leaf rest _ _ _ _ c hEx
        · injection hEx with hC; subst hC; exact hMk _ _ _ _ _ _ _ _ _
    · simp only [hHalf, ↓reduceDIte] at hEx
      split at hEx
      · rename_i hSub
        exfalso; have hW' := hW
        simp only [walkMerkleAuthPath, hHalf, ↓reduceIte] at hW'
        rw [hSub] at hW'; cases hW'
      · split at hEx
        · exact prodWalkMerkleExtract_inr_prop suite pkSeed layer tree kind leafFn U H C mkCol P hMk
            h (2 * nodeIdx + 1) (localIdx - 2 ^ h) leaf rest _ _ _ _ c hEx
        · injection hEx with hC; subst hC; exact hMk _ _ _ _ _ _ _ _ _

private theorem prodWalkMerkleKpExtract_mem_cands (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kind : AdrsKind) (kp : UInt32)
    (leafFn : Nat → List UInt8) (root U H : Nat) (C : Type)
    (mkCol : ∀ (h d b : Nat) (x y : List UInt8),
      d + (h + 1) = H → b * 2 ^ (h + 1) ≤ U → U < (b + 1) * 2 ^ (h + 1) →
      thPreimage tagThH pkSeed
          ⟨layer, tree, kind, kp, UInt32.ofNat (h + 1), UInt32.ofNat (root * 2 ^ d + b)⟩ [x, y] ≠
        thPreimage tagThH pkSeed
          ⟨layer, tree, kind, kp, UInt32.ofNat (h + 1), UInt32.ofNat (root * 2 ^ d + b)⟩
          [computeMerkleNodeKp suite pkSeed layer tree kind kp leafFn h
             (2 * (root * 2 ^ d + b)) (2 * b),
           computeMerkleNodeKp suite pkSeed layer tree kind kp leafFn h
             (2 * (root * 2 ^ d + b) + 1) (2 * b + 1)] →
      suite.rawHash
          (thPreimage tagThH pkSeed
            ⟨layer, tree, kind, kp, UInt32.ofNat (h + 1), UInt32.ofNat (root * 2 ^ d + b)⟩ [x, y]) =
        suite.rawHash
          (thPreimage tagThH pkSeed
            ⟨layer, tree, kind, kp, UInt32.ofNat (h + 1), UInt32.ofNat (root * 2 ^ d + b)⟩
            [computeMerkleNodeKp suite pkSeed layer tree kind kp leafFn h
               (2 * (root * 2 ^ d + b)) (2 * b),
             computeMerkleNodeKp suite pkSeed layer tree kind kp leafFn h
               (2 * (root * 2 ^ d + b) + 1) (2 * b + 1)]) → C)
    (proj : C → Nat × Nat × Nat × List UInt8)
    (hProj : ∀ h d b x y hD hLo hHi hNe hHash,
      proj (mkCol h d b x y hD hLo hHi hNe hHash) =
        (h, d, b, thPreimage tagThH pkSeed
          ⟨layer, tree, kind, kp, UInt32.ofNat (h + 1), UInt32.ofNat (root * 2 ^ d + b)⟩ [x, y])) :
    ∀ (h d localBase localIdx : Nat) (leaf : List UInt8) (path : List (List UInt8))
      (hD : d + h = H) (hLt : localIdx < 2 ^ h) (hU : localBase * 2 ^ h + localIdx = U)
      (hW : walkMerkleAuthPathKp suite pkSeed layer tree kind kp h (root * 2 ^ d + localBase)
        localIdx leaf path =
        some (computeMerkleNodeKp suite pkSeed layer tree kind kp leafFn h
          (root * 2 ^ d + localBase) localBase)) (c : C),
      prodWalkMerkleKpExtract suite pkSeed layer tree kind kp leafFn root U H C mkCol
        h d localBase localIdx leaf path hD hLt hU hW = .inr c →
      proj c ∈ (walkMerkleKpWithCands suite pkSeed layer tree kind kp h d
        (root * 2 ^ d + localBase) localBase localIdx leaf path).2
  | 0, _, _, _, _, [], _, _, _, _, _, hEx => by cases hEx
  | 0, _, _, _, _, _ :: _, _, _, _, hW, _, _ => by simp [walkMerkleAuthPathKp] at hW
  | _ + 1, _, _, _, _, [], _, _, _, hW, _, _ => by simp [walkMerkleAuthPathKp] at hW
  | h + 1, d, localBase, localIdx, leaf, sib :: rest, hD, hLt, hU, hW, c, hEx => by
    have hPow : root * 2 ^ (d + 1) = 2 * (root * 2 ^ d) := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm]
    have hL : 2 * (root * 2 ^ d + localBase) = root * 2 ^ (d + 1) + 2 * localBase := by
      rw [hPow, Nat.mul_add]
    have hR : 2 * (root * 2 ^ d + localBase) + 1 = root * 2 ^ (d + 1) + (2 * localBase + 1) := by
      rw [hPow, Nat.mul_add, Nat.add_assoc]
    simp only [prodWalkMerkleKpExtract] at hEx
    unfold walkMerkleKpWithCands
    by_cases hHalf : localIdx < 2 ^ h
    · simp only [hHalf, ↓reduceDIte, ↓reduceIte] at hEx ⊢
      split at hEx
      · rename_i hSub
        exfalso
        have hW' := hW
        simp only [walkMerkleAuthPathKp, hHalf, ↓reduceIte] at hW'
        rw [hSub] at hW'
        cases hW'
      · rename_i sub hSub
        have hSubW : (walkMerkleKpWithCands suite pkSeed layer tree kind kp h (d + 1)
            (2 * (root * 2 ^ d + localBase)) (2 * localBase) localIdx leaf rest).1 = some sub := by
          rw [walkMerkleKpWithCands_fst]; exact hSub
        rw [hSubW]
        dsimp only at hEx ⊢
        split at hEx
        · apply List.mem_cons_of_mem
          rw [hL]
          exact prodWalkMerkleKpExtract_mem_cands suite pkSeed layer tree kind kp leafFn root U H C
            mkCol proj hProj h (d + 1) (2 * localBase) localIdx leaf rest _ _ _ _ c hEx
        · injection hEx with hC
          subst hC
          rw [hProj]
          exact List.mem_cons_self
    · simp only [hHalf, ↓reduceDIte, ↓reduceIte] at hEx ⊢
      split at hEx
      · rename_i hSub
        exfalso
        have hW' := hW
        simp only [walkMerkleAuthPathKp, hHalf, ↓reduceIte] at hW'
        rw [hSub] at hW'
        cases hW'
      · rename_i sub hSub
        have hSubW : (walkMerkleKpWithCands suite pkSeed layer tree kind kp h (d + 1)
            (2 * (root * 2 ^ d + localBase) + 1) (2 * localBase + 1) (localIdx - 2 ^ h) leaf rest).1 =
            some sub := by
          rw [walkMerkleKpWithCands_fst]; exact hSub
        rw [hSubW]
        dsimp only at hEx ⊢
        split at hEx
        · apply List.mem_cons_of_mem
          rw [hR]
          exact prodWalkMerkleKpExtract_mem_cands suite pkSeed layer tree kind kp leafFn root U H C
            mkCol proj hProj h (d + 1) (2 * localBase + 1) (localIdx - 2 ^ h) leaf rest _ _ _ _ c hEx
        · injection hEx with hC
          subst hC
          rw [hProj]
          exact List.mem_cons_self

private theorem prodWalkMerkleKpExtract_inr_prop (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kind : AdrsKind) (kp : UInt32)
    (leafFn : Nat → List UInt8) (root U H : Nat) (C : Type)
    (mkCol : ∀ (h d b : Nat) (x y : List UInt8),
      d + (h + 1) = H → b * 2 ^ (h + 1) ≤ U → U < (b + 1) * 2 ^ (h + 1) →
      thPreimage tagThH pkSeed
          ⟨layer, tree, kind, kp, UInt32.ofNat (h + 1), UInt32.ofNat (root * 2 ^ d + b)⟩ [x, y] ≠
        thPreimage tagThH pkSeed
          ⟨layer, tree, kind, kp, UInt32.ofNat (h + 1), UInt32.ofNat (root * 2 ^ d + b)⟩
          [computeMerkleNodeKp suite pkSeed layer tree kind kp leafFn h
             (2 * (root * 2 ^ d + b)) (2 * b),
           computeMerkleNodeKp suite pkSeed layer tree kind kp leafFn h
             (2 * (root * 2 ^ d + b) + 1) (2 * b + 1)] →
      suite.rawHash
          (thPreimage tagThH pkSeed
            ⟨layer, tree, kind, kp, UInt32.ofNat (h + 1), UInt32.ofNat (root * 2 ^ d + b)⟩ [x, y]) =
        suite.rawHash
          (thPreimage tagThH pkSeed
            ⟨layer, tree, kind, kp, UInt32.ofNat (h + 1), UInt32.ofNat (root * 2 ^ d + b)⟩
            [computeMerkleNodeKp suite pkSeed layer tree kind kp leafFn h
               (2 * (root * 2 ^ d + b)) (2 * b),
             computeMerkleNodeKp suite pkSeed layer tree kind kp leafFn h
               (2 * (root * 2 ^ d + b) + 1) (2 * b + 1)]) → C)
    (P : C → Prop)
    (hMk : ∀ h d b x y hD hLo hHi hNe hHash, P (mkCol h d b x y hD hLo hHi hNe hHash)) :
    ∀ (h d localBase localIdx : Nat) (leaf : List UInt8) (path : List (List UInt8))
      (hD : d + h = H) (hLt : localIdx < 2 ^ h) (hU : localBase * 2 ^ h + localIdx = U)
      (hW : walkMerkleAuthPathKp suite pkSeed layer tree kind kp h (root * 2 ^ d + localBase)
        localIdx leaf path =
        some (computeMerkleNodeKp suite pkSeed layer tree kind kp leafFn h
          (root * 2 ^ d + localBase) localBase)) (c : C),
      prodWalkMerkleKpExtract suite pkSeed layer tree kind kp leafFn root U H C mkCol
        h d localBase localIdx leaf path hD hLt hU hW = .inr c → P c
  | 0, _, _, _, _, [], _, _, _, _, _, hEx => by cases hEx
  | 0, _, _, _, _, _ :: _, _, _, _, hW, _, _ => by simp [walkMerkleAuthPathKp] at hW
  | _ + 1, _, _, _, _, [], _, _, _, hW, _, _ => by simp [walkMerkleAuthPathKp] at hW
  | h + 1, d, localBase, localIdx, leaf, sib :: rest, hD, hLt, hU, hW, c, hEx => by
    simp only [prodWalkMerkleKpExtract] at hEx
    by_cases hHalf : localIdx < 2 ^ h
    · simp only [hHalf, ↓reduceDIte] at hEx
      split at hEx
      · rename_i hSub
        exfalso; have hW' := hW
        simp only [walkMerkleAuthPathKp, hHalf, ↓reduceIte] at hW'
        rw [hSub] at hW'; cases hW'
      · split at hEx
        · exact prodWalkMerkleKpExtract_inr_prop suite pkSeed layer tree kind kp leafFn root U H C
            mkCol P hMk h (d + 1) (2 * localBase) localIdx leaf rest _ _ _ _ c hEx
        · injection hEx with hC; subst hC; exact hMk _ _ _ _ _ _ _ _ _ _
    · simp only [hHalf, ↓reduceDIte] at hEx
      split at hEx
      · rename_i hSub
        exfalso; have hW' := hW
        simp only [walkMerkleAuthPathKp, hHalf, ↓reduceIte] at hW'
        rw [hSub] at hW'; cases hW'
      · split at hEx
        · exact prodWalkMerkleKpExtract_inr_prop suite pkSeed layer tree kind kp leafFn root U H C
            mkCol P hMk h (d + 1) (2 * localBase + 1) (localIdx - 2 ^ h) leaf rest _ _ _ _ c hEx
        · injection hEx with hC; subst hC; exact hMk _ _ _ _ _ _ _ _ _ _

private theorem prodChainExtract_mem_cands (suite : TweakableHashSuite) (sk : PqSecretKey)
    (layer : UInt32) (tree : UInt64) (kp r top : Nat) (C : Type)
    (mkCol : ∀ (s : Nat) (x : List UInt8), s + 1 ≤ top →
      thPreimage tagThF sk.pkSeed
          ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩ [x] ≠
        thPreimage tagThF sk.pkSeed
          ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩
          [honestChainNode suite sk layer tree kp r s] →
      suite.rawHash
          (thPreimage tagThF sk.pkSeed
            ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩ [x]) =
        suite.rawHash
          (thPreimage tagThF sk.pkSeed
            ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩
            [honestChainNode suite sk layer tree kp r s]) → C)
    (proj : C → Nat × List UInt8)
    (hProj : ∀ s x hs hNe hHash,
      proj (mkCol s x hs hNe hHash) =
        (s, thPreimage tagThF sk.pkSeed
          ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩ [x])) :
    ∀ (k s : Nat) (x : List UInt8) (hTop : s + k = top)
      (hStep : wotsChainSteps suite sk.pkSeed layer tree kp r s k x =
        honestChainNode suite sk layer tree kp r (s + k)) (c : C),
      prodChainExtract suite sk layer tree kp r top C mkCol k s x hTop hStep = .inr c →
      proj c ∈ (wotsChainWithCands suite sk.pkSeed layer tree kp r s k x).2
  | 0, _, _, _, _, _, hEx => by cases hEx
  | k + 1, s, x, hTop, hStep, c, hEx => by
    unfold prodChainExtract at hEx
    unfold wotsChainWithCands
    dsimp only at hEx ⊢
    split at hEx
    · rename_i c' hRec
      injection hEx with hEq
      subst hEq
      exact List.mem_cons_of_mem _ (prodChainExtract_mem_cands suite sk layer tree kp r top C
        mkCol proj hProj k (s + 1) _ _ _ c' hRec)
    · split at hEx
      · cases hEx
      · injection hEx with hEq
        subst hEq
        rw [hProj]
        exact List.mem_cons_self

private theorem prodChainExtract_inr_prop (suite : TweakableHashSuite) (sk : PqSecretKey)
    (layer : UInt32) (tree : UInt64) (kp r top : Nat) (C : Type)
    (mkCol : ∀ (s : Nat) (x : List UInt8), s + 1 ≤ top →
      thPreimage tagThF sk.pkSeed
          ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩ [x] ≠
        thPreimage tagThF sk.pkSeed
          ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩
          [honestChainNode suite sk layer tree kp r s] →
      suite.rawHash
          (thPreimage tagThF sk.pkSeed
            ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩ [x]) =
        suite.rawHash
          (thPreimage tagThF sk.pkSeed
            ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩
            [honestChainNode suite sk layer tree kp r s]) → C)
    (P : C → Prop)
    (hMk : ∀ s x hs hNe hHash, P (mkCol s x hs hNe hHash)) :
    ∀ (k s : Nat) (x : List UInt8) (hTop : s + k = top)
      (hStep : wotsChainSteps suite sk.pkSeed layer tree kp r s k x =
        honestChainNode suite sk layer tree kp r (s + k)) (c : C),
      prodChainExtract suite sk layer tree kp r top C mkCol k s x hTop hStep = .inr c → P c
  | 0, _, _, _, _, _, hEx => by cases hEx
  | k + 1, s, x, hTop, hStep, c, hEx => by
    unfold prodChainExtract at hEx
    dsimp only at hEx
    split at hEx
    · rename_i c' hRec
      injection hEx with hEq
      subst hEq
      exact prodChainExtract_inr_prop suite sk layer tree kp r top C mkCol P hMk k (s + 1) _ _ _
        c' hRec
    · split at hEx
      · cases hEx
      · injection hEx with hEq
        subst hEq
        exact hMk _ _ _ _ _

private theorem prodAllChainsExtract_inr_prop (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (layer : UInt32) (tree : UInt64) (kp : Nat)
    (digF : List Nat) (chains : List (List UInt8)) (C : Type)
    (mkCol : ∀ (r s : Nat) (x : List UInt8), r < params.ell1 → s + 1 ≤ params.w - 1 →
      thPreimage tagThF sk.pkSeed
          ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩ [x] ≠
        thPreimage tagThF sk.pkSeed
          ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩
          [honestChainNode suite sk layer tree kp r s] →
      suite.rawHash
          (thPreimage tagThF sk.pkSeed
            ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩ [x]) =
        suite.rawHash
          (thPreimage tagThF sk.pkSeed
            ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩
            [honestChainNode suite sk layer tree kp r s]) → C)
    (P : C → Prop)
    (hMk : ∀ r s x hr hs hNe hHash, P (mkCol r s x hr hs hNe hHash))
    (hEnds : recoverWotsEndpoints suite params sk.pkSeed layer tree kp digF chains =
      (List.range params.ell1).map fun r => honestChainNode suite sk layer tree kp r (params.w - 1))
    (hTsw : checkTargetSum params.w params.ell1 params.targetSum digF = true) :
    ∀ (m : Nat) (hmLe : m ≤ params.ell1) (c : C),
      prodAllChainsExtract suite params sk layer tree kp digF chains C mkCol hEnds hTsw m hmLe =
        .inr c → P c
  | 0, _, _, hEx => by cases hEx
  | m + 1, hmLe, c, hEx => by
    unfold prodAllChainsExtract at hEx
    dsimp only at hEx
    split at hEx
    · rename_i c' hPrev
      injection hEx with hEq
      subst hEq
      exact prodAllChainsExtract_inr_prop suite params sk layer tree kp digF chains C mkCol P hMk
        hEnds hTsw m _ c' hPrev
    · split at hEx
      · rename_i c' hCh
        injection hEx with hEq
        subst hEq
        exact prodChainExtract_inr_prop suite sk layer tree kp m (params.w - 1) C
          (fun s x hs hNe hHash => mkCol m s x hmLe hs hNe hHash) P
          (fun s x hs hNe hHash => hMk m s x hmLe hs hNe hHash)
          (params.w - 1 - digF.getD m 0) (digF.getD m 0) (chains.getD m []) _ _ c' hCh
      · cases hEx

private theorem prodAllChainsExtract_mem_cands (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (layer : UInt32) (tree : UInt64) (kp : Nat)
    (digF : List Nat) (chains : List (List UInt8)) (C : Type)
    (mkCol : ∀ (r s : Nat) (x : List UInt8), r < params.ell1 → s + 1 ≤ params.w - 1 →
      thPreimage tagThF sk.pkSeed
          ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩ [x] ≠
        thPreimage tagThF sk.pkSeed
          ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩
          [honestChainNode suite sk layer tree kp r s] →
      suite.rawHash
          (thPreimage tagThF sk.pkSeed
            ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩ [x]) =
        suite.rawHash
          (thPreimage tagThF sk.pkSeed
            ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩
            [honestChainNode suite sk layer tree kp r s]) → C)
    (proj : C → Nat × Nat × List UInt8)
    (hProj : ∀ r s x hr hs hNe hHash,
      proj (mkCol r s x hr hs hNe hHash) =
        (r, s, thPreimage tagThF sk.pkSeed
          ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩ [x]))
    (hEnds : recoverWotsEndpoints suite params sk.pkSeed layer tree kp digF chains =
      (List.range params.ell1).map fun r => honestChainNode suite sk layer tree kp r (params.w - 1))
    (hTsw : checkTargetSum params.w params.ell1 params.targetSum digF = true) :
    ∀ (m : Nat) (hmLe : m ≤ params.ell1) (c : C),
      prodAllChainsExtract suite params sk layer tree kp digF chains C mkCol hEnds hTsw m hmLe =
        .inr c →
      proj c ∈ (allWotsChainsWithCands suite params sk.pkSeed layer tree kp digF chains m).2
  | 0, _, _, hEx => by cases hEx
  | m + 1, hmLe, c, hEx => by
    unfold prodAllChainsExtract at hEx
    unfold allWotsChainsWithCands
    dsimp only at hEx ⊢
    split at hEx
    · rename_i c' hPrev
      injection hEx with hEq
      subst hEq
      exact List.mem_append_left _ (prodAllChainsExtract_mem_cands suite params sk layer tree kp
        digF chains C mkCol proj hProj hEnds hTsw m _ c' hPrev)
    · split at hEx
      · rename_i c' hCh
        injection hEx with hEq
        subst hEq
        apply List.mem_append_right
        have hMem := prodChainExtract_mem_cands suite sk layer tree kp m (params.w - 1) C
          (fun s x hs hNe hHash => mkCol m s x hmLe hs hNe hHash)
          (fun c0 => ((proj c0).2.1, (proj c0).2.2))
          (fun s x hs hNe hHash => by rw [hProj])
          (params.w - 1 - digF.getD m 0) (digF.getD m 0) (chains.getD m []) _ _ c' hCh
        have hFst : (proj c').1 = m :=
          prodChainExtract_inr_prop suite sk layer tree kp m (params.w - 1) C
            (fun s x hs hNe hHash => mkCol m s x hmLe hs hNe hHash)
            (fun c0 => (proj c0).1 = m)
            (fun s x hs hNe hHash => by rw [hProj])
            (params.w - 1 - digF.getD m 0) (digF.getD m 0) (chains.getD m []) _ _ c' hCh
        exact List.mem_map.mpr ⟨((proj c').2.1, (proj c').2.2), hMem, by
          rcases hp : proj c' with ⟨a, b, d⟩
          rw [hp] at hFst
          dsimp only at hFst ⊢
          subst hFst
          rfl⟩
      · cases hEx

private theorem prodForsRootsExtract_mem_cands (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8)
    (sigStar : PqHashSig) (hStateless : params.statefulJorts = false)
    (tree0 : UInt64) (kp0 : Nat) (idxs : List Nat) (ops : List ForsTreeOpening)
    (hIdxs : ∀ J, J < params.forsTrees → idxs.getD J 0 < 2 ^ params.forsHeight)
    (mkCol : ∀ (j h d b : Nat) (x y : List UInt8),
      j < params.forsTrees → d + (h + 1) = params.forsHeight →
      b * 2 ^ (h + 1) ≤ idxs.getD j 0 → idxs.getD j 0 < (b + 1) * 2 ^ (h + 1) →
      thPreimage tagThH sk.pkSeed
          ⟨0, tree0, .forsTree, UInt32.ofNat kp0, UInt32.ofNat (h + 1),
            UInt32.ofNat (j * 2 ^ d + b)⟩ [x, y] ≠
        thPreimage tagThH sk.pkSeed
          ⟨0, tree0, .forsTree, UInt32.ofNat kp0, UInt32.ofNat (h + 1),
            UInt32.ofNat (j * 2 ^ d + b)⟩
          [computeMerkleNodeKp suite sk.pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0)
             (forsIndexedLeafFn suite sk tree0 kp0 j) h (2 * (j * 2 ^ d + b)) (2 * b),
           computeMerkleNodeKp suite sk.pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0)
             (forsIndexedLeafFn suite sk tree0 kp0 j) h (2 * (j * 2 ^ d + b) + 1) (2 * b + 1)] →
      suite.rawHash
          (thPreimage tagThH sk.pkSeed
            ⟨0, tree0, .forsTree, UInt32.ofNat kp0, UInt32.ofNat (h + 1),
              UInt32.ofNat (j * 2 ^ d + b)⟩ [x, y]) =
        suite.rawHash
          (thPreimage tagThH sk.pkSeed
            ⟨0, tree0, .forsTree, UInt32.ofNat kp0, UInt32.ofNat (h + 1),
              UInt32.ofNat (j * 2 ^ d + b)⟩
            [computeMerkleNodeKp suite sk.pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0)
               (forsIndexedLeafFn suite sk tree0 kp0 j) h (2 * (j * 2 ^ d + b)) (2 * b),
             computeMerkleNodeKp suite sk.pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0)
               (forsIndexedLeafFn suite sk tree0 kp0 j) h (2 * (j * 2 ^ d + b) + 1)
               (2 * b + 1)]) → ProdTcrWitness suite params sk log msgStar sigStar)
    (hMk : ∀ j h d b x y hj hD hLo hHi hNe hHash,
      ((mkCol j h d b x y hj hD hLo hHi hNe hHash).target,
       (mkCol j h d b x y hj hD hLo hHi hNe hHash).forged) =
        (.forsNode j h d b, thPreimage tagThH sk.pkSeed
          ⟨0, tree0, .forsTree, UInt32.ofNat kp0, UInt32.ofNat (h + 1),
            UInt32.ofNat (j * 2 ^ d + b)⟩ [x, y])) :
    ∀ (rem j : Nat) (rootsF : List (List UInt8)) (hB : j + rem ≤ params.forsTrees)
      (hRec : recoverProductionForsTreeRoots suite params sk.pkSeed tree0 kp0 idxs ops j rem =
        some rootsF)
      (hEq : rootsF = (List.range rem).map (fun off =>
        computeMerkleNodeKp suite sk.pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0)
          (forsIndexedLeafFn suite sk tree0 kp0 (j + off)) params.forsHeight (j + off) 0))
      (w : ProdTcrWitness suite params sk log msgStar sigStar),
      prodForsRootsExtract suite params sk tree0 kp0 idxs ops
        (ProdTcrWitness suite params sk log msgStar sigStar) mkCol hIdxs rem j rootsF hB hRec hEq =
        .inr w →
      (w.target, w.forged) ∈ (forsRootsWithCands suite params sk.pkSeed tree0 kp0 idxs ops j rem).2
  | 0, _, _, _, _, _, _, hEx => by
    have _ := hStateless
    cases hEx
  | rem + 1, j, rootsF, hB, hRec, hEq, w, hEx => by
    have hInv := prod_recoverForsTreeRoots_succ_inv suite params sk.pkSeed tree0 kp0 idxs ops j rem
      rootsF hRec
    unfold prodForsRootsExtract at hEx
    unfold forsRootsWithCands
    dsimp only at hEx ⊢
    split at hEx
    · rename_i hWalk
      obtain ⟨_, _, hW0, _, _⟩ := hInv
      rw [hWalk] at hW0
      cases hW0
    · rename_i rJ hWalk
      have hW1 : (walkMerkleKpWithCands suite sk.pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0)
          params.forsHeight 0 j 0 (idxs.getD j 0)
          (forsIndexedLeafHash suite sk.pkSeed tree0 kp0 j (idxs.getD j 0)
            (ops.getD j ⟨[], []⟩).secretVal)
          (ops.getD j ⟨[], []⟩).authPath).1 = some rJ := by
        rw [walkMerkleKpWithCands_fst]; exact hWalk
      rw [hW1]
      dsimp only at hEx ⊢
      split at hEx
      · rename_i hRest
        obtain ⟨_, _, _, hR0, _⟩ := hInv
        rw [hRest] at hR0
        cases hR0
      · rename_i rsF hRest
        have hR1 : (forsRootsWithCands suite params sk.pkSeed tree0 kp0 idxs ops (j + 1) rem).1 =
            some rsF := by
          rw [forsRootsWithCands_fst]; exact hRest
        rw [hR1]
        dsimp only at hEx ⊢
        split at hEx
        · rename_i w' hKpEx
          injection hEx with hw
          subst hw
          apply List.mem_append_left
          have hj : j < params.forsTrees :=
            Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.succ_pos rem)) hB
          have hj0 : j * 2 ^ 0 + 0 = j := by rw [Nat.pow_zero, Nat.mul_one, Nat.add_zero]
          let projKp : ProdTcrWitness suite params sk log msgStar sigStar →
              Nat × Nat × Nat × List UInt8 := fun c0 =>
            match c0.target with
            | .forsNode _ h d b => (h, d, b, c0.forged)
            | _ => (0, 0, 0, c0.forged)
          have hMem := prodWalkMerkleKpExtract_mem_cands suite sk.pkSeed 0 tree0 .forsTree
            (UInt32.ofNat kp0) (forsIndexedLeafFn suite sk tree0 kp0 j) j (idxs.getD j 0)
            params.forsHeight (ProdTcrWitness suite params sk log msgStar sigStar)
            (fun h d b x y hD hLo hHi hNe hHash => mkCol j h d b x y hj hD hLo hHi hNe hHash)
            projKp
            (fun h d b x y hD hLo hHi hNe hHash => by
              have hm := hMk j h d b x y hj hD hLo hHi hNe hHash
              have ht := congrArg Prod.fst hm
              have hf := congrArg Prod.snd hm
              dsimp only [projKp] at ht hf ⊢
              rw [ht, hf])
            params.forsHeight 0 0 (idxs.getD j 0) _ _ _ _ _ _ w' hKpEx
          rw [hj0] at hMem
          have hTag : ∃ h d b, w'.target = .forsNode j h d b :=
            prodWalkMerkleKpExtract_inr_prop suite sk.pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0)
              (forsIndexedLeafFn suite sk tree0 kp0 j) j (idxs.getD j 0) params.forsHeight
              (ProdTcrWitness suite params sk log msgStar sigStar)
              (fun h d b x y hD hLo hHi hNe hHash => mkCol j h d b x y hj hD hLo hHi hNe hHash)
              (fun c0 => ∃ h d b, c0.target = .forsNode j h d b)
              (fun h d b x y hD hLo hHi hNe hHash =>
                ⟨h, d, b, congrArg Prod.fst (hMk j h d b x y hj hD hLo hHi hNe hHash)⟩)
              params.forsHeight 0 0 (idxs.getD j 0) _ _ _ _ _ _ w' hKpEx
          obtain ⟨h, d, b, hT⟩ := hTag
          dsimp only [projKp] at hMem
          rw [hT] at hMem ⊢
          exact List.mem_map.mpr ⟨(h, d, b, w'.forged), hMem, rfl⟩
        · split at hEx
          · rename_i w' hRecEx
            injection hEx with hw
            subst hw
            exact List.mem_append_right _ (prodForsRootsExtract_mem_cands suite params sk log
              msgStar sigStar hStateless tree0 kp0 idxs ops hIdxs mkCol hMk rem (j + 1) rsF _
              hRest _ w' hRecEx)
          · cases hEx

private theorem prodLayerExtract_mem_cands (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8)
    (sigStar : PqHashSig) (hw : params.w = 4 ∨ params.w = 16)
    (hPwf : params.productionWellFormed = true)
    (hLog : ∀ e ∈ log, ProdLogEntryOk suite params sk e)
    (hCons : ProdLogConsistent suite params sk log)
    (i : Nat) (hi : i < params.numLayers) (cur : List UInt8)
    (lsig : LayerXmssSig) (rest : List LayerXmssSig)
    (hLs : lsig = sigStar.layerSigs.getD i ⟨0, [], []⟩)
    (hCtr : lsig.tswCtr < 2 ^ 32)
    (digF : List Nat)
    (hDigF : digF = extractBaseWDigits params.w params.ell1
      (productionLayerDigest suite params sigStar.rRand sk.pkSeed
        (derivePublicKey suite params sk).pkRoot cur i
        (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
          2 ^ params.subtreeHeight))
        (UInt32.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) %
          2 ^ params.subtreeHeight))
        (sigStar.layerSigs.getD i ⟨0, [], []⟩).tswCtr))
    (hExt : extractBaseWDigitsChecked params.w params.ell1
      (productionLayerDigest suite params sigStar.rRand sk.pkSeed
        (derivePublicKey suite params sk).pkRoot cur i
        (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
          2 ^ params.subtreeHeight))
        (UInt32.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) %
          2 ^ params.subtreeHeight)) lsig.tswCtr) = some digF)
    (hChainsLen : lsig.wotsChains.length = params.ell1)
    (hDiff : ∀ e ∈ log,
      e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) =
        sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) →
      cur ≠ prodHonestLayerMsg suite params sk e i)
    (hTsw : checkTargetSum params.w params.ell1 params.targetSum digF = true)
    (hWalk : walkMerkleAuthPath suite sk.pkSeed (UInt32.ofNat i)
        (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
          2 ^ params.subtreeHeight)) .tree params.subtreeHeight 0
        (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight)
        (recoverWotsPkFromSig suite params sk.pkSeed (UInt32.ofNat i)
          (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
            2 ^ params.subtreeHeight))
          (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight)
          digF (sigStar.layerSigs.getD i ⟨0, [], []⟩).wotsChains)
        (sigStar.layerSigs.getD i ⟨0, [], []⟩).authPath =
      some (computeXmssSubtreeRoot suite params sk (UInt32.ofNat i)
        (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
          2 ^ params.subtreeHeight))))
    (w : ProdTcrWitness suite params sk log msgStar sigStar)
    (hEx : prodLayerExtract suite params sk log msgStar sigStar hw hPwf hLog hCons i hi cur digF
      hDigF hDiff hTsw hWalk = .inl w) :
    (w.target, w.forged) ∈
      (hypertreeLayersWithCands suite params sk.pkSeed (derivePublicKey suite params sk).pkRoot
        sigStar.rRand log i (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)) cur
        (lsig :: rest)).2 := by
  unfold hypertreeLayersWithCands
  simp only [hCtr, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [← productionLayerDigest_rawHash, hExt]
  dsimp only
  simp only [hTsw, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hChainsLen, ne_eq,
    not_true_eq_false]
  have hWotsEq :
      suite.rawHash (thPreimage tagThTl sk.pkSeed
        ⟨UInt32.ofNat i,
         UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
           2 ^ params.subtreeHeight),
         .wotsPk,
         UInt32.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) %
           2 ^ params.subtreeHeight), 0, 0⟩
        (allWotsChainsWithCands suite params sk.pkSeed (UInt32.ofNat i)
          (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
            2 ^ params.subtreeHeight))
          (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight)
          digF lsig.wotsChains params.ell1).1) =
      recoverWotsPkFromSig suite params sk.pkSeed (UInt32.ofNat i)
        (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
          2 ^ params.subtreeHeight))
        (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight)
        digF lsig.wotsChains := by
    rw [allWotsChainsWithCands_fst, recoverWotsPkFromSig_eq, recoverWotsEndpoints_eq,
      thTweakTl_eq, thCall_eq]
  have hMw1 : (walkMerkleKpWithCands suite sk.pkSeed (UInt32.ofNat i)
      (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
        2 ^ params.subtreeHeight)) .tree 0 params.subtreeHeight 0 0 0
      (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight)
      (suite.rawHash (thPreimage tagThTl sk.pkSeed
        ⟨UInt32.ofNat i,
         UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
           2 ^ params.subtreeHeight),
         .wotsPk,
         UInt32.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) %
           2 ^ params.subtreeHeight), 0, 0⟩
        (allWotsChainsWithCands suite params sk.pkSeed (UInt32.ofNat i)
          (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
            2 ^ params.subtreeHeight))
          (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight)
          digF lsig.wotsChains params.ell1).1))
      lsig.authPath).1 =
      some (computeXmssSubtreeRoot suite params sk (UInt32.ofNat i)
        (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
          2 ^ params.subtreeHeight))) := by
    rw [walkMerkleKpWithCands_fst, walkMerkleAuthPathKp_zero_eq, hWotsEq, hLs]
    exact hWalk
  rw [hMw1]
  dsimp only
  apply List.mem_append_left
  subst hLs
  unfold prodLayerExtract at hEx
  dsimp only at hEx
  split at hEx
  · rename_i w' hWkEx
    injection hEx with hwEq
    subst hwEq
    apply List.mem_append_right
    apply List.mem_cons_of_mem
    apply List.mem_append_right
    let projM : ProdTcrWitness suite params sk log msgStar sigStar → Nat × Nat × List UInt8 :=
      fun c0 => match c0.target with
        | .xmssNode _ h n => (h, n, c0.forged)
        | _ => (0, 0, c0.forged)
    obtain ⟨d', _, hMem⟩ := prodWalkMerkleExtract_mem_cands suite sk.pkSeed (UInt32.ofNat i)
      (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
        2 ^ params.subtreeHeight)) .tree
      (computeWotsPk suite params sk (UInt32.ofNat i)
        (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
          2 ^ params.subtreeHeight)))
      (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight)
      params.subtreeHeight (ProdTcrWitness suite params sk log msgStar sigStar)
      (fun h n a b hH hLo hHi hNe hHash =>
        ⟨.xmssNode i h n, _, ⟨hi, hH, hLo, hHi⟩, ⟨a, b, rfl⟩, hNe, hHash⟩)
      projM (fun _ _ _ _ _ _ _ _ _ => rfl)
      params.subtreeHeight 0 0
      (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight)
      _ _ _ _ _ _ w' hWkEx
    have hTag : ∃ h n, w'.target = .xmssNode i h n :=
      prodWalkMerkleExtract_inr_prop suite sk.pkSeed (UInt32.ofNat i)
        (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
          2 ^ params.subtreeHeight)) .tree
        (computeWotsPk suite params sk (UInt32.ofNat i)
          (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
            2 ^ params.subtreeHeight)))
        (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight)
        params.subtreeHeight (ProdTcrWitness suite params sk log msgStar sigStar)
        (fun h n a b hH hLo hHi hNe hHash =>
          ⟨.xmssNode i h n, _, ⟨hi, hH, hLo, hHi⟩, ⟨a, b, rfl⟩, hNe, hHash⟩)
        (fun c0 => ∃ h n, c0.target = .xmssNode i h n)
        (fun h n _ _ _ _ _ _ _ => ⟨h, n, rfl⟩)
        params.subtreeHeight 0
        (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight)
        _ _ _ _ _ _ w' hWkEx
    obtain ⟨h, n, hT⟩ := hTag
    dsimp only [projM] at hMem
    rw [hT] at hMem ⊢
    rw [← hWotsEq] at hMem
    exact List.mem_map.mpr ⟨(h, d', n, w'.forged), hMem, rfl⟩
  · split at hEx
    · injection hEx with hwEq
      subst hwEq
      apply List.mem_append_right
      rw [allWotsChainsWithCands_fst, ← recoverWotsEndpoints_eq]
      exact List.mem_cons_self
    · split at hEx
      · rename_i w' hChEx
        injection hEx with hwEq
        subst hwEq
        apply List.mem_append_right
        apply List.mem_cons_of_mem
        apply List.mem_append_left
        let projCh : ProdTcrWitness suite params sk log msgStar sigStar → Nat × Nat × List UInt8 :=
          fun c0 => match c0.target with
            | .chainStep _ r s => (r, s, c0.forged)
            | _ => (0, 0, c0.forged)
        have hMem := prodAllChainsExtract_mem_cands suite params sk (UInt32.ofNat i)
          (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
            2 ^ params.subtreeHeight))
          (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight)
          digF (sigStar.layerSigs.getD i ⟨0, [], []⟩).wotsChains
          (ProdTcrWitness suite params sk log msgStar sigStar)
          (fun r s x hr hs hNe hHash =>
            ⟨.chainStep i r s, _, ⟨hi, hr, hs⟩, ⟨x, rfl⟩, hNe, hHash⟩)
          projCh (fun _ _ _ _ _ _ _ => rfl) _ hTsw params.ell1 (Nat.le_refl _) w' hChEx
        have hTag : ∃ r s, w'.target = .chainStep i r s :=
          prodAllChainsExtract_inr_prop suite params sk (UInt32.ofNat i)
            (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
              2 ^ params.subtreeHeight))
            (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight)
            digF (sigStar.layerSigs.getD i ⟨0, [], []⟩).wotsChains
            (ProdTcrWitness suite params sk log msgStar sigStar)
            (fun r s x hr hs hNe hHash =>
              ⟨.chainStep i r s, _, ⟨hi, hr, hs⟩, ⟨x, rfl⟩, hNe, hHash⟩)
            (fun w0 => ∃ r s, w0.target = .chainStep i r s)
            (fun r s _ _ _ _ _ => ⟨r, s, rfl⟩) _ hTsw params.ell1 (Nat.le_refl _) w' hChEx
        obtain ⟨r, s, hT⟩ := hTag
        dsimp only [projCh] at hMem
        rw [hT] at hMem ⊢
        exact List.mem_map.mpr ⟨(r, s, w'.forged), hMem, rfl⟩
      · split at hEx
        · cases hEx
        · rename_i e he hPos _
          split at hEx
          · split at hEx
            · rename_i hPre
              exfalso
              simp only [ProdTargetIdx.input] at hPre
              rw [hPos] at hPre
              exact hDiff e he hPos (prodLayerPreimage_cur_inj hPre)
            · injection hEx with hwEq
              subst hwEq
              apply List.mem_append_left
              exact List.mem_map.mpr ⟨e, he, rfl⟩
          · cases hEx

private theorem prodHypertreeWalkExtract_mem_cands (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) (log : List (List UInt8 × PqHashSig))
    (msgStar : List UInt8) (sigStar : PqHashSig) (hw : params.w = 4 ∨ params.w = 16)
    (hPwf : params.productionWellFormed = true)
    (hLog : ∀ e ∈ log, ProdLogEntryOk suite params sk e)
    (hCons : ProdLogConsistent suite params sk log) :
    ∀ (sigs : List LayerXmssSig) (i : Nat) (cur : List UInt8) (hNe : sigs ≠ [])
      (hAlign : ∀ j, sigs.getD j ⟨0, [], []⟩ = sigStar.layerSigs.getD (i + j) ⟨0, [], []⟩)
      (hLenEq : i + sigs.length = params.numLayers)
      (hVer : verifyProductionHypertreeLayers suite params sk.pkSeed
        (derivePublicKey suite params sk).pkRoot sigStar.rRand i
        (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)) cur sigs =
        some (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1))
          (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (params.numLayers * params.subtreeHeight)))))
      (w : ProdTcrWitness suite params sk log msgStar sigStar),
      prodHypertreeWalkExtract suite params sk log msgStar sigStar hw hPwf hLog hCons
        sigs i cur hNe hAlign hLenEq hVer = .tcr w →
      (w.target, w.forged) ∈
        (hypertreeLayersWithCands suite params sk.pkSeed (derivePublicKey suite params sk).pkRoot
          sigStar.rRand log i (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)) cur sigs).2
  | [], _, _, hNe, _, _, _, _, _ => absurd rfl hNe
  | lsig :: rest, i, cur, _, hAlign, hLenEq, hVer, w, hEx => by
    have hLs : lsig = sigStar.layerSigs.getD i ⟨0, [], []⟩ := by
      have h := hAlign 0
      rw [List.getD_cons_zero, Nat.add_zero] at h
      exact h
    have hStep : sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight =
        sigStar.leafGlobalIdx / 2 ^ ((i + 1) * params.subtreeHeight) := by
      have h := div_pow_mul_pow_mul sigStar.leafGlobalIdx i 1 params.subtreeHeight
      rw [Nat.one_mul] at h
      exact h
    have hVerRaw := hVer
    rw [verifyProductionHypertreeLayers_cons] at hVerRaw
    dsimp only at hVerRaw
    cases hCtrB : decide (lsig.tswCtr < 2 ^ 32)
    · simp [hCtrB] at hVerRaw
    · simp only [hCtrB, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hVerRaw
      cases hExt : extractBaseWDigitsChecked params.w params.ell1
          (productionLayerDigest suite params sigStar.rRand sk.pkSeed
            (derivePublicKey suite params sk).pkRoot cur i
            (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
              2 ^ params.subtreeHeight))
            (UInt32.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) %
              2 ^ params.subtreeHeight)) lsig.tswCtr) with
      | none => rw [hExt] at hVerRaw; cases hVerRaw
      | some digits =>
        rw [hExt] at hVerRaw
        dsimp only at hVerRaw
        have hDg := (extractBaseWDigitsChecked_some hExt).symm
        cases hTswB : checkTargetSum params.w params.ell1 params.targetSum digits
        · simp [hTswB] at hVerRaw
        · simp only [hTswB, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hVerRaw
          by_cases hChLen : lsig.wotsChains.length = params.ell1
          · simp only [hChLen, ne_eq, not_true_eq_false, ↓reduceIte] at hVerRaw
            have hInv := verifyProductionHypertreeLayers_cons_inv suite params _ _ _ _ _ _ _ _ _ hVer
            unfold prodHypertreeWalkExtract at hEx
            dsimp only at hEx
            split at hEx
            · rename_i hNextW
              obtain ⟨_, _, _, hW0, _⟩ := hInv
              rw [hLs, hNextW] at hW0
              cases hW0
            · rename_i next hNextW
              cases hR : rest with
              | nil =>
                subst hR
                dsimp only at hEx
                split at hEx
                · cases hEx
                · split at hEx
                  · rename_i w' hLay
                    injection hEx with hwEq
                    subst hwEq
                    exact prodLayerExtract_mem_cands suite params sk log msgStar sigStar hw hPwf
                      hLog hCons i _ cur lsig [] hLs (of_decide_eq_true hCtrB) _ rfl
                      (by rw [← hLs]; exact hDg ▸ hExt) hChLen _ _ _ w' hLay
                  · cases hEx
              | cons r0 rs =>
                subst hR
                dsimp only at hEx
                split at hEx
                · rename_i w' hStepEq
                  injection hEx with hwEq
                  subst hwEq
                  have hUp : prodHypertreeWalkExtract suite params sk log msgStar sigStar hw hPwf
                      hLog hCons (r0 :: rs) (i + 1) next
                      (List.cons_ne_nil _ _)
                      (fun j => by
                        have h := hAlign (j + 1)
                        rw [List.getD_cons_succ] at h
                        rw [h, show i + (j + 1) = i + 1 + j by omega])
                      (by rw [← hLenEq]; simp only [List.length_cons]; omega)
                      (by
                        obtain ⟨_, _, n', hW, hR0⟩ := hInv
                        rw [hLs, hNextW] at hW
                        have hn : next = n' := Option.some.inj hW
                        rw [← hn, hStep] at hR0
                        exact hR0) = .tcr w' := by
                    split at hStepEq
                    · cases hStepEq
                    · injection hStepEq with h1
                      injection h1 with h2
                      subst h2
                      assumption
                    · cases hStepEq
                  have hSubMem := prodHypertreeWalkExtract_mem_cands suite params sk log msgStar
                    sigStar hw hPwf hLog hCons (r0 :: rs) (i + 1) next _ _ _ _ w' hUp
                  unfold hypertreeLayersWithCands
                  simp only [hCtrB, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                    ← productionLayerDigest_rawHash, hExt, hTswB, hChLen, ne_eq, not_true_eq_false]
                  have hWotsEq :
                      suite.rawHash (thPreimage tagThTl sk.pkSeed
                        ⟨UInt32.ofNat i,
                         UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
                           2 ^ params.subtreeHeight),
                         .wotsPk,
                         UInt32.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) %
                           2 ^ params.subtreeHeight), 0, 0⟩
                        (allWotsChainsWithCands suite params sk.pkSeed (UInt32.ofNat i)
                          (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
                            2 ^ params.subtreeHeight))
                          (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) %
                            2 ^ params.subtreeHeight)
                          digits lsig.wotsChains params.ell1).1) =
                      recoverWotsPkFromSig suite params sk.pkSeed (UInt32.ofNat i)
                        (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
                           2 ^ params.subtreeHeight))
                        (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) %
                          2 ^ params.subtreeHeight)
                        digits lsig.wotsChains := by
                    rw [allWotsChainsWithCands_fst, recoverWotsPkFromSig_eq,
                      recoverWotsEndpoints_eq, thTweakTl_eq, thCall_eq]
                  have hMw1 : (walkMerkleKpWithCands suite sk.pkSeed (UInt32.ofNat i)
                      (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
                        2 ^ params.subtreeHeight)) .tree 0 params.subtreeHeight 0 0 0
                      (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) %
                        2 ^ params.subtreeHeight)
                      (suite.rawHash (thPreimage tagThTl sk.pkSeed
                        ⟨UInt32.ofNat i,
                         UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
                           2 ^ params.subtreeHeight),
                         .wotsPk,
                         UInt32.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) %
                           2 ^ params.subtreeHeight), 0, 0⟩
                        (allWotsChainsWithCands suite params sk.pkSeed (UInt32.ofNat i)
                          (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
                            2 ^ params.subtreeHeight))
                          (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) %
                            2 ^ params.subtreeHeight)
                          digits lsig.wotsChains params.ell1).1))
                      lsig.authPath).1 = some next := by
                    rw [walkMerkleKpWithCands_fst, walkMerkleAuthPathKp_zero_eq, hWotsEq, ← hDg,
                      hLs]
                    exact hNextW
                  rw [hMw1, hStep]
                  exact List.mem_append_right _ hSubMem
                · cases hEx
                · split at hEx
                  · cases hEx
                  · split at hEx
                    · rename_i w' hLay
                      injection hEx with hwEq
                      subst hwEq
                      exact prodLayerExtract_mem_cands suite params sk log msgStar sigStar hw hPwf
                        hLog hCons i _ cur lsig (r0 :: rs) hLs (of_decide_eq_true hCtrB) _ rfl
                        (by rw [← hLs]; exact hDg ▸ hExt) hChLen _ _ _ w' hLay
                    · cases hEx
          · simp [hChLen] at hVerRaw

private theorem production_forgery_extract_false (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (queries : List ProdSigningQuery) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hw : params.w = 4 ∨ params.w = 16) (hSt : params.statefulJorts = false)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ queries → ∀ q', q' ∈ queries → q.epoch = q'.epoch → q = q')
    (hFresh : ∀ e ∈ productionSigningLog suite params sk queries, e.1 ≠ msgStar)
    (hAccept : verifyProductionPqHashSig suite params (derivePublicKey suite params sk) msgStar sigStar = true) :
    production_forgery_extract suite params sk queries msgStar sigStar hw hOneTime hFresh hAccept =
      production_stateless_forgery_extract suite params sk queries msgStar sigStar hw hSt hFresh hAccept := by
  unfold production_forgery_extract
  split
  · rfl
  · rename_i hTrue; rw [hSt] at hTrue; cases hTrue

private theorem production_forgery_extract_true (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (queries : List ProdSigningQuery) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hw : params.w = 4 ∨ params.w = 16) (hSt : params.statefulJorts = true)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ queries → ∀ q', q' ∈ queries → q.epoch = q'.epoch → q = q')
    (hFresh : ∀ e ∈ productionSigningLog suite params sk queries, e.1 ≠ msgStar)
    (hAccept : verifyProductionPqHashSig suite params (derivePublicKey suite params sk) msgStar sigStar = true) :
    production_forgery_extract suite params sk queries msgStar sigStar hw hOneTime hFresh hAccept =
      (match production_stateful_forgery_extract suite params sk queries msgStar sigStar hw hSt
          (hOneTime hSt) hFresh hAccept with
       | .inl w => .tcr w
       | .inr h => .pre h) := by
  unfold production_forgery_extract
  split
  · rename_i hFalse; rw [hSt] at hFalse; cases hFalse
  · rfl

/-- **Completeness of the Public Candidate Collector (`prodTcrOutput_mem_publicVerifierCands`):**
    Whenever `prodTcrOutput` extracts `(t, forged)` on outcome `o`, that exact pair appears in the
    public oracle candidate list `publicVerifierWithTcrCands` computed from `(pk, log, msgStar, sigStar)`
    without `sk.skSeed` or `sk.skPrf`. -/
theorem prodTcrOutput_mem_publicVerifierCands (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (o : ProdEufCmaOutcome)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q')
    (t : ProdTargetIdx) (forged : List UInt8)
    (hOut : prodTcrOutput suite params hw o hOneTime = some (t, forged)) :
    (t, forged) ∈
      (publicVerifierWithTcrCands suite params (derivePublicKey suite params o.sk)
        (productionSigningLog suite params o.sk o.queries) o.msgStar o.sigStar).2 := by
  by_cases hWin : prodEufCmaWin suite params o = true
  · have hOut' :
        (match production_forgery_extract suite params o.sk o.queries o.msgStar o.sigStar hw hOneTime
          (fun e he hEq => by
            unfold prodEufCmaWin at hWin
            rw [Bool.and_eq_true] at hWin
            exact of_decide_eq_true hWin.2 (List.mem_map.mpr ⟨e, he, hEq⟩))
          (by
            unfold prodEufCmaWin at hWin
            rw [Bool.and_eq_true] at hWin
            exact hWin.1) with
         | .tcr w => some (w.target, w.forged)
         | _ => none) = some (t, forged) := by
      have hBrk : prodOutcomeBreak suite params hw o hOneTime =
          some (production_forgery_extract suite params o.sk o.queries o.msgStar o.sigStar hw hOneTime
            (fun e he hEq => by
              unfold prodEufCmaWin at hWin
              rw [Bool.and_eq_true] at hWin
              exact of_decide_eq_true hWin.2 (List.mem_map.mpr ⟨e, he, hEq⟩))
            (by
              unfold prodEufCmaWin at hWin
              rw [Bool.and_eq_true] at hWin
              exact hWin.1)) := by
        unfold prodOutcomeBreak
        split
        · rfl
        · contradiction
      unfold prodTcrOutput at hOut
      rw [hBrk] at hOut
      generalize production_forgery_extract _ _ _ _ _ _ _ _ _ _ = brk at hOut ⊢
      cases brk <;> exact hOut
    clear hOut
    obtain ⟨wOut, hOut, rfl, rfl⟩ :
        ∃ w : ProdTcrWitness suite params o.sk
          (productionSigningLog suite params o.sk o.queries) o.msgStar o.sigStar,
          production_forgery_extract suite params o.sk o.queries o.msgStar o.sigStar hw hOneTime
            (fun e he hEq => by
              unfold prodEufCmaWin at hWin
              rw [Bool.and_eq_true] at hWin
              exact of_decide_eq_true hWin.2 (List.mem_map.mpr ⟨e, he, hEq⟩))
            (by
              unfold prodEufCmaWin at hWin
              rw [Bool.and_eq_true] at hWin
              exact hWin.1) = .tcr w ∧
          t = w.target ∧ forged = w.forged := by
      split at hOut'
      · rename_i w hEqW
        simp only [Option.some.injEq, Prod.mk.injEq] at hOut'
        exact ⟨w, hEqW, hOut'.1.symm, hOut'.2.symm⟩
      · cases hOut'
    clear hOut'
    have hAccept : verifyProductionPqHashSig suite params (derivePublicKey suite params o.sk)
        o.msgStar o.sigStar = true := by
      have hWin' := hWin
      unfold prodEufCmaWin at hWin'
      rw [Bool.and_eq_true] at hWin'
      exact hWin'.1
    have hAccRaw := hAccept
    rw [verifyProductionPqHashSig_eq] at hAccRaw
    unfold publicVerifierWithTcrCands
    cases hG1 : (!params.productionWellFormed || !params.productionLeafIdxInRange o.sigStar.leafGlobalIdx)
    · simp only [hG1, Bool.false_eq_true, ↓reduceIte] at hAccRaw ⊢
      cases hG2 : (decide (o.sigStar.layerSigs.length ≠ params.numLayers) || decide (o.sigStar.msgTswCtr ≠ 0))
      · have hNotGuard : ¬ (o.sigStar.layerSigs.length ≠ params.numLayers ∨ o.sigStar.msgTswCtr ≠ 0) := by
          intro hOr
          rcases hOr with h1 | h2
          · simp [h1] at hG2
          · simp [h2] at hG2
        have hL1 : o.sigStar.layerSigs.length = params.numLayers :=
          Decidable.of_not_not (fun h => hNotGuard (.inl h))
        have hL2 : o.sigStar.msgTswCtr = 0 :=
          Decidable.of_not_not (fun h => hNotGuard (.inr h))
        simp only [hL1, hL2, ne_eq, not_true_eq_false, decide_false, Bool.or_self,
          Bool.false_eq_true, ↓reduceIte] at hAccRaw ⊢
        by_cases hSt : params.statefulJorts = false
        · rw [production_forgery_extract_false _ _ _ _ _ _ _ hSt] at hOut
          simp only [hSt, Bool.false_eq_true, ↓reduceIte] at hAccRaw ⊢
          cases hOps : decide (o.sigStar.forsOpenings.length ≠ params.forsTrees)
          · have hOpsEq : o.sigStar.forsOpenings.length = params.forsTrees :=
              Decidable.of_not_not (of_decide_eq_false hOps)
            simp only [hOpsEq, not_true_eq_false, ↓reduceIte] at hAccRaw ⊢
            have hMu : suite.rawHash (thPreimage tagHPre o.sk.pkSeed zeroAdrs
                [(derivePublicKey suite params o.sk).pkRoot, o.msgStar]) =
                thPreHash suite o.sk.pkSeed (derivePublicKey suite params o.sk).pkRoot o.msgStar := rfl
            have hSeed : (derivePublicKey suite params o.sk).pkSeed = o.sk.pkSeed := rfl
            rw [hSeed, hMu]
            cases hD : deriveProductionStatelessInputs suite params o.sigStar.rRand o.sk.pkSeed
                (derivePublicKey suite params o.sk).pkRoot
                (thPreHash suite o.sk.pkSeed (derivePublicKey suite params o.sk).pkRoot o.msgStar) with
            | none => rw [hSeed, hD] at hAccRaw; cases hAccRaw
            | some pr =>
              rcases pr with ⟨derivedLeafIdx, idxs⟩
              rw [hSeed, hD] at hAccRaw
              dsimp only at hAccRaw ⊢
              by_cases hLeafNe : o.sigStar.leafGlobalIdx ≠ derivedLeafIdx
              · simp [hLeafNe] at hAccRaw
              · simp only [hLeafNe, ↓reduceIte] at hAccRaw ⊢
                have hFacts := prod_stateless_accept_facts suite params o.sk o.msgStar o.sigStar
                  hSt hAccept
                unfold production_stateless_forgery_extract at hOut
                dsimp only at hOut
                split at hOut
                · rename_i hFors
                  obtain ⟨_, _, _, _, _, _, hF0, _⟩ := hFacts
                  rw [hFors] at hF0
                  cases hF0
                · rename_i forsPkF hFors
                  have hIdxsEq : prodSigForsIdxs suite params (derivePublicKey suite params o.sk)
                      o.msgStar o.sigStar = idxs := by
                    unfold prodSigForsIdxs; rw [hSeed, hD]
                  have hForsIdxs : recoverProductionForsPk suite params o.sk.pkSeed
                      (UInt64.ofNat (o.sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight))
                      (o.sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight) idxs
                      o.sigStar.forsOpenings = some forsPkF := by
                    rw [← hIdxsEq]; exact hFors
                  have hInvF := prod_recoverForsPk_some_inv suite params o.sk.pkSeed _ _ idxs
                    o.sigStar.forsOpenings forsPkF hForsIdxs
                  obtain ⟨roots, hRoots, hFpkEq⟩ := hInvF
                  have hFr1 : (forsRootsWithCands suite params o.sk.pkSeed
                      (UInt64.ofNat (o.sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight))
                      (o.sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight) idxs
                      o.sigStar.forsOpenings 0 params.forsTrees).1 = some roots := by
                    rw [forsRootsWithCands_fst]; exact hRoots
                  rw [hFr1]
                  dsimp only
                  have hRawFpk : suite.rawHash (thPreimage tagThTl o.sk.pkSeed
                      ⟨0, UInt64.ofNat (o.sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight),
                       .forsRoots, UInt32.ofNat (o.sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight),
                       0, 0⟩ roots) = forsPkF := by
                    rw [← thCall_eq, ← thTweakTl_eq]; exact hFpkEq.symm
                  rw [hRawFpk]
                  split at hOut
                  · rename_i w' hHtEx
                    injection hOut with hwEq
                    subst hwEq
                    apply List.mem_append_right
                    apply List.mem_cons_of_mem
                    apply List.mem_append_right
                    have h0 : o.sigStar.leafGlobalIdx / 2 ^ (0 * params.subtreeHeight) =
                        o.sigStar.leafGlobalIdx := by
                      simp only [Nat.zero_mul, Nat.pow_zero, Nat.div_one]
                    have hMem := prodHypertreeWalkExtract_mem_cands suite params o.sk
                      (productionSigningLog suite params o.sk o.queries) o.msgStar o.sigStar hw
                      _ _ _ o.sigStar.layerSigs 0 forsPkF _ _ _ _ w' hHtEx
                    rw [h0] at hMem
                    exact hMem
                  · cases hOut
                  · rename_i e _ _ _ _
                    unfold prodForsExtract at hOut
                    dsimp only at hOut
                    have hRootsIdxs : recoverProductionForsTreeRoots suite params o.sk.pkSeed
                        (UInt64.ofNat (o.sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight))
                        (o.sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight)
                        (prodSigForsIdxs suite params (derivePublicKey suite params o.sk) o.msgStar
                          o.sigStar)
                        o.sigStar.forsOpenings 0 params.forsTrees = some roots := by
                      rw [hIdxsEq]; exact hRoots
                    split at hOut
                    · rename_i hRNone
                      rw [hRootsIdxs] at hRNone
                      cases hRNone
                    · rename_i rootsF hRSome
                      have hRootsEq : rootsF = roots :=
                        Option.some.inj (hRSome.symm.trans hRootsIdxs)
                      split at hOut
                      · injection hOut with hwEq
                        subst hwEq
                        rw [← hRootsEq]
                        apply List.mem_append_right
                        exact List.mem_cons_self
                      · split at hOut
                        · rename_i w' hFrEx
                          injection hOut with hwEq
                          subst hwEq
                          apply List.mem_append_right
                          apply List.mem_cons_of_mem
                          apply List.mem_append_left
                          rw [← hIdxsEq]
                          exact prodForsRootsExtract_mem_cands suite params o.sk _ o.msgStar o.sigStar
                            hSt _ _ _ _ _ _ (fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl) params.forsTrees 0
                            rootsF _ hRSome _ w' hFrEx
                        · split at hOut <;> cases hOut
          · have hOpsNe : o.sigStar.forsOpenings.length ≠ params.forsTrees := of_decide_eq_true hOps
            simp [hOpsNe] at hAccRaw
        · have hStT : params.statefulJorts = true := Bool.not_eq_false _ |>.mp hSt
          clear hSt
          have hSt := hStT
          clear hStT
          rw [production_forgery_extract_true _ _ _ _ _ _ _ hSt] at hOut
          simp only [hSt, ↓reduceIte] at hAccRaw ⊢
          cases hEmp : (!o.sigStar.forsOpenings.isEmpty)
          · simp only [Bool.false_eq_true, ↓reduceIte] at hAccRaw ⊢
            have hSeed : (derivePublicKey suite params o.sk).pkSeed = o.sk.pkSeed := rfl
            have hMu : suite.rawHash (thPreimage tagHPre o.sk.pkSeed zeroAdrs
                [(derivePublicKey suite params o.sk).pkRoot, o.msgStar]) =
                thPreHash suite o.sk.pkSeed (derivePublicKey suite params o.sk).pkRoot o.msgStar := rfl
            rw [hSeed, hMu]
            split at hOut
            · rename_i w0 hStEx
              injection hOut with hwEq0
              subst hwEq0
              unfold production_stateful_forgery_extract at hStEx
              dsimp only at hStEx
              split at hStEx
              · rename_i w' hHtEx
                injection hStEx with hwEq
                subst hwEq
                apply List.mem_append_right
                have h0 : o.sigStar.leafGlobalIdx / 2 ^ (0 * params.subtreeHeight) =
                    o.sigStar.leafGlobalIdx := by
                  simp only [Nat.zero_mul, Nat.pow_zero, Nat.div_one]
                have hMem := prodHypertreeWalkExtract_mem_cands suite params o.sk
                  (productionSigningLog suite params o.sk o.queries) o.msgStar o.sigStar hw
                  _ _ _ o.sigStar.layerSigs 0 _ _ _ _ _ w' hHtEx
                rw [h0] at hMem
                exact hMem
              · cases hStEx
              · rename_i e he _ _ _
                split at hStEx
                · rename_i hArgs _
                  exfalso
                  have hFresh : ∀ e' ∈ productionSigningLog suite params o.sk o.queries,
                      e'.1 ≠ o.msgStar := by
                    intro e' he' hEq'
                    unfold prodEufCmaWin at hWin
                    rw [Bool.and_eq_true] at hWin
                    exact of_decide_eq_true hWin.2 (List.mem_map.mpr ⟨e', he', hEq'⟩)
                  simp only [List.cons.injEq, and_true] at hArgs
                  exact hFresh e he hArgs.2.symm
                · injection hStEx with hwEq
                  subst hwEq
                  apply List.mem_append_left
                  exact List.mem_map.mpr ⟨e, he, rfl⟩
            · cases hOut
          · simp [hEmp] at hAccRaw
      · simp only [Bool.or_eq_true, decide_eq_true_eq] at hG2
        rcases hG2 with h1 | h2
        · simp [h1] at hAccRaw
        · simp [h2] at hAccRaw
    · simp [hG1] at hAccRaw
  · have hBrk : prodOutcomeBreak suite params hw o hOneTime = none := by
      unfold prodOutcomeBreak
      split
      · contradiction
      · rfl
    unfold prodTcrOutput at hOut
    rw [hBrk] at hOut
    cases hOut

/-! ## 5. Explicit `Within` Challenger Games (`PRF`, `SM_DT_UD`, `ITSR`, `SM_DT_TCR`, `SM_DT_PRE`) -/

/-- One multi-hybrid coin bundling the real public hash suite, PRF-idealized suite,
    UD-idealized suite, and challenger secret key. -/
structure ProdExperimentCoin where
  pubSuite : TweakableHashSuite
  prfSuite : TweakableHashSuite
  udSuite  : TweakableHashSuite
  sk       : PqSecretKey

/-- Construct an explicit PRF-idealized `TweakableHashSuite` overriding keyed `tagPrf` / `tagPrfMsg`
    calls with `prfRand` (padded/truncated to 32 bytes) while agreeing identically with `pubSuite`
    on all public hash calls. -/
def isKeyedPrfPreimage (sk : PqSecretKey) (x : List UInt8) : Bool :=
  let pfxPrf := leb128 4 ++ encodeListField tagPrf ++ encodeListField sk.pkSeed
  let sfxPrf := encodeListField sk.skSeed
  let pfxMsg := leb128 6 ++ encodeListField tagPrfMsg ++ encodeListField [] ++
    encodeListField (encodeAdrs zeroAdrs) ++ encodeListField sk.skPrf
  (decide (x.length = pfxPrf.length + 33 + sfxPrf.length) &&
   decide (x.take pfxPrf.length = pfxPrf) &&
   decide (x.drop (pfxPrf.length + 33) = sfxPrf)) ||
  decide (x.take pfxMsg.length = pfxMsg)

def padHash32 (bs : List UInt8) : List UInt8 :=
  (bs.take 32) ++ List.replicate (32 - (bs.take 32).length) 0

theorem padHash32_length (bs : List UInt8) : (padHash32 bs).length = 32 := by
  unfold padHash32
  rw [List.length_append, List.length_replicate]
  have hLe : (bs.take 32).length ≤ 32 := List.length_take_le 32 bs
  omega

def mkKeyedPrfIdealSuite (pubSuite : TweakableHashSuite) (sk : PqSecretKey)
    (prfRand : List UInt8 → List UInt8) : TweakableHashSuite where
  suiteId := pubSuite.suiteId
  rawHash x := if isKeyedPrfPreimage sk x then padHash32 (prfRand x) else pubSuite.rawHash x
  rawHash_len x := by
    split
    · exact padHash32_length _
    · exact pubSuite.rawHash_len x

/-- EUF-CMA challenger game against `(suite, params, sk)` for a seed-withheld adversary `A`. -/
def eufCmaWithinWin (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (A : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig)) : Bool :=
  let pk := derivePublicKey suite params sk
  let r := runHashSignAdv suite params sk [] (A pk)
  prodEufCmaWin suite params ⟨sk, r.2, r.1.1, r.1.2⟩

def eufCmaRealWithinWins (coins : List ProdExperimentCoin) (params : PqHashParams)
    (A : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig)) : Nat :=
  hitCount (fun ω => eufCmaWithinWin ω.pubSuite params ω.sk A) coins

/-- Replaying a message obtained from a signing query loses `eufCmaWithinWin`. -/
theorem tooth_replayed_query_loses_eufCmaWithin (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) (q : ProdSigningQuery) (sig : PqHashSig)
    (hSign : prodSignQuery suite params sk q = some sig) :
    eufCmaWithinWin suite params sk
      (fun _ => .querySign q (fun resp => .done (q.message, resp.getD sig))) = false := by
  unfold eufCmaWithinWin runHashSignAdv challengerSignStep
  have hNoConf : challengerEpochConflict params [] q = false := by
    simp [challengerEpochConflict]
  rw [hNoConf]
  dsimp only [Bool.false_eq_true, ↓reduceIte, runHashSignAdv]
  apply prodEufCmaWin_rejects_signed_message suite params _ sig
  simp [productionSigningLog, hSign]

/-! ### Game 1 & Game 2: `PRF` and `SM_DT_UD` `Within` Challenger Games & Reductions -/

def prfWithinGameBit (ω : ProdExperimentCoin) (params : PqHashParams) (b : Bool)
    (D : PqPublicKey → HashSignAdv Bool) : Bool :=
  let suite := if b then ω.pubSuite else ω.prfSuite
  (runHashSignAdv suite params ω.sk [] (D (derivePublicKey suite params ω.sk))).1

def prfWithinAdv (coins : List ProdExperimentCoin) (params : PqHashParams)
    (D : PqPublicKey → HashSignAdv Bool) : Nat :=
  natAbsDiff
    (hitCount (fun ω => prfWithinGameBit ω params true D) coins)
    (hitCount (fun ω => prfWithinGameBit ω params false D) coins)

def smDtUdWithinGameBit (ω : ProdExperimentCoin) (params : PqHashParams) (b : Bool)
    (D : PqPublicKey → HashSignAdv Bool) : Bool :=
  let suite := if b then ω.prfSuite else ω.udSuite
  (runHashSignAdv suite params ω.sk [] (D (derivePublicKey suite params ω.sk))).1

def smDtUdWithinAdv (coins : List ProdExperimentCoin) (params : PqHashParams)
    (D : PqPublicKey → HashSignAdv Bool) : Nat :=
  natAbsDiff
    (hitCount (fun ω => smDtUdWithinGameBit ω params true D) coins)
    (hitCount (fun ω => smDtUdWithinGameBit ω params false D) coins)

/-- Seed-withheld distinguisher computing the exact EUF-CMA win bit via public oracle queries. -/
def eufCmaDistinguisherAdv (params : PqHashParams)
    (A : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig)) (pk : PqPublicKey) :
    HashSignAdv Bool :=
  (advTrackSignLog [] (A pk)).bind fun outLog =>
    let msgStar := outLog.1.1
    let sigStar := outLog.1.2
    let advLog := outLog.2
    (advVerifyProductionPqHashSig params pk msgStar sigStar).map fun verBit =>
      verBit && decide (msgStar ∉ advLog.map Prod.fst)

def prfExtractorAdv (params : PqHashParams)
    (A : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig)) :
    PqPublicKey → HashSignAdv Bool :=
  eufCmaDistinguisherAdv params A

def udExtractorAdv (params : PqHashParams)
    (A : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig)) :
    PqPublicKey → HashSignAdv Bool :=
  eufCmaDistinguisherAdv params A

theorem eufCmaDistinguisherAdv_within (params : PqHashParams) {qh qs : Nat}
    (A : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig))
    (hW : ∀ pk, (A pk).Within qh qs) (pk : PqPublicKey) :
    (eufCmaDistinguisherAdv params A pk).Within (qh + prodVerifierHashBudget params) qs := by
  unfold eufCmaDistinguisherAdv
  have h1 := advTrackSignLog_within [] (hW pk)
  have h2 : ∀ outLog : (List UInt8 × PqHashSig) × List (List UInt8 × PqHashSig),
      ((advVerifyProductionPqHashSig params pk outLog.1.1 outLog.1.2).map
        (fun verBit => verBit && decide (outLog.1.1 ∉ outLog.2.map Prod.fst))).Within
        (prodVerifierHashBudget params) 0 :=
    fun outLog => HashSignAdv.Within.map _ (advVerifyProductionPqHashSig_within params pk _ _)
  simpa only [Nat.add_zero] using HashSignAdv.Within.bind h1 h2

theorem eufCmaDistinguisherAdv_simulates (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (A : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig)) :
    (runHashSignAdv suite params sk []
      (eufCmaDistinguisherAdv params A (derivePublicKey suite params sk))).1 =
    eufCmaWithinWin suite params sk A := by
  unfold eufCmaDistinguisherAdv eufCmaWithinWin HashSignAdv.map
  rw [runHashSignAdv_bind, runHashSignAdv_advTrackSignLog suite params sk [] [] _ rfl]
  dsimp only
  rw [runHashSignAdv_bind, runHashSignAdv_advVerifyProductionPqHashSig]
  rfl

/-! ### Game 3: `ITSR` `Within` Challenger Game & Reduction -/

def itsrChallengerCheck (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (qs : List ProdSigningQuery) (msgStar : List UInt8) (sigStar : PqHashSig) : Bool :=
  let pk := derivePublicKey suite params sk
  let log := productionSigningLog suite params sk qs
  decide (0 < params.forsTrees) &&
  decide (msgStar ∉ log.map Prod.fst) &&
  (prodSigForsLeaves suite params pk msgStar sigStar).all
    (fun a => decide (a ∈ prodLogForsLeaves suite params pk log))

def itsrWithinWin (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (B : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig)) : Bool :=
  let r := runHashSignAdv suite params sk [] (B (derivePublicKey suite params sk))
  itsrChallengerCheck suite params sk r.2 r.1.1 r.1.2

def itsrWithinWins (coins : List ProdExperimentCoin) (params : PqHashParams)
    (B : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig)) : Nat :=
  hitCount (fun ω => itsrWithinWin ω.udSuite params ω.sk B) coins

def itsrExtractorAdv (A : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig)) :
    PqPublicKey → HashSignAdv (List UInt8 × PqHashSig) := A

theorem itsrWithinWin_sound (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (B : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig))
    (hWin : itsrWithinWin suite params sk B = true) :
    let r := runHashSignAdv suite params sk [] (B (derivePublicKey suite params sk))
    ProdForsItsrBreak suite params (derivePublicKey suite params sk)
      (productionSigningLog suite params sk r.2) r.1.1 r.1.2 := by
  unfold itsrWithinWin itsrChallengerCheck at hWin
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hWin
  exact ⟨fun e he hEq => hWin.1.2 (List.mem_map.mpr ⟨e, he, hEq⟩), hWin.1.1, hWin.2⟩

theorem prodItsrEvent_implies_itsrWithinWin (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (sk : PqSecretKey)
    (A : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig))
    (hEv :
      let r := runHashSignAdv suite params sk [] (A (derivePublicKey suite params sk))
      prodItsrEvent suite params hw ⟨sk, r.2, r.1.1, r.1.2⟩
        (runHashSignAdv_queries_oneTime suite params sk (A (derivePublicKey suite params sk))) =
          true) :
    itsrWithinWin suite params sk (itsrExtractorAdv A) = true := by
  let m := A (derivePublicKey suite params sk)
  have hBrk := prodItsrEvent_sound suite params hw
    ⟨sk, (runHashSignAdv suite params sk [] m).2,
      (runHashSignAdv suite params sk [] m).1.1, (runHashSignAdv suite params sk [] m).1.2⟩
    (runHashSignAdv_queries_oneTime suite params sk m) hEv
  unfold itsrWithinWin itsrExtractorAdv itsrChallengerCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨hBrk.trees_pos, ?_⟩, hBrk.covered⟩
  intro hMem
  obtain ⟨e, he, hEq⟩ := List.mem_map.mp hMem
  exact hBrk.fresh e he hEq

/-! ### Game 4: `SM_DT_TCR` `Within` Challenger Game & Indexed Reduction Discharging `ProdSmTcrBreak` -/

/-- Submission to the multi-target `SM_DT_TCR` challenger: leaf index, FORS leaf tuple, indexed
    target on that path, and colliding input. -/
structure SmDtTcrSubmission where
  leaf     : Nat
  forsIdxs : List Nat
  target   : ProdTargetIdx
  forged   : List UInt8

/-- Target-validity check ensuring `sub.target.input` is a genuine `ProdHonestHashTarget`. -/
def smDtTcrValidTarget (params : PqHashParams) (log : List (List UInt8 × PqHashSig)) :
    ProdTargetIdx → Bool
  | .signedDigest e i => decide (e ∈ log) && decide (i < params.numLayers)
  | .preHash e => decide (e ∈ log)
  | _ => true

def smDtTcrChallengerCheck (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (qs : List ProdSigningQuery) (subOpt : Option SmDtTcrSubmission) : Bool :=
  match subOpt with
  | none => false
  | some sub =>
    let log := productionSigningLog suite params sk qs
    decide (sub.target ∈ prodPathTargets params log sub.leaf sub.forsIdxs) &&
    smDtTcrValidTarget params log sub.target &&
    prodTcrCheck suite params sk sub.leaf sub.target sub.forged

def smDtTcrWithinWin (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (B : PqPublicKey → HashSignAdv (Option SmDtTcrSubmission)) : Bool :=
  let r := runHashSignAdv suite params sk [] (B (derivePublicKey suite params sk))
  smDtTcrChallengerCheck suite params sk r.2 r.1

def smDtTcrWithinWins (coins : List ProdExperimentCoin) (params : PqHashParams)
    (B : PqPublicKey → HashSignAdv (Option SmDtTcrSubmission)) : Nat :=
  hitCount (fun ω => smDtTcrWithinWin ω.udSuite params ω.sk B) coins

/-- **Discharging `ProdSmTcrBreak` (`smDtTcrWithinWin_discharges_prodSmTcrBreak`):**
    Any win in the query-bounded, seed-withheld `SM_DT_TCR` challenger game constructively yields
    `ProdSmTcrBreak` against the challenger's secret key and signing transcript. -/
theorem smDtTcrWithinWin_discharges_prodSmTcrBreak (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey)
    (B : PqPublicKey → HashSignAdv (Option SmDtTcrSubmission))
    (hWin : smDtTcrWithinWin suite params sk B = true) :
    ProdSmTcrBreak suite params sk
      (productionSigningLog suite params sk
        (runHashSignAdv suite params sk [] (B (derivePublicKey suite params sk))).2) := by
  unfold smDtTcrWithinWin smDtTcrChallengerCheck at hWin
  dsimp only at hWin
  cases hOut : (runHashSignAdv suite params sk [] (B (derivePublicKey suite params sk))).1 with
  | none => rw [hOut] at hWin; cases hWin
  | some sub =>
    rw [hOut] at hWin
    simp only [Bool.and_eq_true, prodTcrCheck, decide_eq_true_eq] at hWin
    obtain ⟨⟨_, hVal⟩, hNe, hCol⟩ := hWin
    have hHon : ProdHonestHashTarget suite params sk
        (productionSigningLog suite params sk
          (runHashSignAdv suite params sk [] (B (derivePublicKey suite params sk))).2)
        (sub.target.input suite params sk sub.leaf) := by
      cases ht : sub.target with
      | xmssNode l h n => exact .xmssNode (UInt32.ofNat l) _ h n
      | wotsPk l => exact .wotsPk (UInt32.ofNat l) _ _
      | chainStep l r s => exact .chainStep (UInt32.ofNat l) _ _ r s
      | forsNode j h d b => exact .forsNode _ _ j h (j * 2 ^ d + b) b
      | forsRoots => exact .forsRoots _ _
      | signedDigest e i =>
        rw [ht] at hVal
        simp only [smDtTcrValidTarget, Bool.and_eq_true, decide_eq_true_eq] at hVal
        exact .signedDigest e hVal.1 i hVal.2
      | preHash e =>
        rw [ht] at hVal
        simp only [smDtTcrValidTarget, decide_eq_true_eq] at hVal
        exact .preHash e hVal
    exact ProdSmTcrBreak.mk _ sub.forged hHon hNe hCol

/-- `#tooth`: Submitting the target preimage itself (`forged = target.input`) is rejected by
    `smDtTcrChallengerCheck`, even though its hash collides trivially. -/
theorem tooth_identical_input_rejected_by_smDtTcr (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) (qs : List ProdSigningQuery)
    (leaf : Nat) (idxs : List Nat) (t : ProdTargetIdx) :
    smDtTcrChallengerCheck suite params sk qs
      (some ⟨leaf, idxs, t, t.input suite params sk leaf⟩) = false := by
  simp [smDtTcrChallengerCheck, prodTcrCheck]

/-- Public oracle helper computing `prodSigForsIdxs` + `publicVerifierWithTcrCands` within
    `1 + prodXofHashBudget params + prodVerifierHashBudget params` hash queries (`0` `sk` access). -/
def advCollectTcrSubmissions (params : PqHashParams) (pk : PqPublicKey)
    (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8) (sigStar : PqHashSig) :
    HashSignAdv (List SmDtTcrSubmission) :=
  let preHashInput := thPreimage tagHPre pk.pkSeed zeroAdrs [pk.pkRoot, msgStar]
  (advRawHash preHashInput).bind fun mu =>
    (advDeriveProductionStatelessInputs params sigStar.rRand pk.pkSeed pk.pkRoot mu).bind fun dOpt =>
      let idxs := match dOpt with | some (_, is) => is | none => []
      (advVerifyWithTcrCands params pk log msgStar sigStar).map fun vc =>
        vc.2.map fun tf => ⟨sigStar.leafGlobalIdx, idxs, tf.1, tf.2⟩

/-- Explicit seed-withheld `SM_DT_TCR` reduction adversary selecting candidate index `slot`. -/
def tcrExtractorAdv (params : PqHashParams) (slot : Nat)
    (A : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig)) (pk : PqPublicKey) :
    HashSignAdv (Option SmDtTcrSubmission) :=
  (advTrackSignLog [] (A pk)).bind fun outLog =>
    (advCollectTcrSubmissions params pk outLog.2 outLog.1.1 outLog.1.2).map fun subs =>
      subs[slot]?

def prodTcrReductionHashBudget (params : PqHashParams) : Nat :=
  1 + prodXofHashBudget params + prodVerifierHashBudget params

private theorem productionSigningLog_length_le_queries (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) :
    ∀ qs : List ProdSigningQuery, (productionSigningLog suite params sk qs).length ≤ qs.length
  | [] => Nat.le_refl 0
  | q :: rest => by
    unfold productionSigningLog
    have ih := productionSigningLog_length_le_queries suite params sk rest
    cases prodSignQuery suite params sk q <;> simp <;> omega

theorem tcrExtractorAdv_within (params : PqHashParams) (slot : Nat) {qh qs : Nat}
    (A : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig))
    (hW : ∀ pk, (A pk).Within qh qs) (pk : PqPublicKey) :
    (tcrExtractorAdv params slot A pk).Within (qh + prodTcrReductionHashBudget params) qs := by
  unfold tcrExtractorAdv advCollectTcrSubmissions prodTcrReductionHashBudget
  have h1 := advTrackSignLog_within [] (hW pk)
  refine HashSignAdv.Within.bind_le
    (qh₂ := 1 + prodXofHashBudget params + prodVerifierHashBudget params) (qs₂ := 0)
    h1 (fun outLog => ?_) (by omega) (by omega)
  refine HashSignAdv.Within.map _ ?_
  refine HashSignAdv.Within.bind_le
    (qh₂ := prodXofHashBudget params + prodVerifierHashBudget params) (qs₂ := 0)
    (advRawHash_within _) (fun mu => ?_) (by omega) (by omega)
  refine HashSignAdv.Within.bind_le (qh₂ := prodVerifierHashBudget params) (qs₂ := 0)
    (advDeriveProductionStatelessInputs_within params _ _ _ mu)
    (fun _ => HashSignAdv.Within.map _ (advVerifyWithTcrCands_within params pk _ _ _))
    (by omega) (by omega)

theorem prodTcrEvent_captured_by_slot (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) {qh qs_max : Nat} (sk : PqSecretKey)
    (A : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig))
    (hW : ∀ pk, (A pk).Within qh qs_max)
    (hEv :
      let r := runHashSignAdv suite params sk [] (A (derivePublicKey suite params sk))
      prodTcrEvent suite params hw ⟨sk, r.2, r.1.1, r.1.2⟩
        (runHashSignAdv_queries_oneTime suite params sk (A (derivePublicKey suite params sk))) =
          true) :
    ∃ slot : Fin (prodPathTargetCount params qs_max),
      smDtTcrWithinWin suite params sk (tcrExtractorAdv params slot.val A) = true := by
  let pk := derivePublicKey suite params sk
  let r := runHashSignAdv suite params sk [] (A pk)
  let hOT := runHashSignAdv_queries_oneTime suite params sk (A pk)
  change prodTcrEvent suite params hw ⟨sk, r.2, r.1.1, r.1.2⟩ hOT = true at hEv
  unfold prodTcrEvent at hEv
  cases hOut : prodTcrOutput suite params hw ⟨sk, r.2, r.1.1, r.1.2⟩ hOT with
  | none => rw [hOut] at hEv; cases hEv
  | some tf =>
    rcases tf with ⟨t, forged⟩
    obtain ⟨_, hOn, _, hChk⟩ := prodTcrOutput_sound suite params hw
      ⟨sk, r.2, r.1.1, r.1.2⟩ hOT t forged hOut
    have hMem := prodTcrOutput_mem_publicVerifierCands suite params hw
      ⟨sk, r.2, r.1.1, r.1.2⟩ hOT t forged hOut
    let cands := (publicVerifierWithTcrCands suite params pk
      (productionSigningLog suite params sk r.2) r.1.1 r.1.2).2
    change (t, forged) ∈ cands at hMem
    obtain ⟨idx, hIdxLt, hIdxEq⟩ := List.mem_iff_getElem.mp hMem
    have hLogLe : (productionSigningLog suite params sk r.2).length ≤ qs_max := by
      have h1 := productionSigningLog_length_le_queries suite params sk r.2
      have h2 := runHashSignAdv_queries_length_le suite params sk [] (A pk) (hW pk)
      simp only [List.length_nil, Nat.zero_add] at h2
      exact Nat.le_trans h1 h2
    have hCandsLe : cands.length ≤ prodPathTargetCount params qs_max :=
      Nat.le_trans (publicVerifierWithTcrCands_cands_length_le suite params pk _ r.1.1 r.1.2)
        (prodPathTargetCount_mono params hLogLe)
    have hSlotLt : idx < prodPathTargetCount params qs_max := Nat.lt_of_lt_of_le hIdxLt hCandsLe
    refine ⟨⟨idx, hSlotLt⟩, ?_⟩
    unfold smDtTcrWithinWin tcrExtractorAdv advCollectTcrSubmissions HashSignAdv.map
    rw [runHashSignAdv_bind, runHashSignAdv_advTrackSignLog suite params sk [] [] _ rfl]
    dsimp only
    rw [runHashSignAdv_bind]
    dsimp only [HashSignAdv.bind]
    rw [runHashSignAdv_bind]
    dsimp only [advRawHash, runHashSignAdv]
    rw [runHashSignAdv_bind, runHashSignAdv_advDeriveProductionStatelessInputs]
    dsimp only
    rw [runHashSignAdv_bind, runHashSignAdv_advVerifyWithTcrCands]
    dsimp only [runHashSignAdv, smDtTcrChallengerCheck]
    have hIdxsEq : (match deriveProductionStatelessInputs suite params r.1.2.rRand pk.pkSeed
        pk.pkRoot (suite.rawHash (thPreimage tagHPre pk.pkSeed zeroAdrs [pk.pkRoot, r.1.1])) with
        | some (_, is) => is | none => []) =
        prodSigForsIdxs suite params pk r.1.1 r.1.2 := rfl
    rw [hIdxsEq, List.getElem?_map, List.getElem?_eq_getElem hIdxLt, Option.map_some, hIdxEq]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨ProdTargetIdx.mem_pathTargets params _ _ _ t hOn, ?_⟩, hChk⟩
    cases t with
    | signedDigest e i =>
      simp only [smDtTcrValidTarget, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hOn.1, hOn.2.1⟩
    | preHash e =>
      simp only [smDtTcrValidTarget, decide_eq_true_eq]
      exact hOn.1
    | _ => rfl

/-! ### Game 5: `SM_DT_PRE` `Within` Challenger Game & Indexed Reduction -/

inductive SmDtPreSubmission : Type where
  | forsLeaf (leaf j u : Nat) (secretVal : List UInt8)
  | wotsStep (leaf i r step : Nat) (chainVal : List UInt8)
  deriving DecidableEq, Repr

def smDtPreChallengerCheck (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (qs : List ProdSigningQuery) (subOpt : Option SmDtPreSubmission) : Bool :=
  let pk := derivePublicKey suite params sk
  let log := productionSigningLog suite params sk qs
  match subOpt with
  | none => false
  | some (.forsLeaf leaf j u secretVal) =>
    decide (j < params.forsTrees) &&
    decide ((leaf, j, u) ∉ prodLogForsLeaves suite params pk log) &&
    decide (forsIndexedLeafHash suite sk.pkSeed (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight))
      (leaf % 2 ^ params.subtreeHeight) j u secretVal =
      forsIndexedLeafFn suite sk (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight))
        (leaf % 2 ^ params.subtreeHeight) j u)
  | some (.wotsStep leaf i r step chainVal) =>
    let tree := UInt64.ofNat (leaf / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight)
    let kp := leaf / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight
    decide (i < params.numLayers) &&
    decide (r < params.ell1) &&
    decide (step + 1 ≤ params.w - 1) &&
    decide (thChainF suite sk.pkSeed
      ⟨UInt32.ofNat i, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat step⟩
      chainVal = honestChainNode suite sk (UInt32.ofNat i) tree kp r (step + 1)) &&
    log.all (fun e =>
      decide (e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) =
        leaf / 2 ^ (i * params.subtreeHeight) →
        step < (prodLogLayerDigits suite params sk e i).getD r 0))

def smDtPreWithinWin (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (B : PqPublicKey → HashSignAdv (Option SmDtPreSubmission)) : Bool :=
  let r := runHashSignAdv suite params sk [] (B (derivePublicKey suite params sk))
  smDtPreChallengerCheck suite params sk r.2 r.1

def smDtPreWithinWins (coins : List ProdExperimentCoin) (params : PqHashParams)
    (B : PqPublicKey → HashSignAdv (Option SmDtPreSubmission)) : Nat :=
  hitCount (fun ω => smDtPreWithinWin ω.udSuite params ω.sk B) coins

def publicSigPreCandidates (params : PqHashParams) (idxs : List Nat) (sig : PqHashSig) :
    List SmDtPreSubmission :=
  ((List.range params.forsTrees).map fun j =>
    SmDtPreSubmission.forsLeaf sig.leafGlobalIdx j (idxs.getD j 0)
      (sig.forsOpenings.getD j ⟨[], []⟩).secretVal) ++
  ((List.range params.numLayers).flatMap fun i =>
    (List.range params.ell1).flatMap fun r =>
      (List.range (params.w - 1)).map fun step =>
        SmDtPreSubmission.wotsStep sig.leafGlobalIdx i r step
          ((sig.layerSigs.getD i ⟨0, [], []⟩).wotsChains.getD r []))

theorem publicSigPreCandidates_length (params : PqHashParams) (idxs : List Nat) (sig : PqHashSig) :
    (publicSigPreCandidates params idxs sig).length = prodPreCandidateCount params := by
  unfold publicSigPreCandidates prodPreCandidateCount
  simp only [List.length_append, List.length_map, List.length_range,
    prod_length_range_flatMap_flatMap_map]

def advCollectPreSubmissions (params : PqHashParams) (pk : PqPublicKey)
    (msgStar : List UInt8) (sigStar : PqHashSig) :
    HashSignAdv (List SmDtPreSubmission) :=
  let preHashInput := thPreimage tagHPre pk.pkSeed zeroAdrs [pk.pkRoot, msgStar]
  (advRawHash preHashInput).bind fun mu =>
    (advDeriveProductionStatelessInputs params sigStar.rRand pk.pkSeed pk.pkRoot mu).map fun dOpt =>
      let idxs := match dOpt with | some (_, is) => is | none => []
      publicSigPreCandidates params idxs sigStar

def preExtractorAdv (params : PqHashParams) (slot : Nat)
    (A : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig)) (pk : PqPublicKey) :
    HashSignAdv (Option SmDtPreSubmission) :=
  (A pk).bind fun msgSig =>
    (advCollectPreSubmissions params pk msgSig.1 msgSig.2).map fun subs =>
      subs[slot]?

theorem preExtractorAdv_within (params : PqHashParams) (slot : Nat) {qh qs : Nat}
    (A : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig))
    (hW : ∀ pk, (A pk).Within qh qs) (pk : PqPublicKey) :
    (preExtractorAdv params slot A pk).Within (qh + (1 + prodXofHashBudget params)) qs := by
  unfold preExtractorAdv advCollectPreSubmissions
  refine HashSignAdv.Within.bind_le (qh₂ := 1 + prodXofHashBudget params) (qs₂ := 0)
    (hW pk) (fun _ => ?_) (by omega) (by omega)
  refine HashSignAdv.Within.map _ ?_
  refine HashSignAdv.Within.bind_le (qh₂ := prodXofHashBudget params) (qs₂ := 0)
    (advRawHash_within _)
    (fun mu => HashSignAdv.Within.map _ (advDeriveProductionStatelessInputs_within params _ _ _ mu))
    (by omega) (by omega)

theorem prodPreEvent_captured_by_slot (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (sk : PqSecretKey)
    (A : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig))
    (hEv :
      let r := runHashSignAdv suite params sk [] (A (derivePublicKey suite params sk))
      prodPreEvent suite params hw ⟨sk, r.2, r.1.1, r.1.2⟩
        (runHashSignAdv_queries_oneTime suite params sk (A (derivePublicKey suite params sk))) =
          true) :
    ∃ slot : Fin (prodPreCandidateCount params),
      smDtPreWithinWin suite params sk (preExtractorAdv params slot.val A) = true := by
  let pk := derivePublicKey suite params sk
  let r := runHashSignAdv suite params sk [] (A pk)
  have hBrk := prodPreEvent_sound suite params hw ⟨sk, r.2, r.1.1, r.1.2⟩
    (runHashSignAdv_queries_oneTime suite params sk (A pk)) hEv
  let idxs := prodSigForsIdxs suite params pk r.1.1 r.1.2
  have hCand : ∃ sub ∈ publicSigPreCandidates params idxs r.1.2,
      smDtPreChallengerCheck suite params sk r.2 (some sub) = true := by
    cases hBrk with
    | fors j hj hUn hInv =>
      refine ⟨.forsLeaf r.1.2.leafGlobalIdx j (idxs.getD j 0)
        (r.1.2.forsOpenings.getD j ⟨[], []⟩).secretVal, ?_, ?_⟩
      · unfold publicSigPreCandidates
        exact List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
      · simp only [smDtPreChallengerCheck, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hj, hUn⟩, hInv⟩
    | wots i hi rIdx hr step hstep hInv hUn =>
      refine ⟨.wotsStep r.1.2.leafGlobalIdx i rIdx step
        ((r.1.2.layerSigs.getD i ⟨0, [], []⟩).wotsChains.getD rIdx []), ?_, ?_⟩
      · unfold publicSigPreCandidates
        apply List.mem_append_right
        exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi,
          List.mem_flatMap.mpr ⟨rIdx, List.mem_range.mpr hr,
            List.mem_map.mpr ⟨step, List.mem_range.mpr hstep, rfl⟩⟩⟩
      · simp only [smDtPreChallengerCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
        exact ⟨⟨⟨⟨hi, hr⟩, hstep⟩, hInv⟩, hUn⟩
  obtain ⟨sub, hMem, hChk⟩ := hCand
  obtain ⟨idx, hIdxLt, hIdxEq⟩ := List.mem_iff_getElem.mp hMem
  have hSlotLt : idx < prodPreCandidateCount params := by
    rw [← publicSigPreCandidates_length params idxs r.1.2]; exact hIdxLt
  refine ⟨⟨idx, hSlotLt⟩, ?_⟩
  unfold smDtPreWithinWin preExtractorAdv advCollectPreSubmissions HashSignAdv.map
  rw [runHashSignAdv_bind]
  dsimp only [HashSignAdv.bind]
  rw [runHashSignAdv_bind]
  dsimp only [advRawHash, runHashSignAdv]
  rw [runHashSignAdv_bind, runHashSignAdv_bind, runHashSignAdv_advDeriveProductionStatelessInputs]
  dsimp only [runHashSignAdv]
  have hIdxsEq : (match deriveProductionStatelessInputs suite params r.1.2.rRand pk.pkSeed
      pk.pkRoot (suite.rawHash (thPreimage tagHPre pk.pkSeed zeroAdrs [pk.pkRoot, r.1.1])) with
      | some (_, is) => is | none => []) = idxs := rfl
  rw [hIdxsEq, List.getElem?_eq_getElem hIdxLt, hIdxEq]
  exact hChk

/-! ## 6. Constructive Argmax & Main Concrete Advantage Sum Inequality -/

/-- Constructive argmax over `Fin n` (`0 Classical.choice`). -/
def bestFinIdx : (n : Nat) → 0 < n → (Fin n → Nat) → Fin n
  | 0, hPos, _ => absurd hPos (Nat.lt_irrefl 0)
  | 1, _, _ => ⟨0, Nat.zero_lt_one⟩
  | n + 2, _, score =>
    let tailBest := bestFinIdx (n + 1) (Nat.succ_pos n)
      (fun i => score ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    let cand : Fin (n + 2) := ⟨tailBest.1 + 1, Nat.succ_lt_succ tailBest.2⟩
    if score cand ≤ score ⟨0, Nat.succ_pos (n + 1)⟩ then
      ⟨0, Nat.succ_pos (n + 1)⟩
    else cand

theorem bestFinIdx_ge : ∀ (n : Nat) (hPos : 0 < n) (score : Fin n → Nat) (i : Fin n),
    score i ≤ score (bestFinIdx n hPos score)
  | 0, hPos, _, _ => absurd hPos (Nat.lt_irrefl 0)
  | 1, _, _, ⟨0, _⟩ => Nat.le_refl _
  | 1, _, _, ⟨_ + 1, hi⟩ => absurd hi (by omega)
  | n + 2, _, score, ⟨0, _⟩ => by
    simp only [bestFinIdx]
    split <;> omega
  | n + 2, _, score, ⟨k + 1, hk⟩ => by
    have ih := bestFinIdx_ge (n + 1) (Nat.succ_pos n)
      (fun j => score ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩) ⟨k, Nat.lt_of_succ_lt_succ hk⟩
    simp only [bestFinIdx] at ih ⊢
    split
    · rename_i hLe
      exact Nat.le_trans ih hLe
    · exact ih

theorem finSum_le_mul_bestFinIdx (n : Nat) (hPos : 0 < n) (score : Fin n → Nat) :
    finSum n score ≤ n * score (bestFinIdx n hPos score) := by
  have hLe : finSum n score ≤ finSum n (fun _ => score (bestFinIdx n hPos score)) :=
    finSum_le_finSum (bestFinIdx_ge n hPos score)
  rw [finSum_const] at hLe
  exact hLe

private theorem hitCount_eq_zero_of_all_false {Ω : Type} (ev : Ω → Bool)
    (hFalse : ∀ ω, ev ω = false) : ∀ coins : List Ω, hitCount ev coins = 0
  | [] => rfl
  | ω :: rest => by
    simp [hitCount, hFalse ω, hitCount_eq_zero_of_all_false ev hFalse rest]

private theorem hitCount_covered_by_fin {Ω : Type} (n : Nat) (ev : Ω → Bool)
    (slotEv : Fin n → Ω → Bool)
    (hCov : ∀ ω, ev ω = true → ∃ k : Fin n, slotEv k ω = true) :
    ∀ coins : List Ω, hitCount ev coins ≤ finSum n (fun k => hitCount (slotEv k) coins)
  | [] => by
    have h0 : finSum n (fun k => hitCount (slotEv k) ([] : List Ω)) = finSum n (fun _ => 0) :=
      finSum_congr (fun _ => rfl)
    rw [h0, finSum_const]
    simp [hitCount]
  | ω :: rest => by
    have ih := hitCount_covered_by_fin n ev slotEv hCov rest
    have hSplit :
        finSum n (fun k => hitCount (slotEv k) (ω :: rest)) =
        finSum n (fun k => if slotEv k ω = true then 1 else 0) +
        finSum n (fun k => hitCount (slotEv k) rest) := by
      rw [← finSum_add]
      apply finSum_congr
      intro k
      simp only [hitCount]
    rw [hSplit]
    have hHead : hitCount ev (ω :: rest) =
        (if ev ω = true then 1 else 0) + hitCount ev rest := rfl
    rw [hHead]
    cases hE : ev ω
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      omega
    · obtain ⟨k₀, hk₀⟩ := hCov ω hE
      have hOne : 1 ≤ finSum n (fun k => if slotEv k ω = true then 1 else 0) := by
        have hInd := finSum_eq_indicator n k₀
        have hLe := finSum_le_finSum (n := n)
          (f := fun k => if k = k₀ then 1 else 0)
          (g := fun k => if slotEv k ω = true then 1 else 0)
          (fun k => by
            by_cases hk : k = k₀
            · subst hk; simp [hk₀]
            · simp [hk])
        omega
      simp only [↓reduceIte]
      omega

/-- Constructive best TCR slot (`0 Classical.choice`). `prodPathTargetCount` has `+ 1`, so `0 < M`. -/
def bestTcrExtractorAdv (coins : List ProdExperimentCoin) (params : PqHashParams)
    (qs_max : Nat) (A : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig)) :
    PqPublicKey → HashSignAdv (Option SmDtTcrSubmission) :=
  let M := prodPathTargetCount params qs_max
  have hPos : 0 < M := by unfold M prodPathTargetCount; omega
  let best := bestFinIdx M hPos (fun k => smDtTcrWithinWins coins params (tcrExtractorAdv params k.val A))
  tcrExtractorAdv params best.val A

/-- Constructive best PRE slot (`0 Classical.choice`), defaulting to slot `0` when `M = 0`. -/
def bestPreExtractorAdv (coins : List ProdExperimentCoin) (params : PqHashParams)
    (A : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig)) :
    PqPublicKey → HashSignAdv (Option SmDtPreSubmission) :=
  let M := prodPreCandidateCount params
  if hPos : 0 < M then
    let best := bestFinIdx M hPos (fun k => smDtPreWithinWins coins params (preExtractorAdv params k.val A))
    preExtractorAdv params best.val A
  else
    preExtractorAdv params 0 A

theorem bestTcrExtractorAdv_within (coins : List ProdExperimentCoin) (params : PqHashParams)
    {qh qs_max : Nat} (A : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig))
    (hW : ∀ pk, (A pk).Within qh qs_max) (pk : PqPublicKey) :
    (bestTcrExtractorAdv coins params qs_max A pk).Within
      (qh + prodTcrReductionHashBudget params) qs_max :=
  tcrExtractorAdv_within params _ A hW pk

theorem bestPreExtractorAdv_within (coins : List ProdExperimentCoin) (params : PqHashParams)
    {qh qs_max : Nat} (A : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig))
    (hW : ∀ pk, (A pk).Within qh qs_max) (pk : PqPublicKey) :
    (bestPreExtractorAdv coins params A pk).Within
      (qh + (1 + prodXofHashBudget params)) qs_max := by
  unfold bestPreExtractorAdv
  split <;> exact preExtractorAdv_within params _ A hW pk

private theorem hitCount_congr {Ω : Type} {p q : Ω → Bool} (h : ∀ ω, p ω = q ω) :
    ∀ xs : List Ω, hitCount p xs = hitCount q xs
  | [] => rfl
  | ω :: rest => by
    simp only [hitCount, h ω, hitCount_congr h rest]

private theorem hitCount_le_of_imp {Ω : Type} {p q : Ω → Bool}
    (h : ∀ ω, p ω = true → q ω = true) :
    ∀ xs : List Ω, hitCount p xs ≤ hitCount q xs
  | [] => Nat.le_refl 0
  | ω :: rest => by
    have ih := hitCount_le_of_imp h rest
    simp only [hitCount]
    by_cases hp : p ω = true
    · simp only [hp, h ω hp, ↓reduceIte]
      omega
    · have hpF : p ω = false := Bool.eq_false_iff.mpr hp
      simp only [hpF, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      exact Nat.le_trans ih (Nat.le_add_left _ _)

/-- **Master Seed-Withheld `Within` Hash-Signature Game Reduction Bound
    (`production_euf_cma_within_game_reduction_bound`):**
    For any EUF-CMA forger `A` making at most `qh` hash queries and `qs_max` signing queries with
    `sk.skSeed` and `sk.skPrf` withheld, the concrete EUF-CMA win count is bounded by the explicit
    `PRF`, `SM_DT_UD`, `ITSR`, `SM_DT_TCR`, and `SM_DT_PRE` `Within`-bounded reduction games. -/
theorem production_euf_cma_within_game_reduction_bound
    (coins : List ProdExperimentCoin) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) {qh qs_max : Nat}
    (A : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig))
    (hW : ∀ pk, (A pk).Within qh qs_max) :
    eufCmaRealWithinWins coins params A ≤
      prfWithinAdv coins params (prfExtractorAdv params A) +
      smDtUdWithinAdv coins params (udExtractorAdv params A) +
      itsrWithinWins coins params (itsrExtractorAdv A) +
      prodPathTargetCount params qs_max *
        smDtTcrWithinWins coins params (bestTcrExtractorAdv coins params qs_max A) +
      prodPreCandidateCount params *
        smDtPreWithinWins coins params (bestPreExtractorAdv coins params A) := by
  have hHopPrf :
      eufCmaRealWithinWins coins params A ≤
      prfWithinAdv coins params (prfExtractorAdv params A) +
      hitCount (fun ω => eufCmaWithinWin ω.prfSuite params ω.sk A) coins := by
    unfold eufCmaRealWithinWins prfWithinAdv prfWithinGameBit prfExtractorAdv
    have hT := hitCount_congr
      (fun ω : ProdExperimentCoin => eufCmaDistinguisherAdv_simulates ω.pubSuite params ω.sk A) coins
    have hF := hitCount_congr
      (fun ω : ProdExperimentCoin => eufCmaDistinguisherAdv_simulates ω.prfSuite params ω.sk A) coins
    simp only [↓reduceIte, Bool.false_eq_true]
    rw [hT, hF]
    unfold natAbsDiff
    split <;> omega
  have hHopUd :
      hitCount (fun ω => eufCmaWithinWin ω.prfSuite params ω.sk A) coins ≤
      smDtUdWithinAdv coins params (udExtractorAdv params A) +
      hitCount (fun ω => eufCmaWithinWin ω.udSuite params ω.sk A) coins := by
    unfold smDtUdWithinAdv smDtUdWithinGameBit udExtractorAdv
    have hT := hitCount_congr
      (fun ω : ProdExperimentCoin => eufCmaDistinguisherAdv_simulates ω.prfSuite params ω.sk A) coins
    have hF := hitCount_congr
      (fun ω : ProdExperimentCoin => eufCmaDistinguisherAdv_simulates ω.udSuite params ω.sk A) coins
    simp only [↓reduceIte, Bool.false_eq_true]
    rw [hT, hF]
    unfold natAbsDiff
    split <;> omega
  let outUd := fun ω : ProdExperimentCoin =>
    let r := runHashSignAdv ω.udSuite params ω.sk [] (A (derivePublicKey ω.udSuite params ω.sk))
    (⟨ω.sk, r.2, r.1.1, r.1.2⟩ : ProdEufCmaOutcome)
  let hOTUd := fun ω : ProdExperimentCoin =>
    runHashSignAdv_queries_oneTime ω.udSuite params ω.sk
      (A (derivePublicKey ω.udSuite params ω.sk))
  have hTerm :
      hitCount (fun ω => eufCmaWithinWin ω.udSuite params ω.sk A) coins ≤
      hitCount (fun ω => prodItsrEvent ω.udSuite params hw (outUd ω) (hOTUd ω)) coins +
      hitCount (fun ω => prodTcrEvent ω.udSuite params hw (outUd ω) (hOTUd ω)) coins +
      hitCount (fun ω => prodPreEvent ω.udSuite params hw (outUd ω) (hOTUd ω)) coins := by
    apply hitCount_union_bound
    intro ω hWin
    exact prodEufCmaWin_classified ω.udSuite params hw (outUd ω) (hOTUd ω) hWin
  have hItsrLe :
      hitCount (fun ω => prodItsrEvent ω.udSuite params hw (outUd ω) (hOTUd ω)) coins ≤
      itsrWithinWins coins params (itsrExtractorAdv A) :=
    hitCount_le_of_imp
      (fun ω hEv => prodItsrEvent_implies_itsrWithinWin ω.udSuite params hw ω.sk A hEv) coins
  have hTcrPos : 0 < prodPathTargetCount params qs_max := by unfold prodPathTargetCount; omega
  have hTcrLe :
      hitCount (fun ω => prodTcrEvent ω.udSuite params hw (outUd ω) (hOTUd ω)) coins ≤
      prodPathTargetCount params qs_max *
        smDtTcrWithinWins coins params (bestTcrExtractorAdv coins params qs_max A) := by
    have hCov := hitCount_covered_by_fin (prodPathTargetCount params qs_max)
      (fun ω => prodTcrEvent ω.udSuite params hw (outUd ω) (hOTUd ω))
      (fun k ω => smDtTcrWithinWin ω.udSuite params ω.sk (tcrExtractorAdv params k.val A))
      (fun ω hEv => prodTcrEvent_captured_by_slot ω.udSuite params hw ω.sk A hW hEv)
      coins
    have hBest := finSum_le_mul_bestFinIdx (prodPathTargetCount params qs_max) hTcrPos
      (fun k => smDtTcrWithinWins coins params (tcrExtractorAdv params k.val A))
    unfold bestTcrExtractorAdv smDtTcrWithinWins at hBest ⊢
    exact Nat.le_trans hCov hBest
  have hPreLe :
      hitCount (fun ω => prodPreEvent ω.udSuite params hw (outUd ω) (hOTUd ω)) coins ≤
      prodPreCandidateCount params *
        smDtPreWithinWins coins params (bestPreExtractorAdv coins params A) := by
    by_cases hPrePos : 0 < prodPreCandidateCount params
    · have hCov := hitCount_covered_by_fin (prodPreCandidateCount params)
        (fun ω => prodPreEvent ω.udSuite params hw (outUd ω) (hOTUd ω))
        (fun k ω => smDtPreWithinWin ω.udSuite params ω.sk (preExtractorAdv params k.val A))
        (fun ω hEv => prodPreEvent_captured_by_slot ω.udSuite params hw ω.sk A hEv)
        coins
      have hBest := finSum_le_mul_bestFinIdx (prodPreCandidateCount params) hPrePos
        (fun k => smDtPreWithinWins coins params (preExtractorAdv params k.val A))
      unfold bestPreExtractorAdv smDtPreWithinWins at hBest ⊢
      simp only [hPrePos]
      exact Nat.le_trans hCov hBest
    · have hZero : prodPreCandidateCount params = 0 := by omega
      have hNoEv : ∀ ω, prodPreEvent ω.udSuite params hw (outUd ω) (hOTUd ω) = false := by
        intro ω
        by_cases hEv : prodPreEvent ω.udSuite params hw (outUd ω) (hOTUd ω) = true
        · obtain ⟨slot, _⟩ := prodPreEvent_captured_by_slot ω.udSuite params hw ω.sk A hEv
          have hLt := slot.isLt
          omega
        · exact Bool.eq_false_iff.mpr hEv
      have hCnt0 : hitCount (fun ω => prodPreEvent ω.udSuite params hw (outUd ω) (hOTUd ω)) coins = 0 :=
        hitCount_eq_zero_of_all_false _ hNoEv coins
      rw [hCnt0]
      exact Nat.zero_le _
  omega

/-! ## 7. Two-Sided Nonvacuity (`0 < wins ∧ wins < totalCoins`) & Assurance Witnesses -/

/-- All-zero 32-byte suite: base-4 digit sum is `0 ≠ 192`, so `prodToyForgery` is rejected at layer 0. -/
def zeroRejectToySuite : TweakableHashSuite where
  suiteId := []
  rawHash := fun _ => List.replicate 32 0x00
  rawHash_len := fun _ => List.length_replicate

theorem prodToyForgery_rejected_by_zeroSuite :
    verifyProductionPqHashSig zeroRejectToySuite prodToyStatefulParams
      (derivePublicKey zeroRejectToySuite prodToyStatefulParams ⟨[], [], []⟩)
      [] prodToyForgery = false := by
  decide +kernel

theorem prodToyForgery_zeroSuite_cands_nil :
    (publicVerifierWithTcrCands zeroRejectToySuite prodToyStatefulParams
      (derivePublicKey zeroRejectToySuite prodToyStatefulParams ⟨[], [], []⟩)
      [] [] prodToyForgery).2 = [] := by
  decide +kernel

def prodToyForgerAdv : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig) :=
  fun _ => .done ([], prodToyForgery)

theorem prodToyForgerAdv_within (pk : PqPublicKey) : (prodToyForgerAdv pk).Within 0 0 := trivial

def prodToyAcceptCoin : ProdExperimentCoin :=
  ⟨crumbToySuite, crumbToySuite, crumbToySuite, ⟨[], [], []⟩⟩

def prodToyRejectCoin : ProdExperimentCoin :=
  ⟨zeroRejectToySuite, zeroRejectToySuite, zeroRejectToySuite, ⟨[], [], []⟩⟩

/-- Concrete 8-coin ensemble (`3` accepting coins + `5` rejecting coins). -/
def prodToyGameCoins : List ProdExperimentCoin :=
  [prodToyAcceptCoin, prodToyAcceptCoin, prodToyAcceptCoin,
   prodToyRejectCoin, prodToyRejectCoin, prodToyRejectCoin, prodToyRejectCoin, prodToyRejectCoin]

/-- **Two-Sided Nonvacuity (`0 < wins ∧ wins < totalCoins`):**
    On `prodToyGameCoins` (`totalCoins = 8`), `eufCmaRealWithinWins = 3` (`0 < 3 < 8`) and the
    constructed seed-withheld reduction `bestTcrExtractorAdv` achieves `0 < smDtTcrWithinWins` and
    `smDtTcrWithinWins < 8`. -/
theorem prodToyGameCoins_two_sided_nonvacuous :
    0 < eufCmaRealWithinWins prodToyGameCoins prodToyStatefulParams prodToyForgerAdv ∧
    eufCmaRealWithinWins prodToyGameCoins prodToyStatefulParams prodToyForgerAdv <
      prodToyGameCoins.length ∧
    0 < smDtTcrWithinWins prodToyGameCoins prodToyStatefulParams
      (bestTcrExtractorAdv prodToyGameCoins prodToyStatefulParams 0 prodToyForgerAdv) ∧
    smDtTcrWithinWins prodToyGameCoins prodToyStatefulParams
      (bestTcrExtractorAdv prodToyGameCoins prodToyStatefulParams 0 prodToyForgerAdv) <
      prodToyGameCoins.length := by
  have hAccWin : eufCmaWithinWin crumbToySuite prodToyStatefulParams ⟨[], [], []⟩
      prodToyForgerAdv = true := by
    unfold eufCmaWithinWin prodToyForgerAdv runHashSignAdv prodEufCmaWin productionSigningLog
    dsimp only
    rw [prodToyForgery_accepted]
    rfl
  have hRejLose : eufCmaWithinWin zeroRejectToySuite prodToyStatefulParams ⟨[], [], []⟩
      prodToyForgerAdv = false := by
    unfold eufCmaWithinWin prodToyForgerAdv runHashSignAdv prodEufCmaWin
    dsimp only
    rw [prodToyForgery_rejected_by_zeroSuite]
    rfl
  have hRealCount :
      eufCmaRealWithinWins prodToyGameCoins prodToyStatefulParams prodToyForgerAdv = 3 := by
    simp [eufCmaRealWithinWins, prodToyGameCoins, prodToyAcceptCoin, prodToyRejectCoin,
      hitCount, hAccWin, hRejLose]
  let B_tcr := bestTcrExtractorAdv prodToyGameCoins prodToyStatefulParams 0 prodToyForgerAdv
  have hToyTcrEv :
      (let r := runHashSignAdv crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ []
        (prodToyForgerAdv (derivePublicKey crumbToySuite prodToyStatefulParams ⟨[], [], []⟩))
      prodTcrEvent crumbToySuite prodToyStatefulParams prodToyRadix ⟨⟨[], [], []⟩, r.2, r.1.1, r.1.2⟩
        (runHashSignAdv_queries_oneTime crumbToySuite prodToyStatefulParams ⟨[], [], []⟩
          (prodToyForgerAdv (derivePublicKey crumbToySuite prodToyStatefulParams ⟨[], [], []⟩)))) =
        true := by
    have hEqEv :
        (let r := runHashSignAdv crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ []
          (prodToyForgerAdv (derivePublicKey crumbToySuite prodToyStatefulParams ⟨[], [], []⟩))
        prodTcrEvent crumbToySuite prodToyStatefulParams prodToyRadix ⟨⟨[], [], []⟩, r.2, r.1.1, r.1.2⟩
          (runHashSignAdv_queries_oneTime crumbToySuite prodToyStatefulParams ⟨[], [], []⟩
            (prodToyForgerAdv (derivePublicKey crumbToySuite prodToyStatefulParams ⟨[], [], []⟩)))) =
        prodTcrEvent crumbToySuite prodToyStatefulParams prodToyRadix
          ⟨⟨[], [], []⟩, [], [], prodToyForgery⟩ prodToyOneTime := rfl
    rw [hEqEv]
    unfold prodTcrEvent
    cases hOut : prodTcrOutput crumbToySuite prodToyStatefulParams prodToyRadix
        ⟨⟨[], [], []⟩, [], [], prodToyForgery⟩ prodToyOneTime with
    | none =>
      have hc := prodToyForgery_returns_collision
      rw [hOut] at hc; cases hc
    | some p =>
      exact (prodTcrOutput_sound crumbToySuite prodToyStatefulParams prodToyRadix
        ⟨⟨[], [], []⟩, [], [], prodToyForgery⟩ prodToyOneTime p.1 p.2 hOut).2.2.2
  have hTcrPos : 0 < smDtTcrWithinWins prodToyGameCoins prodToyStatefulParams B_tcr := by
    obtain ⟨slot, hSlotWin⟩ := prodTcrEvent_captured_by_slot crumbToySuite prodToyStatefulParams
      prodToyRadix (qh := 0) (qs_max := 0) ⟨[], [], []⟩ prodToyForgerAdv prodToyForgerAdv_within
      hToyTcrEv
    have hSlotGe1 : 1 ≤ smDtTcrWithinWins prodToyGameCoins prodToyStatefulParams
        (tcrExtractorAdv prodToyStatefulParams slot.val prodToyForgerAdv) := by
      unfold smDtTcrWithinWins prodToyGameCoins prodToyAcceptCoin hitCount
      dsimp only
      simp only [hSlotWin, ↓reduceIte]
      omega
    have hBestGe := bestFinIdx_ge (prodPathTargetCount prodToyStatefulParams 0)
      (by unfold prodPathTargetCount; omega)
      (fun k => smDtTcrWithinWins prodToyGameCoins prodToyStatefulParams
        (tcrExtractorAdv prodToyStatefulParams k.val prodToyForgerAdv)) slot
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_trans hSlotGe1 hBestGe)
  have hRejTcrFalse : ∀ slot : Nat,
      smDtTcrWithinWin zeroRejectToySuite prodToyStatefulParams ⟨[], [], []⟩
        (tcrExtractorAdv prodToyStatefulParams slot prodToyForgerAdv) = false := by
    intro slot
    unfold smDtTcrWithinWin tcrExtractorAdv advCollectTcrSubmissions HashSignAdv.map
    rw [runHashSignAdv_bind, runHashSignAdv_advTrackSignLog zeroRejectToySuite
      prodToyStatefulParams ⟨[], [], []⟩ [] [] _ rfl]
    dsimp only [prodToyForgerAdv, runHashSignAdv, productionSigningLog]
    rw [runHashSignAdv_bind]
    dsimp only [HashSignAdv.bind]
    rw [runHashSignAdv_bind]
    dsimp only [advRawHash, runHashSignAdv]
    rw [runHashSignAdv_bind, runHashSignAdv_advDeriveProductionStatelessInputs]
    dsimp only
    rw [runHashSignAdv_bind, runHashSignAdv_advVerifyWithTcrCands]
    dsimp only [runHashSignAdv]
    rw [prodToyForgery_zeroSuite_cands_nil]
    simp [smDtTcrChallengerCheck]
  have hTcrLt : smDtTcrWithinWins prodToyGameCoins prodToyStatefulParams B_tcr <
      prodToyGameCoins.length := by
    have hB : smDtTcrWithinWin zeroRejectToySuite prodToyStatefulParams ⟨[], [], []⟩ B_tcr =
        false := by
      unfold B_tcr bestTcrExtractorAdv
      exact hRejTcrFalse _
    cases hC : smDtTcrWithinWin crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ B_tcr
    · simp only [smDtTcrWithinWins, prodToyGameCoins, prodToyAcceptCoin, prodToyRejectCoin,
        hitCount, hB, hC, Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_nil]
      omega
    · simp only [smDtTcrWithinWins, prodToyGameCoins, prodToyAcceptCoin, prodToyRejectCoin,
        hitCount, hB, hC, Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_nil]
      omega
  rw [hRealCount]
  exact ⟨by decide, by decide, hTcrPos, hTcrLt⟩

theorem witness_within_game_reduction :
    ∃ (_coins : List ProdExperimentCoin) (params : PqHashParams) (qh qs_max : Nat)
      (A : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig)),
      (params.w = 4 ∨ params.w = 16) ∧
      (∀ pk, (A pk).Within qh qs_max) :=
  ⟨prodToyGameCoins, prodToyStatefulParams, 0, 0, prodToyForgerAdv, prodToyRadix,
    prodToyForgerAdv_within⟩

theorem witness_smDtTcr_discharges_break :
    ∃ (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
      (B : PqPublicKey → HashSignAdv (Option SmDtTcrSubmission)),
      smDtTcrWithinWin suite params sk B = true := by
  have hToyTcrEv :
      (let r := runHashSignAdv crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ []
        (prodToyForgerAdv (derivePublicKey crumbToySuite prodToyStatefulParams ⟨[], [], []⟩))
      prodTcrEvent crumbToySuite prodToyStatefulParams prodToyRadix ⟨⟨[], [], []⟩, r.2, r.1.1, r.1.2⟩
        (runHashSignAdv_queries_oneTime crumbToySuite prodToyStatefulParams ⟨[], [], []⟩
          (prodToyForgerAdv (derivePublicKey crumbToySuite prodToyStatefulParams ⟨[], [], []⟩)))) =
        true := by
    have hEqEv :
        (let r := runHashSignAdv crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ []
          (prodToyForgerAdv (derivePublicKey crumbToySuite prodToyStatefulParams ⟨[], [], []⟩))
        prodTcrEvent crumbToySuite prodToyStatefulParams prodToyRadix ⟨⟨[], [], []⟩, r.2, r.1.1, r.1.2⟩
          (runHashSignAdv_queries_oneTime crumbToySuite prodToyStatefulParams ⟨[], [], []⟩
            (prodToyForgerAdv (derivePublicKey crumbToySuite prodToyStatefulParams ⟨[], [], []⟩)))) =
        prodTcrEvent crumbToySuite prodToyStatefulParams prodToyRadix
          ⟨⟨[], [], []⟩, [], [], prodToyForgery⟩ prodToyOneTime := rfl
    rw [hEqEv]
    unfold prodTcrEvent
    cases hOut : prodTcrOutput crumbToySuite prodToyStatefulParams prodToyRadix
        ⟨⟨[], [], []⟩, [], [], prodToyForgery⟩ prodToyOneTime with
    | none =>
      have hc := prodToyForgery_returns_collision
      rw [hOut] at hc; cases hc
    | some p =>
      exact (prodTcrOutput_sound crumbToySuite prodToyStatefulParams prodToyRadix
        ⟨⟨[], [], []⟩, [], [], prodToyForgery⟩ prodToyOneTime p.1 p.2 hOut).2.2.2
  obtain ⟨slot, hSlotWin⟩ := prodTcrEvent_captured_by_slot crumbToySuite prodToyStatefulParams
    prodToyRadix (qh := 0) (qs_max := 0) ⟨[], [], []⟩ prodToyForgerAdv prodToyForgerAdv_within
    hToyTcrEv
  exact ⟨crumbToySuite, prodToyStatefulParams, ⟨[], [], []⟩,
    tcrExtractorAdv prodToyStatefulParams slot.val prodToyForgerAdv, hSlotWin⟩

end Qsag
end

#verify_constructive Qsag.runHashSignAdv_seed_withheld
#verify_constructive Qsag.runHashSignAdv_queries_oneTime
#verify_constructive Qsag.runHashSignAdv_advVerifyProductionPqHashSig
#verify_constructive Qsag.prodTcrOutput_mem_publicVerifierCands
#verify_constructive Qsag.smDtTcrWithinWin_discharges_prodSmTcrBreak
#verify_constructive Qsag.production_euf_cma_within_game_reduction_bound
#verify_constructive Qsag.prodToyGameCoins_two_sided_nonvacuous
#tooth_pair Qsag.production_euf_cma_within_game_reduction_bound vs Qsag.tooth_replayed_query_loses_eufCmaWithin
#tooth_pair Qsag.smDtTcrWithinWin_discharges_prodSmTcrBreak vs Qsag.tooth_identical_input_rejected_by_smDtTcr
#verify_inhabited Qsag.production_euf_cma_within_game_reduction_bound Qsag.witness_within_game_reduction
#verify_inhabited Qsag.smDtTcrWithinWin_discharges_prodSmTcrBreak Qsag.witness_smDtTcr_discharges_break

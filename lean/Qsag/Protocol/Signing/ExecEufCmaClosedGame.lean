module
/-
# Qsag.Protocol.Signing.ExecEufCmaClosedGame — closed adaptive EUF-CMA experiment with an epoch latch

`production_euf_cma_gameBound` (`Top/Signing`) bounds the forger over an arbitrary outcome
function `Fin n → ProdEufCmaOutcome` and takes the one-time property of the signing log as a
hypothesis. Here the experiment is closed:

* `evalLatchedAdaptiveTree`: runs a seed-withheld adaptive adversary (`ProdAdaptiveTree`) against
  the raw hash and the executable signer `prodSignQuery`, behind a signing oracle that keeps a
  monotonic epoch latch. A request whose epoch is below the latch is refused (answer `none`, no
  log entry); an admitted request moves the latch to `epoch + 1` whether or not signing succeeds.
* `evalLatchedAdaptiveTree_oneTime`: the log of the latched oracle has strictly increasing
  epochs, hence is one-time. This is the fact `prodEufCmaWin_classified` needs.
* `prodSignQuery_verifies`: a signature returned by `prodSignQuery` is accepted by
  `verifyProductionPqHashSig` under the derived public key.
* `ExecEufCmaGame`: the `FinGame n` whose sample point selects the key (`keygen ω`) and the
  adversary (`adv ω`), and whose win predicate is `prodEufCmaWin`: the executable verifier
  `verifyProductionPqHashSig` accepts and the message was not answered by the signer.
* `execEufCmaItsrReduction`, `execEufCmaTcrReduction`, `execEufCmaPreReduction`: the reduction
  games, whose win predicates are the extractor-defined events on the same run.
* `jorts_baggy_closed_euf_cma`: `Pr[ExecEufCmaGame] ≤ Pr[R_itsr] + (Pr[R_tcr] + Pr[R_pre])`.
* `ExecEufCmaReductionEmbedding`: the obligation that links the three extractor events to the
  `ITSR`, `SM-DT-TCR` and `SM-DT-PRE` experiments of a `Spec.HashSigAssumptions` bundle: every
  coin on which an extractor event fires is a winning coin of the corresponding experiment.
  It is a hypothesis; no instance is constructed in this module.
* `jorts_baggy_closed_euf_cma_assumption_bound`: under such an embedding the experiment is
  bounded by `εItsr + εTcr + εPre`.
* `jorts_baggy_closed_euf_cma_keygen_hop`: a key-generation game hop. With a
  `KeyedPrfAssumption` whose real and ideal PRF games have the win predicates of the experiment
  under two key generators, the real experiment is bounded by the three reductions of the ideal
  one plus `εPrf`.

The hop replaces the key generator only. The signer's internal use of `skPrf` and `skSeed` is not
idealised: `prodSignQuery` has no oracle-parameterised variant to hop to. The three reduction
events are those of `ProdCollisionEvents`; their probabilities are bounded by assumption.
-/

public import Qsag.Protocol.Signing.ProdAdaptiveTcrReduction
public import Qsag.Spec.GameBound
public import Qsag.Spec.Assumptions
import all Qsag.Protocol.Signing.ProdAdaptiveTcrReduction
import all Qsag.Protocol.Signing.ProdCollisionEvents
import all Qsag.Protocol.Signing.HypertreeEufCma
import all Qsag.Spec.GameBound
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-! ## §1. Signing oracle with a monotonic epoch latch -/

/-- One-time property of a signing log: two requests at the same epoch are the same request. -/
@[expose] def ProdOneTimeLog (qs : List ProdSigningQuery) : Prop :=
  ∀ q, q ∈ qs → ∀ q', q' ∈ qs → q.epoch = q'.epoch → q = q'

/-- Run an adaptive adversary against `rawHash` and `sign` behind an epoch latch `lo` (the least
    epoch still admitted). With `latchOn = true` a signing request below the latch is answered
    `none` and is not logged; an admitted request is logged and moves the latch to `epoch + 1`.
    With `latchOn = false` every request is admitted. Returns the adversary's output and the log
    of admitted requests. -/
@[expose] def evalLatchedAdaptiveTree {α : Type} (latchOn : Bool)
    (rawHash : List UInt8 → List UInt8)
    (sign : ProdSigningQuery → Option PqHashSig) :
    ProdAdaptiveTree α → Nat → α × List ProdSigningQuery
  | .pure ret, _ => (ret, [])
  | .hashQuery x next, lo => evalLatchedAdaptiveTree latchOn rawHash sign (next (rawHash x)) lo
  | .signQuery q next, lo =>
    if latchOn = false ∨ lo ≤ q.epoch then
      ((evalLatchedAdaptiveTree latchOn rawHash sign (next (sign q)) (q.epoch + 1)).1,
        q :: (evalLatchedAdaptiveTree latchOn rawHash sign (next (sign q)) (q.epoch + 1)).2)
    else evalLatchedAdaptiveTree latchOn rawHash sign (next none) lo

theorem evalLatchedAdaptiveTree_sign {α : Type} (latchOn : Bool)
    (rawHash : List UInt8 → List UInt8) (sign : ProdSigningQuery → Option PqHashSig)
    (q : ProdSigningQuery) (next : Option PqHashSig → ProdAdaptiveTree α) (lo : Nat) :
    evalLatchedAdaptiveTree latchOn rawHash sign (.signQuery q next) lo =
      if latchOn = false ∨ lo ≤ q.epoch then
        ((evalLatchedAdaptiveTree latchOn rawHash sign (next (sign q)) (q.epoch + 1)).1,
          q :: (evalLatchedAdaptiveTree latchOn rawHash sign (next (sign q)) (q.epoch + 1)).2)
      else evalLatchedAdaptiveTree latchOn rawHash sign (next none) lo := by
  rfl

/-- The log of the latched oracle lies at or above the initial latch and has strictly
    increasing epochs. -/
theorem evalLatchedAdaptiveTree_log_increasing {α : Type}
    (rawHash : List UInt8 → List UInt8) (sign : ProdSigningQuery → Option PqHashSig) :
    ∀ (prog : ProdAdaptiveTree α) (lo : Nat),
      (∀ q, q ∈ (evalLatchedAdaptiveTree true rawHash sign prog lo).2 → lo ≤ q.epoch) ∧
      (evalLatchedAdaptiveTree true rawHash sign prog lo).2.Pairwise
        (fun a b => a.epoch < b.epoch)
  | .pure _, _ => ⟨fun _ h => (nomatch h), List.Pairwise.nil⟩
  | .hashQuery x next, lo =>
    evalLatchedAdaptiveTree_log_increasing rawHash sign (next (rawHash x)) lo
  | .signQuery q next, lo => by
    rw [evalLatchedAdaptiveTree_sign]
    if h : lo ≤ q.epoch then
      rw [ite_eq_left (Or.inr h)]
      obtain ⟨ihLo, ihPw⟩ :=
        evalLatchedAdaptiveTree_log_increasing rawHash sign (next (sign q)) (q.epoch + 1)
      refine ⟨?_, List.pairwise_cons.mpr ⟨fun q' hq' => ihLo q' hq', ihPw⟩⟩
      intro q' hq'
      rcases List.mem_cons.mp hq' with hEq | hTail
      · rw [hEq]; exact h
      · exact Nat.le_trans (Nat.le_trans h (Nat.le_succ _)) (ihLo q' hTail)
    else
      have hNot : ¬ ((true = false) ∨ lo ≤ q.epoch) := fun hOr =>
        hOr.elim (fun hb => Bool.noConfusion hb) h
      rw [ite_eq_right hNot]
      exact evalLatchedAdaptiveTree_log_increasing rawHash sign (next none) lo

theorem prodOneTimeLog_of_increasing :
    ∀ (qs : List ProdSigningQuery),
      qs.Pairwise (fun a b => a.epoch < b.epoch) → ProdOneTimeLog qs
  | [], _ => fun _ h => nomatch h
  | a :: l, hp => by
    obtain ⟨hHead, hTail⟩ := List.pairwise_cons.mp hp
    intro q hq q' hq' he
    rcases List.mem_cons.mp hq with h1 | h1
    · rcases List.mem_cons.mp hq' with h2 | h2
      · rw [h1, h2]
      · rw [h1] at he
        exact absurd he (Nat.ne_of_lt (hHead q' h2))
    · rcases List.mem_cons.mp hq' with h2 | h2
      · rw [h2] at he
        exact absurd he.symm (Nat.ne_of_lt (hHead q h1))
      · exact prodOneTimeLog_of_increasing l hTail q h1 q' h2 he

/-- **The latch enforces one-time signing.** Whatever the adversary does, the log of the latched
    oracle is one-time. -/
theorem evalLatchedAdaptiveTree_oneTime {α : Type}
    (rawHash : List UInt8 → List UInt8) (sign : ProdSigningQuery → Option PqHashSig)
    (prog : ProdAdaptiveTree α) (lo : Nat) :
    ProdOneTimeLog (evalLatchedAdaptiveTree true rawHash sign prog lo).2 :=
  prodOneTimeLog_of_increasing _
    (evalLatchedAdaptiveTree_log_increasing rawHash sign prog lo).2

/-- The oracle admits at most the adversary's signing budget. -/
theorem evalLatchedAdaptiveTree_log_length {α : Type} (latchOn : Bool)
    (rawHash : List UInt8 → List UInt8) (sign : ProdSigningQuery → Option PqHashSig) :
    ∀ {qH qS : Nat} (prog : ProdAdaptiveTree α) (lo : Nat),
      ProdDualBounded qH qS prog →
      (evalLatchedAdaptiveTree latchOn rawHash sign prog lo).2.length ≤ qS
  | _, _, .pure _, _, _ => Nat.zero_le _
  | 0, _, .hashQuery _ _, _, h => False.elim h
  | _ + 1, _, .hashQuery x next, lo, h =>
    evalLatchedAdaptiveTree_log_length latchOn rawHash sign (next (rawHash x)) lo (h (rawHash x))
  | _, 0, .signQuery _ _, _, h => False.elim h
  | _, qS + 1, .signQuery q next, lo, h => by
    rw [evalLatchedAdaptiveTree_sign]
    if hc : latchOn = false ∨ lo ≤ q.epoch then
      rw [ite_eq_left hc]
      exact Nat.succ_le_succ
        (evalLatchedAdaptiveTree_log_length latchOn rawHash sign (next (sign q)) (q.epoch + 1)
          (h (sign q)))
    else
      rw [ite_eq_right hc]
      exact Nat.le_trans
        (evalLatchedAdaptiveTree_log_length latchOn rawHash sign (next none) lo (h none))
        (Nat.le_succ _)

/-- A signature returned by the production signer is accepted by the production verifier under
    the derived public key. -/
theorem prodSignQuery_verifies (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (q : ProdSigningQuery) (sig : PqHashSig)
    (h : prodSignQuery suite params sk q = some sig) :
    verifyProductionPqHashSig suite params (derivePublicKey suite params sk) q.message sig =
      true := by
  unfold prodSignQuery at h
  cases hSt : params.statefulJorts
  · rw [hSt] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact verifyProductionPqHashSig_evalProductionStatelessSign suite params sk _ _ _ sig h
  · rw [hSt] at h
    simp only [↓reduceIte] at h
    exact verifyProductionPqHashSig_evalProductionStatefulSign suite params sk _ _ _ _ sig h

/-! ## §2. The closed experiment and its reduction games -/

/-- Outcome of one run: key `keygen ω`, adversary `adv ω` (given the public key only), executable
    signer `prodSignQuery` behind the latch, starting at epoch `0`. -/
@[expose] def execEufCmaOutcome {n qHash qSign : Nat} (latchOn : Bool)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (keygen : Fin n → PqSecretKey)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) (ω : Fin n) : ProdEufCmaOutcome :=
  ⟨keygen ω,
   (evalLatchedAdaptiveTree latchOn suite.rawHash (prodSignQuery suite params (keygen ω))
      ((adv ω).run (derivePublicKey suite params (keygen ω))) 0).2,
   (evalLatchedAdaptiveTree latchOn suite.rawHash (prodSignQuery suite params (keygen ω))
      ((adv ω).run (derivePublicKey suite params (keygen ω))) 0).1.1,
   (evalLatchedAdaptiveTree latchOn suite.rawHash (prodSignQuery suite params (keygen ω))
      ((adv ω).run (derivePublicKey suite params (keygen ω))) 0).1.2⟩

/-- The experiment with the latch switchable; `latchOn = false` is the mutation used by the
    tooth. The win predicate is `prodEufCmaWin`. -/
@[expose] def execEufCmaGameWith {n qHash qSign : Nat} (latchOn : Bool) (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (keygen : Fin n → PqSecretKey)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) : Spec.FinGame n :=
  ⟨hPos, fun ω => prodEufCmaWin suite params (execEufCmaOutcome latchOn suite params keygen adv ω)⟩

/-- **Closed adaptive EUF-CMA experiment** over the coin space `Fin n`, with the latch on. -/
@[expose] def ExecEufCmaGame {n qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (keygen : Fin n → PqSecretKey)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) : Spec.FinGame n :=
  execEufCmaGameWith true hPos suite params keygen adv

/-- The one-time hypothesis of the extractor, derived from the latch. -/
theorem execEufCmaOutcome_oneTime {n qHash qSign : Nat}
    (suite : TweakableHashSuite) (params : PqHashParams)
    (keygen : Fin n → PqSecretKey)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) (ω : Fin n) :
    ProdOneTimeLog (execEufCmaOutcome true suite params keygen adv ω).queries :=
  evalLatchedAdaptiveTree_oneTime suite.rawHash (prodSignQuery suite params (keygen ω))
    ((adv ω).run (derivePublicKey suite params (keygen ω))) 0

theorem execEufCmaOutcome_queries_le {n qHash qSign : Nat} (latchOn : Bool)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (keygen : Fin n → PqSecretKey)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) (ω : Fin n) :
    (execEufCmaOutcome latchOn suite params keygen adv ω).queries.length ≤ qSign :=
  evalLatchedAdaptiveTree_log_length latchOn suite.rawHash
    (prodSignQuery suite params (keygen ω)) _ 0
    ((adv ω).bounded (derivePublicKey suite params (keygen ω)))

/-- Reduction to `ITSR`: wins on the coins where the extractor returns a few-time subset cover. -/
@[expose] def execEufCmaItsrReduction {n qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16)
    (keygen : Fin n → PqSecretKey)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) : Spec.FinGame n :=
  ⟨hPos, fun ω => prodItsrEvent suite params hw (execEufCmaOutcome true suite params keygen adv ω)
    (fun _ => execEufCmaOutcome_oneTime suite params keygen adv ω)⟩

/-- Reduction to `SM-DT-TCR`: wins on the coins where the extractor returns an on-path target
    and a colliding input. -/
@[expose] def execEufCmaTcrReduction {n qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16)
    (keygen : Fin n → PqSecretKey)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) : Spec.FinGame n :=
  ⟨hPos, fun ω => prodTcrEvent suite params hw (execEufCmaOutcome true suite params keygen adv ω)
    (fun _ => execEufCmaOutcome_oneTime suite params keygen adv ω)⟩

/-- Reduction to `SM-DT-PRE`: wins on the coins where the extractor returns a chain preimage. -/
@[expose] def execEufCmaPreReduction {n qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16)
    (keygen : Fin n → PqSecretKey)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) : Spec.FinGame n :=
  ⟨hPos, fun ω => prodPreEvent suite params hw (execEufCmaOutcome true suite params keygen adv ω)
    (fun _ => execEufCmaOutcome_oneTime suite params keygen adv ω)⟩

/-- Every winning coin of the experiment is a winning coin of one of the three reductions. -/
theorem execEufCma_win_classified {n qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16)
    (keygen : Fin n → PqSecretKey)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) (ω : Fin n)
    (hWin : (ExecEufCmaGame hPos suite params keygen adv).win ω = true) :
    (execEufCmaItsrReduction hPos suite params hw keygen adv).win ω = true ∨
    (execEufCmaTcrReduction hPos suite params hw keygen adv).win ω = true ∨
    (execEufCmaPreReduction hPos suite params hw keygen adv).win ω = true :=
  prodEufCmaWin_classified suite params hw (execEufCmaOutcome true suite params keygen adv ω)
    (fun _ => execEufCmaOutcome_oneTime suite params keygen adv ω) hWin

/-! ## §3. The bound -/

/-- **Closed EUF-CMA reduction.** For every key generator and every family of seed-withheld
    adaptive adversaries, the probability that the executable verifier accepts a message the
    latched signer did not answer is at most the sum of the winning probabilities of the three
    reduction games built from the same run. -/
theorem jorts_baggy_closed_euf_cma {n qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16)
    (keygen : Fin n → PqSecretKey)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) :
    Spec.GameBound (ExecEufCmaGame hPos suite params keygen adv).winProb
      ((execEufCmaItsrReduction hPos suite params hw keygen adv).winProb.add
        ((execEufCmaTcrReduction hPos suite params hw keygen adv).winProb.add
          (execEufCmaPreReduction hPos suite params hw keygen adv).winProb)) := by
  let tcrOrPre : Spec.FinGame n :=
    ⟨hPos, fun ω => (execEufCmaTcrReduction hPos suite params hw keygen adv).win ω ||
      (execEufCmaPreReduction hPos suite params hw keygen adv).win ω⟩
  have h1 := Spec.event_le_two_reductions (ExecEufCmaGame hPos suite params keygen adv)
    (execEufCmaItsrReduction hPos suite params hw keygen adv) tcrOrPre (fun ω hWin => by
      rcases execEufCma_win_classified hPos suite params hw keygen adv ω hWin with h | h | h
      · exact .inl h
      · refine .inr ?_
        show ((execEufCmaTcrReduction hPos suite params hw keygen adv).win ω ||
          (execEufCmaPreReduction hPos suite params hw keygen adv).win ω) = true
        rw [h]; rfl
      · refine .inr ?_
        show ((execEufCmaTcrReduction hPos suite params hw keygen adv).win ω ||
          (execEufCmaPreReduction hPos suite params hw keygen adv).win ω) = true
        rw [h]; exact Bool.or_true _)
  have h2 := Spec.event_le_two_reductions tcrOrPre
    (execEufCmaTcrReduction hPos suite params hw keygen adv)
    (execEufCmaPreReduction hPos suite params hw keygen adv) (fun ω hWin => by
      have hWin' : ((execEufCmaTcrReduction hPos suite params hw keygen adv).win ω ||
          (execEufCmaPreReduction hPos suite params hw keygen adv).win ω) = true := hWin
      cases ht : (execEufCmaTcrReduction hPos suite params hw keygen adv).win ω
      · rw [ht] at hWin'
        exact .inr hWin'
      · exact .inl rfl)
  exact Spec.RatBound.le_trans h1 (Spec.RatBound.add_le_add (Spec.RatBound.le_refl _) h2)

/-- **Reduction embedding (open obligation).** The three extractor events of the closed
    experiment are realised inside the experiments of the bundle `A`: on every coin where the
    extractor returns a subset cover, an on-path target collision or a chain preimage, the
    adversary of the corresponding `Spec` experiment (`A.itsr.adv`, `A.tcr.adv`, `A.pre.adv`,
    against `A.itsr.hmsg`, `A.tcr.th`, `A.pre.th` with the samplers of `A`) wins. Providing it
    means exhibiting those three adversaries as simulations of the forger `adv` against the
    primitives of `suite`. -/
structure ExecEufCmaReductionEmbedding {n qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16)
    (keygen : Fin n → PqSecretKey)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign)
    (A : Spec.HashSigAssumptions n) : Prop where
  itsr : ∀ ω : Fin n, (execEufCmaItsrReduction hPos suite params hw keygen adv).win ω = true →
    A.itsr.itsrGame.win ω = true
  tcr : ∀ ω : Fin n, (execEufCmaTcrReduction hPos suite params hw keygen adv).win ω = true →
    A.tcr.tcrGame.win ω = true
  pre : ∀ ω : Fin n, (execEufCmaPreReduction hPos suite params hw keygen adv).win ω = true →
    A.pre.preGame.win ω = true

/-- Under a reduction embedding into the bundle `A`, the experiment is bounded by
    `εItsr + εTcr + εPre`. -/
theorem jorts_baggy_closed_euf_cma_assumption_bound {n qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16)
    (keygen : Fin n → PqSecretKey)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign)
    (A : Spec.HashSigAssumptions n)
    (hEmbed : ExecEufCmaReductionEmbedding hPos suite params hw keygen adv A) :
    Spec.GameBound (ExecEufCmaGame hPos suite params keygen adv).winProb A.totalBound :=
  A.forger_bound (ExecEufCmaGame hPos suite params keygen adv) (fun ω hWin => by
    rcases execEufCma_win_classified hPos suite params hw keygen adv ω hWin with h | h | h
    · exact .inl (hEmbed.itsr ω h)
    · exact .inr (.inl (hEmbed.tcr ω h))
    · exact .inr (.inr (hEmbed.pre ω h)))

/-- A game's winning probability is at most another's plus their distinguishing advantage. -/
theorem winProb_le_add_advDist {n : Nat} (G₁ G₀ : Spec.FinGame n) :
    Spec.GameBound G₁.winProb (G₀.winProb.add (Spec.AdvDist G₁ G₀)) := by
  unfold Spec.GameBound Spec.RatBound.le Spec.FinGame.winProb Spec.AdvDist Spec.RatBound.add
  dsimp only
  have h : G₁.winCount ≤ G₀.winCount + Spec.natAbsDiff G₁.winCount G₀.winCount := by
    generalize G₁.winCount = a
    generalize G₀.winCount = b
    unfold Spec.natAbsDiff
    if hab : a ≤ b then
      rw [ite_eq_left hab]; exact Nat.le_trans hab (Nat.le_add_right _ _)
    else
      rw [ite_eq_right hab]
      rw [Nat.add_sub_cancel' (Nat.le_of_lt (Nat.lt_of_not_le hab))]
      exact Nat.le_refl _
  rw [← Nat.add_mul, Nat.mul_assoc]
  exact Nat.mul_le_mul_right _ h

/-- **Key-generation hop.** If the real PRF game of a `KeyedPrfAssumption` (its distinguisher
    `P.adv` against `P.prf` under `P.key`) has the win predicate of the experiment under
    `keygenReal`, and its ideal game (against the sampled function `P.rf`) that of the
    experiment under `keygenIdeal`, the real experiment is bounded by the three reductions of
    the ideal experiment plus `εPrf`. -/
theorem jorts_baggy_closed_euf_cma_keygen_hop {n qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16)
    (keygenReal keygenIdeal : Fin n → PqSecretKey)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign)
    (P : Spec.KeyedPrfAssumption n)
    (hReal : P.realGame = ExecEufCmaGame hPos suite params keygenReal adv)
    (hIdeal : P.idealGame = ExecEufCmaGame hPos suite params keygenIdeal adv) :
    Spec.GameBound (ExecEufCmaGame hPos suite params keygenReal adv).winProb
      (((execEufCmaItsrReduction hPos suite params hw keygenIdeal adv).winProb.add
        ((execEufCmaTcrReduction hPos suite params hw keygenIdeal adv).winProb.add
          (execEufCmaPreReduction hPos suite params hw keygenIdeal adv).winProb)).add P.εPrf) := by
  have hAdv : Spec.GameBound
      (Spec.AdvDist (ExecEufCmaGame hPos suite params keygenReal adv)
        (ExecEufCmaGame hPos suite params keygenIdeal adv)) P.εPrf := by
    rw [← hReal, ← hIdeal]
    exact P.advantage_bound
  exact Spec.RatBound.le_trans
    (winProb_le_add_advDist (ExecEufCmaGame hPos suite params keygenReal adv)
      (ExecEufCmaGame hPos suite params keygenIdeal adv))
    (Spec.RatBound.add_le_add
      (jorts_baggy_closed_euf_cma hPos suite params hw keygenIdeal adv) hAdv)

#verify_constructive
  Qsag.evalLatchedAdaptiveTree_log_increasing
  Qsag.evalLatchedAdaptiveTree_oneTime
  Qsag.evalLatchedAdaptiveTree_log_length
  Qsag.prodSignQuery_verifies
  Qsag.execEufCmaOutcome_oneTime
  Qsag.execEufCmaOutcome_queries_le
  Qsag.jorts_baggy_closed_euf_cma
  Qsag.jorts_baggy_closed_euf_cma_assumption_bound
  Qsag.winProb_le_add_advDist
  Qsag.jorts_baggy_closed_euf_cma_keygen_hop

end Qsag
end

#print axioms Qsag.jorts_baggy_closed_euf_cma
#print axioms Qsag.jorts_baggy_closed_euf_cma_keygen_hop

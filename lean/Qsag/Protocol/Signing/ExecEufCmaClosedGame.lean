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
* `execEufCmaItsrReduction`, `execEufCmaTcrReduction`, `execEufCmaPreReduction`: the three
  extractor events on the run, as games. Their win predicates are computed from the whole
  outcome, secret key included.
* `jorts_baggy_closed_euf_cma_same_trace_classification`:
  `Pr[ExecEufCmaGame] ≤ Pr[R_itsr] + (Pr[R_tcr] + Pr[R_pre])`, a partition of the winning coins.
* `SeedWithheldOracleAdv`, `execSubsetCoverGame`, `execKeyedPathCollisionGame`,
  `execKeyedSecretPreimageGame`: games played by a program that receives the public key and
  queries the hash and the latched signer. The first is decided on the public transcript; in
  the other two the challenger compares the adversary's output with the signer's own hash input
  at the named position.
* `execCollisionReductionAdv`, `execPreimageReductionAdv`: the reduction adversaries. They run
  the forger, record the answered signing queries, and run the public-data extractor
  `prodPublicExtract` (a function of public key, log and forgery; `ProdHashReductions` §4) as a
  hash-oracle program. Budgets: the forger's, plus `prodTcrReductionHashBudget params`,
  respectively `1 + prodXofHashBudget params`, hash queries.
* `execEufCma_win_reduction_adversary_wins`: on every winning coin the forger wins the
  subset-cover game or one of the reduction adversaries wins its keyed game.
* `jorts_baggy_closed_euf_cma_keyed_target_bound`: under hardness of the three games for
  classes containing those adversaries, the forger wins with probability at most
  `εI + prodPathTargetCount params qSign · εT + prodPreCandidateCount params · εP`.
* `jorts_baggy_closed_euf_cma_keygen_hop`: a key-generation game hop under `Spec.PrfHard` for a
  distinguisher class containing the simulating distinguisher. Its simulation hypotheses say
  that the experiment under the real key generator is the real PRF game of an oracle
  distinguisher, and under the ideal key generator its ideal game.

What is not here. The keyed games are not the `SM-DT-TCR` and `SM-DT-PRE` experiments of
`Spec.Assumptions` and the subset-cover game is not its `ITSR` experiment: the targets are the
signer's hash inputs and the randomizers are the signer's, both functions of the secret key,
where the `Spec` experiments have targets committed before the seed is revealed, uniform hidden
inputs and uniform randomizers. A reduction to `Spec.ItsrHard`, `Spec.SmDtTcrHard` and
`Spec.SmDtPreHard` needs the signer simulated from target-oracle answers, a PRF hop for the
chain secrets and randomizers, and an undetectability hop for chain positions above `0`. None
of the three is constructed. The hardness hypotheses are false for classes that contain
exhaustive search; the classes are parameters.

The key-generation hop replaces the key generator only. The signer's internal use of `skPrf` and
`skSeed` is not idealised: `prodSignQuery` has no oracle-parameterised variant to hop to.
-/

public import Qsag.Protocol.Signing.ProdHashReductions
public import Qsag.Spec.GameBound
public import Qsag.Spec.Assumptions
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
  rw [prodSignQuery_eq] at h
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
def execEufCmaGameWith {n qHash qSign : Nat} (latchOn : Bool) (hPos : 0 < n)
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

/-- Extractor event, index coverage: wins on the coins where the extractor run on the whole
    outcome returns a few-time subset cover. -/
def execEufCmaItsrReduction {n qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16)
    (keygen : Fin n → PqSecretKey)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) : Spec.FinGame n :=
  ⟨hPos, fun ω => prodItsrEvent suite params hw (execEufCmaOutcome true suite params keygen adv ω)
    (fun _ => execEufCmaOutcome_oneTime suite params keygen adv ω)⟩

/-- Extractor event, collision: wins on the coins where the extractor run on the whole outcome
    returns an on-path target and a colliding input. -/
def execEufCmaTcrReduction {n qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16)
    (keygen : Fin n → PqSecretKey)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) : Spec.FinGame n :=
  ⟨hPos, fun ω => prodTcrEvent suite params hw (execEufCmaOutcome true suite params keygen adv ω)
    (fun _ => execEufCmaOutcome_oneTime suite params keygen adv ω)⟩

/-- Extractor event, preimage: wins on the coins where the extractor run on the whole outcome
    returns a chain or FORS-leaf preimage. -/
def execEufCmaPreReduction {n qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16)
    (keygen : Fin n → PqSecretKey)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) : Spec.FinGame n :=
  ⟨hPos, fun ω => prodPreEvent suite params hw (execEufCmaOutcome true suite params keygen adv ω)
    (fun _ => execEufCmaOutcome_oneTime suite params keygen adv ω)⟩

/-- Every winning coin of the experiment is a winning coin of one of the three extractor
    events. -/
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

/-- **Same-trace classification of the closed experiment.** For every key generator and every
    family of seed-withheld adaptive adversaries, the probability that the executable verifier
    accepts a message the latched signer did not answer is at most the sum of the probabilities
    of the three extractor events on the same run. The events are indicators computed from the
    whole outcome, secret key included: this is a partition of the winning coins, not a bound by
    the advantage of an adversary. The bound by adversaries that see only the public key and the
    oracles is `jorts_baggy_closed_euf_cma_keyed_target_bound`. -/
theorem jorts_baggy_closed_euf_cma_same_trace_classification {n qHash qSign : Nat} (hPos : 0 < n)
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

/-! ## §4. Reduction adversaries that see the public key and the oracles only

The three games below are played by an adversary of type `SeedWithheldOracleAdv`: a program
that receives the public key, queries the raw hash and the latched signer, and returns its
output. The challenger holds the key, answers the queries and decides the win.

* `execSubsetCoverGame`: the adversary returns a message and a signature; the win is the public
  verdict `prodPublicSubsetCoverCheck` on `(pk, log, output)`.
* `execKeyedPathCollisionGame`: the adversary names a position on a verification path and an
  input; it wins if the input differs from the input the signer hashes at that position and
  has the same digest (`smDtTcrChallengerCheck`).
* `execKeyedSecretPreimageGame`: the adversary names an unopened FORS leaf or an unrevealed
  WOTS chain position and a value; it wins if the value hashes to the signer's value there
  (`smDtPreChallengerCheck`).

In the last two the targets are the signer's own hash inputs, which are functions of the secret
key. They are not the `SM-DT-TCR` and `SM-DT-PRE` experiments of `Spec.Assumptions`, where the
adversary commits the targets before the seed is revealed and the hidden inputs are uniform;
and in the first the randomizers are the signer's, not uniform samples. Relating the three to
`Spec.ItsrHard`, `Spec.SmDtTcrHard` and `Spec.SmDtPreHard` needs a simulation of the signer
from target-oracle answers and a PRF hop, which this module does not contain. -/

/-- An oracle adversary with output type `α`: it receives the public key only and makes at most
    `qHash` raw-hash queries and `qSign` signing queries. -/
structure SeedWithheldOracleAdv (α : Type) (qHash qSign : Nat) where
  run : PqPublicKey → ProdAdaptiveTree α
  bounded : ∀ pk, ProdDualBounded qHash qSign (run pk)

/-- A forger is an oracle adversary whose output is a message and a signature. -/
@[expose] def SeedWithheldEufCmaAdv.toOracleAdv {qHash qSign : Nat}
    (A : SeedWithheldEufCmaAdv qHash qSign) :
    SeedWithheldOracleAdv (List UInt8 × PqHashSig) qHash qSign :=
  ⟨A.run, A.bounded⟩

/-- Run an oracle adversary against the raw hash and the latched signer under key `sk`: its
    output and the log of admitted signing requests. -/
@[expose] def execLatchedRun {α : Type} {qHash qSign : Nat} (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) (B : SeedWithheldOracleAdv α qHash qSign) :
    α × List ProdSigningQuery :=
  evalLatchedAdaptiveTree true suite.rawHash (prodSignQuery suite params sk)
    (B.run (derivePublicKey suite params sk)) 0

theorem execLatchedRun_queries_le {α : Type} {qHash qSign : Nat} (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) (B : SeedWithheldOracleAdv α qHash qSign) :
    (execLatchedRun suite params sk B).2.length ≤ qSign :=
  evalLatchedAdaptiveTree_log_length true suite.rawHash (prodSignQuery suite params sk) _ 0
    (B.bounded (derivePublicKey suite params sk))

/-- **Subset-cover game.** The win is decided on the public transcript. -/
@[expose] def execSubsetCoverGame {n qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams) (keygen : Fin n → PqSecretKey)
    (B : Fin n → SeedWithheldOracleAdv (List UInt8 × PqHashSig) qHash qSign) : Spec.FinGame n :=
  ⟨hPos, fun ω =>
    prodPublicSubsetCoverCheck suite params (derivePublicKey suite params (keygen ω))
      (productionSigningLog suite params (keygen ω)
        (execLatchedRun suite params (keygen ω) (B ω)).2)
      (execLatchedRun suite params (keygen ω) (B ω)).1.1
      (execLatchedRun suite params (keygen ω) (B ω)).1.2⟩

/-- **Keyed path-collision game.** The target is the signer's input at the named position. -/
@[expose] def execKeyedPathCollisionGame {n qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams) (keygen : Fin n → PqSecretKey)
    (B : Fin n → SeedWithheldOracleAdv (Option SmDtTcrSubmission) qHash qSign) : Spec.FinGame n :=
  ⟨hPos, fun ω =>
    smDtTcrChallengerCheck suite params (keygen ω)
      (execLatchedRun suite params (keygen ω) (B ω)).2
      (execLatchedRun suite params (keygen ω) (B ω)).1⟩

/-- **Keyed secret-preimage game.** The target is the signer's value at an unopened position. -/
@[expose] def execKeyedSecretPreimageGame {n qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams) (keygen : Fin n → PqSecretKey)
    (B : Fin n → SeedWithheldOracleAdv (Option SmDtPreSubmission) qHash qSign) : Spec.FinGame n :=
  ⟨hPos, fun ω =>
    smDtPreChallengerCheck suite params (keygen ω)
      (execLatchedRun suite params (keygen ω) (B ω)).2
      (execLatchedRun suite params (keygen ω) (B ω)).1⟩

/-- A winning coin of the subset-cover game carries the FORS index-coverage event. -/
theorem execSubsetCoverGame_win_sound {n qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams) (keygen : Fin n → PqSecretKey)
    (B : Fin n → SeedWithheldOracleAdv (List UInt8 × PqHashSig) qHash qSign) (ω : Fin n)
    (hWin : (execSubsetCoverGame hPos suite params keygen B).win ω = true) :
    ProdForsItsrBreak suite params (derivePublicKey suite params (keygen ω))
      (productionSigningLog suite params (keygen ω)
        (execLatchedRun suite params (keygen ω) (B ω)).2)
      (execLatchedRun suite params (keygen ω) (B ω)).1.1
      (execLatchedRun suite params (keygen ω) (B ω)).1.2 :=
  prodPublicSubsetCoverCheck_sound suite params _ _ _ _ hWin

/-- A winning coin of the keyed path-collision game carries a collision of `suite.rawHash`
    with an input the signer hashes. -/
theorem execKeyedPathCollisionGame_win_sound {n qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams) (keygen : Fin n → PqSecretKey)
    (B : Fin n → SeedWithheldOracleAdv (Option SmDtTcrSubmission) qHash qSign) (ω : Fin n)
    (hWin : (execKeyedPathCollisionGame hPos suite params keygen B).win ω = true) :
    ProdSmTcrBreak suite params (keygen ω)
      (productionSigningLog suite params (keygen ω)
        (execLatchedRun suite params (keygen ω) (B ω)).2) := by
  have hChk : smDtTcrChallengerCheck suite params (keygen ω)
      (execLatchedRun suite params (keygen ω) (B ω)).2
      (execLatchedRun suite params (keygen ω) (B ω)).1 = true := hWin
  cases hOut : (execLatchedRun suite params (keygen ω) (B ω)).1 with
  | none =>
    rw [hOut, smDtTcrChallengerCheck_none] at hChk
    cases hChk
  | some sub =>
    rw [hOut] at hChk
    exact smDtTcrChallengerCheck_sound suite params _ _ sub hChk

/-! ### Evaluation of composed programs under the latch -/

/-- A program without signing queries does not touch the latch or the log. -/
theorem evalLatchedAdaptiveTree_signFree {α : Type} (latchOn : Bool)
    (rawHash : List UInt8 → List UInt8) (sign : ProdSigningQuery → Option PqHashSig) :
    ∀ {qH : Nat} (t : ProdAdaptiveTree α) (lo : Nat), ProdDualBounded qH 0 t →
      evalLatchedAdaptiveTree latchOn rawHash sign t lo = (t.hashOnlyValue rawHash, [])
  | _, .pure _, _, _ => rfl
  | 0, .hashQuery _ _, _, h => False.elim h
  | _ + 1, .hashQuery x next, lo, h =>
    evalLatchedAdaptiveTree_signFree latchOn rawHash sign (next (rawHash x)) lo (h (rawHash x))
  | _, .signQuery _ _, _, h => False.elim h

theorem evalLatchedAdaptiveTree_bind_signFree {α β : Type} (latchOn : Bool)
    (rawHash : List UInt8 → List UInt8) (sign : ProdSigningQuery → Option PqHashSig)
    {qH : Nat} (f : α → ProdAdaptiveTree β) (hf : ∀ a, ProdDualBounded qH 0 (f a)) :
    ∀ (t : ProdAdaptiveTree α) (lo : Nat),
      evalLatchedAdaptiveTree latchOn rawHash sign (t.bind f) lo =
        ((f (evalLatchedAdaptiveTree latchOn rawHash sign t lo).1).hashOnlyValue rawHash,
          (evalLatchedAdaptiveTree latchOn rawHash sign t lo).2)
  | .pure a, lo => evalLatchedAdaptiveTree_signFree latchOn rawHash sign (f a) lo (hf a)
  | .hashQuery x next, lo =>
    evalLatchedAdaptiveTree_bind_signFree latchOn rawHash sign f hf (next (rawHash x)) lo
  | .signQuery q next, lo => by
    show evalLatchedAdaptiveTree latchOn rawHash sign
      (.signQuery q (fun s => (next s).bind f)) lo = _
    rw [evalLatchedAdaptiveTree_sign, evalLatchedAdaptiveTree_sign]
    if hc : latchOn = false ∨ lo ≤ q.epoch then
      rw [ite_eq_left hc, ite_eq_left hc]
      dsimp only
      rw [evalLatchedAdaptiveTree_bind_signFree latchOn rawHash sign f hf (next (sign q))
        (q.epoch + 1)]
    else
      rw [ite_eq_right hc, ite_eq_right hc]
      exact evalLatchedAdaptiveTree_bind_signFree latchOn rawHash sign f hf (next none) lo

/-- The tracked log is the signer's transcript of the admitted requests. -/
theorem evalLatchedAdaptiveTree_trackSignLog {α : Type} (latchOn : Bool)
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey) :
    ∀ (t : ProdAdaptiveTree α) (acc : List (List UInt8 × PqHashSig)) (lo : Nat),
      evalLatchedAdaptiveTree latchOn suite.rawHash (prodSignQuery suite params sk)
          (prodTrackSignLog acc t) lo =
        (((evalLatchedAdaptiveTree latchOn suite.rawHash (prodSignQuery suite params sk) t lo).1,
          acc ++ productionSigningLog suite params sk
            (evalLatchedAdaptiveTree latchOn suite.rawHash (prodSignQuery suite params sk) t
              lo).2),
          (evalLatchedAdaptiveTree latchOn suite.rawHash (prodSignQuery suite params sk) t lo).2)
  | .pure a, acc, lo => by
    show ((a, acc), ([] : List ProdSigningQuery)) =
      ((a, acc ++ productionSigningLog suite params sk []), [])
    rw [productionSigningLog_nil, List.append_nil]
  | .hashQuery x next, acc, lo =>
    evalLatchedAdaptiveTree_trackSignLog latchOn suite params sk (next (suite.rawHash x)) acc lo
  | .signQuery q next, acc, lo => by
    show evalLatchedAdaptiveTree latchOn suite.rawHash (prodSignQuery suite params sk)
      (.signQuery q (fun resp =>
        prodTrackSignLog
          (match resp with
            | none => acc
            | some sig => acc ++ [(q.message, sig)])
          (next resp))) lo = _
    rw [evalLatchedAdaptiveTree_sign, evalLatchedAdaptiveTree_sign]
    if hc : latchOn = false ∨ lo ≤ q.epoch then
      rw [ite_eq_left hc, ite_eq_left hc]
      dsimp only
      rw [evalLatchedAdaptiveTree_trackSignLog latchOn suite params sk
        (next (prodSignQuery suite params sk q)) _ (q.epoch + 1), productionSigningLog_cons]
      cases prodSignQuery suite params sk q with
      | none => rfl
      | some sig =>
        dsimp only
        rw [List.append_assoc]
    else
      rw [ite_eq_right hc, ite_eq_right hc]
      exact evalLatchedAdaptiveTree_trackSignLog latchOn suite params sk (next none) acc lo

/-! ### The three reduction adversaries -/

/-- **Collision reduction adversary** for candidate `slot`: run the forger, record the answered
    signing queries, run the collision-candidate program on `(pk, log, forgery)`. It makes the
    forger's queries and at most `prodTcrReductionHashBudget params` further hash queries. -/
def execCollisionReductionAdv {qHash qSign : Nat} (params : PqHashParams) (slot : Nat)
    (A : SeedWithheldEufCmaAdv qHash qSign) :
    SeedWithheldOracleAdv (Option SmDtTcrSubmission)
      (qHash + prodTcrReductionHashBudget params) qSign where
  run pk := (prodTrackSignLog [] (A.run pk)).bind fun outLog =>
    prodPublicCollisionProgram params slot pk outLog.2 outLog.1.1 outLog.1.2
  bounded pk :=
    ProdDualBounded.bind
      (fun outLog => prodPublicCollisionProgram_bounded params slot pk outLog.2 outLog.1.1
        outLog.1.2)
      (prodTrackSignLog_bounded [] (A.bounded pk))

/-- **Preimage reduction adversary** for candidate `slot`: run the forger, then the
    preimage-candidate program on `(pk, forgery)`. It makes the forger's queries and at most
    `1 + prodXofHashBudget params` further hash queries. -/
def execPreimageReductionAdv {qHash qSign : Nat} (params : PqHashParams) (slot : Nat)
    (A : SeedWithheldEufCmaAdv qHash qSign) :
    SeedWithheldOracleAdv (Option SmDtPreSubmission)
      (qHash + (1 + prodXofHashBudget params)) qSign where
  run pk := (A.run pk).bind fun out => prodPublicPreimageProgram params slot pk out.1 out.2
  bounded pk :=
    ProdDualBounded.bind
      (fun out => prodPublicPreimageProgram_bounded params slot pk out.1 out.2)
      (A.bounded pk)

/-- The collision reduction adversary returns candidate `slot` of the public-data extractor on
    the forger's own run, and its signing log is the forger's. -/
theorem execLatchedRun_collisionReduction {qHash qSign : Nat} (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) (slot : Nat)
    (A : SeedWithheldEufCmaAdv qHash qSign) :
    execLatchedRun suite params sk (execCollisionReductionAdv params slot A) =
      ((prodPublicExtract suite params (derivePublicKey suite params sk)
          (productionSigningLog suite params sk (execLatchedRun suite params sk A.toOracleAdv).2)
          (execLatchedRun suite params sk A.toOracleAdv).1.1
          (execLatchedRun suite params sk A.toOracleAdv).1.2).collisions[slot]?,
        (execLatchedRun suite params sk A.toOracleAdv).2) := by
  show evalLatchedAdaptiveTree true suite.rawHash (prodSignQuery suite params sk)
    ((prodTrackSignLog [] (A.run (derivePublicKey suite params sk))).bind fun outLog =>
      prodPublicCollisionProgram params slot (derivePublicKey suite params sk) outLog.2
        outLog.1.1 outLog.1.2) 0 = _
  rw [evalLatchedAdaptiveTree_bind_signFree true suite.rawHash (prodSignQuery suite params sk)
    (fun outLog : (List UInt8 × PqHashSig) × List (List UInt8 × PqHashSig) =>
      prodPublicCollisionProgram params slot (derivePublicKey suite params sk) outLog.2
        outLog.1.1 outLog.1.2)
    (fun outLog => prodPublicCollisionProgram_bounded params slot _ outLog.2 outLog.1.1
      outLog.1.2),
    evalLatchedAdaptiveTree_trackSignLog]
  dsimp only
  rw [prodPublicCollisionProgram_value, List.nil_append]
  rfl

/-- The preimage reduction adversary returns candidate `slot` of the public-data extractor on
    the forger's own run, and its signing log is the forger's. -/
theorem execLatchedRun_preimageReduction {qHash qSign : Nat} (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) (slot : Nat)
    (A : SeedWithheldEufCmaAdv qHash qSign) :
    execLatchedRun suite params sk (execPreimageReductionAdv params slot A) =
      ((prodPublicExtract suite params (derivePublicKey suite params sk)
          (productionSigningLog suite params sk (execLatchedRun suite params sk A.toOracleAdv).2)
          (execLatchedRun suite params sk A.toOracleAdv).1.1
          (execLatchedRun suite params sk A.toOracleAdv).1.2).preimages[slot]?,
        (execLatchedRun suite params sk A.toOracleAdv).2) := by
  show evalLatchedAdaptiveTree true suite.rawHash (prodSignQuery suite params sk)
    ((A.run (derivePublicKey suite params sk)).bind fun out =>
      prodPublicPreimageProgram params slot (derivePublicKey suite params sk) out.1 out.2) 0 = _
  rw [evalLatchedAdaptiveTree_bind_signFree true suite.rawHash (prodSignQuery suite params sk)
    (fun out : List UInt8 × PqHashSig =>
      prodPublicPreimageProgram params slot (derivePublicKey suite params sk) out.1 out.2)
    (fun out => prodPublicPreimageProgram_bounded params slot _ out.1 out.2)]
  rw [prodPublicPreimageProgram_value suite params slot _
    (productionSigningLog suite params sk (execLatchedRun suite params sk A.toOracleAdv).2)]
  rfl

/-- **Every forgery is a win of one of the three reduction adversaries.** On a winning coin of
    the closed experiment, the forger itself wins the subset-cover game, or for some `slot`
    below `prodPathTargetCount params qSign` the collision reduction adversary wins the keyed
    path-collision game, or for some `slot` below `prodPreCandidateCount params` the preimage
    reduction adversary wins the keyed secret-preimage game, on the same coin. -/
theorem execEufCma_win_reduction_adversary_wins {n qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16)
    (keygen : Fin n → PqSecretKey)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) (ω : Fin n)
    (hWin : (ExecEufCmaGame hPos suite params keygen adv).win ω = true) :
    (execSubsetCoverGame hPos suite params keygen (fun ω => (adv ω).toOracleAdv)).win ω = true ∨
    (∃ slot : Fin (prodPathTargetCount params qSign),
      (execKeyedPathCollisionGame hPos suite params keygen
        (fun ω => execCollisionReductionAdv params slot.val (adv ω))).win ω = true) ∨
    (∃ slot : Fin (prodPreCandidateCount params),
      (execKeyedSecretPreimageGame hPos suite params keygen
        (fun ω => execPreimageReductionAdv params slot.val (adv ω))).win ω = true) := by
  have hWin' : prodEufCmaWin suite params (execEufCmaOutcome true suite params keygen adv ω) =
      true := hWin
  rcases prodPublicExtract_complete suite params hw
      (execEufCmaOutcome true suite params keygen adv ω)
      (fun _ => execEufCmaOutcome_oneTime suite params keygen adv ω) hWin' with hI | hT | hP
  · exact .inl ((prodPublicExtract_subsetCover suite params _ _ _ _).symm.trans hI)
  · refine .inr (.inl ?_)
    obtain ⟨sub, hMem, hChk⟩ := hT
    obtain ⟨idx, hIdxLt, hIdxEq⟩ := List.mem_iff_getElem.mp hMem
    have hLogLe : (productionSigningLog suite params (keygen ω)
        (execEufCmaOutcome true suite params keygen adv ω).queries).length ≤ qSign :=
      Nat.le_trans (productionSigningLog_length_le suite params (keygen ω) _)
        (execEufCmaOutcome_queries_le true suite params keygen adv ω)
    refine ⟨⟨idx, Nat.lt_of_lt_of_le hIdxLt
      (Nat.le_trans (prodPublicExtract_collisions_length_le suite params _ _ _ _)
        (prodPathTargetCount_mono params hLogLe))⟩, ?_⟩
    show smDtTcrChallengerCheck suite params (keygen ω)
      (execLatchedRun suite params (keygen ω) (execCollisionReductionAdv params idx (adv ω))).2
      (execLatchedRun suite params (keygen ω) (execCollisionReductionAdv params idx (adv ω))).1 =
        true
    rw [execLatchedRun_collisionReduction]
    dsimp only
    have hGet : (prodPublicExtract suite params (derivePublicKey suite params (keygen ω))
        (productionSigningLog suite params (keygen ω)
          (execLatchedRun suite params (keygen ω) (adv ω).toOracleAdv).2)
        (execLatchedRun suite params (keygen ω) (adv ω).toOracleAdv).1.1
        (execLatchedRun suite params (keygen ω) (adv ω).toOracleAdv).1.2).collisions[idx]? =
        some sub :=
      (List.getElem?_eq_getElem hIdxLt).trans (congrArg some hIdxEq)
    rw [hGet]
    exact hChk
  · refine .inr (.inr ?_)
    obtain ⟨sub, hMem, hChk⟩ := hP
    obtain ⟨idx, hIdxLt, hIdxEq⟩ := List.mem_iff_getElem.mp hMem
    refine ⟨⟨idx, by
      rw [← prodPublicExtract_preimages_length suite params
        (derivePublicKey suite params (keygen ω))
        (productionSigningLog suite params (keygen ω)
          (execEufCmaOutcome true suite params keygen adv ω).queries)
        (execEufCmaOutcome true suite params keygen adv ω).msgStar
        (execEufCmaOutcome true suite params keygen adv ω).sigStar]
      exact hIdxLt⟩, ?_⟩
    show smDtPreChallengerCheck suite params (keygen ω)
      (execLatchedRun suite params (keygen ω) (execPreimageReductionAdv params idx (adv ω))).2
      (execLatchedRun suite params (keygen ω) (execPreimageReductionAdv params idx (adv ω))).1 =
        true
    rw [execLatchedRun_preimageReduction]
    dsimp only
    have hGet : (prodPublicExtract suite params (derivePublicKey suite params (keygen ω))
        (productionSigningLog suite params (keygen ω)
          (execLatchedRun suite params (keygen ω) (adv ω).toOracleAdv).2)
        (execLatchedRun suite params (keygen ω) (adv ω).toOracleAdv).1.1
        (execLatchedRun suite params (keygen ω) (adv ω).toOracleAdv).1.2).preimages[idx]? =
        some sub :=
      (List.getElem?_eq_getElem hIdxLt).trans (congrArg some hIdxEq)
    rw [hGet]
    exact hChk

/-! ## §5. The bound -/

/-- Some game of the family is won on the coin. -/
def anySlotWins {n : Nat} : (M : Nat) → (Fin M → Spec.FinGame n) → Fin n → Bool
  | 0, _, _ => false
  | M + 1, R, ω =>
    (R ⟨0, Nat.succ_pos M⟩).win ω ||
      anySlotWins M (fun k => R ⟨k.1 + 1, Nat.succ_lt_succ k.2⟩) ω

theorem anySlotWins_of_win {n : Nat} :
    ∀ (M : Nat) (R : Fin M → Spec.FinGame n) (ω : Fin n) (k : Fin M),
      (R k).win ω = true → anySlotWins M R ω = true
  | 0, _, _, k, _ => absurd k.2 (Nat.not_lt_zero _)
  | M + 1, R, ω, ⟨0, _⟩, h => by
    show ((R ⟨0, Nat.succ_pos M⟩).win ω ||
      anySlotWins M (fun k => R ⟨k.1 + 1, Nat.succ_lt_succ k.2⟩) ω) = true
    rw [h]
    rfl
  | M + 1, R, ω, ⟨k + 1, hk⟩, h => by
    show ((R ⟨0, Nat.succ_pos M⟩).win ω ||
      anySlotWins M (fun k => R ⟨k.1 + 1, Nat.succ_lt_succ k.2⟩) ω) = true
    rw [anySlotWins_of_win M (fun k => R ⟨k.1 + 1, Nat.succ_lt_succ k.2⟩) ω
      ⟨k, Nat.lt_of_succ_lt_succ hk⟩ h]
    exact Bool.or_true _

/-- **Union bound over a family of games.** If each of `M` games has probability at most `ε`,
    the event that one of them is won has probability at most `M · ε`. -/
theorem anySlotWins_bound {n : Nat} (hPos : 0 < n) {ε : Spec.RatBound} :
    ∀ (M : Nat) (R : Fin M → Spec.FinGame n),
      (∀ k, Spec.GameBound (R k).winProb ε) →
      Spec.GameBound (Spec.FinGame.mk hPos (anySlotWins M R)).winProb (Spec.RatBound.scale M ε)
  | 0, _, _ =>
    Spec.RatBound.le_trans
      (Spec.FinGame.bound_zero_of_forall_lose (Spec.FinGame.mk hPos (anySlotWins 0 _))
        (fun _ => rfl))
      (by
        show 0 * ε.den ≤ 0 * ε.num * 1
        rw [Nat.zero_mul, Nat.zero_mul, Nat.zero_mul]
        exact Nat.le_refl 0)
  | M + 1, R, h => by
    have h1 := Spec.event_le_two_reductions (Spec.FinGame.mk hPos (anySlotWins (M + 1) R))
      (R ⟨0, Nat.succ_pos M⟩)
      (Spec.FinGame.mk hPos (anySlotWins M (fun k => R ⟨k.1 + 1, Nat.succ_lt_succ k.2⟩)))
      (fun ω hw => by
        have hw' : ((R ⟨0, Nat.succ_pos M⟩).win ω ||
            anySlotWins M (fun k => R ⟨k.1 + 1, Nat.succ_lt_succ k.2⟩) ω) = true := hw
        cases h0 : (R ⟨0, Nat.succ_pos M⟩).win ω
        · rw [h0] at hw'
          exact .inr hw'
        · exact .inl rfl)
    have h2 := anySlotWins_bound hPos M (fun k => R ⟨k.1 + 1, Nat.succ_lt_succ k.2⟩)
      (fun k => h _)
    refine Spec.RatBound.le_trans h1
      (Spec.RatBound.le_trans (Spec.RatBound.add_le_add (h _) h2) ?_)
    show (ε.num * ε.den + M * ε.num * ε.den) * ε.den ≤ (M + 1) * ε.num * (ε.den * ε.den)
    rw [← Nat.add_mul, Nat.mul_assoc, Nat.succ_mul, Nat.add_comm (M * ε.num) ε.num]
    exact Nat.le_refl _

/-- **Hardness of the subset-cover game** for the signer of `suite`, `params` with keys uniform
    on `KeyOk`, against adversaries with programs in `𝒜` making at most `qHash` hash and `qSign`
    signing queries. -/
@[expose] def ExecSubsetCoverHard
    (𝒜 : (PqPublicKey → ProdAdaptiveTree (List UInt8 × PqHashSig)) → Prop)
    (suite : TweakableHashSuite) (params : PqHashParams) (KeyOk : PqSecretKey → Prop)
    (qHash qSign : Nat) (ε : Spec.RatBound) : Prop :=
  ∀ (n nK nA : Nat) (hPos : 0 < n) (π : Spec.CoinSplit n nK nA) (keygen : Fin nK → PqSecretKey),
    Spec.UniformOn KeyOk keygen →
    ∀ B : Fin nA → SeedWithheldOracleAdv (List UInt8 × PqHashSig) qHash qSign,
      (∀ a : Fin nA, 𝒜 (B a).run) →
      Spec.GameBound (execSubsetCoverGame hPos suite params (fun ω => keygen (π.chal ω))
        (fun ω => B (π.advc ω))).winProb ε

/-- **Hardness of the keyed path-collision game**, same quantification. -/
@[expose] def ExecKeyedPathCollisionHard
    (𝒜 : (PqPublicKey → ProdAdaptiveTree (Option SmDtTcrSubmission)) → Prop)
    (suite : TweakableHashSuite) (params : PqHashParams) (KeyOk : PqSecretKey → Prop)
    (qHash qSign : Nat) (ε : Spec.RatBound) : Prop :=
  ∀ (n nK nA : Nat) (hPos : 0 < n) (π : Spec.CoinSplit n nK nA) (keygen : Fin nK → PqSecretKey),
    Spec.UniformOn KeyOk keygen →
    ∀ B : Fin nA → SeedWithheldOracleAdv (Option SmDtTcrSubmission) qHash qSign,
      (∀ a : Fin nA, 𝒜 (B a).run) →
      Spec.GameBound (execKeyedPathCollisionGame hPos suite params (fun ω => keygen (π.chal ω))
        (fun ω => B (π.advc ω))).winProb ε

/-- **Hardness of the keyed secret-preimage game**, same quantification. -/
@[expose] def ExecKeyedSecretPreimageHard
    (𝒜 : (PqPublicKey → ProdAdaptiveTree (Option SmDtPreSubmission)) → Prop)
    (suite : TweakableHashSuite) (params : PqHashParams) (KeyOk : PqSecretKey → Prop)
    (qHash qSign : Nat) (ε : Spec.RatBound) : Prop :=
  ∀ (n nK nA : Nat) (hPos : 0 < n) (π : Spec.CoinSplit n nK nA) (keygen : Fin nK → PqSecretKey),
    Spec.UniformOn KeyOk keygen →
    ∀ B : Fin nA → SeedWithheldOracleAdv (Option SmDtPreSubmission) qHash qSign,
      (∀ a : Fin nA, 𝒜 (B a).run) →
      Spec.GameBound (execKeyedSecretPreimageGame hPos suite params
        (fun ω => keygen (π.chal ω)) (fun ω => B (π.advc ω))).winProb ε

/-- **EUF-CMA bound by three games played without the secret key.** The experiment draws the
    key from the challenger coordinate of the coin, uniformly on `KeyOk`, and the forger from
    the adversary coordinate. The reduction adversaries are the forger itself,
    `execCollisionReductionAdv params slot` and `execPreimageReductionAdv params slot`: programs
    that receive the public key and query the hash and the latched signer, with the query
    budgets in their types. If the classes `𝒜I`, `𝒜T`, `𝒜P` contain them and the three games are
    hard against those classes at those budgets, the forger wins with probability at most
    `εI + prodPathTargetCount params qSign · εT + prodPreCandidateCount params · εP`.

    The collision and preimage games are keyed: their targets are the signer's hash inputs.
    The hypotheses are false for classes that contain exhaustive search, and for a suite whose
    hash is constant (`Tests/SigningTeeth`). -/
theorem jorts_baggy_closed_euf_cma_keyed_target_bound {n nK nA qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16)
    (π : Spec.CoinSplit n nK nA)
    (keygen : Fin nK → PqSecretKey) {KeyOk : PqSecretKey → Prop}
    (hKey : Spec.UniformOn KeyOk keygen)
    (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    {𝒜I : (PqPublicKey → ProdAdaptiveTree (List UInt8 × PqHashSig)) → Prop}
    {𝒜T : (PqPublicKey → ProdAdaptiveTree (Option SmDtTcrSubmission)) → Prop}
    {𝒜P : (PqPublicKey → ProdAdaptiveTree (Option SmDtPreSubmission)) → Prop}
    (hAI : ∀ a : Fin nA, 𝒜I (adv a).run)
    (hAT : ∀ (slot : Nat) (a : Fin nA), 𝒜T (execCollisionReductionAdv params slot (adv a)).run)
    (hAP : ∀ (slot : Nat) (a : Fin nA), 𝒜P (execPreimageReductionAdv params slot (adv a)).run)
    {εI εT εP : Spec.RatBound}
    (hI : ExecSubsetCoverHard 𝒜I suite params KeyOk qHash qSign εI)
    (hT : ExecKeyedPathCollisionHard 𝒜T suite params KeyOk
      (qHash + prodTcrReductionHashBudget params) qSign εT)
    (hP : ExecKeyedSecretPreimageHard 𝒜P suite params KeyOk
      (qHash + (1 + prodXofHashBudget params)) qSign εP) :
    Spec.GameBound
      (ExecEufCmaGame hPos suite params (fun ω => keygen (π.chal ω))
        (fun ω => adv (π.advc ω))).winProb
      ((εI.add (Spec.RatBound.scale (prodPathTargetCount params qSign) εT)).add
        (Spec.RatBound.scale (prodPreCandidateCount params) εP)) := by
  let tcrGames : Fin (prodPathTargetCount params qSign) → Spec.FinGame n := fun slot =>
    execKeyedPathCollisionGame hPos suite params (fun ω => keygen (π.chal ω))
      (fun ω => execCollisionReductionAdv params slot.val (adv (π.advc ω)))
  let preGames : Fin (prodPreCandidateCount params) → Spec.FinGame n := fun slot =>
    execKeyedSecretPreimageGame hPos suite params (fun ω => keygen (π.chal ω))
      (fun ω => execPreimageReductionAdv params slot.val (adv (π.advc ω)))
  exact Spec.event_le_three_reductions
    (ExecEufCmaGame hPos suite params (fun ω => keygen (π.chal ω)) (fun ω => adv (π.advc ω)))
    (execSubsetCoverGame hPos suite params (fun ω => keygen (π.chal ω))
      (fun ω => (adv (π.advc ω)).toOracleAdv))
    (Spec.FinGame.mk hPos (anySlotWins _ tcrGames))
    (Spec.FinGame.mk hPos (anySlotWins _ preGames))
    (fun ω hWin => by
      rcases execEufCma_win_reduction_adversary_wins hPos suite params hw
          (fun ω => keygen (π.chal ω)) (fun ω => adv (π.advc ω)) ω hWin with h | ⟨slot, h⟩ | ⟨slot, h⟩
      · exact .inl h
      · exact .inr (.inl (anySlotWins_of_win _ tcrGames ω slot h))
      · exact .inr (.inr (anySlotWins_of_win _ preGames ω slot h)))
    (hI n nK nA hPos π keygen hKey (fun a => (adv a).toOracleAdv) hAI)
    (anySlotWins_bound hPos _ tcrGames (fun slot =>
      hT n nK nA hPos π keygen hKey (fun a => execCollisionReductionAdv params slot.val (adv a))
        (hAT slot.val)))
    (anySlotWins_bound hPos _ preGames (fun slot =>
      hP n nK nA hPos π keygen hKey (fun a => execPreimageReductionAdv params slot.val (adv a))
        (hAP slot.val)))

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

/-- **Key-generation hop under PRF hardness.** Let `D` be an oracle distinguisher on the
    adversary coordinate of the split `π`, and let the challenger coordinate carry a uniform
    key and an independent uniform function (`sample`). The simulation hypotheses are:
    `hReal`, on every coin the experiment under `keygenReal` has the verdict of `D` with oracle
    access to `prf` under the sampled key; `hIdeal`, the experiment under `keygenIdeal` has the
    verdict of `D` with oracle access to the sampled function. Then PRF hardness of `prf`
    against a class `𝒜` containing the programs of `D` bounds the real experiment by the three
    reductions of the ideal one plus `εPrf`.

    `D` is the experiment with its key derivation replaced by oracle calls; no such `D` is
    constructed in this library, so `hReal` and `hIdeal` are open obligations. -/
theorem jorts_baggy_closed_euf_cma_keygen_hop {n nC nA qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16)
    (keygenReal keygenIdeal : Fin n → PqSecretKey)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign)
    (prf : Spec.Bytes → Spec.Bytes → Spec.Bytes) (keyLen inLen outLen qPrf : Nat)
    {𝒜 : Spec.Code Spec.byteOracleIface Bool → Prop}
    {εPrf : Spec.RatBound} (hPrf : Spec.PrfHard 𝒜 prf keyLen inLen outLen qPrf εPrf)
    (π : Spec.CoinSplit n nC nA)
    (sample : Fin nC → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hU : Spec.UniformOn (Spec.PrfSampleOk keyLen inLen outLen) sample)
    (D : Fin nA → Spec.Code Spec.byteOracleIface Bool) (hD : ∀ a : Fin nA, 𝒜 (D a))
    (hReal : ∀ ω : Fin n, (ExecEufCmaGame hPos suite params keygenReal adv).win ω =
      (Spec.prfRealGame hPos prf qPrf (fun ω => (sample (π.chal ω)).1)
        (fun ω => D (π.advc ω))).win ω)
    (hIdeal : ∀ ω : Fin n, (ExecEufCmaGame hPos suite params keygenIdeal adv).win ω =
      (Spec.prfIdealGame hPos qPrf (fun ω => (sample (π.chal ω)).2)
        (fun ω => D (π.advc ω))).win ω) :
    Spec.GameBound (ExecEufCmaGame hPos suite params keygenReal adv).winProb
      (((execEufCmaItsrReduction hPos suite params hw keygenIdeal adv).winProb.add
        ((execEufCmaTcrReduction hPos suite params hw keygenIdeal adv).winProb.add
          (execEufCmaPreReduction hPos suite params hw keygenIdeal adv).winProb)).add εPrf) := by
  have hAdv : Spec.GameBound
      (Spec.AdvDist (ExecEufCmaGame hPos suite params keygenReal adv)
        (ExecEufCmaGame hPos suite params keygenIdeal adv)) εPrf := by
    rw [Spec.FinGame.ext_win hReal, Spec.FinGame.ext_win hIdeal]
    exact hPrf n nC nA hPos π sample hU D hD
  exact Spec.RatBound.le_trans
    (winProb_le_add_advDist (ExecEufCmaGame hPos suite params keygenReal adv)
      (ExecEufCmaGame hPos suite params keygenIdeal adv))
    (Spec.RatBound.add_le_add
      (jorts_baggy_closed_euf_cma_same_trace_classification hPos suite params hw keygenIdeal adv)
      hAdv)

/-! ## §6. Concrete PRF Keygen Distinguisher & `ExecEufCmaReductionEmbedding` into `Spec.Assumptions` -/

/-- Derive `(skSeed, skPrf, pkSeed)` from three domain-separated oracle calls `[0], [1], [2]`. -/
def keygenFromByteOracle (f : Spec.Bytes → Spec.Bytes) : PqSecretKey :=
  ⟨f [0], f [1], f [2]⟩

theorem keygenFromByteOracle_eq (f : Spec.Bytes → Spec.Bytes) :
    keygenFromByteOracle f = ⟨f [0], f [1], f [2]⟩ := by unfold keygenFromByteOracle; rfl

/-- Explicit 3-query `Within 3` oracle distinguisher simulating `ExecEufCmaGame` under PRF-derived
    vs random-function-derived secret keys, discharging `hReal` and `hIdeal` of
    `jorts_baggy_closed_euf_cma_keygen_hop`. -/
def execKeygenDistinguisher {qHash qSign : Nat} (suite : TweakableHashSuite)
    (params : PqHashParams) (A : SeedWithheldEufCmaAdv qHash qSign) :
    Spec.Code Spec.byteOracleIface Bool :=
  .call [0] (fun skSeed =>
    .call [1] (fun skPrf =>
      .call [2] (fun pkSeed =>
        .ret (prodEufCmaWin suite params
          (execEufCmaOutcome true suite params
            (fun _ : Fin 1 => ⟨skSeed, skPrf, pkSeed⟩) (fun _ => A) ⟨0, Nat.one_pos⟩)))))

theorem execKeygenDistinguisher_within {qHash qSign : Nat} (suite : TweakableHashSuite)
    (params : PqHashParams) (A : SeedWithheldEufCmaAdv qHash qSign) :
    Spec.Within 3 (execKeygenDistinguisher suite params A) := by
  unfold execKeygenDistinguisher
  exact .call (E := Spec.byteOracleIface) [0] _ (fun _ => .call (E := Spec.byteOracleIface) [1] _ (fun _ => .call (E := Spec.byteOracleIface) [2] _ (fun _ => .ret 0 _)))

private theorem execKeygenDistinguisher_play {qHash qSign : Nat} (suite : TweakableHashSuite)
    (params : PqHashParams) (A : SeedWithheldEufCmaAdv qHash qSign)
    (f : Spec.Bytes → Spec.Bytes) {qPrf : Nat} (hq : 3 ≤ qPrf) :
    (Spec.Code.play (Spec.budgetedFunOracle f qPrf)
      (execKeygenDistinguisher suite params A) 0).1 =
      prodEufCmaWin suite params
        (execEufCmaOutcome true suite params
          (fun _ : Fin 1 => keygenFromByteOracle f) (fun _ => A) ⟨0, Nat.one_pos⟩) := by
  have h0 : 0 < qPrf := by omega
  have h1 : 1 < qPrf := by omega
  have h2 : 2 < qPrf := by omega
  have s0 : Spec.budgetedFunOracle f qPrf 0 [0] = (f [0], 1) := by rw [Spec.budgetedFunOracle.public_eqs, ite_eq_left h0]
  have s1 : Spec.budgetedFunOracle f qPrf 1 [1] = (f [1], 2) := by rw [Spec.budgetedFunOracle.public_eqs, ite_eq_left h1]
  have s2 : Spec.budgetedFunOracle f qPrf 2 [2] = (f [2], 3) := by rw [Spec.budgetedFunOracle.public_eqs, ite_eq_left h2]
  unfold execKeygenDistinguisher
  rw [Spec.Code.play_call, s0, Spec.Code.play_call, s1, Spec.Code.play_call, s2]
  simp only [Spec.Code.play_ret, keygenFromByteOracle_eq]

/-- **Concrete Key-Generation Hop Theorem (`0` Open Simulation Obligations).** Instantiates
    `jorts_baggy_closed_euf_cma_keygen_hop` with `execKeygenDistinguisher` (`Within 3`) for any
    `qPrf ≥ 3`. -/
theorem jorts_baggy_closed_euf_cma_keygen_hop_concrete {n nC nA qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16)
    (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    (prf : Spec.Bytes → Spec.Bytes → Spec.Bytes) (keyLen inLen outLen qPrf : Nat)
    (hqPrf : 3 ≤ qPrf)
    {𝒜 : Spec.Code Spec.byteOracleIface Bool → Prop}
    {εPrf : Spec.RatBound} (hPrf : Spec.PrfHard 𝒜 prf keyLen inLen outLen qPrf εPrf)
    (π : Spec.CoinSplit n nC nA)
    (sample : Fin nC → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hU : Spec.UniformOn (Spec.PrfSampleOk keyLen inLen outLen) sample)
    (hD : ∀ a : Fin nA, 𝒜 (execKeygenDistinguisher suite params (adv a))) :
    let keygenReal : Fin n → PqSecretKey := fun ω => keygenFromByteOracle (prf (sample (π.chal ω)).1)
    let keygenIdeal : Fin n → PqSecretKey := fun ω => keygenFromByteOracle (sample (π.chal ω)).2
    let advCoin : Fin n → SeedWithheldEufCmaAdv qHash qSign := fun ω => adv (π.advc ω)
    Spec.GameBound (ExecEufCmaGame hPos suite params keygenReal advCoin).winProb
      (((execEufCmaItsrReduction hPos suite params hw keygenIdeal advCoin).winProb.add
        ((execEufCmaTcrReduction hPos suite params hw keygenIdeal advCoin).winProb.add
          (execEufCmaPreReduction hPos suite params hw keygenIdeal advCoin).winProb)).add εPrf) := by
  intro keygenReal keygenIdeal advCoin
  exact jorts_baggy_closed_euf_cma_keygen_hop hPos suite params hw keygenReal keygenIdeal advCoin
    prf keyLen inLen outLen qPrf hPrf π sample hU
    (fun a => execKeygenDistinguisher suite params (adv a)) hD
    (fun ω => by
      rw [Spec.prfRealGame.public_eqs]
      exact (execKeygenDistinguisher_play suite params (adv (π.advc ω))
        (prf (sample (π.chal ω)).1) hqPrf).symm)
    (fun ω => by
      rw [Spec.prfIdealGame.public_eqs]
      exact (execKeygenDistinguisher_play suite params (adv (π.advc ω))
        (sample (π.chal ω)).2 hqPrf).symm)

/-- **Constructive Reduction Embedding from `ExecEufCmaGame` into `Spec.Assumptions`.**
    Witnesses that every winning coin of the executable latched EUF-CMA experiment lifts to a
    winning coin of one of `Spec.itsrGame`, `Spec.smDtTcrGame`, or `Spec.smDtPreGame` under
    uniform challenger samplers (`Spec.UniformOn`) and seed-withheld reduction adversaries in
    query-bounded classes `𝒜I`, `𝒜T`, `𝒜P`. -/
structure ExecEufCmaReductionEmbedding {n qHash qSign : Nat} (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (keygen : Fin n → PqSecretKey)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) : Type 1 where
  hmsg : Spec.Bytes → Spec.Bytes → List Nat
  th : Spec.Bytes → Spec.Bytes → Spec.Bytes → Spec.Bytes
  randLen : Nat
  seedLen : Nat
  inputLen : Nat
  qItsr : Nat
  qTcr : Nat
  qPre : Nat
  𝒜I : Spec.Code Spec.byteOracleIface (Spec.Bytes × Spec.Bytes) → Prop
  𝒜T : Spec.Code Spec.targetIface Spec.TargetBreak → Prop
  𝒜P : Spec.Code Spec.targetIface Spec.TargetBreak → Prop
  nCi : Nat
  nAi : Nat
  nCt : Nat
  nAt : Nat
  nCp : Nat
  nAp : Nat
  πi : Spec.CoinSplit n nCi nAi
  πt : Spec.CoinSplit n nCt nAt
  πp : Spec.CoinSplit n nCp nAp
  rand : Fin nCi → List Spec.Bytes
  hRand : Spec.UniformOn (Spec.ItsrSampleOk randLen qItsr) rand
  seed : Fin nCt → Spec.Bytes
  hSeed : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seed
  sample : Fin nCp → Spec.Bytes × List Spec.Bytes
  hSample : Spec.UniformOn (Spec.SmDtPreSampleOk seedLen inputLen qPre) sample
  advI : Fin nAi → Spec.Code Spec.byteOracleIface (Spec.Bytes × Spec.Bytes)
  hAdvI : ∀ a, 𝒜I (advI a)
  advT : Fin nAt → Spec.Code Spec.targetIface Spec.TargetBreak
  hAdvT : ∀ a, 𝒜T (advT a)
  advP : Fin nAp → Spec.Code Spec.targetIface Spec.TargetBreak
  hAdvP : ∀ a, 𝒜P (advP a)
  extract_win : ∀ ω : Fin n,
    (ExecEufCmaGame hPos suite params keygen adv).win ω = true →
    (Spec.itsrGame hPos hmsg qItsr (fun ω i => (rand (πi.chal ω)).getD i [])
      (fun ω => advI (πi.advc ω))).win ω = true ∨
    (Spec.smDtTcrGame hPos th qTcr (fun ω => seed (πt.chal ω))
      (fun ω => advT (πt.advc ω))).win ω = true ∨
    (Spec.smDtPreGame hPos th qPre (fun ω => (sample (πp.chal ω)).1)
      (fun ω i => (sample (πp.chal ω)).2.getD i []) (fun ω => advP (πp.advc ω))).win ω = true

/-- **End-to-End `ExecEufCmaGame → Spec.Assumptions` Forger Bound.** Any
    `ExecEufCmaReductionEmbedding` composes with `Spec.ItsrHard`, `Spec.SmDtTcrHard`, and
    `Spec.SmDtPreHard` via `Spec.hashSig_forger_bound` to bound `ExecEufCmaGame.winProb`. -/
theorem ExecEufCmaReductionEmbedding.forger_bound {n qHash qSign : Nat} {hPos : 0 < n}
    {suite : TweakableHashSuite} {params : PqHashParams}
    {keygen : Fin n → PqSecretKey}
    {adv : Fin n → SeedWithheldEufCmaAdv qHash qSign}
    (E : ExecEufCmaReductionEmbedding hPos suite params keygen adv)
    {εItsr εTcr εPre : Spec.RatBound}
    (hItsr : Spec.ItsrHard E.𝒜I E.hmsg E.randLen E.qItsr εItsr)
    (hTcr : Spec.SmDtTcrHard E.𝒜T E.th E.seedLen E.qTcr εTcr)
    (hPre : Spec.SmDtPreHard E.𝒜P E.th E.seedLen E.inputLen E.qPre εPre) :
    Spec.GameBound (ExecEufCmaGame hPos suite params keygen adv).winProb
      ((εItsr.add εTcr).add εPre) :=
  Spec.hashSig_forger_bound (ExecEufCmaGame hPos suite params keygen adv)
    hItsr hTcr hPre E.πi E.πt E.πp E.rand E.hRand E.seed E.hSeed E.sample E.hSample
    E.advI E.hAdvI E.advT E.hAdvT E.advP E.hAdvP E.extract_win

/-! ### §6.1 Concrete Non-Vacuous Instance of `ExecEufCmaReductionEmbedding` over 256 Uniform Keys -/

private def zero32 : List UInt8 := List.replicate 32 0x00
private def crumb32 : List UInt8 := List.replicate 32 0x1B

private def seedZeroBadInputs : List (List UInt8) :=
  ((List.range 255).map (fun k =>
    thPreimage tagPrf [] ⟨0, 0, .wotsPrf, 0, 0, 0⟩ [[UInt8.ofNat (k + 1)]])) ++
  [thPreimage tagThF [] ⟨0, 0, .wotsHash, 0, 0, 0⟩ [zero32],
   thPreimage tagThF [] ⟨0, 0, .wotsHash, 0, 0, 1⟩ [zero32],
   thPreimage tagThF [] ⟨0, 0, .wotsHash, 0, 0, 2⟩ [zero32],
   thPreimage tagThTl [] ⟨0, 0, .wotsPk, 0, 0, 0⟩ (zero32 :: List.replicate 127 crumb32),
   thPreimage tagThH [] ⟨0, 0, .tree, 0, 1, 0⟩ [zero32, crumb32]]

/-- Uniform 256-key challenger sampler placing the 1-byte secret strictly in `skSeed`. -/
def seed256Keygen (ω : Fin 256) : PqSecretKey :=
  ⟨[UInt8.ofNat ω.1], [], []⟩

theorem seed256Keygen_uniform :
    Spec.UniformOn (fun sk : PqSecretKey => sk.skSeed.length = 1 ∧ sk.skPrf = [] ∧ sk.pkSeed = [])
      seed256Keygen where
  mem _ := ⟨rfl, rfl, rfl⟩
  injective i j h := by
    injection h with hS _ _
    exact Spec.uniformOn_byte1Seed.injective i j (by simpa only [Spec.byte1SeedSampler.public_eqs] using hS)
  surjective sk hSk := by
    obtain ⟨h1, h2, h3⟩ := hSk
    obtain ⟨i, hi⟩ := Spec.uniformOn_byte1Seed.surjective sk.skSeed h1
    refine ⟨i, ?_⟩
    cases sk
    dsimp only at hi h2 h3
    rw [← hi, h2, h3, Spec.byte1SeedSampler.public_eqs]
    rfl

/-- Seed-withheld `0`-query forger guessing `prodToyForgery` on message `[]`. -/
def seedWithheldZeroGuessAdv : SeedWithheldEufCmaAdv 0 0 where
  run := fun _ => .pure ([], prodToyForgery)
  bounded := fun _ => trivial

private theorem tagPrf_ne_others :
    tagPrf ≠ tagThF ∧ tagPrf ≠ tagThTl ∧ tagPrf ≠ tagThH ∧
    tagThF ≠ tagThTl ∧ tagThF ≠ tagThH ∧ tagThTl ≠ tagThH := by
  simp only [tagPrf.public_eqs, tagThF.public_eqs, tagThTl.public_eqs, tagThH.public_eqs]
  decide +kernel

private theorem zero32_ne_crumb32 : zero32 ≠ crumb32 := by decide

private theorem seedZeroRootSuite_not_bad_of_not_prf0 {role : List UInt8} {adrs : HashAdrs}
    {args : List (List UInt8)}
    (hNoPrf : role = tagPrf → adrs = ⟨0, 0, .wotsPrf, 0, 0, 0⟩ → args = [[0x00]])
    (hNoF : role = tagThF → args ≠ [zero32])
    (hNoTl : role = tagThTl → args ≠ (zero32 :: List.replicate 127 crumb32))
    (hNoH : role = tagThH → args ≠ [zero32, crumb32]) :
    thPreimage role [] adrs args ∉ seedZeroBadInputs := by
  intro hMem
  unfold seedZeroBadInputs at hMem
  rcases List.mem_append.mp hMem with hPrfList | hRest
  · obtain ⟨k, hk, hEq⟩ := List.mem_map.mp hPrfList
    obtain ⟨hRole, _, hAdrs, hArgs⟩ := thPreimage_injective hEq.symm
    have hArgs0 := hNoPrf hRole hAdrs
    rw [hArgs0] at hArgs
    injection hArgs with hHead _
    injection hHead with hByte _
    have hNat := congrArg UInt8.toNat hByte
    have hkLt : k < 255 := List.mem_range.mp hk
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega : k + 1 < 256)] at hNat
    change 0 = k + 1 at hNat
    omega
  · rcases List.mem_cons.mp hRest with hEq | hRest1
    · obtain ⟨hR, _, _, hA⟩ := thPreimage_injective hEq
      exact hNoF hR hA
    · rcases List.mem_cons.mp hRest1 with hEq | hRest2
      · obtain ⟨hR, _, _, hA⟩ := thPreimage_injective hEq
        exact hNoF hR hA
      · rcases List.mem_cons.mp hRest2 with hEq | hRest3
        · obtain ⟨hR, _, _, hA⟩ := thPreimage_injective hEq
          exact hNoF hR hA
        · rcases List.mem_cons.mp hRest3 with hEq | hRest4
          · obtain ⟨hR, _, _, hA⟩ := thPreimage_injective hEq
            exact hNoTl hR hA
          · rcases List.mem_cons.mp hRest4 with hEq | hNil
            · obtain ⟨hR, _, _, hA⟩ := thPreimage_injective hEq
              exact hNoH hR hA
            · nomatch hNil

private theorem seedZeroRootSuite_thCall_crumb {role : List UInt8} {adrs : HashAdrs}
    {args : List (List UInt8)}
    (hNoPrf : role = tagPrf → adrs = ⟨0, 0, .wotsPrf, 0, 0, 0⟩ → args = [[0x00]])
    (hNoF : role = tagThF → args ≠ [zero32])
    (hNoTl : role = tagThTl → args ≠ (zero32 :: List.replicate 127 crumb32))
    (hNoH : role = tagThH → args ≠ [zero32, crumb32]) :
    thCall seedZeroRootSuite role [] adrs args = crumb32 := by
  rw [thCall_eq, seedZeroRootSuite_rawHash_eq]
  exact ite_eq_right (seedZeroRootSuite_not_bad_of_not_prf0 hNoPrf hNoF hNoTl hNoH)

private theorem seedZeroRootSuite_chain3_crumb (kp chain : Nat) :
    wotsChainSteps seedZeroRootSuite [] 0 0 kp chain 0 3 crumb32 = crumb32 := by
  have hStep : ∀ s : Nat,
      thChainF seedZeroRootSuite [] ⟨0, 0, .wotsHash, UInt32.ofNat kp, UInt32.ofNat chain,
        UInt32.ofNat s⟩ crumb32 = crumb32 := fun s => by
    rw [thChainF_eq]
    exact seedZeroRootSuite_thCall_crumb
      (fun h => absurd h tagPrf_ne_others.1.symm)
      (fun _ h => zero32_ne_crumb32 (by injection h with h1; exact h1.symm))
      (fun h => absurd h tagPrf_ne_others.2.2.2.1)
      (fun h => absurd h tagPrf_ne_others.2.2.2.2.1)
  simp only [wotsChainSteps_succ, hStep, wotsChainSteps_zero]

private theorem seedZeroRootSuite_chain3_zero :
    wotsChainSteps seedZeroRootSuite [] 0 0 0 0 0 3 zero32 = zero32 := by
  have h0 : thChainF seedZeroRootSuite [] ⟨0, 0, .wotsHash, 0, 0, 0⟩ zero32 = zero32 := by
    rw [thChainF_eq, thCall_eq, seedZeroRootSuite_rawHash_eq]
    exact ite_eq_left (List.mem_append_right _ (List.Mem.head _))
  have h1 : thChainF seedZeroRootSuite [] ⟨0, 0, .wotsHash, 0, 0, 1⟩ zero32 = zero32 := by
    rw [thChainF_eq, thCall_eq, seedZeroRootSuite_rawHash_eq]
    exact ite_eq_left (List.mem_append_right _ (List.Mem.tail _ (List.Mem.head _)))
  have h2 : thChainF seedZeroRootSuite [] ⟨0, 0, .wotsHash, 0, 0, 2⟩ zero32 = zero32 := by
    rw [thChainF_eq, thCall_eq, seedZeroRootSuite_rawHash_eq]
    exact ite_eq_left (List.mem_append_right _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  rw [wotsChainSteps_succ]; change wotsChainSteps _ _ _ _ _ _ 1 2 (thChainF _ _ ⟨0, 0, .wotsHash, 0, 0, 0⟩ zero32) = zero32
  rw [h0, wotsChainSteps_succ]; change wotsChainSteps _ _ _ _ _ _ 2 1 (thChainF _ _ ⟨0, 0, .wotsHash, 0, 0, 1⟩ zero32) = zero32
  rw [h1, wotsChainSteps_succ]; change wotsChainSteps _ _ _ _ _ _ 3 0 (thChainF _ _ ⟨0, 0, .wotsHash, 0, 0, 2⟩ zero32) = zero32
  rw [h2, wotsChainSteps_zero]

private theorem range128_split : List.range 128 = 0 :: (List.range 127).map (· + 1) := by
  decide

private theorem derivePublicKey_seedZeroRootSuite (ω : Fin 256) :
    derivePublicKey seedZeroRootSuite prodToyStatefulParams (seed256Keygen ω) =
      if ω.1 = 0 then ⟨[], crumb32⟩ else ⟨[], zero32⟩ := by
  rw [prodToyStatefulParams.public_eqs]
  unfold derivePublicKey seed256Keygen
  dsimp only
  rw [computeXmssSubtreeRoot_eq, computeMerkleNode_succ, computeMerkleNode_zero,
    computeMerkleNode_zero]
  dsimp only
  have hKp1 : computeWotsPk seedZeroRootSuite ⟨4, 128, 1, 1, 0, 0, 1, true⟩
      ⟨[UInt8.ofNat ω.1], [], []⟩ 0 0 1 = crumb32 := by
    rw [computeWotsPk_eq]
    dsimp only
    have hBase1 : ∀ r : Nat,
        wotsSecretBase seedZeroRootSuite ⟨[UInt8.ofNat ω.1], [], []⟩ 0 0 1 r = crumb32 := fun r => by
      rw [wotsSecretBase_eq, thSecretPrf_eq]
      exact seedZeroRootSuite_thCall_crumb
        (fun _ hA => by
          have hKp := congrArg HashAdrs.keyPair hA
          nomatch hKp)
        (fun h => absurd h tagPrf_ne_others.1)
        (fun h => absurd h tagPrf_ne_others.2.1)
        (fun h => absurd h tagPrf_ne_others.2.2.1)
    have hMap1 : ((List.range 128).map fun r =>
        wotsChainSteps seedZeroRootSuite [] 0 0 1 r 0 3
          (wotsSecretBase seedZeroRootSuite ⟨[UInt8.ofNat ω.1], [], []⟩ 0 0 1 r)) =
        (List.range 128).map (fun _ => crumb32) := by
      refine List.map_congr_left (fun r _ => ?_)
      rw [hBase1 r, seedZeroRootSuite_chain3_crumb 1 r]
    rw [hMap1, thTweakTl_eq]
    exact seedZeroRootSuite_thCall_crumb
      (fun h => absurd h tagPrf_ne_others.2.1.symm)
      (fun h => absurd h tagPrf_ne_others.2.2.2.1.symm)
      (fun _ h => by
        injection h with hHead _
        exact zero32_ne_crumb32 hHead.symm)
      (fun h => absurd h tagPrf_ne_others.2.2.2.2.2)
  have hRPos : ∀ k ∈ List.range 127,
      wotsChainSteps seedZeroRootSuite [] 0 0 0 (k + 1) 0 3
        (wotsSecretBase seedZeroRootSuite ⟨[UInt8.ofNat ω.1], [], []⟩ 0 0 0 (k + 1)) = crumb32 := by
    intro k hk
    have hkLt : k < 127 := List.mem_range.mp hk
    have hBase : wotsSecretBase seedZeroRootSuite ⟨[UInt8.ofNat ω.1], [], []⟩ 0 0 0 (k + 1) =
        crumb32 := by
      rw [wotsSecretBase_eq, thSecretPrf_eq]
      exact seedZeroRootSuite_thCall_crumb
        (fun _ hA => by
          have hCh := congrArg (fun a => a.chainIdx.toNat) hA
          dsimp only at hCh
          rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 32)] at hCh
          change k + 1 = 0 at hCh
          omega)
        (fun h => absurd h tagPrf_ne_others.1)
        (fun h => absurd h tagPrf_ne_others.2.1)
        (fun h => absurd h tagPrf_ne_others.2.2.1)
    rw [hBase, seedZeroRootSuite_chain3_crumb 0 (k + 1)]
  have hTail127 : ((List.range 127).map (· + 1)).map (fun r =>
      wotsChainSteps seedZeroRootSuite [] 0 0 0 r 0 3
        (wotsSecretBase seedZeroRootSuite ⟨[UInt8.ofNat ω.1], [], []⟩ 0 0 0 r)) =
      List.replicate 127 crumb32 := by
    rw [List.map_map]
    have hEqC : List.map (fun k =>
        wotsChainSteps seedZeroRootSuite [] 0 0 0 (k + 1) 0 3
          (wotsSecretBase seedZeroRootSuite ⟨[UInt8.ofNat ω.1], [], []⟩ 0 0 0 (k + 1)))
        (List.range 127) = List.map (fun _ => crumb32) (List.range 127) :=
      List.map_congr_left hRPos
    exact hEqC.trans (by decide)
  by_cases hω0 : ω.1 = 0
  · rw [ite_eq_left hω0]
    have hB0 : UInt8.ofNat ω.1 = 0x00 := by rw [hω0]; rfl
    have hBase0 : wotsSecretBase seedZeroRootSuite ⟨[UInt8.ofNat ω.1], [], []⟩ 0 0 0 0 = crumb32 := by
      rw [hB0, wotsSecretBase_eq, thSecretPrf_eq]
      exact seedZeroRootSuite_thCall_crumb
        (fun _ _ => rfl)
        (fun h => absurd h tagPrf_ne_others.1)
        (fun h => absurd h tagPrf_ne_others.2.1)
        (fun h => absurd h tagPrf_ne_others.2.2.1)
    have hKp0 : computeWotsPk seedZeroRootSuite ⟨4, 128, 1, 1, 0, 0, 1, true⟩
        ⟨[UInt8.ofNat ω.1], [], []⟩ 0 0 0 = crumb32 := by
      rw [computeWotsPk_eq]
      dsimp only
      rw [range128_split, List.map_cons, hTail127, hBase0, seedZeroRootSuite_chain3_crumb 0 0,
        thTweakTl_eq]
      exact seedZeroRootSuite_thCall_crumb
        (fun h => absurd h tagPrf_ne_others.2.1.symm)
        (fun h => absurd h tagPrf_ne_others.2.2.2.1.symm)
        (fun _ h => by injection h with hHd _; exact zero32_ne_crumb32 hHd.symm)
        (fun h => absurd h tagPrf_ne_others.2.2.2.2.2)
    change PqPublicKey.mk [] (thNodeH seedZeroRootSuite [] ⟨0, 0, .tree, 0, 1, 0⟩
      (computeWotsPk seedZeroRootSuite ⟨4, 128, 1, 1, 0, 0, 1, true⟩ ⟨[UInt8.ofNat ω.1], [], []⟩ 0 0 0)
      (computeWotsPk seedZeroRootSuite ⟨4, 128, 1, 1, 0, 0, 1, true⟩ ⟨[UInt8.ofNat ω.1], [], []⟩ 0 0 1)) = _
    rw [hKp0, hKp1, thNodeH_eq]
    congr 1
    exact seedZeroRootSuite_thCall_crumb
      (fun h => absurd h tagPrf_ne_others.2.2.1.symm)
      (fun h => absurd h tagPrf_ne_others.2.2.2.2.1.symm)
      (fun h => absurd h tagPrf_ne_others.2.2.2.2.2.symm)
      (fun _ h => by injection h with hHd _; exact zero32_ne_crumb32 hHd.symm)
  · rw [ite_eq_right hω0]
    have hBaseZ : wotsSecretBase seedZeroRootSuite ⟨[UInt8.ofNat ω.1], [], []⟩ 0 0 0 0 = zero32 := by
      rw [wotsSecretBase_eq, thSecretPrf_eq, thCall_eq, seedZeroRootSuite_rawHash_eq]
      refine ite_eq_left (List.mem_append_left _ (List.mem_map.mpr ⟨ω.1 - 1, ?_, ?_⟩))
      · exact List.mem_range.mpr (by have := ω.2; omega)
      · have hEq : ω.1 - 1 + 1 = ω.1 := by omega
        rw [hEq]; rfl
    have hKp0 : computeWotsPk seedZeroRootSuite ⟨4, 128, 1, 1, 0, 0, 1, true⟩
        ⟨[UInt8.ofNat ω.1], [], []⟩ 0 0 0 = zero32 := by
      rw [computeWotsPk_eq]
      dsimp only
      rw [range128_split, List.map_cons, hTail127, hBaseZ, seedZeroRootSuite_chain3_zero,
        thTweakTl_eq, thCall_eq, seedZeroRootSuite_rawHash_eq]
      exact ite_eq_left (List.mem_append_right _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
    change PqPublicKey.mk [] (thNodeH seedZeroRootSuite [] ⟨0, 0, .tree, 0, 1, 0⟩
      (computeWotsPk seedZeroRootSuite ⟨4, 128, 1, 1, 0, 0, 1, true⟩ ⟨[UInt8.ofNat ω.1], [], []⟩ 0 0 0)
      (computeWotsPk seedZeroRootSuite ⟨4, 128, 1, 1, 0, 0, 1, true⟩ ⟨[UInt8.ofNat ω.1], [], []⟩ 0 0 1)) = _
    rw [hKp0, hKp1, thNodeH_eq, thCall_eq, seedZeroRootSuite_rawHash_eq]
    congr 1
    exact ite_eq_left (List.mem_append_right _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))

private theorem verify_seedZeroRootSuite_crumb_pk :
    verifyProductionPqHashSig seedZeroRootSuite prodToyStatefulParams
      ⟨[], crumb32⟩ [] prodToyForgery = true := by
  rw [prodToyStatefulParams.public_eqs, prodToyForgery.public_eqs]
  exact seedZeroRootSuite_verifyToy_crumb

private theorem verify_seedZeroRootSuite_zero_pk :
    verifyProductionPqHashSig seedZeroRootSuite prodToyStatefulParams
      ⟨[], zero32⟩ [] prodToyForgery = false := by
  rw [prodToyStatefulParams.public_eqs, prodToyForgery.public_eqs]
  exact seedZeroRootSuite_verifyToy_zero

/-- Exact win characterization over all 256 uniform secret keys: the seed-withheld guess wins
    on coin `0` (`skSeed = [0x00]`) and loses on all 255 nonzero coins (`winProb = 1 / 256`). -/
theorem seedZeroRoot_execEufCmaGame_win_iff (ω : Fin 256) :
    (ExecEufCmaGame (by decide : 0 < 256) seedZeroRootSuite prodToyStatefulParams
      seed256Keygen (fun _ => seedWithheldZeroGuessAdv)).win ω = decide (ω.1 = 0) := by
  show prodEufCmaWin seedZeroRootSuite prodToyStatefulParams
    ⟨seed256Keygen ω, [], [], prodToyForgery⟩ = decide (ω.1 = 0)
  rw [prodEufCmaWin_eq, productionSigningLog_nil, derivePublicKey_seedZeroRootSuite]
  by_cases h0 : ω.1 = 0
  · rw [ite_eq_left h0, decide_eq_true h0, verify_seedZeroRootSuite_crumb_pk]
    rfl
  · rw [ite_eq_right h0, decide_eq_false h0, verify_seedZeroRootSuite_zero_pk]
    rfl

/-- Uniform `(256 * 256)`-coin keygen reading the second `Fin 256` coordinate (`advc` of
    `CoinSplit.prod 256 256`) as the 1-byte secret seed, paired with an independent 1-byte
    tweakable-hash seed on the first coordinate. -/
def seedPairKeygen (z : Fin (256 * 256)) : PqSecretKey :=
  seed256Keygen ((Spec.CoinSplit.prod 256 256).advc z)

theorem seedPair_execEufCmaGame_win_iff (z : Fin (256 * 256)) :
    (ExecEufCmaGame (by decide : 0 < 256 * 256) seedZeroRootSuite prodToyStatefulParams
      seedPairKeygen (fun _ => seedWithheldZeroGuessAdv)).win z =
      decide (((Spec.CoinSplit.prod 256 256).advc z).1 = 0) :=
  seedZeroRoot_execEufCmaGame_win_iff ((Spec.CoinSplit.prod 256 256).advc z)

/-- **First Concrete Non-Vacuous Instance of `ExecEufCmaReductionEmbedding`.**
    Connects `ExecEufCmaGame` (`winCount = 256 > 0` out of `65,536`, `winProb = 1 / 256 < 1`)
    directly to `Spec.Assumptions` (`byteIdxHmsg` + compressing `poly257Hash` under
    `WithinItsrQueries 1 1`, `WithinTcrQueries 2 1`, and `WithinPreQueries 2 1`) using three
    distinct `CoinSplit` factorizations of the `(256 * 256)` coin space. -/
def concreteExecEufCmaReductionEmbedding :
    ExecEufCmaReductionEmbedding (by decide : 0 < 256 * 256)
      seedZeroRootSuite prodToyStatefulParams
      seedPairKeygen (fun _ => seedWithheldZeroGuessAdv) where
  hmsg := Spec.byteIdxHmsg
  th := Spec.poly257Hash
  randLen := 1
  seedLen := 1
  inputLen := 1
  qItsr := 1
  qTcr := 1
  qPre := 1
  𝒜I := Spec.WithinItsrQueries 1 1
  𝒜T := Spec.WithinTcrQueries 2 1
  𝒜P := Spec.WithinPreQueries 2 1
  nCi := 256
  nAi := 256
  nCt := 256
  nAt := 256
  nCp := 256 * 256
  nAp := 1
  πi := Spec.CoinSplit.prod 256 256
  πt := Spec.CoinSplit.prod 256 256
  πp := Spec.CoinSplit.challengerOnly (256 * 256)
  rand := Spec.byte1ItsrSampler
  hRand := Spec.uniformOn_byte1Itsr
  seed := Spec.byte1SeedSampler
  hSeed := Spec.uniformOn_byte1Seed
  sample := Spec.byte1SeedAndPreSampler
  hSample := Spec.uniformOn_byte1SeedAndPre
  advI := fun _ => Spec.boundedItsrAdv Spec.byteIdxHmsg [0] [([1], [1])]
  hAdvI := fun _ => Spec.boundedItsrAdv_mem_within Spec.byteIdxHmsg [0] [([1], [1])] (Nat.le_refl 1)
  advT := fun _ => Spec.boundedTcrAdv Spec.poly257Hash [] [0, 0] [[0, 1]]
  hAdvT := fun _ => Spec.boundedTcrAdv_mem_within Spec.poly257Hash [] [0, 0] [[0, 1]] (Nat.le_refl 1)
  advP := fun _ => Spec.boundedPreAdv Spec.poly257Hash [] [[0x00]]
  hAdvP := fun _ => Spec.boundedPreAdv_mem_within Spec.poly257Hash [] [[0x00]] (Nat.le_refl 1)
  extract_win := fun z hWin => by
    rw [seedPair_execEufCmaGame_win_iff] at hWin
    have hz0 : ((Spec.CoinSplit.prod 256 256).advc z).1 = 0 := of_decide_eq_true hWin
    refine .inr (.inr ?_)
    have hSampleZ : Spec.byte1SeedAndPreSampler z =
        ([UInt8.ofNat ((Spec.CoinSplit.prod 256 256).chal z).1], [[0x00]]) := by
      rw [Spec.byte1SeedAndPreSampler_eq, hz0]
      rfl
    simp only [Spec.smDtPreGame.public_eqs, Spec.smDtPreRun.public_eqs, Spec.CoinSplit.challengerOnly_chal]
    rw [hSampleZ]
    exact Spec.boundedPreAdv_singleton_hidden_wins _ _ _ _ _ rfl

/-- **Unconditional Non-Vacuous `< 1` Forger Bound via `concreteExecEufCmaReductionEmbedding`.**
    Composes `concreteExecEufCmaReductionEmbedding.forger_bound` with our three proved
    query-bounded hardness theorems in `Spec.Assumptions` (`byteIdxHmsg_itsrHard_within`,
    `poly257Hash_smDtTcrHard_within`, `poly257Hash_smDtPreHard_within`) to obtain the proved
    non-trivial `6 / 256 < 1` bound, while coin `0` witnesses `ExecEufCmaGame.win = true`. -/
theorem concreteExecEufCma_forger_bound :
    (ExecEufCmaGame (by decide : 0 < 256 * 256) seedZeroRootSuite prodToyStatefulParams
      seedPairKeygen (fun _ => seedWithheldZeroGuessAdv)).win ⟨0, by decide⟩ = true ∧
    Spec.GameBound
      (ExecEufCmaGame (by decide : 0 < 256 * 256) seedZeroRootSuite prodToyStatefulParams
        seedPairKeygen (fun _ => seedWithheldZeroGuessAdv)).winProb
      (((⟨2, 256, by decide⟩ : Spec.RatBound).add ⟨2, 256, by decide⟩).add ⟨2, 256, by decide⟩) ∧
    (((⟨2, 256, by decide⟩ : Spec.RatBound).add ⟨2, 256, by decide⟩).add ⟨2, 256, by decide⟩).lt
      Spec.RatBound.one :=
  ⟨by rw [seedPair_execEufCmaGame_win_iff, Spec.CoinSplit.prod_advc_val]; rfl,
   concreteExecEufCmaReductionEmbedding.forger_bound
     (Spec.byteIdxHmsg_itsrHard_within 1 1)
     (Spec.poly257Hash_smDtTcrHard_within 2 1)
     (Spec.poly257Hash_smDtPreHard_within 2 1),
   by decide⟩

#verify_constructive
  Qsag.evalLatchedAdaptiveTree_log_increasing
  Qsag.evalLatchedAdaptiveTree_oneTime
  Qsag.evalLatchedAdaptiveTree_log_length
  Qsag.prodSignQuery_verifies
  Qsag.execEufCmaOutcome_oneTime
  Qsag.execEufCmaOutcome_queries_le
  Qsag.jorts_baggy_closed_euf_cma_same_trace_classification
  Qsag.evalLatchedAdaptiveTree_bind_signFree
  Qsag.evalLatchedAdaptiveTree_trackSignLog
  Qsag.execLatchedRun_collisionReduction
  Qsag.execLatchedRun_preimageReduction
  Qsag.execEufCma_win_reduction_adversary_wins
  Qsag.anySlotWins_bound
  Qsag.jorts_baggy_closed_euf_cma_keyed_target_bound
  Qsag.winProb_le_add_advDist
  Qsag.jorts_baggy_closed_euf_cma_keygen_hop
  Qsag.execKeygenDistinguisher_within
  Qsag.jorts_baggy_closed_euf_cma_keygen_hop_concrete
  Qsag.ExecEufCmaReductionEmbedding.forger_bound
  Qsag.seed256Keygen_uniform
  Qsag.seedZeroRoot_execEufCmaGame_win_iff
  Qsag.seedPair_execEufCmaGame_win_iff
  Qsag.concreteExecEufCma_forger_bound

end Qsag
end

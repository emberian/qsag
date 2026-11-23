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

Scope of §4–§6 and downstream multi-hop closure:
* §4 sets up the public-key / oracle games `execSubsetCoverGame`, `execKeyedPathCollisionGame`, and
  `execKeyedSecretPreimageGame`, and §5 proves the master-seed key-generation PRF hop.
* §6 constructs concrete `ExecEufCmaReductionEmbedding` instances directly into `Spec.Assumptions`
  (`Spec.itsrGame`, `Spec.smDtTcrGame`, `Spec.smDtPreGame`).
* `Qsag.Protocol.Signing.FullAdaptiveEufCma` eliminates the offline `hCand` restriction of §6.2 via
  an interactive `.target` / `.reveal` `Code Spec.targetIface Spec.TargetBreak` reduction for ALL
  unrestricted `pk`-dependent adaptive adversaries, proves strict subsumption on an explicit
  `pk`-dependent adaptive witness, and pairs load-bearing probability-`1` forgery refutations for
  disabling `checkTargetSum` and zeroing `HashAdrs` leaf/layer tweaks.
* `Qsag.Protocol.Signing.HulsingMultiHopReduction` and
  `Qsag.Protocol.Signing.ProductionJortsBaggyBounds` close the full multi-hop standard-model
  EUF-CMA game-playing reduction (`PRF_msg` randomizer hop, `PRF` secret-leaf hop, WOTS+C chain
  simulation hop, and interactive reductions into `Spec.itsrGame`, `Spec.smDtTcrGame`, and
  `Spec.smDtPreGame`) for arbitrary `TweakableHashSuite` and real `128`-bit production `Jorts`,
  `Baggy`, `Corduroy`, and `FIPS 205` `SLH-DSA` parameter sets.
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

/-- The win predicate of `execEufCmaGameWith` at a coin. -/
theorem execEufCmaGameWith_win {n qHash qSign : Nat} (latchOn : Bool) (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams) (keygen : Fin n → PqSecretKey)
    (adv : Fin n → SeedWithheldEufCmaAdv qHash qSign) (ω : Fin n) :
    (execEufCmaGameWith latchOn hPos suite params keygen adv).win ω =
      prodEufCmaWin suite params (execEufCmaOutcome latchOn suite params keygen adv ω) := by
  rfl

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

def zero32 : List UInt8 := List.replicate 32 0x00
def crumb32 : List UInt8 := List.replicate 32 0x1B

#export_eqns zero32
#export_eqns crumb32

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

/-! ### §6.2 Multi-Leaf $q$-Query Adaptive Signing Reduction Over `poly257MultiLeafSuite`

Four-leaf (`subtreeHeight = 2`, `w = 4`, `ell1 = 128`, `productionWellFormed = true`) stateful
Jorts suite `poly257MultiLeafSuite` with uniform `(256 * 256 ^ 24)` key generation
`multiLeaf24Keygen`, lossless 3-chain `(hi, lo)` leaf packing (`packLeaf3`), leaf-bound
`{0, 3}`-incomparable sub-message codewords (`encodeSubMsg3Hmsg`), and punctured multi-leaf
signing simulation (`puncturedSignQuery`):

* `poly257MultiLeaf_punctured_sim_sound`, `poly257MultiLeaf_adaptive_forger_bound`, and
  `poly257MultiLeaf_adaptive_forger_bound_concrete`: for arbitrary `qHash qSign` and arbitrary
  adaptive adversary families `adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign`, every winning
  coin of `ExecEufCmaGame` admits an active chain slot `s : Fin 12` whose punctured simulator
  `puncturedSignQuery` (without `sk.skSeed[s]`) reproduces the exact adaptive multi-leaf run and
  recovers `[sk.skSeed[s]]`, bounding `ExecEufCmaGame.winProb` by `12 · εPre` (`24 / 256 < 1`
  unconditionally under `Spec.poly257Hash_smDtPreHard_within 2 1`).
* `adaptive4LeafQueryForger`, `adaptiveMultiQueryReductionEmbedding`, and
  `adaptiveMultiQueryExecEufCma_forger_bound`: concrete 4-signing-query, 3-hash-query adaptive
  adversary querying all four leaves `0, 1, 2, 3`, embedded via `ExecEufCmaReductionEmbedding`
  into `Spec.WithinPreQueries 2 1` with unconditional `< 1` bound `6 / 256` and positive win count.
* `unlatchedLeafReuseForger` and `tooth_poly257MultiLeaf_unlatched_reuse_forges`: with `BeltLatch`
  disabled (`latchOn = false`), two signing queries `[0, 0]` and `[0, 1]` on leaf `0` plus three
  adaptive hash queries constructively assemble a valid signature on fresh message `[0, 2]` and
  win on every coin (`winProb = 1`), proving the monotonic epoch latch is load-bearing. -/

/-- Right-nested powers `256 ^ k` so `pow256 (k + 1) = 256 * pow256 k` holds definitionally. -/
def pow256 : Nat → Nat
  | 0 => 1
  | k + 1 => 256 * pow256 k

theorem pow256_eq_pow : ∀ k : Nat, pow256 k = 256 ^ k
  | 0 => rfl
  | k+1 => by rw [pow256, pow256_eq_pow k, Nat.pow_succ, Nat.mul_comm]

#verify_constructive pow256_eq_pow

theorem pow256_pos : ∀ k : Nat, 0 < pow256 k
  | 0 => Nat.one_pos
  | k + 1 => Nat.mul_pos (by decide) (pow256_pos k)

/-- Canonical uniform `k`-byte sampler over `Fin (pow256 k)`. -/
def byteVecSampler : (k : Nat) → Fin (pow256 k) → Spec.Bytes
  | 0, _ => []
  | k + 1, z =>
    let sp := Spec.CoinSplit.prod 256 (pow256 k)
    UInt8.ofNat (sp.chal z).1 :: byteVecSampler k (sp.advc z)

theorem byteVecSampler_length : ∀ (k : Nat) (z : Fin (pow256 k)),
    (byteVecSampler k z).length = k
  | 0, _ => rfl
  | k + 1, _ => congrArg Nat.succ (byteVecSampler_length k _)

private theorem byteVecSampler_succ (k : Nat) (z : Fin (256 * pow256 k)) :
    byteVecSampler (k + 1) z =
      UInt8.ofNat ((Spec.CoinSplit.prod 256 (pow256 k)).chal z).1 ::
        byteVecSampler k ((Spec.CoinSplit.prod 256 (pow256 k)).advc z) := by
  rfl

theorem uniformOn_byteVecSampler : ∀ k : Nat,
    Spec.UniformOn (fun bs : Spec.Bytes => bs.length = k) (byteVecSampler k)
  | 0 =>
    { mem := fun _ => rfl
      injective := fun i j _ =>
        Fin.ext ((Nat.lt_one_iff.mp i.2).trans (Nat.lt_one_iff.mp j.2).symm)
      surjective := fun bs h => ⟨⟨0, Nat.one_pos⟩, (List.eq_nil_of_length_eq_zero h).symm⟩ }
  | k + 1 =>
    let ih := uniformOn_byteVecSampler k
    let sp := Spec.CoinSplit.prod 256 (pow256 k)
    { mem := fun z => byteVecSampler_length (k + 1) z
      injective := fun i j h => by
        rw [byteVecSampler_succ k i, byteVecSampler_succ k j] at h
        injection h with hHd hTl
        have hB : sp.chal i = sp.chal j :=
          Spec.uniformOn_byte1Seed.injective (sp.chal i) (sp.chal j)
            (by simpa only [Spec.byte1SeedSampler.public_eqs] using congrArg (· :: []) hHd)
        have hR : sp.advc i = sp.advc j := ih.injective _ _ hTl
        exact (sp.pair_eta i).symm.trans ((congrArg (sp.pair · (sp.advc i)) hB).trans
          ((congrArg (sp.pair (sp.chal j)) hR).trans (sp.pair_eta j)))
      surjective := fun bs hLen => by
        match bs, hLen with
        | b :: rest, hLen =>
          have hRest : rest.length = k := Nat.succ.inj hLen
          obtain ⟨ib, hib⟩ := Spec.uniformOn_byte1Seed.surjective [b] rfl
          obtain ⟨ir, hir⟩ := ih.surjective rest hRest
          refine ⟨sp.pair ib ir, ?_⟩
          rw [byteVecSampler_succ k (sp.pair ib ir), sp.chal_pair, sp.advc_pair, hir]
          rw [Spec.byte1SeedSampler.public_eqs] at hib
          injection hib with hb _
          rw [hb] }

private def coinSplitLiftRight {n₁ n₂ a b : Nat} (c : Nat)
    (h1 : Spec.CoinSplit n₁ n₂ c) (sub : Spec.CoinSplit n₂ a b) :
    Spec.CoinSplit n₁ a (b * c) where
  chal ω := sub.chal (h1.chal ω)
  advc ω := (Spec.CoinSplit.prod b c).pair (sub.advc (h1.chal ω)) (h1.advc ω)
  pair x yz := h1.pair (sub.pair x ((Spec.CoinSplit.prod b c).chal yz))
    ((Spec.CoinSplit.prod b c).advc yz)
  chal_pair x yz := by rw [h1.chal_pair, sub.chal_pair]
  advc_pair x yz := by
    rw [h1.chal_pair, h1.advc_pair, sub.advc_pair, (Spec.CoinSplit.prod b c).pair_eta]
  pair_eta ω := by
    rw [(Spec.CoinSplit.prod b c).chal_pair, (Spec.CoinSplit.prod b c).advc_pair,
      sub.pair_eta, h1.pair_eta]

private def coinSplitSwapSecond {n b c : Nat} (a : Nat)
    (sub : Spec.CoinSplit n b c) : Spec.CoinSplit (a * n) b (a * c) where
  chal ω := sub.chal ((Spec.CoinSplit.prod a n).advc ω)
  advc ω := (Spec.CoinSplit.prod a c).pair
    ((Spec.CoinSplit.prod a n).chal ω)
    (sub.advc ((Spec.CoinSplit.prod a n).advc ω))
  pair y xz := (Spec.CoinSplit.prod a n).pair
    ((Spec.CoinSplit.prod a c).chal xz)
    (sub.pair y ((Spec.CoinSplit.prod a c).advc xz))
  chal_pair y xz := by rw [(Spec.CoinSplit.prod a n).advc_pair, sub.chal_pair]
  advc_pair y xz := by
    rw [(Spec.CoinSplit.prod a n).chal_pair, (Spec.CoinSplit.prod a n).advc_pair,
      sub.advc_pair, (Spec.CoinSplit.prod a c).pair_eta]
  pair_eta ω := by
    rw [(Spec.CoinSplit.prod a c).chal_pair, (Spec.CoinSplit.prod a c).advc_pair,
      sub.pair_eta, (Spec.CoinSplit.prod a n).pair_eta]

/-- Insert byte `b` back into a `(k - 1)`-byte list at position `idx`, reconstructing the full
    `k`-byte secret vector. -/
def insertByteAt : Nat → UInt8 → Spec.Bytes → Spec.Bytes
  | 0, b, rest => b :: rest
  | _ + 1, b, [] => [b]
  | i + 1, b, x :: xs => x :: insertByteAt i b xs

/-- Puncture `Fin (pow256 (k + 1))` at byte index `s : Fin (k + 1)` into the target byte
    (`Fin 256`) and the remaining `k` bytes (`Fin (pow256 k)`). -/
def splitByteVecAt : (k : Nat) → Fin (k + 1) → Spec.CoinSplit (pow256 (k + 1)) 256 (pow256 k)
  | k, ⟨0, _⟩ => Spec.CoinSplit.prod 256 (pow256 k)
  | k + 1, ⟨i + 1, hi⟩ =>
    coinSplitSwapSecond 256 (splitByteVecAt k ⟨i, Nat.lt_of_succ_lt_succ hi⟩)

theorem splitByteVecAt_getD_and_insert :
    ∀ (k : Nat) (s : Fin (k + 1)) (z : Fin (pow256 (k + 1))),
      (byteVecSampler (k + 1) z).getD s.1 0 = UInt8.ofNat ((splitByteVecAt k s).chal z).1 ∧
      insertByteAt s.1 (UInt8.ofNat ((splitByteVecAt k s).chal z).1)
        (byteVecSampler k ((splitByteVecAt k s).advc z)) = byteVecSampler (k + 1) z
  | 0, ⟨0, _⟩, _ => ⟨rfl, rfl⟩
  | _ + 1, ⟨0, _⟩, _ => ⟨rfl, rfl⟩
  | k + 1, ⟨i + 1, hi⟩, z => by
    let spTop := Spec.CoinSplit.prod 256 (pow256 (k + 1))
    let spAdv := Spec.CoinSplit.prod 256 (pow256 k)
    let sub := splitByteVecAt k ⟨i, Nat.lt_of_succ_lt_succ hi⟩
    have ih := splitByteVecAt_getD_and_insert k ⟨i, Nat.lt_of_succ_lt_succ hi⟩ (spTop.advc z)
    have hAdvEq : byteVecSampler (k + 1) ((splitByteVecAt (k + 1) ⟨i + 1, hi⟩).advc z) =
        UInt8.ofNat (spTop.chal z).1 :: byteVecSampler k (sub.advc (spTop.advc z)) := by
      show byteVecSampler (k + 1) (spAdv.pair (spTop.chal z) (sub.advc (spTop.advc z))) = _
      rw [byteVecSampler_succ k, spAdv.chal_pair, spAdv.advc_pair]
    refine ⟨?_, ?_⟩
    · show (UInt8.ofNat (spTop.chal z).1 :: byteVecSampler (k + 1) (spTop.advc z)).getD (i + 1) 0 =
        UInt8.ofNat (sub.chal (spTop.advc z)).1
      exact ih.1
    · rw [hAdvEq]
      show UInt8.ofNat (spTop.chal z).1 ::
          insertByteAt i (UInt8.ofNat (sub.chal (spTop.advc z)).1)
            (byteVecSampler k (sub.advc (spTop.advc z))) =
        UInt8.ofNat (spTop.chal z).1 :: byteVecSampler (k + 1) (spTop.advc z)
      exact congrArg _ ih.2

/-- Split of a key coin `Fin (256 * pow256 24)` paired with an adversary coin `Fin nA`: the
    first coordinate holds the `pkSeed` byte and secret byte `s`, the second the other `23`
    secret bytes and the adversary coin. -/
def puncturedKeyAndAdvSplit (nA : Nat) (s : Fin 24) :
    Spec.CoinSplit ((256 * pow256 24) * nA) (256 * 256) (pow256 23 * nA) :=
  coinSplitLiftRight nA (Spec.CoinSplit.prod (256 * pow256 24) nA)
    { chal := fun k => (Spec.CoinSplit.prod 256 256).pair
        ((Spec.CoinSplit.prod 256 (pow256 24)).chal k)
        ((splitByteVecAt 23 s).chal ((Spec.CoinSplit.prod 256 (pow256 24)).advc k))
      advc := fun k => (splitByteVecAt 23 s).advc ((Spec.CoinSplit.prod 256 (pow256 24)).advc k)
      pair := fun c2 rest =>
        (Spec.CoinSplit.prod 256 (pow256 24)).pair
          ((Spec.CoinSplit.prod 256 256).chal c2)
          ((splitByteVecAt 23 s).pair ((Spec.CoinSplit.prod 256 256).advc c2) rest)
      chal_pair := fun c2 rest => by
        rw [(Spec.CoinSplit.prod 256 (pow256 24)).chal_pair,
          (Spec.CoinSplit.prod 256 (pow256 24)).advc_pair,
          (splitByteVecAt 23 s).chal_pair, (Spec.CoinSplit.prod 256 256).pair_eta]
      advc_pair := fun c2 rest => by
        rw [(Spec.CoinSplit.prod 256 (pow256 24)).advc_pair, (splitByteVecAt 23 s).advc_pair]
      pair_eta := fun k => by
        rw [(Spec.CoinSplit.prod 256 256).chal_pair, (Spec.CoinSplit.prod 256 256).advc_pair,
          (splitByteVecAt 23 s).pair_eta, (Spec.CoinSplit.prod 256 (pow256 24)).pair_eta] }

/-- Concrete 4-leaf (`subtreeHeight = 2`), 128-chain (`w = 4`, `targetSum = 192`) stateful Jorts
    parameter set passing `PqHashParams.productionWellFormed`. -/
def multiLeaf4JortsParams : PqHashParams :=
  { w := 4
    ell1 := 128
    subtreeHeight := 2
    numLayers := 1
    forsTrees := 0
    forsHeight := 0
    maxSigsLog2 := 2
    statefulJorts := true }

#export_eqns multiLeaf4JortsParams

theorem multiLeaf4JortsParams_productionWellFormed :
    multiLeaf4JortsParams.productionWellFormed = true := by
  rw [PqHashParams.productionWellFormed_eq]
  decide +kernel

theorem multiLeaf4JortsParams_radix :
    multiLeaf4JortsParams.w = 4 ∨ multiLeaf4JortsParams.w = 16 :=
  .inl rfl

/-- Uniform `(256 * 256 ^ 24)` key generator sampling a 1-byte `pkSeed` and 24 independent 1-byte
    WOTS+C chain secrets in `skSeed`. -/
def multiLeaf24Keygen (k : Fin (256 * pow256 24)) : PqSecretKey :=
  let sp := Spec.CoinSplit.prod 256 (pow256 24)
  { skSeed := byteVecSampler 24 (sp.advc k)
    skPrf := []
    pkSeed := Spec.byte1SeedSampler (sp.chal k) }

#export_eqns multiLeaf24Keygen

theorem multiLeaf24Keygen_uniform :
    Spec.UniformOn
      (fun sk : PqSecretKey => sk.skSeed.length = 24 ∧ sk.skPrf = [] ∧ sk.pkSeed.length = 1)
      multiLeaf24Keygen where
  mem _ := ⟨byteVecSampler_length 24 _, rfl, Spec.uniformOn_byte1Seed.mem _⟩
  injective i j h := by
    let sp := Spec.CoinSplit.prod 256 (pow256 24)
    injection h with hSk _ hPk
    have hC := Spec.uniformOn_byte1Seed.injective (sp.chal i) (sp.chal j) hPk
    have hA := (uniformOn_byteVecSampler 24).injective (sp.advc i) (sp.advc j) hSk
    rw [← sp.pair_eta i, ← sp.pair_eta j, hC, hA]
  surjective sk hOk := by
    obtain ⟨hSk, hPrf, hPk⟩ := hOk
    obtain ⟨c, hc⟩ := Spec.uniformOn_byte1Seed.surjective sk.pkSeed hPk
    obtain ⟨a, ha⟩ := (uniformOn_byteVecSampler 24).surjective sk.skSeed hSk
    refine ⟨(Spec.CoinSplit.prod 256 (pow256 24)).pair c a, ?_⟩
    cases sk
    dsimp only at hc ha hPrf
    unfold multiLeaf24Keygen
    dsimp only
    rw [(Spec.CoinSplit.prod 256 (pow256 24)).chal_pair,
      (Spec.CoinSplit.prod 256 (pow256 24)).advc_pair, hc, ha, hPrf]

/-! #### Self-Delimiting `thPreimage` Decoder & Multi-Leaf `poly257` Tweakable Hash Suite -/

private def decodeLeb128Aux : Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, b :: rest =>
    if b.toNat < 128 then some (b.toNat, rest)
    else
      match decodeLeb128Aux fuel rest with
      | none => none
      | some (hi, tail) => some (b.toNat - 128 + 128 * hi, tail)

private def decodeLeb128 (bs : List UInt8) : Option (Nat × List UInt8) :=
  decodeLeb128Aux bs.length bs

private def decodeMultiFields : Nat → List UInt8 → Option (List (List UInt8))
  | 0, _ => some []
  | k + 1, bs =>
    match decodeLeb128 bs with
    | none => none
    | some (len, rest) =>
      if len ≤ rest.length then
        match decodeMultiFields k (rest.drop len) with
        | none => none
        | some tl => some (rest.take len :: tl)
      else none

private def decodeMultiFrameLocal (bs : List UInt8) : Option (List (List UInt8)) :=
  match decodeLeb128 bs with
  | none => none
  | some (cnt, rest) => decodeMultiFields cnt rest

private theorem uint8_toNat_of_lt256 {n : Nat} (hn : n < 256) :
    (UInt8.ofNat n).toNat = n := by
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hn]

private theorem decodeLeb128Aux_leb128Aux :
    ∀ (f fuel n : Nat) (rest : List UInt8),
      n ≤ f → (leb128Aux f n ++ rest).length ≤ fuel →
      decodeLeb128Aux fuel (leb128Aux f n ++ rest) = some (n, rest)
  | 0, fuel, n, rest, hn, hFuel => by
    have hz : n = 0 := by omega
    subst hz
    rw [leb128Aux_zero] at hFuel ⊢
    cases fuel with
    | zero => simp at hFuel
    | succ fuel' => rfl
  | f + 1, 0, _, _, _, hFuel => by
    rw [leb128Aux_succ] at hFuel
    split at hFuel <;> simp at hFuel
  | f + 1, fuel + 1, n, rest, hn, hFuel => by
    rw [leb128Aux_succ] at hFuel ⊢
    by_cases hlt : n < 128
    · simp only [hlt, ↓reduceIte, List.singleton_append, decodeLeb128Aux,
        uint8_toNat_of_lt256 (by omega : n < 256)]
    · simp only [hlt, ↓reduceIte, List.cons_append, List.length_cons] at hFuel ⊢
      have hb : (UInt8.ofNat (128 + n % 128)).toNat = 128 + n % 128 :=
        uint8_toNat_of_lt256 (by omega)
      have hNotLt : ¬ (128 + n % 128 < 128) := by omega
      have ih := decodeLeb128Aux_leb128Aux f fuel (n / 128) rest (by omega) (by omega)
      simp only [decodeLeb128Aux, hb, hNotLt, ↓reduceIte, ih]
      congr 1; congr 1; omega

private theorem decodeLeb128_leb128 (n : Nat) (rest : List UInt8) :
    decodeLeb128 (leb128 n ++ rest) = some (n, rest) :=
  decodeLeb128Aux_leb128Aux n (leb128 n ++ rest).length n rest (Nat.le_refl n) (Nat.le_refl _)

private theorem decodeMultiFields_encodeByteFields :
    ∀ (fields : List (List UInt8)),
      decodeMultiFields fields.length (encodeByteFields fields) = some fields
  | [] => rfl
  | f :: fs => by
    rw [List.length_cons, encodeByteFields_cons, encodeListField_eq, List.append_assoc]
    unfold decodeMultiFields
    rw [decodeLeb128_leb128]
    dsimp only
    have hLe : f.length ≤ (f ++ encodeByteFields fs).length := by simp
    have hDrop : (f ++ encodeByteFields fs).drop f.length = encodeByteFields fs :=
      List.drop_left' rfl
    have hTake : (f ++ encodeByteFields fs).take f.length = f :=
      List.take_left' rfl
    rw [ite_eq_left hLe, hDrop, decodeMultiFields_encodeByteFields fs, hTake]

private theorem decodeMultiFrameLocal_encodeMultiFrame (fields : List (List UInt8)) :
    decodeMultiFrameLocal (encodeMultiFrame fields) = some fields := by
  unfold decodeMultiFrameLocal encodeMultiFrame
  rw [decodeLeb128_leb128]
  exact decodeMultiFields_encodeByteFields fields

private def decodeAdrsLocal (bs : List UInt8) : Option HashAdrs :=
  if bs.length = 32 then
    match AdrsKind.fromCode (UInt32.ofNat (ofBE ((bs.drop 16).take 4))) with
    | none => none
    | some kind =>
      some
        { layer := UInt32.ofNat (ofBE (bs.take 4))
          tree := UInt64.ofNat (ofBE ((bs.drop 8).take 8))
          kind := kind
          keyPair := UInt32.ofNat (ofBE ((bs.drop 20).take 4))
          chainIdx := UInt32.ofNat (ofBE ((bs.drop 24).take 4))
          hashStep := UInt32.ofNat (ofBE ((bs.drop 28).take 4)) }
  else none

private theorem decodeAdrsLocal_encodeAdrs (a : HashAdrs) :
    decodeAdrsLocal (encodeAdrs a) = some a := by
  have hLen := encodeAdrs_length a
  unfold decodeAdrsLocal
  rw [ite_eq_left hLen]
  have hTake4 : (encodeAdrs a).take 4 = be 4 a.layer.toNat := by
    unfold encodeAdrs; exact List.take_left' (length_be 4 _)
  have hDrop4 : (encodeAdrs a).drop 4 =
      be 4 0 ++ (be 8 a.tree.toNat ++ (be 4 a.kind.toCode.toNat ++
        (be 4 a.keyPair.toNat ++ (be 4 a.chainIdx.toNat ++ be 4 a.hashStep.toNat)))) := by
    unfold encodeAdrs; exact List.drop_left' (length_be 4 _)
  have hDrop8 : (encodeAdrs a).drop 8 =
      be 8 a.tree.toNat ++ (be 4 a.kind.toCode.toNat ++
        (be 4 a.keyPair.toNat ++ (be 4 a.chainIdx.toNat ++ be 4 a.hashStep.toNat))) := by
    have h8 : (8 : Nat) = 4 + 4 := rfl
    rw [h8, ← List.drop_drop, hDrop4]; exact List.drop_left' (length_be 4 _)
  have hTakeTree : ((encodeAdrs a).drop 8).take 8 = be 8 a.tree.toNat := by
    rw [hDrop8]; exact List.take_left' (length_be 8 _)
  have hDrop16 : (encodeAdrs a).drop 16 =
      be 4 a.kind.toCode.toNat ++
        (be 4 a.keyPair.toNat ++ (be 4 a.chainIdx.toNat ++ be 4 a.hashStep.toNat)) := by
    have h16 : (16 : Nat) = 8 + 8 := rfl
    rw [h16, ← List.drop_drop, hDrop8]; exact List.drop_left' (length_be 8 _)
  have hTakeKind : ((encodeAdrs a).drop 16).take 4 = be 4 a.kind.toCode.toNat := by
    rw [hDrop16]; exact List.take_left' (length_be 4 _)
  have hDrop20 : (encodeAdrs a).drop 20 =
      be 4 a.keyPair.toNat ++ (be 4 a.chainIdx.toNat ++ be 4 a.hashStep.toNat) := by
    have h20 : (20 : Nat) = 16 + 4 := rfl
    rw [h20, ← List.drop_drop, hDrop16]; exact List.drop_left' (length_be 4 _)
  have hTakeKp : ((encodeAdrs a).drop 20).take 4 = be 4 a.keyPair.toNat := by
    rw [hDrop20]; exact List.take_left' (length_be 4 _)
  have hDrop24 : (encodeAdrs a).drop 24 = be 4 a.chainIdx.toNat ++ be 4 a.hashStep.toNat := by
    have h24 : (24 : Nat) = 20 + 4 := rfl
    rw [h24, ← List.drop_drop, hDrop20]; exact List.drop_left' (length_be 4 _)
  have hTakeCh : ((encodeAdrs a).drop 24).take 4 = be 4 a.chainIdx.toNat := by
    rw [hDrop24]; exact List.take_left' (length_be 4 _)
  have hDrop28 : (encodeAdrs a).drop 28 = be 4 a.hashStep.toNat := by
    have h28 : (28 : Nat) = 24 + 4 := rfl
    rw [h28, ← List.drop_drop, hDrop24]; exact List.drop_left' (length_be 4 _)
  have hTakeSt : ((encodeAdrs a).drop 28).take 4 = be 4 a.hashStep.toNat := by
    rw [hDrop28, List.take_of_length_le (Nat.le_of_eq (length_be 4 _))]
  have u32Rt : ∀ u : UInt32, UInt32.ofNat (ofBE (be 4 u.toNat)) = u := fun u => by
    rw [ofBE_be (w := 4) (Nat.lt_of_lt_of_le u.toNat_lt (Nat.le_of_eq (by decide)))]
    exact UInt32.ofNat_toNat
  have u64Rt : ∀ u : UInt64, UInt64.ofNat (ofBE (be 8 u.toNat)) = u := fun u => by
    rw [ofBE_be (w := 8) (Nat.lt_of_lt_of_le u.toNat_lt (Nat.le_of_eq (by decide)))]
    exact UInt64.ofNat_toNat
  rw [hTake4, hTakeTree, hTakeKind, hTakeKp, hTakeCh, hTakeSt,
    u32Rt a.kind.toCode, AdrsKind.fromCode_toCode,
    u32Rt a.layer, u64Rt a.tree, u32Rt a.keyPair, u32Rt a.chainIdx, u32Rt a.hashStep]

private def parseThPreimageLocal (raw : List UInt8) :
    Option (List UInt8 × List UInt8 × HashAdrs × List (List UInt8)) :=
  match decodeMultiFrameLocal raw with
  | some (role :: pkSeed :: adrsBytes :: args) =>
    match decodeAdrsLocal adrsBytes with
    | some adrs => some (role, pkSeed, adrs, args)
    | none => none
  | _ => none

private theorem parseThPreimageLocal_thPreimage (role pkSeed : List UInt8)
    (adrs : HashAdrs) (args : List (List UInt8)) :
    parseThPreimageLocal (thPreimage role pkSeed adrs args) = some (role, pkSeed, adrs, args) := by
  rw [thPreimage_eq]
  unfold parseThPreimageLocal
  rw [decodeMultiFrameLocal_encodeMultiFrame]
  show (match decodeAdrsLocal (encodeAdrs adrs) with
        | some a => some (role, pkSeed, a, args)
        | none => none) = _
  rw [decodeAdrsLocal_encodeAdrs]

/-- Domain-separated tweak `[kp, r]` for step-0 `Spec.poly257Hash` chain evaluation. -/
def chain0Tweak (kp r : Nat) : Spec.Bytes :=
  [UInt8.ofNat kp, UInt8.ofNat r]

#export_eqns chain0Tweak

/-- Encode a 1-byte secret `b` into the 32-byte WOTS+C step-0 chain carrier. -/
def encodeStep0Secret (b : UInt8) : List UInt8 :=
  0xA0 :: b :: List.replicate 30 0x00

#export_eqns encodeStep0Secret

theorem encodeStep0Secret_length (b : UInt8) : (encodeStep0Secret b).length = 32 := by rfl

/-- Decode a 32-byte step-0 chain carrier into a 1- or 2-byte `poly257Hash` preimage candidate. -/
def decodeStep0Cand (x : List UInt8) : Option Spec.Bytes :=
  match x with
  | 0xA0 :: b :: rest =>
    if rest = List.replicate 30 0x00 then some [b] else none
  | 0xA1 :: b₀ :: b₁ :: rest =>
    if rest = List.replicate 29 0x00 then some [b₀, b₁] else none
  | _ => none

theorem decodeStep0Cand_encodeStep0Secret (b : UInt8) :
    decodeStep0Cand (encodeStep0Secret b) = some [b] := by
  unfold decodeStep0Cand encodeStep0Secret
  simp

theorem decodeStep0Cand_len_le_two {x : List UInt8} {cand : Spec.Bytes}
    (h : decodeStep0Cand x = some cand) : cand.length ≤ 2 := by
  unfold decodeStep0Cand at h
  split at h
  · split at h
    · injection h with hc; rw [← hc]; exact Nat.le_succ 1
    · cases h
  · split at h
    · injection h with hc; rw [← hc]; exact Nat.le_refl 2
    · cases h
  · cases h

/-- Decode a 32-byte step-0 secret carrier (`0xA0 :: b :: 0^30`) into its 1-byte secret `b`. -/
def decodeStep0Byte (x : List UInt8) : Option UInt8 :=
  match x with
  | 0xA0 :: b :: rest =>
    if rest = List.replicate 30 0x00 then some b else none
  | _ => none

theorem decodeStep0Byte_encodeStep0Secret (b : UInt8) :
    decodeStep0Byte (encodeStep0Secret b) = some b := by
  unfold decodeStep0Byte encodeStep0Secret
  simp

private def invalid32 : List UInt8 :=
  0xFF :: List.replicate 31 0x00

private theorem invalid32_length : invalid32.length = 32 := rfl

/-- Step-`s` (`s ∈ {1, 2, 3}`) 32-byte WOTS+C chain carrier storing `(kp, r, hi, lo)`. -/
def encodeChainNode (stepTag : UInt8) (kp r : Nat) (hi lo : UInt8) : List UInt8 :=
  [stepTag, UInt8.ofNat kp, UInt8.ofNat r, hi, lo] ++ List.replicate 27 0x00

private theorem encodeChainNode_length (st : UInt8) (kp r : Nat) (hi lo : UInt8) :
    (encodeChainNode st kp r hi lo).length = 32 := rfl

private theorem encodeChainNode_inj {st : UInt8} {kp r : Nat} {hi₁ lo₁ hi₂ lo₂ : UInt8}
    (h : encodeChainNode st kp r hi₁ lo₁ = encodeChainNode st kp r hi₂ lo₂) :
    hi₁ = hi₂ ∧ lo₁ = lo₂ :=
  ⟨congrArg (fun l => l.getD 3 0) h, congrArg (fun l => l.getD 4 0) h⟩

private def decodeChainNode (expectedTag : UInt8) (kp r : Nat) (x : List UInt8) :
    Option (UInt8 × UInt8) :=
  match x with
  | st :: kpB :: rB :: hi :: lo :: rest =>
    if st = expectedTag ∧ kpB = UInt8.ofNat kp ∧ rB = UInt8.ofNat r ∧
        rest = List.replicate 27 0x00 then
      some (hi, lo)
    else none
  | _ => none

private theorem decodeChainNode_encodeChainNode (tag : UInt8) (kp r : Nat) (hi lo : UInt8) :
    decodeChainNode tag kp r (encodeChainNode tag kp r hi lo) = some (hi, lo) := by
  unfold decodeChainNode encodeChainNode
  simp

private theorem decodeChainNode_sound {tag : UInt8} {kp r : Nat} {x : List UInt8} {hi lo : UInt8}
    (h : decodeChainNode tag kp r x = some (hi, lo)) :
    x = encodeChainNode tag kp r hi lo := by
  unfold decodeChainNode at h
  match x with
  | st :: kpB :: rB :: hi' :: lo' :: rest =>
    dsimp only at h
    split at h
    · rename_i hc
      injection h with hPair
      injection hPair with h1 h2
      subst h1 h2
      rcases hc with ⟨rfl, rfl, rfl, rfl⟩
      rfl
    · cases h
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] => cases h

/-- Pack 6 `(hi, lo)` pairs (`hi ≤ 1`) losslessly into 7 bytes. -/
def packLeaf6 (ps : List (UInt8 × UInt8)) : List UInt8 :=
  let p0 := ps.getD 0 (0, 0)
  let p1 := ps.getD 1 (0, 0)
  let p2 := ps.getD 2 (0, 0)
  let p3 := ps.getD 3 (0, 0)
  let p4 := ps.getD 4 (0, 0)
  let p5 := ps.getD 5 (0, 0)
  let flags := UInt8.ofNat
    (p0.1.toNat + 2 * p1.1.toNat + 4 * p2.1.toNat +
      8 * p3.1.toNat + 16 * p4.1.toNat + 32 * p5.1.toNat)
  [flags, p0.2, p1.2, p2.2, p3.2, p4.2, p5.2]

/-- Unpack a 7-byte leaf payload back into the `r`-th `(hi, lo)` pair (`r < 6`). -/
def unpackLeaf6At (pay7 : List UInt8) (r : Nat) : UInt8 × UInt8 :=
  let flags := (pay7.headD 0).toNat
  let hi := UInt8.ofNat ((flags / (2 ^ r)) % 2)
  let lo := pay7.getD (r + 1) 0
  (hi, lo)

/-- Pack 3 `(hi, lo)` pairs losslessly into 6 bytes (no restriction on `hi : UInt8`). -/
def packLeaf3 (ps : List (UInt8 × UInt8)) : List UInt8 :=
  let p0 := ps.getD 0 (0, 0)
  let p1 := ps.getD 1 (0, 0)
  let p2 := ps.getD 2 (0, 0)
  [p0.1, p0.2, p1.1, p1.2, p2.1, p2.2]

private theorem packLeaf3_length (ps : List (UInt8 × UInt8)) : (packLeaf3 ps).length = 6 := rfl

private theorem packLeaf3_inj {p0 p1 p2 q0 q1 q2 : UInt8 × UInt8}
    (h : packLeaf3 [p0, p1, p2] = packLeaf3 [q0, q1, q2]) :
    p0 = q0 ∧ p1 = q1 ∧ p2 = q2 := by
  rcases p0 with ⟨a0, b0⟩; rcases p1 with ⟨a1, b1⟩; rcases p2 with ⟨a2, b2⟩
  rcases q0 with ⟨c0, d0⟩; rcases q1 with ⟨c1, d1⟩; rcases q2 with ⟨c2, d2⟩
  dsimp only [packLeaf3, List.getD] at h
  simp only [List.cons.injEq, and_true] at h
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨rfl, rfl, rfl⟩

private def extractActive3 (kp : Nat) (limbs : List (List UInt8)) :
    Option (List (UInt8 × UInt8)) :=
  match limbs with
  | l0 :: l1 :: l2 :: rest =>
    if rest = List.replicate 125 crumb32 then
      match decodeChainNode 0xB3 kp 0 l0, decodeChainNode 0xB3 kp 1 l1,
            decodeChainNode 0xB3 kp 2 l2 with
      | some p0, some p1, some p2 => some [p0, p1, p2]
      | _, _, _ => none
    else none
  | _ => none

/-- 32-byte Manchester `{0, 3}` leaf-message digest for 3-bit message code `m < 8`:
    encodes bits `0, 1, 2` of `m` on chain pairs `(0, 1), (2, 3), (4, 5)` as `(0, 3)` for `0`
    and `(3, 0)` for `1`, and pads chains `6 .. 127` with `(0, 3)` (`sumDigits = 192`). -/
def encodeMsg3Hmsg (m : Nat) : List UInt8 :=
  let b0 := if m % 2 = 0 then 0x30 else 0xC0
  let b1 := if (m / 2) % 2 = 0 then 0x03 else 0x0C
  let b2 := if (m / 4) % 2 = 0 then 0x30 else 0xC0
  UInt8.ofNat (b0 + b1) :: UInt8.ofNat (b2 + 0x03) :: List.replicate 30 0x33

theorem sumDigits_eq_foldr : ∀ ds : List Nat, sumDigits ds = ds.foldr (· + ·) 0
  | [] => sumDigits_nil
  | d :: ds => (sumDigits_cons d ds).trans (congrArg (d + ·) (sumDigits_eq_foldr ds))

private theorem encodeMsg3Hmsg_digits_eval :
    ∀ m : Fin 8,
      extractBaseWDigitsChecked 4 128 (encodeMsg3Hmsg m.1) =
          some (extractBaseWDigits 4 128 (encodeMsg3Hmsg m.1)) ∧
        checkTargetSum 4 128 192 (extractBaseWDigits 4 128 (encodeMsg3Hmsg m.1)) = true ∧
        ∀ r : Nat, r < 128 → 6 ≤ r →
          (extractBaseWDigits 4 128 (encodeMsg3Hmsg m.1)).getD r 0 =
            if r % 2 = 0 then 0 else 3 := by
  simp only [extractBaseWDigitsChecked_eq, extractBaseWDigits_eq, checkTargetSum,
    sumDigits_eq_foldr]
  decide +kernel

theorem encodeMsg3Hmsg_digits_valid :
    ∀ m : Fin 8,
      ∃ digits : List Nat,
        extractBaseWDigitsChecked 4 128 (encodeMsg3Hmsg m.1) = some digits ∧
        checkTargetSum 4 128 192 digits = true ∧
        (∀ r : Nat, 6 ≤ r → r < 128 →
          digits.getD r 0 = if r % 2 = 0 then 0 else 3) :=
  fun m => ⟨_, (encodeMsg3Hmsg_digits_eval m).1, (encodeMsg3Hmsg_digits_eval m).2.1,
    fun r h6 hr => (encodeMsg3Hmsg_digits_eval m).2.2 r hr h6⟩

theorem encodeMsg3Hmsg_incomparable :
    ∀ m₁ m₂ : Fin 8, m₁ ≠ m₂ →
      ∃ r : Fin 6,
        (extractBaseWDigits 4 128 (encodeMsg3Hmsg m₁.1)).getD r.1 0 = 0 ∧
        (extractBaseWDigits 4 128 (encodeMsg3Hmsg m₂.1)).getD r.1 0 = 3 := by
  simp only [extractBaseWDigits_eq]
  decide +kernel

theorem encodeMsg3Hmsg_has_zero_digit :
    ∀ m : Fin 8,
      ∃ r : Fin 6,
        (extractBaseWDigits 4 128 (encodeMsg3Hmsg m.1)).getD r.1 0 = 0 := by
  simp only [extractBaseWDigits_eq]
  decide +kernel

/-- Leaf-local 3-submessage `{0, 3}` digest (`sub ∈ {0, 1, 2}`) on the 3 active chains `r ∈ {0, 1, 2}`:
    * `sub = 0`: `(0, 3, 0)` (`0x33` -> `[0, 3, 0, 3]`)
    * `sub = 1`: `(3, 0, 0)` (`0xC3` -> `[3, 0, 0, 3]`)
    * `sub = 2`: `(0, 0, 3)` (`0x0F` -> `[0, 0, 3, 3]`)
    padded with `31` bytes `0x33` (`sumDigits = 192`). -/
def encodeSubMsg3Hmsg (sub : Nat) : List UInt8 :=
  (if sub = 0 then 0x33 else if sub = 1 then 0xC3 else 0x0F) :: List.replicate 31 0x33

private theorem encodeSubMsg3Hmsg_digits_eval :
    ∀ s : Fin 3,
      extractBaseWDigitsChecked 4 128 (encodeSubMsg3Hmsg s.1) =
          some (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg s.1)) ∧
        checkTargetSum 4 128 192 (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg s.1)) = true := by
  simp only [extractBaseWDigitsChecked_eq, extractBaseWDigits_eq, checkTargetSum,
    sumDigits_eq_foldr]
  decide +kernel

private theorem zero32_checkTargetSum_false :
    checkTargetSum 4 128 192 (extractBaseWDigits 4 128 zero32) = false := by
  unfold zero32
  simp only [extractBaseWDigits_eq, checkTargetSum, sumDigits_eq_foldr]
  decide +kernel

theorem encodeSubMsg3Hmsg_incomparable :
    ∀ s₁ s₂ : Fin 3, s₁ ≠ s₂ →
      ∃ r : Fin 3,
        (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg s₁.1)).getD r.1 0 = 0 ∧
        (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg s₂.1)).getD r.1 0 = 3 := by
  simp only [extractBaseWDigits_eq]
  decide +kernel

theorem encodeSubMsg3Hmsg_has_zero_digit :
    ∀ s : Fin 3,
      ∃ r : Fin 3,
        (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg s.1)).getD r.1 0 = 0 := by
  simp only [extractBaseWDigits_eq]
  decide +kernel

theorem encodeSubMsg3Hmsg_explicit_digits :
    (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD 0 0 = 0 ∧
    (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD 1 0 = 3 ∧
    (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD 2 0 = 0 ∧
    (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 1)).getD 0 0 = 3 ∧
    (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 1)).getD 1 0 = 0 ∧
    (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 1)).getD 2 0 = 0 ∧
    (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 2)).getD 0 0 = 0 ∧
    (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 2)).getD 1 0 = 0 ∧
    (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 2)).getD 2 0 = 3 := by
  simp only [extractBaseWDigits_eq]
  decide +kernel

private def poly257MultiLeafDispatch (role pkSeed : List UInt8) (adrs : HashAdrs)
    (args : List (List UInt8)) : List UInt8 :=
  if role = tagPrf then
    match args with
    | [skSeed] =>
      let kp := adrs.keyPair.toNat
      let r := adrs.chainIdx.toNat
      if kp < 4 ∧ r < 3 then
        encodeStep0Secret (skSeed.getD (3 * kp + r) 0)
      else crumb32
    | _ => invalid32
  else if role = tagPrfMsg then
    zero32
  else if role = tagHPre then
    match args with
    | [_, [kpB, subB]] =>
      if kpB.toNat < 4 ∧ subB.toNat < 3 then
        [0xE0, kpB, subB] ++ List.replicate 29 0x00
      else invalid32
    | _ => invalid32
  else if role = tagHMsg then
    match args with
    | [_, _, 0xE0 :: kpB :: subB :: rest, _] =>
      if kpB.toNat < 4 ∧ subB.toNat < 3 ∧ kpB.toNat = adrs.keyPair.toNat ∧
          rest = List.replicate 29 0x00 then
        encodeSubMsg3Hmsg subB.toNat
      else zero32
    | _ => zero32
  else if role = tagThF then
    match args with
    | [x] =>
      let kp := adrs.keyPair.toNat
      let r := adrs.chainIdx.toNat
      let st := adrs.hashStep.toNat
      if adrs.layer = 0 ∧ adrs.tree = 0 ∧ adrs.kind = .wotsHash then
        if kp < 4 ∧ r < 3 then
          if st = 0 then
            match decodeStep0Byte x with
            | some b =>
              let yx := Spec.byteXorHash pkSeed (chain0Tweak kp r) [b]
              let yp := Spec.poly257Hash pkSeed (chain0Tweak kp r) [b]
              encodeChainNode 0xB1 kp r (yx.headD 0) (yp.getD 2 0)
            | none => invalid32
          else if st = 1 then
            match decodeChainNode 0xB1 kp r x with
            | some (hi, lo) => encodeChainNode 0xB2 kp r hi lo
            | none => invalid32
          else if st = 2 then
            match decodeChainNode 0xB2 kp r x with
            | some (hi, lo) => encodeChainNode 0xB3 kp r hi lo
            | none => invalid32
          else invalid32
        else
          if x = crumb32 then crumb32 else invalid32
      else invalid32
    | _ => invalid32
  else if role = tagThTl then
    let kp := adrs.keyPair.toNat
    if adrs.layer = 0 ∧ adrs.tree = 0 ∧ adrs.kind = .wotsPk ∧ kp < 4 then
      match extractActive3 kp args with
      | some ps => [0xC0, UInt8.ofNat kp] ++ packLeaf3 ps ++ List.replicate 24 0x00
      | none => invalid32
    else invalid32
  else if role = tagThH then
    match args with
    | [left, right] =>
      let h := adrs.chainIdx.toNat
      let idx := adrs.hashStep.toNat
      if adrs.layer = 0 ∧ adrs.tree = 0 ∧ adrs.kind = .tree then
        if h = 1 ∧ idx < 2 then
          if left.take 2 = [0xC0, UInt8.ofNat (2 * idx)] ∧
              left.drop 8 = List.replicate 24 0x00 ∧ left.length = 32 ∧
              right.take 2 = [0xC0, UInt8.ofNat (2 * idx + 1)] ∧
              right.drop 8 = List.replicate 24 0x00 ∧ right.length = 32 then
            [0xD1, UInt8.ofNat idx] ++ (left.drop 2).take 6 ++ (right.drop 2).take 6 ++
              List.replicate 18 0x00
          else invalid32
        else if h = 2 ∧ idx = 0 then
          if left.take 2 = [0xD1, 0] ∧ left.drop 14 = List.replicate 18 0x00 ∧ left.length = 32 ∧
              right.take 2 = [0xD1, 1] ∧ right.drop 14 = List.replicate 18 0x00 ∧
              right.length = 32 then
            [0xD2, 0] ++ (left.drop 2).take 12 ++ (right.drop 2).take 12 ++
              List.replicate 6 0x00
          else invalid32
        else invalid32
      else invalid32
    | _ => invalid32
  else invalid32

private theorem poly257MultiLeafDispatch_length (role pkSeed : List UInt8) (adrs : HashAdrs)
    (args : List (List UInt8)) :
    (poly257MultiLeafDispatch role pkSeed adrs args).length = 32 := by
  unfold poly257MultiLeafDispatch
  by_cases h1 : role = tagPrf
  · rw [ite_eq_left h1]
    match args with
    | [skSeed] => dsimp only; split <;> rfl
    | [] | _ :: _ :: _ => rfl
  · rw [ite_eq_right h1]
    by_cases h2 : role = tagPrfMsg
    · rw [ite_eq_left h2]; rfl
    · rw [ite_eq_right h2]
      by_cases h3 : role = tagHPre
      · rw [ite_eq_left h3]
        repeat' split
        all_goals rfl
      · rw [ite_eq_right h3]
        by_cases h4 : role = tagHMsg
        · rw [ite_eq_left h4]
          repeat' split
          all_goals rfl
        · rw [ite_eq_right h4]
          by_cases h5 : role = tagThF
          · rw [ite_eq_left h5]
            match args with
            | [x] =>
              dsimp only
              split
              · split
                · split
                  · cases decodeStep0Byte x <;> rfl
                  · split
                    · cases decodeChainNode 0xB1 adrs.keyPair.toNat adrs.chainIdx.toNat x with
                      | none => rfl
                      | some p => cases p; rfl
                    · split
                      · cases decodeChainNode 0xB2 adrs.keyPair.toNat adrs.chainIdx.toNat x with
                        | none => rfl
                        | some p => cases p; rfl
                      · rfl
                · split <;> rfl
              · rfl
            | [] | _ :: _ :: _ => rfl
          · rw [ite_eq_right h5]
            by_cases h6 : role = tagThTl
            · rw [ite_eq_left h6]
              dsimp only; split
              · cases extractActive3 adrs.keyPair.toNat args <;> rfl
              · rfl
            · rw [ite_eq_right h6]
              by_cases h7 : role = tagThH
              · rw [ite_eq_left h7]
                match args with
                | [left, right] =>
                  dsimp only
                  split
                  · split
                    · split
                      · rename_i hc
                        have hL : ((left.drop 2).take 6).length = 6 := by
                          rw [List.length_take, List.length_drop, hc.2.2.1]; decide
                        have hR : ((right.drop 2).take 6).length = 6 := by
                          rw [List.length_take, List.length_drop, hc.2.2.2.2.2]; decide
                        simp [hL, hR]
                      · rfl
                    · split
                      · split
                        · rename_i hc
                          have hL : ((left.drop 2).take 12).length = 12 := by
                            rw [List.length_take, List.length_drop, hc.2.2.1]; decide
                          have hR : ((right.drop 2).take 12).length = 12 := by
                            rw [List.length_take, List.length_drop, hc.2.2.2.2.2]; decide
                          simp [hL, hR]
                        · rfl
                      · rfl
                  · rfl
                | [] | [_] | _ :: _ :: _ :: _ => rfl
              · rw [ite_eq_right h7]; rfl

/-- Tweakable-hash suite whose `rawHash` decodes a `thPreimage` and dispatches on the role tag
    (`poly257MultiLeafDispatch`); inputs that do not decode hash to `invalid32`. -/
def poly257MultiLeafSuite : TweakableHashSuite where
  suiteId := "QSAG.PQ.SUITE.POLY257.MULTILEAF/v1".toByteArray.toList
  rawHash raw :=
    match parseThPreimageLocal raw with
    | some (role, pkSeed, adrs, args) => poly257MultiLeafDispatch role pkSeed adrs args
    | none => invalid32
  rawHash_len raw := by
    split
    · exact poly257MultiLeafDispatch_length _ _ _ _
    · rfl

private theorem poly257MultiLeafSuite_thCall (role pkSeed : List UInt8) (adrs : HashAdrs)
    (args : List (List UInt8)) :
    thCall poly257MultiLeafSuite role pkSeed adrs args =
      poly257MultiLeafDispatch role pkSeed adrs args := by
  rw [thCall_eq]
  show (match parseThPreimageLocal (thPreimage role pkSeed adrs args) with
        | some (r, p, a, xs) => poly257MultiLeafDispatch r p a xs
        | none => invalid32) = _
  rw [parseThPreimageLocal_thPreimage]

theorem byteXorHash_headD_inj (pkSeed tweak : Spec.Bytes) {b₁ b₂ : UInt8}
    (h : (Spec.byteXorHash pkSeed tweak [b₁]).headD 0 =
      (Spec.byteXorHash pkSeed tweak [b₂]).headD 0) :
    b₁ = b₂ := by
  rw [Spec.byteXorHash_eq, Spec.byteXorHash_eq] at h
  dsimp only [List.headD] at h
  exact (UInt8.xor_right_inj ((pkSeed.headD 0) ^^^ (tweak.headD 0))).mp h

/-! #### Role-Tag Dispatch Equations, Tree Tables, Verification Soundness, and Punctured Reduction -/

private theorem multiLeaf_role_tags_ne :
    tagPrfMsg ≠ tagPrf ∧
    tagHPre ≠ tagPrf ∧ tagHPre ≠ tagPrfMsg ∧
    tagHMsg ≠ tagPrf ∧ tagHMsg ≠ tagPrfMsg ∧ tagHMsg ≠ tagHPre ∧
    tagThF ≠ tagPrf ∧ tagThF ≠ tagPrfMsg ∧ tagThF ≠ tagHPre ∧ tagThF ≠ tagHMsg ∧
    tagThTl ≠ tagPrf ∧ tagThTl ≠ tagPrfMsg ∧ tagThTl ≠ tagHPre ∧ tagThTl ≠ tagHMsg ∧
      tagThTl ≠ tagThF ∧
    tagThH ≠ tagPrf ∧ tagThH ≠ tagPrfMsg ∧ tagThH ≠ tagHPre ∧ tagThH ≠ tagHMsg ∧
      tagThH ≠ tagThF ∧ tagThH ≠ tagThTl := by
  simp only [tagPrf.public_eqs, tagPrfMsg.public_eqs, tagHPre.public_eqs, tagHMsg.public_eqs,
    tagThF.public_eqs, tagThTl.public_eqs, tagThH.public_eqs]
  decide +kernel

theorem poly257MultiLeaf_thSecretPrf (pkSeed skSeed : List UInt8) (adrs : HashAdrs) :
    thSecretPrf poly257MultiLeafSuite pkSeed skSeed adrs =
      if adrs.keyPair.toNat < 4 ∧ adrs.chainIdx.toNat < 3 then
        encodeStep0Secret (skSeed.getD (3 * adrs.keyPair.toNat + adrs.chainIdx.toNat) 0)
      else crumb32 := by
  rw [thSecretPrf_eq, poly257MultiLeafSuite_thCall]
  unfold poly257MultiLeafDispatch
  rw [ite_eq_left rfl]

private theorem poly257MultiLeaf_thPrfMsg (skPrf optRand mu : List UInt8) :
    thPrfMsg poly257MultiLeafSuite skPrf optRand mu = zero32 := by
  rw [thPrfMsg_eq, poly257MultiLeafSuite_thCall]
  unfold poly257MultiLeafDispatch
  rw [ite_eq_right multiLeaf_role_tags_ne.1, ite_eq_left rfl]

private theorem poly257MultiLeaf_thPreHash (pkSeed pkRoot msg : List UInt8) :
    thPreHash poly257MultiLeafSuite pkSeed pkRoot msg =
      match msg with
      | [kpB, subB] =>
        if kpB.toNat < 4 ∧ subB.toNat < 3 then
          [0xE0, kpB, subB] ++ List.replicate 29 0x00
        else invalid32
      | _ => invalid32 := by
  rw [thPreHash_eq, poly257MultiLeafSuite_thCall]
  unfold poly257MultiLeafDispatch
  rw [ite_eq_right multiLeaf_role_tags_ne.2.1, ite_eq_right multiLeaf_role_tags_ne.2.2.1,
    ite_eq_left rfl]
  cases msg with
  | nil => rfl
  | cons b0 t0 =>
    cases t0 with
    | nil => rfl
    | cons b1 t1 => cases t1 <;> rfl

private theorem poly257MultiLeaf_thHashLeafMsg (rRand pkSeed pkRoot mu : List UInt8)
    (treeIdx : UInt64) (kpIdx : UInt32) (ctr : Nat) :
    thHashLeafMsg poly257MultiLeafSuite rRand pkSeed pkRoot mu treeIdx kpIdx ctr =
      match mu with
      | 0xE0 :: kpB :: subB :: rest =>
        if kpB.toNat < 4 ∧ subB.toNat < 3 ∧ kpB.toNat = kpIdx.toNat ∧
            rest = List.replicate 29 0x00 then
          encodeSubMsg3Hmsg subB.toNat
        else zero32
      | _ => zero32 := by
  rw [thHashLeafMsg_eq, poly257MultiLeafSuite_thCall]
  unfold poly257MultiLeafDispatch
  rw [ite_eq_right multiLeaf_role_tags_ne.2.2.2.1,
    ite_eq_right multiLeaf_role_tags_ne.2.2.2.2.1,
    ite_eq_right multiLeaf_role_tags_ne.2.2.2.2.2.1, ite_eq_left rfl]
  cases mu with
  | nil => rfl
  | cons b0 t0 =>
    by_cases hb0 : b0 = 0xE0
    · subst hb0
      cases t0 with
      | nil => rfl
      | cons b1 t1 => cases t1 <;> rfl
    · simp [hb0]

private theorem poly257MultiLeaf_thChainF (pkSeed : List UInt8) (adrs : HashAdrs)
    (x : List UInt8) :
    thChainF poly257MultiLeafSuite pkSeed adrs x =
      let kp := adrs.keyPair.toNat
      let r := adrs.chainIdx.toNat
      let st := adrs.hashStep.toNat
      if adrs.layer = 0 ∧ adrs.tree = 0 ∧ adrs.kind = .wotsHash then
        if kp < 4 ∧ r < 3 then
          if st = 0 then
            match decodeStep0Byte x with
            | some b =>
              let yx := Spec.byteXorHash pkSeed (chain0Tweak kp r) [b]
              let yp := Spec.poly257Hash pkSeed (chain0Tweak kp r) [b]
              encodeChainNode 0xB1 kp r (yx.headD 0) (yp.getD 2 0)
            | none => invalid32
          else if st = 1 then
            match decodeChainNode 0xB1 kp r x with
            | some (hi, lo) => encodeChainNode 0xB2 kp r hi lo
            | none => invalid32
          else if st = 2 then
            match decodeChainNode 0xB2 kp r x with
            | some (hi, lo) => encodeChainNode 0xB3 kp r hi lo
            | none => invalid32
          else invalid32
        else
          if x = crumb32 then crumb32 else invalid32
      else invalid32 := by
  rw [thChainF_eq, poly257MultiLeafSuite_thCall]
  unfold poly257MultiLeafDispatch
  have hN := multiLeaf_role_tags_ne.2.2.2.2.2.2
  rw [ite_eq_right hN.1, ite_eq_right hN.2.1, ite_eq_right hN.2.2.1, ite_eq_right hN.2.2.2.1,
    ite_eq_left rfl]

private theorem poly257MultiLeaf_thTweakTl (pkSeed : List UInt8) (adrs : HashAdrs)
    (limbs : List (List UInt8)) :
    thTweakTl poly257MultiLeafSuite pkSeed adrs limbs =
      let kp := adrs.keyPair.toNat
      if adrs.layer = 0 ∧ adrs.tree = 0 ∧ adrs.kind = .wotsPk ∧ kp < 4 then
        match extractActive3 kp limbs with
        | some ps => [0xC0, UInt8.ofNat kp] ++ packLeaf3 ps ++ List.replicate 24 0x00
        | none => invalid32
      else invalid32 := by
  rw [thTweakTl_eq, poly257MultiLeafSuite_thCall]
  unfold poly257MultiLeafDispatch
  have hN := multiLeaf_role_tags_ne.2.2.2.2.2.2.2.2.2.2
  rw [ite_eq_right hN.1, ite_eq_right hN.2.1, ite_eq_right hN.2.2.1, ite_eq_right hN.2.2.2.1,
    ite_eq_right hN.2.2.2.2.1, ite_eq_left rfl]

private theorem poly257MultiLeaf_thNodeH (pkSeed : List UInt8) (adrs : HashAdrs)
    (left right : List UInt8) :
    thNodeH poly257MultiLeafSuite pkSeed adrs left right =
      let h := adrs.chainIdx.toNat
      let idx := adrs.hashStep.toNat
      if adrs.layer = 0 ∧ adrs.tree = 0 ∧ adrs.kind = .tree then
        if h = 1 ∧ idx < 2 then
          if left.take 2 = [0xC0, UInt8.ofNat (2 * idx)] ∧
              left.drop 8 = List.replicate 24 0x00 ∧ left.length = 32 ∧
              right.take 2 = [0xC0, UInt8.ofNat (2 * idx + 1)] ∧
              right.drop 8 = List.replicate 24 0x00 ∧ right.length = 32 then
            [0xD1, UInt8.ofNat idx] ++ (left.drop 2).take 6 ++ (right.drop 2).take 6 ++
              List.replicate 18 0x00
          else invalid32
        else if h = 2 ∧ idx = 0 then
          if left.take 2 = [0xD1, 0] ∧ left.drop 14 = List.replicate 18 0x00 ∧ left.length = 32 ∧
              right.take 2 = [0xD1, 1] ∧ right.drop 14 = List.replicate 18 0x00 ∧
              right.length = 32 then
            [0xD2, 0] ++ (left.drop 2).take 12 ++ (right.drop 2).take 12 ++
              List.replicate 6 0x00
          else invalid32
        else invalid32
      else invalid32 := by
  rw [thNodeH_eq, poly257MultiLeafSuite_thCall]
  unfold poly257MultiLeafDispatch
  have hN := multiLeaf_role_tags_ne.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [ite_eq_right hN.1, ite_eq_right hN.2.1, ite_eq_right hN.2.2.1, ite_eq_right hN.2.2.2.1,
    ite_eq_right hN.2.2.2.2.1, ite_eq_right hN.2.2.2.2.2, ite_eq_left rfl]

/-- Honest `(hi, lo)` chain-endpoint table for `sk` on `kp < 4, r < 3`. -/
def honestSlotHiLo (sk : PqSecretKey) (kp r : Nat) : UInt8 × UInt8 :=
  let b := sk.skSeed.getD (3 * kp + r) 0
  ((Spec.byteXorHash sk.pkSeed (chain0Tweak kp r) [b]).headD 0,
   (Spec.poly257Hash sk.pkSeed (chain0Tweak kp r) [b]).getD 2 0)

def leafFromTbl (tbl : Nat → Nat → UInt8 × UInt8) (kp : Nat) : List UInt8 :=
  [0xC0, UInt8.ofNat kp] ++ packLeaf3 [tbl kp 0, tbl kp 1, tbl kp 2] ++ List.replicate 24 0x00

def node1FromTbl (tbl : Nat → Nat → UInt8 × UInt8) (idx : Nat) : List UInt8 :=
  [0xD1, UInt8.ofNat idx] ++
    packLeaf3 [tbl (2 * idx) 0, tbl (2 * idx) 1, tbl (2 * idx) 2] ++
    packLeaf3 [tbl (2 * idx + 1) 0, tbl (2 * idx + 1) 1, tbl (2 * idx + 1) 2] ++
    List.replicate 18 0x00

def rootFromTbl (tbl : Nat → Nat → UInt8 × UInt8) : List UInt8 :=
  [0xD2, 0] ++
    packLeaf3 [tbl 0 0, tbl 0 1, tbl 0 2] ++
    packLeaf3 [tbl 1 0, tbl 1 1, tbl 1 2] ++
    packLeaf3 [tbl 2 0, tbl 2 1, tbl 2 2] ++
    packLeaf3 [tbl 3 0, tbl 3 1, tbl 3 2] ++
    List.replicate 6 0x00

def pkFromTbl (pkSeed : List UInt8) (tbl : Nat → Nat → UInt8 × UInt8) : PqPublicKey :=
  ⟨pkSeed, rootFromTbl tbl⟩

def authPathFromTbl (tbl : Nat → Nat → UInt8 × UInt8) (kp : Nat) : List (List UInt8) :=
  if kp = 0 then [node1FromTbl tbl 1, leafFromTbl tbl 1]
  else if kp = 1 then [node1FromTbl tbl 1, leafFromTbl tbl 0]
  else if kp = 2 then [node1FromTbl tbl 0, leafFromTbl tbl 3]
  else [node1FromTbl tbl 0, leafFromTbl tbl 2]

private theorem u32_toNat_small {n : Nat} (hn : n < 2 ^ 32) : (UInt32.ofNat n).toNat = n := by
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hn]

private theorem active_chain_steps_3 (pkSeed : List UInt8) {kp r : Nat}
    (hkp : kp < 4) (hr : r < 3) (b : UInt8) :
    wotsChainSteps poly257MultiLeafSuite pkSeed 0 0 kp r 0 3 (encodeStep0Secret b) =
      encodeChainNode 0xB3 kp r
        ((Spec.byteXorHash pkSeed (chain0Tweak kp r) [b]).headD 0)
        ((Spec.poly257Hash pkSeed (chain0Tweak kp r) [b]).getD 2 0) := by
  have hkp32 : (UInt32.ofNat kp).toNat = kp := u32_toNat_small (by omega)
  have hr32 : (UInt32.ofNat r).toNat = r := u32_toNat_small (by omega)
  rw [wotsChainSteps_succ]
  dsimp only
  rw [poly257MultiLeaf_thChainF]
  simp only [hkp32, hr32, u32_toNat_small (by decide : 0 < 2 ^ 32), hkp, hr, and_self,
    ↓reduceIte, decodeStep0Byte_encodeStep0Secret]
  rw [wotsChainSteps_succ]
  dsimp only
  rw [poly257MultiLeaf_thChainF]
  simp only [hkp32, hr32, u32_toNat_small (by decide : 1 < 2 ^ 32), hkp, hr, and_self,
    (by decide : ¬ (1 = 0)), ↓reduceIte, decodeChainNode_encodeChainNode]
  rw [wotsChainSteps_succ]
  dsimp only
  rw [poly257MultiLeaf_thChainF]
  simp only [hkp32, hr32, u32_toNat_small (by decide : 2 < 2 ^ 32), hkp, hr, and_self,
    (by decide : ¬ (2 = 0)), (by decide : ¬ (2 = 1)), ↓reduceIte,
    decodeChainNode_encodeChainNode, wotsChainSteps_zero]

private theorem inactive_chain_steps_crumb (pkSeed : List UInt8) {kp r : Nat}
    (hkp : kp < 4) (hr : 3 ≤ r) (hrLt : r < 128) :
    ∀ k start : Nat,
      wotsChainSteps poly257MultiLeafSuite pkSeed 0 0 kp r start k crumb32 = crumb32
  | 0, start => wotsChainSteps_zero _ _ _ _ _ _ start crumb32
  | k + 1, start => by
    have hkp32 : (UInt32.ofNat kp).toNat = kp := u32_toNat_small (by omega)
    have hr32 : (UInt32.ofNat r).toNat = r := u32_toNat_small (by omega)
    have hNot : ¬ (kp < 4 ∧ r < 3) := by omega
    rw [wotsChainSteps_succ]
    dsimp only
    rw [poly257MultiLeaf_thChainF]
    simp only [hkp32, hr32, and_self, hNot, ↓reduceIte]
    exact inactive_chain_steps_crumb pkSeed hkp hr hrLt k (start + 1)

private theorem range128_split3 :
    List.range 128 = 0 :: 1 :: 2 :: (List.range 125).map (· + 3) := by
  decide

private theorem computeWotsPk_poly257MultiLeaf (sk : PqSecretKey) {kp : Nat} (hkp : kp < 4) :
    computeWotsPk poly257MultiLeafSuite multiLeaf4JortsParams sk 0 0 kp =
      leafFromTbl (honestSlotHiLo sk) kp := by
  have hkp32 : (UInt32.ofNat kp).toNat = kp := u32_toNat_small (by omega)
  rw [computeWotsPk_eq, multiLeaf4JortsParams.public_eqs]
  dsimp only
  rw [range128_split3, List.map_cons, List.map_cons, List.map_cons]
  have hTail : List.map (fun r =>
      wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 kp r 0 (4 - 1)
        (wotsSecretBase poly257MultiLeafSuite sk 0 0 kp r)) ((List.range 125).map (· + 3)) =
      List.replicate 125 crumb32 := by
    rw [List.map_map]
    have hEach : ∀ k ∈ List.range 125,
        ((fun r => wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 kp r 0 (4 - 1)
          (wotsSecretBase poly257MultiLeafSuite sk 0 0 kp r)) ∘ (· + 3)) k = crumb32 := by
      intro k hk
      have hkLt : k < 125 := List.mem_range.mp hk
      dsimp only [Function.comp_def]
      rw [wotsSecretBase_eq, poly257MultiLeaf_thSecretPrf]
      have hr32 : (UInt32.ofNat (k + 3)).toNat = k + 3 := u32_toNat_small (by omega)
      have hNot : ¬ (kp < 4 ∧ k + 3 < 3) := by omega
      simp only [hkp32, hr32, hNot, ↓reduceIte]
      exact inactive_chain_steps_crumb sk.pkSeed hkp (by omega) (by omega) 3 0
    exact (List.map_congr_left hEach).trans (by decide)
  have hAct : ∀ r : Nat, (hr : r < 3) →
      wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 kp r 0 (4 - 1)
        (wotsSecretBase poly257MultiLeafSuite sk 0 0 kp r) =
      encodeChainNode 0xB3 kp r (honestSlotHiLo sk kp r).1 (honestSlotHiLo sk kp r).2 := by
    intro r hr
    rw [wotsSecretBase_eq, poly257MultiLeaf_thSecretPrf]
    have hr32 : (UInt32.ofNat r).toNat = r := u32_toNat_small (by omega)
    simp only [hkp32, hr32, hkp, hr, and_self, ↓reduceIte]
    exact active_chain_steps_3 sk.pkSeed hkp hr (sk.skSeed.getD (3 * kp + r) 0)
  rw [hTail, hAct 0 (by decide), hAct 1 (by decide), hAct 2 (by decide),
    poly257MultiLeaf_thTweakTl]
  simp only [hkp32, hkp, and_self, ↓reduceIte]
  unfold extractActive3 leafFromTbl
  simp [decodeChainNode_encodeChainNode]

private theorem leafFromTbl_props (tbl : Nat → Nat → UInt8 × UInt8) (kp : Nat) :
    (leafFromTbl tbl kp).take 2 = [0xC0, UInt8.ofNat kp] ∧
    (leafFromTbl tbl kp).drop 8 = List.replicate 24 0x00 ∧
    (leafFromTbl tbl kp).length = 32 ∧
    ((leafFromTbl tbl kp).drop 2).take 6 = packLeaf3 [tbl kp 0, tbl kp 1, tbl kp 2] := by
  unfold leafFromTbl packLeaf3
  simp

private theorem node1FromTbl_props (tbl : Nat → Nat → UInt8 × UInt8) (idx : Nat) :
    (node1FromTbl tbl idx).take 2 = [0xD1, UInt8.ofNat idx] ∧
    (node1FromTbl tbl idx).drop 14 = List.replicate 18 0x00 ∧
    (node1FromTbl tbl idx).length = 32 ∧
    ((node1FromTbl tbl idx).drop 2).take 12 =
      packLeaf3 [tbl (2 * idx) 0, tbl (2 * idx) 1, tbl (2 * idx) 2] ++
        packLeaf3 [tbl (2 * idx + 1) 0, tbl (2 * idx + 1) 1, tbl (2 * idx + 1) 2] := by
  unfold node1FromTbl packLeaf3
  simp

private theorem thNodeH_leaves_eq (pkSeed : List UInt8) (tbl : Nat → Nat → UInt8 × UInt8)
    {idx : Nat} (hIdx : idx < 2) :
    thNodeH poly257MultiLeafSuite pkSeed ⟨0, 0, .tree, 0, 1, UInt32.ofNat idx⟩
      (leafFromTbl tbl (2 * idx)) (leafFromTbl tbl (2 * idx + 1)) =
      node1FromTbl tbl idx := by
  rw [poly257MultiLeaf_thNodeH]
  have hIdx32 : (UInt32.ofNat idx).toNat = idx := u32_toNat_small (by omega)
  have hL := leafFromTbl_props tbl (2 * idx)
  have hR := leafFromTbl_props tbl (2 * idx + 1)
  have h1 : (1 : UInt32).toNat = 1 := rfl
  simp only [h1, hIdx32, hIdx, and_self, ↓reduceIte, hL.1, hL.2.1, hL.2.2.1,
    hR.1, hR.2.1, hR.2.2.1, hL.2.2.2, hR.2.2.2]
  rfl

private theorem thNodeH_nodes_eq (pkSeed : List UInt8) (tbl : Nat → Nat → UInt8 × UInt8) :
    thNodeH poly257MultiLeafSuite pkSeed ⟨0, 0, .tree, 0, 2, 0⟩
      (node1FromTbl tbl 0) (node1FromTbl tbl 1) =
      rootFromTbl tbl := by
  rw [poly257MultiLeaf_thNodeH]
  have hL := node1FromTbl_props tbl 0
  have hR := node1FromTbl_props tbl 1
  have h2 : (2 : UInt32).toNat = 2 := rfl
  have h0 : (0 : UInt32).toNat = 0 := rfl
  simp only [h2, h0, (by decide : ¬ (2 = 1 ∧ 0 < 2)), and_self, ↓reduceIte,
    hL.1, hL.2.1, hL.2.2.1, hR.1, hR.2.1, hR.2.2.1, hL.2.2.2, hR.2.2.2]
  unfold rootFromTbl
  simp [List.append_assoc]

theorem derivePublicKey_poly257MultiLeaf (sk : PqSecretKey) :
    derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk =
      pkFromTbl sk.pkSeed (honestSlotHiLo sk) := by
  unfold derivePublicKey
  dsimp only
  rw [computeXmssSubtreeRoot_eq]
  have hTop : UInt32.ofNat (multiLeaf4JortsParams.numLayers - 1) = 0 := rfl
  have hSubH : multiLeaf4JortsParams.subtreeHeight = 2 := rfl
  have hc1 : UInt32.ofNat (0 + 1) = 1 := rfl
  have hc2 : UInt32.ofNat (1 + 1) = 2 := rfl
  have hu0 : UInt32.ofNat 0 = 0 := rfl
  have hL1 : thNodeH poly257MultiLeafSuite sk.pkSeed ⟨0, 0, .tree, 0, 1, 1⟩
      (leafFromTbl (honestSlotHiLo sk) 2) (leafFromTbl (honestSlotHiLo sk) 3) =
      node1FromTbl (honestSlotHiLo sk) 1 :=
    thNodeH_leaves_eq sk.pkSeed (honestSlotHiLo sk) (by decide : 1 < 2)
  rw [hTop, hSubH, computeMerkleNode_succ, computeMerkleNode_succ, computeMerkleNode_succ,
    computeMerkleNode_zero, computeMerkleNode_zero, computeMerkleNode_zero, computeMerkleNode_zero]
  dsimp only
  rw [hc1, hc2,
    computeWotsPk_poly257MultiLeaf sk (by decide : 0 < 4),
    computeWotsPk_poly257MultiLeaf sk (by decide : 1 < 4),
    computeWotsPk_poly257MultiLeaf sk (by decide : 2 < 4),
    computeWotsPk_poly257MultiLeaf sk (by decide : 3 < 4),
    thNodeH_leaves_eq sk.pkSeed (honestSlotHiLo sk) (by decide : 0 < 2),
    hL1,
    hu0, thNodeH_nodes_eq sk.pkSeed (honestSlotHiLo sk)]
  rfl

private theorem buildMerkleAuthPathKp_poly257MultiLeaf (sk : PqSecretKey) {kp : Nat}
    (hkp : kp < 4) :
    buildMerkleAuthPathKp poly257MultiLeafSuite sk.pkSeed 0 0 .tree 0
      (computeWotsPk poly257MultiLeafSuite multiLeaf4JortsParams sk 0 0) 2 0 0 kp =
      authPathFromTbl (honestSlotHiLo sk) kp := by
  have hCases : kp = 0 ∨ kp = 1 ∨ kp = 2 ∨ kp = 3 := by omega
  have hc1 : UInt32.ofNat (0 + 1) = 1 := rfl
  have hs1 : (1 : UInt32) = UInt32.ofNat 1 := rfl
  have hL1 : thNodeH poly257MultiLeafSuite sk.pkSeed ⟨0, 0, .tree, 0, UInt32.ofNat 1, UInt32.ofNat 1⟩
      (leafFromTbl (honestSlotHiLo sk) (2 * (2 * 0 + 1)))
      (leafFromTbl (honestSlotHiLo sk) (2 * (2 * 0 + 1) + 1)) =
      node1FromTbl (honestSlotHiLo sk) 1 :=
    thNodeH_leaves_eq sk.pkSeed (honestSlotHiLo sk) (by decide : 1 < 2)
  rcases hCases with rfl | rfl | rfl | rfl
  · rw [buildMerkleAuthPathKp.public_eq_2]
    simp only [Nat.pow_succ, Nat.pow_zero, (by decide : 0 < 2), ↓reduceIte]
    rw [buildMerkleAuthPathKp.public_eq_2]
    simp only [Nat.pow_zero, (by decide : 0 < 1), ↓reduceIte]
    rw [buildMerkleAuthPathKp.public_eq_1, computeMerkleNodeKp_succ, computeMerkleNodeKp_zero,
      computeMerkleNodeKp_zero, computeMerkleNodeKp_zero, hc1, hs1,
      computeWotsPk_poly257MultiLeaf sk (by decide : 2 * (2 * 0 + 1) < 4),
      computeWotsPk_poly257MultiLeaf sk (by decide : 2 * (2 * 0 + 1) + 1 < 4),
      computeWotsPk_poly257MultiLeaf sk (by decide : 2 * 0 + 1 < 4),
      hL1]
    rfl
  · rw [buildMerkleAuthPathKp.public_eq_2]
    simp only [Nat.pow_succ, Nat.pow_zero, (by decide : 1 < 2), ↓reduceIte]
    rw [buildMerkleAuthPathKp.public_eq_2]
    simp only [Nat.pow_zero, (by decide : ¬ (1 < 1)), ↓reduceIte]
    rw [buildMerkleAuthPathKp.public_eq_1, computeMerkleNodeKp_succ, computeMerkleNodeKp_zero,
      computeMerkleNodeKp_zero, computeMerkleNodeKp_zero, hc1, hs1,
      computeWotsPk_poly257MultiLeaf sk (by decide : 2 * (2 * 0 + 1) < 4),
      computeWotsPk_poly257MultiLeaf sk (by decide : 2 * (2 * 0 + 1) + 1 < 4),
      computeWotsPk_poly257MultiLeaf sk (by decide : 2 * 0 < 4),
      hL1]
    rfl
  · rw [buildMerkleAuthPathKp.public_eq_2]
    simp only [Nat.pow_succ, Nat.pow_zero, (by decide : ¬ (2 < 2)), ↓reduceIte]
    rw [buildMerkleAuthPathKp.public_eq_2]
    simp only [Nat.pow_zero, (by decide : 2 - 2 < 1), ↓reduceIte]
    rw [buildMerkleAuthPathKp.public_eq_1, computeMerkleNodeKp_succ, computeMerkleNodeKp_zero,
      computeMerkleNodeKp_zero, computeMerkleNodeKp_zero, hc1,
      computeWotsPk_poly257MultiLeaf sk (by decide : 2 * (2 * 0) < 4),
      computeWotsPk_poly257MultiLeaf sk (by decide : 2 * (2 * 0) + 1 < 4),
      computeWotsPk_poly257MultiLeaf sk (by decide : 2 * (2 * 0 + 1) + 1 < 4),
      thNodeH_leaves_eq sk.pkSeed (honestSlotHiLo sk) (by decide : 2 * 0 < 2)]
    rfl
  · rw [buildMerkleAuthPathKp.public_eq_2]
    simp only [Nat.pow_succ, Nat.pow_zero, (by decide : ¬ (3 < 2)), ↓reduceIte]
    rw [buildMerkleAuthPathKp.public_eq_2]
    simp only [Nat.pow_zero, (by decide : ¬ (3 - 2 < 1)), ↓reduceIte]
    rw [buildMerkleAuthPathKp.public_eq_1, computeMerkleNodeKp_succ, computeMerkleNodeKp_zero,
      computeMerkleNodeKp_zero, computeMerkleNodeKp_zero, hc1,
      computeWotsPk_poly257MultiLeaf sk (by decide : 2 * (2 * 0) < 4),
      computeWotsPk_poly257MultiLeaf sk (by decide : 2 * (2 * 0) + 1 < 4),
      computeWotsPk_poly257MultiLeaf sk (by decide : 2 * (2 * 0 + 1) < 4),
      thNodeH_leaves_eq sk.pkSeed (honestSlotHiLo sk) (by decide : 2 * 0 < 2)]
    rfl

/-- Honest signature produced by `prodSignQuery` on leaf `kp < 4` and sub-message `sub < 3`. -/
def honestMultiLeafSig (sk : PqSecretKey) (kp sub : Nat) : PqHashSig :=
  let digits := extractBaseWDigits 4 128 (encodeSubMsg3Hmsg sub)
  let wotsChains := (List.range 128).map fun r =>
    let dr := digits.getD r 0
    wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 kp r 0 dr
      (wotsSecretBase poly257MultiLeafSuite sk 0 0 kp r)
  { rRand := zero32
    msgTswCtr := 0
    leafGlobalIdx := kp
    forsOpenings := []
    layerSigs := [⟨0, wotsChains, authPathFromTbl (honestSlotHiLo sk) kp⟩] }

private theorem grind_zero32_none (rRand pkSeed pkRoot mu : List UInt8)
    (treeIdx : UInt64) (kpIdx : UInt32)
    (hZero : ∀ ctr : Nat,
      thHashLeafMsg poly257MultiLeafSuite rRand pkSeed pkRoot mu treeIdx kpIdx ctr = zero32) :
    ∀ (fuel curCtr : Nat),
      grindTswLeafCounterAux poly257MultiLeafSuite 4 128 192 rRand pkSeed pkRoot mu
        treeIdx kpIdx curCtr fuel = none
  | 0, curCtr => grindTswLeafCounterAux_zero _ _ _ _ _ _ _ _ _ _ curCtr
  | fuel + 1, curCtr => by
    rw [grindTswLeafCounterAux_succ]
    by_cases hLt : curCtr < 2 ^ 32
    · simp only [hLt, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hZero curCtr]
      have hExt : extractBaseWDigitsChecked 4 128 zero32 =
          some (extractBaseWDigits 4 128 zero32) :=
        extractBaseWDigitsChecked_of_productionWellFormed multiLeaf4JortsParams
          multiLeaf4JortsParams_productionWellFormed zero32 rfl
      rw [hExt]
      dsimp only
      rw [zero32_checkTargetSum_false, ite_eq_right Bool.false_ne_true]
      exact grind_zero32_none rRand pkSeed pkRoot mu treeIdx kpIdx hZero fuel (curCtr + 1)
    · simp [hLt]

private theorem multiLeaf4JortsParams_targetSum : multiLeaf4JortsParams.targetSum = 192 := by
  rw [PqHashParams.targetSum_eq, multiLeaf4JortsParams.public_eqs]
  decide

theorem prodSignQuery_poly257MultiLeaf_valid (sk : PqSecretKey) {kp sub maxGrind : Nat}
    (hkp : kp < 4) (hsub : sub < 3) (hGrind : 0 < maxGrind) (optRand : List UInt8) :
    prodSignQuery poly257MultiLeafSuite multiLeaf4JortsParams sk
      ⟨[UInt8.ofNat kp, UInt8.ofNat sub], optRand, kp, maxGrind⟩ =
      some (honestMultiLeafSig sk kp sub) := by
  match maxGrind, hGrind with
  | fuel + 1, _ =>
    rw [prodSignQuery_eq]
    have hSt : multiLeaf4JortsParams.statefulJorts = true := rfl
    rw [ite_eq_left hSt, evalProductionStatefulSign_def]
    have hRange : multiLeaf4JortsParams.productionLeafIdxInRange kp = true := by
      rw [PqHashParams.productionLeafIdxInRange_eq, multiLeaf4JortsParams.public_eqs]
      simpa using hkp
    simp only [hSt, multiLeaf4JortsParams_productionWellFormed, hRange, Bool.not_true,
      Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    rw [signProductionHypertreeCore_def]
    have hNumLayers : multiLeaf4JortsParams.numLayers = 1 := rfl
    simp only [hSt, ↓reduceIte, hNumLayers]
    have hDiv : kp / 4 = 0 := Nat.div_eq_of_lt hkp
    have hMod : kp % 4 = kp := Nat.mod_eq_of_lt hkp
    have hkp8 : (UInt8.ofNat kp).toNat = kp := uint8_toNat_of_lt256 (by omega)
    have hsub8 : (UInt8.ofNat sub).toNat = sub := uint8_toNat_of_lt256 (by omega)
    have hkp32 : (UInt32.ofNat kp).toNat = kp := u32_toNat_small (by omega)
    have hMu : thPreHash poly257MultiLeafSuite
        (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk).pkSeed
        (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk).pkRoot
        [UInt8.ofNat kp, UInt8.ofNat sub] =
        [0xE0, UInt8.ofNat kp, UInt8.ofNat sub] ++ List.replicate 29 0x00 := by
      rw [poly257MultiLeaf_thPreHash]
      simp [hkp8, hsub8, hkp, hsub]
    have hRand : thPrfMsg poly257MultiLeafSuite sk.skPrf optRand
        ([0xE0, UInt8.ofNat kp, UInt8.ofNat sub] ++ List.replicate 29 0x00) = zero32 :=
      poly257MultiLeaf_thPrfMsg _ _ _
    rw [hMu, hRand]
    have hHmsg0 : thHashLeafMsg poly257MultiLeafSuite zero32 sk.pkSeed
        (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk).pkRoot
        ([0xE0, UInt8.ofNat kp, UInt8.ofNat sub] ++ List.replicate 29 0x00)
        (UInt64.ofNat (kp / 4)) (UInt32.ofNat (kp % 4)) 0 = encodeSubMsg3Hmsg sub := by
      rw [hDiv, hMod, poly257MultiLeaf_thHashLeafMsg]
      simp [hkp8, hsub8, hkp32, hkp, hsub]
    have hGrind0 : grindTswLeafCounterAux poly257MultiLeafSuite 4 128
        multiLeaf4JortsParams.targetSum zero32 sk.pkSeed
        (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk).pkRoot
        ([0xE0, UInt8.ofNat kp, UInt8.ofNat sub] ++ List.replicate 29 0x00)
        (UInt64.ofNat (kp / 4)) (UInt32.ofNat (kp % 4)) 0 (fuel + 1) =
        some (0, extractBaseWDigits 4 128 (encodeSubMsg3Hmsg sub), encodeSubMsg3Hmsg sub) := by
      rw [multiLeaf4JortsParams_targetSum, grindTswLeafCounterAux_succ]
      simp only [(by decide : 0 < 2 ^ 32), decide_true, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, hHmsg0]
      have hEv := encodeSubMsg3Hmsg_digits_eval ⟨sub, hsub⟩
      rw [hEv.1]
      dsimp only
      rw [ite_eq_left hEv.2]
    have hLayers : signProductionHypertreeLayers poly257MultiLeafSuite multiLeaf4JortsParams sk
        (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk).pkRoot zero32
        (fuel + 1) 0 kp
        ([0xE0, UInt8.ofNat kp, UInt8.ofNat sub] ++ List.replicate 29 0x00) 1 =
        some ((honestMultiLeafSig sk kp sub).layerSigs) := by
      rw [signProductionHypertreeLayers_succ]
      have hSubLeaves : 2 ^ multiLeaf4JortsParams.subtreeHeight = 4 := rfl
      have hSubH : multiLeaf4JortsParams.subtreeHeight = 2 := rfl
      have hEll : multiLeaf4JortsParams.ell1 = 128 := rfl
      have hW : multiLeaf4JortsParams.w = 4 := rfl
      have hu32_0 : UInt32.ofNat 0 = 0 := rfl
      have hu64_0 : UInt64.ofNat 0 = 0 := rfl
      simp only [hSubLeaves, hSt, decide_true, Bool.and_self, ↓reduceIte, hW, hEll, hGrind0]
      rw [signProductionHypertreeLayers_zero]
      dsimp only
      rw [hDiv, hMod, hu32_0, hu64_0, hSubH, buildMerkleAuthPathKp_poly257MultiLeaf sk hkp]
      rfl
    rw [hLayers]
    dsimp only
    have hVer : verifyProductionPqHashSig poly257MultiLeafSuite multiLeaf4JortsParams
        (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk)
        [UInt8.ofNat kp, UInt8.ofNat sub] (honestMultiLeafSig sk kp sub) = true := by
      obtain ⟨_, hLsVer⟩ := signProductionHypertreeLayers_sound poly257MultiLeafSuite
        multiLeaf4JortsParams sk
        (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk).pkRoot zero32
        (fuel + 1) 1 0 kp
        ([0xE0, UInt8.ofNat kp, UInt8.ofNat sub] ++ List.replicate 29 0x00)
        (honestMultiLeafSig sk kp sub).layerSigs (by decide)
        (by simpa [multiLeaf4JortsParams.public_eqs] using hkp) hLayers
      rw [verifyProductionPqHashSig_eq]
      have hLsLen : (honestMultiLeafSig sk kp sub).layerSigs.length = 1 := rfl
      have hLeaf : (honestMultiLeafSig sk kp sub).leafGlobalIdx = kp := rfl
      have hCtr : (honestMultiLeafSig sk kp sub).msgTswCtr = 0 := rfl
      have hFors : (honestMultiLeafSig sk kp sub).forsOpenings = [] := rfl
      have hR : (honestMultiLeafSig sk kp sub).rRand = zero32 := rfl
      have hPkSeed : (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk).pkSeed =
          sk.pkSeed := rfl
      have hMu' : thPreHash poly257MultiLeafSuite sk.pkSeed
          (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk).pkRoot
          [UInt8.ofNat kp, UInt8.ofNat sub] =
          [0xE0, UInt8.ofNat kp, UInt8.ofNat sub] ++ List.replicate 29 0x00 := hMu
      simp only [multiLeaf4JortsParams_productionWellFormed, hLeaf, hRange, Bool.not_true,
        Bool.or_self, Bool.false_eq_true, ↓reduceIte, hLsLen, hNumLayers, hSt,
        hCtr, ne_eq, not_true_eq_false, hFors, List.isEmpty_nil, hR, hPkSeed]
      rw [hMu', hLsVer]
      simp [derivePublicKey, hNumLayers]
    change (if verifyProductionPqHashSig poly257MultiLeafSuite multiLeaf4JortsParams
        (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk)
        [UInt8.ofNat kp, UInt8.ofNat sub] (honestMultiLeafSig sk kp sub) = true then
      some (honestMultiLeafSig sk kp sub) else none) = some (honestMultiLeafSig sk kp sub)
    rw [ite_eq_left hVer]

private def queryMsgValidAt (kp : Nat) (msg : List UInt8) : Option Nat :=
  match msg with
  | [kpB, subB] =>
    if kpB.toNat = kp ∧ kp < 4 ∧ subB.toNat < 3 then some subB.toNat else none
  | _ => none

private theorem prodSignQuery_poly257MultiLeaf_characterize (sk : PqSecretKey)
    (q : ProdSigningQuery) :
    prodSignQuery poly257MultiLeafSuite multiLeaf4JortsParams sk q =
      if 0 < q.grindLimit then
        match queryMsgValidAt q.epoch q.message with
        | some sub => some (honestMultiLeafSig sk q.epoch sub)
        | none => none
      else none := by
  by_cases hGrind : 0 < q.grindLimit
  · rw [ite_eq_left hGrind]
    cases hVal : queryMsgValidAt q.epoch q.message with
    | some sub =>
      unfold queryMsgValidAt at hVal
      match hMsg : q.message with
      | [kpB, subB] =>
        rw [hMsg] at hVal
        dsimp only at hVal
        split at hVal
        · rename_i hc
          injection hVal with hSubEq
          rcases hc with ⟨hKpEq, hKpLt, hSubLt⟩
          have hKpB : kpB = UInt8.ofNat q.epoch := by
            rw [← hKpEq]; exact UInt8.ofNat_toNat.symm
          have hSubB : subB = UInt8.ofNat sub := by
            rw [← hSubEq]; exact UInt8.ofNat_toNat.symm
          cases q with
          | mk message randomness epoch grindLimit =>
            dsimp only at hMsg hGrind hKpLt ⊢
            rw [hMsg, hKpB, hSubB]
            exact prodSignQuery_poly257MultiLeaf_valid sk hKpLt (hSubEq ▸ hSubLt) hGrind randomness
        · cases hVal
      | [] | [_] | _ :: _ :: _ :: _ =>
        rw [hMsg] at hVal; cases hVal
    | none =>
      rw [prodSignQuery_eq]
      have hSt : multiLeaf4JortsParams.statefulJorts = true := rfl
      rw [ite_eq_left hSt, evalProductionStatefulSign_def]
      by_cases hkp : q.epoch < 4
      · have hRange : multiLeaf4JortsParams.productionLeafIdxInRange q.epoch = true := by
          rw [PqHashParams.productionLeafIdxInRange_eq, multiLeaf4JortsParams.public_eqs]
          simpa using hkp
        simp only [hSt, multiLeaf4JortsParams_productionWellFormed, hRange, Bool.not_true,
          Bool.or_self, Bool.false_eq_true, ↓reduceIte]
        rw [signProductionHypertreeCore_def]
        have hNumLayers : multiLeaf4JortsParams.numLayers = 1 := rfl
        simp only [hSt, ↓reduceIte, hNumLayers]
        rw [signProductionHypertreeLayers_succ]
        have hSubLeaves : 2 ^ multiLeaf4JortsParams.subtreeHeight = 4 := rfl
        have hMod : q.epoch % 4 = q.epoch := Nat.mod_eq_of_lt hkp
        have hkp32 : (UInt32.ofNat q.epoch).toNat = q.epoch := u32_toNat_small (by omega)
        have hZeroHmsg : ∀ ctr : Nat,
            thHashLeafMsg poly257MultiLeafSuite
              (thPrfMsg poly257MultiLeafSuite sk.skPrf q.randomness
                (thPreHash poly257MultiLeafSuite
                  (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk).pkSeed
                  (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk).pkRoot q.message))
              sk.pkSeed
              (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk).pkRoot
              (thPreHash poly257MultiLeafSuite
                (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk).pkSeed
                (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk).pkRoot q.message)
              (UInt64.ofNat (q.epoch / 4)) (UInt32.ofNat (q.epoch % 4)) ctr = zero32 := by
          intro ctr
          rw [hMod, poly257MultiLeaf_thHashLeafMsg, poly257MultiLeaf_thPreHash]
          match hM : q.message with
          | [kpB, subB] =>
            dsimp only
            by_cases hB : kpB.toNat < 4 ∧ subB.toNat < 3
            · rw [ite_eq_left hB]
              simp only [List.cons_append, List.nil_append]
              have hNeKp : kpB.toNat ≠ q.epoch := by
                intro hEq
                unfold queryMsgValidAt at hVal
                rw [hM] at hVal
                dsimp only at hVal
                have hcV : kpB.toNat = q.epoch ∧ q.epoch < 4 ∧ subB.toNat < 3 :=
                  ⟨hEq, hkp, hB.2⟩
                rw [ite_eq_left hcV] at hVal
                cases hVal
              rw [hkp32]
              have hnc : ¬ (kpB.toNat < 4 ∧ subB.toNat < 3 ∧ kpB.toNat = q.epoch ∧ True) :=
                fun hc => hNeKp hc.2.2.1
              exact ite_eq_right hnc
            · rw [ite_eq_right hB]; rfl
          | [] | [_] | _ :: _ :: _ :: _ => rfl
        have hGrindNone := grind_zero32_none _ _ _ _ _ _ hZeroHmsg q.grindLimit 0
        have hW : multiLeaf4JortsParams.w = 4 := rfl
        have hEll : multiLeaf4JortsParams.ell1 = 128 := rfl
        simp only [hSubLeaves, hSt, decide_true, Bool.and_self, ↓reduceIte, hW, hEll,
          multiLeaf4JortsParams_targetSum, hGrindNone]
      · have hRangeF : multiLeaf4JortsParams.productionLeafIdxInRange q.epoch = false := by
          rw [PqHashParams.productionLeafIdxInRange_eq, multiLeaf4JortsParams.public_eqs]
          simpa using hkp
        simp [hRangeF]
  · rw [ite_eq_right hGrind]
    have hz : q.grindLimit = 0 := by omega
    rw [prodSignQuery_eq]
    have hSt : multiLeaf4JortsParams.statefulJorts = true := rfl
    rw [ite_eq_left hSt, evalProductionStatefulSign_def]
    split
    · rfl
    · rw [signProductionHypertreeCore_def]
      have hNumLayers : multiLeaf4JortsParams.numLayers = 1 := rfl
      simp only [hSt, ↓reduceIte, hNumLayers, hz]
      rw [signProductionHypertreeLayers_succ]
      have hW : multiLeaf4JortsParams.w = 4 := rfl
      have hEll : multiLeaf4JortsParams.ell1 = 128 := rfl
      simp [hSt, hW, hEll, multiLeaf4JortsParams_targetSum, grindTswLeafCounterAux_zero]

/-- Extract the 1-byte step-0 preimage candidate from chain `r` of a `PqHashSig`. -/
def extractSigChainCand (sig : PqHashSig) (r : Nat) : Spec.Bytes :=
  match sig.layerSigs with
  | lsig :: _ =>
    match decodeStep0Byte (lsig.wotsChains.getD r []) with
    | some b => [b]
    | none => []
  | [] => []

private theorem invalid32_ne_tagged {tag b : UInt8} {rest : List UInt8}
    (hTag : tag ≠ 0xFF) : tag :: b :: rest ≠ invalid32 := by
  intro h
  unfold invalid32 at h
  injection h with hEq _
  exact hTag hEq

private theorem slice_mid_left (b0 b1 : UInt8) (a b pad : List UInt8)
    (ha : a.length = 6) (hb : b.length = 6) :
    ((([b0, b1] ++ a ++ b ++ pad).drop 2).take 12).take 6 = a := by
  have hDrop : ([b0, b1] ++ a ++ b ++ pad).drop 2 = (a ++ b) ++ pad := by
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.drop_succ_cons,
      List.drop_zero]
  rw [hDrop, List.take_left' (by rw [List.length_append, ha, hb]), List.take_left' ha]

private theorem slice_mid_right (b0 b1 : UInt8) (a b pad : List UInt8)
    (ha : a.length = 6) (hb : b.length = 6) :
    ((([b0, b1] ++ a ++ b ++ pad).drop 2).take 12).drop 6 = b := by
  have hDrop : ([b0, b1] ++ a ++ b ++ pad).drop 2 = (a ++ b) ++ pad := by
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.drop_succ_cons,
      List.drop_zero]
  rw [hDrop, List.take_left' (by rw [List.length_append, ha, hb]), List.drop_left' ha]

private theorem slice_top_left (b0 b1 : UInt8) (a b pad : List UInt8) (ha : a.length = 12) :
    (([b0, b1] ++ a ++ b ++ pad).drop 2).take 12 = a := by
  have hDrop : ([b0, b1] ++ a ++ b ++ pad).drop 2 = a ++ (b ++ pad) := by
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.drop_succ_cons,
      List.drop_zero]
  rw [hDrop, List.take_left' ha]

private theorem slice_top_right (b0 b1 : UInt8) (a b pad : List UInt8)
    (ha : a.length = 12) (hb : b.length = 12) :
    (([b0, b1] ++ a ++ b ++ pad).drop 14).take 12 = b := by
  have hDrop : ([b0, b1] ++ a ++ b ++ pad).drop 14 = (a ++ (b ++ pad)).drop 12 := by
    change ((b0 :: b1 :: ((a ++ b) ++ pad)).drop (2 + 12)) = _
    rw [← List.drop_drop, List.append_assoc]
    rfl
  rw [hDrop, List.drop_left' ha, List.take_left' hb]

private theorem rootFromTbl_slices (tbl : Nat → Nat → UInt8 × UInt8) :
    (((rootFromTbl tbl).drop 2).take 12).take 6 = packLeaf3 [tbl 0 0, tbl 0 1, tbl 0 2] ∧
    (((rootFromTbl tbl).drop 2).take 12).drop 6 = packLeaf3 [tbl 1 0, tbl 1 1, tbl 1 2] ∧
    (((rootFromTbl tbl).drop 14).take 12).take 6 = packLeaf3 [tbl 2 0, tbl 2 1, tbl 2 2] ∧
    (((rootFromTbl tbl).drop 14).take 12).drop 6 = packLeaf3 [tbl 3 0, tbl 3 1, tbl 3 2] := by
  unfold rootFromTbl packLeaf3
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem walkMerkle2_extract_leaf {pkSeed : List UInt8}
    {tbl : Nat → Nat → UInt8 × UInt8} {kp : Nat} {wotsPk : List UInt8}
    {authPath : List (List UInt8)} (hkp : kp < 4)
    (hWalk : walkMerkleAuthPathKp poly257MultiLeafSuite pkSeed 0 0 .tree 0 2 0 kp
      wotsPk authPath = some (rootFromTbl tbl)) :
    (wotsPk.drop 2).take 6 = packLeaf3 [tbl kp 0, tbl kp 1, tbl kp 2] ∧
    wotsPk ≠ invalid32 := by
  have hNotInvRoot : rootFromTbl tbl ≠ invalid32 :=
    invalid32_ne_tagged (by decide : (0xD2 : UInt8) ≠ 0xFF)
  have hCases : kp = 0 ∨ kp = 1 ∨ kp = 2 ∨ kp = 3 := by omega
  match authPath with
  | [] => cases hWalk
  | [_] => rcases hCases with rfl | rfl | rfl | rfl <;> cases hWalk
  | _ :: _ :: _ :: _ => rcases hCases with rfl | rfl | rfl | rfl <;> cases hWalk
  | [sibTop, sibBot] =>
    have h2 : (2 : UInt32).toNat = 2 := rfl
    have h1 : (1 : UInt32).toNat = 1 := rfl
    have h0 : (0 : UInt32).toNat = 0 := rfl
    rcases hCases with rfl | rfl | rfl | rfl
    · -- kp = 0
      unfold walkMerkleAuthPathKp at hWalk
      simp only [Nat.pow_succ, Nat.pow_zero, (by decide : 0 < 2),
        (by decide : 0 < 1), ↓reduceIte, walkMerkleAuthPathKp, Option.some.injEq] at hWalk
      let mid := thNodeH poly257MultiLeafSuite pkSeed ⟨0, 0, .tree, 0, 1, 0⟩ wotsPk sibBot
      have hTop : thNodeH poly257MultiLeafSuite pkSeed ⟨0, 0, .tree, 0, 2, 0⟩ mid sibTop =
          rootFromTbl tbl := hWalk
      rw [poly257MultiLeaf_thNodeH] at hTop
      simp only [h2, h0, (by decide : ¬ (2 = 1 ∧ 0 < 2)), and_self, ↓reduceIte] at hTop
      split at hTop
      · rename_i hcTop
        have hMid12 : ((mid.drop 2).take 12).length = 12 := by
          rw [List.length_take, List.length_drop, hcTop.2.2.1]; decide
        have hMidPay : ((mid.drop 2).take 12).take 6 =
            packLeaf3 [tbl 0 0, tbl 0 1, tbl 0 2] := by
          have hDrop2 := congrArg (fun l => ((l.drop 2).take 12).take 6) hTop
          rw [slice_top_left 0xD2 0 ((mid.drop 2).take 12) ((sibTop.drop 2).take 12)
            (List.replicate 6 0x00) hMid12, (rootFromTbl_slices tbl).1] at hDrop2
          exact hDrop2
        have hMidNeInv : mid ≠ invalid32 := by
          intro hEq; rw [hEq] at hcTop
          exact absurd hcTop.1 (by decide)
        dsimp only [mid] at hMidNeInv hMidPay
        rw [poly257MultiLeaf_thNodeH] at hMidNeInv hMidPay
        simp only [h1, h0, (by decide : 0 < 2), and_self, ↓reduceIte] at hMidNeInv hMidPay
        split at hMidNeInv
        · rename_i hcMid
          rw [ite_eq_left hcMid] at hMidPay
          have hLen6 : ((wotsPk.drop 2).take 6).length = 6 := by
            rw [List.length_take, List.length_drop, hcMid.2.2.1]; decide
          have hLen6R : ((sibBot.drop 2).take 6).length = 6 := by
            rw [List.length_take, List.length_drop, hcMid.2.2.2.2.2]; decide
          rw [slice_mid_left 0xD1 (UInt8.ofNat 0) ((wotsPk.drop 2).take 6) ((sibBot.drop 2).take 6)
            (List.replicate 18 0x00) hLen6 hLen6R] at hMidPay
          refine ⟨hMidPay, fun hInv => ?_⟩
          rw [hInv] at hcMid
          exact absurd hcMid.1 (by decide)
        · exact absurd rfl hMidNeInv
      · exact absurd hTop.symm hNotInvRoot
    · -- kp = 1
      unfold walkMerkleAuthPathKp at hWalk
      simp only [Nat.pow_succ, Nat.pow_zero, (by decide : 1 < 2),
        (by decide : ¬ (1 < 1)), ↓reduceIte, walkMerkleAuthPathKp, Option.some.injEq] at hWalk
      let mid := thNodeH poly257MultiLeafSuite pkSeed ⟨0, 0, .tree, 0, 1, 0⟩ sibBot wotsPk
      have hTop : thNodeH poly257MultiLeafSuite pkSeed ⟨0, 0, .tree, 0, 2, 0⟩ mid sibTop =
          rootFromTbl tbl := hWalk
      rw [poly257MultiLeaf_thNodeH] at hTop
      simp only [h2, h0, (by decide : ¬ (2 = 1 ∧ 0 < 2)), and_self, ↓reduceIte] at hTop
      split at hTop
      · rename_i hcTop
        have hMid12 : ((mid.drop 2).take 12).length = 12 := by
          rw [List.length_take, List.length_drop, hcTop.2.2.1]; decide
        have hMidPay : ((mid.drop 2).take 12).drop 6 =
            packLeaf3 [tbl 1 0, tbl 1 1, tbl 1 2] := by
          have hDrop2 := congrArg (fun l => ((l.drop 2).take 12).drop 6) hTop
          rw [slice_top_left 0xD2 0 ((mid.drop 2).take 12) ((sibTop.drop 2).take 12)
            (List.replicate 6 0x00) hMid12, (rootFromTbl_slices tbl).2.1] at hDrop2
          exact hDrop2
        have hMidNeInv : mid ≠ invalid32 := by
          intro hEq; rw [hEq] at hcTop
          exact absurd hcTop.1 (by decide)
        dsimp only [mid] at hMidNeInv hMidPay
        rw [poly257MultiLeaf_thNodeH] at hMidNeInv hMidPay
        simp only [h1, h0, (by decide : 0 < 2), and_self, ↓reduceIte] at hMidNeInv hMidPay
        split at hMidNeInv
        · rename_i hcMid
          rw [ite_eq_left hcMid] at hMidPay
          have hLen6L : ((sibBot.drop 2).take 6).length = 6 := by
            rw [List.length_take, List.length_drop, hcMid.2.2.1]; decide
          have hLen6 : ((wotsPk.drop 2).take 6).length = 6 := by
            rw [List.length_take, List.length_drop, hcMid.2.2.2.2.2]; decide
          rw [slice_mid_right 0xD1 (UInt8.ofNat 0) ((sibBot.drop 2).take 6) ((wotsPk.drop 2).take 6)
            (List.replicate 18 0x00) hLen6L hLen6] at hMidPay
          refine ⟨hMidPay, fun hInv => ?_⟩
          rw [hInv] at hcMid
          exact absurd hcMid.2.2.2.1 (by decide)
        · exact absurd rfl hMidNeInv
      · exact absurd hTop.symm hNotInvRoot
    · -- kp = 2
      unfold walkMerkleAuthPathKp at hWalk
      simp only [Nat.pow_succ, Nat.pow_zero, (by decide : ¬ (2 < 2)),
        (by decide : 0 < 1), ↓reduceIte, walkMerkleAuthPathKp, Option.some.injEq] at hWalk
      let mid := thNodeH poly257MultiLeafSuite pkSeed ⟨0, 0, .tree, 0, 1, 1⟩ wotsPk sibBot
      have hTop : thNodeH poly257MultiLeafSuite pkSeed ⟨0, 0, .tree, 0, 2, 0⟩ sibTop mid =
          rootFromTbl tbl := hWalk
      rw [poly257MultiLeaf_thNodeH] at hTop
      simp only [h2, h0, (by decide : ¬ (2 = 1 ∧ 0 < 2)), and_self, ↓reduceIte] at hTop
      split at hTop
      · rename_i hcTop
        have hSib12 : ((sibTop.drop 2).take 12).length = 12 := by
          rw [List.length_take, List.length_drop, hcTop.2.2.1]; decide
        have hMid12 : ((mid.drop 2).take 12).length = 12 := by
          rw [List.length_take, List.length_drop, hcTop.2.2.2.2.2]; decide
        have hMidPay : ((mid.drop 2).take 12).take 6 =
            packLeaf3 [tbl 2 0, tbl 2 1, tbl 2 2] := by
          have hDrop14 := congrArg (fun l => ((l.drop 14).take 12).take 6) hTop
          rw [slice_top_right 0xD2 0 ((sibTop.drop 2).take 12) ((mid.drop 2).take 12)
            (List.replicate 6 0x00) hSib12 hMid12, (rootFromTbl_slices tbl).2.2.1] at hDrop14
          exact hDrop14
        have hMidNeInv : mid ≠ invalid32 := by
          intro hEq; rw [hEq] at hcTop
          exact absurd hcTop.2.2.2.1 (by decide)
        dsimp only [mid] at hMidNeInv hMidPay
        rw [poly257MultiLeaf_thNodeH] at hMidNeInv hMidPay
        simp only [h1, (by decide : 1 < 2), and_self, ↓reduceIte] at hMidNeInv hMidPay
        split at hMidNeInv
        · rename_i hcMid
          rw [ite_eq_left hcMid] at hMidPay
          have hLen6 : ((wotsPk.drop 2).take 6).length = 6 := by
            rw [List.length_take, List.length_drop, hcMid.2.2.1]; decide
          have hLen6R : ((sibBot.drop 2).take 6).length = 6 := by
            rw [List.length_take, List.length_drop, hcMid.2.2.2.2.2]; decide
          rw [slice_mid_left 0xD1 (UInt8.ofNat 1) ((wotsPk.drop 2).take 6) ((sibBot.drop 2).take 6)
            (List.replicate 18 0x00) hLen6 hLen6R] at hMidPay
          refine ⟨hMidPay, fun hInv => ?_⟩
          rw [hInv] at hcMid
          exact absurd hcMid.1 (by decide)
        · exact absurd rfl hMidNeInv
      · exact absurd hTop.symm hNotInvRoot
    · -- kp = 3
      unfold walkMerkleAuthPathKp at hWalk
      simp only [Nat.pow_succ, Nat.pow_zero, (by decide : ¬ (3 < 2)),
        (by decide : ¬ (3 - 2 < 1)), ↓reduceIte, walkMerkleAuthPathKp, Option.some.injEq] at hWalk
      let mid := thNodeH poly257MultiLeafSuite pkSeed ⟨0, 0, .tree, 0, 1, 1⟩ sibBot wotsPk
      have hTop : thNodeH poly257MultiLeafSuite pkSeed ⟨0, 0, .tree, 0, 2, 0⟩ sibTop mid =
          rootFromTbl tbl := hWalk
      rw [poly257MultiLeaf_thNodeH] at hTop
      simp only [h2, h0, (by decide : ¬ (2 = 1 ∧ 0 < 2)), and_self, ↓reduceIte] at hTop
      split at hTop
      · rename_i hcTop
        have hSib12 : ((sibTop.drop 2).take 12).length = 12 := by
          rw [List.length_take, List.length_drop, hcTop.2.2.1]; decide
        have hMid12 : ((mid.drop 2).take 12).length = 12 := by
          rw [List.length_take, List.length_drop, hcTop.2.2.2.2.2]; decide
        have hMidPay : ((mid.drop 2).take 12).drop 6 =
            packLeaf3 [tbl 3 0, tbl 3 1, tbl 3 2] := by
          have hDrop14 := congrArg (fun l => ((l.drop 14).take 12).drop 6) hTop
          rw [slice_top_right 0xD2 0 ((sibTop.drop 2).take 12) ((mid.drop 2).take 12)
            (List.replicate 6 0x00) hSib12 hMid12, (rootFromTbl_slices tbl).2.2.2] at hDrop14
          exact hDrop14
        have hMidNeInv : mid ≠ invalid32 := by
          intro hEq; rw [hEq] at hcTop
          exact absurd hcTop.2.2.2.1 (by decide)
        dsimp only [mid] at hMidNeInv hMidPay
        rw [poly257MultiLeaf_thNodeH] at hMidNeInv hMidPay
        simp only [h1, (by decide : 1 < 2), and_self, ↓reduceIte] at hMidNeInv hMidPay
        split at hMidNeInv
        · rename_i hcMid
          rw [ite_eq_left hcMid] at hMidPay
          have hLen6L : ((sibBot.drop 2).take 6).length = 6 := by
            rw [List.length_take, List.length_drop, hcMid.2.2.1]; decide
          have hLen6 : ((wotsPk.drop 2).take 6).length = 6 := by
            rw [List.length_take, List.length_drop, hcMid.2.2.2.2.2]; decide
          rw [slice_mid_right 0xD1 (UInt8.ofNat 1) ((sibBot.drop 2).take 6) ((wotsPk.drop 2).take 6)
            (List.replicate 18 0x00) hLen6L hLen6] at hMidPay
          refine ⟨hMidPay, fun hInv => ?_⟩
          rw [hInv] at hcMid
          exact absurd hcMid.2.2.2.1 (by decide)
        · exact absurd rfl hMidNeInv
      · exact absurd hTop.symm hNotInvRoot

private theorem chain3_from_step0_sound (pkSeed : List UInt8) {kp r : Nat}
    (hkp : kp < 4) (hr : r < 3) {sigVal : List UInt8} {hi lo : UInt8}
    (hEnd : wotsChainSteps poly257MultiLeafSuite pkSeed 0 0 kp r 0 3 sigVal =
      encodeChainNode 0xB3 kp r hi lo) :
    ∃ b : UInt8,
      decodeStep0Byte sigVal = some b ∧
      (Spec.byteXorHash pkSeed (chain0Tweak kp r) [b]).headD 0 = hi ∧
      (Spec.poly257Hash pkSeed (chain0Tweak kp r) [b]).getD 2 0 = lo := by
  have hkp32 : (UInt32.ofNat kp).toNat = kp := u32_toNat_small (by omega)
  have hr32 : (UInt32.ofNat r).toNat = r := u32_toNat_small (by omega)
  have hNotInv3 : encodeChainNode 0xB3 kp r hi lo ≠ invalid32 :=
    invalid32_ne_tagged (by decide : (0xB3 : UInt8) ≠ 0xFF)
  rw [wotsChainSteps_succ, wotsChainSteps_succ, wotsChainSteps_succ, wotsChainSteps_zero] at hEnd
  let s1 := thChainF poly257MultiLeafSuite pkSeed ⟨0, 0, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, 0⟩ sigVal
  let s2 := thChainF poly257MultiLeafSuite pkSeed ⟨0, 0, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, 1⟩ s1
  have hStep2 : thChainF poly257MultiLeafSuite pkSeed ⟨0, 0, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, 2⟩ s2 =
      encodeChainNode 0xB3 kp r hi lo := hEnd
  rw [poly257MultiLeaf_thChainF] at hStep2
  dsimp only at hStep2
  simp only [hkp32, hr32, hkp, hr, and_self, ↓reduceIte] at hStep2
  cases hDec2 : decodeChainNode 0xB2 kp r s2 with
  | none => rw [hDec2] at hStep2; exact absurd hStep2.symm hNotInv3
  | some p2 =>
    rcases p2 with ⟨hi2, lo2⟩
    rw [hDec2] at hStep2
    obtain ⟨rfl, rfl⟩ := encodeChainNode_inj hStep2
    have hs2Eq := decodeChainNode_sound hDec2
    dsimp only [s2] at hs2Eq
    have hNotInv2 : encodeChainNode 0xB2 kp r hi2 lo2 ≠ invalid32 :=
      invalid32_ne_tagged (by decide : (0xB2 : UInt8) ≠ 0xFF)
    rw [poly257MultiLeaf_thChainF] at hs2Eq
    dsimp only at hs2Eq
    simp only [hkp32, hr32, hkp, hr, and_self, ↓reduceIte] at hs2Eq
    cases hDec1 : decodeChainNode 0xB1 kp r s1 with
    | none => rw [hDec1] at hs2Eq; exact absurd hs2Eq.symm hNotInv2
    | some p1 =>
      rcases p1 with ⟨hi1, lo1⟩
      rw [hDec1] at hs2Eq
      obtain ⟨rfl, rfl⟩ := encodeChainNode_inj hs2Eq
      have hs1Eq := decodeChainNode_sound hDec1
      dsimp only [s1] at hs1Eq
      have hNotInv1 : encodeChainNode 0xB1 kp r hi1 lo1 ≠ invalid32 :=
        invalid32_ne_tagged (by decide : (0xB1 : UInt8) ≠ 0xFF)
      rw [poly257MultiLeaf_thChainF] at hs1Eq
      dsimp only at hs1Eq
      simp only [hkp32, hr32, hkp, hr, and_self, ↓reduceIte] at hs1Eq
      cases hDec0 : decodeStep0Byte sigVal with
      | none => rw [hDec0] at hs1Eq; exact absurd hs1Eq.symm hNotInv1
      | some b =>
        rw [hDec0] at hs1Eq
        obtain ⟨hHi, hLo⟩ := encodeChainNode_inj hs1Eq
        exact ⟨b, rfl, hHi, hLo⟩

private theorem verifyProductionPqHashSig_poly257MultiLeaf_sound
    (sk : PqSecretKey) (msg : List UInt8) (sig : PqHashSig)
    (hVer : verifyProductionPqHashSig poly257MultiLeafSuite multiLeaf4JortsParams
      (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk) msg sig = true) :
    sig.leafGlobalIdx < 4 ∧
    ∃ sub : Nat, sub < 3 ∧ msg = [UInt8.ofNat sig.leafGlobalIdx, UInt8.ofNat sub] ∧
      ∀ r : Nat, r < 3 →
        (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg sub)).getD r 0 = 0 →
        extractSigChainCand sig r = [sk.skSeed.getD (3 * sig.leafGlobalIdx + r) 0] := by
  rw [derivePublicKey_poly257MultiLeaf sk] at hVer
  dsimp only [pkFromTbl] at hVer
  rw [verifyProductionPqHashSig_eq] at hVer
  cases hRange : multiLeaf4JortsParams.productionLeafIdxInRange sig.leafGlobalIdx with
  | false => simp [multiLeaf4JortsParams_productionWellFormed, hRange] at hVer
  | true =>
    have hkp : sig.leafGlobalIdx < 4 := by
      rw [PqHashParams.productionLeafIdxInRange_eq, multiLeaf4JortsParams.public_eqs] at hRange
      simpa using hRange
    simp only [multiLeaf4JortsParams_productionWellFormed, hRange, Bool.not_true, Bool.or_self,
      Bool.false_eq_true, ↓reduceIte] at hVer
    match hLs : sig.layerSigs with
    | [] =>
      have hNe : sig.layerSigs.length ≠ multiLeaf4JortsParams.numLayers := by
        rw [hLs, multiLeaf4JortsParams.public_eqs]; decide
      rw [decide_eq_true hNe] at hVer
      simp only [Bool.true_or, ↓reduceIte] at hVer
      cases hVer
    | _ :: _ :: _ =>
      have hNe : sig.layerSigs.length ≠ multiLeaf4JortsParams.numLayers := by
        rw [hLs, multiLeaf4JortsParams.public_eqs]
        exact fun h => Nat.noConfusion (Nat.succ.inj h)
      rw [decide_eq_true hNe] at hVer
      simp only [Bool.true_or, ↓reduceIte] at hVer
      cases hVer
    | [lsig] =>
      rw [hLs] at hVer
      by_cases hCtr0 : sig.msgTswCtr = 0
      · by_cases hFors : sig.forsOpenings = []
        · simp only [hCtr0, hFors, multiLeaf4JortsParams.public_eqs, List.length_singleton,
            ne_eq, not_true_eq_false, Bool.or_self, ↓reduceIte,
            List.isEmpty_nil] at hVer
          rw [verifyProductionHypertreeLayers_cons] at hVer
          by_cases hTswLt : lsig.tswCtr < 2 ^ 32
          · simp only [hTswLt, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hVer
            have hMod : sig.leafGlobalIdx % 4 = sig.leafGlobalIdx := Nat.mod_eq_of_lt hkp
            have hDiv : sig.leafGlobalIdx / 4 = 0 := Nat.div_eq_of_lt hkp
            have hkp32 : (UInt32.ofNat sig.leafGlobalIdx).toNat = sig.leafGlobalIdx :=
              u32_toNat_small (by omega)
            rw [productionLayerDigest_eq] at hVer
            simp only [decide_true, Bool.and_self, ↓reduceIte, hMod, hDiv] at hVer
            have hTgtRaw : (PqHashParams.mk 4 128 2 1 0 0 2 true).targetSum = 192 := by
              rw [PqHashParams.targetSum_eq]; decide
            have hExtZ : extractBaseWDigitsChecked 4 128 zero32 =
                some (extractBaseWDigits 4 128 zero32) := by
              have h := extractBaseWDigitsChecked_of_productionWellFormed
                multiLeaf4JortsParams multiLeaf4JortsParams_productionWellFormed zero32 rfl
              rw [multiLeaf4JortsParams.public_eqs] at h
              exact h
            have hInvMatch :
                (match invalid32 with
                 | 0xE0 :: kpB :: subB :: rest =>
                   if kpB.toNat < 4 ∧ subB.toNat < 3 ∧
                       kpB.toNat = (UInt32.ofNat sig.leafGlobalIdx).toNat ∧
                       rest = List.replicate 29 0x00 then
                     encodeSubMsg3Hmsg subB.toNat
                   else zero32
                 | _ => zero32) = zero32 := rfl
            have hHmsgValid : ∃ sub : Nat, sub < 3 ∧
                msg = [UInt8.ofNat sig.leafGlobalIdx, UInt8.ofNat sub] ∧
                thHashLeafMsg poly257MultiLeafSuite sig.rRand sk.pkSeed
                  (rootFromTbl (honestSlotHiLo sk))
                  (thPreHash poly257MultiLeafSuite sk.pkSeed
                    (rootFromTbl (honestSlotHiLo sk)) msg)
                  (UInt64.ofNat 0) (UInt32.ofNat sig.leafGlobalIdx) lsig.tswCtr =
                  encodeSubMsg3Hmsg sub := by
              rw [poly257MultiLeaf_thHashLeafMsg, poly257MultiLeaf_thPreHash] at hVer ⊢
              match msg with
              | [kpB, subB] =>
                dsimp only at hVer ⊢
                by_cases hB : kpB.toNat < 4 ∧ subB.toNat < 3
                · rw [ite_eq_left hB] at hVer ⊢
                  simp only [List.cons_append, List.nil_append] at hVer ⊢
                  by_cases hEqKp : kpB.toNat = sig.leafGlobalIdx
                  · have hc : kpB.toNat < 4 ∧ subB.toNat < 3 ∧
                        kpB.toNat = (UInt32.ofNat sig.leafGlobalIdx).toNat ∧ True :=
                      ⟨hB.1, hB.2, hEqKp.trans hkp32.symm, trivial⟩
                    rw [ite_eq_left hc]
                    refine ⟨subB.toNat, hB.2, ?_, rfl⟩
                    rw [← hEqKp, UInt8.ofNat_toNat, UInt8.ofNat_toNat]
                  · have hnc : ¬ (kpB.toNat < 4 ∧ subB.toNat < 3 ∧
                        kpB.toNat = (UInt32.ofNat sig.leafGlobalIdx).toNat ∧ True) := by
                      rw [hkp32]; intro h; exact hEqKp h.2.2.1
                    rw [ite_eq_right hnc, hExtZ] at hVer
                    dsimp only at hVer
                    rw [hTgtRaw, zero32_checkTargetSum_false] at hVer
                    simp only [Bool.not_false, ↓reduceIte] at hVer
                    cases hVer
                · rw [ite_eq_right hB, hInvMatch, hExtZ] at hVer
                  dsimp only at hVer
                  rw [hTgtRaw, zero32_checkTargetSum_false] at hVer
                  simp only [Bool.not_false, ↓reduceIte] at hVer
                  cases hVer
              | [] | [_] | _ :: _ :: _ :: _ =>
                dsimp only at hVer
                rw [hInvMatch, hExtZ] at hVer
                dsimp only at hVer
                rw [hTgtRaw, zero32_checkTargetSum_false] at hVer
                simp only [Bool.not_false, ↓reduceIte] at hVer
                cases hVer
            obtain ⟨sub, hSubLt, hMsgEq, hHmsgEq⟩ := hHmsgValid
            rw [hHmsgEq] at hVer
            have hEv := encodeSubMsg3Hmsg_digits_eval ⟨sub, hSubLt⟩
            dsimp only at hEv
            rw [hEv.1] at hVer
            dsimp only at hVer
            rw [hTgtRaw, hEv.2] at hVer
            by_cases hChLen : lsig.wotsChains.length = 128
            · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hChLen, ne_eq,
                not_true_eq_false] at hVer
              have hu32_0 : UInt32.ofNat 0 = 0 := rfl
              have hu64_0 : UInt64.ofNat 0 = 0 := rfl
              rw [hu32_0, hu64_0, ← multiLeaf4JortsParams.public_eqs] at hVer
              cases hWalk : walkMerkleAuthPathKp poly257MultiLeafSuite sk.pkSeed 0 0 .tree 0
                  2 0 sig.leafGlobalIdx
                  (recoverWotsPkFromSig poly257MultiLeafSuite multiLeaf4JortsParams sk.pkSeed
                    0 0 sig.leafGlobalIdx (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg sub))
                    lsig.wotsChains)
                  lsig.authPath with
              | none => rw [hWalk] at hVer; dsimp only at hVer; cases hVer
              | some topRoot =>
                rw [hWalk] at hVer
                dsimp only at hVer
                rw [verifyProductionHypertreeLayers_nil] at hVer
                dsimp only at hVer
                have hRootEq : topRoot = rootFromTbl (honestSlotHiLo sk) :=
                  of_decide_eq_true hVer
                rw [hRootEq] at hWalk
                obtain ⟨hWotsPay, hWotsNeInv⟩ := walkMerkle2_extract_leaf hkp hWalk
                rw [recoverWotsPkFromSig_eq, poly257MultiLeaf_thTweakTl] at hWotsPay hWotsNeInv
                simp only [hkp32, hkp, and_self, multiLeaf4JortsParams.public_eqs,
                  ↓reduceIte] at hWotsPay hWotsNeInv
                cases hAct3 : extractActive3 sig.leafGlobalIdx
                    (recoverWotsEndpoints poly257MultiLeafSuite
                      (PqHashParams.mk 4 128 2 1 0 0 2 true) sk.pkSeed 0 0 sig.leafGlobalIdx
                      (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg sub)) lsig.wotsChains) with
                | none => rw [hAct3] at hWotsNeInv; exact absurd rfl hWotsNeInv
                | some ps =>
                  rw [hAct3] at hWotsPay
                  unfold extractActive3 at hAct3
                  rw [recoverWotsEndpoints_eq] at hAct3
                  dsimp only at hAct3
                  rw [range128_split3, List.map_cons, List.map_cons, List.map_cons] at hAct3
                  dsimp only at hAct3
                  split at hAct3
                  · cases hD0 : decodeChainNode 0xB3 sig.leafGlobalIdx 0 _ with
                    | none => rw [hD0] at hAct3; cases hAct3
                    | some p0 =>
                      cases hD1 : decodeChainNode 0xB3 sig.leafGlobalIdx 1 _ with
                      | none => rw [hD0, hD1] at hAct3; cases hAct3
                      | some p1 =>
                        cases hD2 : decodeChainNode 0xB3 sig.leafGlobalIdx 2 _ with
                        | none => rw [hD0, hD1, hD2] at hAct3; cases hAct3
                        | some p2 =>
                          rw [hD0, hD1, hD2] at hAct3
                          injection hAct3 with hPs
                          subst hPs
                          have hTakePay : (([0xC0, UInt8.ofNat sig.leafGlobalIdx] ++
                              packLeaf3 [p0, p1, p2] ++ List.replicate 24 0x00).drop 2).take 6 =
                              packLeaf3 [p0, p1, p2] := rfl
                          rw [hTakePay] at hWotsPay
                          obtain ⟨hp0, hp1, hp2⟩ := packLeaf3_inj hWotsPay
                          refine ⟨hkp, sub, hSubLt, hMsgEq, ?_⟩
                          intro r hr hZeroDig
                          have hExtr : extractSigChainCand sig r =
                              match decodeStep0Byte (lsig.wotsChains.getD r []) with
                              | some b => [b]
                              | none => [] := by
                            unfold extractSigChainCand; rw [hLs]
                          rw [hExtr]
                          have hrCases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
                          rcases hrCases with rfl | rfl | rfl
                          · have hSnd := decodeChainNode_sound hD0
                            rw [hZeroDig, hp0] at hSnd
                            obtain ⟨b, hB, hHi, _⟩ :=
                              chain3_from_step0_sound sk.pkSeed hkp (by decide) hSnd
                            rw [hB]
                            exact congrArg (· :: []) (byteXorHash_headD_inj _ _ hHi)
                          · have hSnd := decodeChainNode_sound hD1
                            rw [hZeroDig, hp1] at hSnd
                            obtain ⟨b, hB, hHi, _⟩ :=
                              chain3_from_step0_sound sk.pkSeed hkp (by decide) hSnd
                            rw [hB]
                            exact congrArg (· :: []) (byteXorHash_headD_inj _ _ hHi)
                          · have hSnd := decodeChainNode_sound hD2
                            rw [hZeroDig, hp2] at hSnd
                            obtain ⟨b, hB, hHi, _⟩ :=
                              chain3_from_step0_sound sk.pkSeed hkp (by decide) hSnd
                            rw [hB]
                            exact congrArg (· :: []) (byteXorHash_headD_inj _ _ hHi)
                  · cases hAct3
            · simp [hChLen] at hVer
          · simp [hTswLt] at hVer
        · have hNotEmpty : (!sig.forsOpenings.isEmpty) = true := by
            cases hF : sig.forsOpenings with
            | nil => exact absurd hF hFors
            | cons _ _ => rfl
          simp [hCtr0, hNotEmpty, multiLeaf4JortsParams.public_eqs] at hVer
      · simp [hCtr0] at hVer

/-! #### Punctured Multi-Leaf Signing Oracle Simulator & $q$-Query Adaptive Reduction -/

/-- Embed one of the `12` active `(kp, r)` chain slots (`kp < 4, r < 3`) into `Fin 24`. -/
def slot24Of12 (s : Fin 12) : Fin 24 :=
  ⟨s.1, Nat.lt_trans s.2 (by decide)⟩

private theorem insertByteAt_getD_ne :
    ∀ (idx : Nat) (b₁ b₂ : UInt8) (xs : Spec.Bytes) (j : Nat),
      idx ≤ xs.length → j ≠ idx →
      (insertByteAt idx b₁ xs).getD j 0 = (insertByteAt idx b₂ xs).getD j 0
  | 0, _, _, _, 0, _, hNe => absurd rfl hNe
  | 0, _, _, _, _ + 1, _, _ => rfl
  | _ + 1, _, _, [], _, hIdx, _ => absurd hIdx (Nat.not_succ_le_zero _)
  | _ + 1, _, _, _ :: _, 0, _, _ => rfl
  | i + 1, b₁, b₂, _ :: xs, j + 1, hIdx, hNe =>
    insertByteAt_getD_ne i b₁ b₂ xs j (Nat.le_of_succ_le_succ hIdx)
      (fun h => hNe (congrArg Nat.succ h))

/-- Reconstruct the full `(hi, lo)` endpoint table from the public `0xB3` endpoint `endpt` at
    punctured slot `s : Fin 12` and the `23` non-punctured secret bytes `other23`. -/
def puncturedSlotTbl (pkSeed : List UInt8) (s : Fin 12) (endpt : UInt8 × UInt8)
    (other23 : Spec.Bytes) (kp r : Nat) : UInt8 × UInt8 :=
  if 3 * kp + r = s.1 then
    endpt
  else
    let skDummy : PqSecretKey := ⟨insertByteAt s.1 0x00 other23, [], pkSeed⟩
    honestSlotHiLo skDummy kp r

/-- Simulate `prodSignQuery` across all `4` leaves without knowing secret byte `s : Fin 12`, using
    the public `0xB3` endpoint `endpt` whenever a query on leaf `s / 3` has base-4 digit `3` at
    chain `s % 3`. -/
def puncturedSignQuery (pkSeed : List UInt8) (s : Fin 12) (endpt : UInt8 × UInt8)
    (other23 : Spec.Bytes) (q : ProdSigningQuery) : Option PqHashSig :=
  if 0 < q.grindLimit then
    match queryMsgValidAt q.epoch q.message with
    | none => none
    | some sub =>
      let digits := extractBaseWDigits 4 128 (encodeSubMsg3Hmsg sub)
      if q.epoch = s.1 / 3 ∧ digits.getD (s.1 % 3) 0 ≠ 3 then
        none
      else
        let skDummy : PqSecretKey := ⟨insertByteAt s.1 0x00 other23, [], pkSeed⟩
        let tbl := puncturedSlotTbl pkSeed s endpt other23
        let wotsChains := (List.range 128).map fun r =>
          if q.epoch = s.1 / 3 ∧ r = s.1 % 3 then
            encodeChainNode 0xB3 q.epoch r endpt.1 endpt.2
          else
            let dr := digits.getD r 0
            wotsChainSteps poly257MultiLeafSuite pkSeed 0 0 q.epoch r 0 dr
              (wotsSecretBase poly257MultiLeafSuite skDummy 0 0 q.epoch r)
        some
          { rRand := zero32
            msgTswCtr := 0
            leafGlobalIdx := q.epoch
            forsOpenings := []
            layerSigs := [⟨0, wotsChains, authPathFromTbl tbl q.epoch⟩] }
  else none

/-- Compatibility of a signing query `q` with puncturing active chain slot `s : Fin 12`: if `q` is
    a valid signing query on leaf `s / 3`, its sub-message has base-4 digit `3` on chain `s % 3`
    (so `prodSignQuery` only reveals the `0xB3` endpoint and never reveals `sk.skSeed[s]`). -/
def QuerySlotCompat (s : Fin 12) (q : ProdSigningQuery) : Prop :=
  0 < q.grindLimit →
    ∀ sub : Nat, queryMsgValidAt q.epoch q.message = some sub →
      q.epoch = s.1 / 3 →
      (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg sub)).getD (s.1 % 3) 0 = 3

private theorem puncturedSlotTbl_eq_honest (sk : PqSecretKey) (s : Fin 12)
    (other23 : Spec.Bytes) (hLen23 : other23.length = 23)
    (hIns : insertByteAt s.1 (sk.skSeed.getD s.1 0) other23 = sk.skSeed) :
    ∀ kp r : Nat, kp < 4 → r < 3 →
      puncturedSlotTbl sk.pkSeed s (honestSlotHiLo sk (s.1 / 3) (s.1 % 3)) other23 kp r =
        honestSlotHiLo sk kp r := by
  intro kp r hkp hr
  unfold puncturedSlotTbl honestSlotHiLo
  by_cases hEq : 3 * kp + r = s.1
  · rw [ite_eq_left hEq]
    have hDiv : s.1 / 3 = kp := by omega
    have hMod : s.1 % 3 = r := by omega
    rw [hDiv, hMod]
  · rw [ite_eq_right hEq]
    dsimp only
    have hIdxLe : s.1 ≤ other23.length := by rw [hLen23]; have := s.2; omega
    have hByteEq : (insertByteAt s.1 0x00 other23).getD (3 * kp + r) 0 =
        sk.skSeed.getD (3 * kp + r) 0 := by
      rw [insertByteAt_getD_ne s.1 0x00 (sk.skSeed.getD s.1 0) other23 (3 * kp + r) hIdxLe hEq,
        hIns]
    rw [hByteEq]

private theorem authPathFromTbl_congr {tbl₁ tbl₂ : Nat → Nat → UInt8 × UInt8}
    (hEq : ∀ kp r : Nat, kp < 4 → r < 3 → tbl₁ kp r = tbl₂ kp r) (kp : Nat) :
    authPathFromTbl tbl₁ kp = authPathFromTbl tbl₂ kp := by
  have hLeaf : ∀ j : Nat, j < 4 → leafFromTbl tbl₁ j = leafFromTbl tbl₂ j := fun j hj => by
    unfold leafFromTbl
    rw [hEq j 0 hj (by decide), hEq j 1 hj (by decide), hEq j 2 hj (by decide)]
  have hNode : ∀ idx : Nat, idx < 2 → node1FromTbl tbl₁ idx = node1FromTbl tbl₂ idx :=
    fun idx hi => by
      unfold node1FromTbl
      rw [hEq (2 * idx) 0 (by omega) (by decide), hEq (2 * idx) 1 (by omega) (by decide),
        hEq (2 * idx) 2 (by omega) (by decide), hEq (2 * idx + 1) 0 (by omega) (by decide),
        hEq (2 * idx + 1) 1 (by omega) (by decide), hEq (2 * idx + 1) 2 (by omega) (by decide)]
  unfold authPathFromTbl
  repeat' split
  all_goals simp [hLeaf 0 (by decide), hLeaf 1 (by decide), hLeaf 2 (by decide),
    hLeaf 3 (by decide), hNode 0 (by decide), hNode 1 (by decide)]

private theorem rootFromTbl_congr {tbl₁ tbl₂ : Nat → Nat → UInt8 × UInt8}
    (hEq : ∀ kp r : Nat, kp < 4 → r < 3 → tbl₁ kp r = tbl₂ kp r) :
    rootFromTbl tbl₁ = rootFromTbl tbl₂ := by
  unfold rootFromTbl
  rw [hEq 0 0 (by decide) (by decide), hEq 0 1 (by decide) (by decide),
    hEq 0 2 (by decide) (by decide), hEq 1 0 (by decide) (by decide),
    hEq 1 1 (by decide) (by decide), hEq 1 2 (by decide) (by decide),
    hEq 2 0 (by decide) (by decide), hEq 2 1 (by decide) (by decide),
    hEq 2 2 (by decide) (by decide), hEq 3 0 (by decide) (by decide),
    hEq 3 1 (by decide) (by decide), hEq 3 2 (by decide) (by decide)]

private theorem puncturedSignQuery_eq_prodSignQuery
    (sk : PqSecretKey) (s : Fin 12) (other23 : Spec.Bytes) (hLen23 : other23.length = 23)
    (hIns : insertByteAt s.1 (sk.skSeed.getD s.1 0) other23 = sk.skSeed)
    (q : ProdSigningQuery) (hCompat : QuerySlotCompat s q) :
    puncturedSignQuery sk.pkSeed s (honestSlotHiLo sk (s.1 / 3) (s.1 % 3)) other23 q =
      prodSignQuery poly257MultiLeafSuite multiLeaf4JortsParams sk q := by
  rw [prodSignQuery_poly257MultiLeaf_characterize]
  unfold puncturedSignQuery
  by_cases hGrind : 0 < q.grindLimit
  · rw [ite_eq_left hGrind, ite_eq_left hGrind]
    cases hVal : queryMsgValidAt q.epoch q.message with
    | none => rfl
    | some sub =>
      dsimp only
      have hkp : q.epoch < 4 := by
        unfold queryMsgValidAt at hVal
        match q.message, hVal with
        | [_, _], hVal =>
          dsimp only at hVal
          split at hVal
          · rename_i hc; exact hc.2.1
          · cases hVal
        | [], hVal | [_], hVal | _ :: _ :: _ :: _, hVal => cases hVal
      have hNoAbort : ¬ (q.epoch = s.1 / 3 ∧
          (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg sub)).getD (s.1 % 3) 0 ≠ 3) := by
        intro hc
        exact hc.2 (hCompat hGrind sub hVal hc.1)
      rw [ite_eq_right hNoAbort]
      unfold honestMultiLeafSig
      congr 1; congr 1; congr 1; congr 1
      · apply List.map_congr_left
        intro r hrMem
        have hr128 : r < 128 := List.mem_range.mp hrMem
        by_cases hHit : q.epoch = s.1 / 3 ∧ r = s.1 % 3
        · rw [ite_eq_left hHit]
          have hDig3 := hCompat hGrind sub hVal hHit.1
          rw [← hHit.2] at hDig3
          rw [hDig3]
          have hr3 : r < 3 := by rw [hHit.2]; exact Nat.mod_lt _ (by decide)
          have hkp32 : (UInt32.ofNat q.epoch).toNat = q.epoch := u32_toNat_small (by omega)
          have hr32 : (UInt32.ofNat r).toNat = r := u32_toNat_small (by omega)
          rw [wotsSecretBase_eq, poly257MultiLeaf_thSecretPrf]
          simp only [hkp32, hr32, hkp, hr3, and_self, ↓reduceIte]
          have hSlotEq : 3 * q.epoch + r = s.1 := by omega
          rw [hSlotEq, active_chain_steps_3 sk.pkSeed hkp hr3 (sk.skSeed.getD s.1 0)]
          unfold honestSlotHiLo
          dsimp only
          rw [← hHit.1, ← hHit.2, hSlotEq]
        · rw [ite_eq_right hHit]
          congr 1
          rw [wotsSecretBase_eq, wotsSecretBase_eq, poly257MultiLeaf_thSecretPrf,
            poly257MultiLeaf_thSecretPrf]
          have hkp32 : (UInt32.ofNat q.epoch).toNat = q.epoch := u32_toNat_small (by omega)
          have hr32 : (UInt32.ofNat r).toNat = r := u32_toNat_small (by omega)
          by_cases hr3 : r < 3
          · simp only [hkp32, hr32, hkp, hr3, and_self, ↓reduceIte]
            have hSlotNe : 3 * q.epoch + r ≠ s.1 := by
              intro hEq
              exact hHit ⟨by omega, by omega⟩
            have hIdxLe : s.1 ≤ other23.length := by rw [hLen23]; have := s.2; omega
            rw [insertByteAt_getD_ne s.1 0x00 (sk.skSeed.getD s.1 0) other23
              (3 * q.epoch + r) hIdxLe hSlotNe, hIns]
          · have hNot : ¬ (q.epoch < 4 ∧ r < 3) := by omega
            simp only [hkp32, hr32, hNot, ↓reduceIte]
      · exact authPathFromTbl_congr (puncturedSlotTbl_eq_honest sk s other23 hLen23 hIns) q.epoch
  · rw [ite_eq_right hGrind, ite_eq_right hGrind]

private theorem evalLatchedAdaptiveTree_congr_on_log {α : Type}
    (rawHash : List UInt8 → List UInt8)
    (sign₁ sign₂ : ProdSigningQuery → Option PqHashSig) :
    ∀ (prog : ProdAdaptiveTree α) (lo : Nat),
      (∀ q ∈ (evalLatchedAdaptiveTree true rawHash sign₂ prog lo).2, sign₁ q = sign₂ q) →
      evalLatchedAdaptiveTree true rawHash sign₁ prog lo =
        evalLatchedAdaptiveTree true rawHash sign₂ prog lo
  | .pure _, _, _ => rfl
  | .hashQuery x next, lo, hLog =>
    evalLatchedAdaptiveTree_congr_on_log rawHash sign₁ sign₂ (next (rawHash x)) lo hLog
  | .signQuery q next, lo, hLog => by
    rw [evalLatchedAdaptiveTree_sign, evalLatchedAdaptiveTree_sign]
    by_cases hLo : lo ≤ q.epoch
    · rw [ite_eq_left (Or.inr hLo), ite_eq_left (Or.inr hLo)]
      have hHeadEq : sign₁ q = sign₂ q := by
        refine hLog q ?_
        rw [evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inr hLo)]
        exact List.mem_cons_self
      rw [hHeadEq]
      have ih := evalLatchedAdaptiveTree_congr_on_log rawHash sign₁ sign₂ (next (sign₂ q))
        (q.epoch + 1) (fun q' hq' => hLog q' (by
          rw [evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inr hLo)]
          exact List.mem_cons_of_mem q hq'))
      rw [ih]
    · have hNot : ¬ ((true = false) ∨ lo ≤ q.epoch) := fun hOr =>
        hOr.elim (fun hb => Bool.noConfusion hb) hLo
      rw [ite_eq_right hNot, ite_eq_right hNot]
      exact evalLatchedAdaptiveTree_congr_on_log rawHash sign₁ sign₂ (next none) lo (fun q' hq' =>
        hLog q' (by
          rw [evalLatchedAdaptiveTree_sign, ite_eq_right hNot]
          exact hq'))

theorem puncturedKeyAndAdvSplit_coords {nA : Nat} (s : Fin 12)
    (ω : Fin ((256 * pow256 24) * nA)) :
    let π₀ := Spec.CoinSplit.prod (256 * pow256 24) nA
    let πs := puncturedKeyAndAdvSplit nA (slot24Of12 s)
    let sk := multiLeaf24Keygen (π₀.chal ω)
    let spAdv := Spec.CoinSplit.prod (pow256 23) nA
    let other23 := byteVecSampler 23 (spAdv.chal (πs.advc ω))
    (Spec.byte1SeedAndPreSampler (πs.chal ω)).1 = sk.pkSeed ∧
    (Spec.byte1SeedAndPreSampler (πs.chal ω)).2 = [[sk.skSeed.getD s.1 0]] ∧
    spAdv.advc (πs.advc ω) = π₀.advc ω ∧
    other23.length = 23 ∧
    insertByteAt s.1 (sk.skSeed.getD s.1 0) other23 = sk.skSeed := by
  intro π₀ πs sk spAdv other23
  let spKey := Spec.CoinSplit.prod 256 (pow256 24)
  let s24 := slot24Of12 s
  have hSplit :
      (byteVecSampler 24 (spKey.advc (π₀.chal ω))).getD s.1 0 =
        UInt8.ofNat ((splitByteVecAt 23 s24).chal (spKey.advc (π₀.chal ω))).1 ∧
      insertByteAt s.1 (UInt8.ofNat ((splitByteVecAt 23 s24).chal (spKey.advc (π₀.chal ω))).1)
        (byteVecSampler 23 ((splitByteVecAt 23 s24).advc (spKey.advc (π₀.chal ω)))) =
        byteVecSampler 24 (spKey.advc (π₀.chal ω)) :=
    splitByteVecAt_getD_and_insert 23 s24 (spKey.advc (π₀.chal ω))
  have hChalEq : πs.chal ω = (Spec.CoinSplit.prod 256 256).pair
      (spKey.chal (π₀.chal ω)) ((splitByteVecAt 23 s24).chal (spKey.advc (π₀.chal ω))) := rfl
  have hAdvcChal : spAdv.chal (πs.advc ω) =
      (splitByteVecAt 23 s24).advc (spKey.advc (π₀.chal ω)) := by
    show spAdv.chal (spAdv.pair _ _) = _
    rw [spAdv.chal_pair]
  have hAdvcAdvc : spAdv.advc (πs.advc ω) = π₀.advc ω := by
    show spAdv.advc (spAdv.pair _ _) = _
    rw [spAdv.advc_pair]
  have hSkEq : sk = ⟨byteVecSampler 24 (spKey.advc (π₀.chal ω)), [],
      Spec.byte1SeedSampler (spKey.chal (π₀.chal ω))⟩ := by
    dsimp only [sk]; rw [multiLeaf24Keygen.public_eqs]
  refine ⟨?_, ?_, hAdvcAdvc, byteVecSampler_length 23 _, ?_⟩
  · rw [hChalEq, Spec.byte1SeedAndPreSampler_eq, (Spec.CoinSplit.prod 256 256).chal_pair, hSkEq,
      Spec.byte1SeedSampler.public_eqs]
  · rw [hChalEq, Spec.byte1SeedAndPreSampler_eq, (Spec.CoinSplit.prod 256 256).advc_pair,
      hSkEq]
    dsimp only
    rw [← hSplit.1]
  · dsimp only [other23]
    rw [hAdvcChal, hSkEq]
    dsimp only
    rw [hSplit.1]
    exact hSplit.2

private def findSignedSubAtLeaf (kp : Nat) : List ProdSigningQuery → Option (ProdSigningQuery × Nat)
  | [] => none
  | q :: qs =>
    if 0 < q.grindLimit then
      match queryMsgValidAt q.epoch q.message with
      | some sub => if q.epoch = kp then some (q, sub) else findSignedSubAtLeaf kp qs
      | none => findSignedSubAtLeaf kp qs
    else findSignedSubAtLeaf kp qs

private theorem findSignedSubAtLeaf_some {kp : Nat} :
    ∀ {qs : List ProdSigningQuery} {q₀ : ProdSigningQuery} {sub : Nat},
      findSignedSubAtLeaf kp qs = some (q₀, sub) →
      q₀ ∈ qs ∧ 0 < q₀.grindLimit ∧ queryMsgValidAt q₀.epoch q₀.message = some sub ∧ q₀.epoch = kp
  | [], _, _, h => by cases h
  | q :: qs, q₀, sub, h => by
    unfold findSignedSubAtLeaf at h
    split at h
    · rename_i hG
      cases hV : queryMsgValidAt q.epoch q.message with
      | none =>
        rw [hV] at h
        obtain ⟨h1, h2, h3, h4⟩ := findSignedSubAtLeaf_some h
        exact ⟨List.mem_cons_of_mem q h1, h2, h3, h4⟩
      | some s =>
        rw [hV] at h; dsimp only at h
        split at h
        · rename_i hEp
          injection h with hp; injection hp with hqEq hsEq
          subst hqEq hsEq
          exact ⟨List.mem_cons_self, hG, hV, hEp⟩
        · obtain ⟨h1, h2, h3, h4⟩ := findSignedSubAtLeaf_some h
          exact ⟨List.mem_cons_of_mem q h1, h2, h3, h4⟩
    · obtain ⟨h1, h2, h3, h4⟩ := findSignedSubAtLeaf_some h
      exact ⟨List.mem_cons_of_mem q h1, h2, h3, h4⟩

private theorem findSignedSubAtLeaf_none {kp : Nat} :
    ∀ {qs : List ProdSigningQuery},
      findSignedSubAtLeaf kp qs = none →
      ∀ q ∈ qs, 0 < q.grindLimit → ∀ sub, queryMsgValidAt q.epoch q.message = some sub →
        q.epoch ≠ kp := by
  intro qs
  induction qs with
  | nil =>
    intro _ _ hMem
    nomatch hMem
  | cons q qs ih =>
    intro hNone q' hMem hG sub hV
    unfold findSignedSubAtLeaf at hNone
    rcases List.mem_cons.mp hMem with rfl | hTail
    · rw [ite_eq_left hG, hV] at hNone
      dsimp only at hNone
      intro hEp
      rw [ite_eq_left hEp] at hNone
      cases hNone
    · split at hNone
      · cases hVq : queryMsgValidAt q.epoch q.message with
        | none => rw [hVq] at hNone; exact ih hNone q' hTail hG sub hV
        | some _ =>
          rw [hVq] at hNone; dsimp only at hNone
          split at hNone
          · cases hNone
          · exact ih hNone q' hTail hG sub hV
      · exact ih hNone q' hTail hG sub hV

private theorem mem_productionSigningLog_of_some
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey) :
    ∀ (qs : List ProdSigningQuery) (q : ProdSigningQuery) (sig : PqHashSig),
      q ∈ qs → prodSignQuery suite params sk q = some sig →
      (q.message, sig) ∈ productionSigningLog suite params sk qs
  | [], _, _, hMem, _ => nomatch hMem
  | q' :: qs, q, sig, hMem, hSome => by
    rw [productionSigningLog_cons]
    rcases List.mem_cons.mp hMem with rfl | hTail
    · rw [hSome]; exact List.mem_append_left _ List.mem_cons_self
    · exact List.mem_append_right _ (mem_productionSigningLog_of_some suite params sk qs q sig hTail hSome)

/-- **Punctured Multi-Leaf Simulation & Secret-Extraction Soundness
    (`poly257MultiLeaf_punctured_sim_sound`).**
    For ANY `nA qHash qSign : Nat` and ANY adaptive multi-query adversary family
    `adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign`, on every winning coin `ω` of
    `ExecEufCmaGame` over `poly257MultiLeafSuite` + `multiLeaf4JortsParams`, there exists an
    active chain slot `s : Fin 12` (`kp = s / 3 < 4, r = s % 3 < 3`) such that:
    1. every admitted signing query `q` in the adaptive log is compatible with puncturing `s`
       (`QuerySlotCompat s q`, proved via `BeltLatch` + `encodeSubMsg3Hmsg_incomparable`);
    2. running `adv` against `puncturedSignQuery` using ONLY `pkSeed`, the public `0xB3` endpoint
       `honestSlotHiLo o.sk (s / 3) (s % 3)`, and the `23` non-punctured secret bytes `other23`
       (never touching `o.sk.skSeed[s]`) reproduces the exact adaptive execution output and log;
    3. `extractSigChainCand` on chain `s % 3` of that simulated forgery recovers the withheld
       secret byte `[o.sk.skSeed.getD s.1 0]`. -/
theorem poly257MultiLeaf_punctured_sim_sound {nA qHash qSign : Nat}
    (hPos : 0 < (256 * pow256 24) * nA)
    (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    (ω : Fin ((256 * pow256 24) * nA))
    (hWin : (ExecEufCmaGame hPos poly257MultiLeafSuite multiLeaf4JortsParams
      (fun z => multiLeaf24Keygen ((Spec.CoinSplit.prod (256 * pow256 24) nA).chal z))
      (fun z => adv ((Spec.CoinSplit.prod (256 * pow256 24) nA).advc z))).win ω = true) :
    let π₀ := Spec.CoinSplit.prod (256 * pow256 24) nA
    let o := execEufCmaOutcome true poly257MultiLeafSuite multiLeaf4JortsParams
      (fun z => multiLeaf24Keygen (π₀.chal z)) (fun z => adv (π₀.advc z)) ω
    ∃ s : Fin 12,
      let πs := puncturedKeyAndAdvSplit nA (slot24Of12 s)
      let spAdv := Spec.CoinSplit.prod (pow256 23) nA
      let other23 := byteVecSampler 23 (spAdv.chal (πs.advc ω))
      let endpt := honestSlotHiLo o.sk (s.1 / 3) (s.1 % 3)
      let pkSim := pkFromTbl o.sk.pkSeed (puncturedSlotTbl o.sk.pkSeed s endpt other23)
      let simRun := evalLatchedAdaptiveTree true poly257MultiLeafSuite.rawHash
        (puncturedSignQuery o.sk.pkSeed s endpt other23) ((adv (spAdv.advc (πs.advc ω))).run pkSim) 0
      s.1 / 3 = o.sigStar.leafGlobalIdx ∧
      (∀ q ∈ o.queries, QuerySlotCompat s q) ∧
      pkSim = derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams o.sk ∧
      simRun = ((o.msgStar, o.sigStar), o.queries) ∧
      extractSigChainCand simRun.1.2 (s.1 % 3) = [o.sk.skSeed.getD s.1 0] := by
  intro π₀ o
  have hWinO : prodEufCmaWin poly257MultiLeafSuite multiLeaf4JortsParams o = true :=
    (execEufCmaGameWith_win true hPos poly257MultiLeafSuite multiLeaf4JortsParams
      (fun z => multiLeaf24Keygen (π₀.chal z)) (fun z => adv (π₀.advc z)) ω).symm.trans hWin
  rw [prodEufCmaWin_eq] at hWinO
  obtain ⟨hVerStar, hFreshDec⟩ := Bool.and_eq_true_iff.mp hWinO
  have hFresh : o.msgStar ∉
      (productionSigningLog poly257MultiLeafSuite multiLeaf4JortsParams o.sk o.queries).map
        Prod.fst := of_decide_eq_true hFreshDec
  obtain ⟨hKpStar, subStar, hSubStarLt, hMsgStarEq, hPreExtract⟩ :=
    verifyProductionPqHashSig_poly257MultiLeaf_sound o.sk o.msgStar o.sigStar hVerStar
  have hOneTime : ProdOneTimeLog o.queries :=
    execEufCmaOutcome_oneTime poly257MultiLeafSuite multiLeaf4JortsParams _ _ ω
  have hPickR : ∃ rStar : Fin 3,
      (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg subStar)).getD rStar.1 0 = 0 ∧
      ∀ q ∈ o.queries, QuerySlotCompat ⟨3 * o.sigStar.leafGlobalIdx + rStar.1, by omega⟩ q := by
    cases hFind : findSignedSubAtLeaf o.sigStar.leafGlobalIdx o.queries with
    | none =>
      obtain ⟨rStar, hrZero⟩ := encodeSubMsg3Hmsg_has_zero_digit ⟨subStar, hSubStarLt⟩
      refine ⟨rStar, hrZero, ?_⟩
      intro q hq hG sub hV hEp
      have hDiv : (3 * o.sigStar.leafGlobalIdx + rStar.1) / 3 = o.sigStar.leafGlobalIdx := by
        have := rStar.2; omega
      exact absurd (hEp.trans hDiv) (findSignedSubAtLeaf_none hFind q hq hG sub hV)
    | some pair =>
      rcases pair with ⟨q₀, subQ⟩
      obtain ⟨hq₀Mem, hq₀G, hq₀V, hq₀Ep⟩ := findSignedSubAtLeaf_some hFind
      have hSubQLt : subQ < 3 ∧ q₀.message = [UInt8.ofNat q₀.epoch, UInt8.ofNat subQ] := by
        unfold queryMsgValidAt at hq₀V
        match hM : q₀.message with
        | [kpB, subB] =>
          rw [hM] at hq₀V; dsimp only at hq₀V
          split at hq₀V
          · rename_i hc; injection hq₀V with hs
            exact ⟨hs ▸ hc.2.2, by rw [← hc.1, ← hs, UInt8.ofNat_toNat, UInt8.ofNat_toNat]⟩
          · cases hq₀V
        | [] | [_] | _ :: _ :: _ :: _ => rw [hM] at hq₀V; cases hq₀V
      have hSignedSome : prodSignQuery poly257MultiLeafSuite multiLeaf4JortsParams o.sk q₀ =
          some (honestMultiLeafSig o.sk q₀.epoch subQ) := by
        rw [prodSignQuery_poly257MultiLeaf_characterize, ite_eq_left hq₀G, hq₀V]
      have hInLog : q₀.message ∈
          (productionSigningLog poly257MultiLeafSuite multiLeaf4JortsParams o.sk o.queries).map
            Prod.fst := by
        refine List.mem_map.mpr ⟨(q₀.message, honestMultiLeafSig o.sk q₀.epoch subQ), ?_, rfl⟩
        exact mem_productionSigningLog_of_some _ _ _ _ _ _ hq₀Mem hSignedSome
      have hSubNe : (⟨subStar, hSubStarLt⟩ : Fin 3) ≠ ⟨subQ, hSubQLt.1⟩ := by
        intro hEq
        have hSubVal : subStar = subQ := congrArg Fin.val hEq
        have hMsgSame : q₀.message = o.msgStar := by
          rw [hSubQLt.2, hMsgStarEq, hq₀Ep, hSubVal]
        exact hFresh (hMsgSame ▸ hInLog)
      obtain ⟨rStar, hrZero, hrThree⟩ :=
        encodeSubMsg3Hmsg_incomparable ⟨subStar, hSubStarLt⟩ ⟨subQ, hSubQLt.1⟩ hSubNe
      refine ⟨rStar, hrZero, ?_⟩
      intro q hq _ sub hV hEp
      have hDiv : (3 * o.sigStar.leafGlobalIdx + rStar.1) / 3 = o.sigStar.leafGlobalIdx := by
        have := rStar.2; omega
      have hMod : (3 * o.sigStar.leafGlobalIdx + rStar.1) % 3 = rStar.1 := by
        have := rStar.2; omega
      have hqEq : q = q₀ := hOneTime q hq q₀ hq₀Mem ((hEp.trans hDiv).trans hq₀Ep.symm)
      subst hqEq
      rw [hq₀V] at hV
      injection hV with hSubEq
      subst hSubEq
      rw [hMod]
      exact hrThree
  obtain ⟨rStar, hrZero, hAllCompat⟩ := hPickR
  let s : Fin 12 := ⟨3 * o.sigStar.leafGlobalIdx + rStar.1, by have := rStar.2; omega⟩
  have hsDiv : s.1 / 3 = o.sigStar.leafGlobalIdx := by dsimp only [s]; have := rStar.2; omega
  have hsMod : s.1 % 3 = rStar.1 := by dsimp only [s]; have := rStar.2; omega
  obtain ⟨_, _, hAdvC, hLen23, hIns⟩ := puncturedKeyAndAdvSplit_coords s ω
  let πs := puncturedKeyAndAdvSplit nA (slot24Of12 s)
  let spAdv := Spec.CoinSplit.prod (pow256 23) nA
  let other23 := byteVecSampler 23 (spAdv.chal (πs.advc ω))
  let endpt := honestSlotHiLo o.sk (s.1 / 3) (s.1 % 3)
  have hPkSim : pkFromTbl o.sk.pkSeed (puncturedSlotTbl o.sk.pkSeed s endpt other23) =
      derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams o.sk := by
    rw [derivePublicKey_poly257MultiLeaf]
    unfold pkFromTbl
    rw [rootFromTbl_congr (puncturedSlotTbl_eq_honest o.sk s other23 hLen23 hIns)]
  have hTreeSim : evalLatchedAdaptiveTree true poly257MultiLeafSuite.rawHash
      (puncturedSignQuery o.sk.pkSeed s endpt other23)
      ((adv (spAdv.advc (πs.advc ω))).run
        (pkFromTbl o.sk.pkSeed (puncturedSlotTbl o.sk.pkSeed s endpt other23))) 0 =
      ((o.msgStar, o.sigStar), o.queries) := by
    rw [hAdvC, hPkSim]
    exact evalLatchedAdaptiveTree_congr_on_log poly257MultiLeafSuite.rawHash _ _ _ 0
      (fun q hq => puncturedSignQuery_eq_prodSignQuery o.sk s other23 hLen23 hIns q
        (hAllCompat q hq))
  refine ⟨s, hsDiv, hAllCompat, hPkSim, hTreeSim, ?_⟩
  rw [hTreeSim]
  dsimp only
  have hCand := hPreExtract rStar.1 rStar.2 hrZero
  rw [← hsMod] at hCand
  have hIdxEq : 3 * o.sigStar.leafGlobalIdx + s.1 % 3 = s.1 := by rw [hsMod]
  rw [hIdxEq] at hCand
  exact hCand

/-- **Query-Bounded Punctured `SM-DT-PRE` Reduction Adversary (`multiLeafBoundedPreAdv`).**
    Queries `.target (chain0Tweak (s / 3) (s % 3)) []` and `.reveal`, testing the singleton
    step-0 candidate `[candOf s advCoin]` in `Spec.WithinPreQueries 2 1`. -/
def multiLeafBoundedPreAdv {nA : Nat}
    (candOf : Fin 12 → Fin (pow256 23 * nA) → Spec.Bytes)
    (s : Fin 12) (advCoin : Fin (pow256 23 * nA)) :
    Spec.Code Spec.targetIface Spec.TargetBreak :=
  Spec.boundedPreAdv Spec.poly257Hash (chain0Tweak (s.1 / 3) (s.1 % 3))
    [candOf s advCoin]

theorem multiLeafBoundedPreAdv_mem_within {nA : Nat}
    (candOf : Fin 12 → Fin (pow256 23 * nA) → Spec.Bytes)
    (s : Fin 12) (advCoin : Fin (pow256 23 * nA)) :
    Spec.WithinPreQueries 2 1 (multiLeafBoundedPreAdv candOf s advCoin) :=
  Spec.boundedPreAdv_mem_within Spec.poly257Hash (chain0Tweak (s.1 / 3) (s.1 % 3))
    [candOf s advCoin] (Nat.le_refl 1)

/-- **General $q$-Query Adaptive EUF-CMA Bound Over `poly257MultiLeafSuite`
    (`poly257MultiLeaf_adaptive_forger_bound`).**
    For ANY `nA qHash qSign : Nat`, ANY adaptive multi-query adversary family
    `adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign`, and ANY offline candidate map `candOf`
    covering the punctured simulator's extracted chain-0 candidate on `(pkSeed, endpt)`, under
    `Spec.SmDtPreHard (Spec.WithinPreQueries 2 1) Spec.poly257Hash 1 1 1 εPre` the closed
    epoch-latched EUF-CMA game wins with probability at most `12 · εPre`. -/
theorem poly257MultiLeaf_adaptive_forger_bound {nA qHash qSign : Nat}
    (hPos : 0 < (256 * pow256 24) * nA)
    (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    (candOf : Fin 12 → Fin (pow256 23 * nA) → Spec.Bytes)
    (hCand : ∀ (s : Fin 12) (c : Fin (pow256 23 * nA)) (pkSeed : List UInt8)
        (endpt : UInt8 × UInt8),
      let spAdv := Spec.CoinSplit.prod (pow256 23) nA
      let other23 := byteVecSampler 23 (spAdv.chal c)
      let pkSim := pkFromTbl pkSeed (puncturedSlotTbl pkSeed s endpt other23)
      let simOut := (evalLatchedAdaptiveTree true poly257MultiLeafSuite.rawHash
        (puncturedSignQuery pkSeed s endpt other23) ((adv (spAdv.advc c)).run pkSim) 0).1
      simOut.2.leafGlobalIdx = s.1 / 3 →
      extractSigChainCand simOut.2 (s.1 % 3) ≠ [] →
      extractSigChainCand simOut.2 (s.1 % 3) = candOf s c)
    {εPre : Spec.RatBound}
    (hPre : Spec.SmDtPreHard (Spec.WithinPreQueries 2 1) Spec.poly257Hash 1 1 1 εPre) :
    Spec.GameBound
      (ExecEufCmaGame hPos poly257MultiLeafSuite multiLeaf4JortsParams
        (fun z => multiLeaf24Keygen ((Spec.CoinSplit.prod (256 * pow256 24) nA).chal z))
        (fun z => adv ((Spec.CoinSplit.prod (256 * pow256 24) nA).advc z))).winProb
      (Spec.RatBound.scale 12 εPre) := by
  let R : Fin 12 → Spec.FinGame ((256 * pow256 24) * nA) := fun s =>
    Spec.smDtPreGame hPos Spec.poly257Hash 1
      (fun z => (Spec.byte1SeedAndPreSampler
        ((puncturedKeyAndAdvSplit nA (slot24Of12 s)).chal z)).1)
      (fun z i => (Spec.byte1SeedAndPreSampler
        ((puncturedKeyAndAdvSplit nA (slot24Of12 s)).chal z)).2.getD i [])
      (fun z => multiLeafBoundedPreAdv candOf s
        ((puncturedKeyAndAdvSplit nA (slot24Of12 s)).advc z))
  have hRed := Spec.event_le_reduction_win
    (ExecEufCmaGame hPos poly257MultiLeafSuite multiLeaf4JortsParams
      (fun z => multiLeaf24Keygen ((Spec.CoinSplit.prod (256 * pow256 24) nA).chal z))
      (fun z => adv ((Spec.CoinSplit.prod (256 * pow256 24) nA).advc z)))
    (Spec.FinGame.mk hPos (anySlotWins 12 R))
    (fun ω hW => by
      obtain ⟨s, hsDiv, _, _, hSimEq, hExtrEq⟩ := poly257MultiLeaf_punctured_sim_sound hPos adv ω hW
      refine anySlotWins_of_win 12 R ω s ?_
      let π₀ := Spec.CoinSplit.prod (256 * pow256 24) nA
      let o := execEufCmaOutcome true poly257MultiLeafSuite multiLeaf4JortsParams
        (fun z => multiLeaf24Keygen (π₀.chal z)) (fun z => adv (π₀.advc z)) ω
      let πs := puncturedKeyAndAdvSplit nA (slot24Of12 s)
      obtain ⟨_, hHidC, _, _, _⟩ := puncturedKeyAndAdvSplit_coords s ω
      have hSimFst : (evalLatchedAdaptiveTree true poly257MultiLeafSuite.rawHash
          (puncturedSignQuery o.sk.pkSeed s (honestSlotHiLo o.sk (s.1 / 3) (s.1 % 3))
            (byteVecSampler 23 ((Spec.CoinSplit.prod (pow256 23) nA).chal (πs.advc ω))))
          ((adv ((Spec.CoinSplit.prod (pow256 23) nA).advc (πs.advc ω))).run
            (pkFromTbl o.sk.pkSeed (puncturedSlotTbl o.sk.pkSeed s
              (honestSlotHiLo o.sk (s.1 / 3) (s.1 % 3))
              (byteVecSampler 23 ((Spec.CoinSplit.prod (pow256 23) nA).chal (πs.advc ω)))))) 0).1 =
          (o.msgStar, o.sigStar) := congrArg Prod.fst hSimEq
      have hLeafEq : (evalLatchedAdaptiveTree true poly257MultiLeafSuite.rawHash
          (puncturedSignQuery o.sk.pkSeed s (honestSlotHiLo o.sk (s.1 / 3) (s.1 % 3))
            (byteVecSampler 23 ((Spec.CoinSplit.prod (pow256 23) nA).chal (πs.advc ω))))
          ((adv ((Spec.CoinSplit.prod (pow256 23) nA).advc (πs.advc ω))).run
            (pkFromTbl o.sk.pkSeed (puncturedSlotTbl o.sk.pkSeed s
              (honestSlotHiLo o.sk (s.1 / 3) (s.1 % 3))
              (byteVecSampler 23 ((Spec.CoinSplit.prod (pow256 23) nA).chal (πs.advc ω)))))) 0).1.2.leafGlobalIdx =
          s.1 / 3 := by
        rw [hSimFst]; exact hsDiv.symm
      have hNeNil : extractSigChainCand (evalLatchedAdaptiveTree true poly257MultiLeafSuite.rawHash
          (puncturedSignQuery o.sk.pkSeed s (honestSlotHiLo o.sk (s.1 / 3) (s.1 % 3))
            (byteVecSampler 23 ((Spec.CoinSplit.prod (pow256 23) nA).chal (πs.advc ω))))
          ((adv ((Spec.CoinSplit.prod (pow256 23) nA).advc (πs.advc ω))).run
            (pkFromTbl o.sk.pkSeed (puncturedSlotTbl o.sk.pkSeed s
              (honestSlotHiLo o.sk (s.1 / 3) (s.1 % 3))
              (byteVecSampler 23 ((Spec.CoinSplit.prod (pow256 23) nA).chal (πs.advc ω)))))) 0).1.2
          (s.1 % 3) ≠ [] := by
        rw [hExtrEq]; exact List.cons_ne_nil _ _
      have hCandEq : [o.sk.skSeed.getD s.1 0] = candOf s (πs.advc ω) := by
        rw [← hExtrEq]
        exact hCand s (πs.advc ω) o.sk.pkSeed (honestSlotHiLo o.sk (s.1 / 3) (s.1 % 3))
          hLeafEq hNeNil
      show (Spec.smDtPreGame hPos Spec.poly257Hash 1
        (fun z => (Spec.byte1SeedAndPreSampler (πs.chal z)).1)
        (fun z i => (Spec.byte1SeedAndPreSampler (πs.chal z)).2.getD i [])
        (fun z => multiLeafBoundedPreAdv candOf s (πs.advc z))).win ω = true
      simp only [Spec.smDtPreGame.public_eqs, Spec.smDtPreRun.public_eqs]
      unfold multiLeafBoundedPreAdv
      refine Spec.boundedPreAdv_singleton_hidden_wins Spec.poly257Hash _ _ _ _ ?_
      rw [hHidC]
      exact hCandEq)
  have hEach : ∀ s : Fin 12, Spec.GameBound (R s).winProb εPre := fun s =>
    hPre _ _ _ hPos (puncturedKeyAndAdvSplit nA (slot24Of12 s))
      Spec.byte1SeedAndPreSampler Spec.uniformOn_byte1SeedAndPre
      (multiLeafBoundedPreAdv candOf s) (multiLeafBoundedPreAdv_mem_within candOf s)
  exact Spec.GameBound.trans hRed (anySlotWins_bound hPos 12 R hEach)

/-- **Unconditional `< 1` Corollary (`poly257MultiLeaf_adaptive_forger_bound_concrete`).**
    Discharges `Spec.SmDtPreHard` in `poly257MultiLeaf_adaptive_forger_bound` via
    `Spec.poly257Hash_smDtPreHard_within 2 1`, yielding `24 / 256 < 1` across all 12 active
    `(kp, r)` chain slots. -/
theorem poly257MultiLeaf_adaptive_forger_bound_concrete {nA qHash qSign : Nat}
    (hPos : 0 < (256 * pow256 24) * nA)
    (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    (candOf : Fin 12 → Fin (pow256 23 * nA) → Spec.Bytes)
    (hCand : ∀ (s : Fin 12) (c : Fin (pow256 23 * nA)) (pkSeed : List UInt8)
        (endpt : UInt8 × UInt8),
      let spAdv := Spec.CoinSplit.prod (pow256 23) nA
      let other23 := byteVecSampler 23 (spAdv.chal c)
      let pkSim := pkFromTbl pkSeed (puncturedSlotTbl pkSeed s endpt other23)
      let simOut := (evalLatchedAdaptiveTree true poly257MultiLeafSuite.rawHash
        (puncturedSignQuery pkSeed s endpt other23) ((adv (spAdv.advc c)).run pkSim) 0).1
      simOut.2.leafGlobalIdx = s.1 / 3 →
      extractSigChainCand simOut.2 (s.1 % 3) ≠ [] →
      extractSigChainCand simOut.2 (s.1 % 3) = candOf s c) :
    Spec.GameBound
      (ExecEufCmaGame hPos poly257MultiLeafSuite multiLeaf4JortsParams
        (fun z => multiLeaf24Keygen ((Spec.CoinSplit.prod (256 * pow256 24) nA).chal z))
        (fun z => adv ((Spec.CoinSplit.prod (256 * pow256 24) nA).advc z))).winProb
      (Spec.RatBound.scale 12 ⟨2, 256, by decide⟩) ∧
    (Spec.RatBound.scale 12 ⟨2, 256, by decide⟩).lt Spec.RatBound.one :=
  ⟨poly257MultiLeaf_adaptive_forger_bound hPos adv candOf hCand
     (Spec.poly257Hash_smDtPreHard_within 2 1),
   by decide⟩

/-! #### Concrete 4-Leaf Adaptive Forger & Unconditional `< 1` `ExecEufCmaReductionEmbedding` -/

/-- Step a chain carrier `x` by `3` raw-hash queries (`st = 0, 1, 2`) at `(kp, r)`. -/
def stepChain3Adaptive {α : Type} (pkSeed : List UInt8) (kp r : Nat) (x : List UInt8)
    (k : List UInt8 → ProdAdaptiveTree α) : ProdAdaptiveTree α :=
  .hashQuery
    (thPreimage tagThF pkSeed ⟨0, 0, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, 0⟩ [x])
    (fun s1 =>
      .hashQuery
        (thPreimage tagThF pkSeed ⟨0, 0, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, 1⟩ [s1])
        (fun s2 =>
          .hashQuery
            (thPreimage tagThF pkSeed ⟨0, 0, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, 2⟩ [s2])
            k))

theorem evalLatched_stepChain3Adaptive {α : Type} (latchOn : Bool)
    (sign : ProdSigningQuery → Option PqHashSig)
    (pkSeed : List UInt8) (kp r : Nat) (x : List UInt8)
    (k : List UInt8 → ProdAdaptiveTree α) (lo : Nat) :
    evalLatchedAdaptiveTree latchOn poly257MultiLeafSuite.rawHash sign
      (stepChain3Adaptive pkSeed kp r x k) lo =
      evalLatchedAdaptiveTree latchOn poly257MultiLeafSuite.rawHash sign
        (k (wotsChainSteps poly257MultiLeafSuite pkSeed 0 0 kp r 0 3 x)) lo := by
  have hStep : ∀ (st : UInt32) (cur : List UInt8),
      poly257MultiLeafSuite.rawHash
        (thPreimage tagThF pkSeed ⟨0, 0, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, st⟩ [cur]) =
        thChainF poly257MultiLeafSuite pkSeed
          ⟨0, 0, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, st⟩ cur := by
    intro st cur
    rw [thChainF_eq, thCall_eq]
  unfold stepChain3Adaptive
  dsimp only [evalLatchedAdaptiveTree]
  rw [hStep, hStep, hStep, wotsChainSteps_succ, wotsChainSteps_succ, wotsChainSteps_succ,
    wotsChainSteps_zero]
  rfl

/-- **4-Leaf Adaptive Signing Forger (`adaptive4LeafQueryForger`).**
    Queries all four leaves `epoch = 0, 1, 2, 3` on `[0, 0]`, `[1, 0]`, `[2, 0]`, `[3, 0]`,
    adaptively advances `sig₃.wotsChains[0]` by 3 `rawHash` calls (`stepChain3Adaptive`),
    reuses `sig₃.wotsChains[2]` and `sig₃.authPath`, and guesses `encodeStep0Secret 0x00` at
    the unrevealed slot `(kp = 3, r = 1)` to forge fresh message `[3, 1]`. -/
def adaptive4LeafQueryForger : SeedWithheldEufCmaAdv 3 4 where
  run pk :=
    .signQuery ⟨[0, 0], [], 0, 1⟩ (fun _ =>
      .signQuery ⟨[1, 0], [], 1, 1⟩ (fun _ =>
        .signQuery ⟨[2, 0], [], 2, 1⟩ (fun _ =>
          .signQuery ⟨[3, 0], [], 3, 1⟩ (fun sig3Opt =>
            let lsig3 := match sig3Opt with
              | some s => s.layerSigs.headD ⟨0, [], []⟩
              | none => ⟨0, [], []⟩
            let c0 := lsig3.wotsChains.getD 0 zero32
            let c2 := lsig3.wotsChains.getD 2 zero32
            stepChain3Adaptive pk.pkSeed 3 0 c0 (fun c0End =>
              let forgedChains :=
                c0End :: encodeStep0Secret 0x00 :: c2 :: List.replicate 125 crumb32
              .pure ([3, 1],
                { rRand := zero32
                  msgTswCtr := 0
                  leafGlobalIdx := 3
                  forsOpenings := []
                  layerSigs := [⟨0, forgedChains, lsig3.authPath⟩] }))))))
  bounded _ := fun _ _ _ _ _ _ _ => trivial

private theorem evalLatched_pure_adaptive4Leaf_out
    (rawHash : List UInt8 → List UInt8) (sign : ProdSigningQuery → Option PqHashSig)
    (pk : PqPublicKey) :
    let out := (evalLatchedAdaptiveTree true rawHash sign (adaptive4LeafQueryForger.run pk) 0).1
    out.1 = [3, 1] ∧ out.2.leafGlobalIdx = 3 ∧ extractSigChainCand out.2 1 = [0x00] := by
  unfold adaptive4LeafQueryForger
  dsimp only
  rw [evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inr (Nat.zero_le 0))]
  rw [evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inr (Nat.le_refl 1))]
  rw [evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inr (Nat.le_refl 2))]
  rw [evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inr (Nat.le_refl 3))]
  unfold stepChain3Adaptive
  dsimp only [evalLatchedAdaptiveTree, extractSigChainCand]
  rw [List.getD_cons_succ, List.getD_cons_zero, decodeStep0Byte_encodeStep0Secret]
  exact ⟨rfl, rfl, rfl⟩

private theorem adaptive4Leaf_punctured_cand
    (s : Fin 12) (c : Fin (pow256 23 * 1)) (pkSeed : List UInt8) (endpt : UInt8 × UInt8) :
    let spAdv := Spec.CoinSplit.prod (pow256 23) 1
    let other23 := byteVecSampler 23 (spAdv.chal c)
    let pkSim := pkFromTbl pkSeed (puncturedSlotTbl pkSeed s endpt other23)
    let simOut := (evalLatchedAdaptiveTree true poly257MultiLeafSuite.rawHash
      (puncturedSignQuery pkSeed s endpt other23) (adaptive4LeafQueryForger.run pkSim) 0).1
    simOut.2.leafGlobalIdx = s.1 / 3 →
    extractSigChainCand simOut.2 (s.1 % 3) ≠ [] →
    extractSigChainCand simOut.2 (s.1 % 3) = [0x00] := by
  intro spAdv other23 pkSim simOut hLeaf hNeNil
  have hOut := evalLatched_pure_adaptive4Leaf_out poly257MultiLeafSuite.rawHash
    (puncturedSignQuery pkSeed s endpt other23) pkSim
  change simOut.1 = [3, 1] ∧ simOut.2.leafGlobalIdx = 3 ∧
    extractSigChainCand simOut.2 1 = [0x00] at hOut
  rw [hOut.2.1] at hLeaf
  have hsCases : s.1 = 9 ∨ s.1 = 10 ∨ s.1 = 11 := by have := s.2; omega
  rcases hsCases with hs9 | hs10 | hs11
  · have hMod0 : s.1 % 3 = 0 := by rw [hs9]
    rw [hMod0] at hNeNil
    exfalso
    apply hNeNil
    dsimp only [simOut, adaptive4LeafQueryForger]
    rw [evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inr (Nat.zero_le 0))]
    rw [evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inr (Nat.le_refl 1))]
    rw [evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inr (Nat.le_refl 2))]
    rw [evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inr (Nat.le_refl 3))]
    rw [evalLatched_stepChain3Adaptive]
    dsimp only [evalLatchedAdaptiveTree, extractSigChainCand]
    rw [List.getD_cons_zero, wotsChainSteps_succ, wotsChainSteps_succ, wotsChainSteps_succ,
      wotsChainSteps_zero, poly257MultiLeaf_thChainF]
    have hu3 : (UInt32.ofNat 3).toNat = 3 := rfl
    have hu0 : (UInt32.ofNat 0).toNat = 0 := rfl
    have hu2 : (UInt32.ofNat (0 + 1 + 1)).toNat = 2 := rfl
    dsimp only
    rw [hu3, hu0, hu2]
    simp only [and_self, (by decide : 3 < 4 ∧ 0 < 3), (by decide : ¬ (2 = 0)),
      (by decide : ¬ (2 = 1)), ↓reduceIte]
    cases decodeChainNode 0xB2 3 0 _ with
    | none => rfl
    | some p => cases p; rfl
  · have hMod1 : s.1 % 3 = 1 := by rw [hs10]
    rw [hMod1]
    exact hOut.2.2
  · have hMod2 : s.1 % 3 = 2 := by rw [hs11]
    rw [hMod2] at hNeNil
    exfalso
    apply hNeNil
    have hAbort3 : puncturedSignQuery pkSeed s endpt other23 ⟨[3, 0], [], 3, 1⟩ = none := by
      unfold puncturedSignQuery queryMsgValidAt
      have hc3 : (3 : UInt8).toNat = 3 ∧ 3 < 4 ∧ (0 : UInt8).toNat < 3 := by decide
      dsimp only
      rw [ite_eq_left Nat.one_pos, ite_eq_left hc3]
      dsimp only
      have hHit11 : 3 = s.1 / 3 ∧
          (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD (s.1 % 3) 0 ≠ 3 := by
        rw [hs11]
        refine ⟨rfl, ?_⟩
        change (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD 2 0 ≠ 3
        rw [encodeSubMsg3Hmsg_explicit_digits.2.2.1]
        decide
      exact ite_eq_left hHit11
    dsimp only [simOut, adaptive4LeafQueryForger]
    rw [evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inr (Nat.zero_le 0))]
    rw [evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inr (Nat.le_refl 1))]
    rw [evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inr (Nat.le_refl 2))]
    rw [evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inr (Nat.le_refl 3)), hAbort3]
    dsimp only
    rw [evalLatched_stepChain3Adaptive]
    dsimp only [evalLatchedAdaptiveTree, extractSigChainCand]
    rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero, List.getD_nil]
    rfl

/-- **`adaptiveMultiQueryReductionEmbedding` — Concrete 4-Query Adaptive Instance of
    `ExecEufCmaReductionEmbedding` Over `poly257MultiLeafSuite`.**
    Embeds the 4-signing-query, 3-hash-query adaptive forger `adaptive4LeafQueryForger` on all
    `256 * 256 ^ 24` keys directly into `Spec.Assumptions` (`WithinItsrQueries 1 1`,
    `WithinTcrQueries 2 1`, `WithinPreQueries 2 1`) by puncturing slot `10` (`kp = 3, r = 1`). -/
def adaptiveMultiQueryReductionEmbedding :
    ExecEufCmaReductionEmbedding
      (Nat.mul_pos (Nat.mul_pos (by decide) (pow256_pos 24)) Nat.one_pos)
      poly257MultiLeafSuite multiLeaf4JortsParams
      (fun z => multiLeaf24Keygen ((Spec.CoinSplit.prod (256 * pow256 24) 1).chal z))
      (fun _ => adaptive4LeafQueryForger) where
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
  nAi := pow256 24 * 1
  nCt := 256
  nAt := pow256 24 * 1
  nCp := 256 * 256
  nAp := pow256 23 * 1
  πi := coinSplitLiftRight 1 (Spec.CoinSplit.prod (256 * pow256 24) 1)
    (Spec.CoinSplit.prod 256 (pow256 24))
  πt := coinSplitLiftRight 1 (Spec.CoinSplit.prod (256 * pow256 24) 1)
    (Spec.CoinSplit.prod 256 (pow256 24))
  πp := puncturedKeyAndAdvSplit 1 (slot24Of12 ⟨10, by decide⟩)
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
  advP := multiLeafBoundedPreAdv (fun _ _ => [0x00]) ⟨10, by decide⟩
  hAdvP := multiLeafBoundedPreAdv_mem_within (fun _ _ => [0x00]) ⟨10, by decide⟩
  extract_win := fun ω hWin => by
    refine .inr (.inr ?_)
    let s10 : Fin 12 := ⟨10, by decide⟩
    let π₀ := Spec.CoinSplit.prod (256 * pow256 24) 1
    let o := execEufCmaOutcome true poly257MultiLeafSuite multiLeaf4JortsParams
      (fun z => multiLeaf24Keygen (π₀.chal z)) (fun _ => adaptive4LeafQueryForger) ω
    have hWinO : prodEufCmaWin poly257MultiLeafSuite multiLeaf4JortsParams o = true := hWin
    rw [prodEufCmaWin_eq] at hWinO
    obtain ⟨hVerStar, _⟩ := Bool.and_eq_true_iff.mp hWinO
    have hOut := evalLatched_pure_adaptive4Leaf_out poly257MultiLeafSuite.rawHash
      (prodSignQuery poly257MultiLeafSuite multiLeaf4JortsParams o.sk)
      (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams o.sk)
    change o.msgStar = [3, 1] ∧ o.sigStar.leafGlobalIdx = 3 ∧
      extractSigChainCand o.sigStar 1 = [0x00] at hOut
    obtain ⟨_, sub, hSubLt3, hMsgEq, hPreExtract⟩ :=
      verifyProductionPqHashSig_poly257MultiLeaf_sound o.sk o.msgStar o.sigStar hVerStar
    rw [hOut.1, hOut.2.1] at hMsgEq
    injection hMsgEq with _ hSubCons
    injection hSubCons with hSubByte _
    have hSub1 : sub = 1 := by
      have hSubCases : sub = 0 ∨ sub = 1 ∨ sub = 2 := by omega
      rcases hSubCases with rfl | rfl | rfl
      · exact absurd hSubByte (by decide)
      · rfl
      · exact absurd hSubByte (by decide)
    subst hSub1
    have hExtr1 := hPreExtract 1 (by decide) encodeSubMsg3Hmsg_explicit_digits.2.2.2.2.1
    rw [hOut.2.1, hOut.2.2] at hExtr1
    obtain ⟨_, hHidC, _, _, _⟩ := puncturedKeyAndAdvSplit_coords s10 ω
    simp only [Spec.smDtPreGame.public_eqs, Spec.smDtPreRun.public_eqs]
    unfold multiLeafBoundedPreAdv
    refine Spec.boundedPreAdv_singleton_hidden_wins Spec.poly257Hash _ _ _ _ ?_
    rw [hHidC]
    exact hExtr1.symm

/-- All-zero `k`-byte coin in `Fin (pow256 k)`. -/
def zeroVecCoin : (k : Nat) → Fin (pow256 k)
  | 0 => ⟨0, Nat.one_pos⟩
  | k + 1 => (Spec.CoinSplit.prod 256 (pow256 k)).pair ⟨0, by decide⟩ (zeroVecCoin k)

theorem byteVecSampler_zeroVecCoin :
    ∀ k : Nat, byteVecSampler k (zeroVecCoin k) = List.replicate k 0x00
  | 0 => rfl
  | k + 1 => by
    unfold zeroVecCoin
    rw [byteVecSampler_succ, (Spec.CoinSplit.prod 256 (pow256 k)).chal_pair,
      (Spec.CoinSplit.prod 256 (pow256 k)).advc_pair, byteVecSampler_zeroVecCoin k]
    rfl

theorem verify_assembled_leaf_sig (sk : PqSecretKey) {kp sub : Nat}
    (hkp : kp < 4) (hsub : sub < 3)
    (c0 c1 c2 : List UInt8)
    (hc0 : c0 = wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 kp 0 0
      ((extractBaseWDigits 4 128 (encodeSubMsg3Hmsg sub)).getD 0 0)
      (wotsSecretBase poly257MultiLeafSuite sk 0 0 kp 0))
    (hc1 : c1 = wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 kp 1 0
      ((extractBaseWDigits 4 128 (encodeSubMsg3Hmsg sub)).getD 1 0)
      (wotsSecretBase poly257MultiLeafSuite sk 0 0 kp 1))
    (hc2 : c2 = wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 kp 2 0
      ((extractBaseWDigits 4 128 (encodeSubMsg3Hmsg sub)).getD 2 0)
      (wotsSecretBase poly257MultiLeafSuite sk 0 0 kp 2)) :
    verifyProductionPqHashSig poly257MultiLeafSuite multiLeaf4JortsParams
      (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk)
      [UInt8.ofNat kp, UInt8.ofNat sub]
      { rRand := zero32
        msgTswCtr := 0
        leafGlobalIdx := kp
        forsOpenings := []
        layerSigs := [⟨0, c0 :: c1 :: c2 :: List.replicate 125 crumb32,
          authPathFromTbl (honestSlotHiLo sk) kp⟩] } = true := by
  have hHonestVer : verifyProductionPqHashSig poly257MultiLeafSuite multiLeaf4JortsParams
      (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk)
      [UInt8.ofNat kp, UInt8.ofNat sub] (honestMultiLeafSig sk kp sub) = true :=
    prodSignQuery_verifies poly257MultiLeafSuite multiLeaf4JortsParams sk
      ⟨[UInt8.ofNat kp, UInt8.ofNat sub], [], kp, 1⟩ (honestMultiLeafSig sk kp sub)
      (prodSignQuery_poly257MultiLeaf_valid sk hkp hsub Nat.one_pos [])
  have hChainsEq : c0 :: c1 :: c2 :: List.replicate 125 crumb32 =
      (List.range 128).map (fun r =>
        let dr := (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg sub)).getD r 0
        wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 kp r 0 dr
          (wotsSecretBase poly257MultiLeafSuite sk 0 0 kp r)) := by
    rw [range128_split3, List.map_cons, List.map_cons, List.map_cons, List.map_map, hc0, hc1, hc2]
    congr 3
    have hEach : ∀ k ∈ List.range 125,
        ((fun r => wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 kp r 0
          ((extractBaseWDigits 4 128 (encodeSubMsg3Hmsg sub)).getD r 0)
          (wotsSecretBase poly257MultiLeafSuite sk 0 0 kp r)) ∘ (· + 3)) k = crumb32 := by
      intro k hk
      have hkLt : k < 125 := List.mem_range.mp hk
      dsimp only [Function.comp_def]
      rw [wotsSecretBase_eq, poly257MultiLeaf_thSecretPrf]
      have hkp32 : (UInt32.ofNat kp).toNat = kp := u32_toNat_small (by omega)
      have hr32 : (UInt32.ofNat (k + 3)).toNat = k + 3 := u32_toNat_small (by omega)
      have hNot : ¬ (kp < 4 ∧ k + 3 < 3) := by omega
      simp only [hkp32, hr32, hNot, ↓reduceIte]
      exact inactive_chain_steps_crumb sk.pkSeed hkp (by omega) (by omega) _ 0
    exact ((List.map_congr_left hEach).trans (by decide)).symm
  unfold honestMultiLeafSig at hHonestVer
  rw [hChainsEq]
  exact hHonestVer

/-- **Unconditional Non-Vacuous `< 1` Multi-Query Adaptive Forger Bound
    (`adaptiveMultiQueryExecEufCma_forger_bound`).**
    Certifies simultaneously that on `poly257MultiLeafSuite` + `multiLeaf4JortsParams`:
    1. `adaptive4LeafQueryForger` issues `4` admitted signing queries across leaves `0, 1, 2, 3`,
       all `4` succeed in `productionSigningLog`, and an explicit key coin `z0` wins `ExecEufCmaGame`
       (`winCount > 0`);
    2. composing `adaptiveMultiQueryReductionEmbedding.forger_bound` with
       `Spec.byteIdxHmsg_itsrHard_within`, `Spec.poly257Hash_smDtTcrHard_within`, and
       `Spec.poly257Hash_smDtPreHard_within` yields the unconditional `< 1` bound `6 / 256`. -/
theorem adaptiveMultiQueryExecEufCma_forger_bound :
    let hPos : 0 < (256 * pow256 24) * 1 :=
      Nat.mul_pos (Nat.mul_pos (by decide) (pow256_pos 24)) Nat.one_pos
    let keygen := fun z : Fin ((256 * pow256 24) * 1) =>
      multiLeaf24Keygen ((Spec.CoinSplit.prod (256 * pow256 24) 1).chal z)
    let adv := fun _ : Fin ((256 * pow256 24) * 1) => adaptive4LeafQueryForger
    let z0 : Fin ((256 * pow256 24) * 1) :=
      (Spec.CoinSplit.prod (256 * pow256 24) 1).pair
        ((Spec.CoinSplit.prod 256 (pow256 24)).pair ⟨0, by decide⟩ (zeroVecCoin 24))
        ⟨0, Nat.one_pos⟩
    let o0 := execEufCmaOutcome true poly257MultiLeafSuite multiLeaf4JortsParams keygen adv z0
    o0.queries.length = 4 ∧
    (productionSigningLog poly257MultiLeafSuite multiLeaf4JortsParams o0.sk o0.queries).length = 4 ∧
    (ExecEufCmaGame hPos poly257MultiLeafSuite multiLeaf4JortsParams keygen adv).win z0 = true ∧
    Spec.GameBound
      (ExecEufCmaGame hPos poly257MultiLeafSuite multiLeaf4JortsParams keygen adv).winProb
      (((⟨2, 256, by decide⟩ : Spec.RatBound).add ⟨2, 256, by decide⟩).add ⟨2, 256, by decide⟩) ∧
    (((⟨2, 256, by decide⟩ : Spec.RatBound).add ⟨2, 256, by decide⟩).add ⟨2, 256, by decide⟩).lt
      Spec.RatBound.one := by
  intro hPos keygen adv z0 o0
  have hSk0Seed : (keygen z0).skSeed.getD 10 0 = 0x00 := by
    dsimp only [keygen, z0]
    rw [(Spec.CoinSplit.prod (256 * pow256 24) 1).chal_pair, multiLeaf24Keygen.public_eqs]
    dsimp only
    rw [(Spec.CoinSplit.prod 256 (pow256 24)).advc_pair, byteVecSampler_zeroVecCoin 24]
    decide
  have hS0 : prodSignQuery poly257MultiLeafSuite multiLeaf4JortsParams (keygen z0) ⟨[0, 0], [], 0, 1⟩ =
      some (honestMultiLeafSig (keygen z0) 0 0) :=
    prodSignQuery_poly257MultiLeaf_valid (keygen z0) (by decide : 0 < 4) (by decide : 0 < 3) Nat.one_pos []
  have hS1 : prodSignQuery poly257MultiLeafSuite multiLeaf4JortsParams (keygen z0) ⟨[1, 0], [], 1, 1⟩ =
      some (honestMultiLeafSig (keygen z0) 1 0) :=
    prodSignQuery_poly257MultiLeaf_valid (keygen z0) (by decide : 1 < 4) (by decide : 0 < 3) Nat.one_pos []
  have hS2 : prodSignQuery poly257MultiLeafSuite multiLeaf4JortsParams (keygen z0) ⟨[2, 0], [], 2, 1⟩ =
      some (honestMultiLeafSig (keygen z0) 2 0) :=
    prodSignQuery_poly257MultiLeaf_valid (keygen z0) (by decide : 2 < 4) (by decide : 0 < 3) Nat.one_pos []
  have hS3 : prodSignQuery poly257MultiLeafSuite multiLeaf4JortsParams (keygen z0) ⟨[3, 0], [], 3, 1⟩ =
      some (honestMultiLeafSig (keygen z0) 3 0) :=
    prodSignQuery_poly257MultiLeaf_valid (keygen z0) (by decide : 3 < 4) (by decide : 0 < 3) Nat.one_pos []
  have hOutEq : o0 =
      let lsig3 := (honestMultiLeafSig (keygen z0) 3 0).layerSigs.headD ⟨0, [], []⟩
      let c0End := wotsChainSteps poly257MultiLeafSuite (keygen z0).pkSeed 0 0 3 0 0 3
        (lsig3.wotsChains.getD 0 zero32)
      let c2 := lsig3.wotsChains.getD 2 zero32
      ⟨keygen z0,
       [⟨[0, 0], [], 0, 1⟩, ⟨[1, 0], [], 1, 1⟩, ⟨[2, 0], [], 2, 1⟩, ⟨[3, 0], [], 3, 1⟩],
       [3, 1],
       { rRand := zero32
         msgTswCtr := 0
         leafGlobalIdx := 3
         forsOpenings := []
         layerSigs := [⟨0, c0End :: encodeStep0Secret 0x00 :: c2 :: List.replicate 125 crumb32,
           lsig3.authPath⟩] }⟩ := by
    change execEufCmaOutcome true poly257MultiLeafSuite multiLeaf4JortsParams keygen adv z0 = _
    unfold execEufCmaOutcome
    dsimp only [adv, adaptive4LeafQueryForger]
    rw [derivePublicKey_poly257MultiLeaf (keygen z0)]
    dsimp only [pkFromTbl]
    rw [evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inr (Nat.zero_le 0))]
    rw [evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inr (Nat.le_refl 1))]
    rw [evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inr (Nat.le_refl 2))]
    rw [evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inr (Nat.le_refl 3)), hS3]
    dsimp only
    rw [evalLatched_stepChain3Adaptive]
    rfl
  have hLog4 : productionSigningLog poly257MultiLeafSuite multiLeaf4JortsParams o0.sk o0.queries =
      [([0, 0], honestMultiLeafSig (keygen z0) 0 0),
       ([1, 0], honestMultiLeafSig (keygen z0) 1 0),
       ([2, 0], honestMultiLeafSig (keygen z0) 2 0),
       ([3, 0], honestMultiLeafSig (keygen z0) 3 0)] := by
    rw [hOutEq]
    dsimp only
    rw [productionSigningLog_cons, hS0, productionSigningLog_cons, hS1,
      productionSigningLog_cons, hS2, productionSigningLog_cons, hS3, productionSigningLog_nil]
    rfl
  refine ⟨by rw [hOutEq]; rfl, by rw [hLog4]; rfl, ?_,
    adaptiveMultiQueryReductionEmbedding.forger_bound
      (Spec.byteIdxHmsg_itsrHard_within 1 1)
      (Spec.poly257Hash_smDtTcrHard_within 2 1)
      (Spec.poly257Hash_smDtPreHard_within 2 1),
    by decide⟩
  show prodEufCmaWin poly257MultiLeafSuite multiLeaf4JortsParams o0 = true
  rw [prodEufCmaWin_eq, hLog4]
  have hFresh : ([3, 1] : List UInt8) ∉
      ([[0, 0], [1, 0], [2, 0], [3, 0]] : List (List UInt8)) := by decide
  rw [hOutEq]
  dsimp only [List.map]
  refine Bool.and_eq_true_iff.mpr ⟨?_, decide_eq_true hFresh⟩
  unfold honestMultiLeafSig
  dsimp only [List.headD]
  have hGet0 : ((List.range 128).map (fun r =>
      wotsChainSteps poly257MultiLeafSuite (keygen z0).pkSeed 0 0 3 r 0
        ((extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD r 0)
        (wotsSecretBase poly257MultiLeafSuite (keygen z0) 0 0 3 r))).getD 0 zero32 =
      wotsSecretBase poly257MultiLeafSuite (keygen z0) 0 0 3 0 := by
    rw [list_getD_map_range 128 _ zero32 (by decide), encodeSubMsg3Hmsg_explicit_digits.1,
      wotsChainSteps_zero]
  have hGet2 : ((List.range 128).map (fun r =>
      wotsChainSteps poly257MultiLeafSuite (keygen z0).pkSeed 0 0 3 r 0
        ((extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD r 0)
        (wotsSecretBase poly257MultiLeafSuite (keygen z0) 0 0 3 r))).getD 2 zero32 =
      wotsSecretBase poly257MultiLeafSuite (keygen z0) 0 0 3 2 := by
    rw [list_getD_map_range 128 _ zero32 (by decide), encodeSubMsg3Hmsg_explicit_digits.2.2.1,
      wotsChainSteps_zero]
  rw [hGet0, hGet2]
  refine verify_assembled_leaf_sig (keygen z0) (by decide : 3 < 4) (by decide : 1 < 3) _ _ _ ?_ ?_ ?_
  · rw [encodeSubMsg3Hmsg_explicit_digits.2.2.2.1]
  · rw [encodeSubMsg3Hmsg_explicit_digits.2.2.2.2.1, wotsChainSteps_zero, wotsSecretBase_eq,
      poly257MultiLeaf_thSecretPrf]
    have hu3 : (UInt32.ofNat 3).toNat = 3 := rfl
    have hu1 : (UInt32.ofNat 1).toNat = 1 := rfl
    dsimp only
    rw [hu3, hu1, ite_eq_left (by decide : 3 < 4 ∧ 1 < 3)]
    exact congrArg encodeStep0Secret hSk0Seed.symm
  · rw [encodeSubMsg3Hmsg_explicit_digits.2.2.2.2.2.1, wotsChainSteps_zero]

/-! #### Paired Refutation Tooth: Two Queries on an Unlatched Leaf Forge With Probability `1` -/

/-- **Unlatched Same-Leaf Subset-Cover Forger (`unlatchedLeafReuseForger`).**
    Issues two signing queries `[0, 0]` (digits `(0, 3, 0)`) and `[0, 1]` (digits `(3, 0, 0)`) at
    `epoch = 0`, advances `sig₀.wotsChains[2]` by 3 `rawHash` steps, and assembles a valid
    signature `(c₀, c₁, c₂_end)` on fresh message `[0, 2]` (digits `(0, 0, 3)`). -/
def unlatchedLeafReuseForger : SeedWithheldEufCmaAdv 3 2 where
  run pk :=
    .signQuery ⟨[0, 0], [], 0, 1⟩ (fun sig0Opt =>
      .signQuery ⟨[0, 1], [], 0, 1⟩ (fun sig1Opt =>
        let lsig0 := match sig0Opt with
          | some s => s.layerSigs.headD ⟨0, [], []⟩
          | none => ⟨0, [], []⟩
        let lsig1 := match sig1Opt with
          | some s => s.layerSigs.headD ⟨0, [], []⟩
          | none => ⟨0, [], []⟩
        let c0 := lsig0.wotsChains.getD 0 zero32
        let c1 := lsig1.wotsChains.getD 1 zero32
        let c2 := lsig0.wotsChains.getD 2 zero32
        stepChain3Adaptive pk.pkSeed 0 2 c2 (fun c2End =>
          .pure ([0, 2],
            { rRand := zero32
              msgTswCtr := 0
              leafGlobalIdx := 0
              forsOpenings := []
              layerSigs := [⟨0, c0 :: c1 :: c2End :: List.replicate 125 crumb32,
                lsig0.authPath⟩] }))))
  bounded _ := fun _ _ _ _ _ => trivial

/-- **`#tooth` Removing `BeltLatch` Breaks EUF-CMA on `poly257MultiLeafSuite` With Probability `1`
    (`tooth_poly257MultiLeaf_unlatched_reuse_forges`).**
    Without the monotonic epoch latch (`latchOn = false`), `unlatchedLeafReuseForger` queries
    `[0, 0]` and `[0, 1]` on leaf `0`, constructively assembles a valid WOTS+C signature on fresh
    message `[0, 2]`, and wins `execEufCmaGameWith false` on EVERY coin `ω` across all
    `256 * 256 ^ 24` keys (`winCount = n`, refuting both `6 / 256` and `24 / 256 < 1`), whereas
    with `BeltLatch` enabled (`latchOn = true`) the second query at `epoch = 0` is refused. -/
theorem tooth_poly257MultiLeaf_unlatched_reuse_forges :
    ∃ (hPos : 0 < (256 * pow256 24) * 1) (adv : SeedWithheldEufCmaAdv 3 2),
      (∀ ω : Fin ((256 * pow256 24) * 1),
        (execEufCmaGameWith false hPos poly257MultiLeafSuite multiLeaf4JortsParams
          (fun z => multiLeaf24Keygen ((Spec.CoinSplit.prod (256 * pow256 24) 1).chal z))
          (fun _ => adv)).win ω = true) ∧
      (∀ ω : Fin ((256 * pow256 24) * 1),
        (execEufCmaOutcome true poly257MultiLeafSuite multiLeaf4JortsParams
          (fun z => multiLeaf24Keygen ((Spec.CoinSplit.prod (256 * pow256 24) 1).chal z))
          (fun _ => adv) ω).queries = [⟨[0, 0], [], 0, 1⟩]) ∧
      ¬ Spec.GameBound
          (execEufCmaGameWith false hPos poly257MultiLeafSuite multiLeaf4JortsParams
            (fun z => multiLeaf24Keygen ((Spec.CoinSplit.prod (256 * pow256 24) 1).chal z))
            (fun _ => adv)).winProb
          (((⟨2, 256, by decide⟩ : Spec.RatBound).add ⟨2, 256, by decide⟩).add
            ⟨2, 256, by decide⟩) ∧
      ¬ Spec.GameBound
          (execEufCmaGameWith false hPos poly257MultiLeafSuite multiLeaf4JortsParams
            (fun z => multiLeaf24Keygen ((Spec.CoinSplit.prod (256 * pow256 24) 1).chal z))
            (fun _ => adv)).winProb
          (Spec.RatBound.scale 12 ⟨2, 256, by decide⟩) := by
  let hPos : 0 < (256 * pow256 24) * 1 :=
    Nat.mul_pos (Nat.mul_pos (by decide) (pow256_pos 24)) Nat.one_pos
  let keygen := fun z : Fin ((256 * pow256 24) * 1) =>
    multiLeaf24Keygen ((Spec.CoinSplit.prod (256 * pow256 24) 1).chal z)
  let adv := fun _ : Fin ((256 * pow256 24) * 1) => unlatchedLeafReuseForger
  refine ⟨hPos, unlatchedLeafReuseForger, ?_⟩
  have hForallWin : ∀ ω : Fin ((256 * pow256 24) * 1),
      (execEufCmaGameWith false hPos poly257MultiLeafSuite multiLeaf4JortsParams keygen adv).win ω =
        true := by
    intro ω
    have hS0 : prodSignQuery poly257MultiLeafSuite multiLeaf4JortsParams (keygen ω) ⟨[0, 0], [], 0, 1⟩ =
        some (honestMultiLeafSig (keygen ω) 0 0) :=
      prodSignQuery_poly257MultiLeaf_valid (keygen ω) (by decide : 0 < 4) (by decide : 0 < 3) Nat.one_pos []
    have hS1 : prodSignQuery poly257MultiLeafSuite multiLeaf4JortsParams (keygen ω) ⟨[0, 1], [], 0, 1⟩ =
        some (honestMultiLeafSig (keygen ω) 0 1) :=
      prodSignQuery_poly257MultiLeaf_valid (keygen ω) (by decide : 0 < 4) (by decide : 1 < 3) Nat.one_pos []
    rw [execEufCmaGameWith_win]
    have hOut : execEufCmaOutcome false poly257MultiLeafSuite multiLeaf4JortsParams keygen adv ω =
        let lsig0 := (honestMultiLeafSig (keygen ω) 0 0).layerSigs.headD ⟨0, [], []⟩
        let lsig1 := (honestMultiLeafSig (keygen ω) 0 1).layerSigs.headD ⟨0, [], []⟩
        let c0 := lsig0.wotsChains.getD 0 zero32
        let c1 := lsig1.wotsChains.getD 1 zero32
        let c2End := wotsChainSteps poly257MultiLeafSuite (keygen ω).pkSeed 0 0 0 2 0 3
          (lsig0.wotsChains.getD 2 zero32)
        ⟨keygen ω, [⟨[0, 0], [], 0, 1⟩, ⟨[0, 1], [], 0, 1⟩], [0, 2],
         { rRand := zero32
           msgTswCtr := 0
           leafGlobalIdx := 0
           forsOpenings := []
           layerSigs := [⟨0, c0 :: c1 :: c2End :: List.replicate 125 crumb32,
             lsig0.authPath⟩] }⟩ := by
      unfold execEufCmaOutcome
      dsimp only [adv, unlatchedLeafReuseForger]
      rw [derivePublicKey_poly257MultiLeaf (keygen ω)]
      dsimp only [pkFromTbl]
      rw [evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inl rfl), hS0]
      rw [evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inl rfl), hS1]
      dsimp only
      rw [evalLatched_stepChain3Adaptive]
      rfl
    rw [hOut, prodEufCmaWin_eq]
    dsimp only
    rw [productionSigningLog_cons, hS0, productionSigningLog_cons, hS1, productionSigningLog_nil]
    dsimp only [List.append, List.map]
    have hFresh : ([0, 2] : List UInt8) ∉ ([[0, 0], [0, 1]] : List (List UInt8)) := by decide
    refine Bool.and_eq_true_iff.mpr ⟨?_, decide_eq_true hFresh⟩
    unfold honestMultiLeafSig
    dsimp only [List.headD]
    have hGet0 : ((List.range 128).map (fun r =>
        wotsChainSteps poly257MultiLeafSuite (keygen ω).pkSeed 0 0 0 r 0
          ((extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD r 0)
          (wotsSecretBase poly257MultiLeafSuite (keygen ω) 0 0 0 r))).getD 0 zero32 =
        wotsSecretBase poly257MultiLeafSuite (keygen ω) 0 0 0 0 := by
      rw [list_getD_map_range 128 _ zero32 (by decide), encodeSubMsg3Hmsg_explicit_digits.1,
        wotsChainSteps_zero]
    have hGet1 : ((List.range 128).map (fun r =>
        wotsChainSteps poly257MultiLeafSuite (keygen ω).pkSeed 0 0 0 r 0
          ((extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 1)).getD r 0)
          (wotsSecretBase poly257MultiLeafSuite (keygen ω) 0 0 0 r))).getD 1 zero32 =
        wotsSecretBase poly257MultiLeafSuite (keygen ω) 0 0 0 1 := by
      rw [list_getD_map_range 128 _ zero32 (by decide),
        encodeSubMsg3Hmsg_explicit_digits.2.2.2.2.1, wotsChainSteps_zero]
    have hGet2 : ((List.range 128).map (fun r =>
        wotsChainSteps poly257MultiLeafSuite (keygen ω).pkSeed 0 0 0 r 0
          ((extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD r 0)
          (wotsSecretBase poly257MultiLeafSuite (keygen ω) 0 0 0 r))).getD 2 zero32 =
        wotsSecretBase poly257MultiLeafSuite (keygen ω) 0 0 0 2 := by
      rw [list_getD_map_range 128 _ zero32 (by decide), encodeSubMsg3Hmsg_explicit_digits.2.2.1,
        wotsChainSteps_zero]
    rw [hGet0, hGet1, hGet2]
    refine verify_assembled_leaf_sig (keygen ω) (by decide : 0 < 4) (by decide : 2 < 3) _ _ _ ?_ ?_ ?_
    · rw [encodeSubMsg3Hmsg_explicit_digits.2.2.2.2.2.2.1, wotsChainSteps_zero]
    · rw [encodeSubMsg3Hmsg_explicit_digits.2.2.2.2.2.2.2.1, wotsChainSteps_zero]
    · rw [encodeSubMsg3Hmsg_explicit_digits.2.2.2.2.2.2.2.2]
  have hLatchedLog : ∀ ω : Fin ((256 * pow256 24) * 1),
      (execEufCmaOutcome true poly257MultiLeafSuite multiLeaf4JortsParams keygen adv ω).queries =
        [⟨[0, 0], [], 0, 1⟩] := by
    intro ω
    dsimp only [execEufCmaOutcome, adv, unlatchedLeafReuseForger]
    rw [evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inr (Nat.zero_le 0))]
    have hRefuse : ¬ ((true = false) ∨ 1 ≤ 0) := fun h =>
      h.elim (fun hb => Bool.noConfusion hb) (by decide)
    rw [evalLatchedAdaptiveTree_sign, ite_eq_right hRefuse]
    unfold stepChain3Adaptive
    rfl
  refine ⟨hForallWin, hLatchedLog,
    Spec.FinGame.not_bound_of_forall_win _ hForallWin (by decide),
    Spec.FinGame.not_bound_of_forall_win _ hForallWin (by decide)⟩

/-- Joint inhabitedness witness for `poly257MultiLeaf_adaptive_forger_bound` with
    `adaptive4LeafQueryForger` and `Spec.WithinPreQueries 2 1` at the proved `< 1` bound
    `εPre = 2 / 256` (`12 · εPre = 24 / 256 < 1`). -/
theorem inhabited_poly257MultiLeaf_adaptive_forger_bound :
    ∃ (nA qHash qSign : Nat),
      0 < (256 * pow256 24) * nA ∧
      ∃ (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
        (candOf : Fin 12 → Fin (pow256 23 * nA) → Spec.Bytes),
        (∀ (s : Fin 12) (c : Fin (pow256 23 * nA)) (pkSeed : List UInt8)
            (endpt : UInt8 × UInt8),
          let spAdv := Spec.CoinSplit.prod (pow256 23) nA
          let other23 := byteVecSampler 23 (spAdv.chal c)
          let pkSim := pkFromTbl pkSeed (puncturedSlotTbl pkSeed s endpt other23)
          let simOut := (evalLatchedAdaptiveTree true poly257MultiLeafSuite.rawHash
            (puncturedSignQuery pkSeed s endpt other23) ((adv (spAdv.advc c)).run pkSim) 0).1
          simOut.2.leafGlobalIdx = s.1 / 3 →
          extractSigChainCand simOut.2 (s.1 % 3) ≠ [] →
          extractSigChainCand simOut.2 (s.1 % 3) = candOf s c) ∧
        ∃ εPre : Spec.RatBound,
          Spec.SmDtPreHard (Spec.WithinPreQueries 2 1) Spec.poly257Hash 1 1 1 εPre :=
  ⟨1, 3, 4, Nat.mul_pos (Nat.mul_pos (by decide) (pow256_pos 24)) Nat.one_pos,
   fun _ => adaptive4LeafQueryForger,
   fun _ _ => [0x00],
   adaptive4Leaf_punctured_cand,
   ⟨2, 256, by decide⟩,
   Spec.poly257Hash_smDtPreHard_within 2 1⟩

/-! ### Public Frame/Address Decoders & Dispatch Exports for Downstream Reductions -/

def decodeMultiFrameBytes (raw : List UInt8) : Option (List (List UInt8)) :=
  decodeMultiFrameLocal raw

theorem decodeMultiFrameBytes_encodeMultiFrame (fields : List (List UInt8)) :
    decodeMultiFrameBytes (encodeMultiFrame fields) = some fields :=
  decodeMultiFrameLocal_encodeMultiFrame fields

def decodeAdrsBytes (bs : List UInt8) : Option HashAdrs :=
  decodeAdrsLocal bs

theorem decodeAdrsBytes_encodeAdrs (a : HashAdrs) :
    decodeAdrsBytes (encodeAdrs a) = some a :=
  decodeAdrsLocal_encodeAdrs a

def parseThPreimage (raw : List UInt8) :
    Option (List UInt8 × List UInt8 × HashAdrs × List (List UInt8)) :=
  parseThPreimageLocal raw

theorem parseThPreimage_thPreimage (role pkSeed : List UInt8)
    (adrs : HashAdrs) (args : List (List UInt8)) :
    parseThPreimage (thPreimage role pkSeed adrs args) = some (role, pkSeed, adrs, args) :=
  parseThPreimageLocal_thPreimage role pkSeed adrs args

def decodeChainNodeBytes (expectedTag : UInt8) (kp r : Nat) (x : List UInt8) :
    Option (UInt8 × UInt8) :=
  decodeChainNode expectedTag kp r x

theorem decodeChainNodeBytes_encodeChainNode (tag : UInt8) (kp r : Nat) (hi lo : UInt8) :
    decodeChainNodeBytes tag kp r (encodeChainNode tag kp r hi lo) = some (hi, lo) :=
  decodeChainNode_encodeChainNode tag kp r hi lo

theorem decodeChainNodeBytes_sound {tag : UInt8} {kp r : Nat} {x : List UInt8} {hi lo : UInt8}
    (h : decodeChainNodeBytes tag kp r x = some (hi, lo)) :
    x = encodeChainNode tag kp r hi lo :=
  decodeChainNode_sound h

theorem poly257MultiLeaf_thPreHash_eq (pkSeed pkRoot msg : List UInt8) :
    thPreHash poly257MultiLeafSuite pkSeed pkRoot msg =
      match msg with
      | [kpB, subB] =>
        if kpB.toNat < 4 ∧ subB.toNat < 3 then
          [0xE0, kpB, subB] ++ List.replicate 29 0x00
        else 0xFF :: List.replicate 31 0x00
      | _ => 0xFF :: List.replicate 31 0x00 :=
  poly257MultiLeaf_thPreHash pkSeed pkRoot msg

theorem poly257MultiLeaf_thPrfMsg_eq (skPrf optRand mu : List UInt8) :
    thPrfMsg poly257MultiLeafSuite skPrf optRand mu = zero32 :=
  poly257MultiLeaf_thPrfMsg skPrf optRand mu

theorem poly257MultiLeaf_thTweakTl_cases (pkSeed : List UInt8) {kp : Nat} (hkp : kp < 4)
    (limbs : List (List UInt8)) :
    (∃ ps, thTweakTl poly257MultiLeafSuite pkSeed ⟨0, 0, .wotsPk, UInt32.ofNat kp, 0, 0⟩ limbs =
      [0xC0, UInt8.ofNat kp] ++ packLeaf3 ps ++ List.replicate 24 0x00) ∨
    thTweakTl poly257MultiLeafSuite pkSeed ⟨0, 0, .wotsPk, UInt32.ofNat kp, 0, 0⟩ limbs =
      0xFF :: List.replicate 31 0x00 := by
  rw [poly257MultiLeaf_thTweakTl]
  have hkp32 : (UInt32.ofNat kp).toNat = kp := u32_toNat_small (by omega)
  simp only [hkp32, hkp, and_self, ↓reduceIte]
  cases extractActive3 kp limbs with
  | some ps => exact .inl ⟨ps, rfl⟩
  | none => exact .inr rfl

theorem poly257MultiLeaf_thHashLeafMsg_eq (rRand pkSeed pkRoot mu : List UInt8)
    (treeIdx : UInt64) (kpIdx : UInt32) (ctr : Nat) :
    thHashLeafMsg poly257MultiLeafSuite rRand pkSeed pkRoot mu treeIdx kpIdx ctr =
      match mu with
      | 0xE0 :: kpB :: subB :: rest =>
        if kpB.toNat < 4 ∧ subB.toNat < 3 ∧ kpB.toNat = kpIdx.toNat ∧
            rest = List.replicate 29 0x00 then
          encodeSubMsg3Hmsg subB.toNat
        else zero32
      | _ => zero32 :=
  poly257MultiLeaf_thHashLeafMsg rRand pkSeed pkRoot mu treeIdx kpIdx ctr

theorem poly257MultiLeaf_thChainF_eq (pkSeed : List UInt8) (adrs : HashAdrs) (x : List UInt8) :
    thChainF poly257MultiLeafSuite pkSeed adrs x =
      let kp := adrs.keyPair.toNat
      let r := adrs.chainIdx.toNat
      let st := adrs.hashStep.toNat
      if adrs.layer = 0 ∧ adrs.tree = 0 ∧ adrs.kind = .wotsHash then
        if kp < 4 ∧ r < 3 then
          if st = 0 then
            match decodeStep0Byte x with
            | some b =>
              let yx := Spec.byteXorHash pkSeed (chain0Tweak kp r) [b]
              let yp := Spec.poly257Hash pkSeed (chain0Tweak kp r) [b]
              encodeChainNode 0xB1 kp r (yx.headD 0) (yp.getD 2 0)
            | none => 0xFF :: List.replicate 31 0x00
          else if st = 1 then
            match decodeChainNodeBytes 0xB1 kp r x with
            | some (hi, lo) => encodeChainNode 0xB2 kp r hi lo
            | none => 0xFF :: List.replicate 31 0x00
          else if st = 2 then
            match decodeChainNodeBytes 0xB2 kp r x with
            | some (hi, lo) => encodeChainNode 0xB3 kp r hi lo
            | none => 0xFF :: List.replicate 31 0x00
          else 0xFF :: List.replicate 31 0x00
        else
          if x = crumb32 then crumb32 else 0xFF :: List.replicate 31 0x00
      else 0xFF :: List.replicate 31 0x00 :=
  poly257MultiLeaf_thChainF pkSeed adrs x

theorem poly257MultiLeaf_thTweakTl_limb012_eq (pkSeed : List UInt8) {kp : Nat} (hkp : kp < 4)
    {limbs : List (List UInt8)} {hi₀ lo₀ hi₁ lo₁ hi₂ lo₂ : UInt8}
    (hEq : thTweakTl poly257MultiLeafSuite pkSeed ⟨0, 0, .wotsPk, UInt32.ofNat kp, 0, 0⟩ limbs =
      [0xC0, UInt8.ofNat kp] ++ packLeaf3 [(hi₀, lo₀), (hi₁, lo₁), (hi₂, lo₂)] ++
        List.replicate 24 0x00) :
    limbs.getD 0 [] = encodeChainNode 0xB3 kp 0 hi₀ lo₀ ∧
    limbs.getD 1 [] = encodeChainNode 0xB3 kp 1 hi₁ lo₁ ∧
    limbs.getD 2 [] = encodeChainNode 0xB3 kp 2 hi₂ lo₂ := by
  rw [poly257MultiLeaf_thTweakTl] at hEq
  have hkp32 : (UInt32.ofNat kp).toNat = kp := u32_toNat_small (by omega)
  simp only [hkp32, hkp, and_self, ↓reduceIte] at hEq
  cases hExt : extractActive3 kp limbs with
  | none =>
    rw [hExt] at hEq
    have hHead := congrArg (fun l => l.headD 0) hEq
    cases hHead
  | some ps =>
    rw [hExt] at hEq
    dsimp only at hEq
    unfold extractActive3 at hExt
    rcases limbs with _ | ⟨l0, _ | ⟨l1, _ | ⟨l2, rest⟩⟩⟩
    · cases hExt
    · cases hExt
    · cases hExt
    · dsimp only [List.getD] at hExt ⊢
      by_cases hRest : rest = List.replicate 125 crumb32
      · rw [ite_eq_left hRest] at hExt
        cases h0 : decodeChainNode 0xB3 kp 0 l0 with
        | none => rw [h0] at hExt; cases hExt
        | some p0 =>
          cases h1 : decodeChainNode 0xB3 kp 1 l1 with
          | none => rw [h0, h1] at hExt; cases hExt
          | some p1 =>
            cases h2 : decodeChainNode 0xB3 kp 2 l2 with
            | none => rw [h0, h1, h2] at hExt; cases hExt
            | some p2 =>
              rw [h0, h1, h2] at hExt
              injection hExt with hPs
              subst hPs
              have hPack : packLeaf3 [p0, p1, p2] =
                  packLeaf3 [(hi₀, lo₀), (hi₁, lo₁), (hi₂, lo₂)] := by
                have hSub := congrArg (fun l => (l.drop 2).take 6) hEq
                simpa [packLeaf3] using hSub
              obtain ⟨rfl, rfl, rfl⟩ := packLeaf3_inj hPack
              exact ⟨decodeChainNode_sound h0, decodeChainNode_sound h1, decodeChainNode_sound h2⟩
      · rw [ite_eq_right hRest] at hExt
        cases hExt

theorem poly257MultiLeaf_thChainF_step2_endpt (pkSeed : List UInt8) {kp r : Nat}
    (hkp : kp < 4) (hr : r < 3) (b : UInt8) :
    wotsChainSteps poly257MultiLeafSuite pkSeed 0 0 kp r 0 3 (encodeStep0Secret b) =
      encodeChainNode 0xB3 kp r
        ((Spec.byteXorHash pkSeed (chain0Tweak kp r) [b]).headD 0)
        ((Spec.poly257Hash pkSeed (chain0Tweak kp r) [b]).getD 2 0) :=
  active_chain_steps_3 pkSeed hkp hr b

theorem poly257MultiLeaf_inactive_crumb (pkSeed : List UInt8) {kp r : Nat}
    (hkp : kp < 4) (hr : 3 ≤ r) (hrLt : r < 128) (k start : Nat) :
    wotsChainSteps poly257MultiLeafSuite pkSeed 0 0 kp r start k crumb32 = crumb32 :=
  inactive_chain_steps_crumb pkSeed hkp hr hrLt k start

theorem poly257MultiLeaf_computeWotsPk_eq (sk : PqSecretKey) {kp : Nat} (hkp : kp < 4) :
    computeWotsPk poly257MultiLeafSuite multiLeaf4JortsParams sk 0 0 kp =
      leafFromTbl (honestSlotHiLo sk) kp :=
  computeWotsPk_poly257MultiLeaf sk hkp

theorem extractSigChainCand_stepChain3_empty (pkSeed : List UInt8) (kp r : Nat) (x : List UInt8)
    (hkp : kp < 4) (hr : r < 3) (authPath : List (List UInt8)) (tail : List (List UInt8)) :
    extractSigChainCand
      { rRand := zero32
        msgTswCtr := 0
        leafGlobalIdx := kp
        forsOpenings := []
        layerSigs := [⟨0, wotsChainSteps poly257MultiLeafSuite pkSeed 0 0 kp r 0 3 x :: tail,
          authPath⟩] }
      0 = [] := by
  dsimp only [extractSigChainCand]
  rw [List.getD_cons_zero, wotsChainSteps_succ, wotsChainSteps_succ, wotsChainSteps_succ,
    wotsChainSteps_zero, poly257MultiLeaf_thChainF]
  have hkp32 : (UInt32.ofNat kp).toNat = kp := u32_toNat_small (by omega)
  have hr32 : (UInt32.ofNat r).toNat = r := u32_toNat_small (by omega)
  have hu2 : (UInt32.ofNat (0 + 1 + 1)).toNat = 2 := rfl
  dsimp only
  rw [hkp32, hr32, hu2]
  simp only [and_self, hkp, hr, (by decide : ¬ (2 = 0)), (by decide : ¬ (2 = 1)), ↓reduceIte]
  cases decodeChainNode 0xB2 kp r _ with
  | none => rfl
  | some p => cases p; rfl

#export_eqns evalLatchedAdaptiveTree
#export_eqns encodeChainNode
#export_eqns encodeSubMsg3Hmsg
#export_eqns honestSlotHiLo
#export_eqns honestMultiLeafSig
#export_eqns packLeaf3
#export_eqns leafFromTbl
#export_eqns node1FromTbl
#export_eqns rootFromTbl
#export_eqns pkFromTbl
#export_eqns authPathFromTbl
#export_eqns extractSigChainCand
#export_eqns stepChain3Adaptive

theorem slot24Of12_val (s : Fin 12) : (slot24Of12 s).1 = s.1 := by
  unfold slot24Of12
  rfl

theorem puncturedSignQuery_s1_00_isSome
    (pkSeed : List UInt8) (endpt : UInt8 × UInt8) (other23 : Spec.Bytes) :
    (puncturedSignQuery pkSeed ⟨1, by decide⟩ endpt other23 ⟨[0, 0], [], 0, 1⟩).isSome = true := by
  unfold puncturedSignQuery queryMsgValidAt
  have hc0 : (0 : UInt8).toNat = 0 ∧ 0 < 4 ∧ (0 : UInt8).toNat < 3 := by decide
  have hu0 : (0 : UInt8).toNat = 0 := rfl
  dsimp only
  rw [ite_eq_left Nat.one_pos, ite_eq_left hc0]
  dsimp only
  rw [hu0]
  have hNoAbort : ¬ (0 = 1 / 3 ∧
      (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD (1 % 3) 0 ≠ 3) := by
    intro hc
    exact hc.2 encodeSubMsg3Hmsg_explicit_digits.2.1
  rw [ite_eq_right hNoAbort]
  rfl

theorem puncturedSignQuery_s2_00_none
    (pkSeed : List UInt8) (endpt : UInt8 × UInt8) (other23 : Spec.Bytes) :
    puncturedSignQuery pkSeed ⟨2, by decide⟩ endpt other23 ⟨[0, 0], [], 0, 1⟩ = none := by
  unfold puncturedSignQuery queryMsgValidAt
  have hc0 : (0 : UInt8).toNat = 0 ∧ 0 < 4 ∧ (0 : UInt8).toNat < 3 := by decide
  have hu0 : (0 : UInt8).toNat = 0 := rfl
  dsimp only
  rw [ite_eq_left Nat.one_pos, ite_eq_left hc0]
  dsimp only
  rw [hu0]
  have hAbort : 0 = 2 / 3 ∧
      (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD (2 % 3) 0 ≠ 3 := by
    refine ⟨rfl, ?_⟩
    change (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD 2 0 ≠ 3
    rw [encodeSubMsg3Hmsg_explicit_digits.2.2.1]
    decide
  exact ite_eq_left hAbort

theorem pkFromTbl_puncturedSlotTbl_s1_byte4
    (pkSeed : List UInt8) (hi lo : UInt8) (other23 : Spec.Bytes) :
    (pkFromTbl pkSeed (puncturedSlotTbl pkSeed ⟨1, by decide⟩ (hi, lo) other23)).pkRoot.getD 4 0 =
      hi := by
  unfold pkFromTbl rootFromTbl packLeaf3 puncturedSlotTbl
  rfl

theorem poly257MultiLeaf_walkAuthPath_honest (sk : PqSecretKey) {kp : Nat} (hkp : kp < 4) :
    walkMerkleAuthPathKp poly257MultiLeafSuite sk.pkSeed 0 0 .tree 0 2 0 kp
      (leafFromTbl (honestSlotHiLo sk) kp) (authPathFromTbl (honestSlotHiLo sk) kp) =
      some (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk).pkRoot := by
  have hWalk := walkMerkleAuthPathKp_buildMerkleAuthPathKp poly257MultiLeafSuite sk.pkSeed
    0 0 .tree 0 (computeWotsPk poly257MultiLeafSuite multiLeaf4JortsParams sk 0 0) 2 0 0 kp hkp
  simp only [Nat.zero_mul, Nat.zero_add] at hWalk
  rw [← computeWotsPk_poly257MultiLeaf sk hkp, ← buildMerkleAuthPathKp_poly257MultiLeaf sk hkp,
    hWalk, computeMerkleNodeKp_zero_eq]
  unfold derivePublicKey
  dsimp only
  rw [computeXmssSubtreeRoot_eq]
  rfl

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
  Qsag.uniformOn_byteVecSampler
  Qsag.splitByteVecAt_getD_and_insert
  Qsag.multiLeaf4JortsParams_productionWellFormed
  Qsag.multiLeaf24Keygen_uniform
  Qsag.decodeStep0Byte_encodeStep0Secret
  Qsag.encodeMsg3Hmsg_digits_valid
  Qsag.encodeMsg3Hmsg_incomparable
  Qsag.encodeMsg3Hmsg_has_zero_digit
  Qsag.encodeSubMsg3Hmsg_incomparable
  Qsag.encodeSubMsg3Hmsg_has_zero_digit
  Qsag.derivePublicKey_poly257MultiLeaf
  Qsag.poly257MultiLeaf_punctured_sim_sound
  Qsag.multiLeafBoundedPreAdv_mem_within
  Qsag.poly257MultiLeaf_adaptive_forger_bound
  Qsag.poly257MultiLeaf_adaptive_forger_bound_concrete
  Qsag.adaptiveMultiQueryExecEufCma_forger_bound
  Qsag.tooth_poly257MultiLeaf_unlatched_reuse_forges
  Qsag.inhabited_poly257MultiLeaf_adaptive_forger_bound

#verify_inhabited
  Qsag.poly257MultiLeaf_adaptive_forger_bound
  Qsag.inhabited_poly257MultiLeaf_adaptive_forger_bound

#tooth_pair Qsag.poly257MultiLeaf_adaptive_forger_bound vs
  Qsag.tooth_poly257MultiLeaf_unlatched_reuse_forges
#tooth_pair Qsag.adaptiveMultiQueryExecEufCma_forger_bound vs
  Qsag.tooth_poly257MultiLeaf_unlatched_reuse_forges

end Qsag
end
